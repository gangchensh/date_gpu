/- ========================================================================= -/
/-                        CTA/CTA2warp.lean                                   -/
/-  CTA→warp 派发接口转换模块（CTA2warp）的 Lean 4 模型与契约                   -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/CTA2warp.scala      -/
/-    （class CTA2warp，全文 79 行）                                           -/
/-  参数（top/parameters.scala）：num_warp=8 (:8)、depth_warp=3 (:30)、         -/
/-    TAG_WIDTH=6 (:153，WF_TAG_WIDTH_UINT = log2Ceil(8)+log2Ceil(8))、        -/
/-    MMU_ENABLED=false (:15) ⇒ dispatch2cu_knl_asid 字段不存在（:32）。        -/
/-  例化上下文（GPGPU_top.scala:351-364，SM_wrapper 内）：                     -/
/-    warpReq/warpRsp 接 pipe 的 warp_scheduler；warpReq.ready 恒 1             -/
/-    （warp_schedule.scala:54）；warpRsp.valid 是 warp_end 单拍脉冲            -/
/-    （warp_schedule.scala:55，I-6）；CTAreq/CTArsp 接 CTAinterface            -/
/-    （GPGPU_top.scala:89-113 的字段映射）。                                  -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. CTAreqData 共 13 个字段（:17-33），本模块内部只消费                     -/
/-      dispatch2cu_wf_tag_dispatch（:65 写入 data）；其余字段经 :68            -/
/-      `warpReq.bits.CTAdata := CTAreq.bits` 纯透传给 warp_scheduler，        -/
/-      不在本文件建模。                                                        -/
/-  D2. `Queue(io.warpRsp, 16)`（:73）按 chisel 标准 Queue 语义建模：           -/
/-      enq.ready / deq.valid 都只看**旧** count（pipe=false、flow=false，      -/
/-      无同拍旁路）；元素只关心 wid（warpRspData 只有 wid 一个字段，:41-43）。 -/
/-      队列为空时 CTArsp.bits 是 RAM 未定义读出——建模为 0，因                 -/
/-      CTArsp.valid=0 而不可观测。                                             -/
/-  D3. `data`（:57）是**无 RegInit** 的 Reg Vec：模型保留为任意初值的函数      -/
/-      字段；测试用全 0 初值，定理不依赖初值。                                 -/
/-  D4. warpRsp.valid 是自由输入（I-6：单拍脉冲、不保持到 ready）；             -/
/-      "响应被丢弃"的语义体现在 enqFire 需要 FIFO 非满（:73-74）。             -/
/-  D5. Chisel 语义关键（沿用 WarpScheduler.lean M4）：Reg 读一律读旧值，       -/
/-      data 的当拍写下拍生效——这是 Q1（I-23 候选）时序分析的基础。             -/
/-  D6. :63 的 `(1.U<<idx_next_allocate)` / `(1.U<<wid)`：3 位移位进 8 位       -/
/-      恰好无截断（索引 ≤ 7），建模为 BitVec 8 移位即可。                      -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1 = 【I-23 候选，新发现】CTArsp 的 wf_tag 在**出队时**从 data(wid)         -/
/-      组合读出（:77），而非入队时捕获。wid 在 warpRsp.fire 当拍即被           -/
/-      idx_using 清除（:63），下一拍即可被新 CTAreq 复用并覆写 data(wid)       -/
/-      （:64-66）。若旧响应在 FIFO 中滞留 ≥2 拍（CTArsp 反压），出队时读到的   -/
/-      已是**新 warp 的 tag**。后果链：cu_interface 把 done 计到新 WG 的        -/
/-      (cu, wg_slot)（cu_interface.scala:161 按 wf_tag 取 slot）→ 旧 WG 的    -/
/-      wf_gather_cnt 永远缺 1（**永不完成**：槽位/资源/host 通知全泄漏），      -/
/-      新 WG 多计 1（**提前完成**：num_wf 个 warp 未跑完即 dealloc+上报 host， -/
/-      资源被回收再分配，与仍在运行的 warp 冲突）。触发窗口极宽：同 WG 多 warp -/
/-      相继 endprg 时 cu_interface 的 gather FSM 每处理一个 done 需 ≥2 拍      -/
/-      （UPDATE/DEALLOC 期间 cu_wf_done.ready=0），FIFO 滞留是常态。           -/
/-      本文件 T7 witness + c2w7 两条定理钉死机制与安全边界。                   -/
/-  Q2 = I-6 旁证定量：Queue(16) 填满条件 = "CTArsp 持续不消费期间净增 16 个    -/
/-      endprg 响应"。num_warp=8 时单代最多积压 8 个；填满需两代（idx_using    -/
/-      位在 rsp.fire 即清，CTAreq 可立即复用 wid 再产生 8 个）。填满后：       -/
/-      warpRsp.ready=0 → assert 触发（仅仿真）；综合后响应**静默丢弃** →       -/
/-      idx_using 位永不清（:63 等 fire）→ warp 槽泄漏 → 8 槽全漏后            -/
/-      CTAreq.ready 永 0，SM 派发死锁；同时 warp_scheduler 侧 belong/cnt       -/
/-      卡死（I-6 后果链）。本文件 T6 witness + c2w3/c2w4/c2w6 定理钉死。       -/
/-  Q3. :67 `io.warpReq.valid := io.CTAreq.fire`：valid 依赖自身 ready（经      -/
/-      fire）。无组合环（CTAreq.ready 不看 warpReq.ready），但若下游           -/
/-      warpReq.ready=0，则 CTAreq 已 fire（idx_using 已置位、data 已写）而     -/
/-      warp_scheduler 未收到 warp → warp 丢失且槽位泄漏。当前安全**完全依赖**  -/
/-      warp_schedule.scala:54 的 ready:=true.B——隐性契约，记录。              -/
/-  Q4. :57 `data` 无 RegInit：复位后 wg_id_lookup 读到未定值（:58）。          -/
/-      消费方 warp_schedule.scala:117-118 只在 warp_end 时读，而 warp_end      -/
/-      之前必有 warpReq 写入（:64-66）→ 当前不可观测；复用时需注意。           -/
/-  Q5. :74 的 assert 只在仿真存在，综合后 FIFO 满的丢弃完全静默（与 I-6        -/
/-      报告一致）。                                                             -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.QueueModel
import Std.Tactic.BVDecide

namespace Ventus.CTA

set_option linter.unusedVariables false

open Ventus.Base

/- ========================================================================= -/
/- 1. 常量与位辅助                                                            -/
/- ========================================================================= -/

/-- BitVec 3 索引转 Fin 8（depth_warp=3, num_warp=8） -/
def c2wFin (x : BitVec 3) : Fin 8 := ⟨x.toNat, by have h := x.isLt; omega⟩

theorem c2wFin_inj {a b : BitVec 3} (h : c2wFin a = c2wFin b) : a = b :=
  BitVec.toNat_inj.mp (congrArg Fin.val h)

/-- PriorityEncoder(~idx_using)（:59）：最低置位位的编号；全 0 → 0
    （Chisel PriorityEncoder 对全 0 输入输出 0；此时 CTAreq.ready=0，结果不被消费） -/
def c2wPriorityEnc (u : BitVec 8) : BitVec 3 :=
  if (u >>> 0) &&& 1#8 = 1#8 then 0#3 else
  if (u >>> 1) &&& 1#8 = 1#8 then 1#3 else
  if (u >>> 2) &&& 1#8 = 1#8 then 2#3 else
  if (u >>> 3) &&& 1#8 = 1#8 then 3#3 else
  if (u >>> 4) &&& 1#8 = 1#8 then 4#3 else
  if (u >>> 5) &&& 1#8 = 1#8 then 5#3 else
  if (u >>> 6) &&& 1#8 = 1#8 then 6#3 else
  if (u >>> 7) &&& 1#8 = 1#8 then 7#3 else 0#3

/- ========================================================================= -/
/- 2. 状态、输入、输出                                                        -/
/- ========================================================================= -/

/-- CTA2warp 的全部寄存器状态（:54,:57,:73） -/
structure C2wState where
  idxUsing : BitVec 8            -- :54 idx_using（RegInit 0）
  data : Fin 8 → BitVec 6        -- :57 data（无 RegInit，D3）
  fifo : List (BitVec 3)         -- :73 CTArsp_fifo 内容（队首 = head），容量 16（D2）

/-- RegInit/空 FIFO 初值（data 无复位，测试取全 0，D3） -/
def c2wInit : C2wState := { idxUsing := 0#8, data := rf_zero 8 6, fifo := [] }

/-- 输入（只含本模块消费的字段，D1） -/
structure C2wInputs where
  ctaReqValid : Bool      -- io.CTAreq.valid（:47）
  ctaReqTag : BitVec 6    -- io.CTAreq.bits.dispatch2cu_wf_tag_dispatch（:23）
  warpRspValid : Bool     -- io.warpRsp.valid（单拍脉冲，D4/I-6）
  warpRspWid : BitVec 3   -- io.warpRsp.bits.wid（:42）
  wgIdLookup : BitVec 3   -- io.wg_id_lookup（:51）
  ctaRspReady : Bool      -- io.CTArsp.ready（下游 cta_scheduler 的 cu_wf_done.ready）

/-- CTAreq.ready（:56）：~idx_using.andR = 存在空闲 warp 槽 -/
def c2wReqReady (s : C2wState) : Bool := s.idxUsing != BitVec.allOnes 8

/-- idx_next_allocate（:59） -/
def c2wAllocIdx (s : C2wState) : BitVec 3 := c2wPriorityEnc (~~~s.idxUsing)

/-- CTAreq.fire -/
def c2wReqFire (s : C2wState) (i : C2wInputs) : Bool := i.ctaReqValid && c2wReqReady s

/-- warpRsp.fire = FIFO enq fire（:63,:73）：valid 且 FIFO 非满 -/
def c2wEnqFire (s : C2wState) (i : C2wInputs) : Bool :=
  i.warpRspValid && decide (s.fifo.length < 16)

/-- CTArsp.fire = FIFO deq fire（:76,:78）：非空且下游 ready -/
def c2wDeqFire (s : C2wState) (i : C2wInputs) : Bool :=
  decide (0 < s.fifo.length) && i.ctaRspReady

/-- CTArsp tag 的组合读出（:77）：**当前** data(队首 wid)（Q1 的机制核心） -/
def c2wRspTagOf (d : Fin 8 → BitVec 6) (f : List (BitVec 3)) : BitVec 6 :=
  match f with | [] => 0#6 | w :: _ => d (c2wFin w)

/-- 输出（组合，全读旧状态） -/
structure C2wOutputs where
  ctaReqReady : Bool      -- :56
  warpReqValid : Bool     -- :67（= CTAreq.fire，Q3）
  warpReqWid : BitVec 3   -- :69
  warpRspReady : Bool     -- :73 Queue enq.ready（:74 assert 的监控对象）
  ctaRspValid : Bool      -- :78
  ctaRspTag : BitVec 6    -- :77（出队时读 data(队首 wid)，Q1）
  wgIdTag : BitVec 6      -- :58

def c2wOut (s : C2wState) (i : C2wInputs) : C2wOutputs where
  ctaReqReady := c2wReqReady s
  warpReqValid := c2wReqFire s i
  warpReqWid := c2wAllocIdx s
  warpRspReady := decide (s.fifo.length < 16)
  ctaRspValid := decide (0 < s.fifo.length)
  ctaRspTag := c2wRspTagOf s.data s.fifo
  wgIdTag := s.data (c2wFin i.wgIdLookup)

theorem c2wOut_ctaRspTag (s : C2wState) (i : C2wInputs) :
    (c2wOut s i).ctaRspTag = c2wRspTagOf s.data s.fifo := rfl

/- ========================================================================= -/
/- 3. 单拍 step（全读旧值，D5）与多拍 run                                       -/
/- ========================================================================= -/

/-- idx_using（:63）：req 置位 | rsp 清除（清除胜；契约内两事件不撞槽，c2w1_no_clash） -/
def c2wStepIdx (u : BitVec 8) (allocIdx : BitVec 3) (reqFire : Bool)
    (rspFire : Bool) (rspWid : BitVec 3) : BitVec 8 :=
  (u ||| (if reqFire then 1#8 <<< allocIdx.zeroExtend 8 else 0#8)) &&&
  (if rspFire then ~~~(1#8 <<< rspWid.zeroExtend 8) else BitVec.allOnes 8)

/-- CTArsp_fifo（:73,:76）：先出队（旧队首）再入队（接队尾） -/
def c2wStepFifo (f : List (BitVec 3)) (enqFire deqFire : Bool) (w : BitVec 3) :
    List (BitVec 3) :=
  if enqFire then (if deqFire then f.tail else f) ++ [w]
  else (if deqFire then f.tail else f)

def c2wStep (s : C2wState) (i : C2wInputs) : C2wState where
  idxUsing := c2wStepIdx s.idxUsing (c2wAllocIdx s) (c2wReqFire s i)
                (c2wEnqFire s i) i.warpRspWid
  data := if c2wReqFire s i then rf_write s.data (c2wFin (c2wAllocIdx s)) i.ctaReqTag
          else s.data
  fifo := c2wStepFifo s.fifo (c2wEnqFire s i) (c2wDeqFire s i) i.warpRspWid

-- 投影引理（rfl）
theorem c2wStep_idxUsing (s : C2wState) (i : C2wInputs) :
    (c2wStep s i).idxUsing = c2wStepIdx s.idxUsing (c2wAllocIdx s) (c2wReqFire s i)
      (c2wEnqFire s i) i.warpRspWid := rfl
theorem c2wStep_data (s : C2wState) (i : C2wInputs) :
    (c2wStep s i).data = if c2wReqFire s i then
      rf_write s.data (c2wFin (c2wAllocIdx s)) i.ctaReqTag else s.data := rfl
theorem c2wStep_fifo (s : C2wState) (i : C2wInputs) :
    (c2wStep s i).fifo = c2wStepFifo s.fifo (c2wEnqFire s i) (c2wDeqFire s i)
      i.warpRspWid := rfl

/-- 多拍运行 -/
def c2wRun (s : C2wState) (ins : List C2wInputs) : C2wState := ins.foldl c2wStep s

/- ========================================================================= -/
/- 4. 数值回归测试（先测试；单拍 by decide，多拍轨迹 native_decide）            -/
/- ========================================================================= -/

section C2wRegressionTests

/-- 空输入 -/
def c2wInNop : C2wInputs :=
  { ctaReqValid := false, ctaReqTag := 0#6, warpRspValid := false, warpRspWid := 0#3,
    wgIdLookup := 0#3, ctaRspReady := false }

/-- CTA 派发请求（携带 wf_tag） -/
def c2wInReq (tag : BitVec 6) : C2wInputs := { c2wInNop with ctaReqValid := true, ctaReqTag := tag }

/-- warp 结束脉冲（warp_scheduler 单拍 valid，D4） -/
def c2wInRsp (wid : BitVec 3) (rdy : Bool) : C2wInputs :=
  { c2wInNop with warpRspValid := true, warpRspWid := wid, ctaRspReady := rdy }

/-- 下游消费一拍 -/
def c2wInConsume : C2wInputs := { c2wInNop with ctaRspReady := true }

-- T1 空闲分配：fire → idx_using 置位、warpReq 当拍发出、data 写入
def c2wT1s : C2wState := c2wStep c2wInit (c2wInReq 0x0A#6)
example : (c2wOut c2wInit (c2wInReq 0x0A#6)).warpReqValid = true := by decide
example : (c2wOut c2wInit (c2wInReq 0x0A#6)).warpReqWid = 0#3 := by decide
example : c2wT1s.idxUsing = 0b00000001#8 := by decide
example : c2wT1s.data (c2wFin 0#3) = 0x0A#6 := by decide
example : c2wT1s.fifo = [] := by decide

-- T2 全占用：ready=0 → 不 fire、warpReq 不 valid（Q3 的上游表现）
def c2wT2s : C2wState := { c2wInit with idxUsing := 0xFF#8 }
example : (c2wOut c2wT2s (c2wInReq 0x0A#6)).ctaReqReady = false := by decide
example : (c2wOut c2wT2s (c2wInReq 0x0A#6)).warpReqValid = false := by decide
example : (c2wStep c2wT2s (c2wInReq 0x0A#6)).idxUsing = 0xFF#8 := by decide

-- T3 最低空闲位优先：idx_using=0b0101 → 分配 wid=1
def c2wT3s : C2wState := { c2wInit with idxUsing := 0b00000101#8 }
example : (c2wOut c2wT3s (c2wInReq 0x0B#6)).warpReqWid = 1#3 := by decide
example : (c2wStep c2wT3s (c2wInReq 0x0B#6)).idxUsing = 0b00000111#8 := by decide

-- T4 响应路径：alloc wid0(tag 0x08) → endprg wid0（FIFO 入队、idx 位清除）
--     → 下一拍出队消费，tag 正确（0x08）
def c2wT4s1 : C2wState := c2wStep c2wInit (c2wInReq 0x08#6)
def c2wT4s2 : C2wState := c2wStep c2wT4s1 (c2wInRsp 0#3 false)
example : c2wT4s2.idxUsing = 0#8 := by decide
example : c2wT4s2.fifo = [0#3] := by decide
example : (c2wOut c2wT4s2 c2wInConsume).ctaRspValid = true := by decide
example : (c2wOut c2wT4s2 c2wInConsume).ctaRspTag = 0x08#6 := by decide
def c2wT4s3 : C2wState := c2wStep c2wT4s2 c2wInConsume
example : c2wT4s3.fifo = [] := by decide

-- T5 FIFO 顺序：wid 1、0 相继入队，按序出队，tag 各自查表
def c2wT5s0 : C2wState := c2wStep c2wInit (c2wInReq 0x20#6)        -- wid0 → tag 0x20
def c2wT5s1 : C2wState := c2wStep c2wT5s0 (c2wInReq 0x21#6)        -- wid1 → tag 0x21
def c2wT5s2 : C2wState := c2wStep c2wT5s1 (c2wInRsp 1#3 false)     -- 入队 wid1
def c2wT5s3 : C2wState := c2wStep c2wT5s2 (c2wInRsp 0#3 false)     -- 入队 wid0
example : c2wT5s3.fifo = [1#3, 0#3] := by decide
example : (c2wOut c2wT5s3 c2wInConsume).ctaRspTag = 0x21#6 := by decide  -- 先 wid1
def c2wT5s4 : C2wState := c2wStep c2wT5s3 c2wInConsume
example : (c2wOut c2wT5s4 c2wInConsume).ctaRspTag = 0x20#6 := by decide  -- 后 wid0

-- T6 I-6/Queue(16) 填满 witness（Q2）：8 warp 全部在跑 → 8 个 endprg 入队
-- （CTArsp 持续不消费）→ 8 个新 warp 复用槽位 → 再 8 个 endprg → FIFO 满 16。
-- 此后：第 17 个响应被**静默丢弃**，且对应 idx_using 位泄漏为 1。
def c2wFillIns : List C2wInputs :=
  ((List.range 8).map fun k => c2wInRsp (BitVec.ofNat 3 k) false) ++
  ((List.range 8).map fun _ => c2wInReq 0x30#6) ++
  ((List.range 8).map fun k => c2wInRsp (BitVec.ofNat 3 k) false)
def c2wT6full : C2wState := c2wRun { c2wInit with idxUsing := 0xFF#8 } c2wFillIns
example : c2wT6full.fifo.length = 16 := by native_decide
example : c2wT6full.idxUsing = 0#8 := by native_decide
example : (c2wOut c2wT6full (c2wInRsp 0#3 false)).warpRspReady = false := by native_decide
-- 满后继续：wid0 被复用（新 warp 分到槽 0），它 endprg 的响应被丢弃
def c2wT6alloc : C2wState := c2wStep c2wT6full (c2wInReq 0x31#6)
example : c2wT6alloc.idxUsing = 1#8 := by native_decide
def c2wT6drop : C2wState := c2wStep c2wT6alloc (c2wInRsp 0#3 false)
example : c2wT6drop.fifo.length = 16 := by native_decide                 -- 丢弃：FIFO 不变
example : ((c2wT6drop.idxUsing >>> 0) &&& 1#8) = 1#8 := by native_decide -- 槽 0 泄漏

-- T7 【I-23 候选 witness】tag 迟读污染（Q1）：
--   拍1: CTAreq 派发 WG A 的 warp（wid0，tag=0b001000=0x08，slot1/wf0）
--   拍2: warp0 endprg（响应入队；CTArsp 反压不消费）
--   拍3: wid0 被 WG B 复用（tag=0b010001=0x11，slot2/wf1），data(0) 被覆写
--   拍4: 消费旧响应 —— 读到的 tag 是 0x11（WG B 的），不是 0x08（WG A 的）
def c2wT7s1 : C2wState := c2wStep c2wInit (c2wInReq 0x08#6)
def c2wT7s2 : C2wState := c2wStep c2wT7s1 (c2wInRsp 0#3 false)
def c2wT7s3 : C2wState := c2wStep c2wT7s2 (c2wInReq 0x11#6)
example : (c2wOut c2wT7s3 c2wInConsume).ctaRspValid = true := by native_decide
example : (c2wOut c2wT7s3 c2wInConsume).ctaRspTag = 0x11#6 := by native_decide  -- ≠ 0x08：污染
-- 对照：拍3 若立即消费（复用当拍的写尚未生效），tag 正确
example : (c2wOut c2wT7s2 c2wInConsume).ctaRspTag = 0x08#6 := by native_decide

-- T8 同拍 req+rsp（不同 wid）：各自动作都生效（c2w1_no_clash 的数值版）
def c2wT8s0 : C2wState := c2wStep c2wInit (c2wInReq 0x08#6)          -- wid0 占用
def c2wT8in : C2wInputs := { c2wInReq 0x09#6 with warpRspValid := true, warpRspWid := 0#3 }
def c2wT8s1 : C2wState := c2wStep c2wT8s0 c2wT8in                    -- 同拍：清 wid0、置 wid1
example : c2wT8s1.idxUsing = 0b00000010#8 := by decide
example : c2wT8s1.fifo = [0#3] := by decide
example : c2wT8s1.data (c2wFin 1#3) = 0x09#6 := by decide

-- T9 同拍出队+入队：FIFO 头 wid5 出队（其 idx_using 位在入队时已清），
-- 同拍新响应 wid7 入队（清 bit7）
def c2wT9base : C2wState :=
  { idxUsing := 0b10000000#8, data := rf_write (rf_zero 8 6) (c2wFin 5#3) 0x25#6,
    fifo := [5#3] }
def c2wT9in : C2wInputs := c2wInRsp 7#3 true
def c2wT9s1 : C2wState := c2wStep c2wT9base c2wT9in
example : (c2wOut c2wT9base c2wT9in).ctaRspTag = 0x25#6 := by decide -- 出队的是 wid5 的 tag
example : c2wT9s1.fifo = [7#3] := by decide
example : ((c2wT9s1.idxUsing >>> 5) &&& 1#8) = 0#8 := by decide      -- wid5 清除
example : ((c2wT9s1.idxUsing >>> 7) &&& 1#8) = 0#8 := by decide      -- wid7 本就不占

-- T10 wg_id_tag 组合查表（:58）
example : (c2wOut c2wT9base { c2wInNop with wgIdLookup := 5#3 }).wgIdTag = 0x25#6 := by decide

end C2wRegressionTests

/- ========================================================================= -/
/- 5. 契约定理（后证明）                                                      -/
/- ========================================================================= -/

/-- C2W1a 分配索引指向空闲位（前提：有空闲位；fire 时由 :56 ready 保证） -/
theorem c2w1_alloc_idx_clear (u : BitVec 8) (h : u ≠ BitVec.allOnes 8) :
    ((u >>> (c2wPriorityEnc (~~~u)).zeroExtend 8) &&& 1#8) = 0#8 := by
  unfold c2wPriorityEnc; bv_decide

/-- C2W1b 分配索引是**最低**空闲位：所有更低编号位均被占用 -/
theorem c2w1_alloc_idx_min (u : BitVec 8) (h : u ≠ BitVec.allOnes 8) :
    (u &&& ((1#8 <<< (c2wPriorityEnc (~~~u)).zeroExtend 8) - 1#8)) =
      ((1#8 <<< (c2wPriorityEnc (~~~u)).zeroExtend 8) - 1#8) := by
  unfold c2wPriorityEnc; bv_decide

/-- C2W1c 同拍 alloc/rsp 不撞槽（:63 的清除覆盖置位路径不可达）：
    响应的 wid 在册（idx_using 位=1）且有空闲位时，分配索引 ≠ 响应 wid。
    前提即环境契约"warp_scheduler 只为在册 warp 发响应"（wid 由本模块分配）。 -/
theorem c2w1_alloc_rsp_no_clash (u : BitVec 8) (w : BitVec 3)
    (h : u ≠ BitVec.allOnes 8) (hw : ((u >>> w.zeroExtend 8) &&& 1#8) = 1#8) :
    c2wPriorityEnc (~~~u) ≠ w := by
  unfold c2wPriorityEnc; bv_decide

/-- C2W2a 分配后置位（:63 的左半） -/
theorem c2w2_alloc_sets (u : BitVec 8) :
    (((u ||| (1#8 <<< (c2wPriorityEnc (~~~u)).zeroExtend 8)) >>>
      (c2wPriorityEnc (~~~u)).zeroExtend 8) &&& 1#8) = 1#8 := by
  unfold c2wPriorityEnc; bv_decide

/-- C2W2b 响应后清除（:63 的右半） -/
theorem c2w2_rsp_clears (u : BitVec 8) (w : BitVec 3) :
    (((u &&& ~~~(1#8 <<< w.zeroExtend 8)) >>> w.zeroExtend 8) &&& 1#8) = 0#8 := by
  bv_decide

/-- C2W2c 置位单调：已占用的位不会被分配动作清除 -/
theorem c2w2_set_preserves (u m : BitVec 8) (k : BitVec 3)
    (hk : ((u >>> k.zeroExtend 8) &&& 1#8) = 1#8) :
    (((u ||| m) >>> k.zeroExtend 8) &&& 1#8) = 1#8 := by
  bv_decide

/-- C2W3 FIFO 满 ⇒ idx_using 只增不减（:63 的清除项等 fire，满即不 fire）——
    槽位泄漏的单拍形式 -/
theorem c2w3_step_full_idx_mono (s : C2wState) (i : C2wInputs) (hf : s.fifo.length = 16)
    (k : BitVec 3) (hk : ((s.idxUsing >>> k.zeroExtend 8) &&& 1#8) = 1#8) :
    (((c2wStep s i).idxUsing >>> k.zeroExtend 8) &&& 1#8) = 1#8 := by
  obtain ⟨u, d, f⟩ := s
  replace hk : ((u >>> k.zeroExtend 8) &&& 1#8) = 1#8 := hk
  have hf' : f.length = 16 := hf
  have hfire : c2wEnqFire ⟨u, d, f⟩ i = false := by simp [c2wEnqFire, hf']
  rw [c2wStep_idxUsing]
  unfold c2wStepIdx
  simp only [hfire, Bool.false_eq_true, if_false]
  by_cases hc : c2wReqFire ⟨u, d, f⟩ i = true
  · simp only [hc, if_true]
    generalize c2wAllocIdx ⟨u, d, f⟩ = a
    bv_decide
  · simp only [hc, Bool.false_eq_true, if_false]
    bv_decide

/-- C2W4 FIFO 满 + CTArsp 永不消费 ⇒ 任意长运行后：FIFO 保持满、idx_using
    已置位的位永不清除（槽位泄漏不可恢复；配合 c2w6 即 I-6 后果链的 CTA2warp 侧） -/
theorem c2w4_full_stuck_run (s : C2wState) (ins : List C2wInputs)
    (hf : s.fifo.length = 16) (hnr : ∀ x ∈ ins, x.ctaRspReady = false) :
    (c2wRun s ins).fifo.length = 16 ∧
      ∀ k : BitVec 3, ((s.idxUsing >>> k.zeroExtend 8) &&& 1#8) = 1#8 →
        (((c2wRun s ins).idxUsing >>> k.zeroExtend 8) &&& 1#8) = 1#8 := by
  induction ins generalizing s with
  | nil => exact ⟨hf, fun _ h => h⟩
  | cons x xs ih =>
    have hxr : x.ctaRspReady = false := hnr x List.mem_cons_self
    have hdeq : c2wDeqFire s x = false := by simp [c2wDeqFire, hxr]
    have henq : c2wEnqFire s x = false := by simp [c2wEnqFire, hf]
    have hfifo1 : (c2wStep s x).fifo.length = 16 := by
      rw [c2wStep_fifo]; simp [c2wStepFifo, hdeq, henq, hf]
    obtain ⟨h1, h2⟩ := ih (c2wStep s x) hfifo1 (fun y hy => hnr y (List.mem_cons_of_mem x hy))
    exact ⟨h1, fun k hk => h2 k (c2w3_step_full_idx_mono s x hf k hk)⟩

/-- C2W5a FIFO 容量不变式：任何单拍后长度仍 ≤ 16 -/
theorem c2w5_step_fifo_bound (s : C2wState) (i : C2wInputs) (hb : s.fifo.length ≤ 16) :
    (c2wStep s i).fifo.length ≤ 16 := by
  rw [c2wStep_fifo]
  by_cases hd : c2wDeqFire s i = true <;> by_cases he : c2wEnqFire s i = true
  · have hpos : 0 < s.fifo.length := by
      simp [c2wDeqFire, Bool.and_eq_true] at hd; exact hd.1
    have hlt : s.fifo.length < 16 := by
      simp [c2wEnqFire, Bool.and_eq_true] at he; exact he.2
    rw [c2wStepFifo, if_pos he, if_pos hd, List.length_append, List.length_tail,
      List.length_cons, List.length_nil]
    omega
  · have hpos : 0 < s.fifo.length := by
      simp [c2wDeqFire, Bool.and_eq_true] at hd; exact hd.1
    rw [c2wStepFifo, if_neg he, if_pos hd, List.length_tail]
    omega
  · have hlt : s.fifo.length < 16 := by
      simp [c2wEnqFire, Bool.and_eq_true] at he; exact he.2
    rw [c2wStepFifo, if_pos he, if_neg hd, List.length_append, List.length_cons,
      List.length_nil]
    omega
  · rw [c2wStepFifo, if_neg he, if_neg hd]; exact hb

/-- C2W5b 填充记账：长度变化 = 入队数 − 出队数（"填满条件"的精确形式：
    净增 16 个未消费响应即满） -/
theorem c2w5_fifo_len_delta (s : C2wState) (i : C2wInputs) (hb : s.fifo.length ≤ 16) :
    (c2wStep s i).fifo.length =
      s.fifo.length + (if c2wEnqFire s i then 1 else 0) - (if c2wDeqFire s i then 1 else 0) := by
  rw [c2wStep_fifo]
  by_cases hd : c2wDeqFire s i = true <;> by_cases he : c2wEnqFire s i = true
  · have hpos : 0 < s.fifo.length := by
      simp [c2wDeqFire, Bool.and_eq_true] at hd; exact hd.1
    rw [c2wStepFifo, if_pos he, if_pos hd, List.length_append, List.length_tail,
      List.length_cons, List.length_nil, if_pos he, if_pos hd]
    omega
  · have hpos : 0 < s.fifo.length := by
      simp [c2wDeqFire, Bool.and_eq_true] at hd; exact hd.1
    rw [c2wStepFifo, if_neg he, if_pos hd, List.length_tail, if_neg he, if_pos hd]
    omega
  · rw [c2wStepFifo, if_pos he, if_neg hd, List.length_append, List.length_cons,
      List.length_nil, if_pos he, if_neg hd]
    omega
  · rw [c2wStepFifo, if_neg he, if_neg hd, if_neg he, if_neg hd]
    omega

/-- C2W6 响应丢弃判据（Q2/I-6）：valid 的响应被丢弃 ⟺ FIFO 满 -/
theorem c2w6_rsp_dropped_iff_full (s : C2wState) (i : C2wInputs) (hb : s.fifo.length ≤ 16)
    (hv : i.warpRspValid = true) :
    c2wEnqFire s i = false ↔ s.fifo.length = 16 := by
  constructor
  · intro hf
    unfold c2wEnqFire at hf
    rw [hv] at hf
    simp at hf
    omega
  · intro hf
    unfold c2wEnqFire
    rw [hv, hf]
    decide

/-- C2W7a tag 读出机制（Q1，:77）：出队响应携带的是**当前** data(队首 wid)，
    而非该 warp 分配时写入的 tag -/
theorem c2wOut_tag_cons (u : BitVec 8) (d : Fin 8 → BitVec 6) (w : BitVec 3)
    (ws : List (BitVec 3)) (i : C2wInputs) :
    (c2wOut ⟨u, d, w :: ws⟩ i).ctaRspTag = d (c2wFin w) := rfl

/-- C2W7b tag 安全的充分条件（Q1 边界）：响应入队后**一拍内**消费必正确——
    入队当拍若有新分配，写的是别的槽（c2w1_no_clash，前提：响应 wid 在册）；
    下一拍的分配写下下拍才生效。T7 表明滞留 ≥2 拍即可被污染。 -/
theorem c2w7_tag_safe_next_cycle (u : BitVec 8) (d : Fin 8 → BitVec 6)
    (i1 i2 : C2wInputs)
    (hbit : ((u >>> i1.warpRspWid.zeroExtend 8) &&& 1#8) = 1#8)
    (hrsp : c2wEnqFire ⟨u, d, []⟩ i1 = true)
    (hdeq : c2wDeqFire (c2wStep ⟨u, d, []⟩ i1) i2 = true) :
    (c2wOut (c2wStep ⟨u, d, []⟩ i1) i2).ctaRspTag = d (c2wFin i1.warpRspWid) := by
  have hdeq1 : c2wDeqFire ⟨u, d, []⟩ i1 = false := by simp [c2wDeqFire]
  have hfifo : (c2wStep ⟨u, d, []⟩ i1).fifo = [i1.warpRspWid] := by
    rw [c2wStep_fifo]; simp [c2wStepFifo, hdeq1, hrsp]
  have hdata : (c2wStep ⟨u, d, []⟩ i1).data (c2wFin i1.warpRspWid) =
      d (c2wFin i1.warpRspWid) := by
    rw [c2wStep_data]
    by_cases hr : c2wReqFire ⟨u, d, []⟩ i1 = true
    · rw [if_pos hr]
      have hready : u ≠ BitVec.allOnes 8 := by
        simp only [c2wReqFire, c2wReqReady, Bool.and_eq_true, bne_iff_ne] at hr
        exact hr.2
      have hne : c2wFin (c2wAllocIdx ⟨u, d, []⟩) ≠ c2wFin i1.warpRspWid := by
        intro heq
        exact c2w1_alloc_rsp_no_clash u i1.warpRspWid hready hbit (c2wFin_inj heq)
      exact rf_read_write_diff d _ _ _ hne
    · rw [if_neg hr]
  rw [c2wOut_ctaRspTag, hfifo]
  exact hdata

/- ========================================================================= -/
/- 6. FIFO 精化：Queue(16) ⊑ AQueue 16（QueueModel 框架）                       -/
/- ========================================================================= -/

section C2wFifoRefinement

/-- 深 16 FIFO 的状态（内容 + 容量界证明） -/
structure C2wFifo where
  items : List (BitVec 3)
  bounded : items.length ≤ 16

def c2wFifoAbs (f : C2wFifo) : AQueue (BitVec 3) 16 := ⟨f.items, f.bounded⟩

/-- FIFO 的单拍输入（D2/D4） -/
structure C2wFifoIn where
  enqValid : Bool      -- io.warpRsp.valid
  wid : BitVec 3
  deqReady : Bool      -- io.CTArsp.ready

/-- 单拍行为（函数形式）：(本拍出队输出, 新内容)。
    enq/deq 接受条件都只看旧长度（chisel Queue 无同拍旁路，D2）。 -/
def c2wFifoStepF (inp : C2wFifoIn) (f : C2wFifo) : Option (BitVec 3) × List (BitVec 3) :=
  ((if decide (0 < f.items.length) && inp.deqReady then f.items.head? else none),
   if inp.enqValid && decide (f.items.length < 16) then
     (if decide (0 < f.items.length) && inp.deqReady then f.items.tail else f.items) ++ [inp.wid]
   else
     (if decide (0 < f.items.length) && inp.deqReady then f.items.tail else f.items))

/-- 单步关系（Simulates 框架要求的关系形式） -/
def c2wFifoStepR (inp : C2wFifoIn) (f : C2wFifo) (out : Option (BitVec 3))
    (f' : C2wFifo) : Prop :=
  c2wFifoStepF inp f = (out, f'.items)

/-- C2W8 FIFO 单步模拟：具体实现对抽象 AQueue 的逐步精化。
    标签选择：同拍出入 → enqDeq（**仅当旧队列非满**——满时同拍 enq 被拒，
    与 D2 一致，此时只对应 deq 标签）。多步性质由 simulates_steps 免费获得。 -/
theorem c2wFifo_simulates (inp : C2wFifoIn) :
    Simulates c2wFifoAbs (c2wFifoStepR inp) := by
  intro s s' out h
  unfold c2wFifoStepR c2wFifoStepF at h
  by_cases he : (inp.enqValid && decide (s.items.length < 16)) = true
  · by_cases hd : (decide (0 < s.items.length) && inp.deqReady) = true
    · -- 同拍出入（旧队列非满非空）→ AOp.enqDeq
      simp only [he, hd, if_true] at h
      obtain ⟨hout, hitems⟩ := Prod.mk.inj h
      have hlt : s.items.length < 16 := of_decide_eq_true ((Bool.and_eq_true _ _).mp he).2
      have hpos : 0 < s.items.length := of_decide_eq_true ((Bool.and_eq_true _ _).mp hd).1
      obtain ⟨y, q', hrun, hcnt, ys, h1, h2⟩ :=
        (c2wFifoAbs s).enqDeq_success inp.wid hpos
      have h1' : s.items = y :: ys := h1
      have h2' : q'.items = ys ++ [inp.wid] := h2
      have hout' : out = some y := by rw [← hout, h1']; rfl
      have hstate : c2wFifoAbs s' = q' := by
        apply AQueue.ext
        show s'.items = q'.items
        rw [← hitems, h2', h1']
        rfl
      refine ⟨.enqDeq inp.wid, ?_⟩
      rw [aStep_enqDeq hrun, hout', hstate]
    · -- 只入队 → AOp.enq
      simp only [he, hd, if_true, Bool.false_eq_true, if_false] at h
      obtain ⟨hout, hitems⟩ := Prod.mk.inj h
      have hlt : s.items.length < 16 := of_decide_eq_true ((Bool.and_eq_true _ _).mp he).2
      obtain ⟨q', henq, hitems', hcnt⟩ := (c2wFifoAbs s).enq_success inp.wid hlt
      have hout' : out = none := hout.symm
      have hstate : c2wFifoAbs s' = q' := by
        apply AQueue.ext
        show s'.items = q'.items
        rw [← hitems, hitems']
        rfl
      refine ⟨.enq inp.wid, ?_⟩
      rw [aStep_enq henq, hout', hstate]
  · by_cases hd : (decide (0 < s.items.length) && inp.deqReady) = true
    · -- 只出队（含"满时同拍 enq 被拒"的情形）→ AOp.deq
      simp only [he, hd, if_true, Bool.false_eq_true, if_false] at h
      obtain ⟨hout, hitems⟩ := Prod.mk.inj h
      have hpos : 0 < s.items.length := of_decide_eq_true ((Bool.and_eq_true _ _).mp hd).1
      obtain ⟨y, q', hdeq, h1, hcnt⟩ := (c2wFifoAbs s).deq_success hpos
      have h1' : s.items = y :: q'.items := h1
      have hout' : out = some y := by rw [← hout, h1']; rfl
      have hstate : c2wFifoAbs s' = q' := by
        apply AQueue.ext
        show s'.items = q'.items
        rw [← hitems, h1']
        rfl
      refine ⟨.deq, ?_⟩
      rw [aStep_deq hdeq, hout', hstate]
    · -- 空转 → AOp.skip
      simp only [he, hd, Bool.false_eq_true, if_false] at h
      obtain ⟨hout, hitems⟩ := Prod.mk.inj h
      have hout' : out = none := hout.symm
      have hstate : c2wFifoAbs s' = c2wFifoAbs s := by
        apply AQueue.ext
        show s'.items = s.items
        rw [← hitems]
      refine ⟨.skip, ?_⟩
      rw [aStep_skip, hout', hstate]

end C2wFifoRefinement

/- 公理审计（bv_decide 定理各带私有 LRAT trust 公理；native_decide 测试
   额外引入 Lean.ofReduceBool，归档注明） -/
#print axioms c2w1_alloc_idx_clear
#print axioms c2w1_alloc_rsp_no_clash
#print axioms c2w2_rsp_clears
#print axioms c2w3_step_full_idx_mono
#print axioms c2w4_full_stuck_run
#print axioms c2w6_rsp_dropped_iff_full
#print axioms c2w7_tag_safe_next_cycle
#print axioms c2wFifo_simulates

end Ventus.CTA
