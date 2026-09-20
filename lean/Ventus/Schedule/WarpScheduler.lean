/- ========================================================================= -/
/-                     Schedule/WarpScheduler.lean                            -/
/-  warp 调度器（warp_scheduler）的 Lean 4 模型与调度/barrier/CTA 簿记契约      -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/warp_schedule.scala -/
/-    （class warp_scheduler，全文 222 行）                                    -/
/-  参数（top/parameters.scala）：num_warp=8 (:8)、num_block=8 (:53)、          -/
/-    num_warp_in_a_block=8 (:55)、depth_warp=3 (:30)、WF_ID_WIDTH=3、          -/
/-    TAG_WIDTH = log2Ceil(8)+log2Ceil(8) = 6 (:153,:187-188)、               -/
/-    SINGLE_INST=false (:10)、MMU_ENABLED=false (:15)、GVM_ENABLED 默认 off。  -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  M1. PCcontrol（:78-100,:194-219）不建模内部，每 warp 的 PC 视为不透明；    -/
/-      本文件只建模 pc_req 的 valid/warpid。io.pc_req.bits.addr/mask 跳过。   -/
/-  M2. MMU_ENABLED=false（:63-70 asid 整段不生成）；GVM_ENABLED 默认 false    -/
/-      （:142-153 GvmDutBarrierDone 不建模）；SINGLE_INST=false（:190 的      -/
/-      next_warp:=0 不生效）。SPIKE/GVM 调试通路全部忽略。                   -/
/-  M3. pc_ibuffer_ready(i) 在源码是 UInt(depth_ibuffer.W)（:33），:184 做     -/
/-      `UInt & Bool` 再赋给 Bool wire。本模型将其抽象为"每 warp 一个 Bool"， -/
/-      以 BitVec 8 输入（bit i = warp i 的 ibuffer 就绪）。源码该表达式的     -/
/-      精确位语义（UInt 与 Bool 位与后截断）存疑，记为观察项 Q3，上报主会话。 -/
/-  M4. Chisel 语义关键：对 Reg 的读一律读"旧值"（时钟沿前的值），同一拍内对   -/
/-      同一寄存器（元素）的多次 `:=` 后写覆盖先写（last connect wins），且    -/
/-      后写的 RHS 仍读旧值。本模型所有 step 函数严格遵守：每个更新表达式的    -/
/-      读侧一律用旧状态字段，多次写用"先写结果为底、后写覆盖同索引"的链式     -/
/-      更新实现（如 wsStepCnt/wsStepBelong 中第二笔写以第一笔结果为底、       -/
/-      值却从旧数组读出）。                                                   -/
/-  M5. CTA2csr（:58-59）是 warpReq 的纯转发，不建模。wg_id_lookup（:103）的   -/
/-      Mux 两分支同为 warp_end_id（warpRsp.bits.wid := warp_end_id，:56），   -/
/-      冗余 mux，输出直接建模为 wcWid（观察项 Q2）。                          -/
/-  M6. OHToUInt（:168）按 Chisel 语义建模为"置位索引的按位或"：结果第 j 位   -/
/-      = 所有索引第 j 位为 1 的置位项之或。非 one-hot 输入时输出为索引按位或 -/
/-      （如 {1,2} → 3），这是 I-5 的核心。                                   -/
/-  M7. warpRsp 是 Decoupled（:22），fire 需要下游 ready；源码 :55 注释        -/
/-      "always ready" 是假设而非保证。本模型把 warpRsp.ready 作为输入，       -/
/-      以便刻画 ready 被拉低时的行为（见疑点 I-6）。                          -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1 = I-5（任务书编号）：mask_0 非 one-hot 时 flush_entry = OHToUInt 输出   -/
/-      各置位索引的按位或，可能落在 mask_0 未置位的索引上，导致 :169 的清除   -/
/-      条件永假、valid 位卡死。本文件 WS4 系列定理 + T6 测试证实。           -/
/-  Q2. :103 wg_id_lookup 的 Mux 两分支都是 warp_end_id（冗余），无功能影响。 -/
/-  Q3. :184 `io.pc_ibuffer_ready(i) & warp_active(i)` 是 UInt(depth_ibuffer) -/
/-      与 Bool 的位与再赋 Bool wire，精确语义依赖 Chisel 的 UInt/Bool 位与   -/
/-      与截断规则；若按"取结果最低位"理解，pc_ibuffer_ready 为偶数值（如 2） -/
/-      时会被误判为不就绪。本模型按"非零即就绪"的布尔抽象处理（M3）。        -/
/-  Q4 = I-6（新）：warpRsp 握手违规。:55 warpRsp.valid := warp_end 只维持    -/
/-      单拍（warp_end 是 warp_control.fire 的脉冲），而 :131/:161 的          -/
/-      belong/cnt 清除以 warpRsp.fire 为条件。若下游拉低 ready，响应永久丢   -/
/-      失：warp_active 已被 :180 清除（它用 warp_end 而非 rsp.fire），但      -/
/-      cnt/belong 位永远清不掉 → 该 wg 的 lock 卡死（exp 永不重初始化）、     -/
/-      mask_0 永不置位（flush 永不发出）。旁证：CTA2warp.scala:71-74 开发者   -/
/-      自己的 TODO + assert(io.warpRsp.ready)（"FIFO is used to satisfy it,  -/
/-      but not enough"——深度 16 的 Queue 填满即出事）。本文件 T8 测试给出     -/
/-      witness。需主会话核实 CTA2warp 深度 16 FIFO 是否可能填满。            -/
/-  Q5 = I-7（新）：同拍 warpReq 与 warpRsp 打到同一 wg（wg 有多个 warp，一   -/
/-      个 endprg 的同拍 CTA 又派发新 warp 进同槽）：:123-134 与 :157-163 中   -/
/-      rsp 的清除是后写，整体覆盖 req 的置位（last connect wins，M4），新    -/
/-      warp 的 belong/cnt 位丢失。后果：cnt 少计 → wg 尚有活跃 warp 时       -/
/-      mask_0 提前置位 → 提前 flushDCache；belong 少计 → lock 提前掉落 →     -/
/-      下个 warpReq 重初始化 exp/cur；更严重的是 barrier 释放时 :141 按       -/
/-      belong 清 data，新 warp 若已 barrier 等待，其 data 位清不掉 → 永久    -/
/-      不 ready（死锁）。本文件 T7 测试给出 belong/cnt 位丢失的 witness。    -/
/-  Q6. :180 warp_active 同拍 req 置位 + warp_end 清除同一 wid 时清除胜       -/
/-      （&~ 在 | 之后），与 M4 一致，无异常，仅记录。                         -/
/-                                                                           -/
/- ======================== D 区：工程性偏离（非源码语义） ==================== -/
/-  D1. WsState 的 per-wg 寄存器原为 `Fin 8 → …` 函数字段（rf_write 闭包链）。 -/
/-      第 16 波实测：函数值状态字段跨拍经组合链互相重入，SM 整机模拟原生执行  -/
/-      指数级（拍 6→8：60ms→335ms→2522ms）。本波（第 17 波）将全部 5 个       -/
/-      函数字段 Array 化（`Array (BitVec 8)` / `Array Bool`，定长 8），读用   -/
/-      `Array.getD`、写用 `Array.setIfInBounds`——每拍构造时逐元素求值并共享  -/
/-      堆对象，切断跨拍闭包链。**无函数值状态字段残留**（currentWarp/        -/
/-      warpActive/barData 本就是扁平 BitVec）。行为保持：对外访问经同名       -/
/-      访问器（`s.barCur`/`s.wgValid` 等仍是 `Fin 8 → …` 视图），全部既有     -/
/-      定理陈述语义不变；wsStepCnt 等 step 函数签名改为 Array（内部实现）。   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Schedule

set_option linter.unusedVariables false

open Ventus.Base

/- ========================================================================= -/
/- 1. 常量与位切片辅助                                                        -/
/- ========================================================================= -/

/-- BitVec 3 索引转 Fin 8（depth_warp=3, num_warp=8） -/
def wsFin (x : BitVec 3) : Fin 8 := ⟨x.toNat, by have h := x.isLt; omega⟩

/-- end_wg_id = wg_id_tag[5:3]（:117，TAG_WIDTH=6, WF_ID_WIDTH=3） -/
def wsEndWgId (tag : BitVec 6) : BitVec 3 := tag.extractLsb' 3 3

/-- end_wf_id = wg_id_tag[2:0]（:118） -/
def wsEndWfId (tag : BitVec 6) : BitVec 3 := tag.extractLsb' 0 3

/-- exp 初始化值（:128）：(1 << wf_count) - 1，赋给 8 位寄存器。
    Chisel 中 1.U << count 会加宽再在赋值时截断回 8 位；count ≥ 8 时
    (1<<count)-1 ≡ 255 (mod 256)，与 BitVec 8 中 1<<<count = 0、0-1 = 255 一致。 -/
def wsExpInit (count : BitVec 4) : BitVec 8 := (1#8 <<< count.zeroExtend 8) - 1#8

/-- OHToUInt（:168，M6）：结果第 j 位 = 索引第 j 位为 1 的所有置位项之或 -/
def wsOHToUInt (m : BitVec 8) : BitVec 3 :=
  let b : Nat → Bool := fun i => (m >>> i) &&& 1#8 == 1#8
  (if b 4 || b 5 || b 6 || b 7 then 4#3 else 0#3) |||
  (if b 2 || b 3 || b 6 || b 7 then 2#3 else 0#3) |||
  (if b 1 || b 3 || b 5 || b 7 then 1#3 else 0#3)

/- ========================================================================= -/
/- 2. 状态、输入、输出                                                        -/
/- ========================================================================= -/

/-- warp_scheduler 的全部寄存器状态（:49,:105-108,:119-120,:176）。
    per-wg 寄存器（Vec(num_block, ·)）建模为定长 8 的 `Array`（D1：原为
    `Fin 8 → BitVec 8` / `Fin 8 → Bool` 函数字段，Array 化消除跨拍闭包链
    求值爆炸）；函数视图由同名访问器（见下）提供，定理陈述不受影响。 -/
structure WsState where
  currentWarp : BitVec 3              -- :49 current_warp
  warpActive  : BitVec 8              -- :176 warp_active
  barCurArr      : Array (BitVec 8)   -- :105 warp_bar_cur（每 wg 已到达 barrier 的 wf 集合）
  barExpArr      : Array (BitVec 8)   -- :106 warp_bar_exp（期望到达集合）
  barBelongArr   : Array (BitVec 8)   -- :120 warp_bar_belong（wg 含哪些 warp）
  barData     : BitVec 8              -- :119 warp_bar_data（哪些 warp 在 barrier 等待）
  endprgCntArr   : Array (BitVec 8)   -- :107 warp_endprg_cnt（wg 内未 endprg 的 warp）
  wgValidArr     : Array Bool         -- :108 warp_wg_valid

/-- Array 读（对应 rf_read）。越界返回默认值——WsState 不变式 size = 8，
    健康状态下永不越界；越界语义只影响病态状态的泛化定理形态，不影响任何
    从 wsInit 出发的可达状态。 -/
def wsRd8 (a : Array (BitVec 8)) (i : Fin 8) : BitVec 8 := a.getD i.val 0#8
def wsRdB (a : Array Bool) (i : Fin 8) : Bool := a.getD i.val false

/-- Array 写（对应 rf_write）。越界时返回原数组（setIfInBounds 语义），
    size = 8 时不发生。 -/
def wsWr8 (a : Array (BitVec 8)) (i : Fin 8) (v : BitVec 8) : Array (BitVec 8) :=
  a.setIfInBounds i.val v
def wsWrB (a : Array Bool) (i : Fin 8) (v : Bool) : Array Bool :=
  a.setIfInBounds i.val v

/-- 写后读（同索引）：界内读到新值；越界时写无效、读到默认值 -/
theorem wsRd8_wr8_self (a : Array (BitVec 8)) (i : Fin 8) (v : BitVec 8) :
    wsRd8 (wsWr8 a i v) i = (if i.val < a.size then v else 0#8) := by
  simp [wsRd8, wsWr8, Array.getD_eq_getD_getElem?]

theorem wsRdB_wrB_self (a : Array Bool) (i : Fin 8) (v : Bool) :
    wsRdB (wsWrB a i v) i = (if i.val < a.size then v else false) := by
  simp [wsRdB, wsWrB, Array.getD_eq_getD_getElem?]

/-- 写后读（异索引）：不受影响（无条件成立，size 保持） -/
theorem wsRd8_wr8_of_ne (a : Array (BitVec 8)) {i j : Fin 8} (v : BitVec 8) (h : i ≠ j) :
    wsRd8 (wsWr8 a i v) j = wsRd8 a j := by
  have hv : i.val ≠ j.val := fun hc => h (Fin.ext hc)
  simp [wsRd8, wsWr8, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hv]

theorem wsRdB_wrB_of_ne (a : Array Bool) {i j : Fin 8} (v : Bool) (h : i ≠ j) :
    wsRdB (wsWrB a i v) j = wsRdB a j := by
  have hv : i.val ≠ j.val := fun hc => h (Fin.ext hc)
  simp [wsRdB, wsWrB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hv]

/-- 状态投影访问器：保持原函数字段的名称与语义（D1），实现为 Array + getD。
    所有既有定理/测试中的 `s.barCur j`、`s.wgValid j` 等写法原样有效。 -/
def WsState.barCur    (s : WsState) : Fin 8 → BitVec 8 := fun j => wsRd8 s.barCurArr j
def WsState.barExp    (s : WsState) : Fin 8 → BitVec 8 := fun j => wsRd8 s.barExpArr j
def WsState.barBelong (s : WsState) : Fin 8 → BitVec 8 := fun j => wsRd8 s.barBelongArr j
def WsState.endprgCnt (s : WsState) : Fin 8 → BitVec 8 := fun j => wsRd8 s.endprgCntArr j
def WsState.wgValid   (s : WsState) : Fin 8 → Bool      := fun j => wsRdB s.wgValidArr j

/-- RegInit 全 0（:49,:105-108,:119-120,:176） -/
def wsInit : WsState :=
  { currentWarp := 0#3, warpActive := 0#8
    barCurArr := Array.replicate 8 0#8, barExpArr := Array.replicate 8 0#8
    barBelongArr := Array.replicate 8 0#8, barData := 0#8
    endprgCntArr := Array.replicate 8 0#8, wgValidArr := Array.replicate 8 false }

/-- 输入（只含本模型消费的字段；PCcontrol/ICTA 数据字段按 M1/M5 略去） -/
structure WsInputs where
  warpReqFire      : Bool      -- :123 io.warpReq.fire（warpReq.ready 恒 true，:54）
  reqWid           : BitVec 3  -- :61 new_warpid
  newWgId          : BitVec 3  -- :114 tag[5:3]
  newWfCount       : BitVec 4  -- :116 dispatch2cu_wg_wf_count
  warpControlFire  : Bool      -- io.warp_control.fire
  simtStackOp      : Bool      -- io.warp_control.bits.ctrl.simt_stack_op
  wcWid            : BitVec 3  -- :48 warp_end_id = warp_control.bits.ctrl.wid
  wgIdTag          : BitVec 6  -- :24 io.wg_id_tag（[5:3]=end_wg_id, [2:0]=end_wf_id）
  warpRspReady     : Bool      -- 下游 ready（M7，:55 的 "always ready" 假设）
  scoreboardBusy   : BitVec 8  -- :30
  exeBusy          : BitVec 8  -- :31
  pcIbufRdy        : BitVec 8  -- :33 的布尔抽象（M3）
  flushDCacheReady : Bool      -- :41
  branchFire       : Bool      -- :73 io.branch.fire
  branchJump       : Bool      -- :73 io.branch.bits.jump
  branchWid        : BitVec 3  -- :74 io.branch.bits.wid
  pcRspValid       : Bool      -- :75
  pcRspMiss        : Bool      -- :75 pc_rsp.bits.status(0)
  pcRspWid         : BitVec 3  -- :76
  pcReset          : Bool      -- :218

/-- 派生条件 -/
def wsWarpEnd (i : WsInputs) : Bool := i.warpControlFire && i.simtStackOp   -- :47
def wsBarFire (i : WsInputs) : Bool := i.warpControlFire && !i.simtStackOp  -- :136
def wsRspFire (i : WsInputs) : Bool := wsWarpEnd i && i.warpRspReady        -- Decoupled.fire

/-- 输出（组合逻辑，全部为旧状态与当前输入的纯函数） -/
structure WsOutputs where
  warpReady        : BitVec 8  -- :35,:182
  nextWarp         : BitVec 3  -- :50,:95
  pcReqValid       : Bool      -- :187,:206-207,:220
  pcReqWid         : BitVec 3  -- :99
  flushValid       : Bool      -- :73
  flushWid         : BitVec 3  -- :74
  flushCacheValid  : Bool      -- :75
  flushCacheWid    : BitVec 3  -- :76
  warpRspValid     : Bool      -- :55
  flushDCacheValid : Bool      -- :172（:173 bits 同为 need_flush，略）
  branchReady      : Bool      -- :51
  warpControlReady : Bool      -- :52
  wgIdLookup       : BitVec 3  -- :103（冗余 mux，M5）

/- ========================================================================= -/
/- 3. 逐字段 step（全部读旧值，后写覆盖先写，M4）                              -/
/- ========================================================================= -/

/-- warp_bar_belong（:123-134）：req 置位（:124）先写，rsp 清除（:133）后写；
    两笔的值都读旧 belong。同拍同 wg 时 rsp 覆盖 req（Q5）。
    D1：参数与返回值均为 Array（定长 8），读 wsRd8、写 wsWr8。 -/
def wsStepBelong (bel : Array (BitVec 8)) (i : WsInputs) : Array (BitVec 8) :=
  let b1 := if i.warpReqFire then
    wsWr8 bel (wsFin i.newWgId) (wsRd8 bel (wsFin i.newWgId) ||| (1#8 <<< i.reqWid.zeroExtend 8))
    else bel
  if wsRspFire i then
    wsWr8 b1 (wsFin (wsEndWgId i.wgIdTag))
      (wsRd8 bel (wsFin (wsEndWgId i.wgIdTag)) &&& ~~~(1#8 <<< i.wcWid.zeroExtend 8))
    else b1

/-- barrier 释放条件（:139）：(cur | 1<<wf) == exp，读旧 cur/exp -/
def wsBarRelease (cur exp : BitVec 8) (wf : BitVec 3) : Bool :=
  (cur ||| (1#8 <<< wf.zeroExtend 8)) == exp

/-- warp_bar_cur（:126-127,:137,:140）：req 且未 lock 时清 0 先写（lock = 旧
    belong.orR，:135）；barrier 到达或位后写；释放清 0 最后写。值全读旧 cur。 -/
def wsStepCur (cur exp bel : Array (BitVec 8)) (i : WsInputs) : Array (BitVec 8) :=
  let newG := wsFin i.newWgId
  let endG := wsFin (wsEndWgId i.wgIdTag)
  let wf := wsEndWfId i.wgIdTag
  let c1 := if i.warpReqFire && (wsRd8 bel newG == 0#8) then wsWr8 cur newG 0#8 else cur
  let c2 := if wsBarFire i then wsWr8 c1 endG (wsRd8 cur endG ||| (1#8 <<< wf.zeroExtend 8)) else c1
  if wsBarFire i && wsBarRelease (wsRd8 cur endG) (wsRd8 exp endG) wf then wsWr8 c2 endG 0#8 else c2

/-- warp_bar_exp（:126-129）：仅 req 且未 lock 时初始化（后写无，单笔） -/
def wsStepExp (exp bel : Array (BitVec 8)) (i : WsInputs) : Array (BitVec 8) :=
  if i.warpReqFire && (wsRd8 bel (wsFin i.newWgId) == 0#8) then
    wsWr8 exp (wsFin i.newWgId) (wsExpInit i.newWfCount)
  else exp

/-- barrier 释放/等待时 warp_bar_data 的逐值形式（:138,:141）。
    释放：data & ~belong（读旧 data，整体覆盖 :138 的置位）；未释放：data | 1<<wid。 -/
def wsBarDataNext (data belong : BitVec 8) (wid : BitVec 3) (rel : Bool) : BitVec 8 :=
  if rel then data &&& ~~~belong else data ||| (1#8 <<< wid.zeroExtend 8)

/-- warp_bar_data（:136-141） -/
def wsStepData (data : BitVec 8) (cur exp bel : Fin 8 → BitVec 8) (i : WsInputs) : BitVec 8 :=
  if wsBarFire i then
    wsBarDataNext data (bel (wsFin (wsEndWgId i.wgIdTag))) i.wcWid
      (wsBarRelease (cur (wsFin (wsEndWgId i.wgIdTag))) (exp (wsFin (wsEndWgId i.wgIdTag)))
        (wsEndWfId i.wgIdTag))
  else data

/-- warp_endprg_cnt（:157-163）：req 置位先写，rsp 清除后写，值全读旧 cnt（Q5） -/
def wsStepCnt (cnt : Array (BitVec 8)) (i : WsInputs) : Array (BitVec 8) :=
  let c1 := if i.warpReqFire then
    wsWr8 cnt (wsFin i.newWgId) (wsRd8 cnt (wsFin i.newWgId) ||| (1#8 <<< i.reqWid.zeroExtend 8))
    else cnt
  if wsRspFire i then
    wsWr8 c1 (wsFin (wsEndWgId i.wgIdTag))
      (wsRd8 cnt (wsFin (wsEndWgId i.wgIdTag)) &&& ~~~(1#8 <<< i.wcWid.zeroExtend 8))
    else c1

/-- mask_0（:164-166）：cnt(i) 空 ∧ valid(i)。用 ofBool+移位而非 if，便于 bv_decide -/
def wsMask0 (cnt : Fin 8 → BitVec 8) (v : Fin 8 → Bool) : BitVec 8 :=
  (BitVec.ofBool ((cnt (wsFin 0#3) == 0#8) && v (wsFin 0#3))).zeroExtend 8 |||
  ((BitVec.ofBool ((cnt (wsFin 1#3) == 0#8) && v (wsFin 1#3))).zeroExtend 8 <<< 1) |||
  ((BitVec.ofBool ((cnt (wsFin 2#3) == 0#8) && v (wsFin 2#3))).zeroExtend 8 <<< 2) |||
  ((BitVec.ofBool ((cnt (wsFin 3#3) == 0#8) && v (wsFin 3#3))).zeroExtend 8 <<< 3) |||
  ((BitVec.ofBool ((cnt (wsFin 4#3) == 0#8) && v (wsFin 4#3))).zeroExtend 8 <<< 4) |||
  ((BitVec.ofBool ((cnt (wsFin 5#3) == 0#8) && v (wsFin 5#3))).zeroExtend 8 <<< 5) |||
  ((BitVec.ofBool ((cnt (wsFin 6#3) == 0#8) && v (wsFin 6#3))).zeroExtend 8 <<< 6) |||
  ((BitVec.ofBool ((cnt (wsFin 7#3) == 0#8) && v (wsFin 7#3))).zeroExtend 8 <<< 7)

/-- flush 清除条件（:169）：mask_0(flush_entry) && flushDCache.ready，读旧 mask_0 -/
def wsFlushClear (cnt : Fin 8 → BitVec 8) (v : Fin 8 → Bool) (i : WsInputs) : Bool :=
  let m0 := wsMask0 cnt v
  ((m0 >>> (wsOHToUInt m0).zeroExtend 8) &&& 1#8 == 1#8) && i.flushDCacheReady

/-- warp_wg_valid（:159,:169-170）：req 置 true 先写；flush 清 false 后写。
    mask_0/flush_entry 读旧 cnt/valid（:164-168 是 wire，经 wsRd8/wsRdB 的
    函数视图喂给 wsMask0/wsFlushClear）。 -/
def wsStepValid (cnt : Array (BitVec 8)) (v : Array Bool) (i : WsInputs) : Array Bool :=
  let v1 := if i.warpReqFire then wsWrB v (wsFin i.newWgId) true else v
  if wsFlushClear (fun j => wsRd8 cnt j) (fun j => wsRdB v j) i then
    wsWrB v1 (wsFin (wsOHToUInt (wsMask0 (fun j => wsRd8 cnt j) (fun j => wsRdB v j)))) false
  else v1

/-- warp_active（:180）：req 置位 | warp_end 清除（清除胜，Q6）。注意清除条件是
    warp_end 而非 warpRsp.fire（Q4：rsp 未就绪时 active 已清、cnt/belong 未清）。 -/
def wsStepActive (act : BitVec 8) (i : WsInputs) : BitVec 8 :=
  (act ||| (if i.warpReqFire then 1#8 <<< i.reqWid.zeroExtend 8 else 0#8)) &&&
  (if wsWarpEnd i then ~~~(1#8 <<< i.wcWid.zeroExtend 8) else 0xFF#8)

/-- next_warp（:183-186）：递降 when 链，后写（小编号）胜 ⇒ 固定优先级，
    最低编号 pc_ready warp 获胜；无 ready 时保持 current_warp（:50 WireInit）。 -/
def wsNextWarp (pcRdy : BitVec 8) (cur : BitVec 3) : BitVec 3 :=
  if (pcRdy >>> 0) &&& 1#8 = 1#8 then 0#3 else
  if (pcRdy >>> 1) &&& 1#8 = 1#8 then 1#3 else
  if (pcRdy >>> 2) &&& 1#8 = 1#8 then 2#3 else
  if (pcRdy >>> 3) &&& 1#8 = 1#8 then 3#3 else
  if (pcRdy >>> 4) &&& 1#8 = 1#8 then 4#3 else
  if (pcRdy >>> 5) &&& 1#8 = 1#8 then 5#3 else
  if (pcRdy >>> 6) &&& 1#8 = 1#8 then 6#3 else
  if (pcRdy >>> 7) &&& 1#8 = 1#8 then 7#3 else cur

/-- warp_ready（:181）：~(bar_data | scoreboard_busy | exe_busy | ~warp_active) -/
def wsWarpReady (bar sb exe act : BitVec 8) : BitVec 8 :=
  ~~~(bar ||| sb ||| exe ||| ~~~act)

/-- 单拍状态转移。currentWarp := next_warp（:95），pc_ready = ibuf_rdy & active（:184，
    M3），均为旧状态。barData 的输出是扁平 BitVec（无闭包残留），wsStepData 仍走
    访问器函数视图；per-wg 字段经 wsStepXxx 直接产出新 Array（D1）。 -/
def wsStep (s : WsState) (i : WsInputs) : WsState where
  currentWarp := wsNextWarp (i.pcIbufRdy &&& s.warpActive) s.currentWarp
  warpActive  := wsStepActive s.warpActive i
  barCurArr      := wsStepCur s.barCurArr s.barExpArr s.barBelongArr i
  barExpArr      := wsStepExp s.barExpArr s.barBelongArr i
  barBelongArr   := wsStepBelong s.barBelongArr i
  barData     := wsStepData s.barData s.barCur s.barExp s.barBelong i
  endprgCntArr   := wsStepCnt s.endprgCntArr i
  wgValidArr     := wsStepValid s.endprgCntArr s.wgValidArr i

-- 投影引理（rfl）
theorem wsStep_currentWarp (s : WsState) (i : WsInputs) :
    (wsStep s i).currentWarp = wsNextWarp (i.pcIbufRdy &&& s.warpActive) s.currentWarp := rfl
theorem wsStep_warpActive (s : WsState) (i : WsInputs) :
    (wsStep s i).warpActive = wsStepActive s.warpActive i := rfl
theorem wsStep_barData (s : WsState) (i : WsInputs) :
    (wsStep s i).barData = wsStepData s.barData s.barCur s.barExp s.barBelong i := rfl
theorem wsStep_endprgCnt (s : WsState) (i : WsInputs) :
    (wsStep s i).endprgCntArr = wsStepCnt s.endprgCntArr i := rfl
theorem wsStep_wgValid (s : WsState) (i : WsInputs) :
    (wsStep s i).wgValidArr = wsStepValid s.endprgCntArr s.wgValidArr i := rfl

/-- 组合输出 -/
def wsOut (s : WsState) (i : WsInputs) : WsOutputs :=
  let pcRdy := i.pcIbufRdy &&& s.warpActive
  let nw := wsNextWarp pcRdy s.currentWarp
  let fcValid := i.pcRspValid && i.pcRspMiss
  { warpReady        := wsWarpReady s.barData i.scoreboardBusy i.exeBusy s.warpActive
    nextWarp         := nw
    pcReqValid       := ((pcRdy >>> nw.zeroExtend 8) &&& 1#8 == 1#8) &&
                        !(i.branchFire && i.branchJump && (i.branchWid == nw)) && !i.pcReset
    pcReqWid         := nw
    flushValid       := (i.branchFire && i.branchJump) || wsWarpEnd i
    flushWid         := if i.branchFire && i.branchJump then i.branchWid else i.wcWid
    flushCacheValid  := fcValid
    flushCacheWid    := i.pcRspWid
    warpRspValid     := wsWarpEnd i
    flushDCacheValid := wsMask0 s.endprgCnt s.wgValid != 0#8
    branchReady      := !fcValid
    warpControlReady := !i.branchFire && !fcValid
    wgIdLookup       := i.wcWid }

/-- 多拍运行 -/
def wsRun (s : WsState) (ins : List WsInputs) : WsState := ins.foldl wsStep s

/- 求值性能对照（第 17 波，2026-08-28；同一混合输入轨迹：req/barrier/endprg/
   flushRdy/nop 按拍轮换，每拍 wsStep + wsOut + 全部 per-wg 字段深读校验和，
   #eval + IO.monoMsNow 计时；注意 do 块内 `let` 是惰性 thunk，必须先 println
   强制求值再取 t1，否则测到的是 0ms——本次第一轮就踩了这个坑）。
   Array 化前（Fin 8 → … 函数字段，rf_write 闭包链，逐拍指数爆炸）：
     n=6 → 648ms，n=7 → 5428ms，n=8 → 42408ms（每多一拍 ×8），
     n=10 超 240s 未完成，n=400 超 600s 被kill无任何输出。
   Array 化后（本文件）：
     n=8 → 1ms，n=100 → 2ms，n=400 → 8ms，n=1000 → 21ms，n=5000 → 99ms
     （严格线性，约 20µs/拍；n=8 处提速 >40000×）。
   行为保持交叉验证：两侧 n=2/5/6/7/8 的校验和逐项一致（acc=3/2/3/34/1）。 -/

/- ========================================================================= -/
/- 4. 数值回归测试（先测试；单拍 by decide，多拍轨迹 native_decide）            -/
/- ========================================================================= -/

section WsRegressionTests

/-- 空输入 -/
def wsInNop : WsInputs :=
  { warpReqFire := false, reqWid := 0#3, newWgId := 0#3, newWfCount := 0#4,
    warpControlFire := false, simtStackOp := false, wcWid := 0#3, wgIdTag := 0#6,
    warpRspReady := true, scoreboardBusy := 0#8, exeBusy := 0#8, pcIbufRdy := 0#8,
    flushDCacheReady := false, branchFire := false, branchJump := false, branchWid := 0#3,
    pcRspValid := false, pcRspMiss := false, pcRspWid := 0#3, pcReset := false }

/-- warp 分配请求 -/
def wsInReq (wid wg : BitVec 3) (cnt : BitVec 4) : WsInputs :=
  { wsInNop with warpReqFire := true, reqWid := wid, newWgId := wg, newWfCount := cnt }

/-- endprg（warp_control.fire & simt_stack_op）；tag = wg:wf -/
def wsInEndprg (wid wg wf : BitVec 3) (rdy : Bool) : WsInputs :=
  { wsInNop with warpControlFire := true, simtStackOp := true, wcWid := wid, wgIdTag := (wg.zeroExtend 6 <<< 3) ||| wf.zeroExtend 6, warpRspReady := rdy }

/-- barrier 到达（warp_control.fire & !simt_stack_op） -/
def wsInBarrier (wid wg wf : BitVec 3) : WsInputs :=
  { wsInNop with warpControlFire := true, simtStackOp := false, wcWid := wid, wgIdTag := (wg.zeroExtend 6 <<< 3) ||| wf.zeroExtend 6 }

/-- flushDCache 就绪的空拍 -/
def wsInFlushRdy : WsInputs := { wsInNop with flushDCacheReady := true }

-- T1 warp 分配 → active 置位、簿记建立、下拍可调度
def wsS1 : WsState := wsStep wsInit (wsInReq 3#3 1#3 1#4)
example : (wsS1.warpActive >>> 3) &&& 1#8 = 1#8 := by decide
example : wsS1.barExp ⟨1, by decide⟩ = 1#8 := by decide          -- (1<<1)-1
example : wsS1.barBelong ⟨1, by decide⟩ = 8#8 := by decide        -- 1<<3
example : wsS1.endprgCnt ⟨1, by decide⟩ = 8#8 := by decide
example : wsS1.wgValid ⟨1, by decide⟩ = true := by decide
example : ((wsOut wsS1 wsInNop).warpReady >>> 3) &&& 1#8 = 1#8 := by decide
example : ((wsOut wsInit wsInNop).warpReady >>> 3) &&& 1#8 = 0#8 := by decide  -- 分配当拍不 ready

-- T2 endprg → active/cnt/belong 清除；mask_0 当拍读旧值，flush 下一拍才被消费
def wsS2 : WsState := wsStep wsS1 (wsInEndprg 3#3 1#3 0#3 true)
example : (wsS2.warpActive >>> 3) &&& 1#8 = 0#8 := by decide
example : wsS2.endprgCnt ⟨1, by decide⟩ = 0#8 := by decide
example : wsS2.barBelong ⟨1, by decide⟩ = 0#8 := by decide
example : (wsOut wsS2 wsInNop).flushDCacheValid = true := by decide
def wsS3 : WsState := wsStep wsS2 wsInFlushRdy
example : wsS3.wgValid ⟨1, by decide⟩ = false := by decide
example : (wsOut wsS3 wsInNop).flushDCacheValid = false := by decide

-- T3/T4 barrier：两 warp 到达 → 释放；未齐不释放且已到 warp 不 ready
def wsB1 : WsState := wsStep wsInit (wsInReq 0#3 2#3 2#4)
def wsB2 : WsState := wsStep wsB1 (wsInReq 1#3 2#3 2#4)
example : wsB2.barExp ⟨2, by decide⟩ = 3#8 := by decide           -- (1<<2)-1
example : wsB2.barBelong ⟨2, by decide⟩ = 3#8 := by decide
def wsB3 : WsState := wsStep wsB2 (wsInBarrier 0#3 2#3 0#3)       -- warp0 到达
example : (wsB3.barData >>> 0) &&& 1#8 = 1#8 := by decide
example : wsB3.barCur ⟨2, by decide⟩ = 1#8 := by decide           -- 未齐，cur 累积
example : ((wsOut wsB3 wsInNop).warpReady >>> 0) &&& 1#8 = 0#8 := by decide  -- 已 barrier 不 ready
example : ((wsOut wsB3 wsInNop).warpReady >>> 1) &&& 1#8 = 1#8 := by decide  -- 未到的不受影响
def wsB4 : WsState := wsStep wsB3 (wsInBarrier 1#3 2#3 1#3)       -- warp1 到达 → 齐 → 释放
example : wsB4.barCur ⟨2, by decide⟩ = 0#8 := by decide
example : wsB4.barData = 0#8 := by decide                         -- 该 wg 全部 warp 解除
example : (wsOut wsB4 wsInNop).warpReady &&& 3#8 = 3#8 := by decide

-- T5 固定优先级：0/3/5 同时 ready → 0；3/5 → 3；无 ready → current_warp
def wsP : WsState := { wsInit with warpActive := 0b00101001#8, currentWarp := 2#3 }
def wsInAllRdy : WsInputs := { wsInNop with pcIbufRdy := 0xFF#8 }
example : (wsOut wsP wsInAllRdy).nextWarp = 0#3 := by decide
example : (wsOut { wsP with warpActive := 0b00101000#8 } wsInAllRdy).nextWarp = 3#3 := by decide
example : (wsOut { wsP with warpActive := 0#8 } wsInAllRdy).nextWarp = 2#3 := by decide
example : (wsOut wsP { wsInNop with pcIbufRdy := 0b00101000#8 }).nextWarp = 3#3 := by decide

-- T6 I-5 witness：wg1(warp1)、wg2(warp2) 同拍完成窗口 → mask_0={1,2}，
-- flush_entry = OHToUInt = 1|2 = 3，mask_0(3)=0 → valid 位永远清不掉
def wsF1 : WsState := wsStep wsInit (wsInReq 1#3 1#3 1#4)
def wsF2 : WsState := wsStep wsF1 (wsInReq 2#3 2#3 1#4)
def wsF3 : WsState := wsStep wsF2 (wsInEndprg 1#3 1#3 0#3 true)
def wsF4 : WsState := wsStep wsF3 (wsInEndprg 2#3 2#3 0#3 true)
example : wsMask0 wsF4.endprgCnt wsF4.wgValid = 0b00000110#8 := by native_decide
example : wsOHToUInt (wsMask0 wsF4.endprgCnt wsF4.wgValid) = 3#3 := by native_decide
def wsF7 : WsState := wsRun wsF4 [wsInFlushRdy, wsInFlushRdy, wsInFlushRdy]
example : wsF7.wgValid ⟨1, by decide⟩ = true := by native_decide
example : wsF7.wgValid ⟨2, by decide⟩ = true := by native_decide
example : (wsOut wsF7 wsInFlushRdy).flushDCacheValid = true := by native_decide

-- T7 I-7 witness：同拍 warpReq(warp5→wg3) 与 warpRsp(warp4 endprg, wg3)，
-- rsp 后写覆盖 req（M4），warp5 的 belong/cnt 位丢失
def wsC1 : WsState := wsStep wsInit (wsInReq 4#3 3#3 1#4)
def wsInC2 : WsInputs :=
  { wsInReq 5#3 3#3 1#4 with warpControlFire := true, simtStackOp := true, wcWid := 4#3, wgIdTag := ((3#3).zeroExtend 6 <<< 3) ||| 0#6, warpRspReady := true }
def wsC2 : WsState := wsStep wsC1 wsInC2
example : wsC2.barBelong ⟨3, by decide⟩ = 0#8 := by native_decide   -- warp5 的 belong 位丢失
example : wsC2.endprgCnt ⟨3, by decide⟩ = 0#8 := by native_decide   -- warp5 的 cnt 位丢失
example : (wsC2.warpActive >>> 5) &&& 1#8 = 1#8 := by native_decide  -- 但 warp5 确实 active
example : ((wsMask0 wsC2.endprgCnt wsC2.wgValid >>> 3) &&& 1#8) = 1#8 := by native_decide  -- wg3 有活跃 warp 却请求 flush

-- T8 I-6 witness：warpRsp ready=0 时 endprg 响应丢失：active 已清（:180 用
-- warp_end），cnt/belong 永不清除，flush 永不发出，warpRsp.valid 不再回升
def wsD1 : WsState := wsStep wsInit (wsInReq 3#3 1#3 1#4)
def wsD2 : WsState := wsStep wsD1 (wsInEndprg 3#3 1#3 0#3 false)
example : (wsD2.warpActive >>> 3) &&& 1#8 = 0#8 := by decide      -- active 已清
example : wsD2.endprgCnt ⟨1, by decide⟩ = 8#8 := by decide        -- cnt 未清
def wsD5 : WsState := wsRun wsD2 [wsInNop, wsInNop, wsInNop]
example : wsD5.endprgCnt ⟨1, by decide⟩ = 8#8 := by native_decide
example : wsD5.barBelong ⟨1, by decide⟩ = 8#8 := by native_decide  -- lock 卡死
example : (wsOut wsD5 wsInNop).flushDCacheValid = false := by native_decide
example : (wsOut wsD5 wsInNop).warpRspValid = false := by native_decide  -- valid 不再回升

end WsRegressionTests

/- ========================================================================= -/
/- 5. 契约定理（后证明）                                                      -/
/- ========================================================================= -/

/-- WS1 warp_ready 规约：ready(i) ⟺ active(i) ∧ ¬barred(i) ∧ ¬sb_busy(i) ∧ ¬exe_busy(i)。
    取位用移位形式（bv_decide 不支持变量 Nat 下标）。 -/
theorem ws1_ready_spec (bar sb exe act : BitVec 8) (i : BitVec 3) :
    ((wsWarpReady bar sb exe act >>> i.zeroExtend 8) &&& 1#8 = 1#8) ↔
    ((act >>> i.zeroExtend 8) &&& 1#8 = 1#8 ∧ (bar >>> i.zeroExtend 8) &&& 1#8 = 0#8 ∧
     (sb >>> i.zeroExtend 8) &&& 1#8 = 0#8 ∧ (exe >>> i.zeroExtend 8) &&& 1#8 = 0#8) := by
  unfold wsWarpReady
  bv_decide

/-- WS2a barrier 释放判定：释放 ⟺ 到达集合（cur ∪ {wf}）= exp 指定集合（:139） -/
theorem ws2_release_iff (cur exp : BitVec 8) (wf : BitVec 3) :
    wsBarRelease cur exp wf = true ↔ (cur ||| (1#8 <<< wf.zeroExtend 8)) = exp := by
  unfold wsBarRelease
  bv_decide

/-- WS2b 释放清除该 wg 全部 warp 的 barrier 等待位（:141） -/
theorem ws2_release_clears (data belong : BitVec 8) (wid : BitVec 3) :
    wsBarDataNext data belong wid true &&& belong = 0#8 := by
  unfold wsBarDataNext
  bv_decide

/-- WS2c 未释放时，到达 barrier 的 warp 被记入 bar_data（:138） -/
theorem ws2_arrive_barred (data belong : BitVec 8) (wid : BitVec 3) :
    ((wsBarDataNext data belong wid false >>> wid.zeroExtend 8) &&& 1#8) = 1#8 := by
  unfold wsBarDataNext
  bv_decide

/-- WS2d 释放前该 wg 已 barrier 的 warp 不 ready（WS1 的推论，:181） -/
theorem ws2_barred_not_ready (data sb exe act : BitVec 8) (i : BitVec 3)
    (h : ((data >>> i.zeroExtend 8) &&& 1#8) = 1#8) :
    ((wsWarpReady data sb exe act >>> i.zeroExtend 8) &&& 1#8) = 0#8 := by
  unfold wsWarpReady
  bv_decide

/-- WS2e 释放后该 wg 的活跃 warp 重新 ready（:141 + :181） -/
theorem ws2_release_ready_again (data belong sb exe act : BitVec 8) (wid i : BitVec 3)
    (hb : ((belong >>> i.zeroExtend 8) &&& 1#8) = 1#8)
    (ha : ((act >>> i.zeroExtend 8) &&& 1#8) = 1#8)
    (hs : ((sb >>> i.zeroExtend 8) &&& 1#8) = 0#8)
    (he : ((exe >>> i.zeroExtend 8) &&& 1#8) = 0#8) :
    ((wsWarpReady (wsBarDataNext data belong wid true) sb exe act >>> i.zeroExtend 8) &&& 1#8) = 1#8 := by
  unfold wsWarpReady wsBarDataNext
  bv_decide

/-- WS2f cur 语义（:137,:140）：释放则清 0，否则累积到达位 -/
theorem ws2_cur_sem (cur exp : BitVec 8) (wf : BitVec 3) :
    (if wsBarRelease cur exp wf then 0#8 else cur ||| (1#8 <<< wf.zeroExtend 8)) =
    if (cur ||| (1#8 <<< wf.zeroExtend 8)) = exp then 0#8 else cur ||| (1#8 <<< wf.zeroExtend 8) := by
  unfold wsBarRelease
  bv_decide

/-- WS3a 固定优先级：next_warp = 最小 ready 编号。前提：bit k 就绪且所有
    更低编号位不就绪（低 k 位掩码为 0）。 -/
theorem ws3_next_warp_min (m : BitVec 8) (cur k : BitVec 3)
    (hk : ((m >>> k.zeroExtend 8) &&& 1#8) = 1#8)
    (hmin : m &&& ((1#8 <<< k.zeroExtend 8) - 1#8) = 0#8) :
    wsNextWarp m cur = k := by
  unfold wsNextWarp
  bv_decide

/-- WS3b 无 ready warp 时保持 current_warp（:50 WireInit + :185 无命中） -/
theorem ws3_next_warp_fallback (cur : BitVec 3) :
    wsNextWarp 0#8 cur = cur := by
  unfold wsNextWarp
  bv_decide

/-- WS3c 结果 warp 必然 ready（有 ready 时）：饥饿风险的正面表述——
    被选中的 warp 一定 pc_ready，但选中与"公平"无关，纯固定优先级。 -/
theorem ws3_next_warp_ready (m : BitVec 8) (cur : BitVec 3) (hm : m ≠ 0#8) :
    ((m >>> (wsNextWarp m cur).zeroExtend 8) &&& 1#8) = 1#8 := by
  unfold wsNextWarp
  bv_decide

/-- WS4a I-5 位级核心：mask_0 同时含 bit1、bit2 时，flush_entry = OHToUInt
    必含 1|2=3 的贡献，故不可能等于 1 或 2（:168-169 的清除目标永远错过
    这两个 wg）。 -/
theorem ws4_flush_entry_avoids (m : BitVec 8)
    (h1 : ((m >>> 1) &&& 1#8) = 1#8) (h2 : ((m >>> 2) &&& 1#8) = 1#8) :
    wsOHToUInt m ≠ 1#3 ∧ wsOHToUInt m ≠ 2#3 := by
  unfold wsOHToUInt
  bv_decide

/-- mask_0 取位引理：bit1 ⟺ cnt(1) 空 ∧ valid(1) -/
theorem wsMask0_bit1 (cnt : Fin 8 → BitVec 8) (v : Fin 8 → Bool) :
    ((wsMask0 cnt v >>> 1) &&& 1#8) = 1#8 ↔
    (cnt (wsFin 1#3) = 0#8 ∧ v (wsFin 1#3) = true) := by
  unfold wsMask0
  bv_decide

/-- mask_0 取位引理：bit2 ⟺ cnt(2) 空 ∧ valid(2) -/
theorem wsMask0_bit2 (cnt : Fin 8 → BitVec 8) (v : Fin 8 → Bool) :
    ((wsMask0 cnt v >>> 2) &&& 1#8) = 1#8 ↔
    (cnt (wsFin 2#3) = 0#8 ∧ v (wsFin 2#3) = true) := by
  unfold wsMask0
  bv_decide

/-- I-5 卡死态：wg1、wg2 的 cnt 已空但 valid 仍置位（T6 中 wsF4 之后的形态） -/
def wsStuck (s : WsState) : Prop :=
  s.endprgCnt (wsFin 1#3) = 0#8 ∧ s.wgValid (wsFin 1#3) = true ∧
  s.endprgCnt (wsFin 2#3) = 0#8 ∧ s.wgValid (wsFin 2#3) = true

/-- 卡死态 ⇒ mask_0 非零（need_flush 为真，:167） -/
theorem wsMask0_ne_zero_of_stuck (s : WsState) (h : wsStuck s) :
    wsMask0 s.endprgCnt s.wgValid ≠ 0#8 := by
  obtain ⟨hc1, hv1, _, _⟩ := h
  have hb1 : ((wsMask0 s.endprgCnt s.wgValid >>> 1) &&& 1#8) = 1#8 :=
    (wsMask0_bit1 _ _).mpr ⟨hc1, hv1⟩
  intro hz
  rw [hz] at hb1
  exact absurd hb1 (by decide)

/-- WS4b I-5 单拍不变式：只要不再有 warpReq 派发进 wg1/wg2（这里用更强的
    "warpReq 完全不发"），卡死态保持——flush_entry 永远错过 1 和 2，
    valid 位清不掉，cnt 保持为 0。 -/
theorem ws4_step_stuck (s : WsState) (i : WsInputs)
    (h : wsStuck s) (hnr : i.warpReqFire = false) : wsStuck (wsStep s i) := by
  obtain ⟨hc1, hv1, hc2, hv2⟩ := h
  have hb1 : ((wsMask0 s.endprgCnt s.wgValid >>> 1) &&& 1#8) = 1#8 :=
    (wsMask0_bit1 _ _).mpr ⟨hc1, hv1⟩
  have hb2 : ((wsMask0 s.endprgCnt s.wgValid >>> 2) &&& 1#8) = 1#8 :=
    (wsMask0_bit2 _ _).mpr ⟨hc2, hv2⟩
  have hfe := ws4_flush_entry_avoids _ hb1 hb2
  have hne1 : wsFin (wsOHToUInt (wsMask0 s.endprgCnt s.wgValid)) ≠ wsFin 1#3 := by
    intro heq
    have hv : (wsOHToUInt (wsMask0 s.endprgCnt s.wgValid)).toNat = (1#3).toNat :=
      congrArg Fin.val heq
    exact hfe.1 (BitVec.toNat_inj.mp hv)
  have hne2 : wsFin (wsOHToUInt (wsMask0 s.endprgCnt s.wgValid)) ≠ wsFin 2#3 := by
    intro heq
    have hv : (wsOHToUInt (wsMask0 s.endprgCnt s.wgValid)).toNat = (2#3).toNat :=
      congrArg Fin.val heq
    exact hfe.2 (BitVec.toNat_inj.mp hv)
  -- 访问器展开（defeq）后的数组形式假设
  have hc1' : wsRd8 s.endprgCntArr (wsFin 1#3) = 0#8 := hc1
  have hv1' : wsRdB s.wgValidArr (wsFin 1#3) = true := hv1
  have hc2' : wsRd8 s.endprgCntArr (wsFin 2#3) = 0#8 := hc2
  have hv2' : wsRdB s.wgValidArr (wsFin 2#3) = true := hv2
  have hne1' : wsFin (wsOHToUInt (wsMask0 (fun j => wsRd8 s.endprgCntArr j)
      (fun j => wsRdB s.wgValidArr j))) ≠ wsFin 1#3 := hne1
  have hne2' : wsFin (wsOHToUInt (wsMask0 (fun j => wsRd8 s.endprgCntArr j)
      (fun j => wsRdB s.wgValidArr j))) ≠ wsFin 2#3 := hne2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- cnt(1) 保持 0：req 不发（hnr），rsp 只清除位（0 &&& _ = 0）
    show wsRd8 (wsStepCnt s.endprgCntArr i) (wsFin 1#3) = 0#8
    by_cases hr : wsRspFire i = true
    · by_cases he : wsFin (wsEndWgId i.wgIdTag) = wsFin 1#3
      · simp [wsStepCnt, hnr, hr, he, wsRd8_wr8_self, hc1']
      · simp [wsStepCnt, hnr, hr, wsRd8_wr8_of_ne, he, hc1']
    · simp [wsStepCnt, hnr, hr, hc1']
  · -- valid(1) 保持 true：flush 清除目标 ≠ 1
    show wsRdB (wsStepValid s.endprgCntArr s.wgValidArr i) (wsFin 1#3) = true
    by_cases hfc : wsFlushClear s.endprgCnt s.wgValid i = true
    · have hfc' : wsFlushClear (fun j => wsRd8 s.endprgCntArr j)
          (fun j => wsRdB s.wgValidArr j) i = true := hfc
      simp [wsStepValid, hfc', hnr, wsRdB_wrB_of_ne, hne1', hv1']
    · have hfc' : ¬ wsFlushClear (fun j => wsRd8 s.endprgCntArr j)
          (fun j => wsRdB s.wgValidArr j) i = true := hfc
      simp [wsStepValid, hnr, hfc', hv1']
  · show wsRd8 (wsStepCnt s.endprgCntArr i) (wsFin 2#3) = 0#8
    by_cases hr : wsRspFire i = true
    · by_cases he : wsFin (wsEndWgId i.wgIdTag) = wsFin 2#3
      · simp [wsStepCnt, hnr, hr, he, wsRd8_wr8_self, hc2']
      · simp [wsStepCnt, hnr, hr, wsRd8_wr8_of_ne, he, hc2']
    · simp [wsStepCnt, hnr, hr, hc2']
  · show wsRdB (wsStepValid s.endprgCntArr s.wgValidArr i) (wsFin 2#3) = true
    by_cases hfc : wsFlushClear s.endprgCnt s.wgValid i = true
    · have hfc' : wsFlushClear (fun j => wsRd8 s.endprgCntArr j)
          (fun j => wsRdB s.wgValidArr j) i = true := hfc
      simp [wsStepValid, hfc', hnr, wsRdB_wrB_of_ne, hne2', hv2']
    · have hfc' : ¬ wsFlushClear (fun j => wsRd8 s.endprgCntArr j)
          (fun j => wsRdB s.wgValidArr j) i = true := hfc
      simp [wsStepValid, hnr, hfc', hv2']

/-- WS4c I-5 卡死的永恒性：任意长的无 warpReq 输入序列后卡死态仍保持。
    即：need_flush 永真（flushDCache.valid 卡高）且 valid(1)、valid(2) 永真，
    除非 CTA 调度器再向 wg1 或 wg2 派发新 warp（此时新 warp 的 cnt 位会先把
    mask_0 从 {1,2} 变成单例，flush_entry 落回正确索引，系统自愈——
    见 ws4_step_stuck 前提 hnr）。 -/
theorem ws4_run_stuck (s : WsState) (ins : List WsInputs)
    (h : wsStuck s) (hnr : ∀ x ∈ ins, x.warpReqFire = false) : wsStuck (wsRun s ins) := by
  induction ins generalizing s with
  | nil => exact h
  | cons x xs ih =>
    exact ih (wsStep s x) (ws4_step_stuck s x h (hnr x List.mem_cons_self))
      (fun y hy => hnr y (List.mem_cons_of_mem x hy))

/-- WS4d I-5 判定（证实）：卡死态下 need_flush 永真且 valid(1)、valid(2) 永真 -/
theorem ws4_stuck_forever (s : WsState) (ins : List WsInputs)
    (h : wsStuck s) (hnr : ∀ x ∈ ins, x.warpReqFire = false) :
    wsMask0 (wsRun s ins).endprgCnt (wsRun s ins).wgValid ≠ 0#8 ∧
    (wsRun s ins).wgValid (wsFin 1#3) = true ∧
    (wsRun s ins).wgValid (wsFin 2#3) = true := by
  have hrun := ws4_run_stuck s ins h hnr
  exact ⟨wsMask0_ne_zero_of_stuck _ hrun, hrun.2.1, hrun.2.2.2⟩

/- 公理审计（bv_decide 会引入每定理私有的 LRAT 检查 trust 公理；
   native_decide 的测试额外引入 Lean.ofReduceBool，归档注明） -/
#print axioms ws1_ready_spec
#print axioms ws2_release_clears
#print axioms ws2_barred_not_ready
#print axioms ws3_next_warp_min
#print axioms ws4_flush_entry_avoids
#print axioms ws4_stuck_forever

end Ventus.Schedule
