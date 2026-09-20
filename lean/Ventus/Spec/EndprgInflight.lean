/- ========================================================================= -/
/-                     EndprgInflight.lean                                   -/
/-  跨模块风险链核查：warp 的 endprg 不等待在飞访存完成，其 wid/槽位被复用后， -/
/-  在飞 load 的迟到写回落入新 warp 的寄存器堆。                                -/
/-                                                                           -/
/-  ======================== 机制链（Chisel 源码行号证据） =================== -/
/-  (a) endprg 立即完成、槽位立即释放：                                        -/
/-    warp_schedule.scala:47    warp_end = warp_control.fire & simt_stack_op   -/
/-      —— 条件里没有任何访存 outstanding 项；                                 -/
/-    warp_schedule.scala:55    warpRsp.valid := warp_end（"always ready"）；  -/
/-    warp_schedule.scala:180   warp_active 当拍清除（用 warp_end，不等响应）；-/
/-    warp_schedule.scala:39-40 ldst/switch 输入被注释掉——设计者曾计划         -/
/-      "assume finish l2cache request" 的访存排空接口，后删除；               -/
/-    pipe.scala:219            exe_busy 恒接 false（执行侧忙检查被禁用）；    -/
/-    warp_schedule.scala:167-173 唯一的访存侧动作 flushDCache 在**整个 wg**   -/
/-      所有 warp 都 endprg 后才发出，且只是 DCache 刷写请求，与槽位释放并行， -/
/-      不回灌任何等待；LSU.scala:137 flush_dcache.ready 只要求 AddrCalc       -/
/-      s_idle（不含 MSHR 在飞响应排空）。                                     -/
/-  (b) wid 复用 + 迟到写回用"当前"基址：                                      -/
/-    CTA2warp.scala:56         CTAreq.ready = ~idx_using.andR（只看槽位空闲， -/
/-      不查任何访存状态）；                                                    -/
/-    CTA2warp.scala:59,63      idx_next_allocate = PriorityEncoder(~idx_using)；-/
/-      warpRsp.fire 当拍清 idx_using 位，下一拍即可复用；                      -/
/-    CSR.scala:296-301,355     新 warp 派发时 vCSR(wid) 的 sgpr/vgpr_base      -/
/-      被覆写为新 warp 的基址；                                                -/
/-    operandCollector.scala:604,606 写回 bank 内地址 =                        -/
/-      (vgpr_base(wid)/sgpr_base(wid) >> 2) + (reg_idxw >> 2)——读的是**当前** -/
/-      基址；写回通道 ready 恒 true（:623-624），迟到写回必被接受。            -/
/-  (c) 记分板：endprg/派发均不清 busy 位（scoreboard.scala:88 RegInit 0 后    -/
/-      只有 set/clear 两条路径；clear 只发生在 wb 拍，:110/:112）；             -/
/-    pipe.scala:271-272 迟到写回按 wb.bits.warp_id 路由 wb_v_fire/wb_x_fire， -/
/-      槽位复用后仍会清该槽记分板的对应 busy 位。                               -/
/-    后果：同号寄存器上，新 warp 的访问会被遗留 busy 位**串行化**到迟到写回     -/
/-    之后（偶然保护，掩盖同号覆写危害），但：                                   -/
/-      (i)  新 warp 同号寄存器的首次访问要白等一个已死 warp 的访存延迟；       -/
/-      (ii) 串行化结束后读到的就是旧 warp 的 load 数据（寄存器堆在 warp 间     -/
/-           不清零，读未初始化寄存器本就无定义——但硬件语义从"读到残留"退化为  -/
/-           "读到一块正在异步变化、且由上一个租户决定何时稳定的存储"）；       -/
/-      (iii) 若新 warp 的 vgpr 分配小于旧 warp 的目的寄存器号（基址来自        -/
/-           cu_interface.scala:74,87-89,105 的按 wg 可变长切分，不是每槽       -/
/-           定长），迟到写回的物理地址越出本 warp 分配，落入相邻分配——可能     -/
/-           是另一个正在运行的 warp 的区域，那里没有任何 busy 位保护；         -/
/-      (iv) 若旧 wg 的 vgpr 区域在迟到写回落地前已被资源表回收并分给别的 wg   -/
/-           （cta_scheduler 的 dealloc/alloc 链路不等在飞响应），写回直接      -/
/-           污染无关 warp。                                                   -/
/-  (d) 防护核查：warp_schedule/CTA2warp/cu_interface 中没有任何"派发前等待或  -/
/-      冲刷在飞访存"的逻辑（grep 无 outstanding/drain 类条件；(a) 所列行即     -/
/-      全部相关代码）。唯一的每 warp 在飞计数值 LSU.scala:572-577 的           -/
/-      shiftBoard/fence_end 只接记分板的 fence 停顿（pipe.scala:241），       -/
/-      不接 endprg/槽位释放路径。                                             -/
/-                                                                           -/
/-  ======================== 结论 =========================================== -/
/-  链 (a)-(b)-(d) 成立，witness 见第 4 节（eifW_*）：在抽象跨模块机器上，     -/
/-  w endprg 时在飞 load 保留（eifW_endprg_with_inflight）、槽位下一拍被新     -/
/-  warp 复用且 vgpr_base 覆写（eifW_reuse）、迟到写回物理地址由**新**基址     -/
/-  计算并落入新 warp 的寄存器（eifW_pollution）。归类：新 I 类候选。         -/
/-  危害：见 (c)(i)-(iv)；同号覆写被遗留 busy 位偶然掩盖，但 (iii)(iv) 两      -/
/-  条路径无保护。触发条件：warp 在 load 未完成时 endprg（正常程序即可能，     -/
/-  SMMemDc SMD-B4 实测 endprg 比在飞 load 写回早 17 拍）+ 槽位被快速复用。   -/
/-  修复建议（最小改动）：把 LSU 已有的每 warp 在飞排空信号 fence_end          -/
/-  （LSU.scala:577）接入 endprg 完成条件——warpRsp 延迟到 fence_end(wid)=1    -/
/-  才发出（或在 CTA2warp 的槽释放/再分配上 gate），第 5 节给出该守卫的        -/
/-  形式化（eifStepG）与"守卫下 witness 被阻断"定理。                          -/
/-  附带观察（另立候选，不在本文件展开）：wg 完成上报 host 的路径              -/
/-  （CTA2warp FIFO → CTArsp → cta_scheduler host_wg_done）不等待 flushDCache  -/
/-  完成（cta_scheduler.scala 无 flush 相关逻辑），存在 store 全局可见性       -/
/-  先于完成上报的排序风险。                                                   -/
/-                                                                           -/
/-  ======================== 建模决策 ======================================= -/
/-  M1. 组合机器 = 既有忠实模型的直接拼装：warp 调度用 Ventus.Schedule 的      -/
/-      wsStep/wsInReq/wsInEndprg（warp_schedule.scala 逐行翻译），槽位簿记用  -/
/-      Ventus.CTA 的 c2wStep/c2wInReq/c2wInRsp（CTA2warp.scala 逐行翻译），   -/
/-      写回地址用 ocWbVecAddr（operandCollector.scala:604 的既有翻译）。     -/
/-      本文件只新增两处粘合：每槽 vgpr_base 表（CSR.scala:296-301,355 的      -/
/-      一行覆写语义）与在飞写回队列 inflight（LSU.scala:572-577 shiftBoard   -/
/-      所跟踪事务的抽象：已接受、未写回的 load）。                             -/
/-  M2. 缩放：寄存器堆物理空间缩到 256 表项（bank 内地址 8 位，与             -/
/-      ocWbVecAddr 的输出宽度一致），bank 交织不影响本链结论（写读两侧同式   -/
/-      计算，见 operandCollector.scala:116 vs :604）。sgpr 侧同构（:606），   -/
/-      只建 vgpr 侧。                                                         -/
/-  M3. inflight 用 List（FIFO 序无关结论；写回恒被接受，:623-624）。          -/
/- ========================================================================= -/

import Ventus.Schedule.WarpScheduler
import Ventus.CTA.CTA2warp
import Ventus.Schedule.OperandCollector

namespace Ventus.Spec

open Ventus.Base Ventus.Schedule Ventus.CTA

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 状态与单拍操作                                                          -/
/- ========================================================================= -/

/-- 在飞 load 的未决写回（M1：shiftBoard 跟踪的事务抽象）。
    注意记录里**没有**基址字段——硬件写回通路的地址信息只有 wid + reg_idxw
    （WriteVecCtrl/WriteScalarCtrl，operandCollector.scala:604 用当前基址现算）。 -/
structure EifWb where
  wid  : BitVec 3    -- WriteVecCtrl.warp_id
  ridx : BitVec 8    -- WriteVecCtrl.reg_idxw（regidx_width + regext_width = 8）
  data : BitVec 32   -- 单 lane 抽象（M2）
deriving DecidableEq

/-- 组合机器状态（M1） -/
structure EifState where
  ws       : WsState            -- warp_scheduler（:176 warp_active 等）
  c2w      : C2wState           -- CTA2warp（:54 idx_using 等）
  vbase    : RegFile 8 11       -- vCSR(w).vgpr_base_dispatch（CSR.scala:174-177）
  inflight : List EifWb         -- 在飞未写回 load（M3）
  rf       : RegFile 256 32     -- 缩放向量寄存器堆（M2，bank 内地址索引）

def eifInit : EifState :=
  { ws := wsInit
    c2w := c2wInit
    vbase := rf_zero 8 11
    inflight := []
    rf := rf_zero 256 32 }

/-- 单拍操作 -/
inductive EifOp where
  | nop
  | dispatchA (wg : BitVec 3) (cnt : BitVec 4) (tag : BitVec 6) (base : BitVec 11)
  | issueLoad (wid : BitVec 3) (ridx : BitVec 8) (data : BitVec 32)
  | endprg (wid wg wf : BitVec 3)
  | lateWb

/-- BitVec 8 地址转 Fin 256 -/
def eifFin256 (x : BitVec 8) : Fin 256 := ⟨x.toNat, by have h := x.isLt; omega⟩

/-- 单拍转移。逐分支源码对应：
    dispatchA：CTA2warp.scala:56,59,63,67-69（槽位分配）+ warp_schedule.scala:123-130
      （req 置位）+ CSR.scala:296-301,355（基址覆写，选中 wid = 当拍分配结果）；
    issueLoad：LSU.scala:574 的 left（lsu_req.fire 入 shiftBoard）+ scoreboard.scala:109
      （busy 置位——本机器不建记分板，遗留 busy 的串行化效应见文件头 (c)）；
    endprg：warp_schedule.scala:47,55,180 + CTA2warp.scala:63（rsp fire 清槽）。
      **关键：inflight 原样保留——endprg 路径不触碰任何访存状态**；
    lateWb：operandCollector.scala:604（地址 = 当前 vgpr_base(wid) 现算）+
      :621-624（写回恒接受）。 -/
def eifStep (s : EifState) (op : EifOp) : EifState :=
  match op with
  | .nop => s
  | .issueLoad wid ridx data => { s with inflight := s.inflight ++ [⟨wid, ridx, data⟩] }
  | .endprg wid wg wf =>
      { s with
        ws := wsStep s.ws (wsInEndprg wid wg wf true)
        c2w := c2wStep s.c2w (c2wInRsp wid false) }
  | .dispatchA wg cnt tag base =>
      let ci := c2wInReq tag
      let fire := c2wReqFire s.c2w ci
      let newWid := c2wAllocIdx s.c2w
      { s with
        c2w := c2wStep s.c2w ci
        ws := wsStep s.ws (if fire then wsInReq newWid wg cnt else wsInNop)
        vbase := if fire then rf_write s.vbase (c2wFin newWid) base else s.vbase }
  | .lateWb =>
      match s.inflight with
      | [] => s
      | w :: rest =>
          let addr := ocWbVecAddr (s.vbase (c2wFin w.wid)) w.ridx
          { s with inflight := rest, rf := rf_write s.rf (eifFin256 addr) w.data }

def eifRun (s : EifState) (ops : List EifOp) : EifState := ops.foldl eifStep s

/- ========================================================================= -/
/- 2. 机制事实（符号化，非 witness 特化）                                      -/
/- ========================================================================= -/

/-- EIF-1 endprg 不排空在飞访存：endprg 拍 inflight 逐字保留（无等待、无冲刷） -/
theorem eif_endprg_preserves_inflight (s : EifState) (wid wg wf : BitVec 3) :
    (eifStep s (.endprg wid wg wf)).inflight = s.inflight := rfl

/-- EIF-2 endprg 当拍清除 warp_active 对应位（warp_schedule.scala:180，
    清除条件是 warp_end 而非任何访存完成信号） -/
theorem eif_endprg_clears_active (act : BitVec 8) (wid wg wf : BitVec 3) :
    ((wsStepActive act (wsInEndprg wid wg wf true) >>> wid.zeroExtend 8) &&& 1#8) = 0#8 := by
  have h1 : wsWarpEnd (wsInEndprg wid wg wf true) = true := rfl
  have h2 : (wsInEndprg wid wg wf true).wcWid = wid := rfl
  have h3 : (wsInEndprg wid wg wf true).warpReqFire = false := rfl
  unfold wsStepActive
  simp only [h1, if_true, h2, h3, Bool.false_eq_true, if_false]
  bv_decide

/-- EIF-2' 组合机器版：endprg 拍后该 wid 的 active 位为 0 -/
theorem eif_step_endprg_clears_active (s : EifState) (wid wg wf : BitVec 3) :
    (((eifStep s (.endprg wid wg wf)).ws.warpActive >>> wid.zeroExtend 8) &&& 1#8) = 0#8 :=
  eif_endprg_clears_active s.ws.warpActive wid wg wf

/-- EIF-3 warpRsp fire 清 idx_using 对应位（CTA2warp.scala:63；无论同拍是否有
    新分配——分配结果落在别的槽，c2w1_alloc_rsp_no_clash） -/
theorem eif_stepIdx_rsp_clears (u : BitVec 8) (a w : BitVec 3) (reqFire : Bool) :
    ((c2wStepIdx u a reqFire true w >>> w.zeroExtend 8) &&& 1#8) = 0#8 := by
  unfold c2wStepIdx
  cases reqFire <;> bv_decide

/-- EIF-3' 组合机器版：endprg 拍后该槽在 CTA2warp 簿记中空闲（前提：CTArsp
    FIFO 非满——满则响应丢失，那是 I-6 的另一条链） -/
theorem eif_step_endprg_frees_slot (s : EifState) (wid wg wf : BitVec 3)
    (h : s.c2w.fifo.length < 16) :
    (((eifStep s (.endprg wid wg wf)).c2w.idxUsing >>> wid.zeroExtend 8) &&& 1#8) = 0#8 := by
  have hr : c2wReqFire s.c2w (c2wInRsp wid false) = false := rfl
  have he : c2wEnqFire s.c2w (c2wInRsp wid false) = true := by
    have hv : (c2wInRsp wid false).warpRspValid = true := rfl
    have hd : decide (s.c2w.fifo.length < 16) = true := by simp [h]
    unfold c2wEnqFire
    rw [hv, hd]
    decide
  have hw : (c2wInRsp wid false).warpRspWid = wid := rfl
  show ((c2wStepIdx s.c2w.idxUsing (c2wAllocIdx s.c2w) (c2wReqFire s.c2w (c2wInRsp wid false))
          (c2wEnqFire s.c2w (c2wInRsp wid false)) (c2wInRsp wid false).warpRspWid >>>
          wid.zeroExtend 8) &&& 1#8) = 0#8
  rw [hr, he, hw]
  exact eif_stepIdx_rsp_clears s.c2w.idxUsing (c2wAllocIdx s.c2w) wid false

/-- EIF-4 迟到写回的地址用**当前** vgpr_base(wid) 现算（operandCollector.scala:604）。
    写回记录里不携带发射时基址——基址覆写（CSR.scala:300）即重定向。 -/
theorem eif_lateWb_uses_current_base (s : EifState) (w : EifWb) (rest : List EifWb) :
    (eifStep { s with inflight := w :: rest } .lateWb).rf =
      rf_write s.rf (eifFin256 (ocWbVecAddr (s.vbase (c2wFin w.wid)) w.ridx)) w.data := rfl

/- ========================================================================= -/
/- 3. witness：w endprg → 槽位复用 → 迟到写回污染新 warp 寄存器                -/
/- ========================================================================= -/

/-- 拍0：初始 -/
def eifW0 : EifState := eifInit
/-- 拍1：派发 warp A → slot 0，vgpr_base = 0，wg0，wf_count = 1 -/
def eifW1 : EifState := eifStep eifW0 (.dispatchA 0#3 1#4 0x08#6 0#11)
/-- 拍2：A 发射向量 load，目的 v8，数据 0xDEADBEEF，进入在飞（未写回） -/
def eifW2 : EifState := eifStep eifW1 (.issueLoad 0#3 8#8 0xDEADBEEF#32)
/-- 拍3：A endprg——**在飞 load 仍在路上** -/
def eifW3 : EifState := eifStep eifW2 (.endprg 0#3 0#3 0#3)
/-- 拍4：新 CTA 派发 warp B——复用 slot 0，新 vgpr_base = 128 -/
def eifW4 : EifState := eifStep eifW3 (.dispatchA 1#3 1#4 0x11#6 128#11)
/-- 拍5：A 的在飞 load 迟到写回 -/
def eifW5 : EifState := eifStep eifW4 .lateWb

-- W1 基线：A 分得 slot 0，active/idx_using 置位
theorem eifW_dispatch1_alloc : (c2wOut eifW0.c2w (c2wInReq 0x08#6)).warpReqWid = 0#3 := by decide
theorem eifW1_occupied :
    eifW1.ws.warpActive = 0b00000001#8 ∧ eifW1.c2w.idxUsing = 0b00000001#8 ∧
    eifW1.vbase (c2wFin 0#3) = 0#11 := by native_decide
theorem eifW2_inflight : eifW2.inflight.length = 1 := by decide

/-- **关键拍**：endprg 在 load 未写回时完成——inflight 原样保留、active 清除、
    槽位当拍释放 -/
theorem eifW_endprg_with_inflight :
    eifW3.inflight = eifW2.inflight ∧
    eifW3.ws.warpActive = 0#8 ∧
    eifW3.c2w.idxUsing = 0#8 := by native_decide

/-- endprg 后唯一的访存侧动作：wg 级 DCache 刷写请求有效（与在飞 load 排空
    无关，也不回灌槽位释放路径） -/
theorem eifW_flushDCache_after : (wsOut eifW3.ws wsInNop).flushDCacheValid = true := by
  native_decide

/-- 下一拍：slot 0 被 warp B 复用，vgpr_base 覆写为 128 -/
theorem eifW_reuse :
    (c2wOut eifW3.c2w (c2wInReq 0x11#6)).warpReqWid = 0#3 ∧
    eifW4.c2w.idxUsing = 0b00000001#8 ∧
    eifW4.vbase (c2wFin 0#3) = 128#11 ∧
    eifW4.ws.warpActive = 0b00000001#8 := by native_decide

/-- **污染**：迟到写回的物理地址 = 当前基址现算 = B 的逻辑 v8（读侧同式，
    operandCollector.scala:116）；A 发射时的原目的地址（base 0 现算的 2）
    反而没有收到这笔写回。B 全程未写任何寄存器，其 v8 变为 A 的 load 数据。 -/
theorem eifW_pollution :
    ocWbVecAddr 0#11 8#8 = 2#8 ∧
    ocWbVecAddr 128#11 8#8 = 34#8 ∧
    ocWbVecAddr (eifW4.vbase (c2wFin 0#3)) 8#8 = 34#8 ∧
    rf_read eifW5.rf (eifFin256 34#8) = 0xDEADBEEF#32 ∧
    rf_read eifW5.rf (eifFin256 2#8) = 0#32 ∧
    eifW5.inflight.length = 0 := by native_decide

/- ========================================================================= -/
/- 4. 修复方向的形式化：endprg 守卫 = 该 wid 无在飞写回                         -/
/-    （硬件对应：LSU.scala:577 的 fence_end(wid) 接入 warpRsp 完成条件）      -/
/- ========================================================================= -/

/-- 该 wid 是否有在飞未写回 load -/
def eifInflightOf (s : EifState) (wid : BitVec 3) : Bool :=
  s.inflight.any (fun w => w.wid == wid)

/-- endprg 守卫：该 wid 无在飞写回才允许完成 -/
def eifEndprgGuardOK (s : EifState) (wid : BitVec 3) : Bool := !eifInflightOf s wid

/-- 加守卫的组合机器：守卫不满足时 endprg 被阻塞（状态不变，等待排空） -/
def eifStepG (s : EifState) (op : EifOp) : EifState :=
  match op with
  | .endprg wid wg wf =>
      if eifEndprgGuardOK s wid then eifStep s (.endprg wid wg wf) else s
  | _ => eifStep s op

/-- 守卫安全性：放行的 endprg 满足"该 wid 无在飞写回"，且不触碰 inflight -/
theorem eif_guarded_endprg_safe (s : EifState) (wid wg wf : BitVec 3)
    (h : eifEndprgGuardOK s wid = true) :
    (eifStepG s (.endprg wid wg wf)).inflight = s.inflight ∧ eifInflightOf s wid = false := by
  unfold eifStepG
  simp only [h, if_true]
  refine ⟨rfl, ?_⟩
  unfold eifEndprgGuardOK at h
  cases hb : eifInflightOf s wid with
  | false => rfl
  | true => rw [hb] at h; exact absurd h (by decide)

/-- witness 的 endprg 拍违反守卫（在飞非空） -/
theorem eifW_guard_violated : eifEndprgGuardOK eifW2 0#3 = false := by native_decide

/-- 守卫机器阻断 witness：endprg 不生效（active/idx_using/inflight 全保持），
    等迟到写回落地后才放行——污染轨迹在守卫机器上不可达 -/
theorem eifW_guarded_blocks :
    (eifStepG eifW2 (.endprg 0#3 0#3 0#3)).ws.warpActive = 0b00000001#8 ∧
    (eifStepG eifW2 (.endprg 0#3 0#3 0#3)).c2w.idxUsing = 0b00000001#8 ∧
    (eifStepG eifW2 (.endprg 0#3 0#3 0#3)).inflight.length = 1 ∧
    -- 迟到写回落地（守卫机器里 inflight 已排空）后再次 endprg：放行，active 清除
    (eifStepG (eifStepG (eifStepG eifW2 (.endprg 0#3 0#3 0#3)) .lateWb)
      (.endprg 0#3 0#3 0#3)).ws.warpActive = 0#8 := by native_decide

/- 公理审计（bv_decide 定理带私有 LRAT trust 公理；native_decide 测试额外
   引入 Lean.ofReduceBool，归档注明） -/
#print axioms eif_endprg_preserves_inflight
#print axioms eif_step_endprg_clears_active
#print axioms eif_step_endprg_frees_slot
#print axioms eif_lateWb_uses_current_base
#print axioms eifW_endprg_with_inflight
#print axioms eifW_reuse
#print axioms eifW_pollution
#print axioms eif_guarded_endprg_safe
#print axioms eifW_guarded_blocks

end Ventus.Spec
