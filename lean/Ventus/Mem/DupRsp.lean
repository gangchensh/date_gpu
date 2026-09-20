/- ========================================================================= -/
/-                          Mem/DupRsp.lean                                  -/
/-  I-44 下游影响核销：L2"同 source 重复 refill A / 双重 AccessAckData"到达    -/
/-  L1 时各层的行为（重复响应 = 同一 d_source 的第二个 AccessAckData）。         -/
/-                                                                           -/
/-  背景（doc/03 I-44【已确认】）：L2 Scheduler 的 allocate 用 result.valid     -/
/-  （非 fire）× ListBuffer 池耗尽 ⇒ miss result 滞留 ⇒ 同一 source 的 refill   -/
/-  A 重复发出 ⇒ 外层内存返回两个同 source 的 AccessAckData。本文件核销这两     -/
/-  个响应到达 L1（DCache）及下游（LSU）时的行为。                              -/
/-                                                                           -/
/-  接口事实（Chisel 源码，2026-08-30 复核）：                                  -/
/-  * DCache.scala:616-617：missRspIn.bits.instrId =                           -/
/-    d_source(SetIdxBits+log2Up(NMshrEntry)-1, SetIdxBits)——2 位 L1MSHR       -/
/-    entry 号；:621：allocateWrite.setIdx = d_source 低 8 位（请求拍冻结的    -/
/-    set）。重复响应与正品响应的 d_source 完全相同。                           -/
/-  * DCache.scala:546-547：memRsp_Q 出队要求 missRspIn.ready ∧                -/
/-    coreRsp_Q.enq.ready ∧ tagAllocateWriteReady_mod——L1MSHR 的               -/
/-    missRspIn.ready（L1MSHR.scala:319-321，模型 l1mRspInReady）是链上唯一    -/
/-    的"响应是否被期待"检查，且它只查 subentry 行非空（used≠0）。              -/
/-  * DCache.scala:693：读 miss 的 coreRsp 数据 = memRsp_st1.d_data（响应      -/
/-    载荷直通）；:620-621 + :629 + :585-590：TagAccess.allocateWrite 与        -/
/-    DataAccess 回填写使能由 memRsp 直接驱动（不经 L1MSHR 守卫），tag 取自    -/
/-    missRspOut.bits.blockAddr（组合、无 valid 限定）。                        -/
/-  * LSU 侧：pipeline/MSHR.scala:45 的 from_dcache.ready = state===s_idle     -/
/-    （`&& used.orR` 被注释，MSHR.lean Q4）——无任何"该 instrId 是否在飞"      -/
/-    检查。                                                                   -/
/-                                                                           -/
/- ======================== 结论摘要（详见各节与返回报告） ==================== -/
/-  C1（L1MSHR，entry 已释放——孤儿响应）：被吸收，不产生 coreRsp               -/
/-      （l1mRspEnqV 的 used≠0 守卫，定理 dbr_l1m_orphan_no_coreRsp /          -/
/-      dbr_l1m_orphan_subValid_kept），簿记表（ti/blockAddr/instrId/subValid） -/
/-      不受污染；**但**有两个副作用：(a) releasing_stall 被翻转置位            -/
/-      （dbr_l1m_orphan_stall_toggle，L1MSHR.lean Q8 的触发实例）——           -/
/-      DCache.scala:217 用 !releasing_stall 拦 coreReq，粘滞反压直到下一次    -/
/-      同 entry 响应完成排空（entry 复用后自愈，属瞬时性能损失）；(b)           -/
/-      statusR 被 :235-243 的响应分支当正品推进（dbr_l1m_orphan_statusR）。   -/
/-      witness：dbrW1_orphan_absorbed / dbrW1_sole_effect_stall。             -/
/-      ⚠ DCache 级残余风险（未形式化，L1MSHR 吸收≠DCache 吸收）：孤儿响应     -/
/-      仍触发 allocateWrite/dataFill（:620-621 不经 L1MSHR 守卫），tag 取     -/
/-      残留 blockAddr（:629 无 valid 限定）、way 取 waymaskReplacement_st1     -/
/-      ——两响应之间若无新 miss 改动替换状态则为幂等重写（同 tag 同数据），    -/
/-      否则可能把旧 tag/旧数据写进错误的 way。需 TagAccess 级建模裁定，已上     -/
/-      报主会话。                                                             -/
/-  C2（L1MSHR，entry 已复用——两响应之间 entry 被分给新 miss）：**无守卫**。   -/
/-      重复响应被当成新 miss 的正品：排空新 entry 的 subentry、以新 entry 的   -/
/-      ti/blockAddr 提前发出 coreRsp（dbr_l1m_reused_consumed，witness        -/
/-      dbrW2_dup_emits_B_coreRsp）；新 miss 的正品响应随后到达时 entry 已空， -/
/-      沦为孤儿被静默吸收（dbrW2_genuine_orphaned）。端到端后果：新块 B 的     -/
/-      coreRsp 数据 = 重复响应载荷 = 旧块 A 的数据（DCache.scala:693），路由  -/
/-      信息（instrId/mask）全部合法 ⇒ LSU 无任何手段察觉；同时 allocateWrite  -/
/-      把 get_tag(B) 写进 d_source 里冻结的 A 的 set（:621,:629）⇒ tag 阵列   -/
/-      错位。**静默数据损坏（正确性级）**。触发窗口 = 两个响应到达之间         -/
/-      entry 被释放并复用（I-44 witness 两发 A 间隔 2 拍，响应间隔同量级，    -/
/-      4 entry 高流失下窗口非零，模块级不可排除）。                            -/
/-  C3（MSHRv2/LSU 消费侧）：无守卫（dbr_mshr_no_guard：ready=state==idle）。  -/
/-      孤儿响应（entry 未占用且 cm=0，即已释放表项的稳态）被吸收：不新产生    -/
/-      complete、used/tag/cm 均不变，仅写不可观测的废 data 槽                 -/
/-      （dbr_mshr_orphan_cm_kept / _tag_kept / _complete8_kept）。但复用       -/
/-      entry 场景下，任何 mask 覆盖剩余 mask 的响应都立即补齐 entry           -/
/-      （dbr_mshr_rsp_premature_complete）——配合 C2，witness                  -/
/-      dbrW3_dup_premature：warp5 的新 load 表项被 warp2 的陈旧响应数据       -/
/-      提前补齐并写回寄存器堆；warp5 的正品响应到达时 entry 已释放，先被       -/
/-      Q2 粘滞挡一拍、再被孤儿吸收（dbrW3_genuine_blocked / _orphan）。       -/
/-  C4（端到端链闭环）：I-44（已确认触发）× C2/C3（无守卫，机证 witness）     -/
/-      ⇒ 整机后果闭环成立：同 source 双重 AccessAckData 可造成**与该          -/
/-      miss 无关的另一个 warp 的 load 收到陈旧数据 + L1 tag/数据阵列错位**，   -/
/-      全链路无任何一层报错或丢弃。仅当两响应间隔内 entry 未复用时降级为       -/
/-      C1（瞬时反压 + DCache 级幂等性存疑）。                                 -/
/-  修复建议（随 I-44 上报）：L2 侧根治（allocate.valid 加 push.ready 门控）； -/
/-  L1 侧加固：missRspIn 增加"entry 在飞且未开始排空"的期待性检查，或          -/
/-  allocateWrite/dataFill 使能并入 L1MSHR 的 used≠0 守卫。                    -/
/- ========================================================================= -/

import Ventus.Mem.L1MSHR
import Ventus.Mem.MSHR

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. L1MSHR 层：守卫的精确刻画与孤儿响应（entry 已释放）的符号化结论          -/
/- ========================================================================= -/

/-- 守卫的精确刻画：missRspOut 的入队使能 = rspIn.valid ∧ 该 entry subentry 行
    非空。**不含**任何"响应是否属于当前占用者"的检查（无地址/tag 比对）。 -/
theorem dbr_l1m_guard_exact (s : L1mState) (i : L1mIn) :
    l1mRspEnqV s i = (i.rspInV && (l1mRspUsed s i != 0)) := rfl

/-- used = 0 ⇒ 该 subentry 行全空。 -/
theorem dbrL1m_used0_row (s : L1mState) (i : L1mIn) (h : l1mRspUsed s i = 0) :
    ∀ se, s.subValid (l1mRspSel i) se = false := by
  have h01 : s.subValid (l1mRspSel i) 0 = false ∧ s.subValid (l1mRspSel i) 1 = false := by
    cases h0 : s.subValid (l1mRspSel i) 0 <;> cases h1 : s.subValid (l1mRspSel i) 1 <;>
      simp_all [l1mRspUsed, l1mRspRow, l1mCount2]
  intro se
  have hse : se = 0 ∨ se = 1 := by
    have hlt := se.isLt
    have hv : se.val = 0 ∨ se.val = 1 := by omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hse with rfl | rfl
  · exact h01.1
  · exact h01.2

/-- C1 正面：孤儿响应（used=0）不产生任何 coreRsp（唯一的守卫）。 -/
theorem dbr_l1m_orphan_no_coreRsp (s : L1mState) (i : L1mIn)
    (hused : l1mRspUsed s i = 0) :
    l1mRspEnqV s i = false := by
  simp [l1mRspEnqV, hused]

/-- C1 正面：孤儿响应被正常接收弹出（ready=1，被吸收而非报错/挂死）。
    前提 reqV=false（同拍无 missReq，:321 的反压项不介入）。 -/
theorem dbr_l1m_orphan_absorbed_ready (s : L1mState) (i : L1mIn)
    (hreq : i.reqV = false) (hused : l1mRspUsed s i = 0) :
    l1mRspInReady s i = true := by
  simp [l1mRspInReady, hused, hreq]

/-- C1 正面：孤儿响应不污染 subValid（清除分支写 false 到本就全空的行，无操作）。 -/
theorem dbr_l1m_orphan_subValid_kept (s : L1mState) (i : L1mIn)
    (hreq : i.reqV = false) (hused : l1mRspUsed s i = 0) :
    (l1mStep s i).subValid = s.subValid := by
  have hrf : l1mReqFire s i = false := by simp [l1mReqFire, hreq]
  have hrow := dbrL1m_used0_row s i hused
  funext e se
  by_cases he : e = l1mRspSel i
  · subst he
    have hfalse := hrow se
    by_cases hb : (se == l1mNext2Cancel s i) && i.rspInV && l1mQEnqRdy s.rspQ <;>
      simp_all [l1mStep]
  · have hbe : (e == l1mRspSel i) = false := by simp [beq_eq_false_iff_ne, he]
    simp_all [l1mStep]

/-- C1 正面：孤儿响应不触碰 ti/blockAddr/instrId 簿记表
    （三表更新都以 reqFire 为使能）。 -/
theorem dbr_l1m_orphan_tables_kept (s : L1mState) (i : L1mIn)
    (hreq : i.reqV = false) :
    (l1mStep s i).ti = s.ti ∧ (l1mStep s i).blockAddr = s.blockAddr ∧
    (l1mStep s i).instrId = s.instrId := by
  have hrf : l1mReqFire s i = false := by simp [l1mReqFire, hreq]
  simp [l1mStep, hrf]

/-- C1 副作用 (a)：孤儿响应**翻转** releasing_stall（:360-366，L1MSHR.lean Q8
    的触发实例）——未置位时置位（粘滞反压，DCache.scala:217 拦 coreReq），
    已置位时清除（同 entry 下一次响应 pop 时自愈）。其他 entry 不变。 -/
theorem dbr_l1m_orphan_stall_toggle (s : L1mState) (i : L1mIn)
    (hrsp : i.rspInV = true) (hreq : i.reqV = false) (hused : l1mRspUsed s i = 0) :
    (l1mStep s i).releasing (l1mRspSel i) = !s.releasing (l1mRspSel i) ∧
    ∀ e, e ≠ l1mRspSel i → (l1mStep s i).releasing e = s.releasing e := by
  have hready := dbr_l1m_orphan_absorbed_ready s i hreq hused
  have hfire : l1mRspInFire s i = true := by simp [l1mRspInFire, hrsp, hready]
  constructor
  · cases h : s.releasing (l1mRspSel i) <;> simp [l1mStep, hfire, hrsp, h]
  · intro e hne
    have hd : decide (e = l1mRspSel i) = false := decide_eq_false hne
    simp [l1mStep, hd, hfire, hrsp]

/-- C1 副作用 (b)：孤儿响应被 :235-243 的响应分支当正品推进 statusR——
    PRIMARY_FULL(1)/SECONDARY_AVAIL(2)/SECONDARY_FULL_RETURN(4) 被清零。
    方向保守（放行更多请求），但证明孤儿并非纯透明。 -/
theorem dbr_l1m_orphan_statusR (s : L1mState) (i : L1mIn)
    (hrsp : i.rspInV = true) (hreq : i.reqV = false) (hprobe : i.probeV = false)
    (hused : l1mRspUsed s i = 0) :
    (l1mStep s i).statusR =
      (if (s.statusR == 1#3 || s.statusR == 2#3 || s.statusR == 4#3) then 0#3
       else s.statusR) := by
  have hrf : l1mReqFire s i = false := by simp [l1mReqFire, hreq]
  have hu1 : (l1mRspUsed s i == 1) = false := by simp [hused]
  have hu0 : (l1mRspUsed s i == 0) = true := by simp [hused]
  simp only [l1mStep, l1mStatusRN, hrf, hprobe, hrsp, hu1, hu0]
  by_cases h12 : (s.statusR == 1#3 || s.statusR == 2#3) = true <;>
    by_cases h4 : (s.statusR == 4#3) = true <;> simp_all

/-- C2 核心：entry 非空（含"已复用"情形）时，任何携带该 entry 号的响应都被当
    正品消费——立即以**当前占用者**的 ti/blockAddr 发出 coreRsp 并清掉一个
    subentry，无任何归属检查。 -/
theorem dbr_l1m_reused_consumed (s : L1mState) (i : L1mIn)
    (hrsp : i.rspInV = true) (hused : l1mRspUsed s i ≠ 0)
    (hq : l1mQEnqRdy s.rspQ = true) (hreq : i.reqV = false) (hrdy : i.rspOutRdy = true) :
    l1mRspOutFire s i = true ∧
    (l1mRspOutBits s i).ti = s.ti (l1mRspSel i) (l1mNext2Cancel s i) ∧
    (l1mRspOutBits s i).ba = s.blockAddr (l1mRspSel i) ∧
    (l1mStep s i).subValid (l1mRspSel i) (l1mNext2Cancel s i) = false := by
  have hu : (l1mRspUsed s i != 0) = true := bne_iff_ne.mpr hused
  have hev : l1mRspEnqV s i = true := by simp [l1mRspEnqV, hrsp, hu]
  have hfull : s.rspQ.full = false := by
    cases h : s.rspQ.full <;> simp_all [l1mQEnqRdy]
  have hrf : l1mReqFire s i = false := by simp [l1mReqFire, hreq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [l1mRspOutFire, l1mRspOutValid, l1mQDeqValid, hfull, hev, hrdy]
  · simp [l1mRspOutBits, l1mQDeqBits, hfull, l1mRspEnqBits]
  · simp [l1mRspOutBits, l1mQDeqBits, hfull, l1mRspEnqBits]
  · simp [l1mStep, hrf, hrsp, hq]

/- ========================================================================= -/
/- 2. L1MSHR witness 轨迹（从初态可达，native_decide 机证）                    -/
/- ========================================================================= -/

/-- 分配输入：probe+missReq 同拍穿透（同 l1mT1 流程），块 A=0x10 / 块 B=0x20。 -/
def dbrIAllocA : L1mIn := ⟨true, 0x10#25, true, 0x10#25, 5#3, 0xAAAA#323, false, 0, true, true, true⟩
def dbrIAllocB : L1mIn := ⟨true, 0x20#25, true, 0x20#25, 6#3, 0xBBBB#323, false, 0, true, true, true⟩
/-- 响应输入：rspIn.valid=1、rspIdx=entry0、rspOut.ready=1。正品与重复响应同形
    （d_source 完全相同，见文件头 :616-617）。 -/
def dbrIRsp : L1mIn := ⟨false, 0, false, 0, 0, 0, true, 0#2, true, true, true⟩

/- ---- W1：孤儿响应（entry 已释放未复用）——被吸收 + 粘滞 stall ---- -/

def dbrW1S1 := l1mStep l1mInit dbrIAllocA   -- c0：分配 entry0（块 A）
def dbrW1S2 := l1mStep dbrW1S1 dbrIRsp       -- c1：正品响应排空 subentry0（coreRsp 发出）
def dbrW1S3 := l1mStep dbrW1S2 dbrIRsp       -- c2：used=0，正品 pop，entry0 释放
def dbrW1S4dup := l1mStep dbrW1S3 dbrIRsp    -- c3：重复响应到达（孤儿）
def dbrW1S4idl := l1mStep dbrW1S3 l1mInIdle  -- c3 对照：无重复响应

-- 正常流程基线：正品响应发出 A 的 coreRsp，第二拍 pop，entry0 干净释放
theorem dbrW1_genuine_drains :
    l1mRspOutValid dbrW1S1 dbrIRsp = true ∧
    (l1mRspOutBits dbrW1S1 dbrIRsp).ti = 0xAAAA#323 ∧
    l1mRspInFire dbrW1S2 dbrIRsp = true ∧
    l1mEmpty dbrW1S3 = true ∧
    dbrW1S3.releasing ⟨0, by decide⟩ = false := by
  native_decide

-- 孤儿响应：不产生 coreRsp、被正常弹出吸收、簿记表保持（entry 仍空、残留不污染）
theorem dbrW1_orphan_absorbed :
    l1mRspOutValid dbrW1S3 dbrIRsp = false ∧
    l1mRspInFire dbrW1S3 dbrIRsp = true ∧
    l1mEmpty dbrW1S4dup = true ∧
    dbrW1S4dup.blockAddr ⟨0, by decide⟩ = 0x10#25 ∧
    dbrW1S4dup.ti ⟨0, by decide⟩ ⟨0, by decide⟩ = 0xAAAA#323 := by
  native_decide

-- 唯一可观测副作用：releasing_stall(0) 粘滞置位（对照组不置位）
theorem dbrW1_sole_effect_stall :
    dbrW1S4dup.releasing ⟨0, by decide⟩ = true ∧
    l1mReleasingStall dbrW1S4dup = true ∧
    dbrW1S4idl.releasing ⟨0, by decide⟩ = false ∧
    l1mReleasingStall dbrW1S4idl = false := by
  native_decide

/- ---- W2：复用 entry（两响应之间 entry0 分给新 miss 块 B）——污染 witness ---- -/

def dbrW2S4 := l1mStep dbrW1S3 dbrIAllocB   -- c3'：entry0 复用给块 B（新 miss）
def dbrW2S5 := l1mStep dbrW2S4 dbrIRsp       -- c4'：重复响应到达——被当成 B 的正品
def dbrW2S6 := l1mStep dbrW2S5 dbrIRsp       -- c5'：used=0，重复响应 pop
def dbrW2S7 := l1mStep dbrW2S6 dbrIRsp       -- c6'：B 的正品响应到达——孤儿

-- 复用成立：entry0 现在属于块 B
theorem dbrW2_realloc :
    dbrW2S4.subValid ⟨0, by decide⟩ ⟨0, by decide⟩ = true ∧
    dbrW2S4.blockAddr ⟨0, by decide⟩ = 0x20#25 ∧
    dbrW2S4.ti ⟨0, by decide⟩ ⟨0, by decide⟩ = 0xBBBB#323 := by
  native_decide

-- 核心 witness：重复响应驱动输出了 **B 的** coreRsp（ti/ba 全合法，下游无法察觉；
-- 但 coreRsp 数据 = 重复响应载荷 = A 的旧数据，DCache.scala:693）
theorem dbrW2_dup_emits_B_coreRsp :
    l1mRspOutValid dbrW2S4 dbrIRsp = true ∧
    (l1mRspOutBits dbrW2S4 dbrIRsp).ti = 0xBBBB#323 ∧
    (l1mRspOutBits dbrW2S4 dbrIRsp).ba = 0x20#25 ∧
    l1mRspInReady dbrW2S4 dbrIRsp = false ∧
    l1mRspInFire dbrW2S5 dbrIRsp = true := by
  native_decide

-- B 的正品响应到达时 entry 已空：被静默吸收（无 coreRsp、无报错），
-- 并再次置位 releasing_stall
theorem dbrW2_genuine_orphaned :
    l1mEmpty dbrW2S6 = true ∧
    l1mRspOutValid dbrW2S6 dbrIRsp = false ∧
    dbrW2S7.releasing ⟨0, by decide⟩ = true ∧
    l1mReleasingStall dbrW2S7 = true := by
  native_decide

/- ========================================================================= -/
/- 3. MSHRv2（LSU 消费侧）：无守卫 + 孤儿吸收 + 提前补齐                       -/
/- ========================================================================= -/

/-- C3：from_dcache 的唯一门控是 state==s_idle（MSHR.scala:45；
    `&& used.orR` 被注释，MSHR.lean Q4）——无"该 instrId 是否在飞"检查。 -/
theorem dbr_mshr_no_guard (s : MshrState) : mshrDcRdy s = s.state.isIdle := rfl

/-- C3 正面：孤儿响应（已释放表项的稳态：used=0 且 cm=0）不改 currentMask。
    （cm=0 的表项再清批仍是 0；写废 data 槽不可观测，MSHR.lean D1。） -/
theorem dbr_mshr_orphan_cm_kept (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true)
    (hcm : s.currentMask (mshrIdx3 i.rspId) = 0#32) :
    (mshrStep s i).currentMask = s.currentMask := by
  have hidle : s.state.isIdle = true := by simp [MshrFSM.isIdle, hs]
  funext e
  simp only [mshrStep, mshrCmN, hidle, hdc, Bool.true_and, if_true]
  by_cases he : e = mshrIdx3 i.rspId
  · subst he
    rw [mshrUpd_self, hcm]
    simp
  · exact mshrUpd_of_ne _ _ _ _ he

/-- C3 正面：孤儿响应不改 tag 表（响应拍 :75-78/:86-89 两个分配分支均不成立）。 -/
theorem dbr_mshr_orphan_tag_kept (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true) :
    (mshrStep s i).tag = s.tag := by
  have hidle : s.state.isIdle = true := by simp [MshrFSM.isIdle, hs]
  have hnotadd : s.state.isAdd = false := by simp [MshrFSM.isAdd, hs]
  simp [mshrStep, mshrTagN, hidle, hnotadd, hdc]

/-- C3 正面：孤儿响应不新产生 complete（used 不变 + cm 不变 ⇒ complete8 不变），
    即不会触发任何伪输出；也不释放任何表项（used 不变）。 -/
theorem dbr_mshr_orphan_complete8_kept (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true)
    (hcm : s.currentMask (mshrIdx3 i.rspId) = 0#32) :
    mshrComplete8 (mshrStep s i) = mshrComplete8 s := by
  have hcmk := dbr_mshr_orphan_cm_kept s i hs hdc hcm
  have husk : (mshrStep s i).used = s.used := mshr_used_unchanged_of_idle_dcFire s i hs hdc
  have hEC : ∀ j : Fin 8, mshrEntryComplete (mshrStep s i) j = mshrEntryComplete s j := by
    intro j
    simp only [mshrEntryComplete, mshrUsedBit, mshrUsedBit3]
    rw [hcmk, husk]
  simp only [mshrComplete8, hEC]

/-- C3 核心：任何 mask 覆盖剩余 mask 的响应都立即补齐该 entry——无来源/次序
    检查（:71 清批 + :37 complete 判定）。重复/陈旧响应据此提前完成复用表项。 -/
theorem dbr_mshr_rsp_premature_complete (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true)
    (hused : mshrUsedBit s (mshrIdx3 i.rspId) = true)
    (hcover : s.currentMask (mshrIdx3 i.rspId) &&& ~~~i.rspMask = 0#32) :
    mshrEntryComplete (mshrStep s i) (mshrIdx3 i.rspId) = true := by
  have hcm : (mshrStep s i).currentMask (mshrIdx3 i.rspId) = 0#32 := by
    rw [mshr_rsp_cm_update s i hs hdc, hcover]
  have hu : (mshrStep s i).used = s.used := mshr_used_unchanged_of_idle_dcFire s i hs hdc
  have hub : mshrUsedBit (mshrStep s i) (mshrIdx3 i.rspId) = true := by
    simp only [mshrUsedBit, mshrUsedBit3]; rw [hu]; exact hused
  simp [mshrEntryComplete, hcm, hub]

/- ---- W3：复用 entry 被陈旧数据提前补齐（寄存器堆级数据损坏 witness） ---- -/

/-- warp2 的 load 表项 / warp5 的新 load 表项（mask=lanes 0,1，全按 lw 抽取）。 -/
def dbrMshrTagA : MshrTag :=
  { warp_id := 2, wfd := true, wxd := false, reg_idxw := 5, mask := 0x3#32,
    unsigned := false, isvec := true, wordOffset1H := fun _ => 0xF#4, isWrite := false }
def dbrMshrTagB : MshrTag := { dbrMshrTagA with warp_id := 5, reg_idxw := 9 }

/-- 陈旧响应数据（A 的载荷）与 B 的正品数据。 -/
def dbrDataA : Fin 32 → BitVec 32 :=
  fun l => if l.val = 0 then 0xAAAA0000#32 else if l.val = 1 then 0xBBBB1111#32 else 0
def dbrDataB : Fin 32 → BitVec 32 :=
  fun l => if l.val = 0 then 0x0000CCCC#32 else 0

def dbrMAllocA : MshrIn := ⟨true, dbrMshrTagA, false, 0, fun _ => 0, 0, false⟩
def dbrMRspA : MshrIn := ⟨false, mshrTagDefault, true, 0#3, dbrDataA, 0x3#32, true⟩
def dbrMOutFire : MshrIn := ⟨false, mshrTagDefault, false, 0, fun _ => 0, 0, true⟩
def dbrMAllocB : MshrIn := ⟨true, dbrMshrTagB, false, 0, fun _ => 0, 0, false⟩
def dbrMRspB : MshrIn := ⟨false, mshrTagDefault, true, 0#3, dbrDataB, 0x3#32, true⟩

def dbrM1 := mshrStep mshrInit dbrMAllocA      -- c0：分配 entry0（warp2 的 load）
def dbrM2 := mshrStep dbrM1 dbrMRspA           -- c1：正品响应补齐 → s_out
def dbrM3 := mshrStep dbrM2 dbrMOutFire        -- c2：输出 fire，entry0 释放
def dbrM4 := mshrStep dbrM3 mshrInIdle         -- c3：Q2 粘滞拍后回 idle
def dbrM5 := mshrStep dbrM4 dbrMAllocB         -- c4：entry0 复用给 warp5 的新 load
def dbrM6 := mshrStep dbrM5 dbrMRspA           -- c5：重复（陈旧）响应 → 提前补齐
def dbrM7 := mshrStep dbrM6 dbrMOutFire        -- c6：输出 fire：warp5 ← A 的旧数据
def dbrM8 := mshrStep dbrM7 dbrMRspB           -- c7：B 的正品响应到达，被 Q2 粘滞挡回
def dbrM9 := mshrStep dbrM8 dbrMRspB           -- c8：重试——孤儿吸收

-- 正常流程基线：warp2 的 load 正确输出
theorem dbrW3_normal_flow :
    mshrOutValid dbrM2 = true ∧
    (mshrOutTag dbrM2).warp_id = 2#3 ∧
    mshrOutData dbrM2 ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    dbrM3.used = 0#8 := by
  native_decide

-- 复用成立：entry0 属于 warp5 的新 load
theorem dbrW3_realloc :
    dbrM5.used = 0x01#8 ∧
    (dbrM5.tag ⟨0, by decide⟩).warp_id = 5#3 ∧
    dbrM5.currentMask ⟨0, by decide⟩ = 0x3#32 ∧
    dbrM5.state = .idle := by
  native_decide

-- 核心 witness：陈旧响应把 warp5 的表项提前补齐，输出数据是 warp2 的旧数据
theorem dbrW3_dup_premature :
    mshrEntryComplete dbrM6 ⟨0, by decide⟩ = true ∧
    mshrOutValid dbrM6 = true ∧
    (mshrOutTag dbrM6).warp_id = 5#3 ∧
    mshrOutData dbrM6 ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    mshrOutData dbrM6 ⟨1, by decide⟩ = 0xBBBB1111#32 ∧
    dbrM7.used = 0#8 := by
  native_decide

-- B 的正品响应：首拍被 Q2 粘滞（state=s_out 多停一拍）挡回
theorem dbrW3_genuine_blocked :
    mshrDcFire dbrM7 dbrMRspB = false ∧ dbrM8.state = .idle := by
  native_decide

-- 重试后被孤儿吸收：不产生 complete、不释放、不输出、tag 不动
theorem dbrW3_genuine_orphan :
    mshrDcFire dbrM8 dbrMRspB = true ∧
    mshrComplete8 dbrM9 = 0#8 ∧
    dbrM9.used = 0#8 ∧
    mshrOutValid dbrM9 = false ∧
    (dbrM9.tag ⟨0, by decide⟩).warp_id = 5#3 := by
  native_decide

/- ---- 公理审计（native_decide witness 带各定理 `_native.native_decide.ax_1_1`
     信任公理，属本项目 4.31 工具链下的预期，归档注明） ---- -/

#print axioms dbr_l1m_guard_exact
#print axioms dbr_l1m_orphan_no_coreRsp
#print axioms dbr_l1m_orphan_absorbed_ready
#print axioms dbr_l1m_orphan_subValid_kept
#print axioms dbr_l1m_orphan_tables_kept
#print axioms dbr_l1m_orphan_stall_toggle
#print axioms dbr_l1m_orphan_statusR
#print axioms dbr_l1m_reused_consumed
#print axioms dbrW1_genuine_drains
#print axioms dbrW1_orphan_absorbed
#print axioms dbrW1_sole_effect_stall
#print axioms dbrW2_realloc
#print axioms dbrW2_dup_emits_B_coreRsp
#print axioms dbrW2_genuine_orphaned
#print axioms dbr_mshr_no_guard
#print axioms dbr_mshr_orphan_cm_kept
#print axioms dbr_mshr_orphan_tag_kept
#print axioms dbr_mshr_orphan_complete8_kept
#print axioms dbr_mshr_rsp_premature_complete
#print axioms dbrW3_normal_flow
#print axioms dbrW3_realloc
#print axioms dbrW3_dup_premature
#print axioms dbrW3_genuine_blocked
#print axioms dbrW3_genuine_orphan

end Ventus.Mem
