/- ========================================================================= -/
/-                      CTA/CtaScheduler.lean                                 -/
/-  CTA 级调度器顶层（cta_scheduler_top）的 Lean 4 模型：组合契约 +            -/
/-  WG 生命周期抽象状态机                                                     -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/cta_scheduler.scala      -/
/-    （class cta_scheduler_top，:106-145；数据 Bundle :14-104）               -/
/-  例化上下文：GPGPU_top.scala:54-114（CTAinterface：host2CTA 字段映射        -/
/-    :64-79、cu_wf_new/cu_wf_done 与各 SM 的 CTA2warp 对接 :88-113）。        -/
/-  参数（top/parameters.scala:164-197）：NUM_CU=2 (:167, num_sm=2)、           -/
/-    NUM_WG_SLOT=8 (:169, num_block)、NUM_WF_MAX=8 (:179, num_warp_in_a_block)、-/
/-    NUM_SGPR_MAX=2048 (:181, 256*8)、NUM_VGPR_MAX=1024 (:182, 128*8)、        -/
/-    NUM_LDS_MAX=131072 (:180, 1024*32*4)、WG_BUFFER.NUM_ENTRIES=8 (:191)、    -/
/-    WF_TAG_WIDTH=6 (:187)、WG_ID_WIDTH=32 (:176)。                            -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. cta_scheduler_top 本身**没有逻辑**，只有 :122-125 的 init_ok 门控和     -/
/-      连线；wg_buffer / allocator / resource_table_top / cu_interface 四个    -/
/-      子模块本波**不建模**，其接口行为写成显式契约（CtasEventOk 的各分支，    -/
/-      集中注释见第 3 节"黑盒契约清单"）。                                  -/
/-      【2026-09-06 状态更新】八条契约随后已全部核销（各子模块建模完成，       -/
/-      见 doc/03-bug发现报告.md I-25 条目末"CtasEventOk 八条契约至此全部      -/
/-      核销完毕"与 Spec/Contracts.lean 登记册）；本文件头注的"波 10 验证     -/
/-      债务"表述自此过时。                                                  -/
/-  D2. 抽象事件模型：每个握手 fire 抽象为一个事件（hostNew/alloc/wfNew/        -/
/-      wfDone/dealloc），不做逐拍建模；事件的可发生条件 = 子模块契约。         -/
/-  D3. 资源量（base/size、wf 计数）用 Nat：各域上界 ≤ 2^18（NUM_LDS_MAX+1），  -/
/-      契约保证界内，无回绕问题；id/tag 用 BitVec（精确性要紧）。              -/
/-  D4. hostNew 只记账 pending 数（wg_buffer 内容抽象掉）；wgId 的正确流转      -/
/-      由契约 H-CUIF-DEALLOC 表达。                                            -/
/-  D5. resource_table 的 DEBUG 断言（:613 PopCount(valid)=cnt、handler :323    -/
/-      等）与 allocator :91 的断言只在仿真存在——本模型把对应性质写成契约。    -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1. :123-124 init_ok 门控双向正确（valid/ready 都门控）：init 期间           -/
/-      （cu_interface 清零 wf_gather_cnt，16 拍）host 事务不会进入 wg_buffer。 -/
/-      cu_wf_done/cu_wf_new 不门控无害（此前不可能有在跑 WF）。                -/
/-  Q2. GPGPU_top.scala:64-79 的 host2CTA→host_wg_new 字段映射逐字段核对：      -/
/-      一致；仅 num_wg_x/y/z → dispatch2cu_wgid_x/y/z 的命名错位（语义是       -/
/-      "kernel 网格维度"），记录在案。                                         -/
/-  Q3 = 跨模块警报（接 CTA2warp.lean Q1/I-23 候选）：契约 H-CUIF-DONE 依赖     -/
/-      cu_wf_done 的 wf_tag 指向正确的 (cu, wg_slot)；该 tag 来自 CTA2warp     -/
/-      的 data(wid) **迟读**（CTA2warp.scala:77），wid 复用后可被污染 →        -/
/-      cu_interface 把 done 计到错误槽位 → 旧 WG 泄漏 + 新 WG 提前完成。       -/
/-      即：本文件证明的"不超分/不冲突/回收精确"以 H-CUIF-DONE 为前提，         -/
/-      而 CTA2warp 侧已给出该前提可被违反的 witness（c2w T7）。                -/
/-  Q4（2026-09-06 状态更新：两侧已建模，残留缺口 G2 在案）：allocator 的     -/
/-      资源检查用自己的 rtcache 缓存（allocator.scala:251-262），缓存 = rt     -/
/-      最近 SCAN 的最大两段 ± alloc 扣减（:86-92）。当前核销状态：            -/
/-      Allocator 侧已证（alc_h_alloc_fit/alc_assert91：分配决策相对 rtcache   -/
/-      内容不漏不超）；ResourceTable 侧已证 rt_scan_max（rtcache(0) = 最大    -/
/-      空段）；**缓存与 rt 实际链表的时序一致性半边（SCAN 未完成窗口）无      -/
/-      定理，已登记为 Spec/Contracts.lean 的缺口 G2**（H-ALLOC-FIT 条目       -/
/-      evidence 栏）。若缓存高估，H-ALLOC-FIT 失效，ctasX2 反例显示顶层       -/
/-      无任何自保。                                                           -/
/-  Q5. resource_table_handler 的 alloc/dealloc 同拍互斥（:188 断言）核查：     -/
/-      dealloc.ready 含 !io.alloc.valid（:142），同拍双 valid 时 dealloc 不    -/
/-      fire → 断言成立。记录在案，非 bug。                                     -/
/-  Q6. cu_interface.scala:77：WG 描述符在最后一个 WF 发出时才弹出              -/
/-      （fifo.deq.ready = splitter_cnt==1 && cu ready）——CTA2warp 反压         -/
/-      （idx_using 满）会正确回堵 splitter，无协议问题。记录在案。              -/
/-  未覆盖范围（2026-09-10 更新）：四个子模块均已逐拍建模；活性方向         -/
/-      "每个被 alloc 的 WG 最终被回收"已由 VentusF/CtaLiveness.lean          -/
/-      立项消解为条件形式（ctl_liveness/ctl_alloc_eventually_dealloc/        -/
/-      ctl_all_drained：前提包 = 轨迹展开 + CtasEventOk + 三个事件级命名      -/
/-      事实——其中 ctlWfDoneLive 依赖取指级 hcov，被 I-49 裁定不可免费        -/
/-      获得）。                                                              -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.CTA

set_option linter.unusedVariables false

open Ventus.Base

/- ========================================================================= -/
/- 1. 参数与 wf_tag 布局                                                       -/
/- ========================================================================= -/

def ctasNUM_CU : Nat := 2            -- parameters.scala:167
def ctasNUM_WG_SLOT : Nat := 8       -- :169
def ctasNUM_WF_MAX : Nat := 8        -- :179
def ctasNUM_SGPR_MAX : Nat := 2048   -- :181 (256*num_warp)
def ctasNUM_VGPR_MAX : Nat := 1024   -- :182 (128*num_warp)
def ctasNUM_LDS_MAX : Nat := 131072  -- :180 (sharemem_size)
def ctasWGBUF_ENTRIES : Nat := 8     -- :191

/-- wf_tag = cat(wg_slot_id, wf_id)（cu_interface.scala:108-112，:35-37）-/
def ctasWfTag (slot wf : BitVec 3) : BitVec 6 := (slot.zeroExtend 6 <<< 3) ||| wf.zeroExtend 6

/-- 从完成 tag 提取 wg_slot_id（cu_interface.scala:161） -/
def ctasTagSlot (tag : BitVec 6) : BitVec 3 := tag.extractLsb' 3 3

/-- 从完成 tag 提取 wf_id -/
def ctasTagWf (tag : BitVec 6) : BitVec 3 := tag.extractLsb' 0 3

/-- TAG1 wf_tag 布局往返正确（回收定位的位级基础） -/
theorem ctas_tag_roundtrip (slot wf : BitVec 3) :
    ctasTagSlot (ctasWfTag slot wf) = slot ∧ ctasTagWf (ctasWfTag slot wf) = wf := by
  unfold ctasWfTag ctasTagSlot ctasTagWf
  bv_decide

/- ========================================================================= -/
/- 2. init_ok 门控（:122-125，本模块唯一的真实逻辑）                            -/
/- ========================================================================= -/

/-- host_wg_new.fire：:123-124 的双向门控 -/
def ctasHostFire (hostValid wgbufReady initOk : Bool) : Bool := hostValid && initOk && wgbufReady

/-- CTAS0a fire ⇒ initOk（init 期间 host 事务不会进入系统） -/
theorem ctas_hostFire_imp_initOk (v r i : Bool) (h : ctasHostFire v r i = true) : i = true := by
  unfold ctasHostFire at h
  cases v <;> cases r <;> cases i <;> simp_all

/-- CTAS0b init 未就绪时必然不 fire -/
theorem ctas_hostFire_blocked_init (v r : Bool) : ctasHostFire v r false = false := by
  cases v <;> cases r <;> rfl

/-- CTAS0c fire 的完整刻画 -/
theorem ctas_hostFire_iff (v r i : Bool) :
    ctasHostFire v r i = true ↔ v = true ∧ r = true ∧ i = true := by
  unfold ctasHostFire; cases v <;> cases r <;> cases i <;> simp

/- ========================================================================= -/
/- 3. 抽象生命周期模型与黑盒契约                                               -/
/-                                                                           -/
/-  黑盒契约清单（CtasEventOk 各分支；原波 10 核销目标，现已全部核销——       -/
/-  见上述 D1 状态更新）：                                                   -/
/-   H-WGB   hostNew ⇒ pending < 8：wg_buffer 反压                             -/
/-           （wg_buffer.scala:85，ready = 有空槽）。                           -/
/-   H-ALLOC-PENDING alloc ⇒ pending > 0：只分派已收到的 WG                    -/
/-           （allocator.scala:187-188 从 wg_buffer 取）。                      -/
/-   H-ALLOC-SLOT  alloc ⇒ 目标槽空闲：allocator 的 wgslot 簿记                -/
/-           （:162,:270-271 选 ~wgslot 的置位位，:295 置位）。                 -/
/-   H-WF    1 ≤ numWf ≤ 8：host 契约 + WG 定义。                              -/
/-   H-RT-BOUNDS   rt 分配的基址+尺寸在界内（resource_table.scala:301-307,     -/
/-           364-369 段查找与写入；addr2 = base+size-1）。                      -/
/-   H-RT-DISJOINT 新分配与所有在驻 WG 的三类资源区间两两不交                   -/
/-           （链表按地址有序查找空段，:281-313）。                             -/
/-   H-ALLOC-FIT   used + size ≤ MAX：allocator 资源检查（:251-262 的           -/
/-           `rtcache.size(j) >= wg.num_*` + writer 扣减断言 :91）。            -/
/-   H-CUIF-SPLIT  wfNew ⇒ wfSent < numWf：splitter 恰好派 numWf 个 WF         -/
/-           （cu_interface.scala:71-82,99-113）。                              -/
/-   H-CUIF-DONE   wfDone ⇒ wfDone < wfSent 且 tag 指向本槽：只有已派发的       -/
/-           WF 会完成（cu_interface.scala:161,171,179）。**依赖 CTA2warp       -/
/-           的 tag 正确性——可被 I-23 候选破坏，见 Q3！**                       -/
/-   H-CUIF-DEALLOC dealloc ⇒ 该槽 wfDone = numWf 且 wgId 与在驻记录一致：      -/
/-           wf_gather_finish（:179）触发，:204-223 配对发出 rt_dealloc 与      -/
/-           host_wg_done。                                                     -/
/- ========================================================================= -/

/-- 在驻 WG 的幽灵记录（本模型不跟踪硬件寄存器内容，只跟踪调度相关字段） -/
structure CtasWgRec where
  wgId : BitVec 32   -- WG_ID_WIDTH=32
  numWf : Nat        -- 该 WG 的 WF 数
  sgprBase : Nat     -- sgpr 区间 [base, base+size)
  sgprSize : Nat
  vgprBase : Nat
  vgprSize : Nat
  ldsBase : Nat
  ldsSize : Nat
  wfSent : Nat       -- 已派发到 CU 的 WF 数
  wfDone : Nat       -- 已回收的 WF 数
  deriving DecidableEq

/-- CTA 调度器的抽象状态 -/
structure CtasState where
  live : Fin 2 → Fin 8 → Option CtasWgRec   -- 每 CU 每 wg 槽的在驻记录
  pending : Nat                             -- wg_buffer 中已收未派的 WG 数

def ctasInit : CtasState := ⟨fun _ _ => none, 0⟩

/-- 写槽（cu, slot 处更新，其余不变） -/
def ctasWrite (lv : Fin 2 → Fin 8 → Option CtasWgRec) (cu : Fin 2) (slot : Fin 8)
    (v : Option CtasWgRec) : Fin 2 → Fin 8 → Option CtasWgRec :=
  fun c j => if c = cu ∧ j = slot then v else lv c j

/-- 槽位对某资源的占用（空槽 = 0） -/
def ctasSlotRes (o : Option CtasWgRec) (proj : CtasWgRec → Nat) : Nat :=
  match o with | none => 0 | some r => proj r

/-- 8 槽求和 -/
def ctasSum8 (f : Fin 8 → Nat) : Nat :=
  f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
  f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩

/-- 某 CU 某资源的总占用（Σ 已分配） -/
def ctasUsed (s : CtasState) (cu : Fin 2) (proj : CtasWgRec → Nat) : Nat :=
  ctasSum8 (fun j => ctasSlotRes (s.live cu j) proj)

/-- 单条在驻记录的合法性与界内性 -/
def ctasRecOk (o : Option CtasWgRec) : Prop :=
  match o with
  | none => True
  | some r =>
    1 ≤ r.numWf ∧ r.numWf ≤ ctasNUM_WF_MAX ∧ r.wfDone ≤ r.wfSent ∧ r.wfSent ≤ r.numWf ∧
    r.sgprBase + r.sgprSize ≤ ctasNUM_SGPR_MAX ∧
    r.vgprBase + r.vgprSize ≤ ctasNUM_VGPR_MAX ∧
    r.ldsBase + r.ldsSize ≤ ctasNUM_LDS_MAX

/-- 两个 WG 的三类资源区间两两不交 -/
def ctasDisjoint (r1 r2 : CtasWgRec) : Prop :=
  (r1.sgprBase + r1.sgprSize ≤ r2.sgprBase ∨ r2.sgprBase + r2.sgprSize ≤ r1.sgprBase) ∧
  (r1.vgprBase + r1.vgprSize ≤ r2.vgprBase ∨ r2.vgprBase + r2.vgprSize ≤ r1.vgprBase) ∧
  (r1.ldsBase + r1.ldsSize ≤ r2.ldsBase ∨ r2.ldsBase + r2.ldsSize ≤ r1.ldsBase)

/-- 两个槽位的记录相容（同在驻 ⇒ 区间不交） -/
def ctasPairOk (o1 o2 : Option CtasWgRec) : Prop :=
  match o1, o2 with
  | some r1, some r2 => ctasDisjoint r1 r2
  | _, _ => True

/-- 顶层不变式：资源不超分（Σ ≤ MAX）∧ 记录合法 ∧ 槽位两两相容 ∧ 缓冲有界 -/
@[reducible] def CtasInv (s : CtasState) : Prop :=
  (∀ cu, ctasUsed s cu CtasWgRec.sgprSize ≤ ctasNUM_SGPR_MAX ∧
         ctasUsed s cu CtasWgRec.vgprSize ≤ ctasNUM_VGPR_MAX ∧
         ctasUsed s cu CtasWgRec.ldsSize ≤ ctasNUM_LDS_MAX) ∧
  (∀ cu slot, ctasRecOk (s.live cu slot)) ∧
  (∀ cu s1 s2, s1 ≠ s2 → ctasPairOk (s.live cu s1) (s.live cu s2)) ∧
  s.pending ≤ ctasWGBUF_ENTRIES

/-- 抽象事件（每个握手 fire 一个事件，D2） -/
inductive CtasEvent where
  | hostNew                                             -- host_wg_new.fire
  | alloc (cu : Fin 2) (slot : Fin 8) (rec : CtasWgRec) -- 分配完成（3-to-1 握手）
  | wfNew (cu : Fin 2) (slot : Fin 8)                   -- cu_wf_new(cu).fire
  | wfDone (cu : Fin 2) (slot : Fin 8)                  -- cu_wf_done(cu).fire（tag 解析出 slot）
  | dealloc (cu : Fin 2) (slot : Fin 8) (wgId : BitVec 32) -- rt_dealloc + host_wg_done

/-- 抽象转移 -/
def ctasStep (s : CtasState) : CtasEvent → CtasState
  | .hostNew => { s with pending := s.pending + 1 }
  | .alloc cu slot rec =>
      { s with pending := s.pending - 1, live := ctasWrite s.live cu slot (some rec) }
  | .wfNew cu slot =>
      let m := (s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }
      { s with live := ctasWrite s.live cu slot m }
  | .wfDone cu slot =>
      let m := (s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }
      { s with live := ctasWrite s.live cu slot m }
  | .dealloc cu slot _ => { s with live := ctasWrite s.live cu slot none }

/-- wfNew 契约谓词（H-CUIF-SPLIT）：splitter 恰好派 numWf 个 WF -/
def ctasWfNewOk (o : Option CtasWgRec) : Prop :=
  match o with | some r => r.wfSent < r.numWf | none => False

/-- wfDone 契约谓词（H-CUIF-DONE）：只有已派发的 WF 会完成 -/
def ctasWfDoneOk (o : Option CtasWgRec) : Prop :=
  match o with | some r => r.wfDone < r.wfSent | none => False

/-- dealloc 契约谓词（H-CUIF-DEALLOC）：全部 WF 完成才回收，上报 wgId 一致 -/
def ctasDeallocOk (o : Option CtasWgRec) (wgId : BitVec 32) : Prop :=
  match o with | some r => r.wfDone = r.numWf ∧ r.wgId = wgId | none => False

instance (o : Option CtasWgRec) : Decidable (ctasWfNewOk o) :=
  match o with
  | some r => inferInstanceAs (Decidable (r.wfSent < r.numWf))
  | none => isFalse (fun h => h)

instance (o : Option CtasWgRec) : Decidable (ctasWfDoneOk o) :=
  match o with
  | some r => inferInstanceAs (Decidable (r.wfDone < r.wfSent))
  | none => isFalse (fun h => h)

instance (o : Option CtasWgRec) (wgId : BitVec 32) : Decidable (ctasDeallocOk o wgId) :=
  match o with
  | some r => inferInstanceAs (Decidable (r.wfDone = r.numWf ∧ r.wgId = wgId))
  | none => isFalse (fun h => h)

/-- 事件可发生条件 = 四个黑盒子模块的接口契约（集中清单见第 3 节头注） -/
@[reducible] def CtasEventOk (s : CtasState) : CtasEvent → Prop
  | .hostNew => s.pending < ctasWGBUF_ENTRIES                       -- H-WGB
  | .alloc cu slot rec =>
      s.pending > 0 ∧                                               -- H-ALLOC-PENDING
      s.live cu slot = none ∧                                       -- H-ALLOC-SLOT
      rec.wfSent = 0 ∧ rec.wfDone = 0 ∧
      1 ≤ rec.numWf ∧ rec.numWf ≤ ctasNUM_WF_MAX ∧                  -- H-WF
      rec.sgprBase + rec.sgprSize ≤ ctasNUM_SGPR_MAX ∧              -- H-RT-BOUNDS
      rec.vgprBase + rec.vgprSize ≤ ctasNUM_VGPR_MAX ∧
      rec.ldsBase + rec.ldsSize ≤ ctasNUM_LDS_MAX ∧
      (∀ s2, ctasPairOk (some rec) (s.live cu s2)) ∧                -- H-RT-DISJOINT
      ctasUsed s cu CtasWgRec.sgprSize + rec.sgprSize ≤ ctasNUM_SGPR_MAX ∧  -- H-ALLOC-FIT
      ctasUsed s cu CtasWgRec.vgprSize + rec.vgprSize ≤ ctasNUM_VGPR_MAX ∧
      ctasUsed s cu CtasWgRec.ldsSize + rec.ldsSize ≤ ctasNUM_LDS_MAX
  | .wfNew cu slot => ctasWfNewOk (s.live cu slot)                 -- H-CUIF-SPLIT
  | .wfDone cu slot => ctasWfDoneOk (s.live cu slot)               -- H-CUIF-DONE（依赖 CTA2warp，Q3）
  | .dealloc cu slot wgId => ctasDeallocOk (s.live cu slot) wgId   -- H-CUIF-DEALLOC

/- ========================================================================= -/
/- 4. 引理：写槽与求和                                                         -/
/- ========================================================================= -/

theorem ctasWrite_self (lv : Fin 2 → Fin 8 → Option CtasWgRec) (cu : Fin 2)
    (slot : Fin 8) (v : Option CtasWgRec) :
    ctasWrite lv cu slot v cu slot = v := by
  simp [ctasWrite]

theorem ctasWrite_other (lv : Fin 2 → Fin 8 → Option CtasWgRec) {cu cu' : Fin 2}
    {slot slot' : Fin 8} (h : ¬ (cu' = cu ∧ slot' = slot)) (v : Option CtasWgRec) :
    ctasWrite lv cu slot v cu' slot' = lv cu' slot' := by
  simp [ctasWrite, h]

theorem ctasWrite_ne (lv : Fin 2 → Fin 8 → Option CtasWgRec) {cu cu' : Fin 2}
    (hc : cu' ≠ cu) (slot : Fin 8) (v : Option CtasWgRec) (j : Fin 8) :
    ctasWrite lv cu slot v cu' j = lv cu' j := by
  simp [ctasWrite, hc]

/-- 8 槽求和的写入引理 -/
theorem ctasSum8_write (f : Fin 8 → Nat) (k : Fin 8) (v : Nat) :
    ctasSum8 (fun j => if j = k then v else f j) = ctasSum8 f - f k + v := by
  obtain ⟨kv, hkv⟩ := k
  have h8 : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 ∨ kv = 4 ∨ kv = 5 ∨ kv = 6 ∨ kv = 7 := by omega
  obtain h|h|h|h|h|h|h|h := h8 <;> subst h <;> simp [ctasSum8] <;> omega

/-- 写槽后某 CU 的资源占用变化：−旧槽占用 +新值占用 -/
theorem ctasUsed_write_eq (lv : Fin 2 → Fin 8 → Option CtasWgRec) (cu : Fin 2) (slot : Fin 8)
    (v : Option CtasWgRec) (proj : CtasWgRec → Nat) :
    ctasSum8 (fun j => ctasSlotRes (ctasWrite lv cu slot v cu j) proj) =
      ctasSum8 (fun j => ctasSlotRes (lv cu j) proj) - ctasSlotRes (lv cu slot) proj +
        ctasSlotRes v proj := by
  have hfun : (fun j => ctasSlotRes (ctasWrite lv cu slot v cu j) proj) =
      (fun j => if j = slot then ctasSlotRes v proj else ctasSlotRes (lv cu j) proj) := by
    funext j
    by_cases hj : j = slot
    · rw [if_pos hj]; simp [ctasWrite, hj]
    · rw [if_neg hj]; simp [ctasWrite, hj]
  rw [hfun]
  exact ctasSum8_write _ _ _

/-- 单槽占用 ≤ 总和（截断减法消去的前提） -/
theorem ctasSlotRes_le_sum (lv : Fin 2 → Fin 8 → Option CtasWgRec) (cu : Fin 2)
    (slot : Fin 8) (proj : CtasWgRec → Nat) :
    ctasSlotRes (lv cu slot) proj ≤ ctasSum8 (fun j => ctasSlotRes (lv cu j) proj) := by
  have hx : slot = ⟨0, by decide⟩ ∨ slot = ⟨1, by decide⟩ ∨ slot = ⟨2, by decide⟩ ∨
      slot = ⟨3, by decide⟩ ∨ slot = ⟨4, by decide⟩ ∨ slot = ⟨5, by decide⟩ ∨
      slot = ⟨6, by decide⟩ ∨ slot = ⟨7, by decide⟩ := by
    obtain ⟨xv, xh⟩ := slot
    have h8 : xv = 0 ∨ xv = 1 ∨ xv = 2 ∨ xv = 3 ∨ xv = 4 ∨ xv = 5 ∨ xv = 6 ∨ xv = 7 := by omega
    obtain h|h|h|h|h|h|h|h := h8 <;> subst h <;>
      first
        | exact Or.inl (Fin.ext rfl)
        | exact Or.inr (Or.inl (Fin.ext rfl))
        | exact Or.inr (Or.inr (Or.inl (Fin.ext rfl)))
        | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl)))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl)))))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext rfl)))))))
  obtain h|h|h|h|h|h|h|h := hx <;> rw [h] <;> simp [ctasSum8] <;> omega

/-- 写别的 CU 不影响本 CU 的占用 -/
theorem ctasUsed_other (lv : Fin 2 → Fin 8 → Option CtasWgRec) {cu cu' : Fin 2}
    (hc : cu' ≠ cu) (slot : Fin 8) (v : Option CtasWgRec) (proj : CtasWgRec → Nat) :
    ctasSum8 (fun j => ctasSlotRes (ctasWrite lv cu slot v cu' j) proj) =
      ctasSum8 (fun j => ctasSlotRes (lv cu' j) proj) := by
  congr 1
  funext j
  rw [ctasWrite_ne lv hc slot v j]

/-- alloc（目标槽原为空）后的占用 = 原占用 + 新 WG 尺寸 -/
theorem ctasUsed_alloc (s : CtasState) (cu : Fin 2) (slot : Fin 8) (rec : CtasWgRec)
    (hslot : s.live cu slot = none) (proj : CtasWgRec → Nat) :
    ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu j) proj) =
      ctasSum8 (fun j => ctasSlotRes (s.live cu j) proj) + proj rec := by
  rw [ctasUsed_write_eq]
  have h0 : ctasSlotRes (s.live cu slot) proj = 0 := by rw [hslot]; rfl
  have h1 : ctasSlotRes (some rec) proj = proj rec := rfl
  rw [h0, h1]
  omega

/-- dealloc 后的占用 = 原占用 − 被回收 WG 的占用 -/
theorem ctasUsed_remove (s : CtasState) (cu : Fin 2) (slot : Fin 8) (proj : CtasWgRec → Nat) :
    ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu j) proj) =
      ctasSum8 (fun j => ctasSlotRes (s.live cu j) proj) - ctasSlotRes (s.live cu slot) proj := by
  rw [ctasUsed_write_eq]
  have h0 : ctasSlotRes (none : Option CtasWgRec) proj = 0 := rfl
  rw [h0]
  omega

theorem ctasDisjoint_symm {r1 r2 : CtasWgRec} (h : ctasDisjoint r1 r2) : ctasDisjoint r2 r1 := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem ctasPairOk_symm {o1 o2 : Option CtasWgRec} (h : ctasPairOk o1 o2) : ctasPairOk o2 o1 := by
  cases o1 with
  | none => cases o2 with
    | none => exact h
    | some r2 => exact h
  | some r1 => cases o2 with
    | none => exact h
    | some r2 => exact ctasDisjoint_symm h

theorem ctasPairOk_none_left (o : Option CtasWgRec) : ctasPairOk none o = True := by
  cases o <;> rfl

theorem ctasPairOk_none_right (o : Option CtasWgRec) : ctasPairOk o none = True := by
  cases o <;> rfl

/- ========================================================================= -/
/- 5. 主定理：契约内任意事件保持顶层不变式                                      -/
/- ========================================================================= -/

/-- CTAS1 不变式保持：只要四个子模块满足接口契约（CtasEventOk），
    组合系统的"资源不超分 ∧ 记录合法 ∧ 槽位相容 ∧ 缓冲有界"在任意事件后保持。 -/
theorem ctas_step_inv (s : CtasState) (e : CtasEvent)
    (hinv : CtasInv s) (hok : CtasEventOk s e) : CtasInv (ctasStep s e) := by
  obtain ⟨hused, hrec, hpair, hpend⟩ := hinv
  cases e with
  | hostNew =>
    have hok' : s.pending < 8 := hok
    exact ⟨hused, hrec, hpair, by show s.pending + 1 ≤ 8; omega⟩
  | alloc cu slot rec =>
    unfold CtasEventOk at hok
    obtain ⟨hp0, hslot, hws0, hwd0, hwf1, hwf2, hsb, hvb, hlb, hdisj, hsf, hvf, hlf⟩ := hok
    have hstep : ctasStep s (.alloc cu slot rec) =
        { s with pending := s.pending - 1, live := ctasWrite s.live cu slot (some rec) } := rfl
    rw [hstep]
    have hproj : ({ s with pending := s.pending - 1, live := ctasWrite s.live cu slot (some rec) } : CtasState).live = ctasWrite s.live cu slot (some rec) := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- 资源不超分：H-ALLOC-FIT
      intro cu'
      by_cases hc : cu' = cu
      · rw [hc]
        refine ⟨?_, ?_, ?_⟩
        · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu j)
              CtasWgRec.sgprSize) ≤ 2048
          rw [ctasUsed_alloc s cu slot rec hslot CtasWgRec.sgprSize]
          have hsf' : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.sgprSize) +
              rec.sgprSize ≤ 2048 := hsf
          omega
        · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu j)
              CtasWgRec.vgprSize) ≤ 1024
          rw [ctasUsed_alloc s cu slot rec hslot CtasWgRec.vgprSize]
          have hvf' : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.vgprSize) +
              rec.vgprSize ≤ 1024 := hvf
          omega
        · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu j)
              CtasWgRec.ldsSize) ≤ 131072
          rw [ctasUsed_alloc s cu slot rec hslot CtasWgRec.ldsSize]
          have hlf' : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.ldsSize) +
              rec.ldsSize ≤ 131072 := hlf
          omega
      · refine ⟨?_, ?_, ?_⟩
        · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu' j)
              CtasWgRec.sgprSize) ≤ 2048
          rw [ctasUsed_other s.live hc slot (some rec) CtasWgRec.sgprSize]
          exact (hused cu').1
        · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu' j)
              CtasWgRec.vgprSize) ≤ 1024
          rw [ctasUsed_other s.live hc slot (some rec) CtasWgRec.vgprSize]
          exact (hused cu').2.1
        · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot (some rec) cu' j)
              CtasWgRec.ldsSize) ≤ 131072
          rw [ctasUsed_other s.live hc slot (some rec) CtasWgRec.ldsSize]
          exact (hused cu').2.2
    · -- 记录合法：新槽由契约保证，其余槽不变
      intro cu' slot'
      rw [hproj]
      by_cases hcs : cu' = cu ∧ slot' = slot
      · obtain ⟨rfl, rfl⟩ := hcs
        rw [ctasWrite_self]
        refine ⟨hwf1, hwf2, by omega, by omega, hsb, hvb, hlb⟩
      · rw [ctasWrite_other _ hcs]
        exact hrec cu' slot'
    · -- 槽位相容：新对由 H-RT-DISJOINT，旧对由原不变式
      intro cu' s1 s2 hne
      rw [hproj]
      by_cases hc : cu' = cu
      · rw [hc]
        by_cases h1 : s1 = slot
        · rw [h1]
          by_cases h2 : s2 = slot
          · exact absurd (h1.trans h2.symm) hne
          · rw [ctasWrite_self, ctasWrite_other _ (fun h => h2 h.2)]
            exact hdisj s2
        · by_cases h2 : s2 = slot
          · rw [h2]
            rw [ctasWrite_self, ctasWrite_other _ (fun h => h1 h.2)]
            exact ctasPairOk_symm (hdisj s1)
          · rw [ctasWrite_other _ (fun h => h1 h.2), ctasWrite_other _ (fun h => h2 h.2)]
            exact hpair cu s1 s2 hne
      · rw [ctasWrite_ne _ hc, ctasWrite_ne _ hc]
        exact hpair cu' s1 s2 hne
    · -- pending 计数
      show s.pending - 1 ≤ 8
      have hpend' : s.pending ≤ 8 := hpend
      omega
  | wfNew cu slot =>
    cases hl : s.live cu slot with
    | none => simp [CtasEventOk, ctasWfNewOk, hl] at hok
    | some r =>
      have hok' : r.wfSent < r.numWf := by simp [CtasEventOk, ctasWfNewOk, hl] at hok; exact hok
      have hr0 := hrec cu slot
      rw [hl] at hr0
      obtain ⟨hwf1, hwf2, hwd, hws, hsb, hvb, hlb⟩ := hr0
      have hstep : ctasStep s (.wfNew cu slot) =
          { s with live := ctasWrite s.live cu slot ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) } := rfl
      rw [hstep]
      have hproj : ({ s with live := ctasWrite s.live cu slot ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) } : CtasState).live = ctasWrite s.live cu slot ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) := rfl
      have hmap : ∀ proj : CtasWgRec → Nat,
          (∀ w, proj { w with wfSent := w.wfSent + 1 } = proj w) →
          ctasSlotRes ((s.live cu slot).map (fun w => { w with wfSent := w.wfSent + 1 })) proj =
            ctasSlotRes (s.live cu slot) proj := by
        intro proj hp; rw [hl]; exact hp r
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- 计数更新不动资源尺寸 ⇒ 占用不变
        intro cu'
        by_cases hc : cu' = cu
        · rw [hc]
          refine ⟨?_, ?_, ?_⟩
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) cu j)
                CtasWgRec.sgprSize) ≤ 2048
            rw [ctasUsed_write_eq, hmap CtasWgRec.sgprSize (fun _ => rfl)]
            have hle := ctasSlotRes_le_sum s.live cu slot CtasWgRec.sgprSize
            have hu1 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.sgprSize) ≤ 2048 :=
              (hused cu).1
            omega
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) cu j)
                CtasWgRec.vgprSize) ≤ 1024
            rw [ctasUsed_write_eq, hmap CtasWgRec.vgprSize (fun _ => rfl)]
            have hle := ctasSlotRes_le_sum s.live cu slot CtasWgRec.vgprSize
            have hu2 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.vgprSize) ≤ 1024 :=
              (hused cu).2.1
            omega
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) cu j)
                CtasWgRec.ldsSize) ≤ 131072
            rw [ctasUsed_write_eq, hmap CtasWgRec.ldsSize (fun _ => rfl)]
            have hle := ctasSlotRes_le_sum s.live cu slot CtasWgRec.ldsSize
            have hu3 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.ldsSize) ≤ 131072 :=
              (hused cu).2.2
            omega
        · refine ⟨?_, ?_, ?_⟩
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) cu' j)
                CtasWgRec.sgprSize) ≤ 2048
            rw [ctasUsed_other s.live hc slot _ CtasWgRec.sgprSize]
            exact (hused cu').1
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) cu' j)
                CtasWgRec.vgprSize) ≤ 1024
            rw [ctasUsed_other s.live hc slot _ CtasWgRec.vgprSize]
            exact (hused cu').2.1
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfSent := w.wfSent + 1 }) cu' j)
                CtasWgRec.ldsSize) ≤ 131072
            rw [ctasUsed_other s.live hc slot _ CtasWgRec.ldsSize]
            exact (hused cu').2.2
      · -- 记录合法：wfSent+1 ≤ numWf 由 H-CUIF-SPLIT
        intro cu' slot'
        rw [hproj]
        by_cases hcs : cu' = cu ∧ slot' = slot
        · obtain ⟨rfl, rfl⟩ := hcs
          rw [ctasWrite_self, hl]
          refine ⟨hwf1, hwf2, by show r.wfDone ≤ r.wfSent + 1; omega,
            by show r.wfSent + 1 ≤ r.numWf; omega, hsb, hvb, hlb⟩
        · rw [ctasWrite_other _ hcs]
          exact hrec cu' slot'
      · -- 槽位相容：尺寸不变 ⇒ 不交性保持
        intro cu' s1 s2 hne
        rw [hproj]
        by_cases hc : cu' = cu
        · rw [hc]
          by_cases h1 : s1 = slot
          · rw [h1]
            by_cases h2 : s2 = slot
            · exact absurd (h1.trans h2.symm) hne
            · rw [ctasWrite_self, ctasWrite_other _ (fun h => h2 h.2), hl]
              cases hs2 : s.live cu s2 with
              | none => exact trivial
              | some r2 =>
                have hp := hpair cu slot s2 (fun h => hne (h1.trans h))
                rw [hl, hs2] at hp
                show ctasDisjoint r r2
                exact hp
          · by_cases h2 : s2 = slot
            · rw [h2]
              rw [ctasWrite_self, ctasWrite_other _ (fun h => h1 h.2), hl]
              cases hs1 : s.live cu s1 with
              | none => exact trivial
              | some r1 =>
                have hp := hpair cu s1 slot (fun h => hne (h.trans h2.symm))
                rw [hs1, hl] at hp
                show ctasDisjoint r1 r
                exact hp
            · rw [ctasWrite_other _ (fun h => h1 h.2), ctasWrite_other _ (fun h => h2 h.2)]
              exact hpair cu s1 s2 hne
        · rw [ctasWrite_ne _ hc, ctasWrite_ne _ hc]
          exact hpair cu' s1 s2 hne
      · exact hpend
  | wfDone cu slot =>
    cases hl : s.live cu slot with
    | none => simp [CtasEventOk, ctasWfDoneOk, hl] at hok
    | some r =>
      have hok' : r.wfDone < r.wfSent := by simp [CtasEventOk, ctasWfDoneOk, hl] at hok; exact hok
      have hr0 := hrec cu slot
      rw [hl] at hr0
      obtain ⟨hwf1, hwf2, hwd, hws, hsb, hvb, hlb⟩ := hr0
      have hstep : ctasStep s (.wfDone cu slot) =
          { s with live := ctasWrite s.live cu slot ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) } := rfl
      rw [hstep]
      have hproj : ({ s with live := ctasWrite s.live cu slot ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) } : CtasState).live = ctasWrite s.live cu slot ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) := rfl
      have hmap : ∀ proj : CtasWgRec → Nat,
          (∀ w, proj { w with wfDone := w.wfDone + 1 } = proj w) →
          ctasSlotRes ((s.live cu slot).map (fun w => { w with wfDone := w.wfDone + 1 })) proj =
            ctasSlotRes (s.live cu slot) proj := by
        intro proj hp; rw [hl]; exact hp r
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cu'
        by_cases hc : cu' = cu
        · rw [hc]
          refine ⟨?_, ?_, ?_⟩
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) cu j)
                CtasWgRec.sgprSize) ≤ 2048
            rw [ctasUsed_write_eq, hmap CtasWgRec.sgprSize (fun _ => rfl)]
            have hle := ctasSlotRes_le_sum s.live cu slot CtasWgRec.sgprSize
            have hu1 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.sgprSize) ≤ 2048 :=
              (hused cu).1
            omega
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) cu j)
                CtasWgRec.vgprSize) ≤ 1024
            rw [ctasUsed_write_eq, hmap CtasWgRec.vgprSize (fun _ => rfl)]
            have hle := ctasSlotRes_le_sum s.live cu slot CtasWgRec.vgprSize
            have hu2 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.vgprSize) ≤ 1024 :=
              (hused cu).2.1
            omega
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) cu j)
                CtasWgRec.ldsSize) ≤ 131072
            rw [ctasUsed_write_eq, hmap CtasWgRec.ldsSize (fun _ => rfl)]
            have hle := ctasSlotRes_le_sum s.live cu slot CtasWgRec.ldsSize
            have hu3 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.ldsSize) ≤ 131072 :=
              (hused cu).2.2
            omega
        · refine ⟨?_, ?_, ?_⟩
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) cu' j)
                CtasWgRec.sgprSize) ≤ 2048
            rw [ctasUsed_other s.live hc slot _ CtasWgRec.sgprSize]
            exact (hused cu').1
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) cu' j)
                CtasWgRec.vgprSize) ≤ 1024
            rw [ctasUsed_other s.live hc slot _ CtasWgRec.vgprSize]
            exact (hused cu').2.1
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot
                ((s.live cu slot).map fun w => { w with wfDone := w.wfDone + 1 }) cu' j)
                CtasWgRec.ldsSize) ≤ 131072
            rw [ctasUsed_other s.live hc slot _ CtasWgRec.ldsSize]
            exact (hused cu').2.2
      · intro cu' slot'
        rw [hproj]
        by_cases hcs : cu' = cu ∧ slot' = slot
        · obtain ⟨rfl, rfl⟩ := hcs
          rw [ctasWrite_self, hl]
          refine ⟨hwf1, hwf2, by show r.wfDone + 1 ≤ r.wfSent; omega,
            by show r.wfSent ≤ r.numWf; omega, hsb, hvb, hlb⟩
        · rw [ctasWrite_other _ hcs]
          exact hrec cu' slot'
      · intro cu' s1 s2 hne
        rw [hproj]
        by_cases hc : cu' = cu
        · rw [hc]
          by_cases h1 : s1 = slot
          · rw [h1]
            by_cases h2 : s2 = slot
            · exact absurd (h1.trans h2.symm) hne
            · rw [ctasWrite_self, ctasWrite_other _ (fun h => h2 h.2), hl]
              cases hs2 : s.live cu s2 with
              | none => exact trivial
              | some r2 =>
                have hp := hpair cu slot s2 (fun h => hne (h1.trans h))
                rw [hl, hs2] at hp
                show ctasDisjoint r r2
                exact hp
          · by_cases h2 : s2 = slot
            · rw [h2]
              rw [ctasWrite_self, ctasWrite_other _ (fun h => h1 h.2), hl]
              cases hs1 : s.live cu s1 with
              | none => exact trivial
              | some r1 =>
                have hp := hpair cu s1 slot (fun h => hne (h.trans h2.symm))
                rw [hs1, hl] at hp
                show ctasDisjoint r1 r
                exact hp
            · rw [ctasWrite_other _ (fun h => h1 h.2), ctasWrite_other _ (fun h => h2 h.2)]
              exact hpair cu s1 s2 hne
        · rw [ctasWrite_ne _ hc, ctasWrite_ne _ hc]
          exact hpair cu' s1 s2 hne
      · exact hpend
  | dealloc cu slot wgId =>
    cases hl : s.live cu slot with
    | none => simp [CtasEventOk, ctasDeallocOk, hl] at hok
    | some r =>
      have hstep : ctasStep s (.dealloc cu slot wgId) =
          { s with live := ctasWrite s.live cu slot none } := rfl
      rw [hstep]
      have hproj : ({ s with live := ctasWrite s.live cu slot none } : CtasState).live = ctasWrite s.live cu slot none := rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- 回收后占用只减不增
        intro cu'
        by_cases hc : cu' = cu
        · rw [hc]
          refine ⟨?_, ?_, ?_⟩
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu j)
                CtasWgRec.sgprSize) ≤ 2048
            rw [ctasUsed_remove]
            have hu1 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.sgprSize) ≤ 2048 :=
              (hused cu).1
            omega
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu j)
                CtasWgRec.vgprSize) ≤ 1024
            rw [ctasUsed_remove]
            have hu2 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.vgprSize) ≤ 1024 :=
              (hused cu).2.1
            omega
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu j)
                CtasWgRec.ldsSize) ≤ 131072
            rw [ctasUsed_remove]
            have hu3 : ctasSum8 (fun j => ctasSlotRes (s.live cu j) CtasWgRec.ldsSize) ≤ 131072 :=
              (hused cu).2.2
            omega
        · refine ⟨?_, ?_, ?_⟩
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu' j)
                CtasWgRec.sgprSize) ≤ 2048
            rw [ctasUsed_other s.live hc slot none CtasWgRec.sgprSize]
            exact (hused cu').1
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu' j)
                CtasWgRec.vgprSize) ≤ 1024
            rw [ctasUsed_other s.live hc slot none CtasWgRec.vgprSize]
            exact (hused cu').2.1
          · show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu' j)
                CtasWgRec.ldsSize) ≤ 131072
            rw [ctasUsed_other s.live hc slot none CtasWgRec.ldsSize]
            exact (hused cu').2.2
      · intro cu' slot'
        rw [hproj]
        by_cases hcs : cu' = cu ∧ slot' = slot
        · obtain ⟨rfl, rfl⟩ := hcs
          rw [ctasWrite_self]
          exact trivial
        · rw [ctasWrite_other _ hcs]
          exact hrec cu' slot'
      · intro cu' s1 s2 hne
        rw [hproj]
        by_cases hc : cu' = cu
        · rw [hc]
          by_cases h1 : s1 = slot
          · rw [h1]
            rw [ctasWrite_self, ctasPairOk_none_left]
            trivial
          · by_cases h2 : s2 = slot
            · rw [h2]
              rw [ctasWrite_self, ctasPairOk_none_right]
              trivial
            · rw [ctasWrite_other _ (fun h => h1 h.2), ctasWrite_other _ (fun h => h2 h.2)]
              exact hpair cu s1 s2 hne
        · rw [ctasWrite_ne _ hc, ctasWrite_ne _ hc]
          exact hpair cu' s1 s2 hne
      · exact hpend

/- ========================================================================= -/
/- 6. 规格投影定理                                                             -/
/- ========================================================================= -/

/-- CTAS2 规格 S1（资源不超分）：不变式 ⇒ 任意 CU 的 Σ已分配 ≤ NUM_*_MAX -/
theorem ctas_no_oversubscribe (s : CtasState) (h : CtasInv s) (cu : Fin 2) :
    ctasUsed s cu CtasWgRec.sgprSize ≤ ctasNUM_SGPR_MAX ∧
    ctasUsed s cu CtasWgRec.vgprSize ≤ ctasNUM_VGPR_MAX ∧
    ctasUsed s cu CtasWgRec.ldsSize ≤ ctasNUM_LDS_MAX := h.1 cu

/-- CTAS3 规格 S2（槽位不冲突）：live 表以 Option 表达每 (cu,slot) 至多一个 WG；
    新分配只在空槽发生（H-ALLOC-SLOT，allocator.scala:270 的 PriorityEncoder(~wgslot)） -/
theorem ctas_alloc_needs_free_slot (s : CtasState) (cu : Fin 2) (slot : Fin 8) (rec : CtasWgRec)
    (hok : CtasEventOk s (.alloc cu slot rec)) : s.live cu slot = none := by
  unfold CtasEventOk at hok
  exact hok.2.1

/-- CTAS4 规格 S3（回收无幽灵、无提前）：dealloc 只对在驻且 wf 全部完成的 WG 发生，
    且上报 host 的 wgId 与在驻记录一致（H-CUIF-DEALLOC，cu_interface.scala:179,222） -/
theorem ctas_dealloc_only_when_complete (s : CtasState) (cu : Fin 2) (slot : Fin 8)
    (wgId : BitVec 32) (hok : CtasEventOk s (.dealloc cu slot wgId)) :
    ∃ r, s.live cu slot = some r ∧ r.wfDone = r.numWf ∧ r.wgId = wgId := by
  cases hl : s.live cu slot with
  | none => simp [CtasEventOk, ctasDeallocOk, hl] at hok
  | some r =>
    have hok' : r.wfDone = r.numWf ∧ r.wgId = wgId := by simp [CtasEventOk, ctasDeallocOk, hl] at hok; exact hok
    exact ⟨r, rfl, hok'.1, hok'.2⟩

/-- CTAS5 规格 S4（回收即释放）：dealloc 后槽位腾空，占用精确扣减被回收 WG 的尺寸 -/
theorem ctas_dealloc_frees (s : CtasState) (cu : Fin 2) (slot : Fin 8) (wgId : BitVec 32) :
    (ctasStep s (.dealloc cu slot wgId)).live cu slot = none ∧
    ∀ proj : CtasWgRec → Nat,
      ctasUsed (ctasStep s (.dealloc cu slot wgId)) cu proj =
        ctasUsed s cu proj - ctasSlotRes (s.live cu slot) proj := by
  constructor
  · show ctasWrite s.live cu slot none cu slot = none
    exact ctasWrite_self _ _ _ _
  · intro proj
    show ctasSum8 (fun j => ctasSlotRes (ctasWrite s.live cu slot none cu j) proj) =
      ctasSum8 (fun j => ctasSlotRes (s.live cu j) proj) - ctasSlotRes (s.live cu slot) proj
    exact ctasUsed_remove s cu slot proj

/-- CTAS6 wf 计数有界：在驻 WG 的完成数 ≤ 派发数 ≤ 总数（不超收、不超发） -/
theorem ctas_wfCount_bounded (s : CtasState) (h : CtasInv s) (cu : Fin 2) (slot : Fin 8)
    (r : CtasWgRec) (hl : s.live cu slot = some r) :
    r.wfDone ≤ r.wfSent ∧ r.wfSent ≤ r.numWf := by
  have hr := h.2.1 cu slot
  rw [hl] at hr
  exact ⟨hr.2.2.1, hr.2.2.2.1⟩

/- ========================================================================= -/
/- 7. 判定实例（无 mathlib，自造 Fin 2/Fin 8 的 ∀ 判定与 Option 谓词判定）      -/
/- ========================================================================= -/

instance ctasRecOkDecidable (o : Option CtasWgRec) : Decidable (ctasRecOk o) :=
  match o with
  | none => isTrue trivial
  | some r => inferInstanceAs (Decidable (1 ≤ r.numWf ∧ r.numWf ≤ ctasNUM_WF_MAX ∧
      r.wfDone ≤ r.wfSent ∧ r.wfSent ≤ r.numWf ∧
      r.sgprBase + r.sgprSize ≤ ctasNUM_SGPR_MAX ∧ r.vgprBase + r.vgprSize ≤ ctasNUM_VGPR_MAX ∧
      r.ldsBase + r.ldsSize ≤ ctasNUM_LDS_MAX))

instance ctasDisjointDecidable (r1 r2 : CtasWgRec) : Decidable (ctasDisjoint r1 r2) :=
  inferInstanceAs (Decidable
    ((r1.sgprBase + r1.sgprSize ≤ r2.sgprBase ∨ r2.sgprBase + r2.sgprSize ≤ r1.sgprBase) ∧
     (r1.vgprBase + r1.vgprSize ≤ r2.vgprBase ∨ r2.vgprBase + r2.vgprSize ≤ r1.vgprBase) ∧
     (r1.ldsBase + r1.ldsSize ≤ r2.ldsBase ∨ r2.ldsBase + r2.ldsSize ≤ r1.ldsBase)))

instance ctasPairOkDecidable (o1 o2 : Option CtasWgRec) : Decidable (ctasPairOk o1 o2) :=
  match o1, o2 with
  | some r1, some r2 => ctasDisjointDecidable r1 r2
  | none, _ => isTrue trivial
  | some _, none => isTrue trivial

instance ctasDecForallFin2 {p : Fin 2 → Prop} [DecidablePred p] : Decidable (∀ x : Fin 2, p x) :=
  if h : p ⟨0, by decide⟩ ∧ p ⟨1, by decide⟩ then
    isTrue (fun x => by
      have hx : x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ := by
        obtain ⟨xv, xh⟩ := x
        have h2 : xv = 0 ∨ xv = 1 := by omega
        obtain h0|h0 := h2
        · subst h0; exact Or.inl (Fin.ext rfl)
        · subst h0; exact Or.inr (Fin.ext rfl)
      obtain h0|h0 := hx
      · rw [h0]; exact h.1
      · rw [h0]; exact h.2)
  else isFalse (fun hall => h ⟨hall _, hall _⟩)

instance ctasDecForallFin8 {p : Fin 8 → Prop} [DecidablePred p] : Decidable (∀ x : Fin 8, p x) :=
  if h : p ⟨0, by decide⟩ ∧ p ⟨1, by decide⟩ ∧ p ⟨2, by decide⟩ ∧ p ⟨3, by decide⟩ ∧
      p ⟨4, by decide⟩ ∧ p ⟨5, by decide⟩ ∧ p ⟨6, by decide⟩ ∧ p ⟨7, by decide⟩ then
    isTrue (fun x => by
      have hx : x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ ∨ x = ⟨2, by decide⟩ ∨
          x = ⟨3, by decide⟩ ∨ x = ⟨4, by decide⟩ ∨ x = ⟨5, by decide⟩ ∨
          x = ⟨6, by decide⟩ ∨ x = ⟨7, by decide⟩ := by
        obtain ⟨xv, xh⟩ := x
        have h8 : xv = 0 ∨ xv = 1 ∨ xv = 2 ∨ xv = 3 ∨ xv = 4 ∨ xv = 5 ∨ xv = 6 ∨ xv = 7 := by omega
        obtain h0|h0|h0|h0|h0|h0|h0|h0 := h8 <;> subst h0 <;>
          first
            | exact Or.inl (Fin.ext rfl)
            | exact Or.inr (Or.inl (Fin.ext rfl))
            | exact Or.inr (Or.inr (Or.inl (Fin.ext rfl)))
            | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl)))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl)))))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext rfl)))))))
      obtain h0|h0|h0|h0|h0|h0|h0|h0 := hx <;> rw [h0] <;>
        first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1 |
          exact h.2.2.2.2.1 | exact h.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.2)
  else isFalse (fun hall => h ⟨hall _, hall _, hall _, hall _, hall _, hall _, hall _, hall _⟩)

/- ========================================================================= -/
/- 8. 数值回归测试                                                             -/
/- ========================================================================= -/

section CtasRegressionTests

def ctasCU0 : Fin 2 := ⟨0, by decide⟩
def ctasCU1 : Fin 2 := ⟨1, by decide⟩
def ctasSlot0 : Fin 8 := ⟨0, by decide⟩
def ctasSlot1 : Fin 8 := ⟨1, by decide⟩

/-- 测试 WG A：wgId=7、2 个 WF、sgpr [0,100)、vgpr [0,64)、lds [0,256) -/
def ctasRecA : CtasWgRec := ⟨7#32, 2, 0, 100, 0, 64, 0, 256, 0, 0⟩

-- T1 完整生命周期：hostNew → alloc → wfNew×2 → wfDone×2 → dealloc
def ctasL1 : CtasState := ctasStep ctasInit .hostNew
def ctasL2 : CtasState := ctasStep ctasL1 (.alloc ctasCU0 ctasSlot0 ctasRecA)
def ctasL3 : CtasState := ctasStep ctasL2 (.wfNew ctasCU0 ctasSlot0)
def ctasL4 : CtasState := ctasStep ctasL3 (.wfNew ctasCU0 ctasSlot0)
def ctasL5 : CtasState := ctasStep ctasL4 (.wfDone ctasCU0 ctasSlot0)
def ctasL6 : CtasState := ctasStep ctasL5 (.wfDone ctasCU0 ctasSlot0)
def ctasL7 : CtasState := ctasStep ctasL6 (.dealloc ctasCU0 ctasSlot0 7#32)

-- 契约在各步均可满足（可判定）
example : CtasEventOk ctasInit .hostNew := by decide
example : CtasEventOk ctasL1 (.alloc ctasCU0 ctasSlot0 ctasRecA) := by decide
example : CtasEventOk ctasL2 (.wfNew ctasCU0 ctasSlot0) := by decide
example : CtasEventOk ctasL3 (.wfNew ctasCU0 ctasSlot0) := by decide
example : CtasEventOk ctasL4 (.wfDone ctasCU0 ctasSlot0) := by decide
example : CtasEventOk ctasL5 (.wfDone ctasCU0 ctasSlot0) := by decide
example : CtasEventOk ctasL6 (.dealloc ctasCU0 ctasSlot0 7#32) := by decide

-- 不变式沿生命周期保持（直接判定）
example : CtasInv ctasInit := by decide
example : CtasInv ctasL2 := by decide
example : CtasInv ctasL4 := by decide
example : CtasInv ctasL6 := by decide
example : CtasInv ctasL7 := by decide

-- 占用与计数的精确值
example : ctasUsed ctasL2 ctasCU0 CtasWgRec.sgprSize = 100 := by decide
example : ctasUsed ctasL2 ctasCU0 CtasWgRec.vgprSize = 64 := by decide
example : ctasUsed ctasL2 ctasCU0 CtasWgRec.ldsSize = 256 := by decide
example : ctasUsed ctasL2 ctasCU1 CtasWgRec.sgprSize = 0 := by decide
example : (ctasL4.live ctasCU0 ctasSlot0).map CtasWgRec.wfSent = some 2 := by decide
example : (ctasL6.live ctasCU0 ctasSlot0).map CtasWgRec.wfDone = some 2 := by decide
example : ctasL7.live ctasCU0 ctasSlot0 = none := by decide
example : ctasUsed ctasL7 ctasCU0 CtasWgRec.sgprSize = 0 := by decide   -- 回收精确
example : ctasL7.pending = 0 := by decide

-- T2 契约缺位即超分（Q4 的定量演示）：若 allocator 检查失守，
-- 两个各 1500 sgpr 的 WG 相继 alloc 即得 Σ=3000 > 2048，顶层无任何自保
def ctasRecBig : CtasWgRec := ⟨9#32, 1, 0, 1500, 0, 0, 0, 0, 0, 0⟩
def ctasX1 : CtasState := ctasStep (ctasStep ctasInit .hostNew) (.alloc ctasCU0 ctasSlot0 ctasRecBig)
def ctasX2 : CtasState := ctasStep (ctasStep ctasX1 .hostNew) (.alloc ctasCU0 ctasSlot1 ctasRecBig)
example : ctasUsed ctasX2 ctasCU0 CtasWgRec.sgprSize = 3000 := by decide
example : ¬ CtasInv ctasX2 := by decide
-- 契约本身拦下第二次 alloc（H-ALLOC-FIT 生效）
example : ¬ CtasEventOk ctasX1 (.alloc ctasCU0 ctasSlot1 ctasRecBig) := by decide

-- T3 契约缺位即撞槽：对已占槽再 alloc 直接覆盖（H-ALLOC-SLOT 是承重墙）
example : (ctasStep ctasL2 (.alloc ctasCU0 ctasSlot0 ctasRecBig)).live ctasCU0 ctasSlot0 =
    some ctasRecBig := by decide
example : ¬ CtasEventOk ctasL2 (.alloc ctasCU0 ctasSlot0 ctasRecBig) := by decide

-- T4 提前回收被契约拦下（wfDone < numWf 时 dealloc 不允许）
example : ¬ CtasEventOk ctasL5 (.dealloc ctasCU0 ctasSlot0 7#32) := by decide
-- 错误 wgId 的回收上报被契约拦下
example : ¬ CtasEventOk ctasL6 (.dealloc ctasCU0 ctasSlot0 8#32) := by decide

-- T5 双 CU 互不干扰
def ctasM1 : CtasState := ctasStep (ctasStep ctasInit .hostNew) (.alloc ctasCU1 ctasSlot0 ctasRecA)
example : ctasUsed ctasM1 ctasCU1 CtasWgRec.sgprSize = 100 := by decide
example : ctasUsed ctasM1 ctasCU0 CtasWgRec.sgprSize = 0 := by decide
example : CtasInv ctasM1 := by decide

end CtasRegressionTests

/- 公理审计（ctas_tag_roundtrip 带 bv_decide 的 LRAT trust 公理；
   其余定理仅标准公理；测试中的 decide 无额外公理） -/
#print axioms ctas_tag_roundtrip
#print axioms ctas_step_inv
#print axioms ctas_no_oversubscribe
#print axioms ctas_dealloc_only_when_complete
#print axioms ctas_dealloc_frees

end Ventus.CTA
