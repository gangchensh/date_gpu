/- ========================================================================= -/
/-                      CTA/RtCacheConsistency.lean                           -/
/-  rtcache 与 rt 链表的时序一致性（契约缺口 G2 的核销/裁定文件）             -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/allocator.scala          -/
/-      （rtcache_writer :61-100——allocWr 扣减 :86-92、rt_result 写入 :93-96、 -/
/-       :91 扣减断言；allocator 资源检查 :251-262——行检查 :251-253、          -/
/-       PriorityMux 高行优先 :257-259、orR :261-263）                        -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/resource_table.scala     -/
/-      （alloc.ready 含 SCAN/OUTPUT :137-138；抢占跳转 :560-567；            -/
/-       SCAN :449-517；OUTPUT/rtcache_update :522-525）                      -/
/-                                                                           -/
/-  ======================== 结论摘要（G2 裁定） ============================ -/
/-  模型：单资源通道（lds/sgpr/vgpr 各自独立，ResourceTable D1）的事件系统。  -/
/-  状态 = (rt 链表, rtcache 两行)；事件 = SCAN 落地 / alloc(检查+扣减+插表)  -/
/-  / dealloc(摘除)。每拍语义逐行对应上述源码。                               -/
/-                                                                           -/
/-  【正】（定理）                                                            -/
/-  P1 rtcc_sound_step：cache 两行都不超过当前最大空段 ⟹ 本次 alloc 的        -/
/-     H-ALLOC-FIT（rt 中确有能放下的空段）成立。                             -/
/-  P2 rtcc_fit_after_scan：SCAN 刚落地（cache = 准确 top-2）后的第一次       -/
/-     alloc 必安全。                                                         -/
/-  P3 rtccInv_run（经 rtcc_gapSum 望远镜 + 守恒引理）：总量守恒不变式        -/
/-     cache(0)+cache(1) ≤ 空段总长 在所有守约轨迹上成立——cache 对"剩余       -/
/-     总量"永不高估。                                                        -/
/-  【反】（破窗见证，rtcc_w_* 全部 decide 核证）                             -/
/-  N1 "cache 逐行 ≤ 最大空段"不是不变式：SCAN 后连续 alloc 的窗口内，        -/
/-     allocator 按 sel 行扣减（allocator.scala:86-92）而 rt 按 best-fit      -/
/-     选段（resource_table.scala:305-311），两者错配时扣减记到错误的行上；   -/
/-     若该 alloc 的 SCAN 被后续同 CU alloc 抢占（:560-567 允许，:137-138     -/
/-     的 ready 条件即为此设计），错配不被刷新，可累积为高估。                -/
/-  N2 见证（sgpr 通道 N=2048 实参数，全部 decide）：轨迹                     -/
/-       alloc(2038) alloc(3) alloc(1) dealloc SCAN alloc(4) alloc(1) alloc(2)-/
/-     之后 cache=(2,0) 而实际最大空段=1（rtcc_w_gapmax / rtcc_w_final_cache）；-/
/-     此时 allocator 检查 size=2 通过（rtcc_w_break_check），但 rt 无任何    -/
/-     ≥2 的空段（rtcc_w_nofit）——H-ALLOC-FIT 失效；rt FIND 失败仍按初值      -/
/-     base=0 插表（rtcc_w_find_fails / rtcc_w_corrupt），与在驻填充节点      -/
/-     [0,2038) 重叠——即 ResourceTable Q4 的链表腐蚀在真实参数下可达。       -/
/-  【破窗条件】（三条同时成立才触发，按"潜伏缺陷+监测断言"处置）            -/
/-  (a) 某次 alloc 的 rt best-fit 空段 ≠ allocator 扣减行所对应的空段         -/
/-      （cache 仅记录 top-2 长度不记录段号，错配不可避免）；                -/
/-  (b) 该 alloc 之后的 SCAN 在下一次同 CU alloc 的资源检查之前未完成         -/
/-      （抢占窗口，:560-567）；                                             -/
/-  (c) 窗口内又有同 CU alloc 凭错配后的 cache 通过检查。                     -/
/-  【监测断言建议】resource_table_handler 的 WRITE 输出路径加 DEBUG 断言：   -/
/-      非零 size 的 alloc 完成时 FIND 必须命中（found 已更新），            -/
/-      即 assert(wgsize === 0.U || 已选中真实段)；这把潜伏腐蚀变成仿真即时  -/
/-      报错。allocator.scala:91 现有断言只防扣减回绕，不防 cache 高估。      -/
/-  【对 H-ALLOC-FIT 的结论】时序一致性半边**不成立**（非"尚未证明"）：       -/
/-      G2 应改判为"已证伪 + I 类潜伏缺陷候选"，细节见 doc/03 与头注 N1/N2。  -/
/-                                                                           -/
/-  位宽说明：cache/扣减用 Nat 建模合法——守约执行下 sel 行 ≥ size           -/
/-  （rtccCheck + 高行优先规则），硬件减法不回绕（:91 断言同一事实），        -/
/-  Nat 减与 BitVec 减一致。见证全部数值 ≤ 2048，落在 sgpr 通道 12 位内。     -/
/- ========================================================================= -/

import Ventus.CTA.ResourceTable

namespace Ventus.CTA

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 事件模型：单资源通道 (rt 链表 × rtcache 两行)                            -/
/- ========================================================================= -/

/-- 单通道状态：rt 链表 + rtcache 第 0/1 行（allocator.scala:131-145 的
    rtcache_*(cuid).size(0/1)） -/
structure RtccCh where
  ram : RtRam
  c0 : Nat
  c1 : Nat

/-- 复位/初值（allocator.scala:131-145：行 0 = 满资源、行 1 = 0；rt 空表） -/
def rtccInit (N : Nat) : RtccCh := ⟨rtEmpty, N, 0⟩

/-- allocator 资源检查的资源部分（:251-262 的 orR；槽位/WF 部分由
    H-ALLOC-SLOT 等承担，与本缺口无关） -/
def rtccCheck (ch : RtccCh) (size : Nat) : Prop := size ≤ ch.c0 ∨ size ≤ ch.c1

instance rtccCheckDecidable (ch : RtccCh) (size : Nat) : Decidable (rtccCheck ch size) := by
  unfold rtccCheck
  infer_instance

/-- alloc 完成拍的 cache 扣减（allocator.scala:86-92 + :257-259 PriorityMux
    高行优先：行 1 够就扣行 1，否则扣行 0） -/
def rtccAllocCache (c0 c1 size : Nat) : Nat × Nat :=
  if size ≤ c1 then (c0, c1 - size) else (c0 - size, c1)

/-- 通道事件 -/
inductive RtccEv where
  | scan                              -- rt 的 SCAN→OUTPUT 完成、rtcache_update 落 cache
  | alloc (slot : Fin 8) (size : Nat) -- alloc 完成（检查通过 + 扣减 + rt 插表）
  | dealloc (slot : Fin 8)            -- dealloc 完成（rt 摘除；cache 不动）

/-- 单事件步进 -/
def rtccStep (N : Nat) (ch : RtccCh) : RtccEv → RtccCh
  | .scan => ⟨ch.ram, (rtScan ch.ram N).1, (rtScan ch.ram N).2⟩
  | .alloc slot size =>
      ⟨rtStep ch.ram N (.alloc slot size),
        (rtccAllocCache ch.c0 ch.c1 size).1, (rtccAllocCache ch.c0 ch.c1 size).2⟩
  | .dealloc slot => ⟨rtStep ch.ram N (.dealloc slot), ch.c0, ch.c1⟩

/-- 事件轨迹 -/
def rtccRun (N : Nat) (ch : RtccCh) (es : List RtccEv) : RtccCh :=
  es.foldl (rtccStep N) ch

/-- 事件契约：alloc 需通过 allocator 检查 + rt 侧契约（含 H-ALLOC-FIT 的
    ∃ 拟合空段——注意：本文件的 N2 见证表明该半边会被时序窗口打破，
    rtccInv_run 的结论只在"迄今未破"的轨迹上成立） -/
def rtccEvOk (N : Nat) (ch : RtccCh) : RtccEv → Prop
  | .scan => True
  | .alloc slot size => rtccCheck ch size ∧ rtEventOk ch.ram N (.alloc slot size)
  | .dealloc slot => rtEventOk ch.ram N (.dealloc slot)

/-- 空段总长的 fold（段 i..i+f-1） -/
def rtccGapSumGo (ram : RtRam) (N : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | (f+1), i => rtGapSize ram N i + rtccGapSumGo ram N f (i+1)

/-- 空段总长（段 0..cnt） -/
def rtccGapSum (ram : RtRam) (N : Nat) : Nat := rtccGapSumGo ram N (ram.cnt + 1) 0

/-- 不变式：链表良构 + 总量守恒（cache 两行和 ≤ 空段总长） -/
def RtccInv (N : Nat) (ch : RtccCh) : Prop :=
  RtWf ch.ram N ∧ ch.c0 + ch.c1 ≤ rtccGapSum ch.ram N

theorem rtccGapSumGo_zero (ram : RtRam) (N i : Nat) : rtccGapSumGo ram N 0 i = 0 := rfl

theorem rtccGapSumGo_succ (ram : RtRam) (N f i : Nat) :
    rtccGapSumGo ram N (f+1) i = rtGapSize ram N i + rtccGapSumGo ram N f (i+1) := rfl


/- ========================================================================= -/
/- 2. 正定理（一）：SCAN 后缓存的准确性与单步可靠性                          -/
/- ========================================================================= -/

/-- 当前最大空段长 -/
def rtccGapMax (ram : RtRam) (N : Nat) : Nat := rtGapMaxGo ram N (ram.cnt + 1) 0

/-- SCAN fold 保持 acc.2 ≤ acc.1（sort3 取前二，:478-484） -/
theorem rtccScanGo_snd_le (ram : RtRam) (N : Nat) :
    ∀ f i r0 r1, r1 ≤ r0 →
      (rtScanGo ram N f i (r0, r1)).2 ≤ (rtScanGo ram N f i (r0, r1)).1 := by
  intro f
  induction f with
  | zero =>
    intro i r0 r1 h
    rw [rtScanGo_zero]
    exact h
  | succ f ih =>
    intro i r0 r1 h
    rw [rtScanGo_succ]
    unfold rtScanStep
    by_cases h0 : r0 ≤ rtGapSize ram N i
    · rw [if_pos h0]
      exact ih (i+1) (rtGapSize ram N i) r0 h0
    · by_cases h1 : r1 ≤ rtGapSize ram N i
      · rw [if_neg h0, if_pos h1]
        exact ih (i+1) r0 (rtGapSize ram N i) (Nat.le_of_not_ge h0)
      · rw [if_neg h0, if_neg h1]
        exact ih (i+1) r0 r1 h

/-- SCAN 结果有序：rtcache(1) ≤ rtcache(0) -/
theorem rtccScan_snd_le (ram : RtRam) (N : Nat) : (rtScan ram N).2 ≤ (rtScan ram N).1 :=
  rtccScanGo_snd_le ram N (ram.cnt + 1) 0 0 0 (Nat.le_refl 0)

/-- **P1 单步可靠性**：cache 两行都不超过当前最大空段时，allocator 检查通过
    ⟹ rt 中确有能放下的空段（本次 alloc 的 H-ALLOC-FIT 成立）。
    注意该前提不是不变式（第 4 节的见证）；SCAN 刚落地时它成立（P2）。 -/
theorem rtcc_sound_step (ch : RtccCh) (N size : Nat)
    (h0 : ch.c0 ≤ rtccGapMax ch.ram N) (h1 : ch.c1 ≤ rtccGapMax ch.ram N)
    (hchk : rtccCheck ch size) :
    ∃ i, i ≤ ch.ram.cnt ∧ size ≤ rtGapSize ch.ram N i := by
  have hm : size ≤ rtccGapMax ch.ram N := by
    rcases hchk with h | h <;> omega
  unfold rtccGapMax at hm
  obtain ⟨j, hj0, hj1, hj2⟩ := rtGapMaxGo_mem ch.ram N size (ch.ram.cnt + 1) 0
    (Nat.succ_pos _) hm
  exact ⟨j, by omega, hj2⟩

/-- P1 推论：cache 逐线有界且表非空 ⟹ FIND 必命中（rt 不会腐蚀） -/
theorem rtcc_find_success_of_bounded (ch : RtccCh) (N size : Nat) (hwf : RtWf ch.ram N)
    (hcnt : 0 < ch.ram.cnt)
    (h0 : ch.c0 ≤ rtccGapMax ch.ram N) (h1 : ch.c1 ≤ rtccGapMax ch.ram N)
    (hchk : rtccCheck ch size) :
    (rtFind ch.ram N size).upd = true :=
  rtFind_success ch.ram N size hwf hcnt (rtcc_sound_step ch N size h0 h1 hchk)

/-- **P2 SCAN 落地后的第一次 alloc 必安全**（rtcache = 准确 top-2） -/
theorem rtcc_fit_after_scan (ch : RtccCh) (N size : Nat)
    (hchk : rtccCheck (rtccStep N ch .scan) size) :
    ∃ i, i ≤ ch.ram.cnt ∧ size ≤ rtGapSize ch.ram N i := by
  apply rtcc_sound_step (rtccStep N ch .scan) N size _ _ hchk
  · show (rtScan ch.ram N).1 ≤ rtccGapMax ch.ram N
    rw [rtScan_max]
    exact Nat.le_refl _
  · show (rtScan ch.ram N).2 ≤ rtccGapMax ch.ram N
    exact Nat.le_trans (rtccScan_snd_le ch.ram N) (by rw [rtScan_max]; exact Nat.le_refl _)

/- ========================================================================= -/
/- 3. 正定理（二）：总量守恒不变式                                            -/
/-    cache(0)+cache(1) ≤ 空段总长 在所有守约轨迹上成立                       -/
/- ========================================================================= -/

/-- fold 的末项剥离：rtccGapSumGo (f+1) i = rtccGapSumGo f i + 第 i+f 段 -/
theorem rtccGapSumGo_last (ram : RtRam) (N : Nat) :
    ∀ f i, rtccGapSumGo ram N (f+1) i = rtccGapSumGo ram N f i + rtGapSize ram N (i+f) := by
  intro f
  induction f with
  | zero =>
    intro i
    simp [rtccGapSumGo_succ, rtccGapSumGo_zero]
  | succ f ih =>
    intro i
    have e1 : rtccGapSumGo ram N (f+1+1) i =
        rtGapSize ram N i + rtccGapSumGo ram N (f+1) (i+1) := rtccGapSumGo_succ ram N (f+1) i
    have e2 := ih (i+1)
    have e3 : rtccGapSumGo ram N (f+1) i =
        rtGapSize ram N i + rtccGapSumGo ram N f (i+1) := rtccGapSumGo_succ ram N f i
    rw [e1, e2, e3]
    have e4 : i + 1 + f = i + (f + 1) := by omega
    rw [e4]
    omega

/-- 望远镜辅助：前 k+1 段总长 + 前 k+1 节点占用 = 第 k 节点末址+1 -/
theorem rtcc_telescope_aux (ram : RtRam) (N : Nat) (hwf : RtWf ram N) :
    ∀ k, k < ram.cnt →
      rtccGapSumGo ram N (k+1) 0 + rtSumSizes ram (k+1) = ram.addr2 (ram.walk k) + 1 := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hb := (hwf.bounds 0 hk).1
    have hhi : rtGapHi ram N 0 = ram.addr1 (ram.walk 0) := rtGapHi_of_lt ram N hk
    rw [rtccGapSumGo_succ, rtccGapSumGo_zero, rtSumSizes_succ, rtSumSizes_zero]
    simp only [rtGapSize, hhi, rtGapLo_zero]
    omega
  | succ k ih =>
    intro hk
    have hk' : k < ram.cnt := by omega
    have ih' := ih hk'
    rw [rtccGapSumGo_last ram N (k+1) 0, Nat.zero_add, rtSumSizes_succ]
    have hhi : rtGapHi ram N (k+1) = ram.addr1 (ram.walk (k+1)) := rtGapHi_of_lt ram N hk
    have hlo : rtGapLo ram (k+1) = ram.addr2 (ram.walk k) + 1 := rtGapLo_succ ram k
    have hb := (hwf.bounds (k+1) hk).1
    have hs := hwf.sorted k hk
    simp only [rtGapSize, hhi, hlo]
    omega

/-- **RTCC-TELESCOPE 空段-占用望远镜**：空段总长 + 节点占用总长 = N -/
theorem rtcc_gapSum (ram : RtRam) (N : Nat) (hwf : RtWf ram N) :
    rtccGapSum ram N + rtSumSizes ram ram.cnt = N := by
  unfold rtccGapSum
  by_cases hcnt : ram.cnt = 0
  · rw [hcnt]
    rw [rtccGapSumGo_succ, rtccGapSumGo_zero, rtSumSizes_zero]
    have hhi : rtGapHi ram N 0 = N := by simp [rtGapHi, hcnt]
    simp only [rtGapSize, hhi, rtGapLo_zero]
    omega
  · have hpos : 0 < ram.cnt := by omega
    have ht := rtcc_telescope_aux ram N hwf (ram.cnt - 1) (by omega)
    have e1 : ram.cnt - 1 + 1 = ram.cnt := by omega
    rw [e1] at ht
    rw [rtccGapSumGo_last ram N ram.cnt 0, Nat.zero_add]
    have hhi : rtGapHi ram N ram.cnt = N := rtGapHi_cnt ram N
    have hlo : rtGapLo ram ram.cnt = ram.addr2 (ram.walk (ram.cnt - 1)) + 1 := by
      simp [rtGapLo, hcnt]
    have hb := (hwf.bounds (ram.cnt - 1) (by omega)).2
    simp only [rtGapSize, hhi, hlo]
    omega

/-- 扣减的总量形式：检查通过 ⟹ 扣减后两行和精确减 size（不回绕，:91 的语义） -/
theorem rtccAllocCache_sum (c0 c1 size : Nat) (hchk : size ≤ c0 ∨ size ≤ c1) :
    (rtccAllocCache c0 c1 size).1 + (rtccAllocCache c0 c1 size).2 = c0 + c1 - size := by
  unfold rtccAllocCache
  by_cases h : size ≤ c1
  · rw [if_pos h]
    show c0 + (c1 - size) = c0 + c1 - size
    omega
  · rw [if_neg h]
    show c0 - size + c1 = c0 + c1 - size
    rcases hchk with h0 | h1 <;> omega

/-- alloc 保持守恒方向：链表空段总长精确减 size（契约内 alloc） -/
theorem rtcc_gapSum_alloc (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    (slot : Fin 8) (size : Nat)
    (hcnt8 : ram.cnt < rtNUM_WG_SLOT) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot)
    (hfit : size = 0 ∨ ∃ i, i ≤ ram.cnt ∧ size ≤ rtGapSize ram N i) :
    rtccGapSum (rtStep ram N (.alloc slot size)) N = rtccGapSum ram N - size := by
  by_cases hsize0 : size = 0
  · subst hsize0
    rw [rtStep_alloc, if_pos rfl]
    simp
  · obtain ⟨i, hi0, hi1⟩ := hfit.resolve_left hsize0
    rw [rtStep_alloc, if_neg hsize0]
    by_cases hcnt0 : ram.cnt = 0
    · -- 空表：FIND 保持初值，插入段 0（gapSize 0 = N ≥ size）
      rw [rtFind_empty ram N size hcnt0]
      show rtccGapSum (rtInsert ram slot 0 size 0) N = rtccGapSum ram N - size
      have hi : i = 0 := by omega
      subst hi
      have hsz : rtGapSize ram N 0 = N := by simp [rtGapSize, rtGapHi, rtGapLo, hcnt0]
      rw [hsz] at hi1
      have hhi : 0 + size ≤ rtGapHi ram N 0 := by
        have e : rtGapHi ram N 0 = N := by simp [rtGapHi, hcnt0]
        omega
      have hwf' := rtInsert_wf ram N hwf (slot := slot) (base := 0) (size := size) (k := 0)
        (Nat.zero_le _) hnew (by simp [rtGapLo]) hhi (by omega) hcnt8
      have hu := rt_alloc_used ram N hwf (slot := slot) (base := 0) (size := size) (k := 0)
        (Nat.zero_le _) hnew (by omega)
      have h1 := rtcc_gapSum _ N hwf'
      have h2 := rtcc_gapSum ram N hwf
      have hcnt' := rtInsert_cnt ram slot 0 size 0
      have hle := rt_sum_le_N _ N hwf'
      rw [hcnt'] at h1 hle
      rw [hu] at h1 hle
      omega
    · -- 非空表：FIND 命中（契约提供拟合段），插入段 fk
      have hup := rtFind_success ram N size hwf (by omega) ⟨i, hi0, hi1⟩
      obtain ⟨hfk, haddr, hsize', hfit'⟩ := rtFind_upd ram N size hwf hup
      have hwf' : RtWf (rtInsert ram slot (rtFind ram N size).faddr size
          (rtFind ram N size).fk) N := by
        have h := rt_step_wf ram N hwf (.alloc slot size) ⟨hcnt8, hnew, Or.inr ⟨i, hi0, hi1⟩⟩
        rwa [rtStep_alloc, if_neg hsize0] at h
      have hu := rt_alloc_used ram N hwf (slot := slot)
        (base := (rtFind ram N size).faddr) (size := size) (k := (rtFind ram N size).fk)
        hfk hnew (by omega)
      have h1 := rtcc_gapSum _ N hwf'
      have h2 := rtcc_gapSum ram N hwf
      have hcnt' := rtInsert_cnt ram slot (rtFind ram N size).faddr size (rtFind ram N size).fk
      have hle := rt_sum_le_N _ N hwf'
      rw [hcnt'] at h1 hle
      rw [hu] at h1 hle
      omega

/-- 摘除目标的定位必然成功（rtFindSlot 的完备性方向） -/
theorem rtccFindSlot_isSome (ram : RtRam) (slot : Fin 8)
    (h : ∃ k, k < ram.cnt ∧ ram.walk k = slot) : ∃ k', rtFindSlot ram slot = some k' := by
  cases hfs : rtFindSlot ram slot with
  | none =>
    obtain ⟨k, hk, hw⟩ := h
    exact absurd hw (rtFindSlot_none ram slot hfs k hk)
  | some k' => exact ⟨k', rfl⟩

/-- dealloc 保持守恒方向：链表空段总长只增不减（合并相邻段） -/
theorem rtcc_gapSum_dealloc_le (ram : RtRam) (N : Nat) (hwf : RtWf ram N) (slot : Fin 8)
    (hres : ∃ k, k < ram.cnt ∧ ram.walk k = slot) :
    rtccGapSum ram N ≤ rtccGapSum (rtStep ram N (.dealloc slot)) N := by
  obtain ⟨k', hfs⟩ := rtccFindSlot_isSome ram slot hres
  obtain ⟨hk, hslot⟩ := rtFindSlot_spec ram slot hfs
  rw [rtStep_dealloc, hfs]
  show rtccGapSum ram N ≤ rtccGapSum (rtRemove ram slot k') N
  have hwf' := rtRemove_wf ram N hwf hk hslot
  have hu := rt_dealloc_used ram N hwf hk hslot
  have h1 := rtcc_gapSum _ N hwf'
  have h2 := rtcc_gapSum ram N hwf
  have hcnt' := rtRemove_cnt ram slot k'
  have hle1 : rtSumSizes ram (k'+1) ≤ rtSumSizes ram ram.cnt :=
    rtSumSizes_mono_le ram (by omega)
  have hsucc := rtSumSizes_succ ram k'
  rw [hcnt'] at h1
  rw [hu] at h1
  omega

/-- rtScanStep 在字面对上的展开（避免 (r0, r1).1 形式的投影项干扰 omega） -/
theorem rtccScanStep_pair (r0 r1 sz : Nat) :
    rtScanStep (r0, r1) sz =
      if r0 ≤ sz then (sz, r0) else if r1 ≤ sz then (r0, sz) else (r0, r1) := rfl

/-- SCAN fold 的总量界：结果两行和 ≤ 初值和 + 已扫段总长 -/
theorem rtccScanGo_sum_le (ram : RtRam) (N : Nat) :
    ∀ f i r0 r1, (rtScanGo ram N f i (r0, r1)).1 + (rtScanGo ram N f i (r0, r1)).2 ≤
      r0 + r1 + rtccGapSumGo ram N f i := by
  intro f
  induction f with
  | zero =>
    intro i r0 r1
    rw [rtScanGo_zero, rtccGapSumGo_zero]
    omega
  | succ f ih =>
    intro i r0 r1
    rw [rtScanGo_succ, rtccGapSumGo_succ, rtccScanStep_pair]
    by_cases h0 : r0 ≤ rtGapSize ram N i
    · rw [if_pos h0]
      have h := ih (i+1) (rtGapSize ram N i) r0
      omega
    · by_cases h1 : r1 ≤ rtGapSize ram N i
      · rw [if_neg h0, if_pos h1]
        have h := ih (i+1) r0 (rtGapSize ram N i)
        omega
      · rw [if_neg h0, if_neg h1]
        have h := ih (i+1) r0 r1
        omega

/-- 不变式在单事件下保持 -/
theorem rtccInv_step (N : Nat) (hN : 0 < N) (ch : RtccCh) (e : RtccEv)
    (hinv : RtccInv N ch) (hok : rtccEvOk N ch e) : RtccInv N (rtccStep N ch e) := by
  obtain ⟨hwf, hsum⟩ := hinv
  cases e with
  | scan =>
    refine ⟨hwf, ?_⟩
    show (rtScan ch.ram N).1 + (rtScan ch.ram N).2 ≤ rtccGapSum ch.ram N
    have h := rtccScanGo_sum_le ch.ram N (ch.ram.cnt + 1) 0 0 0
    simpa [rtScan, rtccGapSum] using h
  | alloc slot size =>
    obtain ⟨hchk, hok2⟩ := hok
    refine ⟨rt_step_wf ch.ram N hwf (.alloc slot size) hok2, ?_⟩
    show (rtccAllocCache ch.c0 ch.c1 size).1 + (rtccAllocCache ch.c0 ch.c1 size).2 ≤
      rtccGapSum (rtStep ch.ram N (.alloc slot size)) N
    rw [rtccAllocCache_sum _ _ _ hchk]
    obtain ⟨hcnt8, hnew, hfit⟩ := hok2
    rw [rtcc_gapSum_alloc ch.ram N hwf slot size hcnt8 hnew hfit]
    exact Nat.sub_le_sub_right hsum size
  | dealloc slot =>
    refine ⟨rt_step_wf ch.ram N hwf (.dealloc slot) hok, ?_⟩
    show ch.c0 + ch.c1 ≤ rtccGapSum (rtStep ch.ram N (.dealloc slot)) N
    exact Nat.le_trans hsum (rtcc_gapSum_dealloc_le ch.ram N hwf slot hok)

/-- 初值满足不变式 -/
theorem rtccInv_init (N : Nat) (hN : 0 < N) : RtccInv N (rtccInit N) := by
  refine ⟨rtEmpty_wf N hN, ?_⟩
  show N + 0 ≤ rtccGapSum rtEmpty N
  have h : rtccGapSum rtEmpty N = N := by
    show rtccGapSumGo rtEmpty N (rtEmpty.cnt + 1) 0 = N
    rw [show rtEmpty.cnt = 0 from rfl, rtccGapSumGo_succ, rtccGapSumGo_zero]
    simp [rtGapSize, rtGapHi, rtGapLo, rtEmpty]
  omega

/-- **P3 总量守恒**：任何守约事件轨迹下，cache 对剩余总量永不高估
    （RTCC-MAIN；注意契约含 alloc 当拍的 FIT 半边——第 4 节表明该半边
    会被 SCAN 抢占窗口打破，故本定理的适用边界即"尚未腐蚀"的轨迹） -/
theorem rtccInv_run (N : Nat) (hN : 0 < N) (es : List RtccEv)
    (hok : ∀ (pre : List RtccEv) (e : RtccEv), rtccEvOk N (rtccRun N (rtccInit N) pre) e) :
    RtccInv N (rtccRun N (rtccInit N) es) := by
  have key : ∀ l : List RtccEv, RtccInv N (rtccRun N (rtccInit N) l.reverse) := by
    intro l
    induction l with
    | nil => exact rtccInv_init N hN
    | cons x xs ih =>
      have e2 : rtccRun N (rtccInit N) ((x :: xs).reverse) =
          rtccStep N (rtccRun N (rtccInit N) xs.reverse) x := by
        simp [rtccRun, List.reverse_cons, List.foldl_append]
      rw [e2]
      exact rtccInv_step N hN _ _ ih (hok _ _)
  have h := key es.reverse
  rwa [List.reverse_reverse] at h

/- ========================================================================= -/
/- 4. 破窗见证（N1/N2）：sgpr 通道实参数 N=2048，全部 decide 核证            -/
/-                                                                           -/
/-  场景：填充 WG 占据 [0,2038)，顶端留 10 单位空洞；洞内的分配/回收序列     -/
/-  制造 cache 与链表的错配。SCAN 后的三次连续 alloc（其 SCAN 被抢占，        -/
/-  resource_table.scala:560-567）使 cache 从准确的 (6,3) 漂移到 (2,0)，      -/
/-  而实际最大空段只剩 1——第四次 alloc 检查通过但无段可放。                   -/
/- ========================================================================= -/

/-- 破窗轨迹（事件含义见各条 rtcc_w_* 的注释） -/
def rtccTrace : List RtccEv :=
  [ .alloc 6 2038   -- 填充节点 F [0,2038)，留下空洞 [2038,2048)；cache (2048,0)→(10,0)
  , .alloc 0 3      -- A [2038,2041)；cache →(7,0)
  , .alloc 1 1      -- B [2041,2042)；cache →(6,0)
  , .dealloc 0      -- 摘除 A：空洞合并为 3 与 6；cache 不动 (6,0)
  , .scan           -- SCAN 落地：cache 刷新为准确的 (6,3)
  , .alloc 2 4      -- sel=0 扣行0 →(2,3)；rt best-fit 6 段 → C [2042,2046)
  , .alloc 3 1      -- sel=1 扣行1 →(2,2)；rt best-fit 是 2 段（≠行1对应的 3 段）
                    --   → D [2046,2047)：错配发生，行1 虚高
  , .alloc 4 2      -- sel=1 扣行1 →(2,0)；rt best-fit 3 段 → E [2038,2040)
  ]                 -- 实际空段 (0,1,0,0,1)，最大 1 < cache 声称的 2

/-- 轨迹第 k 个事件后的通道状态 -/
def rtccW (k : Nat) : RtccCh := rtccRun rtNUM_SGPR (rtccInit rtNUM_SGPR) (rtccTrace.take k)

-- SCAN 落地后 cache 准确：(6,3) = 当时空段 (0,3,6) 的 top-2
theorem rtcc_w_scan_cache : (rtccW 5).c0 = 6 ∧ (rtccW 5).c1 = 3 := by decide

-- 三次窗口内 alloc 后：cache (2,0)，逐行虚高（实际空段 (0,1,0,0,1)）
theorem rtcc_w_final_cache : (rtccW 8).c0 = 2 ∧ (rtccW 8).c1 = 0 := by decide

-- 实际最大空段只剩 1 —— "cache 逐行 ≤ 最大空段"被跌破（N1 的直接证据）
theorem rtcc_w_gapmax : rtccGapMax (rtccW 8).ram rtNUM_SGPR = 1 := by decide

-- 窗口内每次 alloc 的 allocator 检查都通过（含破窗的第四次 size=2）
theorem rtcc_w_checks :
    rtccCheck (rtccW 5) 4 ∧ rtccCheck (rtccW 6) 1 ∧
    rtccCheck (rtccW 7) 2 ∧ rtccCheck (rtccW 8) 2 := by decide

-- 前三次窗口内 alloc 各自当拍确有拟合空段（错配是"安全地"累积的）
theorem rtcc_w_fit5 : 4 ≤ rtccGapMax (rtccW 5).ram rtNUM_SGPR := by decide
theorem rtcc_w_fit6 : 1 ≤ rtccGapMax (rtccW 6).ram rtNUM_SGPR := by decide
theorem rtcc_w_fit7 : 2 ≤ rtccGapMax (rtccW 7).ram rtNUM_SGPR := by decide

/-- **N2-a H-ALLOC-FIT 失效**：第四次 alloc（size=2）检查通过，
    但链表中不存在 ≥2 的空段 -/
theorem rtcc_w_nofit :
    rtccCheck (rtccW 8) 2 ∧
    ¬ ∃ i, i ≤ (rtccW 8).ram.cnt ∧ 2 ≤ rtGapSize (rtccW 8).ram rtNUM_SGPR i := by
  refine ⟨by decide, ?_⟩
  intro h
  obtain ⟨i, hi, hgi⟩ := h
  have hg := rtGapMaxGo_ge (rtccW 8).ram rtNUM_SGPR 2 ((rtccW 8).ram.cnt + 1) 0 i
    (by omega) (by omega) hgi
  have hm : rtccGapMax (rtccW 8).ram rtNUM_SGPR = 1 := by decide
  unfold rtccGapMax at hm
  omega

/-- **N2-b FIND 失败仍插表**：rt 的 FIND 找不到段（upd=false）…… -/
theorem rtcc_w_find_fails : (rtFind (rtccW 8).ram rtNUM_SGPR 2).upd = false := by decide

/-- **N2-c 链表腐蚀**（ResourceTable Q4 的实参数 witness）：
    size=2 的 alloc 按 FIND 初值 base=0 插入 slot 5，区间 [0,1] 与在驻
    填充节点 slot 6 的 [0,2037] 重叠 -/
theorem rtcc_w_corrupt :
    (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr1 5 = 0 ∧
    (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr2 5 = 1 ∧
    (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr1 6 = 0 ∧
    (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr2 6 = 2037 := by decide

/-- 腐蚀的区间重叠形式化：两节点区间互含地址 0 -/
theorem rtcc_w_overlap :
    (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr1 5 ≤
      (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr2 6 ∧
    (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr1 6 ≤
      (rtStep (rtccW 8).ram rtNUM_SGPR (.alloc 5 2)).addr2 5 := by decide

/- ========================================================================= -/
/- 5. 公理审计                                                                -/
/-    全部定理仅依赖标准公理与 decide（无 bv_decide/native_decide，           -/
/-    无 LRAT/ofReduceBool 信任公理）。                                       -/
/- ========================================================================= -/

#print axioms rtcc_sound_step
#print axioms rtcc_fit_after_scan
#print axioms rtcc_find_success_of_bounded
#print axioms rtcc_gapSum
#print axioms rtcc_gapSum_alloc
#print axioms rtcc_gapSum_dealloc_le
#print axioms rtccInv_run
#print axioms rtcc_w_nofit
#print axioms rtcc_w_corrupt
#print axioms rtcc_w_overlap

end Ventus.CTA
