/- ========================================================================= -/
/-                        Mem/DupRspTag.lean                                 -/
/-  I-44 下游核销遗留的 **TagAccess 级残余风险** 裁定：孤儿/重复 memRsp 是否    -/
/-  驱动 tag/data 阵列的错误写入（DupRsp.lean 文件头 C1 ⚠ 段）。               -/
/-                                                                           -/
/-  接口事实（Chisel 源码，2026-08-30 复核；DC:NNN = L1Cache/DCache/DCache.    -/
/-  scala，TA:NNN = L1Cache/L1TagAccess.scala）：                              -/
/-  * DC:620  allocateWrite.valid = Mux(tagReqValidCtrl,                       -/
/-      memRsp_Q.io.deq.valid && memRspIsRead, false)——**不含** L1MSHR         -/
/-      used≠0 守卫；孤儿响应的 missRspIn.ready=1（DupRsp.lean                 -/
/-      dbr_l1m_orphan_absorbed_ready）⇒ deq fire（DC:546-547）⇒ 与正品        -/
/-      一样驱动 allocateWrite。                                               -/
/-  * DC:621  allocateWrite.setIdx = d_source 低 8 位 = 请求拍冻结的 set       -/
/-      （孤儿响应与正品同 d_source ⇒ set 一致）。                             -/
/-  * DC:629  allocateWriteData_st1 = get_tag(missRspOut.bits.blockAddr)——     -/
/-      组合读 L1MSHR 簿记表、无 valid 限定；孤儿响应（entry 已释放未复用）     -/
/-      时 blockAddr = 残留旧块地址（DupRsp.lean dbr_l1m_orphan_tables_kept    -/
/-      / dbrW1_orphan_absorbed：簿记表不被孤儿污染）⇒ tag 也与正品一致。      -/
/-  * DC:633  tag SRAM 写使能 = RegNext(allocateWrite.valid) &&                -/
/-      tagAllocateWriteReady；TA:310-311 写 allocateWrite_st1.setIdx 的       -/
/-      waymask = Replacement.io.waymask_st1。                                 -/
/-  * DC:585-590  dataFillVaild = RegNext(allocateWrite.valid) &&              -/
/-      tagReplaceStatus==false && !needReplace；写地址 =                      -/
/-      Cat(missRspSetIdx_st1, OHToUInt(waymaskReplacement_st1))，数据 =       -/
/-      memRsp_st1.d_data（I-44 重复响应与正品同载荷）。                       -/
/-  * TA:297,:299,:367  waymaskReplacement_st1 由**当前** way_valid/time 经    -/
/-      ReplacementUnit 选出：非满 = PriorityEncoder(~valid)（最低空 way）；    -/
/-      满 = minIdxTree（Q2：实逐 MRU；并列时 l1taMinIdx2 取 way1）。          -/
/-  * DC:408,:416 + TA:282,:246,:192  命中读/写数据阵列、写命中置脏都走        -/
/-      OHToUInt(waymaskHit_st1)；命中刷时间戳用**原始** waymask（TA:192）。   -/
/-  * Chisel 6.4.0 `OHToUInt`（width≤2 分支 = `Log2` = 最高置位下标，全 0      -/
/-      得 0；chipsalliance/chisel v6.4.0 util/OneHot.scala）⇒ two-hot        -/
/-      0b11 → 1。                                                             -/
/-  * TA:403,:409  tagChecker.waymask = 全部（tag 等 ∧ valid）way 的匹配       -/
/-      向量（**可多热**）；TA:408 作者自留并被注释的断言：                     -/
/-      `assert(PopCount(io.waymask) <= 1.U)` —— "if waymask not one-hot,     -/
/-      duplicate tags in one set, error"。                                    -/
/-                                                                           -/
/- ======================== 裁定结论摘要 ===================================== -/
/-  R1（机制，无守卫）：孤儿/重复响应必然驱动 allocateWrite/dataFill——使能      -/
/-      式不含任何 entry 状态项（dbt_orphan_allocV / dbt_orphan_datafill）。    -/
/-  R2（幂等判据）：dup 的阵列写入幂等 ⟺ dup 拍替换选择仍指向 genuine 的 way    -/
/-      且该 way 内容未被改动（dbt_fill_idempotent_of_same——无害证明：         -/
/-      tag/data/valid 三阵列不变）。                                          -/
/-  R3（"无新 miss 即幂等"猜想**不成立**）：genuine fill 自身就置位 valid       -/
/-      （TA:314）——非满 set 上 dup 必选**不同** way                            -/
/-      （dbt_notfull_dup_way_diff，bv_decide 全枚举）→ 同 tag 同数据写入      -/
/-      另一个 way = **安装重复 tag**（dbt_fill_makes_dup_tags + witness W1）。 -/
/-      幂等仅在"genuine 后 set 满且 genuine 的 way 仍是 MRU（Q2 语义）"时      -/
/-      成立（witness W5）。                                                   -/
/-  R4（重复 tag 非透明）：probe 该 tag 得 **two-hot** waymask（dbt_dup_twohot -/
/-      / dbt_dup_hit_reads_dup_copy）——TA:408 注释断言防御的状态被达成。       -/
/-      两层偶合暂时掩蔽：(a) OHToUInt=Log2 恒选 dup 副本（way1），命中读/写/   -/
/-      置脏全走 way1（陈旧 way0 不可见）；(b) 命中刷时间戳用原始 two-hot       -/
/-      waymask ⇒ 两副本时间戳恒同（dbt_storeHit_times_tie）。                  -/
/-  R5（**有害 witness，正确性级**）：Q2 的 tie-break 满组驱逐 way1              -/
/-      （dbt_tie_evicts_way1）打破上述掩蔽——dup→写命中→同 set 新 miss→读       -/
/-      轨迹（W1-W4）：写命中只更新 way1 且两副本时间戳并列，新 miss 恰驱逐     -/
/-      way1（新数据随正确写回流向 L2），**陈旧 way0 副本复活**，之后读该块     -/
/-      命中 way0 返回**陈旧数据**（W4 vs 无 dup 对照组读回新数据，             -/
/-      dbtW_stale_read_contrast）。静默数据陈旧，全链路无报错。                -/
/-  R6（附带危害）：dup 期间 set 有效容量减半——对照 witness（dbtW_capacity）   -/
/-      无 dup 时新 miss 直接填空 way 无驱逐，有 dup 时必驱逐一行。             -/
/-  R7（更广错位情形）：两响应之间任何对 way_valid/time 的改动（新 miss、        -/
/-      hit、invalidateAll）都改变 dup 的 victim——判据统一为 R2 的             -/
/-      dbt_fill_idempotent_of_same 前提是否成立；entry 已复用（tag 写错         -/
/-      set）属 DupRsp.lean C2，不在本文件范围。                                -/
/-  修复建议（随 I-44 上报）：allocateWrite/dataFill 使能并入 L1MSHR used≠0     -/
/-  守卫（dbt_fix_orphan_noop 验证修复后孤儿零阵列写）；另建议恢复 TA:408 的    -/
/-  PopCount≤1 断言作在线检测。                                                -/
/- ========================================================================= -/

import Ventus.Mem.L1TagAccess

namespace Ventus.Mem

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 使能条件与数据来源的精确刻画（DC:526-534,:585-590,:620-621,:629,:633）   -/
/- ========================================================================= -/

/-- `TagAccess.io.allocateWrite.valid`（DC:620）：`Mux(tagReqValidCtrl,
    memRsp_Q.io.deq.valid && memRspIsRead, false)`。
    **不含** L1MSHR 的 used≠0 守卫——该守卫只经 missRspIn.ready 影响 deq.ready
    （DC:546-547），而孤儿响应 ready=1（DupRsp.lean dbr_l1m_orphan_absorbed_ready）。 -/
def dbtAllocV (ctrl deqV isRead : Bool) : Bool := ctrl && deqV && isRead

/-- tag SRAM 写使能（DC:633）：`RegNext(allocateWrite.valid) && tagAllocateWriteReady`。 -/
def dbtTagWV (prevAllocV allocRdy : Bool) : Bool := prevAllocV && allocRdy

/-- dataFill 使能（DC:585-587）：`RegNext(allocateWrite.valid) &&
    tagReplaceStatus==false && !needReplace`。 -/
def dbtDataFillV (prevAllocV tagReplaceStatus needReplace : Bool) : Bool :=
  prevAllocV && !tagReplaceStatus && !needReplace

/-- R1：孤儿响应（deqV=1 由 dbr_l1m_orphan_absorbed_ready 保证，isRead=1 因
    AccessAckData）与正品一样驱动 allocateWrite——使能式只含握手位。 -/
theorem dbt_orphan_allocV (ctrl : Bool) : dbtAllocV ctrl true true = ctrl := by
  cases ctrl <;> rfl

/-- R1：allocateWrite 有效的次拍，dataFill 使能只被替换流程状态（tagReplaceStatus、
    needReplace）调制——同样无 entry 守卫。 -/
theorem dbt_orphan_datafill (ctrl : Bool) :
    dbtDataFillV ctrl false false = ctrl := by
  cases ctrl <;> rfl

/-- Chisel 6.4.0 `OHToUInt`（way=2 展开）：width≤2 分支即 `Log2` = 最高置位下标，
    全 0 输入退化得 0（util/OneHot.scala v6.4.0；two-hot 0b11 → 1，即**较大**下标）。 -/
def dbtOH2 (wm : BitVec 2) : Fin 2 :=
  if ((wm &&& 0b10#2) != 0#2) then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- OHToUInt 数值语义回归（含 two-hot 0b11 → 1：命中多热时选中 dup 的 way1）。 -/
theorem dbtT_oh2 :
    dbtOH2 0b00#2 = ⟨0, by decide⟩ ∧ dbtOH2 0b01#2 = ⟨0, by decide⟩ ∧
    dbtOH2 0b10#2 = ⟨1, by decide⟩ ∧ dbtOH2 0b11#2 = ⟨1, by decide⟩ := by
  native_decide

/- ========================================================================= -/
/- 2. set 级阵列状态与 fill/probe/store 步进（way=2，DCache 实际配置）         -/
/- ========================================================================= -/

/-- 单个 set 的 tag/data 阵列视图：valid（TA:82,:314-315）、dirty（TA:105,:285-286）、
    tag SRAM（TA:310-311）、data SRAM（DC:585-590,:646-649）、time（TA:167,:195-200）。
    DCache 实际配置 way=2（parameters.scala；L1TagAccess.lean D1）。 -/
structure DbtSet where
  valid : Fin 2 → Bool
  dirty : Fin 2 → Bool
  tag   : Fin 2 → BitVec 17
  data  : Fin 2 → BitVec 32
  time  : Fin 2 → BitVec 10

/-- 测试用 way 下标常量。 -/
def dbtW0 : Fin 2 := ⟨0, by decide⟩
def dbtW1 : Fin 2 := ⟨1, by decide⟩

/-- Fin 2 穷举（核心库无 fin_cases）。 -/
theorem dbtW2_cases (w : Fin 2) : w = dbtW0 ∨ w = dbtW1 := by
  have hlt := w.isLt
  have hv : w.val = 0 ∨ w.val = 1 := by omega
  rcases hv with h0 | h1
  · exact Or.inl (Fin.ext h0)
  · exact Or.inr (Fin.ext h1)

/-- 当前替换选择（TA:297,:299 + ReplacementUnit TA:367；复用 L1TagAccess.lean 的
    l1taReplD2 模型，含 Q2 的 MRU/tie 语义）。 -/
def dbtWaymask (s : DbtSet) : BitVec 2 :=
  l1taReplD2 (l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1)) (s.time dbtW0) (s.time dbtW1)

/-- set 满（validOfSet 全 1，TA:356）。 -/
def dbtFullB (s : DbtSet) : Bool :=
  l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) == 0b11#2

/-- 一次 allocateWrite+dataFill 的最终阵列效应（一次 memRsp 到达，正品/孤儿/重复同构）。
    来源：setIdx = d_source 低 8 位（DC:621，本模型按 set 对齐、只建单个 set）；
    tag = get_tag(missRspOut.bits.blockAddr)（DC:629；孤儿 = 残留旧块 tag，与载荷同属
    旧块，见 DupRsp.lean C1）；data = memRsp_st1.d_data（DC:590）。
    效应：tag/data 写 victim way（TA:310-311，DC:589-590）；非满置 victim valid
    （TA:314-315）；victim dirty 归 0（本就干净，或 needReplace 分支 TA:285-286 清）；
    time 更新（TA:195-200）。
    D-注：victim 脏时 dataFill 延至 tagReplaceStatus 归假后补写（DC:561-573,:585-587），
    最终态相同；孤儿场景 L1MSHR 簿记表不被污染（dbr_l1m_orphan_tables_kept），
    延迟重写期间 tag 源不变。 -/
def dbtFill (s : DbtSet) (tg : BitVec 17) (dt : BitVec 32) (cnt : BitVec 10) : DbtSet where
  valid := if l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2 then s.valid
           else sramUpd s.valid (dbtOH2 (dbtWaymask s)) true
  dirty := sramUpd s.dirty (dbtOH2 (dbtWaymask s)) false
  tag   := sramUpd s.tag (dbtOH2 (dbtWaymask s)) tg
  data  := sramUpd s.data (dbtOH2 (dbtWaymask s)) dt
  time  := sramUpd s.time (dbtOH2 (dbtWaymask s)) cnt

/-- probe 的 waymask（TA:403：全部（tag 等 ∧ valid）way 的匹配向量，可多热）。 -/
def dbtProbeMask (s : DbtSet) (pt : BitVec 17) : BitVec 2 :=
  l1taTagWaymask2 (s.tag dbtW0) (s.tag dbtW1) pt (s.valid dbtW0) (s.valid dbtW1)

/-- cache_hit = waymask.orR（TA:409）。 -/
def dbtProbeHit (s : DbtSet) (pt : BitVec 17) : Bool := dbtProbeMask s pt != 0#2

/-- 命中读的数据（DC:416,:656：Cat(set, OHToUInt(waymaskHit_st1)) 选 way）。 -/
def dbtHitReadData (s : DbtSet) (pt : BitVec 17) : BitVec 32 :=
  s.data (dbtOH2 (dbtProbeMask s pt))

/-- 写命中（TA:281-282 + DC:408-411 + TA:188-193）对 set 的效应。
    契约：仅当 cache_hit（DBT 层 dbtProbeHit）时调用。
    数据写与置脏走 OHToUInt(waymask)（单 way）；时间戳写用**原始 waymask**
    （two-hot 时两 way 同刷，TA:192）。 -/
def dbtStoreHit (s : DbtSet) (pt : BitVec 17) (nd : BitVec 32) (cnt : BitVec 10) : DbtSet where
  valid := s.valid
  dirty := sramUpd s.dirty (dbtOH2 (dbtProbeMask s pt)) true
  tag   := s.tag
  data  := sramUpd s.data (dbtOH2 (dbtProbeMask s pt)) nd
  time  := fun j => if ((dbtProbeMask s pt >>> j.val) &&& 1#2) = 1#2 then cnt else s.time j

/- ========================================================================= -/
/- 3. 裁定定理                                                               -/
/- ========================================================================= -/

/-- **R3（非满情形 ⇒ 非幂等）**：genuine fill 后 set 仍非满时，dup 的替换选择
    **必不同于** genuine 的 way——genuine 自己已把该 way 置 valid（TA:314），
    PriorityEncoder(~valid) 必选另一个空 way（way=2 全枚举，bv_decide）。
    "两响应间无新 miss 改动替换状态即为幂等重写"的猜想对此情形不成立。 -/
theorem dbt_notfull_dup_way_diff (v : BitVec 2) (t0 t1 t0' t1' : BitVec 10)
    (h : v ≠ 0b11#2) (h' : (v ||| l1taReplD2 v t0 t1) ≠ 0b11#2) :
    l1taReplD2 (v ||| l1taReplD2 v t0 t1) t0' t1' ≠ l1taReplD2 v t0 t1 := by
  unfold l1taReplD2 l1taFreeIdx2 l1taOH2 l1taMinIdx2 at *
  bv_decide

/-- validOfSet 全 1 ⟺ 两 way 均 valid（辅助）。 -/
theorem dbtVos_eq_11 (v0 v1 : Bool) :
    l1taValidOfSetD v0 v1 = 0b11#2 ↔ v0 = true ∧ v1 = true := by
  cases v0 <;> cases v1 <;> simp [l1taValidOfSetD, l1taCat2, l1taRev2]

/-- **R2（幂等 = 无害判据）**：dup 拍 set 满、替换选择仍指向 way w、且 w 的
    现有内容就是 dup 要写的 (tag, data) 时，dup 的 fill 对 tag/data/valid 三个
    阵列**完全无效果**（仅 time 刷新、dirty 保持 0——均不可观测为错误）。 -/
theorem dbt_fill_idempotent_of_same (s : DbtSet) (tg : BitVec 17) (dt : BitVec 32)
    (cnt : BitVec 10) (w : Fin 2)
    (hfull : l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2)
    (hway : dbtOH2 (dbtWaymask s) = w)
    (htag : s.tag w = tg) (hdata : s.data w = dt) :
    (dbtFill s tg dt cnt).tag = s.tag ∧
    (dbtFill s tg dt cnt).data = s.data ∧
    (dbtFill s tg dt cnt).valid = s.valid := by
  have htag' : (dbtFill s tg dt cnt).tag = s.tag := by
    funext w'
    show sramUpd s.tag (dbtOH2 (dbtWaymask s)) tg w' = s.tag w'
    rw [hway]
    by_cases hw : w' = w
    · subst hw; rw [sramUpd_self]; exact htag.symm
    · exact sramUpd_of_ne _ _ _ _ hw
  have hdata' : (dbtFill s tg dt cnt).data = s.data := by
    funext w'
    show sramUpd s.data (dbtOH2 (dbtWaymask s)) dt w' = s.data w'
    rw [hway]
    by_cases hw : w' = w
    · subst hw; rw [sramUpd_self]; exact hdata.symm
    · exact sramUpd_of_ne _ _ _ _ hw
  have hvalid' : (dbtFill s tg dt cnt).valid = s.valid := by
    show (if l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2 then s.valid
          else sramUpd s.valid (dbtOH2 (dbtWaymask s)) true) = s.valid
    rw [if_pos hfull]
  exact ⟨htag', hdata', hvalid'⟩

/-- **R3 推论（错写 ⇒ 重复 tag）**：dup 选中 way w，而另一 way w' 已持同 tag 的
    valid 行时，fill 后**两个 way 都持该 tag 且均 valid**——TA:408 被注释的
    `PopCount(waymask) ≤ 1` 断言所防御的状态被达成。 -/
theorem dbt_fill_makes_dup_tags (s : DbtSet) (tg : BitVec 17) (dt : BitVec 32)
    (cnt : BitVec 10) (w w' : Fin 2) (hne : w ≠ w')
    (hway : dbtOH2 (dbtWaymask s) = w)
    (htg' : s.tag w' = tg) (hv' : s.valid w' = true)
    (hvw : s.valid w = true ∨ l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) ≠ 0b11#2) :
    (dbtFill s tg dt cnt).tag w = tg ∧ (dbtFill s tg dt cnt).tag w' = tg ∧
    (dbtFill s tg dt cnt).valid w = true ∧ (dbtFill s tg dt cnt).valid w' = true := by
  have htagw : (dbtFill s tg dt cnt).tag w = tg := by
    show sramUpd s.tag (dbtOH2 (dbtWaymask s)) tg w = tg
    rw [hway, sramUpd_self]
  have htagw' : (dbtFill s tg dt cnt).tag w' = tg := by
    show sramUpd s.tag (dbtOH2 (dbtWaymask s)) tg w' = tg
    rw [hway, sramUpd_of_ne _ _ _ _ (Ne.symm hne)]; exact htg'
  have hvalidw : (dbtFill s tg dt cnt).valid w = true := by
    show (if l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2 then s.valid
          else sramUpd s.valid (dbtOH2 (dbtWaymask s)) true) w = true
    by_cases hf : l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2
    · rw [if_pos hf]
      rcases hvw with h | h
      · exact h
      · exact absurd hf h
    · rw [if_neg hf, hway]; exact sramUpd_self _ _ _
  have hvalidw' : (dbtFill s tg dt cnt).valid w' = true := by
    show (if l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2 then s.valid
          else sramUpd s.valid (dbtOH2 (dbtWaymask s)) true) w' = true
    by_cases hf : l1taValidOfSetD (s.valid dbtW0) (s.valid dbtW1) = 0b11#2
    · rw [if_pos hf]; exact hv'
    · rw [if_neg hf, hway, sramUpd_of_ne _ _ _ _ (Ne.symm hne)]; exact hv'
  exact ⟨htagw, htagw', hvalidw, hvalidw'⟩

/-- **R4（重复 tag ⇒ two-hot probe）**：同 set 两 way 同 tag 同 valid 时，
    probe 该 tag 的 waymask = 0b11（**非 one-hot**）——TA:408 注释断言被违反。
    对照 L1TagAccess.lean `l1ta_tagWaymask2_not_both`（其前提 t0 ≠ t1 恰被 dup 破坏）。 -/
theorem dbt_dup_twohot (tg : BitVec 17) :
    l1taTagWaymask2 tg tg tg true true = 0b11#2 := by
  simp [l1taTagWaymask2, l1taCat2, l1taRev2]

/-- **R4 偶合 (a)**：two-hot 命中下 OHToUInt（=Log2，最高置位）恒选 **way1**
    （dup 的副本）——命中读（DC:416）、命中写（DC:408）、写命中置脏（TA:282）
    全只作用 way1；genuine 的 way0 副本自此不可见也不可写。 -/
theorem dbt_dup_hit_reads_dup_copy (s : DbtSet) (tg : BitVec 17)
    (ht0 : s.tag dbtW0 = tg) (ht1 : s.tag dbtW1 = tg)
    (hv0 : s.valid dbtW0 = true) (hv1 : s.valid dbtW1 = true) :
    dbtProbeMask s tg = 0b11#2 ∧ dbtHitReadData s tg = s.data dbtW1 := by
  have hm : dbtProbeMask s tg = 0b11#2 := by
    show l1taTagWaymask2 (s.tag dbtW0) (s.tag dbtW1) tg (s.valid dbtW0) (s.valid dbtW1) = 0b11#2
    rw [ht0, ht1, hv0, hv1]
    exact dbt_dup_twohot tg
  refine ⟨hm, ?_⟩
  show s.data (dbtOH2 (dbtProbeMask s tg)) = s.data dbtW1
  rw [hm]
  exact congrArg s.data (by native_decide)

/-- **R4 偶合 (b)**：dup 状态下的写命中把**两个** way 的时间戳刷成同一值
    （TA:192 用原始 two-hot waymask）——两副本时间戳恒同，为 Q2 的 tie-break
    （dbt_tie_evicts_way1）埋下伏笔。 -/
theorem dbt_storeHit_times_tie (s : DbtSet) (tg : BitVec 17) (nd : BitVec 32)
    (cnt : BitVec 10) (hdup : dbtProbeMask s tg = 0b11#2) :
    (dbtStoreHit s tg nd cnt).time dbtW0 = cnt ∧
    (dbtStoreHit s tg nd cnt).time dbtW1 = cnt := by
  constructor
  · show (if ((dbtProbeMask s tg >>> dbtW0.val) &&& 1#2) = 1#2 then cnt else s.time dbtW0) = cnt
    rw [hdup]
    rw [if_pos (by decide)]
  · show (if ((dbtProbeMask s tg >>> dbtW1.val) &&& 1#2) = 1#2 then cnt else s.time dbtW1) = cnt
    rw [hdup]
    rw [if_pos (by decide)]

/-- **R5 关键（Q2 tie-break）**：满组且两 way 时间戳**相等**时，minIdxTree 并列取
    反序坐标 1 → 驱逐 **way1**（dup 的副本、写命中唯一更新过的副本）。
    （对照：L1TagAccess.lean l1ta_replD2_full_evicts_mru 只覆盖 t0 ≠ t1。） -/
theorem dbt_tie_evicts_way1 (t : BitVec 10) : l1taReplD2 0b11#2 t t = 0b10#2 := by
  unfold l1taReplD2 l1taMinIdx2 l1taOH2
  bv_decide

/-- **修复验证**：allocateWrite/dataFill 使能并入 L1MSHR 的 used≠0 期待性守卫
    （DupRsp.lean 修复建议）后，孤儿响应（used=0）不产生任何 tag/data 阵列写。 -/
def dbtAllocVFixed (ctrl deqV isRead usedNz : Bool) : Bool :=
  ctrl && deqV && isRead && usedNz

theorem dbt_fix_orphan_noop (ctrl deqV isRead : Bool) :
    dbtAllocVFixed ctrl deqV isRead false = false := by
  simp [dbtAllocVFixed]

/- ========================================================================= -/
/- 4. witness 轨迹（native_decide 机证）                                      -/
/- ========================================================================= -/

/-- 测试用 tag/data 常量。 -/
def dbtTagA : BitVec 17 := 0x0123#17
def dbtTagB : BitVec 17 := 0x0456#17
def dbtDatA : BitVec 32 := 0xAAAA0000#32   -- A 的初始载荷（正品与 dup 同载荷）
def dbtDatA2 : BitVec 32 := 0xAAAA1111#32  -- 写命中后的新数据
def dbtDatB : BitVec 32 := 0xBBBB0000#32

/-- 空 set（全 invalid；上电 / invalidateAll 后的状态）。 -/
def dbtSetEmpty : DbtSet := ⟨fun _ => false, fun _ => false, fun _ => 0, fun _ => 0, fun _ => 0⟩

/- ---- dup 组：空 set → 正品 A → 重复 A → 写命中 A → 同 set 新 miss B → 读 A ---- -/

def dbtS1 := dbtFill dbtSetEmpty dbtTagA dbtDatA 10#10    -- c1：正品响应 → way0
def dbtS2 := dbtFill dbtS1 dbtTagA dbtDatA 20#10          -- c2：重复响应（孤儿）→ way1！
def dbtS3 := dbtStoreHit dbtS2 dbtTagA dbtDatA2 30#10     -- c3：写命中 A → 只写 way1
def dbtS4 := dbtFill dbtS3 dbtTagB dbtDatB 40#10          -- c4：B 的 miss → 满组 tie → 逐 way1
/-- 对照组（无重复响应）：正品 A → 写命中 A → B 的 miss → 读 A。 -/
def dbtT1 := dbtFill dbtSetEmpty dbtTagA dbtDatA 10#10
def dbtT2 := dbtStoreHit dbtT1 dbtTagA dbtDatA2 30#10     -- one-hot 命中 → 写 way0
def dbtT3 := dbtFill dbtT2 dbtTagB dbtDatB 40#10          -- set 非满 → B 填空 way1，无驱逐

/-- **W1（R3 witness）**：空 set 出发，重复响应把 tagA 装进**第二个** way——
    两 way 同 tag 同 valid，probe 得 two-hot 0b11（TA:408 注释断言防御的状态）。 -/
theorem dbtW1_dup_installed :
    dbtS2.tag dbtW0 = dbtTagA ∧ dbtS2.tag dbtW1 = dbtTagA ∧
    dbtS2.valid dbtW0 = true ∧ dbtS2.valid dbtW1 = true ∧
    dbtS2.data dbtW0 = dbtDatA ∧ dbtS2.data dbtW1 = dbtDatA ∧
    dbtProbeMask dbtS2 dbtTagA = 0b11#2 := by
  native_decide

/-- **W2（偶合 (a)(b) witness）**：dup 状态下写命中 A：新数据只写 way1、dirty 只置
    way1，两副本时间戳并列 30；此后读 A 仍得**新**数据（陈旧 way0 暂不可见）。 -/
theorem dbtW2_storeHit_dup_copy :
    dbtS3.data dbtW1 = dbtDatA2 ∧ dbtS3.data dbtW0 = dbtDatA ∧
    dbtS3.dirty dbtW1 = true ∧ dbtS3.dirty dbtW0 = false ∧
    dbtS3.time dbtW0 = 30#10 ∧ dbtS3.time dbtW1 = 30#10 ∧
    dbtHitReadData dbtS3 dbtTagA = dbtDatA2 := by
  native_decide

/-- **W3（R5 关键拍）**：B 的 miss 到达满组、时间戳并列 → Q2 tie-break 驱逐 **way1**
    （持新数据 dbtDatA2 的副本；其 dirty=1 → 新数据经正确写回流去 L2，DC:561-573），
    B 装入 way1；**陈旧 way0 副本（tagA, dbtDatA）复活为唯一匹配**。 -/
theorem dbtW3_evict_fresh_copy :
    dbtS4.tag dbtW0 = dbtTagA ∧ dbtS4.valid dbtW0 = true ∧
    dbtS4.data dbtW0 = dbtDatA ∧
    dbtS4.tag dbtW1 = dbtTagB ∧
    dbtProbeMask dbtS4 dbtTagA = 0b01#2 := by
  native_decide

/-- **W4（裁定主 witness：静默数据陈旧）**：同一段" refill A → 写 A → 同 set 新 miss B
    → 读 A"轨迹，有 dup 时读回**陈旧数据** dbtDatA（L2 已持 dbtDatA2，但 L1 命中不
    再 refetch）；无 dup 时读回**新数据** dbtDatA2（B 装入空 way1，无驱逐）。
    唯一差异 = I-44 的重复响应是否到达。 -/
theorem dbtW_stale_read_contrast :
    dbtHitReadData dbtS4 dbtTagA = dbtDatA ∧      -- 有 dup：陈旧
    dbtProbeHit dbtS4 dbtTagA = true ∧            --   （命中，无 refetch 机会）
    dbtHitReadData dbtT3 dbtTagA = dbtDatA2 ∧     -- 无 dup：正确
    dbtT3.tag dbtW0 = dbtTagA ∧ dbtT3.tag dbtW1 = dbtTagB := by
  native_decide

/-- **W5（R2 幂等分支 witness）**：genuine 填满 set（way1 持 A、时间戳最新）、
    两响应间另一 way 未被触碰时，dup 的 victim 仍是 way1 → tag/data/valid 不变，
    仅 time 刷新（无害重写）。 -/
def dbtF0 : DbtSet :=
  ⟨fun _ => true, fun _ => false,
   fun j => if j = dbtW0 then dbtTagB else dbtTagA,
   fun j => if j = dbtW0 then dbtDatB else dbtDatA,
   fun j => if j = dbtW0 then 5#10 else 20#10⟩
def dbtF1 := dbtFill dbtF0 dbtTagA dbtDatA 25#10   -- dup A 到达（满组、way1 为 MRU）

theorem dbtW5_idempotent_full_mru :
    dbtF1.tag dbtW0 = dbtF0.tag dbtW0 ∧ dbtF1.tag dbtW1 = dbtF0.tag dbtW1 ∧
    dbtF1.data dbtW0 = dbtF0.data dbtW0 ∧ dbtF1.data dbtW1 = dbtF0.data dbtW1 ∧
    dbtF1.valid dbtW0 = true ∧ dbtF1.valid dbtW1 = true ∧
    dbtF1.time dbtW1 = 25#10 := by
  native_decide

/-- **W6（R6 容量损失 witness）**：B 的 miss 到达前，dup 组 set 已满（驱逐不可避免），
    无 dup 对照组 set 非满（B 直接装入空 way，无驱逐）——dup 期间 set 有效容量减半。 -/
theorem dbtW_capacity :
    dbtFullB dbtS3 = true ∧ dbtFullB dbtT2 = false := by
  native_decide

/- ---- 公理审计（native_decide witness 带各定理 `_native.native_decide.ax_1_1`
     信任公理，bv_decide 定理带 `_native.bv_decide.ax_*`，均属本项目 4.31 工具链
     下的预期，归档注明） ---- -/

#print axioms dbtT_oh2
#print axioms dbt_notfull_dup_way_diff
#print axioms dbt_fill_idempotent_of_same
#print axioms dbt_fill_makes_dup_tags
#print axioms dbt_dup_twohot
#print axioms dbt_dup_hit_reads_dup_copy
#print axioms dbt_storeHit_times_tie
#print axioms dbt_tie_evicts_way1
#print axioms dbt_fix_orphan_noop
#print axioms dbtW1_dup_installed
#print axioms dbtW2_storeHit_dup_copy
#print axioms dbtW3_evict_fresh_copy
#print axioms dbtW_stale_read_contrast
#print axioms dbtW5_idempotent_full_mru
#print axioms dbtW_capacity

end Ventus.Mem
