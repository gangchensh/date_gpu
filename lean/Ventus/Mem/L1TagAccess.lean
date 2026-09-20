/- ========================================================================= -/
/-                        Mem/L1TagAccess.lean                               -/
/-  Ventus L1TagAccess（DCache/ICache 共用 tag/替换/脏位阵列）Lean 4 模型      -/
/-                                                                           -/
/-  Chisel 源码：opengpgpu/original/ventus-gpgpu/ventus/src/L1Cache/         -/
/-    L1TagAccess.scala（全文 522 行；下文 :NNN 均指该文件）                   -/
/-                                                                           -/
/- ======================== 例化核查（2026-08-27 全仓 grep） ================= -/
/-  * L1TagAccess（DCache 版，:24-345）：仅 DCache.scala:184 一处例化，        -/
/-      set=dcache_NSets=256, way=dcache_NWays=2, tagBits=17, readOnly=false  -/
/-      （parameters.scala:71-86；readOnly=true 配置全仓无例化，不建模）       -/
/-  * L1TagAccess_ICache（:432-509）：仅 ICache.scala:83 一处，set=256, way=2, -/
/-      tagBits=21（num_fetch=2 → BlockBits=64 → BlockOffsetBits=1）          -/
/-  * ReplacementUnit（:347-379）：仅 :108 例化（DCache 版内），way=2，        -/
/-      timeLength=Length_Replace_time_SRAM=10（:70）                         -/
/-  * ReplacementUnit_ICache（:510-522）：仅 :467 例化，way=2                 -/
/-  * tagChecker（:380-410）：:112（DCache）与 :469（ICache），way=2           -/
/-  * minIdxTree（:412-431）：仅 :362 例化，numInput=way=2, width=10           -/
/-  * MMU_ENABLED=false（parameters.scala:15）→ 全部 ASID 分支不展开，不建模   -/
/-                                                                           -/
/- ======================== 建模决策 / 偏离点（D 区） ======================== -/
/-  D1. way=2 特化：实际唯一配置（DCache/ICache 均 NWays=2）。Cat/Reverse/    -/
/-      PriorityEncoder/UIntToOH/minIdxTree 均按 way=2 展开建模，语义与        -/
/-      Chisel 逐条对应（注释标行号）。                                       -/
/-  D2. st1 对齐：allocateWrite_st1 = RegEnable(bits, fire)（:110）及各        -/
/-      RegNext 链是纯延迟，模型中"当前拍输入即 st1 值"。probeReadBuf/         -/
/-      cachehit_hold（:72-73,:113,:272-278）的反压保持不重造——它只重放      -/
/-      同一拍 tagChecker 的判定结果，命中语义不变。                          -/
/-  D3. tag/time/dirtyMask 的 SRAM 本体复用 SRAMTemplate.lean（配置           -/
/-      sramCfgDCacheTag / sramCfgDCacheDirty），本文件不重复建模；集成测试     -/
/-      直接组合两个模型。                                                    -/
/-  D4. accessCount（:77 Counter(1000)）不建计数器，替换时间戳建模为输入       -/
/-      （BitVec 10）；回绕副作用记 Q5。                                      -/
/-  D5. way_valid/way_dirty 为 RegInit 寄存器阵列（:82,:105），建模为          -/
/-      Fin nset → Fin way → Bool；写口优先级按 when/elsewhen 链忠实排列       -/
/-      （valid: allocate > invalidateAll，:314-318；dirty: writeHit > flush  -/
/-      > needReplace，:281-287）。Chisel 断言（:71,:185,:280,:319）作为输入   -/
/-      契约记录，不建模。                                                    -/
/-  D6. hasDirty/dirty 扫描（:325-343）建模为 List.finRange 上的 any/find?     -/
/-      （PriorityEncoder = 最低下标优先）。                                  -/
/-  未覆盖（收窄交付，留待后续波次）：多 set/way 通用化的 ReplacementUnit/     -/
/-  minIdxTree 归纳证明；tagBodyAccess 三口仲裁器（:127-138）与 timeAccess    -/
/-  写仲裁（:181-201）的冲突时序；a_addrReplacement/asidReplacement 拼地址；   -/
/-  probeReadBuf 反压时序；dirtyTag_st1/dirtyMask_st1 输出的逐拍对齐证明。     -/
/-                                                                           -/
/- ======================== 源码审查发现（Q 区） ============================= -/
/-  Q1【I 类，I-24 独立复证】:496 ICache 版 ReplacementUnit 输入               -/
/-      `Cat(way_valid(...))` 缺 Reverse（DCache 版 :297 有）→ bit0=way1，    -/
/-      indexWhere 从 bit0 起扫 → 选择只看 way1 的 valid。机证：              -/
/-      l1ta_i24_mapping / l1ta_i24_way0_occupied / l1ta_i24_way1_never_valid -/
/-      / l1taT_two_refill_contrast；修复验证 l1ta_i24_fix_correct。          -/
/-  Q2【I 类新发现，性能 bug】DCache 版满组驱逐 MRU 而非 LRU：minIdxTree      -/
/-      候选反序装配（:426 candVec(i)=candidateIn(numInput-1-i)），输出        -/
/-      idxOfMin 是反序坐标，:364 未映射回（应 way = way-1-idx）直接当 way    -/
/-      下标用 → way=2 时恒驱逐 argmin 的补 way = 时间戳最大（最近使用）者。  -/
/-      机证：l1ta_replD2_full_evicts_mru / l1ta_replD2_full_ne_lru /         -/
/-      l1taT_replD2_full_witness。后果：热组 ping-pong 驱逐刚分配/刚命中     -/
/-      的行，命中率崩塌；不致数据错（victim 写回路径对任意合法 victim 均     -/
/-      正确），现有配置可触发（任何满组 allocate）。修复：:364 victimIdx     -/
/-      改为 (way-1) - idxOfMin，或 minIdxTree 去掉反序装配。                 -/
/-  Q3【I 类候选，一致性】dirtyMaskPerCL_init（:241-245）lane 升序 `:=` 覆盖： -/
/-      同 blockOffset 多活跃 lane 时先 lane 的 wordOffset1H 整体丢失；且     -/
/-      TagAccess 的 perLaneAddr_st1 接的是未 remap 的 coreReq_st1.           -/
/-      perLaneAddr（DCache.scala:267）——DCache.scala:111-133 的             -/
/-      remapDataPerWord 本就为"同字多 lane 合并字节掩码"存在，数据写路径     -/
/-      （:410）用 remap 后值，dirtyMask 路径用原始值。两 lane 写同字不同     -/
/-      字节（相邻地址 SB/SH）时低序号 lane 的字节脏位丢失 → 该行替换/flush  -/
/-      写回 L2 的 mask 缺字节 → L2 残留陈旧字节。机证（机制）：              -/
/-      l1taT_dmBuild_overwrite / l1taT_dmBuild_overwrite_real。可达性（      -/
/-      coalescing 是否产生同 blockOffset 多活跃 lane）需 DCache 波次确认。   -/
/-  Q4【I 类候选，协议依赖】invalidateAll（:316-318）只清 way_valid 不清      -/
/-      way_dirty → 陈旧 dirty 残留；needReplace（:294）只看 way_dirty 不看   -/
/-      valid → 之后 allocate 选中该 way 时假性 needReplace → 对无效行发起   -/
/-      写回（陈旧 tag/数据/掩码）。现配置由"flush 先于 invalidate"协议       -/
/-      （DCache.scala:782，flush 经 :283-284 逐行清 dirty）掩蔽；被注释的    -/
/-      :521 方案（不查 hasDirty 直接 invalidate）会立即触发。机证：         -/
/-      l1taT_stale_dirty_after_invalidate。                                  -/
/-  Q5【提示，性能】accessCount Counter（:77）mod 1000 回绕 → 时间戳新旧序   -/
/-      周期性反转，LRU 语义周期性失效（与 Q2 叠加，均只影响性能）。          -/
/-  Q6【提示】:307 注释"需要将dirtyMaskAccess读出的数据与way_dirtyAfterValid -/
/-      相与"未实现（:308 直接输出原始 mask）——依赖 needReplace ⟹ victim    -/
/-      valid∧dirty 的不变量；该不变量被 Q4 破坏时输出无效行的陈旧掩码。      -/
/-  Q7【提示】:334 作者自留 "todo:check correctness"；已核对：st0 用          -/
/-      choosenDirtySetIdx_st0 发读（:135-136）、waymask 经 RegNext 对齐 st1  -/
/-      （:333），时序一致，无问题。                                          -/
/-  Q8【提示】:273 cachehit_hold enq.bits.waymask 的 Mux(!ready,·,0) 冗余     -/
/-      （enq.valid = valid && !ready 已蕴含 !ready），无害。                 -/
/-  Q9【提示】:326 `way_dirty(i).zip(way_valid(i)).map { case (v, d) => ...}` -/
/-      模式绑定名 (v,d) 与实际 (dirty,valid) 颠倒，& 可交换故无害。          -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Mem.SRAMTemplate
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 位序助手（way=2 展开，D1）                                              -/
/- ========================================================================= -/

/-- Chisel `Cat([b0, b1])`（way=2 展开）：首元素在 MSB（bit1=b0, bit0=b1）。 -/
def l1taCat2 (b0 b1 : Bool) : BitVec 2 :=
  (if b0 then 0b10#2 else 0#2) ||| (if b1 then 0b01#2 else 0#2)

/-- Chisel `Reverse`（way=2 展开）：两比特交换。 -/
def l1taRev2 (b : BitVec 2) : BitVec 2 := ((b &&& 1#2) <<< 1) ||| (b >>> 1)

/-- `UIntToOH`（way=2）。 -/
def l1taOH2 (x : BitVec 1) : BitVec 2 := if x = 1#1 then 0b10#2 else 0b01#2

/- ---- 助手测试与位序引理 ---- -/

theorem l1taT_cat2 :
    l1taCat2 true false = 0b10#2 ∧ l1taCat2 false true = 0b01#2 ∧
    l1taCat2 true true = 0b11#2 ∧ l1taCat2 false false = 0#2 := by native_decide

/-- Reverse∘Cat = way 序（结果 bit j = 第 j 个元素）：tagChecker（:403）与
    DCache 版 validOfSet（:297）的正确性支点；ICache 版（:496）缺的正是它。 -/
theorem l1ta_rev2_cat2_roundtrip : ∀ b0 b1 : Bool,
    l1taRev2 (l1taCat2 b0 b1) = l1taCat2 b1 b0 := by decide

theorem l1ta_rev2_invol : ∀ b : BitVec 2, l1taRev2 (l1taRev2 b) = b := by native_decide

/-- UIntToOH 语义对照（建模自查）。 -/
theorem l1taOH2_eq (x : BitVec 1) : l1taOH2 x = 1#2 <<< x.toNat := by
  have h : x = 0#1 ∨ x = 1#1 := by bv_decide
  rcases h with rfl | rfl <;> native_decide

/- ========================================================================= -/
/- 2. tagChecker（:380-410）：命中判定                                        -/
/- ========================================================================= -/

/-- tagChecker 的 waymask（:403；MMU_ENABLED=false 分支 :399-401 → waymask=tagMatch）：
    `Reverse(Cat(逐 way 的 (tag 相等 ∧ valid)))`，结果 bit j = way j 命中。 -/
def l1taTagWaymask2 (t0 t1 tp : BitVec tb) (v0 v1 : Bool) : BitVec 2 :=
  l1taRev2 (l1taCat2 ((t0 == tp) && v0) ((t1 == tp) && v1))

/-- cache_hit = waymask.orR（:409）。 -/
def l1taTagHit2 (t0 t1 tp : BitVec tb) (v0 v1 : Bool) : Bool :=
  l1taTagWaymask2 t0 t1 tp v0 v1 != 0#2

/-- waymask 位序语义：bit j = way j 的（tag 等 ∧ valid）（Reverse 抵消 Cat 的
    MSB-first）。 -/
theorem l1ta_tagWaymask2_sem (t0 t1 tp : BitVec tb) (v0 v1 : Bool) :
    l1taTagWaymask2 t0 t1 tp v0 v1 = l1taCat2 ((t1 == tp) && v1) ((t0 == tp) && v0) := by
  by_cases h0 : t0 = tp <;> by_cases h1 : t1 = tp <;> cases v0 <;> cases v1 <;>
    simp_all [l1taTagWaymask2, l1taCat2, l1taRev2]

/-- **命中 ⟺ ∃way（tag 等 ∧ valid）**（way=2 展开形式）。 -/
theorem l1ta_tagHit2_iff (t0 t1 tp : BitVec tb) (v0 v1 : Bool) :
    l1taTagHit2 t0 t1 tp v0 v1 = true ↔
      (t0 = tp ∧ v0 = true) ∨ (t1 = tp ∧ v1 = true) := by
  by_cases h0 : t0 = tp <;> by_cases h1 : t1 = tp <;> cases v0 <;> cases v1 <;>
    simp_all [l1taTagHit2, l1taTagWaymask2, l1taCat2, l1taRev2]

/-- 同 set 两 way tag 不同 ⇒ 不会双 way 同时命中（:408 注释掉的
    PopCount≤1 断言的 way=2 形式）。 -/
theorem l1ta_tagWaymask2_not_both (t0 t1 tp : BitVec tb) (v0 v1 : Bool) (h : t0 ≠ t1) :
    l1taTagWaymask2 t0 t1 tp v0 v1 ≠ 0b11#2 := by
  by_cases h0 : t0 = tp <;> by_cases h1 : t1 = tp <;> cases v0 <;> cases v1 <;>
    simp_all [l1taTagWaymask2, l1taCat2, l1taRev2]

/- ---- tagChecker 数值测试 ---- -/

theorem l1taT_tagcheck :
    l1taTagWaymask2 0x5A#8 0x33#8 0x5A#8 true true = 0b01#2 ∧   -- way0 命中
    l1taTagWaymask2 0x5A#8 0x33#8 0x33#8 true true = 0b10#2 ∧   -- way1 命中
    l1taTagWaymask2 0x5A#8 0x33#8 0x33#8 true false = 0#2 ∧     -- tag 等但 invalid
    l1taTagHit2 0x5A#8 0x33#8 0x33#8 true true = true ∧
    l1taTagHit2 0x5A#8 0x33#8 0x77#8 true true = false := by native_decide

/- ========================================================================= -/
/- 3. ReplacementUnit（DCache 版，:347-379，:108 例化）                       -/
/- ========================================================================= -/

/-- `PriorityEncoder(~validOfSet)`（:367 非满分支）：最低无效 way 的下标。 -/
def l1taFreeIdx2 (validOfSet : BitVec 2) : BitVec 1 :=
  if (~~~validOfSet &&& 1#2) = 1#2 then 0#1 else 1#1

/-- minIdxTree（:412-431）way=2 展开：候选**反序**装配
    （candVec(0)={candidateIn(1), idx 0}、candVec(1)={candidateIn(0), idx 1}，:424-428），
    reduceTree 单次 minWithIdx（:422，严格小于取 a、否则取 b）。
    输出 idxOfMin 是**反序坐标**下的下标；:364 未做 way = way-1-idx 的映射——Q2。 -/
def l1taMinIdx2 (t0 t1 : BitVec 10) : BitVec 1 := if t1 < t0 then 0#1 else 1#1

/-- DCache 版 waymask_st1（:367）：满组走 minIdxTree（LRU 意图，有 Q2 缺陷），
    非满走最低空闲 way。 -/
def l1taReplD2 (validOfSet : BitVec 2) (t0 t1 : BitVec 10) : BitVec 2 :=
  if validOfSet = 0b11#2 then l1taOH2 (l1taMinIdx2 t0 t1)
  else l1taOH2 (l1taFreeIdx2 validOfSet)

/-- Set_is_full（:356）。 -/
def l1taSetFull2 (validOfSet : BitVec 2) : Bool := validOfSet == 0b11#2

/-- DCache 版 validOfSet 装配（:297，`Reverse(Cat(...))`）：bit j = way j 的 valid。 -/
def l1taValidOfSetD (v0 v1 : Bool) : BitVec 2 := l1taRev2 (l1taCat2 v0 v1)

/-- 非满分支选中的 way 必为无效 way（:367 的正确性性质）。 -/
theorem l1ta_freeIdx2_picks_invalid (v : BitVec 2) (h : v ≠ 0b11#2) :
    (l1taOH2 (l1taFreeIdx2 v) &&& v) = 0#2 := by
  unfold l1taOH2 l1taFreeIdx2; bv_decide

/-- 非满分支选中**最低**无效 way：所有更低编号 way 均被占用。 -/
theorem l1ta_freeIdx2_lowest (v : BitVec 2) :
    (v &&& (l1taOH2 (l1taFreeIdx2 v) - 1#2)) = (l1taOH2 (l1taFreeIdx2 v) - 1#2) := by
  unfold l1taOH2 l1taFreeIdx2; bv_decide

/-- DCache 版非满 victim（从 way_valid 出发全链路）：way0 空选 way0，
    否则选 way1——选择正确。 -/
theorem l1ta_replD2_mapping (v0 v1 : Bool) (t0 t1 : BitVec 10)
    (h : ¬(v0 = true ∧ v1 = true)) :
    l1taReplD2 (l1taValidOfSetD v0 v1) t0 t1 = (if v0 then 0b10#2 else 0b01#2) := by
  cases v0 <;> cases v1 <;>
    simp_all [l1taReplD2, l1taValidOfSetD, l1taCat2, l1taRev2, l1taFreeIdx2, l1taOH2]

/-- Q2 核心：满组时驱逐的是**时间戳较大（最近使用，MRU）**的 way。
    t0/t1 = way0/way1 的最后访问时间（:167,:188-200，越大越新）。 -/
theorem l1ta_replD2_full_evicts_mru (t0 t1 : BitVec 10) (h : t0 ≠ t1) :
    l1taReplD2 0b11#2 t0 t1 = (if t0 < t1 then 0b10#2 else 0b01#2) := by
  unfold l1taReplD2 l1taMinIdx2 l1taOH2; bv_decide

/-- LRU 规约（应然）：满组驱逐时间戳最小的 way（并列取 way0）。 -/
def l1taLruSpec2 (t0 t1 : BitVec 10) : BitVec 2 := if t0 ≤ t1 then 0b01#2 else 0b10#2

/-- Q2：实际行为与 LRU 规约在两时间戳不等时**恒相反**。 -/
theorem l1ta_replD2_full_ne_lru (t0 t1 : BitVec 10) (h : t0 ≠ t1) :
    l1taReplD2 0b11#2 t0 t1 ≠ l1taLruSpec2 t0 t1 := by
  unfold l1taReplD2 l1taMinIdx2 l1taOH2 l1taLruSpec2; bv_decide

/- ---- DCache 版替换单元数值测试 ---- -/

theorem l1taT_replD2_notfull :
    l1taReplD2 0b00#2 7#10 9#10 = 0b01#2 ∧   -- 全空 → way0
    l1taReplD2 0b01#2 7#10 9#10 = 0b10#2 ∧   -- way0 占用 → way1
    l1taReplD2 0b10#2 7#10 9#10 = 0b01#2 := by native_decide  -- way1 占用 → way0

/-- Q2 数值 witness：way1 更旧（3<5）却驱逐 way0；反向亦然。 -/
theorem l1taT_replD2_full_witness :
    l1taReplD2 0b11#2 5#10 3#10 = 0b01#2 ∧
    l1taLruSpec2 5#10 3#10 = 0b10#2 ∧
    l1taReplD2 0b11#2 3#10 5#10 = 0b10#2 ∧
    l1taLruSpec2 3#10 5#10 = 0b01#2 := by native_decide

/- ========================================================================= -/
/- 4. ReplacementUnit_ICache（:510-522，:467 例化）与 I-24 独立复证           -/
/- ========================================================================= -/

/-- ICache 版 validOfSet 装配（:496，`Cat(...)` **缺 Reverse**——I-24）：
    bit0 = way1 的 valid，bit1 = way0 的 valid。 -/
def l1taValidOfSetI (v0 v1 : Bool) : BitVec 2 := l1taCat2 v0 v1

/-- ReplacementUnit_ICache（:510-521）：非满时
    `UIntToOH(VecInit(validbits.asBools).indexWhere(===false))`（:518）从 bit0 起扫；
    满组返回轮转 victim 寄存器（:516）。 -/
def l1taReplI2 (validbits victim : BitVec 2) : BitVec 2 :=
  if validbits = 0b11#2 then victim
  else l1taOH2 (if (validbits &&& 1#2) = 0#2 then 0#1 else 1#1)

/-- 满组 victim 轮转（:521）：`Cat(victim(0), victim(1))` = 两比特交换。 -/
def l1taVictimRot2 (v : BitVec 2) : BitVec 2 := l1taRev2 v

/-- **I-24 机制全证**：非满时 ICache 版 victim 只看 **way1** 的 valid
    （Cat 后 bit0=way1），way0 的占用状态完全被忽略。
    对照正确行为 `if v0 then way1 else way0`（l1ta_replD2_mapping）。 -/
theorem l1ta_i24_mapping : ∀ (v0 v1 : Bool) (victim : BitVec 2),
    ¬(v0 = true ∧ v1 = true) →
    l1taReplI2 (l1taValidOfSetI v0 v1) victim = (if v1 then 0b10#2 else 0b01#2) := by
  decide

/-- **I-24 witness**（:496 对照 :297）：way0 已占用、way1 空闲时，
    DCache 版正确选 way1（0b10），ICache 版误选已占用的 way0（0b01）。 -/
theorem l1ta_i24_way0_occupied (victim : BitVec 2) (t0 t1 : BitVec 10) :
    l1taReplD2 (l1taValidOfSetD true false) t0 t1 = 0b10#2 ∧
    l1taReplI2 (l1taValidOfSetI true false) victim = 0b01#2 := by
  refine ⟨?_, ?_⟩
  · simp [l1taReplD2, l1taValidOfSetD, l1taCat2, l1taRev2, l1taFreeIdx2, l1taOH2]
  · simp [l1taReplI2, l1taValidOfSetI, l1taCat2, l1taOH2]

/-- ICache way_valid 单拍（:503-507）：invalidate 优先清零；
    否则写请求且非满时置 victim（OHToUInt(waymask)）位。 -/
def l1taIValidStep (v0 v1 : Bool) (wen inval : Bool) (victim : BitVec 2) : Bool × Bool :=
  if inval then (false, false)
  else if wen && !(l1taValidOfSetI v0 v1 == 0b11#2) then
    let wm := l1taReplI2 (l1taValidOfSetI v0 v1) victim
    (v0 || (wm == 0b01#2), v1 || (wm == 0b10#2))
  else (v0, v1)

/-- **I-24 退化不变式**：way1 无效则单拍后仍无效（任意写/无效化/victim 输入）。
    配合 RegInit 全 0（:464）→ way1 恒无效、Set_is_full 恒假、
    victim 轮转（:521）成为死逻辑——双路组相联退化为 way0 直接映射。 -/
theorem l1ta_i24_way1_never_valid (v0 : Bool) (wen inval : Bool) (victim : BitVec 2) :
    (l1taIValidStep v0 false wen inval victim).2 = false := by
  cases v0 <;> cases wen <;> cases inval <;>
    simp [l1taIValidStep, l1taValidOfSetI, l1taCat2, l1taReplI2, l1taOH2]

/-- 同 set 连续两次 refill 的轨迹对比（victim 由各自替换单元产生）。 -/
def l1taTraceD2 : BitVec 2 × BitVec 2 × (Bool × Bool) :=
  let v : Bool × Bool := (false, false)
  let wm1 := l1taReplD2 (l1taValidOfSetD v.1 v.2) 0#10 0#10
  let v1 := (v.1 || (wm1 == 0b01#2), v.2 || (wm1 == 0b10#2))
  let wm2 := l1taReplD2 (l1taValidOfSetD v1.1 v1.2) 1#10 1#10
  let v2 := (v1.1 || (wm2 == 0b01#2), v1.2 || (wm2 == 0b10#2))
  (wm1, wm2, v2)

def l1taTraceI2 : BitVec 2 × BitVec 2 × (Bool × Bool) :=
  let v : Bool × Bool := (false, false)
  let wm1 := l1taReplI2 (l1taValidOfSetI v.1 v.2) 0b01#2
  let v1 := (v.1 || (wm1 == 0b01#2), v.2 || (wm1 == 0b10#2))
  let wm2 := l1taReplI2 (l1taValidOfSetI v1.1 v1.2) 0b01#2
  let v2 := (v1.1 || (wm2 == 0b01#2), v1.2 || (wm2 == 0b10#2))
  (wm1, wm2, v2)

/-- I-24 轨迹 witness：DCache 版两次 refill 依次填满 way0/way1；
    ICache 版第二次仍选 way0（顶掉刚填的行），way1 恒空。 -/
theorem l1taT_two_refill_contrast :
    l1taTraceD2 = (0b01#2, 0b10#2, (true, true)) ∧
    l1taTraceI2 = (0b01#2, 0b01#2, (true, false)) := by native_decide

/-- I-24 修复验证：:496 补回 Reverse 后，ICache 版非满选择与正确行为一致。 -/
theorem l1ta_i24_fix_correct : ∀ (v0 v1 : Bool) (victim : BitVec 2),
    ¬(v0 = true ∧ v1 = true) →
    l1taReplI2 (l1taRev2 (l1taCat2 v0 v1)) victim = (if v0 then 0b10#2 else 0b01#2) := by
  decide

/-- 满组轮转（:521）数值回归（注：因 I-24 该路径在 ICache 中不可达）。 -/
theorem l1taT_victim_rot :
    l1taVictimRot2 0b01#2 = 0b10#2 ∧ l1taVictimRot2 0b10#2 = 0b01#2 := by native_decide

/- ========================================================================= -/
/- 5. way_valid / way_dirty 寄存器阵列（DCache 版，:82,:105,:281-318）        -/
/- ========================================================================= -/

/-- DCache 版 TagAccess 的寄存器阵列状态（D5）。 -/
structure L1taDState (nset way : Nat) where
  valid : Fin nset → Fin way → Bool   -- way_valid（:82）
  dirty : Fin nset → Fin way → Bool   -- way_dirty（:105）

/-- RegInit 全 0（:82,:105）。 -/
def l1taDInit : L1taDState nset way := ⟨fun _ _ => false, fun _ _ => false⟩

/-- 单拍输入（st1 对齐，D2；Chisel 断言 :71/:280/:319 为输入契约，不建模）。 -/
structure L1taDIn (nset way : Nat) where
  allocFire : Bool       -- RegNext(allocateWrite.fire)（:314）
  allocSet : Fin nset     -- allocateWrite_st1.setIdx（:110）
  allocNotFull : Bool    -- !Replacement.io.Set_is_full（:314）
  victim : Fin way       -- OHToUInt(waymaskReplacement_st1)（:299,:315）
  invalAll : Bool        -- invalidateAll（:316）
  writeHit : Bool        -- cache_hit && probeIsWrite_st1（:281）
  hitSet : Fin nset       -- RegNext(probeRead.bits.setIdx)（:282）
  hitWay : Fin way       -- OHToUInt(iTagChecker.io.waymask)（:282）
  flushV : Bool          -- flushChoosen.valid（:283）
  flushSet : Fin nset     -- flushChoosen.bits 高位（:284）
  flushWay : Fin way     -- OHToUInt(flushChoosen.bits 低位)（:284）
  needReplace : Bool     -- io.needReplace（:285,:294）

/-- 单拍转移：valid 链 allocate > invalidateAll（:314-318）；
    dirty 链 writeHit > flush > needReplace（:281-287）。 -/
def l1taDStep (st : L1taDState nset way) (i : L1taDIn nset way) : L1taDState nset way where
  valid :=
    if i.allocFire && i.allocNotFull then
      sramUpd st.valid i.allocSet (sramUpd (st.valid i.allocSet) i.victim true)
    else if i.invalAll then fun _ _ => false
    else st.valid
  dirty :=
    if i.writeHit then
      sramUpd st.dirty i.hitSet (sramUpd (st.dirty i.hitSet) i.hitWay true)
    else if i.flushV then
      sramUpd st.dirty i.flushSet (sramUpd (st.dirty i.flushSet) i.flushWay false)
    else if i.needReplace then
      sramUpd st.dirty i.allocSet (sramUpd (st.dirty i.allocSet) i.victim false)
    else st.dirty

/-- refill（allocate）置 victim 的 valid（:314-315）。 -/
theorem l1taD_alloc_sets_valid (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = true) (hnf : i.allocNotFull = true) :
    (l1taDStep st i).valid i.allocSet i.victim = true := by
  simp [l1taDStep, ha, hnf]

/-- allocate 不影响其他 set 的 valid。 -/
theorem l1taD_alloc_valid_other_set (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = true) (hnf : i.allocNotFull = true)
    (s : Fin nset) (hs : s ≠ i.allocSet) :
    (l1taDStep st i).valid s = st.valid s := by
  simp [l1taDStep, ha, hnf, sramUpd_of_ne _ _ _ _ hs]

/-- allocate 不影响同 set 其他 way 的 valid。 -/
theorem l1taD_alloc_valid_other_way (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = true) (hnf : i.allocNotFull = true)
    (w : Fin way) (hw : w ≠ i.victim) :
    (l1taDStep st i).valid i.allocSet w = st.valid i.allocSet w := by
  simp [l1taDStep, ha, hnf, sramUpd_of_ne _ _ _ _ hw]

/-- invalidateAll 清空全部 valid（:316-317）。 -/
theorem l1taD_invalidate_clears (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = false) (hi : i.invalAll = true) :
    ∀ s w, (l1taDStep st i).valid s w = false := by
  simp [l1taDStep, ha, hi]

/-- allocate 与 invalidateAll 同拍时 allocate 优先（when/elsewhen，:314-318；
    Chisel :319 断言禁止该组合，本模型忠实于优先级语义）。 -/
theorem l1taD_alloc_prio_invalidate (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = true) (hnf : i.allocNotFull = true) (hi : i.invalAll = true) :
    (l1taDStep st i).valid i.allocSet i.victim = true := by
  simp [l1taDStep, ha, hnf]

/-- 写命中置 dirty（:281-282）。 -/
theorem l1taD_writeHit_sets_dirty (st : L1taDState nset way) (i : L1taDIn nset way)
    (hw : i.writeHit = true) :
    (l1taDStep st i).dirty i.hitSet i.hitWay = true := by
  simp [l1taDStep, hw]

/-- flush 清 dirty（:283-284，writeHit 不在拍时）。 -/
theorem l1taD_flush_clears_dirty (st : L1taDState nset way) (i : L1taDIn nset way)
    (hw : i.writeHit = false) (hf : i.flushV = true) :
    (l1taDStep st i).dirty i.flushSet i.flushWay = false := by
  simp [l1taDStep, hw, hf]

/-- needReplace 清 victim 的 dirty（:285-286，writeHit/flush 不在拍时）。 -/
theorem l1taD_needReplace_clears_dirty (st : L1taDState nset way) (i : L1taDIn nset way)
    (hw : i.writeHit = false) (hf : i.flushV = false) (hn : i.needReplace = true) :
    (l1taDStep st i).dirty i.allocSet i.victim = false := by
  simp [l1taDStep, hw, hf, hn]

/-- writeHit 与 flush 同拍时 writeHit 优先（:281-285；
    Chisel :280 断言禁止该组合，本模型忠实于优先级语义）。 -/
theorem l1taD_writeHit_prio_flush (st : L1taDState nset way) (i : L1taDIn nset way)
    (hw : i.writeHit = true) (hf : i.flushV = true) :
    (l1taDStep st i).dirty i.hitSet i.hitWay = true := by
  simp [l1taDStep, hw]

/-- 无 allocate/invalidate 的拍，valid 整体不变。 -/
theorem l1taD_valid_idle (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = false) (hi : i.invalAll = false) :
    (l1taDStep st i).valid = st.valid := by
  simp [l1taDStep, ha, hi]

/- ========================================================================= -/
/- 6. hasDirty 与 dirty 扫描（:325-343，D6）                                  -/
/- ========================================================================= -/

/-- setDirty：该 set 有 dirty ∧ valid 的 way（:326-327）。 -/
def l1taSetDirty (st : L1taDState nset way) (s : Fin nset) : Bool :=
  (List.finRange way).any (fun w => st.dirty s w && st.valid s w)

/-- hasDirty_st0（:329）。 -/
def l1taHasDirtyB (st : L1taDState nset way) : Bool :=
  (List.finRange nset).any (fun s => l1taSetDirty st s)

/-- hasDirty 的命题形式。 -/
def l1taHasDirty (st : L1taDState nset way) : Prop :=
  ∃ s w, st.dirty s w = true ∧ st.valid s w = true

/-- choosenDirtySetIdx_st0（:330，PriorityEncoder = 最低下标）。 -/
def l1taChosenSet (st : L1taDState nset way) : Option (Fin nset) :=
  (List.finRange nset).find? (fun s => l1taSetDirty st s)

/-- choosenDirtyWayMask_st0（:332，PriorityEncoderOH = 最低置位 one-hot）。 -/
def l1taChosenWayOH2 (d0 d1 : Bool) : BitVec 2 :=
  if d0 then 0b01#2 else if d1 then 0b10#2 else 0#2

/-- needReplace（:294）：victim 的 dirty && 分配拍。注意**不看 valid**——Q4。 -/
def l1taNeedReplace (st : L1taDState nset way) (s : Fin nset) (w : Fin way)
    (alloc : Bool) : Bool :=
  st.dirty s w && alloc

/-- 写命中置脏一个 valid 行后，hasDirty 成立。 -/
theorem l1taD_hasDirty_after_writeHit (st : L1taDState nset way) (i : L1taDIn nset way)
    (hw : i.writeHit = true) (ha : i.allocFire = false) (hi : i.invalAll = false)
    (hv : st.valid i.hitSet i.hitWay = true) :
    l1taHasDirty (l1taDStep st i) := by
  refine ⟨i.hitSet, i.hitWay, ?_, ?_⟩
  · simp [l1taDStep, hw]
  · rw [l1taD_valid_idle st i ha hi]; exact hv

/-- invalidateAll 后无可见 dirty（valid 全清；dirty 位本身残留，见 Q4）。 -/
theorem l1taD_no_dirty_after_invalidate (st : L1taDState nset way) (i : L1taDIn nset way)
    (ha : i.allocFire = false) (hi : i.invalAll = true) :
    ¬ l1taHasDirty (l1taDStep st i) := by
  rintro ⟨s, w, -, hv⟩
  rw [l1taD_invalidate_clears st i ha hi s w] at hv
  exact Bool.noConfusion hv

/- ---- 4×2 规模有界全枚举（无 mathlib，函数空间无 Fintype，用 BitVec 8 打包） ---- -/

/-- 4×2 状态的 8 位打包：bit (2s+w)。 -/
def l1taStateOfBits (v d : BitVec 8) : L1taDState 4 2 :=
  ⟨fun s w => (v >>> (2 * s.val + w.val)) &&& 1#8 = 1#8,
   fun s w => (d >>> (2 * s.val + w.val)) &&& 1#8 = 1#8⟩

/-- hasDirtyB ⇔ "某 set 脏"（4×2 全枚举；无 mathlib，∃ over Fin 无判定实例，
    故 RHS 用显式四析取）。 -/
theorem l1taT_hasDirtyB_iff : ∀ v d : BitVec 8,
    l1taHasDirtyB (l1taStateOfBits v d) = true ↔
      (l1taSetDirty (l1taStateOfBits v d) 0 = true ∨ l1taSetDirty (l1taStateOfBits v d) 1 = true ∨
       l1taSetDirty (l1taStateOfBits v d) 2 = true ∨ l1taSetDirty (l1taStateOfBits v d) 3 = true) := by
  native_decide

/-- choosenDirtySetIdx 无结果 ⟹ 无脏行（4×2 全枚举）。 -/
theorem l1taT_chosenSet_none : ∀ v d : BitVec 8,
    l1taChosenSet (l1taStateOfBits v d) = none →
      l1taHasDirtyB (l1taStateOfBits v d) = false := by
  native_decide

/-- choosenDirtySetIdx 正确且最小（4×2 全枚举）：some s ⟹ s 脏且所有更低 set 干净。 -/
theorem l1taT_chosenSet_some_minimal : ∀ v d : BitVec 8, ∀ s : Fin 4,
    l1taChosenSet (l1taStateOfBits v d) = some s →
      (l1taSetDirty (l1taStateOfBits v d) s = true ∧
        ∀ s' : Fin 4, s'.val < s.val → l1taSetDirty (l1taStateOfBits v d) s' = false) := by
  native_decide

/-- choosenDirtyWayMask_st0 语义（:332，way=2 全枚举）。 -/
theorem l1taT_chosenWayOH2 : ∀ d0 d1 : Bool,
    (l1taChosenWayOH2 d0 d1 = 0b01#2 ↔ d0 = true) ∧
    (l1taChosenWayOH2 d0 d1 = 0b10#2 ↔ (d0 = false ∧ d1 = true)) ∧
    (l1taChosenWayOH2 d0 d1 = 0#2 ↔ (d0 = false ∧ d1 = false)) := by decide

/- ---- dirty 流程轨迹与 Q4 witness ---- -/

/-- 输入构造器：allocate / writeHit / flush / invalidateAll。 -/
def l1taInAlloc (s : Fin nset) (w : Fin way) : L1taDIn nset way :=
  { allocFire := true, allocSet := s, allocNotFull := true, victim := w,
    invalAll := false, writeHit := false, hitSet := s, hitWay := w,
    flushV := false, flushSet := s, flushWay := w, needReplace := false }
def l1taInWriteHit (s : Fin nset) (w : Fin way) : L1taDIn nset way :=
  { l1taInAlloc s w with allocFire := false, allocNotFull := false, writeHit := true }
def l1taInFlush (s : Fin nset) (w : Fin way) : L1taDIn nset way :=
  { l1taInAlloc s w with allocFire := false, allocNotFull := false, flushV := true }
def l1taInInvalAll (s : Fin nset) (w : Fin way) : L1taDIn nset way :=
  { l1taInAlloc s w with allocFire := false, allocNotFull := false, invalAll := true }

/-- 测试用具名下标常量。 -/
def l1taS0 : Fin 4 := ⟨0, by decide⟩
def l1taS1 : Fin 4 := ⟨1, by decide⟩
def l1taS2 : Fin 4 := ⟨2, by decide⟩
def l1taW0 : Fin 2 := ⟨0, by decide⟩
def l1taW1 : Fin 2 := ⟨1, by decide⟩

def l1taTD_alloc : L1taDState 4 2 := l1taDStep l1taDInit (l1taInAlloc l1taS1 l1taW0)
def l1taTD_hit := l1taDStep l1taTD_alloc (l1taInWriteHit l1taS1 l1taW0)
def l1taTD_flush := l1taDStep l1taTD_hit (l1taInFlush l1taS1 l1taW0)

/-- refill → 写命中置脏 → flush 清脏 的全流程。 -/
theorem l1taT_dirty_flow :
    l1taHasDirtyB l1taTD_alloc = false ∧
    l1taHasDirtyB l1taTD_hit = true ∧
    l1taChosenSet l1taTD_hit = some l1taS1 ∧
    l1taHasDirtyB l1taTD_flush = false := by native_decide

/-- **Q4 witness**：invalidateAll 只清 valid 不清 dirty（:316-318）→ 陈旧 dirty
    残留；之后 allocate 选中该 way 时 needReplace 假阳性（对无效行发起写回）。 -/
def l1taTQ4 : L1taDState 4 2 := l1taDStep l1taTD_hit (l1taInInvalAll l1taS1 l1taW0)

theorem l1taT_stale_dirty_after_invalidate :
    l1taTQ4.dirty l1taS1 l1taW0 = true ∧
    l1taTQ4.valid l1taS1 l1taW0 = false ∧
    l1taHasDirtyB l1taTQ4 = false ∧
    l1taNeedReplace l1taTQ4 l1taS1 l1taW0 true = true := by native_decide

/- ========================================================================= -/
/- 7. dirtyMask 构造与合并（:235-258）                                        -/
/- ========================================================================= -/

/-- perLaneAddr 三元组（activeMask, blockOffset, wordOffset1H）
    （L1Interfaces.scala:29-33）。 -/
abbrev L1taLane (bw bow : Nat) := Bool × Fin bw × BitVec bow

/-- `Vec(bw, UInt(bow)).asUInt` 展平：元素 0 在低位。 -/
def l1taDmFlatten (f : Fin bw → BitVec bow) : BitVec (bw * bow) :=
  (List.finRange bw).foldl (fun acc i => acc ||| ((f i).zeroExtend (bw*bow) <<< (i.val * bow)))
    (0 : BitVec (bw * bow))

/-- dirtyMaskPerCL_init（:239-245）：lane 升序遍历，活跃 lane 把 wordOffset1H
    写入 blockOffset 槽——**同 blockOffset 的后 lane 覆盖先 lane**（Q3）。 -/
def l1taDmBuild (lanes : Fin nl → L1taLane bw bow) : BitVec (bw * bow) :=
  l1taDmFlatten ((List.finRange nl).foldl (fun acc i =>
    let ⟨act, off, m⟩ := lanes i
    if act then sramUpd acc off m else acc) (fun _ => 0))

/-- 写命中时的最终掩码（:246）：本次贡献 | 阵列旧值。 -/
def l1taDmMerge (initb old : BitVec n) : BitVec n := initb ||| old

/-- 合并不漏位：旧值与本次贡献均为最终掩码的子集
    （实际宽度 dcache_BlockWords × BytesOfWord = 32×4 = 128）。 -/
theorem l1ta_dmMerge_superset (initb old : BitVec 128) :
    (l1taDmMerge initb old &&& old) = old ∧ (l1taDmMerge initb old &&& initb) = initb := by
  unfold l1taDmMerge; bv_decide

/-- 单活跃 lane：掩码 = 该 lane wordOffset1H 放到其 blockOffset，其余全 0。 -/
theorem l1taT_dmBuild_single : ∀ (off : Fin 4) (m : BitVec 4),
    l1taDmBuild (fun i : Fin 2 => if i = 0 then (true, off, m) else (false, off, m)) =
      (m.zeroExtend 16 <<< (off.val * 4)) := by
  native_decide

/-- **Q3 witness（小规模）**：两 lane 同 blockOffset 不同字节 →
    先 lane 的字节掩码整体消失（m0 不出现在结果中）。 -/
theorem l1taT_dmBuild_overwrite : ∀ (off : Fin 4) (m0 m1 : BitVec 4),
    l1taDmBuild (fun i : Fin 2 => if i = 0 then (true, off, m0) else (true, off, m1)) =
      (m1.zeroExtend 16 <<< (off.val * 4)) := by
  native_decide

/-- **Q3 witness（实际规模：num_lane=32, BlockWords=32, BytesOfWord=4）**：
    lane5 与 lane27 同写 block 3（byte0/byte1）→ 只剩 lane27 的 byte1，
    lane5 写入的 byte0 脏位丢失。 -/
theorem l1taT_dmBuild_overwrite_real :
    l1taDmBuild ((fun i =>
      if i = 5 then (true, 3, 0b0001#4)
      else if i = 27 then (true, 3, 0b0010#4)
      else (false, 0, 0#4)) : Fin 32 → L1taLane 32 4) =
      (0b0010#4).zeroExtend 128 <<< 12 := by
  native_decide

/- ========================================================================= -/
/- 8. 集成测试：refill → probe 命中（tag 阵列复用 SRAMTemplate，D3）          -/
/- ========================================================================= -/

/-- refill 拍：tag 写 set1/way0（wm=0b01，:310-311 的 waymask 语义）+ valid 置位。 -/
def l1taTI_v1 : L1taDState 4 2 := l1taDStep l1taDInit (l1taInAlloc l1taS1 l1taW0)
def l1taTI_s1 := sramStep sramCfgDCacheTag (sramInit 4 2 8)
  (sramInWrite l1taS1 (fun _ => 0x5A#8) 0b01#2)
/-- probe 拍：读 set1（:265-269 路径的 st1 采样）。 -/
def l1taTI_s2 := sramStep sramCfgDCacheTag l1taTI_s1 (sramInRead l1taS1)
/-- 对照：读从未 refill 的 set2（tag 上电值 0，但 valid=0）。 -/
def l1taTI_s3 := sramStep sramCfgDCacheTag l1taTI_s1 (sramInRead l1taS2)

/-- refill 后 probe 命中且 waymask 指向 victim（写后读 + valid 门控联合）。 -/
theorem l1taT_refill_then_hit :
    l1taTagWaymask2 (sramRespData sramCfgDCacheTag l1taTI_s2 l1taW0)
                    (sramRespData sramCfgDCacheTag l1taTI_s2 l1taW1) 0x5A#8
                    (l1taTI_v1.valid l1taS1 l1taW0)
                    (l1taTI_v1.valid l1taS1 l1taW1) = 0b01#2 := by
  native_decide

/-- valid 门控：tag 值相等（上电 0）但 valid=0 不命中。 -/
theorem l1taT_invalid_no_hit :
    l1taTagHit2 (sramRespData sramCfgDCacheTag l1taTI_s3 l1taW0)
                (sramRespData sramCfgDCacheTag l1taTI_s3 l1taW1) 0#8
                (l1taTI_v1.valid l1taS2 l1taW0)
                (l1taTI_v1.valid l1taS2 l1taW1) = false := by
  native_decide

/- ---- 公理审计（native_decide 测试含 Lean.ofReduceBool，bv_decide 定理含
   各自 LRAT trust 公理，均属预期） ---- -/

#print axioms l1ta_tagHit2_iff
#print axioms l1ta_replD2_full_evicts_mru
#print axioms l1ta_replD2_full_ne_lru
#print axioms l1ta_i24_mapping
#print axioms l1ta_i24_way1_never_valid
#print axioms l1taT_two_refill_contrast
#print axioms l1taT_stale_dirty_after_invalidate
#print axioms l1taT_dmBuild_overwrite_real
#print axioms l1taT_refill_then_hit

end Ventus.Mem
