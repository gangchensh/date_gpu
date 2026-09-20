/- ========================================================================= -/
/-                          Mem/ICache.lean                                  -/
/-  ICache（InstructionCache + L1TagAccess_ICache + ICacheMSHR + memRsp_Q）    -/
/-  的 Lean 4 模型、测试与证明                                                 -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    L1Cache/ICache/ICache.scala（277 行）、ICache/ICacheMSHR.scala（229 行）、-/
/-    ICache/ICacheParameters.scala（43 行）、L1Cache/L1TagAccess.scala        -/
/-      （L1TagAccess_ICache :432-509、ReplacementUnit_ICache :510-522、      -/
/-        tagChecker :380-410）、L1Cache/L1CacheParameters.scala（地址切片     -/
/-        :54-68）、SRAMTemplate（模型见 Mem/SRAMTemplate.lean）              -/
/-                                                                           -/
/-  例化配置（top/parameters.scala + ICacheParameters.scala，取默认值固化）：   -/
/-    NSets = dcache_NSets = 256（SetIdxBits = 8）、NWays = dcache_NWays = 2、 -/
/-    BlockWords = dcache_BlockWords = 32（BlockBits = 1024、                 -/
/-    BlockOffsetBits = 5、WordOffsetBits = 2）、WordLength = 32              -/
/-    （TagBits = 32-8-5-2 = 17、bABits = 25）、num_fetch = 2（响应数据 64     -/
/-    位）、num_warp = 8（WIdBits = 3）、NMshrEntry = NMshrSubEntry = 4、      -/
/-    MMU_ENABLED = false（asid/TLB 通路不展开）。                            -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 参数取上述默认值固化为字面量（Chisel 侧亦为唯一例化）。结构按          -/
/-      Chisel 逐行翻译；地址切片的一致性关系用 bv_decide 钉住。              -/
/-  D2. MMU_ENABLED = false 分支建模（ICache.scala:126-135/:227-245 与         -/
/-      L1TagAccess.scala:472-491 的 ASID/TLB 通路不展开）。                  -/
/-  D3. spike_info 仅 printf/透传（SPIKE_OUTPUT=true 但无功能影响），省略。    -/
/-  D4. memRsp_Q = Queue(ICacheMemRsp, 2, pipe=true)（ICache.scala:99）：      -/
/-      建模为 2 深指针 FIFO + 空时 enq→deq 组合旁路（pipe；flow=false，       -/
/-      enq.ready 不依赖 deq.ready）。                                        -/
/-  D5. warpid_st1/mask_st1/addr_st1 的 RegEnable 使能是 io.coreReq.ready      -/
/-      ≡ true（ICache.scala:120-125, :262）——每拍更新、与 valid 无关；        -/
/-      pipeReqAddr_st1 是 fire 门控（:142）。模型忠实区分两者。              -/
/-  D6. 宽→窄 connect 截断：ICache.scala:164 targetInfo（3 位，                -/
/-      ICacheParameters.scala:39 把 tIBits override 成 WIdBits）被赋           -/
/-      Cat(warpid, offsets)（10 位）；:169 EntryIdx（2 位）:= d_source（5     -/
/-      位）。本仓库用 Chisel 6.4.0（build.sc:32）+ CIRCT firtool，宽源        -/
/-      connect 截断保留低位（否则无法 elaborate，而 sim-verilator 流程在      -/
/-      用）。targetInfo 在本快照无消费者（missRspOut.targetInfo 只进入被      -/
/-      注释掉的 :205-216），d_source 低 2 位恰是 a_source（:249 零扩展的      -/
/-      instrId）——两处截断均无功能影响。                                    -/
/-  D7. memRsp.d_addr 在 ICache 内无消费者（tag/data 写地址取自 MSHR 的        -/
/-      missRspOut.blockAddr），模型省略。                                    -/
/-  D8. 环境假设（对应 Chisel assert）：memRsp 只回"已分配且已发访存请求"的    -/
/-      entry（ICacheMSHR.scala:163 的 assert）；coreReq 地址按 num_fetch=2    -/
/-      对齐（ICache.scala:185 的 assert，由 warp_sche 的 icache_align=8       -/
/-      保证）。本文件定理凡依赖处均显式列为假设。                             -/
/-  D9. data SRAM 读不受 invalidate 门控（ICache.scala:179 无 && !invalidate），-/
/-      tag 读有（L1TagAccess.scala:461）；tag 写/valid 位受 invalidate 门控   -/
/-      （:498,:503-507）。忠实建模。                                         -/
/-  D10. SRAM 侧直接用 Mem/SRAMTemplate.lean 的 SramState/sramStep，配置取     -/
/-      sramCfgICacheTag（F,T,F,F，L1TagAccess.scala:451-459）与               -/
/-      sramCfgICacheData（F,F,F,F，ICache.scala:84-91）。                    -/
/-  D11. 第 20 波闭包扇出根治（范本 = WarpScheduler D1）。三处函数值状态    -/
/-      字段 Array 化 + 一处严格化，全部经同名访问器保持接口：              -/
/-      (a) IcMshrState 的 4 个 per-entry 表（blockAddr/targetInfo/subValid/ -/
/-      hasSend，`Fin 4 → …`，2D 表 = Array (Array ·)）：icMshrStep 的       -/
/-      subValid/hasSend 每拍**无条件**套闭包，而组合逻辑单次求值回读 30+   -/
/-      次——跨拍 ~×5/拍扇出（实测 n=6→5ms、n=8→109ms、n=10→3.7s、          -/
/-      n=12→79s）。改为定长 4 Array，icMshrStep 每拍以 `Array.ofFn` 逐点   -/
/-      物化（输出尺寸恒 4，定理无需尺寸假设）。                            -/
/-      (b) IcTagState.wayValid（`Fin 256 → BitVec 2`）：仅 refill 时增长，  -/
/-      但写体 `old(wSet) ||| icVictimMask t wSet` 对旧链**回读两次**        -/
/-      （icVictimMask 内部再读一次），×2/refill 层扇出——SMICache 原注      -/
/-      "不炸，不动"系误判：仅做 (a) 后实测 n=60→80→100 拍 =                -/
/-      39ms→1.2s→37.9s。Array 化（写分支 ofFn 物化，输出尺寸恒 256）后     -/
/-      n=100 拍 2ms。                                                      -/
/-      (c) IcRspQ.mem（`Fin 2 → IcMemRsp`）：enq 闭包链，Array 化（2 项）。-/
/-      (d) icStep 的 data SRAM 写数据由原 `fun _ => (icDeqBits s i).dData`  -/
/-      改为严格 let 预取扁平值（预防性：消除闭包对整拍旧状态的捕获）。     -/
/-      残留已根治：SramState 已于第 21 波 Array 化（SRAMTemplate.lean       -/
/-      D10，二次尾项消除，求值严格线性：n=16000 拍 260ms）。               -/
/-                                                                           -/
/- ======================== 源码审查发现（详见各节与返回报告） =============== -/
/-  Q1（I 类，本文件主交付，ICache.scala:145+152 + :179+175 + :262）：        -/
/-      tag/data SRAM 的读（coreReq.fire 的 probe）与写（memRsp_Q.deq.fire     -/
/-      的 refill）之间**没有任何互斥**——coreReq.ready 恒 true.B（:262，       -/
/-      被注释掉的旧代码曾含 !memRsp_Q.io.deq.valid 互斥），deq.ready 只看     -/
/-      MSHR busy。而两个 SRAMTemplate 例化都是 bypassWrite=false 的           -/
/-      dual-port，同拍同 set 读写时命中 way 的读出为 LFSR64 随机值            -/
/-      （sram_lfsr_bypass 已机证）。第 7 节给出符号化机制定理                 -/
/-      （ic_tag_collision_lfsr / ic_data_collision_lfsr）与 native_decide     -/
/-      witness：假 miss（icTA_false_miss / icTA_duplicate_alloc，重复分配     -/
/-      MSHR、重复访存——性能）与假 hit（icTB_false_hit，对从未进过 cache 的    -/
/-      地址返回 status=00 HIT + LFSR 垃圾指令——**数据错误**）。              -/
/-  Q2（I 类，L1TagAccess.scala:496 + :518）：ICache 的                        -/
/-      ReplacementUnit_ICache 输入 validbits_of_set = Cat(way_valid(...))     -/
/-      **缺 Reverse**（对照 DCache 版 :297 有 Reverse）。Cat 使               -/
/-      validbits(0)=way1、validbits(1)=way0，而 indexWhere 从 bit0 起扫：     -/
/-      way0 有效/way1 空闲（v=0b01）时选中的仍是 way0 → 新块覆盖旧块、        -/
/-      way1 永远装不进（icVictimMask_way0_valid_only 与 icTD_victim_thrash    -/
/-      钉死；ic_way1_never_valid 机证：从复位起任意输入序列后 way1 恒无效、   -/
/-      victim 恒 0b01，ICache 事实退化为直接映射）。同 set 两块交替取指       -/
/-      → 每次必 miss 的 ping-pong（性能 bug，ICache 只读故不致数据错误）。   -/
/-  Q3（提示性，ICacheMSHR.scala:104-107 + :136 + :186-188）：secondary        -/
/-      miss 的 subentry 分配下标 subentryStatus.io.next 取自                   -/
/-      entryMatchMissRsp（rsp 选中行）而非匹配行——rsp 空闲时 EntryIdx 是      -/
/-      总线上的任意值，分配位置实质不确定；missReq.ready 的 subentry 满判定   -/
/-      同样看错行（icT_subfull_quirk 给出可观测反压 witness）。当前无功能     -/
/-      危害：targetInfo 是死字段（D6），subentry 计数只影响 entry 释放拍数， -/
/-      而 miss 的 warp 一律靠 status=01 后重放取指（warp_schedule.scala       -/
/-      :194-198）。                                                           -/
/-  Q4（提示性，ICacheMSHR.scala:214）：`for (i <- 0 to NMshrEntry)` 含        -/
/-      i = NMshrEntry 的越界迭代；NMshrEntry = 4（2 的幂）时 i=4 与 2 位      -/
/-      索引恒不等，是死代码；若改为非 2 幂（如 3），i=3 可命中               -/
/-      entryMatchMissRsp → 对 Vec(3) 的动态越界写（UB）。                    -/
/-  Q5（提示性，ICache.scala:217-221 + :270-276）：Status_st1 把               -/
/-      OrderViolation 编进 bit1；ov 时 coreRsp.valid 被 OrderViolation_st2    -/
/-      压低（:201），响应被丢弃，靠更早的 miss 重放覆盖（设计上自洽）。       -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Mem.SRAMTemplate
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 固化参数与地址切片（L1CacheParameters.scala:33-68）                      -/
/- ========================================================================= -/

def icSetBits : Nat := 8          -- log2Up(NSets=256)
def icTagBits : Nat := 17         -- 32-8-5-2
def icBABits : Nat := 25          -- TagBits+SetIdxBits
def icOffsetBits : Nat := 7       -- BlockOffsetBits+WordOffsetBits = 5+2
def icWIdBits : Nat := 3          -- log2Up(num_warp=8)
def icNEntry : Nat := 4           -- NMshrEntry
def icNSub : Nat := 4             -- NMshrSubEntry
def icBlockBits : Nat := 1024     -- BlockWords*4*8
def icRspDataBits : Nat := 64     -- num_fetch*xLen

/-- get_setIdx（:55-56，32 位地址）：addr(14,7)。 -/
def icGetSetIdx (a : BitVec 32) : BitVec 8 := a.extractLsb' 7 8
def icGetSetIdxFin (a : BitVec 32) : Fin 256 := (icGetSetIdx a).toFin
/-- get_tag（:54，32 位地址）：addr(31,15)。 -/
def icGetTag (a : BitVec 32) : BitVec 17 := a.extractLsb' 15 17
/-- get_blockAddr（:66）：addr(31,7)。 -/
def icGetBA (a : BitVec 32) : BitVec 25 := a.extractLsb' 7 25
/-- get_offsets（:65）：addr(6,0)。 -/
def icGetOffsets (a : BitVec 32) : BitVec 7 := a.extractLsb' 0 7
/-- get_blockOffset（:63）：addr(6,2)。 -/
def icGetBlockOffset (a : BitVec 32) : BitVec 5 := a.extractLsb' 2 5
/-- get_tag（:54，25 位 blockAddr）：ba(24,8)。 -/
def icBATag (ba : BitVec 25) : BitVec 17 := ba.extractLsb' 8 17
/-- get_setIdx（:57-58，25 位 blockAddr）：ba(7,0)。 -/
def icBASet (ba : BitVec 25) : Fin 256 := (ba.extractLsb' 0 8).toFin

/- ---- 地址切片一致性（bv_decide 前必须先 unfold 自定义 def，否则抽象为     -/
/-      不透明变量报 spurious counterexample）与数值回归 ---- -/

theorem icBATag_getBA (a : BitVec 32) : icBATag (icGetBA a) = icGetTag a := by
  have h : (icGetBA a).extractLsb' 8 17 = a.extractLsb' 15 17 := by
    simp only [icGetBA]; bv_decide
  simp [icBATag, icGetTag, h]

theorem icBASet_getBA (a : BitVec 32) : icBASet (icGetBA a) = icGetSetIdxFin a := by
  have h : (icGetBA a).extractLsb' 0 8 = a.extractLsb' 7 8 := by
    simp only [icGetBA]; bv_decide
  simp [icBASet, icGetSetIdxFin, icGetSetIdx, h]

theorem icGetBA_inj_parts (a : BitVec 32) :
    icGetBA a = (icGetTag a).zeroExtend 25 <<< 8 ||| (icGetSetIdx a).zeroExtend 25 := by
  simp only [icGetBA, icGetTag, icGetSetIdx]; bv_decide

-- 数值回归：addr = 0x55E68180 → tag=0xABCD、set=3、offsets=0
theorem icT_addr_split :
    icGetTag 0x55E68180#32 = 0x0ABCD#17 ∧ icGetSetIdxFin 0x55E68180#32 = ⟨3, by decide⟩ ∧
    icGetBA 0x55E68180#32 = 0xABCD03#25 ∧ icGetBlockOffset 0x55E68180#32 = 0#5 := by
  native_decide

/- ---- Fin 2/Fin 4 小工具（无 mathlib，fin_cases 的自给替代） ---- -/

theorem icFin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  have hlt := j.isLt
  have hv : j.val = 0 ∨ j.val = 1 := by omega
  rcases hv with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem icFin4_cases (e : Fin 4) : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by
  have hlt := e.isLt
  have hv : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨ e.val = 3 := by omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- Fin 4 不等 ⇒ beq 为 false。 -/
theorem icBeq4_ne {a b : Fin 4} (h : a ≠ b) : (a == b) = false := by simp [h]

/-- 4 项或（getEntryStatus 的 orR 类归约）。 -/
def icAny4 (f : Fin 4 → Bool) : Bool := f 0 || f 1 || f 2 || f 3
/-- 4 项与（getEntryStatus 的 andR，:69）。 -/
def icAll4 (f : Fin 4 → Bool) : Bool := f 0 && f 1 && f 2 && f 3
/-- PopCount（:67）。 -/
def icCount4 (f : Fin 4 → Bool) : Nat := (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat
/-- indexWhere（:70/:109）：最低满足项下标；无满足项时 Chisel 返回 4，
    截断到 log2Up(4)=2 位 = 0（仅对 2 的幂规模忠实，本配置 4 项成立）。 -/
def icIdxOf4 (f : Fin 4 → Bool) : Fin 4 :=
  if f 0 then 0 else if f 1 then 1 else if f 2 then 2 else if f 3 then 3 else 0
/-- OHToUInt（2 位 one-hot 或全 0 → 下标；Chisel OHToUInt 为下标 OR 归约，
    两位情形 = bit1）。 -/
def icOHToUInt2 (wm : BitVec 2) : Fin 2 := if wm.getLsbD 1 then 1 else 0

theorem icAny4_eq_true (f : Fin 4 → Bool) : icAny4 f = true ↔ ∃ e, f e = true := by
  constructor
  · intro h
    have h' : (f 0 || f 1 || f 2 || f 3) = true := h
    by_cases h0 : f 0 = true
    · exact ⟨0, h0⟩
    · by_cases h1 : f 1 = true
      · exact ⟨1, h1⟩
      · by_cases h2 : f 2 = true
        · exact ⟨2, h2⟩
        · by_cases h3 : f 3 = true
          · exact ⟨3, h3⟩
          · exfalso
            simp only [Bool.not_eq_true] at h0 h1 h2 h3
            simp [h0, h1, h2, h3] at h'
  · intro ⟨e, he⟩
    rcases icFin4_cases e with h | h | h | h <;> subst h <;> simp [icAny4, he]

theorem icAll4_eq_true (f : Fin 4 → Bool) : icAll4 f = true ↔ ∀ e, f e = true := by
  constructor
  · intro h e
    have h' : (f 0 && f 1 && f 2 && f 3) = true := h
    rcases icFin4_cases e with he | he | he | he <;> subst he <;>
      simp [Bool.and_eq_true] at h' <;> simp_all
  · intro h
    simp [icAll4, h 0, h 1, h 2, h 3]

theorem icIdxOf4_spec (f : Fin 4 → Bool) (h : icAny4 f = true) : f (icIdxOf4 f) = true := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;>
    simp_all [icIdxOf4, icAny4]

theorem icCount4_eq_one_unique (f : Fin 4 → Bool) (a b : Fin 4)
    (hc : icCount4 f = 1) (ha : f a = true) (hb : b ≠ a) : f b = false := by
  rcases icFin4_cases a with ha' | ha' | ha' | ha' <;>
    rcases icFin4_cases b with hb' | hb' | hb' | hb' <;>
    subst ha' <;> subst hb' <;>
    (cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;>
      simp_all [icCount4])

theorem icOHToUInt2_onehot (j : Fin 2) :
    icOHToUInt2 (BitVec.ofNat 2 (1 <<< j.val)) = j := by
  rcases icFin2_cases j with h | h <;> subst h <;> decide

/- ========================================================================= -/
/- 2. ICacheMSHR（ICacheMSHR.scala:73-229）                                    -/
/- ========================================================================= -/

/-- MSHR 状态：blockAddr 表（:84）、targetInfo 表（:85）、subentry_valid（:104）、
    has_send2mem（:208）、missRsqBusy（:119）、missRspInHoldingIdx 的保持寄存器
    （:121 的 RegNext）。D11：4 个 per-entry 表为定长 4 的 Array（原为
    `Fin 4 → …` 函数字段，Array 化消除跨拍闭包链求值爆炸）；函数视图由
    同名访问器（见下）提供，定理陈述不受影响。 -/
structure IcMshrState where
  blockAddrArr : Array (BitVec 25)          -- :84
  targetInfoArr : Array (Array (BitVec 3))  -- :85（entry × subentry）
  subValidArr : Array (Array Bool)          -- :104（entry × subentry）
  hasSendArr : Array Bool                   -- :208
  busy : Bool
  holdIdx : Fin 4

/-- 状态投影访问器：保持原函数字段的名称与语义（D11），实现为 Array + getD。
    越界返回默认值——自 icMshrInit 起经 icMshrStep 的可达状态各表尺寸恒 4，
    永不越界；越界语义只影响病态状态的泛化推理。所有既有的
    `s.blockAddr e`、`s.subValid e se` 等写法原样有效。 -/
def IcMshrState.blockAddr (s : IcMshrState) (e : Fin 4) : BitVec 25 :=
  s.blockAddrArr.getD e.val 0#25
/-- targetInfo 访问器（:85），见 blockAddr。 -/
def IcMshrState.targetInfo (s : IcMshrState) (e se : Fin 4) : BitVec 3 :=
  (s.targetInfoArr.getD e.val #[]).getD se.val 0#3
/-- subentry_valid 访问器（:104），见 blockAddr。 -/
def IcMshrState.subValid (s : IcMshrState) (e se : Fin 4) : Bool :=
  (s.subValidArr.getD e.val #[]).getD se.val false
/-- has_send2mem 访问器（:208），见 blockAddr。 -/
def IcMshrState.hasSend (s : IcMshrState) (e : Fin 4) : Bool :=
  s.hasSendArr.getD e.val false

/-- ofFn 物化表的回读（表尺寸恒 n，Fin n 索引必在界内）——Array 化后
    "写后读"的基础引理（对照 WarpScheduler 的 wsRd8_wr8_self/of_ne）。 -/
theorem icRd_ofFn (f : Fin n → α) (e : Fin n) (d : α) :
    (Array.ofFn f).getD e.val d = f e := by
  simp [Array.getD_eq_getD_getElem?]

/-- RegInit 全 0/全 invalid（:84-85,:104,:119,:208 的 reset 语义） -/
def icMshrInit : IcMshrState :=
  ⟨Array.replicate 4 0#25, Array.replicate 4 (Array.replicate 4 0#3),
   Array.replicate 4 (Array.replicate 4 false), Array.replicate 4 false, false, 0⟩

/-- 初态访问器求值（供不变式奠基等 simp 使用）。 -/
@[simp] theorem icMshrInit_blockAddr (e : Fin 4) : icMshrInit.blockAddr e = 0#25 := by
  simp [IcMshrState.blockAddr, icMshrInit, Array.getD_eq_getD_getElem?]
@[simp] theorem icMshrInit_targetInfo (e se : Fin 4) :
    icMshrInit.targetInfo e se = 0#3 := by
  simp [IcMshrState.targetInfo, icMshrInit, Array.getD_eq_getD_getElem?]
@[simp] theorem icMshrInit_subValid (e se : Fin 4) : icMshrInit.subValid e se = false := by
  simp [IcMshrState.subValid, icMshrInit, Array.getD_eq_getD_getElem?]
@[simp] theorem icMshrInit_hasSend (e : Fin 4) : icMshrInit.hasSend e = false := by
  simp [IcMshrState.hasSend, icMshrInit, Array.getD_eq_getD_getElem?]

/-- MSHR 每拍输入（missReq/missRspIn/miss2mem.ready 三通道；missRspOut.ready
    恒 true，ICache.scala:171）。 -/
structure IcMshrIn where
  reqValid : Bool
  reqBA : BitVec 25
  reqTI : BitVec 3
  rspValid : Bool
  rspIdx : Fin 4
  memReady : Bool

section IcMshrComb

variable (s : IcMshrState) (i : IcMshrIn)

/-- entry_valid（:112）。 -/
def icEntryValid (e : Fin 4) : Bool :=
  s.subValid e 0 || s.subValid e 1 || s.subValid e 2 || s.subValid e 3

/-- entryMatchMissReq（:155，MMU off 分支）。 -/
def icMatchVec (ba : BitVec 25) (e : Fin 4) : Bool :=
  (s.blockAddr e == ba) && icEntryValid s e

def icSecondary : Bool := icAny4 (icMatchVec s i.reqBA)              -- :127
def icMatchIdx : Fin 4 := icIdxOf4 (icMatchVec s i.reqBA)            -- OHToUInt(:135)
def icEntryFull : Bool := icAll4 (icEntryValid s)                    -- entryStatus.full
def icEntryNext : Fin 4 := icIdxOf4 (fun e => !icEntryValid s e)     -- entryStatus.next

/-- entryMatchMissRsp（:121-122）。 -/
def icRspSel : Fin 4 := if s.busy then s.holdIdx else i.rspIdx
/-- subentryStatus 作用在 **rsp 选中行**（:105-107，Q3）。 -/
def icSelUsed : Nat := icCount4 (s.subValid (icRspSel s i))
def icSelFull : Bool := icAll4 (s.subValid (icRspSel s i))
def icSelNext : Fin 4 := icIdxOf4 (fun se => !s.subValid (icRspSel s i) se)
def icNext2Cancel : Fin 4 := icIdxOf4 (s.subValid (icRspSel s i))    -- :109

def icRspInFire : Bool := i.rspValid && !s.busy                      -- :172 ready=¬busy
def icRspOutFire : Bool := icRspInFire s i || s.busy                 -- :173（ready=true）
def icRspInBA : BitVec 25 := s.blockAddr i.rspIdx                    -- :224

/-- ReqConflictWithRsp（:156-158，MMU off 分支）。 -/
def icConflict : Bool :=
  i.reqValid &&
    ((icRspInFire s i && (icRspInBA s i == i.reqBA)) ||
     (s.busy && (s.blockAddr s.holdIdx == i.reqBA)))

/-- io.missReq.ready（:132-133；注意 subentry 满看的是 rsp 选中行，Q3）。 -/
def icMshrReqReady : Bool :=
  !((icEntryFull s && !icSecondary s i) || (icSelFull s i && icSecondary s i) || icConflict s i)

def icMshrReqFire : Bool := i.reqValid && icMshrReqReady s i

/-- tAEntryIdx / tASubEntryIdx（:135-136）。 -/
def icTAEntry : Fin 4 := if icSecondary s i then icMatchIdx s i else icEntryNext s
def icTASub : Fin 4 := if icSecondary s i then icSelNext s i else 0

/-- miss2mem（:210-211, :221-222）：next = 最低"已分配未发送"项（全已发送时
    截断为 0，此时 entry_valid(0)/hasSend(0) 使 valid 仍正确）。 -/
def icMemNext : Fin 4 := icIdxOf4 (fun e => !s.hasSend e && icEntryValid s e)
def icMemValid : Bool := !s.hasSend (icMemNext s) && icEntryValid s (icMemNext s)
def icMemFire : Bool := icMemValid s && i.memReady

def icRspOutValid : Bool := icRspOutFire s i                        -- :173
def icRspOutBA : BitVec 25 := s.blockAddr (icRspSel s i)            -- :176
def icRspOutTI : BitVec 3 := s.targetInfo (icRspSel s i) (icNext2Cancel s i)  -- :175

end IcMshrComb

/-- 单拍转移（:138-139, :180-200, :203-205, :214-219, :166-170, :121）。
    D11：4 个表字段以 `Array.ofFn` 逐点物化（每槽位 = 旧访问器的逐点表达式，
    构造时即逐槽求值，不留跨拍闭包）；逐点语义与原闭包版逐项相同。 -/
def icMshrStep (s : IcMshrState) (i : IcMshrIn) : IcMshrState where
  blockAddrArr := Array.ofFn fun e =>
    (if icMshrReqFire s i && !icSecondary s i then sramUpd s.blockAddr (icEntryNext s) i.reqBA
     else s.blockAddr) e
  targetInfoArr := Array.ofFn fun e => Array.ofFn fun se =>
    if icMshrReqFire s i then
      (if e == icTAEntry s i && se == icTASub s i then i.reqTI else s.targetInfo e se)
    else s.targetInfo e se
  subValidArr := Array.ofFn fun e => Array.ofFn fun se =>
    if icMshrReqFire s i then
      (if e == icEntryNext s && se == 0 && !icSecondary s i then true
       else if e == icMatchIdx s i && se == icSelNext s i && icSecondary s i then true
       else if icRspOutFire s i && e == icRspSel s i && se == icNext2Cancel s i then false
       else s.subValid e se)
    else if icRspOutFire s i && e == icRspSel s i && se == icNext2Cancel s i then false
    else s.subValid e se
  hasSendArr := Array.ofFn fun e =>
    if icMemFire s i && e == icMemNext s then true
    else if (s.busy || icRspInFire s i) && icRspOutFire s i && icSelUsed s i == 1 &&
        e == icRspSel s i then false
    else s.hasSend e
  busy :=
    if icRspInFire s i && !(icSelUsed s i == 1) then true
    else if s.busy && icSelUsed s i == 1 then false
    else s.busy
  holdIdx := icRspSel s i

/-- 多拍执行。 -/
def icMshrRun (s : IcMshrState) (is : List IcMshrIn) : IcMshrState :=
  is.foldl icMshrStep s

/- 求值性能对照（第 20 波，2026-08-28；探针 /tmp/icprobe/IcProbe.lean 编译为
   原生二进制（lake env lean -c + leanc 链 Ventus .so），混合输入轨迹
   （probe/rsp/idle 按拍轮换），每拍 icStep + MSHR 全字段深读校验和，
   IO.monoMsNow 计时；校验和同时充当行为保持的交叉验证）。
   改造前（全部函数字段，闭包链跨拍重入）：
     n=4 → 1ms，n=6 → 5ms，n=8 → 109ms，n=10 → 3722ms，n=12 → 79088ms
     （~×5/拍爆炸；校验和 33777675 / 64125458 / 102303001 / 132650784 /
      155169319）。
   仅 IcMshrState Array 化（中间态）：12 拍即 0ms，但 wayValid 双重回读
     扇出接棒：n=60 → 39ms、n=80 → 1.2s、n=100 → 37.9s（~×1.18/拍）。
   最终（D11 (a)-(d) 全部完成）：
     n=100 → 2ms，n=1000 → 97ms，n=5000 → 2533ms，n=20000 → 59.4s
     （残留为 SRAMTemplate 闭包链的二次尾项，见 D11 末尾）。
   行为保持交叉验证：改造前后 n=4/6/8/10/12/100 校验和逐项一致；
   SMICache 全 10 条 native_decide 轨迹定理在适配后原样通过（见日志）。 -/

/-- subValid 字段的展开等式（供 if_pos/if_neg 显式推理；simp 对嵌套
    if + beq 的条件容易走偏，故显式化）。D11：Array 化后经访问器+ofFn
    回读引理证得，陈述与原闭包版逐字相同。 -/
@[simp] theorem icMshrStep_subValid (s : IcMshrState) (i : IcMshrIn) (e se : Fin 4) :
    (icMshrStep s i).subValid e se =
      (if icMshrReqFire s i then
        (if e == icEntryNext s && se == 0 && !icSecondary s i then true
         else if e == icMatchIdx s i && se == icSelNext s i && icSecondary s i then true
         else if icRspOutFire s i && e == icRspSel s i && se == icNext2Cancel s i then false
         else s.subValid e se)
       else
        (if icRspOutFire s i && e == icRspSel s i && se == icNext2Cancel s i then false
         else s.subValid e se)) := by
  simp [IcMshrState.subValid, icMshrStep]

/-- blockAddr 字段的展开等式（D11，同 icMshrStep_subValid）。 -/
@[simp] theorem icMshrStep_blockAddr (s : IcMshrState) (i : IcMshrIn) (e : Fin 4) :
    (icMshrStep s i).blockAddr e =
      (if icMshrReqFire s i && !icSecondary s i then
        sramUpd s.blockAddr (icEntryNext s) i.reqBA else s.blockAddr) e := by
  simp [IcMshrState.blockAddr, icMshrStep]

/-- targetInfo 字段的展开等式（D11，同 icMshrStep_subValid）。 -/
@[simp] theorem icMshrStep_targetInfo (s : IcMshrState) (i : IcMshrIn) (e se : Fin 4) :
    (icMshrStep s i).targetInfo e se =
      (if icMshrReqFire s i then
        (if e == icTAEntry s i && se == icTASub s i then i.reqTI else s.targetInfo e se)
       else s.targetInfo e se) := by
  simp [IcMshrState.targetInfo, icMshrStep]

/-- hasSend 字段的展开等式（D11，同 icMshrStep_subValid）。 -/
@[simp] theorem icMshrStep_hasSend (s : IcMshrState) (i : IcMshrIn) (e : Fin 4) :
    (icMshrStep s i).hasSend e =
      (if icMemFire s i && e == icMemNext s then true
       else if (s.busy || icRspInFire s i) && icRspOutFire s i && icSelUsed s i == 1 &&
           e == icRspSel s i then false
       else s.hasSend e) := by
  simp [IcMshrState.hasSend, icMshrStep]

/- ========================================================================= -/
/- 3. MSHR 符号化定理                                                         -/
/- ========================================================================= -/

section IcMshrThms

variable {s : IcMshrState} {i : IcMshrIn}

/-- missReq.ready 定义即规约（:132-133）。 -/
theorem icMshr_reqReady_spec :
    icMshrReqReady s i =
      !((icEntryFull s && !icSecondary s i) ||
        (icSelFull s i && icSecondary s i) || icConflict s i) := rfl

/-- 与 rsp 冲突的同块 miss 被拒（:131-133, :156-158）：core 收到
    reservation fail（status=11）后重试。 -/
theorem icMshr_conflict_block (h : icConflict s i = true) :
    icMshrReqReady s i = false := by
  simp [icMshrReqReady, h]

/-- busy 期间 missRspIn 不 ready（:172）——memRsp_Q 顶住，响应不丢。 -/
theorem icMshr_busy_rspIn_not_ready (h : s.busy = true) :
    icRspInFire s i = false := by
  simp [icRspInFire, h]

/-- hasSendStatus.next 指向一个"已分配未发送"项（若存在）。 -/
theorem icMemNext_spec (h : icAny4 (fun e => !s.hasSend e && icEntryValid s e) = true) :
    (!s.hasSend (icMemNext s) && icEntryValid s (icMemNext s)) = true := by
  have h2 := icIdxOf4_spec _ h
  simpa [icMemNext] using h2

/-- 主 miss 分配：写入 entryNext 的 blockAddr/subValid[0]/targetInfo（:138-139,
    :183-185, :203-205），其余 entry 的 blockAddr 不变。 -/
theorem icMshr_primary_alloc (hf : icMshrReqFire s i = true) (hp : icSecondary s i = false) :
    (icMshrStep s i).blockAddr (icEntryNext s) = i.reqBA ∧
    (icMshrStep s i).subValid (icEntryNext s) 0 = true ∧
    (icMshrStep s i).targetInfo (icEntryNext s) 0 = i.reqTI ∧
    (∀ e, e ≠ icEntryNext s → (icMshrStep s i).blockAddr e = s.blockAddr e) := by
  have hta : icTAEntry s i = icEntryNext s := by simp [icTAEntry, hp]
  have hts : icTASub s i = 0 := by simp [icTASub, hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hf, hp]
  · simp [hf, hp]
  · simp [hf, hta, hts]
  · intro e hne
    simp [hf, hp, sramUpd_of_ne _ _ _ _ hne]

/-- 次 miss 合并（:186-188）：不写 blockAddr 表（不新占 entry）、targetInfo 记入
    匹配 entry 的（rsp 行给出的）subentry 槽；除 rsp 释放行外 entryValid 不变。 -/
theorem icMshr_secondary_merge (hf : icMshrReqFire s i = true) (hs : icSecondary s i = true)
    (hsep : icMatchIdx s i ≠ icRspSel s i) :
    (∀ e, (icMshrStep s i).blockAddr e = s.blockAddr e) ∧
    (icMshrStep s i).subValid (icMatchIdx s i) (icSelNext s i) = true ∧
    (icMshrStep s i).targetInfo (icMatchIdx s i) (icSelNext s i) = i.reqTI ∧
    (∀ e, e ≠ icRspSel s i → icEntryValid (icMshrStep s i) e = icEntryValid s e) := by
  have hta : icTAEntry s i = icMatchIdx s i := by simp [icTAEntry, hs]
  have hts : icTASub s i = icSelNext s i := by simp [icTASub, hs]
  have hmv : icMatchVec s i.reqBA (icMatchIdx s i) = true :=
    icIdxOf4_spec _ (by simpa [icSecondary] using hs)
  have hev : icEntryValid s (icMatchIdx s i) = true := by
    simp only [icMatchVec, Bool.and_eq_true] at hmv; exact hmv.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e; simp [hf, hs]
  · simp [hf, hs]
  · simp [hf, hta, hts]
  · intro e hne
    by_cases hem : e = icMatchIdx s i
    · -- e = 匹配行：set 分支把 selNext 槽置 1，但该行本来就有效（hev）
      subst hem
      have hset : (icMshrStep s i).subValid (icMatchIdx s i) (icSelNext s i) = true := by
        simp [hf, hs]
      have hLHS : icEntryValid (icMshrStep s i) (icMatchIdx s i) = true := by
        have h2 : icAny4 ((icMshrStep s i).subValid (icMatchIdx s i)) = true := by
          rw [icAny4_eq_true]; exact ⟨icSelNext s i, hset⟩
        simpa only [icEntryValid, icAny4] using h2
      rw [hLHS, hev]
    · -- e 既非 rsp 释放行也非匹配行：三个分支都不命中，逐位不变
      have hbits : ∀ se, (icMshrStep s i).subValid e se = s.subValid e se := by
        intro se
        have hb1 : (e == icEntryNext s && se == 0 && !icSecondary s i) = false := by
          simp [hs]
        have hb2 : (e == icMatchIdx s i && se == icSelNext s i && icSecondary s i) = false := by
          simp [icBeq4_ne hem]
        have hb3 : (icRspOutFire s i && e == icRspSel s i && se == icNext2Cancel s i) = false := by
          simp [icBeq4_ne hne]
        rw [icMshrStep_subValid, if_pos hf, if_neg (by simp [hb1]), if_neg (by simp [hb2]),
          if_neg (by simp [hb3])]
      simp [icEntryValid, hbits]

/-- 主分配成立时 entryNext 必为无效行（reqReady ⇒ ¬entryFull）。 -/
theorem icEntryNext_invalid (hreq : icMshrReqFire s i = true) (hsec : icSecondary s i = false) :
    icEntryValid s (icEntryNext s) = false := by
  have hready : icMshrReqReady s i = true := by
    simp [icMshrReqFire] at hreq; exact hreq.2
  have hnotfull : icEntryFull s = false := by
    have h2 := hready
    simp [icMshrReqReady, hsec] at h2
    exact h2.1
  have hex : icAny4 (fun e => !icEntryValid s e) = true := by
    cases h0 : icEntryValid s 0 <;> cases h1 : icEntryValid s 1 <;>
      cases h2 : icEntryValid s 2 <;> cases h3 : icEntryValid s 3 <;>
      simp_all [icAny4, icEntryFull, icAll4]
  have h := icIdxOf4_spec _ hex
  simpa [icEntryNext] using h

/-- 次分配成立时 matchIdx ≠ rspSel 行（否则同块冲突使 reqReady=0）。 -/
theorem icMatchIdx_ne_rspSel_of_secondary
    (hreq : icMshrReqFire s i = true) (hsec : icSecondary s i = true)
    (hfire : icRspInFire s i = true) :
    i.rspIdx ≠ icMatchIdx s i := by
  intro hh
  have hmv : icMatchVec s i.reqBA (icMatchIdx s i) = true :=
    icIdxOf4_spec _ (by simpa [icSecondary] using hsec)
  have hba : s.blockAddr (icMatchIdx s i) = i.reqBA := by
    simp only [icMatchVec, Bool.and_eq_true, beq_iff_eq] at hmv; exact hmv.1
  have hrvq : i.reqValid = true := by simp [icMshrReqFire] at hreq; exact hreq.1
  have hconf : icConflict s i = true := by
    simp [icConflict, hrvq, hfire, icRspInBA, hh, hba]
  have hnr := icMshr_conflict_block hconf
  simp [icMshrReqFire, hnr] at hreq

/-- 响应到达（:172-176, :194-197）：rspOut 当拍有效、blockAddr 正确、
    目标 subentry 被清。`hvalid` 是环境假设（对应 ICacheMSHR.scala:163 的
    assert：响应只指向已分配 entry）。 -/
theorem icMshr_rsp_fire (hrv : i.rspValid = true) (hb : s.busy = false)
    (hvalid : icEntryValid s i.rspIdx = true) :
    icRspOutValid s i = true ∧
    icRspOutBA s i = s.blockAddr i.rspIdx ∧
    (icMshrStep s i).subValid i.rspIdx (icNext2Cancel s i) = false := by
  have hsel : icRspSel s i = i.rspIdx := by simp [icRspSel, hb]
  have hfire : icRspInFire s i = true := by simp [icRspInFire, hrv, hb]
  have hof : icRspOutFire s i = true := by simp [icRspOutFire, hfire]
  refine ⟨?_, ?_, ?_⟩
  · simp [icRspOutValid, hof]
  · simp [icRspOutBA, hsel]
  · rw [icMshrStep_subValid]
    by_cases hreq : icMshrReqFire s i = true
    · rw [if_pos hreq]
      have hb3 : (icRspOutFire s i && i.rspIdx == icRspSel s i &&
          icNext2Cancel s i == icNext2Cancel s i) = true := by
        simp [hof, hsel]
      by_cases hsec : icSecondary s i = true
      · have hne : i.rspIdx ≠ icMatchIdx s i :=
          icMatchIdx_ne_rspSel_of_secondary hreq hsec hfire
        have hb1 : (i.rspIdx == icEntryNext s && icNext2Cancel s i == 0 &&
            !icSecondary s i) = false := by
          simp [hsec]
        have hb2 : (i.rspIdx == icMatchIdx s i && icNext2Cancel s i == icSelNext s i &&
            icSecondary s i) = false := by
          simp [icBeq4_ne hne]
        rw [if_neg (by simp [hb1]), if_neg (by simp [hb2]), if_pos hb3]
      · have hsec' : icSecondary s i = false := by simpa using hsec
        have hne : i.rspIdx ≠ icEntryNext s := by
          intro hh
          have hinval := icEntryNext_invalid hreq hsec'
          rw [hh, hinval] at hvalid; exact Bool.noConfusion hvalid
        have hb1 : (i.rspIdx == icEntryNext s && icNext2Cancel s i == 0 &&
            !icSecondary s i) = false := by
          simp [icBeq4_ne hne]
        have hb2 : (i.rspIdx == icMatchIdx s i && icNext2Cancel s i == icSelNext s i &&
            icSecondary s i) = false := by
          simp [hsec']
        rw [if_neg (by simp [hb1]), if_neg (by simp [hb2]), if_pos hb3]
    · rw [if_neg hreq]
      have hb3 : (icRspOutFire s i && i.rspIdx == icRspSel s i &&
          icNext2Cancel s i == icNext2Cancel s i) = true := by
        simp [hof, hsel]
      rw [if_pos hb3]

/-- subValid' 单比特来源分类（供 entryValid 级推理）。 -/
theorem icMshr_subValid'_cases (e se : Fin 4)
    (hv : (icMshrStep s i).subValid e se = true) :
    s.subValid e se = true ∨
      (icMshrReqFire s i = true ∧ icSecondary s i = false ∧ e = icEntryNext s) ∨
      (icMshrReqFire s i = true ∧ icSecondary s i = true ∧ e = icMatchIdx s i) := by
  rw [icMshrStep_subValid] at hv
  by_cases hreq : icMshrReqFire s i = true
  · rw [if_pos hreq] at hv
    by_cases b1 : (e == icEntryNext s && se == 0 && !icSecondary s i) = true
    · rw [if_pos b1] at hv
      right; left
      simp only [Bool.and_eq_true] at b1
      obtain ⟨⟨he, _⟩, hsec⟩ := b1
      exact ⟨hreq, by simpa using hsec, beq_iff_eq.mp he⟩
    · rw [if_neg (by simpa using b1)] at hv
      by_cases b2 : (e == icMatchIdx s i && se == icSelNext s i && icSecondary s i) = true
      · rw [if_pos b2] at hv
        right; right
        simp only [Bool.and_eq_true] at b2
        obtain ⟨⟨he, _⟩, hsec⟩ := b2
        exact ⟨hreq, hsec, beq_iff_eq.mp he⟩
      · rw [if_neg (by simpa using b2)] at hv
        by_cases b3 : (icRspOutFire s i && e == icRspSel s i &&
            se == icNext2Cancel s i) = true
        · rw [if_pos b3] at hv; exact absurd hv (by decide)
        · rw [if_neg (by simpa using b3)] at hv; exact Or.inl hv
  · rw [if_neg (by simpa using hreq)] at hv
    by_cases b3 : (icRspOutFire s i && e == icRspSel s i &&
        se == icNext2Cancel s i) = true
    · rw [if_pos b3] at hv; exact absurd hv (by decide)
    · rw [if_neg (by simpa using b3)] at hv; exact Or.inl hv

/-- entryValid' 的来源分类：要么原本有效，要么是本拍主分配的新 entry。 -/
theorem icMshr_entryValid'_cases (e : Fin 4)
    (hv : icEntryValid (icMshrStep s i) e = true) :
    icEntryValid s e = true ∨
      (icMshrReqFire s i = true ∧ icSecondary s i = false ∧ e = icEntryNext s) := by
  have aux : ∀ se : Fin 4, (icMshrStep s i).subValid e se = true →
      icEntryValid s e = true ∨
        (icMshrReqFire s i = true ∧ icSecondary s i = false ∧ e = icEntryNext s) := by
    intro se hse
    rcases icMshr_subValid'_cases e se hse with h | h | h
    · left
      rcases icFin4_cases se with hs0 | hs0 | hs0 | hs0 <;> subst hs0 <;>
        simp_all [icEntryValid]
    · exact Or.inr h
    · left
      have hmv : icMatchVec s i.reqBA (icMatchIdx s i) = true :=
        icIdxOf4_spec _ (by simpa [icSecondary] using h.2.1)
      have hev : icEntryValid s (icMatchIdx s i) = true := by
        simp only [icMatchVec, Bool.and_eq_true] at hmv; exact hmv.2
      rwa [h.2.2]
  have hv2 : ((icMshrStep s i).subValid e 0 || (icMshrStep s i).subValid e 1 ||
      (icMshrStep s i).subValid e 2 || (icMshrStep s i).subValid e 3) = true := hv
  -- `||` 左结合，simp 得左嵌套 Or；逐层拆
  have hv3 : (((icMshrStep s i).subValid e 0 = true ∨ (icMshrStep s i).subValid e 1 = true) ∨
      (icMshrStep s i).subValid e 2 = true) ∨ (icMshrStep s i).subValid e 3 = true := by
    simpa only [Bool.or_eq_true] using hv2
  rcases hv3 with hv3 | h
  · rcases hv3 with hv3 | h2
    · rcases hv3 with h | h1
      · exact aux 0 h
      · exact aux 1 h1
    · exact aux 2 h2
  · exact aux 3 h

/-- 原本有效的 entry，其 blockAddr 不被本拍改写（主分配只写无效行）。 -/
theorem icMshr_blockAddr'_old (e : Fin 4) (hev : icEntryValid s e = true) :
    (icMshrStep s i).blockAddr e = s.blockAddr e := by
  by_cases hf : icMshrReqFire s i = true ∧ icSecondary s i = false
  · have hne : e ≠ icEntryNext s := by
      intro hh; subst hh
      have hinval := icEntryNext_invalid hf.1 hf.2
      rw [hinval] at hev; exact Bool.noConfusion hev
    simp [hf.1, hf.2, sramUpd_of_ne _ _ _ _ hne]
  · by_cases hc : (icMshrReqFire s i && !icSecondary s i) = true
    · simp only [Bool.and_eq_true] at hc
      have hc2 : icSecondary s i = false := by simpa using hc.2
      exact absurd ⟨hc.1, hc2⟩ hf
    · simp [hc]

/-- 同块唯一性不变式（ICacheMSHR.scala:125 的 assert PopCount ≤ 1 的不变式形式）：
    任意两个有效 entry 的 blockAddr 不同。 -/
def icMshrInv (s : IcMshrState) : Prop :=
  ∀ e1 e2 : Fin 4, icEntryValid s e1 = true → icEntryValid s e2 = true →
    s.blockAddr e1 = s.blockAddr e2 → e1 = e2

theorem icMshrInit_inv : icMshrInv icMshrInit := by
  intro e1 e2 h1 _ _
  simp [icEntryValid] at h1

/-- 不变式保持：主分配只发生在无匹配（primary）时，故新块不会与旧块重复。 -/
theorem icMshrStep_inv (h : icMshrInv s) : icMshrInv (icMshrStep s i) := by
  intro e1 e2 h1 h2 hba
  rcases icMshr_entryValid'_cases e1 h1 with o1 | n1
  · rcases icMshr_entryValid'_cases e2 h2 with o2 | n2
    · rw [icMshr_blockAddr'_old e1 o1, icMshr_blockAddr'_old e2 o2] at hba
      exact h e1 e2 o1 o2 hba
    · exfalso
      rw [icMshr_blockAddr'_old e1 o1, n2.2.2, (icMshr_primary_alloc n2.1 n2.2.1).1] at hba
      have hsec : icSecondary s i = true := by
        simp only [icSecondary, icAny4_eq_true]
        exact ⟨e1, by simp [icMatchVec, hba, o1]⟩
      rw [hsec] at n2; exact Bool.noConfusion n2.2.1
  · rcases icMshr_entryValid'_cases e2 h2 with o2 | n2
    · exfalso
      rw [icMshr_blockAddr'_old e2 o2, n1.2.2, (icMshr_primary_alloc n1.1 n1.2.1).1] at hba
      have hsec : icSecondary s i = true := by
        simp only [icSecondary, icAny4_eq_true]
        exact ⟨e2, by simp [icMatchVec, ← hba, o2]⟩
      rw [hsec] at n1; exact Bool.noConfusion n1.2.1
    · rw [n1.2.2, n2.2.2]

/-- 不丢：missReq.fire ⇒ （blockAddr, targetInfo）确已入表。 -/
theorem icMshr_no_loss (hf : icMshrReqFire s i = true) :
    ∃ e se, (icMshrStep s i).subValid e se = true ∧
      (icMshrStep s i).blockAddr e = i.reqBA ∧
      (icMshrStep s i).targetInfo e se = i.reqTI := by
  by_cases hsec : icSecondary s i
  · have hmv : icMatchVec s i.reqBA (icMatchIdx s i) = true :=
      icIdxOf4_spec _ (by simpa [icSecondary] using hsec)
    have hba : s.blockAddr (icMatchIdx s i) = i.reqBA := by
      simp only [icMatchVec, Bool.and_eq_true, beq_iff_eq] at hmv; exact hmv.1
    have hta : icTAEntry s i = icMatchIdx s i := by simp [icTAEntry, hsec]
    have hts : icTASub s i = icSelNext s i := by simp [icTASub, hsec]
    refine ⟨icMatchIdx s i, icSelNext s i, ?_, ?_, ?_⟩
    · simp [hf, hsec]
    · simp [hf, hsec, hba]
    · simp [hf, hta, hts]
  · have hsec' : icSecondary s i = false := by simpa using hsec
    have h := icMshr_primary_alloc hf hsec'
    exact ⟨icEntryNext s, 0, h.2.1, h.1, h.2.2.1⟩

/-- 不重（访存级）：miss2mem.fire 后该 entry 标记已发送（:215-216）。 -/
theorem icMshr_miss2mem_once (hf : icMemFire s i = true) :
    (icMshrStep s i).hasSend (icMemNext s) = true := by
  simp [hf]

/-- hasSend 粘性：非"该 entry 最后一个 subentry 被响应释放"时保持
    （:217-219 的 elsewhen）。 -/
theorem icMshr_hasSend_sticky (e : Fin 4)
    (hnc : ¬((s.busy || icRspInFire s i) = true ∧ icRspOutFire s i = true ∧
        icSelUsed s i = 1 ∧ e = icRspSel s i))
    (hold : s.hasSend e = true) : (icMshrStep s i).hasSend e = true := by
  rw [icMshrStep_hasSend]
  by_cases b1 : (icMemFire s i && e == icMemNext s) = true
  · simp [b1]
  · by_cases b2 : ((s.busy || icRspInFire s i) && icRspOutFire s i &&
        icSelUsed s i == 1 && e == icRspSel s i) = true
    · simp only [Bool.and_eq_true] at b2
      obtain ⟨⟨⟨hbz, hof⟩, hu⟩, he⟩ := b2
      exact absurd ⟨hbz, hof, beq_iff_eq.mp hu, beq_iff_eq.mp he⟩ hnc
    · simp [b1, b2, hold]

/-- 最后 subentry 释放（:166-170, :194-197, :217-219 联立）：used=1 的响应
    使 entry 无效、hasSend 清除、busy 不升起。hsent 对应"响应只回已发出的
    entry"（memReq→memRsp 因果，D8）。 -/
theorem icMshr_rsp_last_frees (hrv : i.rspValid = true) (hb : s.busy = false)
    (hused : icSelUsed s i = 1) (hsent : s.hasSend i.rspIdx = true)
    (hvalid : icEntryValid s i.rspIdx = true) :
    icEntryValid (icMshrStep s i) i.rspIdx = false ∧
    (icMshrStep s i).hasSend i.rspIdx = false ∧
    (icMshrStep s i).busy = false := by
  have hsel : icRspSel s i = i.rspIdx := by simp [icRspSel, hb]
  have hfire : icRspInFire s i = true := by simp [icRspInFire, hrv, hb]
  have hof : icRspOutFire s i = true := by simp [icRspOutFire, hfire]
  have hrow : icAny4 (s.subValid i.rspIdx) = true := by
    rw [icAny4_eq_true]
    by_cases h0 : s.subValid i.rspIdx 0 = true
    · exact ⟨0, h0⟩
    · by_cases h1 : s.subValid i.rspIdx 1 = true
      · exact ⟨1, h1⟩
      · by_cases h2 : s.subValid i.rspIdx 2 = true
        · exact ⟨2, h2⟩
        · by_cases h3 : s.subValid i.rspIdx 3 = true
          · exact ⟨3, h3⟩
          · exfalso
            simp only [Bool.not_eq_true] at h0 h1 h2 h3
            have hv : icEntryValid s i.rspIdx = false := by
              simp [icEntryValid, h0, h1, h2, h3]
            rw [hv] at hvalid; exact Bool.noConfusion hvalid
  have hcan : s.subValid i.rspIdx (icNext2Cancel s i) = true := by
    have h := icIdxOf4_spec _ hrow
    simpa [icNext2Cancel, hsel] using h
  -- busy 不升起
  have hbusy : (icMshrStep s i).busy = false := by
    simp only [icMshrStep]
    have h1 : (icRspInFire s i && !(icSelUsed s i == 1)) = false := by
      simp [hused]
    simp [h1, hb]
  -- hasSend 清除：memFire 分支不会命中 rspIdx（memNext 要求 !hasSend）
  have hsend : (icMshrStep s i).hasSend i.rspIdx = false := by
    rw [icMshrStep_hasSend]
    have hclr : ((s.busy || icRspInFire s i) && icRspOutFire s i &&
        icSelUsed s i == 1 && i.rspIdx == icRspSel s i) = true := by
      simp [hb, hfire, hof, hused, hsel]
    by_cases b1 : (icMemFire s i && i.rspIdx == icMemNext s) = true
    · simp only [Bool.and_eq_true] at b1
      have hmv : icMemValid s = true := by
        have h1 := b1.1
        simp only [icMemFire, Bool.and_eq_true] at h1
        exact h1.1
      have hns : s.hasSend (icMemNext s) = false := by
        have h1 := hmv
        simp only [icMemValid, Bool.and_eq_true] at h1
        cases hb2 : s.hasSend (icMemNext s)
        · rfl
        · simp [hb2] at h1
      have heq : i.rspIdx = icMemNext s := beq_iff_eq.mp b1.2
      rw [← heq, hsent] at hns
      exact Bool.noConfusion hns
    · simp [b1, hclr]
  -- entryValid' rspIdx = false：next2cancel 被清，其余位本就为 0（used=1）
  have hval : icEntryValid (icMshrStep s i) i.rspIdx = false := by
    have hothers : ∀ se, se ≠ icNext2Cancel s i →
        s.subValid i.rspIdx se = false := by
      intro se hse
      have hc : icCount4 (s.subValid i.rspIdx) = 1 := by
        simpa [icSelUsed, hsel] using hused
      exact icCount4_eq_one_unique _ _ _ hc hcan hse
    have hclr2 := (icMshr_rsp_fire hrv hb hvalid).2.2
    have hall : ∀ se : Fin 4, (icMshrStep s i).subValid i.rspIdx se = false := by
      intro se
      by_cases hse : se = icNext2Cancel s i
      · rw [hse]; exact hclr2
      · have horig := hothers se hse
        have hse2 : (se == icNext2Cancel s i) = false := icBeq4_ne hse
        rw [icMshrStep_subValid]
        have hb3 : (icRspOutFire s i && i.rspIdx == icRspSel s i &&
            se == icNext2Cancel s i) = false := by
          simp [hse2]
        by_cases hreq : icMshrReqFire s i = true
        · rw [if_pos hreq]
          by_cases hsec : icSecondary s i = true
          · have hne : i.rspIdx ≠ icMatchIdx s i :=
              icMatchIdx_ne_rspSel_of_secondary hreq hsec hfire
            have hb1 : (i.rspIdx == icEntryNext s && se == 0 && !icSecondary s i) = false := by
              simp [hsec]
            have hb2 : (i.rspIdx == icMatchIdx s i && se == icSelNext s i &&
                icSecondary s i) = false := by
              simp [icBeq4_ne hne]
            rw [if_neg (by simp [hb1]), if_neg (by simp [hb2]), if_neg (by simp [hb3])]
            exact horig
          · have hsec' : icSecondary s i = false := by simpa using hsec
            have hne : i.rspIdx ≠ icEntryNext s := by
              intro hh
              have hinval := icEntryNext_invalid hreq hsec'
              rw [hh, hinval] at hvalid
              exact Bool.noConfusion hvalid
            have hb1 : (i.rspIdx == icEntryNext s && se == 0 && !icSecondary s i) = false := by
              simp [icBeq4_ne hne]
            have hb2 : (i.rspIdx == icMatchIdx s i && se == icSelNext s i &&
                icSecondary s i) = false := by
              simp [hsec']
            rw [if_neg (by simp [hb1]), if_neg (by simp [hb2]), if_neg (by simp [hb3])]
            exact horig
        · rw [if_neg hreq, if_neg (by simp [hb3])]
          exact horig
    simp [icEntryValid, hall 0, hall 1, hall 2, hall 3]
  exact ⟨hval, hsend, hbusy⟩

end IcMshrThms

/- ========================================================================= -/
/- 4. memRsp_Q：Queue(ICacheMemRsp, 2, pipe=true)（ICache.scala:99, D4）       -/
/- ========================================================================= -/

/-- ICacheMemRsp（ICache.scala:48-52）：d_addr 无消费者（D7），省略。 -/
structure IcMemRsp where
  dSource : BitVec 5     -- WIdBits+log2Up(NMshrEntry) = 3+2
  dData : BitVec 1024    -- BlockWords 个 32 位字 asUInt
deriving DecidableEq

/-- 2 深指针 FIFO（chisel3.util.Queue 寄存器实现）：enqPtr/deqPtr/maybeFull。
    D11：mem 原为 `Fin 2 → IcMemRsp` 函数字段（enq 时套闭包），Array 化；
    `q.mem p` 写法由同名访问器保持。 -/
structure IcRspQ where
  memArr : Array IcMemRsp
  enqP : Fin 2
  deqP : Fin 2
  full : Bool

/-- 队列存储访问器（D11）：保持原 `q.mem p` 语义，Array + getD。 -/
def IcRspQ.mem (q : IcRspQ) (p : Fin 2) : IcMemRsp := q.memArr.getD p.val ⟨0, 0⟩

def icRspQInit : IcRspQ := ⟨Array.replicate 2 ⟨0, 0⟩, 0, 0, false⟩

def icQEmpty (q : IcRspQ) : Bool := (q.enqP == q.deqP) && !q.full
/-- full = 指针相遇且 maybe_full（chisel Queue 的 ptr_match && maybe_full）。 -/
def icQFull (q : IcRspQ) : Bool := (q.enqP == q.deqP) && q.full
/-- enq.ready = !full（flow=false）。 -/
def icQEnqReady (q : IcRspQ) : Bool := !icQFull q
/-- deq.valid：pipe=true，空时组合旁路 enq.valid。 -/
def icQDeqValid (q : IcRspQ) (enqV : Bool) : Bool := if icQEmpty q then enqV else true
/-- deq.bits：空时旁路 enq.bits。 -/
def icQDeqBits (q : IcRspQ) (enqB : IcMemRsp) : IcMemRsp :=
  if icQEmpty q then enqB else q.mem q.deqP

/-- 单拍：do_enq/do_deq（pipe 的"空且即取"抑制入队）。 -/
def icQStep (q : IcRspQ) (enqV : Bool) (enqB : IcMemRsp) (deqRdy : Bool) : IcRspQ where
  memArr := if enqV && icQEnqReady q && !(icQEmpty q && deqRdy) then
      q.memArr.setIfInBounds q.enqP.val enqB else q.memArr
  enqP := if enqV && icQEnqReady q && !(icQEmpty q && deqRdy) then q.enqP + 1 else q.enqP
  deqP := if icQDeqValid q enqV && deqRdy && !icQEmpty q then q.deqP + 1 else q.deqP
  full :=
    let doEnq := enqV && icQEnqReady q && !(icQEmpty q && deqRdy)
    let doDeq := icQDeqValid q enqV && deqRdy && !icQEmpty q
    if doEnq == doDeq then q.full else doEnq

/- ---- Queue 数值回归 ---- -/

theorem icT_q_bypass :  -- 空时 enq 同拍直通 deq，且不入队
    icQDeqValid icRspQInit true = true ∧
    icQDeqBits icRspQInit ⟨7#5, 42#1024⟩ = ⟨7#5, 42#1024⟩ ∧
    icQEmpty (icQStep icRspQInit true ⟨7#5, 42#1024⟩ true) = true := by
  native_decide

theorem icT_q_hold :  -- deq 不 ready 时入队保持，下一拍可取
    let q1 := icQStep icRspQInit true ⟨7#5, 42#1024⟩ false
    icQEmpty q1 = false ∧ icQDeqBits q1 ⟨0, 0⟩ = ⟨7#5, 42#1024⟩ ∧
    icQEmpty (icQStep q1 false ⟨0, 0⟩ true) = true := by
  native_decide

theorem icT_q_fifo :  -- 两个元素先进先出
    let q1 := icQStep icRspQInit true ⟨1#5, 11#1024⟩ false
    let q2 := icQStep q1 true ⟨2#5, 22#1024⟩ false
    let q3 := icQStep q2 false ⟨0, 0⟩ true
    icQDeqBits q2 ⟨0, 0⟩ = ⟨1#5, 11#1024⟩ ∧ icQDeqBits q3 ⟨0, 0⟩ = ⟨2#5, 22#1024⟩ ∧
    icQEnqReady q2 = false := by
  native_decide

/- ========================================================================= -/
/- 5. L1TagAccess_ICache（L1TagAccess.scala:432-509 + tagChecker :380-410 +    -/
/-    ReplacementUnit_ICache :510-522）                                        -/
/- ========================================================================= -/

/-- Tag 访问状态：tag SRAM（sramCfgICacheTag：holdRead，无旁路）+ way_valid
    寄存器阵列（:464）+ victim 轮转独热（:516）。
    D11：wayValid 原为 `Fin 256 → BitVec 2` 函数字段——refill 写的更新体
    `old(wSet) ||| icVictimMask t wSet` 对旧链**回读两次**（icVictimMask 内部
    再读一次 wayValid），跨 refill 形成 ×2/层的扇出（第 20 波实测：probe 打到
    被 refill 的 set 时每拍成本 ~×1.18/拍，n=100 拍 38s）。Array 化 + 同名
    访问器；icTagStep 写分支用 `Array.ofFn` 逐点物化（输出尺寸恒 256）。 -/
structure IcTagState where
  sram : SramState 256 2 17
  wayValidArr : Array (BitVec 2)
  victim : BitVec 2

/-- way_valid 访问器（D11）：保持原 `t.wayValid v` 语义，Array + getD。 -/
def IcTagState.wayValid (t : IcTagState) (v : Fin 256) : BitVec 2 :=
  t.wayValidArr.getD v.val 0#2

def icTagInit : IcTagState := ⟨sramInit 256 2 17, Array.replicate 256 0#2, 1#2⟩

/-- 初态 wayValid（:464 RegInit 全 0）。 -/
@[simp] theorem icTagInit_wayValid (v : Fin 256) : icTagInit.wayValid v = 0#2 := by
  simp [IcTagState.wayValid, icTagInit, Array.getD_eq_getD_getElem?]

/-- ReplacementUnit_ICache.waymask（:517-518）。
    **注意**：输入 validbits_of_set = Cat(way_valid(...))（:496，无 Reverse——
    对照 DCache 版 :297 有 Reverse），故 validbits(0)=way1、validbits(1)=way0，
    indexWhere 从 bit0 起扫：v=0b01（way0 占用、way1 空闲）时仍选 way0（Q2）。 -/
def icVictimMask (t : IcTagState) (v : Fin 256) : BitVec 2 :=
  if t.wayValid v = 0b11#2 then t.victim
  else if (t.wayValid v).getLsbD 1 = false then 0b01#2 else 0b10#2

/-- Set_is_full（:517）。 -/
def icSetFull (t : IcTagState) (v : Fin 256) : Bool := t.wayValid v == 0b11#2

/-- victim 轮转（:521）：way=2 时 Cat(victim(0), victim(1)) = 循环左移 1 位。 -/
def icRot2 (v : BitVec 2) : BitVec 2 := (v <<< 1) ||| (v >>> 1)

/-- 单拍转移（:460-462, :498-507, :521）。
    rV/wV 为 ICache 侧 valid（未含 invalidate 门控），内部再按 :461/:498 门控。 -/
def icTagStep (t : IcTagState) (rV : Bool) (rSet : Fin 256)
    (wV : Bool) (wSet : Fin 256) (wTag : BitVec 17) (inv : Bool) : IcTagState where
  sram := sramStep sramCfgICacheTag t.sram
    { rValid := rV && !inv, rAddr := rSet,
      wValid := wV && !inv, wAddr := wSet,
      wData := fun _ => wTag, wMask := icVictimMask t wSet }
  wayValidArr :=
    if inv then Array.replicate 256 0#2
    else if wV && !icSetFull t wSet then
      Array.ofFn fun v => if v == wSet then t.wayValid wSet ||| icVictimMask t wSet else t.wayValid v
    else t.wayValidArr
  victim := if icSetFull t wSet then icRot2 t.victim else t.victim

/-- 单 way 命中判定（tagChecker :403：tag 比较 && valid）。 -/
def icWayMatch (t : IcTagState) (tag : BitVec 17) (v : Fin 256) (j : Fin 2) : Bool :=
  (sramRespData sramCfgICacheTag t.sram j == tag) && ((t.wayValid v >>> j.val) &&& 1#2 == 1#2)

/-- waymaskHit_st1（:493，tagChecker 的 Reverse(Cat(...))：bit j = way j）。 -/
def icWaymaskHit (t : IcTagState) (tag : BitVec 17) (v : Fin 256) : BitVec 2 :=
  (if icWayMatch t tag v 1 then 2#2 else 0#2) ||| (if icWayMatch t tag v 0 then 1#2 else 0#2)

/-- hit_st1（:494, :409）。 -/
def icTagHit (t : IcTagState) (tag : BitVec 17) (v : Fin 256) : Bool :=
  icWaymaskHit t tag v != 0#2

/- ---- Tag 访问定理 ---- -/

/-- waymaskHit 的逐位规约（命中判定正确性的基础）。 -/
theorem icWaymaskHit_eq (t : IcTagState) (tag : BitVec 17) (v : Fin 256) :
    icWaymaskHit t tag v =
      (if icWayMatch t tag v 1 then 2#2 else 0#2) |||
      (if icWayMatch t tag v 0 then 1#2 else 0#2) := rfl

/-- hit ↔ 存在某 way：tag 匹配且 valid。 -/
theorem icTagHit_iff (t : IcTagState) (tag : BitVec 17) (v : Fin 256) :
    icTagHit t tag v = true ↔ ∃ j : Fin 2, icWayMatch t tag v j = true := by
  constructor
  · intro h
    by_cases h0 : icWayMatch t tag v 0 = true
    · exact ⟨0, h0⟩
    · by_cases h1 : icWayMatch t tag v 1 = true
      · exact ⟨1, h1⟩
      · exfalso
        simp only [Bool.not_eq_true] at h0 h1
        simp [icTagHit, icWaymaskHit, h0, h1] at h
  · intro ⟨j, hj⟩
    rcases icFin2_cases j with h | h
    · subst h
      simp only [icTagHit, bne_iff_ne, icWaymaskHit]
      cases h1 : icWayMatch t tag v 1 <;> simp [hj]
    · subst h
      simp only [icTagHit, bne_iff_ne, icWaymaskHit]
      cases h0 : icWayMatch t tag v 0 <;> simp [hj]

/-- one-hot 命中时 OHToUInt 取到该 way（数据选择正确性）。 -/
theorem icHitWayIdx_of_onehot (wm : BitVec 2) (j : Fin 2)
    (h : wm = BitVec.ofNat 2 (1 <<< j.val)) : icOHToUInt2 wm = j := by
  rw [h]; exact icOHToUInt2_onehot j

/-- victim 选择：空 set（00）选 way0 —— 正确。 -/
theorem icVictimMask_empty (t : IcTagState) (v : Fin 256) (h : t.wayValid v = 0#2) :
    icVictimMask t v = 1#2 := by
  simp [icVictimMask, h]

/-- victim 选择：满 set 取轮转 victim —— 正确。 -/
theorem icVictimMask_full (t : IcTagState) (v : Fin 256) (h : t.wayValid v = 0b11#2) :
    icVictimMask t v = t.victim := by
  simp [icVictimMask, h]

/-- **Q2 钉死**：way0 占用、way1 空闲（v=0b01）时，victim 仍选中已占用的
    way0（应为 way1=0b10）——缺 Reverse 的直接后果。 -/
theorem icVictimMask_way0_valid_only (t : IcTagState) (v : Fin 256) (h : t.wayValid v = 0b01#2) :
    icVictimMask t v = 0b01#2 := by
  simp [icVictimMask, h]

/-- refill 后 way_valid 置位（:505-506）。 -/
theorem icTagStep_wayValid_refill (t : IcTagState) (rV : Bool) (rSet wSet : Fin 256)
    (wTag : BitVec 17) (hnotfull : icSetFull t wSet = false) :
    (icTagStep t rV rSet true wSet wTag false).wayValid wSet =
      t.wayValid wSet ||| icVictimMask t wSet := by
  simp [icTagStep, IcTagState.wayValid, hnotfull]

/-- wayValid 转移（invalidate 分支，:503-504）。 -/
theorem icTagStep_wayValid_of_inv (t : IcTagState) (rV : Bool) (rSet wSet : Fin 256)
    (wTag : BitVec 17) (wV : Bool) (v : Fin 256) :
    (icTagStep t rV rSet wV wSet wTag true).wayValid v = 0#2 := by
  simp [icTagStep, IcTagState.wayValid]

/-- wayValid 转移（refill 写分支，:505-506，D11 逐点形式）。 -/
theorem icTagStep_wayValid_of_wr (t : IcTagState) (rV : Bool) (rSet wSet : Fin 256)
    (wTag : BitVec 17) (inv : Bool) (wV : Bool) (hinv : inv = false)
    (hw : (wV && !icSetFull t wSet) = true) (v : Fin 256) :
    (icTagStep t rV rSet wV wSet wTag inv).wayValid v =
      (if v == wSet then t.wayValid wSet ||| icVictimMask t wSet else t.wayValid v) := by
  simp [icTagStep, IcTagState.wayValid, hinv, hw]

/-- wayValid 转移（保持分支）。 -/
theorem icTagStep_wayValid_of_keep (t : IcTagState) (rV : Bool) (rSet wSet : Fin 256)
    (wTag : BitVec 17) (inv : Bool) (wV : Bool) (hinv : inv = false)
    (hw : (wV && !icSetFull t wSet) = false) (v : Fin 256) :
    (icTagStep t rV rSet wV wSet wTag inv).wayValid v = t.wayValid v := by
  simp [icTagStep, IcTagState.wayValid, hinv, hw]

/-- invalidate 清空全部 valid（:503-504）。 -/
theorem icTagStep_invalidate (t : IcTagState) (rV : Bool) (rSet wSet : Fin 256)
    (wTag : BitVec 17) (wV : Bool) :
    (icTagStep t rV rSet wV wSet wTag true).wayValid = fun _ => 0#2 := by
  funext v; exact icTagStep_wayValid_of_inv _ _ _ _ _ _ _

/-- Q2 推论（容量退化不变式）：way1 恒无效、victim 恒 0b01。 -/
def icTagInv (t : IcTagState) : Prop :=
  (∀ v, t.wayValid v = 0#2 ∨ t.wayValid v = 1#2) ∧ t.victim = 1#2

theorem icTagInit_inv : icTagInv icTagInit := by
  refine ⟨fun v => Or.inl (icTagInit_wayValid v), rfl⟩

theorem icTagStep_preserves_inv (t : IcTagState) (rV : Bool) (rSet : Fin 256)
    (wV : Bool) (wSet : Fin 256) (wTag : BitVec 17) (inv : Bool) (h : icTagInv t) :
    icTagInv (icTagStep t rV rSet wV wSet wTag inv) := by
  obtain ⟨hv, hvc⟩ := h
  have hmask : ∀ v, icVictimMask t v = 1#2 := by
    intro v
    rcases hv v with h0 | h1
    · simp [icVictimMask, h0]
    · simp [icVictimMask, h1]
  have hnofull : ∀ v, icSetFull t v = false := by
    intro v
    rcases hv v with h0 | h1
    · simp [icSetFull, h0]
    · simp [icSetFull, h1]
  constructor
  · intro v
    by_cases hinv : inv
    · left
      have hinv' : inv = true := hinv
      subst hinv'
      exact icTagStep_wayValid_of_inv _ _ _ _ _ _ _
    · have hinv' : inv = false := by simpa using hinv
      by_cases hw : (wV && !icSetFull t wSet) = true
      · by_cases hv' : v = wSet
        · subst v
          rcases hv wSet with h0 | h1
          · right; rw [icTagStep_wayValid_of_wr _ _ _ _ _ _ _ hinv' hw]; simp [hmask, h0]
          · right; rw [icTagStep_wayValid_of_wr _ _ _ _ _ _ _ hinv' hw]; simp [hmask, h1]
        · rcases hv v with h0 | h1
          · left; rw [icTagStep_wayValid_of_wr _ _ _ _ _ _ _ hinv' hw]; simp [beq_iff_eq, hv', h0]
          · right; rw [icTagStep_wayValid_of_wr _ _ _ _ _ _ _ hinv' hw]; simp [beq_iff_eq, hv', h1]
      · have hw' : (wV && !icSetFull t wSet) = false := by simpa using hw
        rcases hv v with h0 | h1
        · left; rw [icTagStep_wayValid_of_keep _ _ _ _ _ _ _ hinv' hw']; exact h0
        · right; rw [icTagStep_wayValid_of_keep _ _ _ _ _ _ _ hinv' hw']; exact h1
  · simp [icTagStep, hnofull, hvc]

/- ========================================================================= -/
/- 6. InstructionCache 顶层（ICache.scala:79-277）                             -/
/- ========================================================================= -/

/-- ICache 每拍输入。coreReq.ready ≡ true（:262），故请求侧只需 valid+bits；
    memReq.ready 由下游给；memRsp 进入 memRsp_Q（enq.ready = !full）。 -/
structure IcIn where
  reqValid : Bool
  reqAddr : BitVec 32
  reqMask : BitVec 2
  reqWarp : BitVec 3
  flushValid : Bool
  flushWarp : BitVec 3
  rspValid : Bool
  rspBits : IcMemRsp
  memReady : Bool
  invalidate : Bool

def icInIdle : IcIn := ⟨false, 0, 0, 0, false, 0, false, ⟨0, 0⟩, true, false⟩

/-- ICache 状态：子模块 + 命中流水线寄存器（:107-125, :142, :196, :200,
    :217-220, :268-271）。 -/
structure IcState where
  tag : IcTagState
  dat : SramState 256 2 1024
  mshr : IcMshrState
  q : IcRspQ
  fire1 : Bool              -- coreReqFire_st1（:107）
  fire2 : Bool              -- coreReqFire_st2（:108）
  wid1 : BitVec 3           -- warpid_st1（:120，ready 门控 ≡ 每拍更新）
  wid2 : BitVec 3
  wid3 : BitVec 3           -- :269
  mask1 : BitVec 2          -- :121
  mask2 : BitVec 2
  addr1 : BitVec 32         -- :124
  addr2 : BitVec 32
  paddr1 : BitVec 32        -- pipeReqAddr_st1（:142，fire 门控）
  st1Set : Fin 256          -- way_valid 采样寄存器（L1TagAccess.scala:492，en=coreReqReady≡true）
  data2 : BitVec 64         -- data_after_blockOffset_st2（:196）
  flush0d : Bool            -- RegNext(ShouldFlushCoreRsp_st0)（:217）
  flush1d : Bool            -- RegNext(ShouldFlushCoreRsp_st1)（:220）
  statusD : BitVec 2        -- RegNext(Status_st1)（:220）
  ov2 : Bool                -- OrderViolation_st2（:200）
  ov3 : Bool                -- :268
  miss2 : Bool              -- cacheMiss_st2（:270）
  miss3 : Bool              -- :271

def icInit : IcState :=
  ⟨icTagInit, sramInit 256 2 1024, icMshrInit, icRspQInit,
   false, false, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, by decide⟩, 0, false, false, 0,
   false, false, false, false⟩

/-- ShouldFlushCoreRsp_st0（:140）。显式双参（不依赖 s，仅为统一调用形）。 -/
def icFlush0 (s : IcState) (i : IcIn) : Bool := i.flushValid && (i.reqWarp == i.flushWarp)
/-- ShouldFlushCoreRsp_st1（:139）。 -/
def icFlush1 (s : IcState) (i : IcIn) : Bool := i.flushValid && (s.wid1 == i.flushWarp)

section IcTopComb

variable (s : IcState) (i : IcIn)

/-- **io.coreReq.ready 恒 true**（:262）——probe 无反压，Q1 的结构性原因。 -/
def icCoreReqReady : Bool := true
def icCoreReqFire : Bool := i.reqValid && icCoreReqReady

/- ---- st1 信号（当前状态 s 所代表的拍） ---- -/

/-- waymaskHit_st1（:118 的输入，tagChecker 组合逻辑）。 -/
def icWaymaskHitSt1 : BitVec 2 := icWaymaskHit s.tag (icGetTag s.paddr1) s.st1Set
def icHitSt1 : Bool := icWaymaskHitSt1 s != 0#2
def icWayIdxHitSt1 : Fin 2 := icOHToUInt2 (icWaymaskHitSt1 s)          -- :118
/-- cacheHit_st1 / cacheMiss_st1（:114-115）。 -/
def icCacheHit1 : Bool := icHitSt1 s && s.fire1
def icCacheMiss1 : Bool := !icHitSt1 s && s.fire1

/-- st1 数据通路（:181-193）：way 选择 → blockOffset 移位 → 取低 64 位。 -/
def icDataSt1 : BitVec 64 :=
  (sramRespData sramCfgICacheData s.dat (icWayIdxHitSt1 s)).extractLsb'
    ((icGetBlockOffset s.paddr1).toNat * 32) 64

/-- OrderViolation_st1（:273-276）。 -/
def icOvSt1 : Bool :=
  (s.wid1 == s.wid2 && s.miss2 && !s.ov2) || (s.wid1 == s.wid3 && s.miss3 && !s.ov3)

/- ---- memRsp_Q 与 refill ---- -/

/-- memRsp_Q deq.valid（pipe 旁路）。 -/
def icDeqValid : Bool := icQDeqValid s.q i.rspValid
/-- memRsp_Q deq.fire（:167-168：ready = mshr.missRspIn.ready = ¬busy）。 -/
def icDeqFire : Bool := icDeqValid s i && !s.mshr.busy
def icDeqBits : IcMemRsp := icQDeqBits s.q i.rspBits

/-- missRspIn.bits.EntryIdx := d_source（:169，5→2 截断保留低位，D6）。 -/
def icRspEntryIdx (r : IcMemRsp) : Fin 4 := (r.dSource.extractLsb' 0 2).toFin

/-- MSHR 输入组装（:161-169, :247-250）。 -/
def icMshrInOf : IcMshrIn :=
  { reqValid := icCacheMiss1 s
    reqBA := icGetBA s.paddr1
    reqTI := s.paddr1.extractLsb' 0 3   -- :164 Cat(warpid,offsets) 截断低 3 位（D6，死字段）
    rspValid := icDeqValid s i
    rspIdx := icRspEntryIdx (icDeqBits s i)
    memReady := i.memReady }

/-- refill 写的 blockAddr（missRspOut.bits.blockAddr，:153/:176）。 -/
def icRefillBA : BitVec 25 := icRspOutBA s.mshr (icMshrInOf s i)
def icRefillSet : Fin 256 := icBASet (icRefillBA s i)
def icRefillTag : BitVec 17 := icBATag (icRefillBA s i)
/-- waymask_replace_st0（:119）。 -/
def icRefillMask : BitVec 2 := icVictimMask s.tag (icRefillSet s i)

/-- Status_st1（:217-219）。 -/
def icStatusSt1 : BitVec 2 :=
  if s.flush0d then 0b10#2
  else
    let miss := icCacheMiss1 s
    let mfire := icMshrReqFire s.mshr (icMshrInOf s i)
    (if (miss && !mfire) || icOvSt1 s then 2#2 else 0#2) ||| (if miss then 1#2 else 0#2)

end IcTopComb

/-- 单拍转移。`deqBitsD` 严格预取（D11-d，预防性）：原
    `wData := fun _ => (icDeqBits s i).dData` 闭包把整拍旧状态捕获进
    data SRAM 的 mem 链；提前取值为扁平 BitVec 后闭包只捕获数值
    （q.mem 已 Array 化，此预取本身 O(1)）。 -/
def icStep (s : IcState) (i : IcIn) : IcState :=
  let deqBitsD : BitVec 1024 := (icDeqBits s i).dData
  { tag := icTagStep s.tag (i.reqValid && !icFlush0 s i) (icGetSetIdxFin i.reqAddr)
      (icDeqFire s i) (icRefillSet s i) (icRefillTag s i) i.invalidate,
    dat := sramStep sramCfgICacheData s.dat
      { rValid := i.reqValid && !icFlush0 s i,
        rAddr := icGetSetIdxFin i.reqAddr,
        wValid := icDeqFire s i,
        wAddr := icRefillSet s i,
        wData := fun _ => deqBitsD,
        wMask := icRefillMask s i },
    mshr := icMshrStep s.mshr (icMshrInOf s i),
    q := icQStep s.q i.rspValid i.rspBits (!s.mshr.busy),
    fire1 := i.reqValid && !icFlush0 s i,
    fire2 := s.fire1 && !icFlush1 s i,
    wid1 := i.reqWarp,
    wid2 := s.wid1,
    wid3 := s.wid2,
    mask1 := i.reqMask,
    mask2 := s.mask1,
    addr1 := i.reqAddr,
    addr2 := s.addr1,
    paddr1 := if i.reqValid then i.reqAddr else s.paddr1,
    st1Set := icGetSetIdxFin i.reqAddr,
    data2 := icDataSt1 s,
    flush0d := icFlush0 s i,
    flush1d := icFlush1 s i,
    statusD := icStatusSt1 s i,
    ov2 := icOvSt1 s,
    ov3 := s.ov2,
    miss2 := if icFlush1 s i then false else icCacheMiss1 s,
    miss3 := s.miss2 }

/-- 多拍执行。 -/
def icRun (s : IcState) (is : List IcIn) : IcState := is.foldl icStep s

/- ---- 输出（st2，对当前状态 s 求值） ---- -/

/-- io.coreRsp（:201-221）。 -/
def icRspValidOut (s : IcState) : Bool := s.fire2 && !s.ov2
def icRspStatus (s : IcState) : BitVec 2 := if s.flush1d then 0b10#2 else s.statusD
def icRspData (s : IcState) : BitVec 64 := s.data2
def icRspWarp (s : IcState) : BitVec 3 := s.wid2
def icRspAddr (s : IcState) : BitVec 32 := s.addr2
/-- io.memReq（:247-250，MMU off 分支）。 -/
def icMemReqValid (s : IcState) : Bool := icMemValid s.mshr
def icMemReqAddr (s : IcState) : BitVec 32 :=
  (s.mshr.blockAddr (icMemNext s.mshr)).zeroExtend 32 <<< 7
def icMemReqSource (s : IcState) : BitVec 5 :=
  (BitVec.ofNat 2 (icMemNext s.mshr).val).zeroExtend 5

/- ========================================================================= -/
/- 7. LFSR 核销（Q1）：机制定理 + 可达性 witness + 后果 witness                -/
/- ========================================================================= -/

/-- coreReq 恒 ready（ICache.scala:262）。 -/
theorem ic_coreReq_ready_true : icCoreReqReady = true := rfl

/-- refill（SRAM 写使能 = memRsp_Q deq.fire）与 probe 无互斥：只依赖队列与
    MSHR busy，不依赖 coreReq 任何字段（:167-168 vs :262）。 -/
theorem ic_deqFire_indep_probe (s : IcState) (i : IcIn) :
    icDeqFire s i =
      (if icQEmpty s.q then i.rspValid && !s.mshr.busy else !s.mshr.busy) := by
  cases h : icQEmpty s.q <;> simp [icDeqFire, icDeqValid, icQDeqValid, h]

/-- probe 的 tag/data 读使能与 refill 完全无关（:145/:179 只含 coreReq.fire
    与 flush）。 -/
theorem ic_probe_read_indep_refill (s : IcState) (i i' : IcIn)
    (hreq : i.reqValid = i'.reqValid) (hfa : i.flushValid = i'.flushValid)
    (hrw : i.reqWarp = i'.reqWarp) (hfw : i.flushWarp = i'.flushWarp) :
    (i.reqValid && !icFlush0 s i) = (i'.reqValid && !icFlush0 s i') := by
  simp [icFlush0, hreq, hfa, hrw, hfw]

/-- **Q1 机制定理（tag 阵列）**：probe（coreReq.fire）与 refill（deq.fire）
    同拍同 set、victim 掩码命中 way j 时，下一拍 st1 的 tag 读出在 way j 上
    为 LFSR64 递增值的低 17 位——与被写入的 tag、阵列原内容均无关。
    （Mem/SRAMTemplate.lean 的 sram_lfsr_bypass 在 ICache tag 例化上的投影。） -/
theorem ic_tag_collision_lfsr (s : IcState) (i : IcIn) (j : Fin 2)
    (hinv : i.invalidate = false) (hfl : icFlush0 s i = false)
    (hreq : i.reqValid = true) (hdeq : icDeqFire s i = true)
    (hset : icGetSetIdxFin i.reqAddr = icRefillSet s i)
    (hmask : ((icRefillMask s i) >>> j.val) &&& 1#2 = 1#2) :
    sramRespData sramCfgICacheTag (icStep s i).tag.sram j =
      (sramLfsrStep (s.tag.sram.lfsr j)).setWidth 17 := by
  have hs : (icStep s i).tag.sram = sramStep sramCfgICacheTag s.tag.sram
      (sramInRW (icRefillSet s i) (fun _ => icRefillTag s i) (icRefillMask s i)) := by
    simp [icStep, icTagStep, hinv, hfl, hreq, hdeq, hset, sramInRW, icRefillMask]
  rw [hs]
  exact sram_lfsr_bypass _ _ _ _ _ j rfl rfl rfl hmask

/-- **Q1 机制定理（data 阵列）**：同上，1024 位块读出为 LFSR 零扩展值。
    （data 读不受 invalidate 门控，D9，故无需 hinv。） -/
theorem ic_data_collision_lfsr (s : IcState) (i : IcIn) (j : Fin 2)
    (hfl : icFlush0 s i = false) (hreq : i.reqValid = true)
    (hdeq : icDeqFire s i = true)
    (hset : icGetSetIdxFin i.reqAddr = icRefillSet s i)
    (hmask : ((icRefillMask s i) >>> j.val) &&& 1#2 = 1#2) :
    sramRespData sramCfgICacheData (icStep s i).dat j =
      (sramLfsrStep (s.dat.lfsr j)).setWidth 1024 := by
  have hs : (icStep s i).dat = sramStep sramCfgICacheData s.dat
      (sramInRW (icRefillSet s i) (fun _ => (icDeqBits s i).dData) (icRefillMask s i)) := by
    simp [icStep, hfl, hreq, hdeq, hset, sramInRW, icRefillMask]
  rw [hs]
  exact sram_lfsr_bypass _ _ _ _ _ j rfl rfl rfl hmask

/-- waymaskHit 的命中位置：way j 匹配 ⇒ waymaskHit 的 bit j 置位。 -/
theorem icWaymaskHit_bit_set (t : IcTagState) (tag : BitVec 17) (v : Fin 256)
    (j : Fin 2) (h : icWayMatch t tag v j = true) :
    (icWaymaskHit t tag v >>> j.val) &&& 1#2 = 1#2 := by
  rcases icFin2_cases j with hj | hj <;> subst hj <;>
    (cases h0 : icWayMatch t tag v 0 <;> cases h1 : icWayMatch t tag v 1) <;>
    simp_all [icWaymaskHit]

/-- **假 hit 符号化判据**：碰撞拍若 probe 的 tag 恰等于将读出的 LFSR 值
    （低 17 位），则 st1 在 victim way 上"命中"——命中的是从未写入阵列的
    幽灵 tag。 -/
theorem ic_false_hit_st1 (s : IcState) (i : IcIn) (j : Fin 2)
    (hinv : i.invalidate = false) (hfl : icFlush0 s i = false)
    (hreq : i.reqValid = true) (hdeq : icDeqFire s i = true)
    (hset : icGetSetIdxFin i.reqAddr = icRefillSet s i)
    (hmask : ((icRefillMask s i) >>> j.val) &&& 1#2 = 1#2)
    (htag : icGetTag i.reqAddr = (sramLfsrStep (s.tag.sram.lfsr j)).setWidth 17)
    (hnotfull : icSetFull s.tag (icRefillSet s i) = false) :
    icWayMatch (icStep s i).tag (icGetTag (icStep s i).paddr1) (icStep s i).st1Set j = true := by
  have hcol := ic_tag_collision_lfsr s i j hinv hfl hreq hdeq hset hmask
  have hp : (icStep s i).paddr1 = i.reqAddr := by simp [icStep, hreq]
  have hss : (icStep s i).st1Set = icGetSetIdxFin i.reqAddr := rfl
  have hwv : (icStep s i).tag.wayValid (icRefillSet s i) =
      s.tag.wayValid (icRefillSet s i) ||| icRefillMask s i := by
    have h := icTagStep_wayValid_refill s.tag (i.reqValid && !icFlush0 s i)
      (icGetSetIdxFin i.reqAddr) (icRefillSet s i) (icRefillTag s i) hnotfull
    simpa [icStep, hreq, hfl, hdeq, hinv, icRefillMask] using h
  simp only [icWayMatch]
  rw [hp, hss, hcol, htag]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [hset, hwv]
  rcases icFin2_cases j with hj | hj <;> subst hj <;> simp at hmask ⊢ <;> bv_decide

/- --------------------------- 可达性 witness ---------------------------- -/

/-- 复位起第 4 次 LFSR 递增后的值（碰撞拍 st1 实际读出的"随机"源）。 -/
def icL4 : BitVec 64 :=
  sramLfsrStep (sramLfsrStep (sramLfsrStep (sramLfsrStep sramLfsrInit)))

/-- 场景公共参数：set S=3，块 B 的 blockAddr = 0xABCD03（tag=0x0ABCD, set=3）。 -/
def icBAB : BitVec 25 := 0xABCD03#25
def icAddrA : BitVec 32 := icBAB.zeroExtend 32 <<< 7
/-- L2 返回：d_source = entry 0，数据低 64 位 = 0xDEADBEEF。 -/
def icRspB : IcMemRsp := ⟨0#5, 0xDEADBEEF#1024⟩

def icI0 : IcIn := { icInIdle with reqValid := true, reqAddr := icAddrA, reqMask := 3#2 }
/-- 碰撞拍输入：probe A 与 B 的 refill 同拍。 -/
def icI3coll : IcIn := { icInIdle with reqValid := true, reqAddr := icAddrA, rspValid := true, rspBits := icRspB }
def icI3clean : IcIn := { icInIdle with rspValid := true, rspBits := icRspB }
def icI4probe : IcIn := { icInIdle with reqValid := true, reqAddr := icAddrA }

/- ---- 场景 A：假 miss + 同块重复分配 ---- -/

def icTA1 := icStep icInit icI0        -- probe A → st1 miss
def icTA2 := icStep icTA1 icInIdle     -- missReq.fire：entry0 分配
def icTA3 := icStep icTA2 icInIdle     -- miss2mem.fire：访存请求发出
def icTA4 := icStep icTA3 icI3coll     -- ★ 碰撞：refill B ∥ retry probe A
def icTA5 := icStep icTA4 icInIdle     -- 假 miss 作为新主 miss 再分配

-- miss 被接受：st2 响应 status=01（MISS accepted），访存请求发出
theorem icTA_miss_accepted :
    icRspValidOut icTA2 = true ∧ icRspStatus icTA2 = 0b01#2 ∧
    icMemReqValid icTA2 = true ∧ icMemReqAddr icTA2 = icBAB.zeroExtend 32 <<< 7 := by
  native_decide

-- 可达性：probe 与 refill 同拍同 set 同时成立（无互斥，由
-- ic_coreReq_ready_true / ic_deqFire_indep_probe 结构性保证）
theorem icTA_collision_reachable :
    (icI3coll.reqValid && !icFlush0 icTA3 icI3coll) = true ∧
    icDeqFire icTA3 icI3coll = true ∧
    icGetSetIdxFin icI3coll.reqAddr = icRefillSet icTA3 icI3coll := by
  native_decide

-- 机制数值确认：st1 tag 读出 = LFSR 低 17 位；写入本身不受影响
theorem icTA_tag_readout_lfsr :
    sramRespData sramCfgICacheTag icTA4.tag.sram ⟨0, by decide⟩ = icL4.setWidth 17 ∧
    icTA4.tag.sram.mem ⟨3, by decide⟩ ⟨0, by decide⟩ = 0x0ABCD#17 ∧
    icTA4.tag.wayValid ⟨3, by decide⟩ = 0b01#2 := by
  native_decide

-- 后果 1（假 miss）：B 的 tag+valid 已在阵列，st1 仍判 miss，且该 miss 被
-- 当作新主 miss 接受（MSHR 的 ReqConflictWithRsp 只覆盖同拍，:156-158）
theorem icTA_false_miss :
    icHitSt1 icTA4 = false ∧ icCacheMiss1 icTA4 = true ∧
    icMshrReqFire icTA4.mshr (icMshrInOf icTA4 icInIdle) = true := by
  native_decide

-- 后果 2（同块重复分配）：B 已在 cache，却又占一个 MSHR entry 并将再次访存
-- （重复 refill 带宽浪费；本配置下数据无错——refill 会覆盖写入相同数据）
theorem icTA_duplicate_alloc :
    icEntryValid icTA5.mshr ⟨0, by decide⟩ = true ∧
    icTA5.mshr.blockAddr ⟨0, by decide⟩ = icBAB ∧
    icMemReqValid icTA5 = true ∧ icMemReqAddr icTA5 = icBAB.zeroExtend 32 <<< 7 ∧
    icTA5.tag.sram.mem ⟨3, by decide⟩ ⟨0, by decide⟩ = 0x0ABCD#17 := by
  native_decide

/- ---- 场景 B：假 hit（数据错误） ---- -/

/-- 幽灵 tag：碰撞拍 st1 将从 victim way 读出的 LFSR 低 17 位。 -/
def icTagX : BitVec 17 := icL4.setWidth 17
def icAddrX : BitVec 32 := ((icTagX.zeroExtend 25 <<< 8) ||| 3#25).zeroExtend 32 <<< 7
def icI3X : IcIn := { icInIdle with reqValid := true, reqAddr := icAddrX, rspValid := true, rspBits := icRspB }

def icTB1 := icStep icInit icI0
def icTB2 := icStep icTB1 icInIdle
def icTB3 := icStep icTB2 icInIdle
def icTB4 := icStep icTB3 icI3X        -- ★ 碰撞：refill B ∥ probe X(tag=LFSR)
def icTB5 := icStep icTB4 icInIdle     -- X 的 st2

-- 后果 3（假 hit = 数据错误）：阵列中只有 tagB（way0）与空（way1），
-- 对 tagX 的 probe 却命中 way0；st2 返回 status=00（HIT）+ LFSR 垃圾指令，
-- 而非任何已缓存数据（0xDEADBEEF 才是当拍写入的块数据）。
theorem icTB_false_hit :
    icHitSt1 icTB4 = true ∧ icCacheMiss1 icTB4 = false ∧
    icTB4.tag.sram.mem ⟨3, by decide⟩ ⟨0, by decide⟩ = 0x0ABCD#17 ∧
    icTB4.tag.sram.mem ⟨3, by decide⟩ ⟨1, by decide⟩ = 0#17 ∧
    icTagX ≠ 0x0ABCD#17 ∧ icTagX ≠ 0#17 ∧
    icRspValidOut icTB5 = true ∧ icRspStatus icTB5 = 0b00#2 ∧
    icRspData icTB5 = icL4 ∧ icRspData icTB5 ≠ 0xDEADBEEF#64 ∧
    icRspAddr icTB5 = icAddrX := by
  native_decide

/- ---- 场景 C：干净 refill 后的命中正确性（对照组） ---- -/

def icTC1 := icStep icInit icI0
def icTC2 := icStep icTC1 icInIdle
def icTC3 := icStep icTC2 icInIdle
def icTC4 := icStep icTC3 icI3clean    -- refill，无 probe 冲突
def icTC5 := icStep icTC4 icI4probe    -- probe A → st1 hit
def icTC6 := icStep icTC5 icInIdle     -- st2

-- 命中判定 + 数据通路正确性：tag 比较 + valid 命中 way0，返回该 set 该 way
-- 的数据（经 blockOffset=0 切片），status=00
theorem icTC_clean_hit :
    icHitSt1 icTC5 = true ∧ icWaymaskHitSt1 icTC5 = 0b01#2 ∧
    icRspValidOut icTC6 = true ∧ icRspStatus icTC6 = 0b00#2 ∧
    icRspData icTC6 = 0xDEADBEEF#64 ∧ icRspAddr icTC6 = icAddrA ∧
    icRspWarp icTC6 = 0#3 := by
  native_decide

/- ---- 场景 D（Q2 witness）：同 set 两块 ping-pong ---- -/

/-- 块 B2：tag=0x12345, set=3（与 B 同 set）。 -/
def icBAB2 : BitVec 25 := 0x1234503#25
def icAddrB2 : BitVec 32 := icBAB2.zeroExtend 32 <<< 7
def icRspB2 : IcMemRsp := ⟨0#5, 0xCAFEBABE#1024⟩

def icIprobeB2 : IcIn := { icInIdle with reqValid := true, reqAddr := icAddrB2 }
def icIrspB2 : IcIn := { icInIdle with rspValid := true, rspBits := icRspB2 }

-- refill B（干净）→ probe B2（miss）→ refill B2（干净）→ probe A
def icTD8 : IcState := icRun icInit
  [icI0, icInIdle, icInIdle, icI3clean,          -- B 进 way0
   icIprobeB2, icInIdle, icInIdle, icIrspB2]     -- B2 应进 way1，实际覆盖 way0
def icTD9 := icStep icTD8 icI4probe              -- 再取 A

-- Q2 witness：B2 覆盖 way0（A 被挤出）、way1 恒空、再取 A 必 miss
theorem icTD_victim_thrash :
    icTD8.tag.sram.mem ⟨3, by decide⟩ ⟨0, by decide⟩ = 0x12345#17 ∧
    icTD8.tag.sram.mem ⟨3, by decide⟩ ⟨1, by decide⟩ = 0#17 ∧
    icTD8.tag.wayValid ⟨3, by decide⟩ = 0b01#2 ∧
    icHitSt1 icTD9 = false ∧ icCacheMiss1 icTD9 = true := by
  native_decide

/-- Q2 不变式：从复位起任意输入序列后，way1 恒无效、victim 恒 0b01
    （ICache 事实退化为直接映射）。 -/
theorem ic_way1_never_valid (s : IcState) (is : List IcIn) (h : icTagInv s.tag) :
    icTagInv (icRun s is).tag := by
  induction is generalizing s with
  | nil => exact h
  | cons x xs ih =>
    exact ih (icStep s x)
      (icTagStep_preserves_inv s.tag _ _ _ _ _ _ h)

/-- 顶层数据选择正确性：独热命中 way j ⇒ st1 数据 = data SRAM 该 way 读出
    的 blockOffset 切片。 -/
theorem icDataSt1_of_onehot (s : IcState) (j : Fin 2)
    (h : icWaymaskHitSt1 s = BitVec.ofNat 2 (1 <<< j.val)) :
    icDataSt1 s = (sramRespData sramCfgICacheData s.dat j).extractLsb'
      ((icGetBlockOffset s.paddr1).toNat * 32) 64 := by
  simp [icDataSt1, icWayIdxHitSt1, icHitWayIdx_of_onehot _ _ h]

/- ========================================================================= -/
/- 8. MSHR 数值回归测试                                                       -/
/- ========================================================================= -/

/-- miss 请求输入（memReady=1）。 -/
def icMI (ba : BitVec 25) (ti : BitVec 3) : IcMshrIn := ⟨true, ba, ti, false, 0, true⟩
def icMIno : IcMshrIn := ⟨false, 0, 0, false, 0, true⟩
def icMIrsp (idx : Fin 4) : IcMshrIn := ⟨false, 0, 0, true, idx, true⟩

def icM1 := icMshrStep icMshrInit (icMI 0x100#25 5#3)
-- 主 miss 分配：entry0 占用、信息入表、发起访存
theorem icT_mshr_alloc :
    icEntryValid icM1 0 = true ∧ icM1.blockAddr 0 = 0x100#25 ∧
    icM1.subValid 0 0 = true ∧ icM1.targetInfo 0 0 = 5#3 ∧
    icMemValid icM1 = true ∧ icMemNext icM1 = ⟨0, by decide⟩ := by
  native_decide

def icM2 := icMshrStep icM1 (icMI 0x100#25 6#3)
-- 同块二次 miss 合并：不新占 entry、不产生新访存（hasSend 已置位），
-- targetInfo 记入 subentry1
theorem icT_mshr_merge :
    icSecondary icM1 (icMI 0x100#25 6#3) = true ∧
    icEntryValid icM2 1 = false ∧
    icM2.subValid 0 1 = true ∧ icCount4 (icM2.subValid 0) = 2 ∧
    icM2.targetInfo 0 1 = 6#3 ∧
    (∀ e, icM2.blockAddr e = icM1.blockAddr e) ∧
    icM2.hasSend 0 = true ∧ icMemValid icM2 = false := by
  native_decide

def icM3 := icMshrStep icM2 (icMIrsp 0)
-- 响应到达（used=2）：rspOut 有效、blockAddr 正确；busy 升起顶住 memRsp_Q
theorem icT_mshr_rsp_busy :
    icRspOutValid icM2 (icMIrsp 0) = true ∧
    icRspOutBA icM2 (icMIrsp 0) = 0x100#25 ∧
    icRspOutTI icM2 (icMIrsp 0) = 5#3 ∧
    icM3.busy = true ∧
    icRspInFire icM3 (icMIrsp 0) = false ∧
    icRspOutValid icM3 (icMIrsp 0) = true := by
  native_decide

def icM4 := icMshrStep icM3 icMIno
-- busy 续排：第二个 subentry 释放后 entry 完全释放、hasSend 清除、busy 落下
theorem icT_mshr_rsp_drain :
    icEntryValid icM4 0 = false ∧ icM4.hasSend 0 = false ∧ icM4.busy = false := by
  native_decide

def icM4full := icMshrRun icMshrInit
  [icMI 0x10#25 0, icMI 0x20#25 0, icMI 0x30#25 0, icMI 0x40#25 0]
-- MSHR 满：主 miss 被拒（reservation fail），次 miss（同块合并）仍收
theorem icT_mshr_full :
    icEntryFull icM4full = true ∧
    icMshrReqReady icM4full (icMI 0x50#25 0) = false ∧
    icMshrReqReady icM4full (icMI 0x10#25 1) = true := by
  native_decide

-- 同块 refill 与 miss 同拍：missReq 被拒（ReqConflictWithRsp，:156-158）
theorem icT_mshr_conflict :
    icMshrReqReady icM1 ⟨true, 0x100#25, 0, true, ⟨0, by decide⟩, true⟩ = false := by
  native_decide

-- Q3 witness：次 miss 的 subentry 满判定看错行——entry1（0x20）的次 miss
-- 因 rspIdx 指向的 entry0 行满而被拒（entry1 本有空位）
def icMq1 := icMshrRun icMshrInit
  [icMI 0x10#25 0, icMI 0x20#25 0, icMI 0x10#25 1, icMI 0x10#25 2, icMI 0x10#25 3]
theorem icT_subfull_quirk :
    icSecondary icMq1 ⟨true, 0x20#25, 0, false, ⟨0, by decide⟩, true⟩ = true ∧
    icSelFull icMq1 ⟨true, 0x20#25, 0, false, ⟨0, by decide⟩, true⟩ = true ∧
    icMshrReqReady icMq1 ⟨true, 0x20#25, 0, false, ⟨0, by decide⟩, true⟩ = false := by
  native_decide

/- ---- 公理审计（native_decide 定理含 Lean.ofReduceBool，属预期） ---- -/

#print axioms ic_tag_collision_lfsr
#print axioms ic_data_collision_lfsr
#print axioms ic_false_hit_st1
#print axioms ic_deqFire_indep_probe
#print axioms icMshr_primary_alloc
#print axioms icMshr_secondary_merge
#print axioms icMshr_rsp_fire
#print axioms icMshr_rsp_last_frees
#print axioms icMshrStep_inv
#print axioms icMshr_no_loss
#print axioms icVictimMask_way0_valid_only
#print axioms ic_way1_never_valid
#print axioms icDataSt1_of_onehot
#print axioms icTB_false_hit
#print axioms icTA_false_miss

end Ventus.Mem
