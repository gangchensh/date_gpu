/- ========================================================================= -/
/-                        Mem/SRAMTemplate.lean                              -/
/-  NutShell 血统 SRAM 封装 SRAMTemplate 的 Lean 4 模型、测试与证明            -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/SRAMTemplate/                -/
/-      SRAMTemplate.scala（全文 166 行）、Hold.scala、LFSR64.scala           -/
/-    L2cache/SRAMTemplate.scala 为近亲副本（package 不同；LFSR64 改用         -/
/-      rocketchip 版本；Hold.scala 的 ReadAndHold 多个显式复位——结构相同）   -/
/-                                                                           -/
/- ======================== 例化配置核查（2026-08-26 全仓 grep） ============= -/
/-  shouldReset / holdRead / singlePort / bypassWrite：                       -/
/-  * DCache.scala:638   DataAccess（UInt(8.W), set=NSets*NWays, way=4）：     -/
/-      F,F,F,F（bypassWrite 取缺省 false）——dual-port 无旁路，Q1             -/
/-  * ICache.scala:84    dataAccess（UInt(BlockBits=1024.W), way=NWays）：     -/
/-      F,F,F,F（缺省）——dual-port 无旁路，Q1                                 -/
/-  * L1TagAccess.scala:115 tagBodyAccess（DCache tag）：F,T,F,T               -/
/-    L1TagAccess.scala:142 ASIDAccess：MMU_ENABLED=false，不展开，不建模      -/
/-    L1TagAccess.scala:168 timeAccess：F,T,F,T（同 tag 配置）                 -/
/-    L1TagAccess.scala:209 dirtyMaskAccess：T,T,F,T——仅有的两个              -/
/-      shouldReset=true 例化之一                                             -/
/-  * L1TagAccess.scala:451 tagBodyAccess（ICache tag）：F,T,F,F——             -/
/-      dual-port 无旁路 + holdRead，Q1                                       -/
/-    L1TagAccess.scala:473 asidAccess：MMU_ENABLED=false，不展开              -/
/-  * ShareMem.scala:146 DataAccess：F,F,F,T                                  -/
/-  * L2cache/BankedStore.scala:93 cc_banks：F,F,F,F（L2cache 变体），Q1        -/
/-  * L2cache/Directory_test.scala:104 cc_dir：T,T,F,T（L2cache 变体）          -/
/-  * SRAMTemplateWithArbiter（:148-166）：全仓（含 L2cache 副本）无任何        -/
/-      例化 —— 死代码，不建模（D7）。其内部 singlePort=true 配置由             -/
/-      sramCfgSinglePort 覆盖。                                              -/
/-  另外：L2TLB.scala:3 只 import 不例化；全仓再无其他 SRAMTemplate 例化。      -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. set/way/字宽 w 参数化建模；地址用 Fin set（Chisel UInt(log2Up set)，   -/
/-      合法范围内等价）。                                                    -/
/-  D2. 同拍同址读写的 raw 读出（SyncReadMem read-during-write）在 Chisel/     -/
/-      物理 SRAM 中未定义；本模型取"写后值"。该选择只影响 don't-care 情形：   -/
/-      bypassWrite 时同址 way 被旁路覆盖；!bypassWrite 时同址且写掩码命中的   -/
/-      way 被 LFSR 覆盖（Q1）；未命中 way 写前后不变，写后值=写前值。        -/
/-  D3. realRen=false 拍的 raw 读出建模为 mem[prevRaddr]（真实 SRAM 宏观       -/
/-      值不定）；holdRead 配置下被 holdData 覆盖，非 holdRead 配置消费方只    -/
/-      在发起过读后采样——该 don't-care 不进入任何定理结论。                  -/
/-  D4. LFSR64（LFSR64.scala:17-26）：初值 0x1234567887654321，每拍递增        -/
/-      （increment 缺省 true.B），全 0 锁存保护（lfsr==0 → 1）。way 个实例    -/
/-      同种子同序列。L2cache 变体用 rocketchip LFSR64（种子/多项式不同，      -/
/-      定性结论相同）。bypass_wdata 取 lfsr 当前值的 setWidth（w≤64 截低位； -/
/-      w>64 如 ICache dataAccess 的 1024 位为高位零扩展——Q1 备注）。         -/
/-  D5. shouldReset 的 Counter（:99-106）建模为 resetBusy+resetSet：           -/
/-      resetBusy 期间逐拍写一个 set（全 0、全 way），resetSet=set-1 拍末       -/
/-      清 resetBusy。shouldReset=false 时 resetState 恒 false（:97 WireInit） -/
/-      ——模型以 sramResetBusy cfg s = cfg.shouldReset && s.resetBusy 表达。  -/
/-  D6. way=1 时 waymask 字段不存在，getOrElse "b1"（:113）：模型要求调用方    -/
/-      传 wm=全 1，等价。                                                    -/
/-  D7. SRAMTemplateWithArbiter（:148-166）死代码不建模（见例化核查）。        -/
/-  D8. mem 上电初值建模为全 0（真实 SRAM 未定）；所有定理结论只落在           -/
/-      "写后读"或"复位后读"的确定值上。                                      -/
/-  D9. MemLaws 接口是整字读写契约，与本模块的 way 掩码部分写不匹配，故不      -/
/-      建 MemLaws 实例，写后读/waymask 选择性/单端口互斥以直接定理给出        -/
/-      （sram_read_after_write / sramWriteMem_* / sram_realRen_singlePort）。 -/
/-  D10. SramState 的 mem/holdData/prevWdata/lfsr 原为 `Fin … → …` 函数字段    -/
/-      （sramUpd/逐拍闭包链）：第 20 波 agent-41 实测其在整机模拟中残留         -/
/-      ~0.1µs/拍² 的二次尾项（每拍读 lfsr/holdData/mem 都要展开整条历史闭包）。 -/
/-      本波（第 21 波）四字段全部 Array 化（范本：第 17 波 WarpScheduler.lean、 -/
/-      第 20 波 ICache.lean）：读用 `Array.getD`、每拍构造时以 `Array.ofFn`     -/
/-      逐点物化（mem 无写拍、holdData 无更新拍直接共享旧数组，O(1)），切断跨拍  -/
/-      闭包链。函数视图由同名访问器（`s.mem a j`、`s.holdData j`、              -/
/-      `s.prevWdata j`、`s.lfsr j`，见下）提供，全部既有定理陈述语义不变；      -/
/-      sramMemN/sramWriteMem/sramUpd 保持函数视图签名不变（定理陈述与           -/
/-      L1TagAccess/DCache/ICache 的 sramUpd 复用均不受影响）。性能对照见        -/
/-      sramRun 下方注释。                                                       -/
/-                                                                           -/
/- ======================== 源码审查发现（详见返回报告） ===================== -/
/-  Q1（I 类候选，bypassWrite=false && dual-port 时同拍同址读读出 LFSR         -/
/-      "随机"值，:128-135）：bypass_wdata = LFSR64() 是综合后的真实逻辑       -/
/-      （NutShell 的 X 探测惯用法）。need_bypass 用的是 io.*.req.valid 的      -/
/-      RegNext（:121,:130，非 wen/realRen）。命中条件的例化点分析：          -/
/-      - ICache tagBodyAccess（L1TagAccess.scala:451, F,T,F,F）：读 =          -/
/-        coreReq.fire 的 probe（ICache.scala:145-146），写 =                  -/
/-        memRsp_Q.io.deq.fire 的 refill（:152-153）。两者无互斥逻辑：miss     -/
/-        refill 落 set S 的当拍，若有对 set S 的 fetch probe，victim way 的   -/
/-        tag 读出为 LFSR 值并被 holdRead 保持 → tagChecker 误判（大概率假     -/
/-        miss，2^-tagBits 概率假 hit）。是否真实发生取决于 miss 重放与        -/
/-        refill 的时序关系，需主会话在 ICache 波次确认。                     -/
/-      - ICache dataAccess（ICache.scala:84, F,F,F,F）：同上时序，数据阵      -/
/-        列 1024 位宽读出为 LFSR 64 位零扩展值。                             -/
/-      - DCache DataAccess（DCache.scala:638, F,F,F,F）：readHit_st1 与       -/
/-        writeHit_st1 互斥（同请求的 isRead/isWrite），dataReplaceReadValid   -/
/-        与 dataFillVaild 互斥（needReplace 互补，:579-589）；但               -/
/-        dataReplaceReadValid（读淘汰 victim，:579-583）与 writeHit_st1       -/
/-        （写命中，:646-648）同拍同址（同 set 且命中 way == waymaskReplacement）-/
/-        未见显式互斥 → victim 写回 L2 的数据可能被 LFSR 污染。需 DCache      -/
/-        波次确认该时序组合是否可达。                                        -/
/-      - L2 cc_banks（BankedStore.scala:93）：L2cache 变体，同结构，可达性    -/
/-        由 L2 波次判断。                                                    -/
/-      模型层结论由 sram_lfsr_bypass（符号）与 sramT_lfsr_*（数值）钉死：     -/
/-      命中 way 的读出 = sramLfsrStep 后的 LFSR 值，与写入数据、原数据均      -/
/-      无关。                                                                -/
/-  Q2（提示性，复位期间写静默丢失）：wen = wValid || resetState（:108），     -/
/-      但 setIdx/wdata/waymask 在 resetState 时被强制为 resetSet/0/全 1       -/
/-      （:111-114），且 w.req.ready 恒 true（:144）——复位期间的用户写被      -/
/-      静默丢弃（sram_resetStep_mem 的右端与输入无关即此意的形式化）。        -/
/-      现有例化的上游均在复位完成后才写，无实际危害。                          -/
/-  Q3（提示性，:130 的 bypass 检测用原始 valid 而非 wen/realRen）：           -/
/-      shouldReset 复位期间的强制写不触发 bypass（prevNeedCheck 只看          -/
/-      io.w.req.valid）——与"复位清零对外不可见"的设计意图一致；singlePort    -/
/-      时 bypass 整体不用（:132），无影响。                                   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 配置与 LFSR64                                                           -/
/- ========================================================================= -/

/-- SRAMTemplate 的四个布尔参数（SRAMTemplate.scala:88-89）。 -/
structure SramCfg where
  shouldReset : Bool
  holdRead : Bool
  singlePort : Bool
  bypassWrite : Bool
deriving DecidableEq, Repr

-- 实际例化配置（见头部核查）
def sramCfgDCacheData : SramCfg := ⟨false, false, false, false⟩  -- DCache.scala:638
def sramCfgICacheData : SramCfg := ⟨false, false, false, false⟩  -- ICache.scala:84
def sramCfgDCacheTag  : SramCfg := ⟨false, true, false, true⟩    -- L1TagAccess.scala:115,168
def sramCfgICacheTag  : SramCfg := ⟨false, true, false, false⟩   -- L1TagAccess.scala:451
def sramCfgShareMem   : SramCfg := ⟨false, false, false, true⟩   -- ShareMem.scala:146
def sramCfgDCacheDirty : SramCfg := ⟨true, true, false, true⟩    -- L1TagAccess.scala:209
def sramCfgL2Dir      : SramCfg := ⟨true, true, false, true⟩     -- Directory_test.scala:104（L2 变体）
def sramCfgL2Bank     : SramCfg := ⟨false, false, false, false⟩  -- BankedStore.scala:93（L2 变体）
def sramCfgSinglePort : SramCfg := ⟨false, false, true, false⟩   -- WithArbiter 内（死代码，D7）

/-- LFSR64 初值（LFSR64.scala:20）。 -/
def sramLfsrInit : BitVec 64 := 0x1234567887654321#64

/-- LFSR64 单拍（LFSR64.scala:21-24）：xor = lfsr(0)^lfsr(1)^lfsr(3)^lfsr(4)，
    lfsr := Mux(lfsr==0, 1, Cat(xor, lfsr(63,1)))。 -/
def sramLfsrStep (x : BitVec 64) : BitVec 64 :=
  if x = 0#64 then 1#64
  else
    let xb := xor (xor (x.getLsbD 0) (x.getLsbD 1)) (xor (x.getLsbD 3) (x.getLsbD 4))
    (x >>> 1) ||| ((if xb then 1#64 else 0#64) <<< 63)

/- ---- LFSR64 测试 ---- -/

theorem sramT_lfsr_step0 : sramLfsrStep sramLfsrInit = 0x891A2B3C43B2A190#64 := by
  native_decide
theorem sramT_lfsr_step1 :
    sramLfsrStep (sramLfsrStep sramLfsrInit) = 0xC48D159E21D950C8#64 := by
  native_decide
theorem sramT_lfsr_zero_lockup : sramLfsrStep 0#64 = 1#64 := by native_decide
-- bypass_wdata 取低 32 位（w=32 情形）
theorem sramT_lfsr_low32 : (sramLfsrStep sramLfsrInit).setWidth 32 = 0x43B2A190#32 := by
  native_decide

/- ========================================================================= -/
/- 2. 状态、输入与组合逻辑（SRAMTemplate.scala:96-144）                       -/
/- ========================================================================= -/

/-- SRAMTemplate 状态：SyncReadMem 阵列 + hold 寄存器 + bypass 的 RegNext 链
    （:120-130）+ LFSR（每 way 一个，:129）+ 复位计数（:99-106）。
    D10：mem/holdData/prevWdata/lfsr 原为 `Fin … → …` 函数字段，Array 化
    消除跨拍闭包链求值二次尾项；函数视图由同名访问器（见下）提供，
    定理陈述不受影响。数组尺寸：memArr 为 set × way，其余为 way。 -/
structure SramState (set way w : Nat) where
  memArr : Array (Array (BitVec w))  -- array（:96）
  holdDataArr : Array (BitVec w)     -- HoldUnless 的 RegEnable（:139，holdRead 时有效）
  prevRealRen : Bool                 -- RegNext(realRen)（:139 的 en）
  prevNeedCheck : Bool               -- RegNext(rValid && wValid)（:121，原始 valid，Q3）
  prevWaddr : Fin set                -- RegNext(waddr)（:122）
  prevRaddr : Fin set                -- RegNext(raddr)（:123）
  prevWmask : BitVec way             -- RegNext(wmask)（:125）
  prevWdataArr : Array (BitVec w)    -- RegNext(w.req.bits.data)（:128，bypassWrite 时有效）
  lfsrArr : Array (BitVec 64)        -- 每 way 一个 LFSR64（:129）
  resetBusy : Bool                   -- _resetState（:100）
  resetSet : Fin set                 -- _resetSet（:101）

/-- 状态投影访问器（D10）：保持原函数字段的名称与语义，实现为 Array + getD。
    越界返回默认值——自 sramInit 起经 sramStep 的可达状态各数组尺寸恒
    set/way，永不越界；越界语义只影响病态状态的泛化推理。所有既有
    `s.mem a j`、`s.holdData j`、`s.prevWdata j`、`s.lfsr j` 写法原样有效。 -/
def SramState.mem {set way w : Nat} (s : SramState set way w) : Fin set → Fin way → BitVec w :=
  fun a j => ((s.memArr.getD a.val #[]).getD j.val 0)
/-- holdData 访问器（:139），见 mem。 -/
def SramState.holdData {set way w : Nat} (s : SramState set way w) : Fin way → BitVec w :=
  fun j => s.holdDataArr.getD j.val 0
/-- prevWdata 访问器（:128），见 mem。 -/
def SramState.prevWdata {set way w : Nat} (s : SramState set way w) : Fin way → BitVec w :=
  fun j => s.prevWdataArr.getD j.val 0
/-- lfsr 访问器（:129），见 mem。 -/
def SramState.lfsr {set way w : Nat} (s : SramState set way w) : Fin way → BitVec 64 :=
  fun j => s.lfsrArr.getD j.val 0

/-- 初始状态（RegInit 部分忠实：holdData/prev 链为 0、resetBusy=true、
    resetSet=0、lfsr=种子；mem 上电未定，建模为全 0，D8）。 -/
def sramInit (set way w : Nat) [NeZero set] : SramState set way w :=
  { memArr := Array.replicate set (Array.replicate way 0)
    holdDataArr := Array.replicate way 0
    prevRealRen := false
    prevNeedCheck := false
    prevWaddr := 0
    prevRaddr := 0
    prevWmask := 0
    prevWdataArr := Array.replicate way 0
    lfsrArr := Array.replicate way sramLfsrInit
    resetBusy := true
    resetSet := 0 }

/-- 读/写请求（SRAMReadBus/SRAMWriteBus 的 req.bits + valid，:63-86）。 -/
structure SramIn (set way w : Nat) where
  rValid : Bool
  rAddr : Fin set
  wValid : Bool
  wAddr : Fin set
  wData : Fin way → BitVec w
  wMask : BitVec way

section SramModel

variable {set way w : Nat} [NeZero set]

def sramInIdle : SramIn set way w := ⟨false, 0, false, 0, fun _ => 0, 0⟩
def sramInWrite (a : Fin set) (wd : Fin way → BitVec w) (wm : BitVec way) : SramIn set way w :=
  ⟨false, a, true, a, wd, wm⟩
def sramInRead (a : Fin set) : SramIn set way w :=
  ⟨true, a, false, a, fun _ => 0, 0⟩
/-- 同拍同址读写（Q1/Q4 场景）。 -/
def sramInRW (a : Fin set) (wd : Fin way → BitVec w) (wm : BitVec way) : SramIn set way w :=
  ⟨true, a, true, a, wd, wm⟩

/-- resetState（:97-106，shouldReset=false 时恒 false，D5）。 -/
def sramResetBusy (cfg : SramCfg) (s : SramState set way w) : Bool :=
  cfg.shouldReset && s.resetBusy

/-- wen = wValid || resetState（:108）。 -/
def sramWen (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w) : Bool :=
  i.wValid || sramResetBusy cfg s

/-- realRen（:109）：singlePort 时读让写。 -/
def sramRealRen (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w) : Bool :=
  if cfg.singlePort then i.rValid && !sramWen cfg s i else i.rValid

/-- io.r.req.ready（:143）。 -/
def sramRRdy (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w) : Bool :=
  !sramResetBusy cfg s && (if cfg.singlePort then !sramWen cfg s i else true)

/-- io.w.req.ready（:144，恒 true；复位期间写被丢弃见 Q2）。 -/
def sramWRdy : Bool := true

/-- 函数表更新（本项目手写版，与 Ventus.Base.Defs 的 rf_write 同风格）。 -/
def sramUpd (f : Fin n → α) (i : Fin n) (v : α) : Fin n → α :=
  fun j => if i = j then v else f j

@[simp] theorem sramUpd_self (f : Fin n → α) (i : Fin n) (v : α) :
    sramUpd f i v i = v := by simp [sramUpd]

theorem sramUpd_of_ne (f : Fin n → α) (i j : Fin n) (v : α) (h : j ≠ i) :
    sramUpd f i v j = f j := by
  simp only [sramUpd]; exact if_neg (fun hh => h hh.symm)

/-- 带 way 掩码的阵列写（:111-114 的 array.write(setIdx, wdata, waymask)）。 -/
def sramWriteMem (mem : Fin set → Fin way → BitVec w) (a : Fin set)
    (wd : Fin way → BitVec w) (wm : BitVec way) : Fin set → Fin way → BitVec w :=
  sramUpd mem a (fun j => if (wm >>> j.val) &&& 1#way = 1#way then wd j else mem a j)

/-- 阵列写更新（:108-114）：复位期间强制写 resetSet/全 0/全 way（Q2）。 -/
def sramMemN (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w) :
    Fin set → Fin way → BitVec w :=
  if sramWen cfg s i then
    let rb := sramResetBusy cfg s
    sramWriteMem s.mem
      (if rb then s.resetSet else i.wAddr)
      (if rb then (fun _ => 0) else i.wData)
      (if rb then BitVec.allOnes way else i.wMask)
  else s.mem

/-- SyncReadMem 原始读出（:116）：读上一拍 prevRaddr 处的内容。
    read-during-write 与 realRen=false 的取值约定见 D2/D3。 -/
def sramRawRead (s : SramState set way w) (j : Fin way) : BitVec w :=
  s.mem s.prevRaddr j

/-- bypass 命中（:120-127 的 need_bypass，逐 way）：非 singlePort 且上一拍
    读写同址且该 way 在写掩码内。 -/
def sramBypassHit (cfg : SramCfg) (s : SramState set way w) (j : Fin way) : Bool :=
  !cfg.singlePort && s.prevNeedCheck && (s.prevWaddr == s.prevRaddr) &&
    ((s.prevWmask >>> j.val) &&& 1#way = 1#way)

/-- bypass 数据（:128-129）：bypassWrite=true 前递写数据；否则 LFSR 值（Q1）。 -/
def sramBypassData (cfg : SramCfg) (s : SramState set way w) (j : Fin way) : BitVec w :=
  if cfg.bypassWrite then s.prevWdata j else (s.lfsr j).setWidth w

/-- mem_rdata（:131-136）。 -/
def sramMemRdata (cfg : SramCfg) (s : SramState set way w) (j : Fin way) : BitVec w :=
  if sramBypassHit cfg s j then sramBypassData cfg s j else sramRawRead s j

/-- io.r.resp.data（:139-142）：holdRead 时 en=prevRealRen 直通、否则保持。 -/
def sramRespData (cfg : SramCfg) (s : SramState set way w) (j : Fin way) : BitVec w :=
  if cfg.holdRead then
    if s.prevRealRen then sramMemRdata cfg s j else s.holdData j
  else sramMemRdata cfg s j

/-- 单拍转移（:99-144）。LFSR 每拍递增（D4）；holdData 的 RegEnable
    条件 en = prevRealRen（Hold.scala:18，仅 holdRead 时可观测）。
    D10：四个表字段经 `Array.ofFn` 逐点物化（构造时即逐槽求值，不留跨拍
    闭包）；mem 无写拍、holdData 无更新拍直接共享旧数组（O(1)）。
    逐点语义与原闭包版逐项相同（写后读引理 sramStep_mem 等钉死）。 -/
def sramStep (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w) :
    SramState set way w :=
  { memArr := if sramWen cfg s i then
        Array.ofFn fun a => Array.ofFn fun j => sramMemN cfg s i a j
      else s.memArr
    holdDataArr := if s.prevRealRen then
        Array.ofFn fun j => sramMemRdata cfg s j
      else s.holdDataArr
    prevRealRen := sramRealRen cfg s i
    prevNeedCheck := i.rValid && i.wValid
    prevWaddr := i.wAddr
    prevRaddr := i.rAddr
    prevWmask := i.wMask
    prevWdataArr := Array.ofFn i.wData
    lfsrArr := Array.ofFn fun j => sramLfsrStep (s.lfsr j)
    resetBusy := if sramResetBusy cfg s then !(s.resetSet.val == set - 1) else s.resetBusy
    resetSet := if sramResetBusy cfg s then s.resetSet + 1 else s.resetSet }

/-- 多拍执行。 -/
def sramRun (cfg : SramCfg) (s : SramState set way w) (is : List (SramIn set way w)) :
    SramState set way w :=
  is.foldl (sramStep cfg) s

/- 求值性能对照（第 21 波，2026-08-28；探针 /tmp/sramprobe：Old = 改造前函数
   字段版快照、New = 本文件 Array 版，同一文件内 verbatim 双份编译为原生二
   进制；同一混合轨迹——写/读/同址读写按拍轮换，cfg = sramCfgICacheTag
   （holdRead + LFSR 旁路），set=256 way=2 w=32，每拍 sramStep + 深读
   mem/holdData/lfsr/respData 四字段累计校验和，IO.monoMsNow 计时）。
   改造前（Fin … → … 函数字段，sramUpd/lfsr 闭包链跨拍重入）：
     n=1000 → 205ms，n=2000 → 819ms，n=4000 → 3326ms，n=8000 → 13263ms，
     n=16000 → 55215ms（每翻倍 ×4.0-4.2，实测 ~0.22µs/拍² 二次尾项——
     与第 20 波 agent-41 在整机轨迹中观测的 ~0.1µs/拍² 同量级同机制）。
   改造后（本文件，Array.ofFn 逐点物化 + 无写拍共享旧数组）：
     n=1000 → 17ms，n=2000 → 33ms，n=4000 → 65ms，n=8000 → 129ms，
     n=16000 → 260ms（每翻倍 ×2.0，严格线性 ~16µs/拍；n=16000 处提速 212×，
     残留为写拍 ofFn 物化的 O(set×way) 线性成本）。
   行为保持交叉验证：两版 n=1000/2000/4000/8000/16000 校验和逐项一致。 -/

/-- ofFn 物化表的回读（表尺寸恒 n，Fin n 索引必在界内）——Array 化后
    "写后读"的基础引理（同 ICache 的 icRd_ofFn、WarpScheduler 的 wsRd8_wr8_self）。 -/
@[simp] theorem sramRd_ofFn (f : Fin n → α) (e : Fin n) (d : α) :
    (Array.ofFn f).getD e.val d = f e := by
  simp [Array.getD_eq_getD_getElem?]

/-- 写后读（mem 视图）：step 后的阵列视图 = sramMemN（与原闭包版逐点一致；
    无写拍共享旧数组，视图不变）。 -/
@[simp] theorem sramStep_mem (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (a : Fin set) (j : Fin way) :
    (sramStep cfg s i).mem a j = sramMemN cfg s i a j := by
  by_cases hw : sramWen cfg s i = true
  · simp [SramState.mem, sramStep, hw]
  · simp [SramState.mem, sramStep, hw, sramMemN]

/-- 写后读（holdData 视图）：prevRealRen 拍更新为 mem_rdata，否则保持。 -/
@[simp] theorem sramStep_holdData (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) (j : Fin way) :
    (sramStep cfg s i).holdData j =
      if s.prevRealRen then sramMemRdata cfg s j else s.holdData j := by
  by_cases hp : s.prevRealRen = true <;>
    simp [SramState.holdData, sramStep, hp]

/-- 写后读（prevWdata 视图）：RegNext 直通输入。 -/
@[simp] theorem sramStep_prevWdata (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) (j : Fin way) :
    (sramStep cfg s i).prevWdata j = i.wData j := by
  simp [SramState.prevWdata, sramStep]

/-- 写后读（lfsr 视图）：每拍递增（D4）。 -/
@[simp] theorem sramStep_lfsr (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) (j : Fin way) :
    (sramStep cfg s i).lfsr j = sramLfsrStep (s.lfsr j) := by
  simp [SramState.lfsr, sramStep]

-- 扁平字段的投影引理（rfl）
@[simp] theorem sramStep_prevRealRen (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) :
    (sramStep cfg s i).prevRealRen = sramRealRen cfg s i := rfl
@[simp] theorem sramStep_prevNeedCheck (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) :
    (sramStep cfg s i).prevNeedCheck = (i.rValid && i.wValid) := rfl
@[simp] theorem sramStep_prevWaddr (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) : (sramStep cfg s i).prevWaddr = i.wAddr := rfl
@[simp] theorem sramStep_prevRaddr (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) : (sramStep cfg s i).prevRaddr = i.rAddr := rfl
@[simp] theorem sramStep_prevWmask (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) : (sramStep cfg s i).prevWmask = i.wMask := rfl
@[simp] theorem sramStep_resetBusy (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) :
    (sramStep cfg s i).resetBusy =
      (if sramResetBusy cfg s then !(s.resetSet.val == set - 1) else s.resetBusy) := rfl
@[simp] theorem sramStep_resetSet (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) :
    (sramStep cfg s i).resetSet =
      (if sramResetBusy cfg s then s.resetSet + 1 else s.resetSet) := rfl

end SramModel

/- ========================================================================= -/
/- 3. 符号化定理                                                              -/
/- ========================================================================= -/

section SramTheorems

variable {set way w : Nat} [NeZero set]

/-- waymask 选择性：命中 way 写入新值（:113-114）。 -/
theorem sramWriteMem_masked (mem : Fin set → Fin way → BitVec w) (a : Fin set)
    (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way)
    (hm : (wm >>> j.val) &&& 1#way = 1#way) :
    sramWriteMem mem a wd wm a j = wd j := by
  simp [sramWriteMem, sramUpd, hm]

/-- waymask 选择性：未命中 way 保持原值。 -/
theorem sramWriteMem_unmasked (mem : Fin set → Fin way → BitVec w) (a : Fin set)
    (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way)
    (hm : (wm >>> j.val) &&& 1#way ≠ 1#way) :
    sramWriteMem mem a wd wm a j = mem a j := by
  simp [sramWriteMem, sramUpd, hm]

/-- 写后读异址：其他 set 不受影响。 -/
theorem sramWriteMem_diff_set (mem : Fin set → Fin way → BitVec w) (a b : Fin set)
    (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way) (h : b ≠ a) :
    sramWriteMem mem a wd wm b j = mem b j := by
  simp [sramWriteMem, sramUpd_of_ne _ _ _ _ h]

/-- w.req.ready 恒 true（:144）。 -/
theorem sram_wready_true : sramWRdy = true := rfl

/-- 复位期间 r.req.ready = false（:143）。 -/
theorem sram_rready_reset (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (h : sramResetBusy cfg s = true) : sramRRdy cfg s i = false := by
  simp [sramRRdy, h]

/-- singlePort：有写（含复位强制写）则读口不 ready（:109,:143）。 -/
theorem sram_rready_singlePort_wen (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (hsp : cfg.singlePort = true) (hw : i.wValid = true) : sramRRdy cfg s i = false := by
  simp [sramRRdy, sramWen, hsp, hw]

/-- singlePort 读写互斥：realRen 成立 ⇒ 当拍无写（:109）。 -/
theorem sram_realRen_singlePort (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (hsp : cfg.singlePort = true) (h : sramRealRen cfg s i = true) :
    sramWen cfg s i = false := by
  simp [sramRealRen, hsp] at h
  exact h.2

/-- 非复位状态经任意一拍仍非复位（复位只会自行结束）。 -/
theorem sramResetBusy_step_false (cfg : SramCfg) (s : SramState set way w)
    (i : SramIn set way w) (h : sramResetBusy cfg s = false) :
    sramResetBusy cfg (sramStep cfg s i) = false := by
  unfold sramResetBusy at h ⊢
  simp [sramResetBusy, h]

/-- 复位拍：写入 resetSet/全 0/全 way，与用户输入无关（Q2：复位期间的用户写
    被静默丢弃）。 -/
theorem sram_resetStep_mem (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (h : sramResetBusy cfg s = true) :
    (sramStep cfg s i).mem = sramWriteMem s.mem s.resetSet (fun _ => 0) (BitVec.allOnes way) := by
  funext a j
  simp [sramMemN, sramWen, h]

/-- 复位推进：未到最后一拍则 resetSet+1 且保持 busy（:101 Counter）。 -/
theorem sram_resetStep_progress (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (h : sramResetBusy cfg s = true) (hnotlast : s.resetSet.val ≠ set - 1) :
    (sramStep cfg s i).resetBusy = true ∧
    (sramStep cfg s i).resetSet.val = s.resetSet.val + 1 := by
  have hv := s.resetSet.isLt
  have hlt : s.resetSet.val + 1 < set := by omega
  constructor
  · simp [h, hnotlast]
  · show (if sramResetBusy cfg s then s.resetSet + 1 else s.resetSet).val = s.resetSet.val + 1
    rw [if_pos h, Fin.val_add]
    have h1 : ((1 : Fin set)).val = 1 % set := rfl
    rw [h1, Nat.mod_eq_of_lt (by have := s.resetSet.isLt; omega : 1 < set),
        Nat.mod_eq_of_lt hlt]

/-- 复位收尾：resetSet = set-1 的拍末清 busy（:102 resetFinish）。 -/
theorem sram_resetStep_finish (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (h : sramResetBusy cfg s = true) (hlast : s.resetSet.val = set - 1) :
    (sramStep cfg s i).resetBusy = false := by
  simp [h, hlast]

/-- 干净读的 MemLaws 式刻画（:116,:131-142）：无冲突时，发起读后一拍的
    respData = 当前阵列内容（holdRead 与否皆然——发起读使 prevRealRen=1，
    HoldUnless 直通 mem_rdata）。 -/
theorem sram_read_clean (cfg : SramCfg) (s : SramState set way w)
    (b : Fin set) (j : Fin way) (hres : sramResetBusy cfg s = false) :
    sramRespData cfg (sramStep cfg (sramStep cfg s sramInIdle) (sramInRead b)) j = s.mem b j := by
  obtain ⟨cr, ch, csp, cbp⟩ := cfg
  cases cr <;> cases ch <;> cases csp <;> cases cbp <;>
    simp_all [sramRespData, sramMemRdata, sramBypassHit, sramRawRead,
      sramMemN, sramWen, sramRealRen, sramInIdle, sramInRead, sramResetBusy]

/-- 写后读（跨拍、无冲突）：写后隔拍读回 = 写入后的阵列内容。 -/
theorem sram_read_after_write (cfg : SramCfg) (s : SramState set way w)
    (a b : Fin set) (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way)
    (hres : sramResetBusy cfg s = false) :
    sramRespData cfg (sramStep cfg (sramStep cfg s (sramInWrite a wd wm)) (sramInRead b)) j =
      sramWriteMem s.mem a wd wm b j := by
  obtain ⟨cr, ch, csp, cbp⟩ := cfg
  cases cr <;> cases ch <;> cases csp <;> cases cbp <;>
    simp_all [sramRespData, sramMemRdata, sramBypassHit, sramRawRead,
      sramMemN, sramWen, sramRealRen, sramInWrite, sramInRead, sramResetBusy,
      sramWriteMem]

/-- 写后读同址 + way 命中：读回写入值。 -/
theorem sram_read_after_write_masked (cfg : SramCfg) (s : SramState set way w)
    (a : Fin set) (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way)
    (hres : sramResetBusy cfg s = false) (hm : (wm >>> j.val) &&& 1#way = 1#way) :
    sramRespData cfg (sramStep cfg (sramStep cfg s (sramInWrite a wd wm)) (sramInRead a)) j =
      wd j := by
  rw [sram_read_after_write cfg s a a wd wm j hres, sramWriteMem_masked s.mem a wd wm j hm]

/-- bypassWrite=true 前递（:120-130, bypass 命中情形）：同拍同址读写，
    下一拍读出 = 写入数据（对掩码命中的 way）。DCache tag/ShareMem/L2 Dir
    配置的正确性支柱。 -/
theorem sram_bypass_forward (cfg : SramCfg) (s : SramState set way w)
    (a : Fin set) (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way)
    (hres : sramResetBusy cfg s = false) (hsp : cfg.singlePort = false)
    (hbp : cfg.bypassWrite = true) (hm : (wm >>> j.val) &&& 1#way = 1#way) :
    sramRespData cfg (sramStep cfg s (sramInRW a wd wm)) j = wd j := by
  obtain ⟨cr, ch, csp, cbp⟩ := cfg
  cases cr <;> cases ch <;> cases csp <;> cases cbp <;>
    simp_all [sramRespData, sramMemRdata, sramBypassHit, sramBypassData,
      sramRealRen, sramInRW, sramResetBusy]

/-- Q1 钉死（bypassWrite=false && dual-port）：同拍同址读写，下一拍读出 =
    递增后的 LFSR 值（与写入数据、原数据均无关）。 -/
theorem sram_lfsr_bypass (cfg : SramCfg) (s : SramState set way w)
    (a : Fin set) (wd : Fin way → BitVec w) (wm : BitVec way) (j : Fin way)
    (hres : sramResetBusy cfg s = false) (hsp : cfg.singlePort = false)
    (hbp : cfg.bypassWrite = false) (hm : (wm >>> j.val) &&& 1#way = 1#way) :
    sramRespData cfg (sramStep cfg s (sramInRW a wd wm)) j =
      (sramLfsrStep (s.lfsr j)).setWidth w := by
  obtain ⟨cr, ch, csp, cbp⟩ := cfg
  cases cr <;> cases ch <;> cases csp <;> cases cbp <;>
    simp_all [sramRespData, sramMemRdata, sramBypassHit, sramBypassData,
      sramRealRen, sramInRW, sramResetBusy]

/-- holdRead 保持性（:139, Hold.scala:18）：读接受（prevRealRen=1）后，只要
    下一拍不再发读（rValid=0），respData 保持为刚读出的值。 -/
theorem sram_hold_holds (cfg : SramCfg) (s : SramState set way w) (i : SramIn set way w)
    (j : Fin way)
    (hh : cfg.holdRead = true) (hpr : s.prevRealRen = true) (hrv : i.rValid = false) :
    sramRespData cfg (sramStep cfg s i) j = sramRespData cfg s j := by
  obtain ⟨cr, ch, csp, cbp⟩ := cfg
  cases cr <;> cases ch <;> cases csp <;> cases cbp <;>
    simp_all [sramRespData, sramMemRdata, sramBypassHit, sramBypassData,
      sramRawRead, sramRealRen]

end SramTheorems

/- ========================================================================= -/
/- 4. 具体数值测试（set=4, way=2, w=32；多拍轨迹一律 native_decide）          -/
/- ========================================================================= -/

section SramTests

/-- 测试写数据：way0 = 0xAAAA0000，way1 = 0xBBBB1111。 -/
def sramTdA : Fin 2 → BitVec 32 := fun j => if j.val = 0 then 0xAAAA0000#32 else 0xBBBB1111#32

/- ---- 测试 A：sramCfgDCacheTag（holdRead + bypassWrite，L1TagAccess.scala:115 型） ---- -/

def sramTA1 := sramStep sramCfgDCacheTag (sramInit 4 2 32) (sramInWrite ⟨1, by decide⟩ sramTdA 0b01#2)
def sramTA2 := sramStep sramCfgDCacheTag sramTA1 (sramInRead ⟨1, by decide⟩)
def sramTA3 := sramStep sramCfgDCacheTag sramTA2 sramInIdle

-- 写后读：way0 命中掩码得新值，way1 未命中保持初值
theorem sramT_read_after_write :
    sramRespData sramCfgDCacheTag sramTA2 ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    sramRespData sramCfgDCacheTag sramTA2 ⟨1, by decide⟩ = 0#32 := by
  native_decide

-- holdRead：无新读时 respData 保持
theorem sramT_hold :
    sramRespData sramCfgDCacheTag sramTA3 ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    sramRespData sramCfgDCacheTag sramTA3 ⟨1, by decide⟩ = 0#32 := by
  native_decide

-- 异址读：读到初值（未被写污染）
theorem sramT_read_diff_set :
    sramRespData sramCfgDCacheTag
      (sramStep sramCfgDCacheTag sramTA1 (sramInRead ⟨2, by decide⟩)) ⟨0, by decide⟩ = 0#32 := by
  native_decide

-- bypass 前递：同拍同址读写，way0 读出写入值，way1（掩码外）读出原值
theorem sramT_bypass_forward :
    sramRespData sramCfgDCacheTag
      (sramStep sramCfgDCacheTag (sramInit 4 2 32)
        (sramInRW ⟨1, by decide⟩ sramTdA 0b01#2)) ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    sramRespData sramCfgDCacheTag
      (sramStep sramCfgDCacheTag (sramInit 4 2 32)
        (sramInRW ⟨1, by decide⟩ sramTdA 0b01#2)) ⟨1, by decide⟩ = 0#32 := by
  native_decide

/- ---- 测试 B：sramCfgICacheTag（holdRead && !bypassWrite → LFSR，Q1） ---- -/

def sramTB1 := sramStep sramCfgICacheTag (sramInit 4 2 32) (sramInRW ⟨1, by decide⟩ sramTdA 0b01#2)

-- 同拍同址读写：掩码命中 way 读出 LFSR 值 0x43B2A190（既非写入值也非原值）；
-- 写入本身不受影响（mem 中是新值，后续干净读可取回）
theorem sramT_lfsr_bypass :
    sramRespData sramCfgICacheTag sramTB1 ⟨0, by decide⟩ = 0x43B2A190#32 ∧
    sramRespData sramCfgICacheTag sramTB1 ⟨0, by decide⟩ ≠ sramTdA ⟨0, by decide⟩ ∧
    sramTB1.mem ⟨1, by decide⟩ ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    sramRespData sramCfgICacheTag sramTB1 ⟨1, by decide⟩ = 0#32 := by
  native_decide

/- ---- 测试 C：sramCfgSinglePort（singlePort 互斥；WithArbiter 内配置，死代码 D7） ---- -/

-- 同拍读写：写优先，读口不 ready、realRen 不成立
theorem sramT_singlePort_block :
    sramRRdy sramCfgSinglePort (sramInit 4 2 32)
      (sramInRW ⟨1, by decide⟩ sramTdA 0b11#2) = false ∧
    sramRealRen sramCfgSinglePort (sramInit 4 2 32)
      (sramInRW ⟨1, by decide⟩ sramTdA 0b11#2) = false ∧
    sramWRdy = true := by
  native_decide

-- 单端口写后隔拍读正常
theorem sramT_singlePort_raw :
    sramRespData sramCfgSinglePort
      (sramStep sramCfgSinglePort
        (sramStep sramCfgSinglePort (sramInit 4 2 32) (sramInWrite ⟨1, by decide⟩ sramTdA 0b01#2))
        (sramInRead ⟨1, by decide⟩)) ⟨0, by decide⟩ = 0xAAAA0000#32 := by
  native_decide

/- ---- 测试 D：sramCfgDCacheDirty（shouldReset=true，L1TagAccess.scala:209 型） ---- -/

/-- 上电脏数据状态（验证复位清零语义；真实 SRAM 上电未定，此处取定值以观测清零）。
    D10：视图与原 `fun _ _ => 0xDEADBEEF` 逐点相同。 -/
def sramTDInit : SramState 4 2 32 :=
  { sramInit 4 2 32 with memArr := Array.replicate 4 (Array.replicate 2 0xDEADBEEF#32) }

def sramTD1 := sramStep sramCfgDCacheDirty sramTDInit sramInIdle
def sramTD2 := sramStep sramCfgDCacheDirty sramTD1 sramInIdle
def sramTD3 := sramStep sramCfgDCacheDirty sramTD2 sramInIdle
def sramTD4 := sramStep sramCfgDCacheDirty sramTD3 sramInIdle

-- 复位共 set=4 拍：期间 r.req.ready 恒低
theorem sramT_reset_rdy_low :
    sramRRdy sramCfgDCacheDirty sramTDInit sramInIdle = false ∧
    sramRRdy sramCfgDCacheDirty sramTD1 sramInIdle = false ∧
    sramRRdy sramCfgDCacheDirty sramTD2 sramInIdle = false ∧
    sramRRdy sramCfgDCacheDirty sramTD3 sramInIdle = false := by
  native_decide

-- 4 拍后复位完成：busy 清、全阵列清零、读口 ready
theorem sramT_reset_done :
    sramTD4.resetBusy = false ∧ (∀ a j, sramTD4.mem a j = 0#32) ∧
    sramRRdy sramCfgDCacheDirty sramTD4 sramInIdle = true := by
  native_decide

-- 复位完成后读出 0
theorem sramT_reset_read_zero :
    sramRespData sramCfgDCacheDirty
      (sramStep sramCfgDCacheDirty (sramStep sramCfgDCacheDirty sramTD4 sramInIdle)
        (sramInRead ⟨2, by decide⟩)) ⟨0, by decide⟩ = 0#32 := by
  native_decide

-- Q2：复位最后一拍的用户写（写 set0 —— 该 set 已于复位第 0 拍清零，若写生效
-- 会留下 0xAAAA）被静默丢弃
theorem sramT_reset_drop_write :
    (∀ a j, (sramRun sramCfgDCacheDirty sramTDInit
      [sramInIdle, sramInIdle, sramInIdle,
       sramInWrite ⟨0, by decide⟩ (fun _ => 0xAAAA5555#32) 0b11#2]).mem a j = 0#32) := by
  native_decide

end SramTests

/- ---- 公理审计（native_decide 定理含 Lean.ofReduceBool，属预期） ---- -/

#print axioms sram_read_clean
#print axioms sram_read_after_write
#print axioms sram_bypass_forward
#print axioms sram_lfsr_bypass
#print axioms sram_hold_holds
#print axioms sram_resetStep_mem
#print axioms sramT_lfsr_bypass

end Ventus.Mem
