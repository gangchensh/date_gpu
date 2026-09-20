/- ========================================================================= -/
/-                     Arith/RegFile.lean                                    -/
/-  寄存器堆（regfile.scala）的 Lean 4 模型、测试与证明                        -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/regfile.scala      -/
/-    （RegFileBank 标量 bank :18-39；FloatRegFileBank 向量 bank :51-66；      -/
/-      ImmGen 立即数生成器 :97-116；unifiedBank :67-93 为死代码不建模）       -/
/-  例化点（活代码判定）：                                                     -/
/-    RegFileBank      ← operandCollector.scala:532（×num_bank）              -/
/-    FloatRegFileBank ← operandCollector.scala:531（×num_bank）              -/
/-    ImmGen           ← operandCollector.scala:83                            -/
/-  参数（top/parameters.scala，已核实）：num_warp=8(:8) num_thread=32(:9)     -/
/-    num_bank=4(:18) num_vgpr=1024(:20) num_sgpr=2048(:21)                  -/
/-    depth_regBank=log2Ceil(1024/4)=8(:22) xLen=32(:47)                     -/
/-    NUMBER_VGPR_SLOTS=num_vgpr(:139) NUMBER_SGPR_SLOTS=num_sgpr(:140)      -/
/-  IMM_* 常量（pipeline/DecodeUnit.scala:42-52 的 object IDecode，          -/
/-    注意任务书说的 Instructions.scala 有误，实际在 DecodeUnit.scala）：      -/
/-    IMM_I=0 IMM_S=1 IMM_B=2 IMM_U=3 IMM_2=4 IMM_J=5 IMM_V=6 IMM_Z=7        -/
/-    IMM_S11=8 IMM_L11=9                                                    -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 只建模 !GVM_ENABLED 分支（regfile.scala:23-30）。GVM_ENABLED 默认      -/
/-      false（parameters.scala:14，环境变量控制）；GVM 分支（:31-38，         -/
/-      RegInit 数组 + all_regs 观测口）不建模。                               -/
/-  D2. 标量 bank 物理深度 = NUMBER_SGPR_SLOTS/num_bank = 512（:24），但      -/
/-      rsidx/rdidx 宽度为 depth_regBank=8 位（:10-12，源自 num_vgpr 而非     -/
/-      num_sgpr），只能寻址低 256 项（见 Q3）。模型取可达地址空间             -/
/-      RegFile 256 32（复用 Ventus.Base.Defs 的 rf_read/rf_write/            -/
/-      rf_read_write_same/rf_read_write_diff），对全部可达行为无损。          -/
/-      向量 bank 物理深度 = 1024/4 = 256（:53），8 位索引恰好覆盖。           -/
/-  D3. SyncReadMem 未初始化地址的读建模为全 0（rfSInit/rfVInit 用 rf_zero）， -/
/-      与 SIMT/BranchJoin.lean 的 D3 惯例一致；Chisel 实际为未定值，          -/
/-      正确性依赖"读前必有写"的上层协议。                                     -/
/-  D4. SyncReadMem 时序语义：单写端口单读端口、1 拍读延迟。建模为状态寄存器   -/
/-      readData（读数据输出寄存器，取写前旧值）+ rdReg（RegNext(io.rd)）+    -/
/-      bypass（RegNext((rsidx===rdidx)&rdwen)，:22）。同拍同址读写由旁路      -/
/-      覆盖（:25），同拍异址读旧值——无双端口仲裁属 SyncReadMem 正常语义。   -/
/-  D5. unifiedBank（:67-93）为死代码（全仓无例化，已 grep 确认），不建模；   -/
/-      其体内缺陷记入 Q4。                                                   -/
/-  D6. ImmGen 的 SInt 符号扩展统一建模为 BitVec.signExtend 32：MuxLookup     -/
/-      各值宽度 5-32 不等（SInt），结果宽度取最大 32（Uimm/Zimm），各分支     -/
/-      符号扩展到 32 位后 io.out 取 asUInt（:115）。默认分支 Iimm & -2.S     -/
/-      （:114）：-2.S 符号扩展后与 Iimm 按位与 = 清 bit0，定理               -/
/-      rfImm_default_quirk 钉死此 quirk。                                    -/
/-  D7. imm_ext 为 7 位（:93，MSB 打包 exti_valid），:108 的 imm_ext(6) 即     -/
/-      MSB；tail(1) 丢弃 MSB 取低 6 位（Cat 高位），建模为 extractLsb' 0 6。 -/
/-  D8. v0 恒全 1（:61 WireInit VecInit.fill(~0.U)，:59-60 注释自承 v0 未     -/
/-      使用，为省一个读端口而移除），建模为常量行 rfVV0。                     -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类候选】FloatRegFileBank 旁路与写掩码发散（:57-58 vs :63-65）。      -/
/-      bypassSignal 只看 (rsidx===rdidx)&rdwen，不看 rdwmask。触发序列：     -/
/-        拍 N：rdwen=1, rdidx=X, rdwmask=m（m(t)=false）, rd=v               -/
/-              （v(t) ≠ mem[X](t)，即对被掩 lane 写入新值）；                -/
/-        拍 N+1：rsidx=X → io.rs = RegNext(rd) = v（全部 32 lane 都是新值）； -/
/-        但 mem[X] 只更新了 m 开启的 lane（:63-65 掩码写），lane t 仍为旧值； -/
/-        拍 N+2 再读 X → lane t 读出旧值，与拍 N+1 旁路读出的 v(t) 不一致。  -/
/-      定理 rfV_bypass_mem_diverge 钉死该机制；数值证据见测试 V3/V4。        -/
/-      是否有害取决于消费方：operandCollector 读出向量操作数后是否按同一      -/
/-      执行掩码使用被掩 lane。若执行单元对被掩 lane 的结果弃之不用则无害；   -/
/-      若存在"用旧值合并写回"的路径（如掩码指令的 undisturbed 语义），       -/
/-      则旁路前递的新值会污染。本文件范围内无法判定，上报主会话定性。        -/
/-  Q2【I 类，面积浪费】RegFileBank 有两个同名 `val regs = SyncReadMem(...)`  -/
/-      （:20 外层、:24 内层遮蔽）。外层无条件例化但从不连接（:25 用的是内    -/
/-      层），两种模式下都展开成一块无连接的 512×32 SRAM。死硬件，面积浪费。  -/
/-  Q3【I 类候选】标量 bank 地址宽度不足。SyncReadMem 深度 512（:20/:24），  -/
/-      但 rsidx/rdidx 仅 8 位（:10-12，depth_regBank=log2Ceil(num_vgpr/      -/
/-      num_bank)=8，parameters.scala:22 按 VGPR 计算却用于 SGPR bank）——    -/
/-      每个标量 bank 高 256 项（地址 256-511）永远不可达（面积浪费），且     -/
/-      写回侧 operandCollector.scala:596,606 的 wbScaBankAddr 同为 8 位，    -/
/-      (sgpr_base(wid)>>2)+(reg_idxw>>2) ≥ 256 时回绕别名到低 256 项。       -/
/-      sgpr 总量 2048（:21），只要任一 warp 的 sgpr_base ≥ 1024 即可触发。   -/
/-      是否可达取决于 sgpr 分配上限，上报主会话结合 warp 分配模块判定。      -/
/-      （向量 bank 无此问题：256 深度与 8 位索引恰好匹配。）                -/
/-  Q4【I 类，死代码内缺陷】unifiedBank（:67-93，无例化）：:73/:75 的          -/
/-      regs.read(io.rsidx)(num_thread+1) 对 Vec(num_thread+1, ·) 越界       -/
/-      （合法下标 0..num_thread）；scalar 分支只驱动 io.rs(0)，其余 31       -/
/-      lane 未驱动；switch 无默认分支、internalMask 在 scalar 分支未赋值     -/
/-      → 若被例化将推断出锁存器/越界硬件。模块已死，记录在案防复活。        -/
/-  Q5【观察】ImmGen 默认分支（:114）：sel=10-15（IMM_* 仅 0-9）时输出       -/
/-      Iimm 清 bit0。sel 来自译码表（DecodeUnit.scala 各 LUT 的 IMM_* 列    -/
/-      均 ≤ 9），正常路径不可达；作为容错 quirk 钉死（rfImm_default_quirk）， -/
/-      非 bug。                                                              -/
/-  Q6【观察】两个 bank 的读数据寄存器取"写前旧值"，同拍同址读写依赖旁路      -/
/-      得到新值（:22,:25,:57-58）——SyncReadMem 标准用法，未见仲裁缺陷。     -/
/-      标量 bank 无写掩码，不存在 Q1 类发散。                                -/
/-  Q7【观察】Imm2 = inst(24,20).asSInt（:106）：shamt ≥ 16（inst(24)=1）时    -/
/-      立即数符号扩展为负（如 SLLI shamt=31 → 0xFFFFFFFF）。消费方           -/
/-      ScalarALU 取 in2 低 5 位作 shamt（ALU.scala:84），符号扩展不影响      -/
/-      结果；数值现状由测试 I7 钉死，非 bug。                                -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 常量                                                                    -/
/- =========================================================================-/

/-- IMM_* 选择码（DecodeUnit.scala:42-52，object IDecode） -/
def rfIMM_I   : BitVec 4 := 0   -- DecodeUnit.scala:42
def rfIMM_S   : BitVec 4 := 1   -- DecodeUnit.scala:43
def rfIMM_B   : BitVec 4 := 2   -- DecodeUnit.scala:44
def rfIMM_U   : BitVec 4 := 3   -- DecodeUnit.scala:45
def rfIMM_2   : BitVec 4 := 4   -- DecodeUnit.scala:46
def rfIMM_J   : BitVec 4 := 5   -- DecodeUnit.scala:47
def rfIMM_V   : BitVec 4 := 6   -- DecodeUnit.scala:49
def rfIMM_Z   : BitVec 4 := 7   -- DecodeUnit.scala:50
def rfIMM_S11 : BitVec 4 := 8   -- DecodeUnit.scala:51
def rfIMM_L11 : BitVec 4 := 9   -- DecodeUnit.scala:52

/- ========================================================================= -/
/- 2. RegFileBank 标量 bank（regfile.scala:18-39，!GVM 分支 :23-30）           -/
/- =========================================================================-/

/-- 标量 bank 可达存储（见 D2：物理 512 深，8 位索引只达低 256 项） -/
abbrev RfSMem : Type := RegFile 256 32

/-- 输入（RegFileBankIO :8-16 去掉 GVM 的 all_regs） -/
structure RfSInputs where
  rsidx : BitVec 8    -- :10
  rdidx : BitVec 8    -- :12
  rd    : BitVec 32   -- :11
  rdwen : Bool        -- :13

/-- 状态：SyncReadMem 内容 + 三个输出寄存器（见 D4） -/
structure RfSState where
  mem      : RfSMem      -- :24 SyncReadMem
  readData : BitVec 32   -- :25 regs.read(io.rsidx) 的 1 拍延迟输出
  rdReg    : BitVec 32   -- :25 RegNext(io.rd)
  bypass   : Bool        -- :22 bypassSignal := RegNext((rsidx===rdidx)&rdwen)

/-- 初始状态：mem 未初始化建模为全 0（D3），输出寄存器上电值任意、取 0 -/
def rfSInit : RfSState := ⟨rf_zero 256 32, 0#32, 0#32, false⟩

/-- 单拍转移：读旧 mem（:25）、写 mem（:27-29）、三个寄存器更新 -/
def rfSStep (s : RfSState) (i : RfSInputs) : RfSState :=
  { mem      := if i.rdwen then rf_write s.mem i.rdidx.toFin i.rd else s.mem  -- :27-29
  , readData := rf_read s.mem i.rsidx.toFin                                    -- :25（写前旧值，D4）
  , rdReg    := i.rd                                                           -- :25 RegNext
  , bypass   := (i.rsidx == i.rdidx) && i.rdwen }                              -- :22

/-- 输出 io.rs（:25）：Mux(bypassSignal, RegNext(rd), regs.read(rsidx)) -/
def rfSOut (s : RfSState) : BitVec 32 :=
  if s.bypass then s.rdReg else s.readData

/-- 多拍运行 -/
def rfSRun (s : RfSState) (ins : List RfSInputs) : RfSState := ins.foldl rfSStep s

/- ========================================================================= -/
/- 3. FloatRegFileBank 向量 bank（regfile.scala:51-66）                        -/
/- =========================================================================-/

/-- 一个向量寄存器行：num_thread=32 个 32 位 lane -/
abbrev RfVRow : Type := Fin 32 → BitVec 32

/-- 按线程写掩码 rdwmask（:48） -/
abbrev RfVMask : Type := Fin 32 → Bool

/-- 向量 bank 存储：256 行（NUMBER_VGPR_SLOTS/num_bank=256，:53），8 位索引恰好 -/
abbrev RfVMem : Type := Fin 256 → RfVRow

/-- 存储行更新（元素为行，Base 的 rf_write 只到 Bits，故本地定义） -/
def rfVUpd (m : RfVMem) (i : Fin 256) (r : RfVRow) : RfVMem :=
  fun j => if i = j then r else m j

theorem rfVUpd_same (m : RfVMem) (i : Fin 256) (r : RfVRow) :
    rfVUpd m i r i = r := by simp [rfVUpd]

theorem rfVUpd_diff (m : RfVMem) (i j : Fin 256) (r : RfVRow) (h : i ≠ j) :
    rfVUpd m i r j = m j := by simp [rfVUpd, h]

/-- SyncReadMem 掩码写（:63-65）：掩码开启的 lane 取新值，关闭的保留旧值 -/
def rfVRowUpd (oldRow newRow : RfVRow) (mask : RfVMask) : RfVRow :=
  fun t => if mask t then newRow t else oldRow t

/-- 输入（FloatRegFileBankIO :41-50，unified=false 无 rsType） -/
structure RfVInputs where
  rsidx   : BitVec 8   -- :44
  rdidx   : BitVec 8   -- :46
  rd      : RfVRow     -- :45
  rdwen   : Bool       -- :47
  rdwmask : RfVMask    -- :48

/-- 状态：同标量 bank，readData/rdReg 为整行 -/
structure RfVState where
  mem      : RfVMem    -- :53
  readData : RfVRow    -- :58 regs.read(io.rsidx) 的 1 拍延迟输出
  rdReg    : RfVRow    -- :58 RegNext(io.rd)
  bypass   : Bool      -- :57

def rfVInit : RfVState := ⟨fun _ => rf_zero 32 32, rf_zero 32 32, rf_zero 32 32, false⟩

/-- 单拍转移（:57-65）：掩码写合并进 mem（:63-65），旁路寄存整行 rd（:58，见 Q1） -/
def rfVStep (s : RfVState) (i : RfVInputs) : RfVState :=
  { mem      := if i.rdwen
                then rfVUpd s.mem i.rdidx.toFin (rfVRowUpd (s.mem i.rdidx.toFin) i.rd i.rdwmask)
                else s.mem                                                     -- :63-65
  , readData := s.mem i.rsidx.toFin                                            -- :58（写前旧值，D4）
  , rdReg    := i.rd                                                           -- :58 RegNext(io.rd)
  , bypass   := (i.rsidx == i.rdidx) && i.rdwen }                              -- :57（不看 rdwmask，Q1）

/-- 输出 io.rs（:58） -/
def rfVOut (s : RfVState) : RfVRow :=
  if s.bypass then s.rdReg else s.readData

/-- 多拍运行 -/
def rfVRun (s : RfVState) (ins : List RfVInputs) : RfVState := ins.foldl rfVStep s

/-- io.v0 恒全 1（:61；v0 未使用，D8） -/
def rfVV0 : RfVRow := fun _ => 0xFFFFFFFF#32

/- ========================================================================= -/
/- 4. ImmGen 立即数生成器（regfile.scala:97-116，纯组合）                      -/
/- =========================================================================-/

/-- ImmGen 纯组合模型（:100-114）。各立即数切片见 D6/D7。 -/
def rfImmGen (sel : BitVec 4) (inst : BitVec 32) (immExt : BitVec 7) : BitVec 32 :=
  -- :100 Iimm = inst(31,20).asSInt（load, arithmetic, logic, jalr）
  let iimm := BitVec.signExtend 32 (inst.extractLsb' 20 12)
  -- :101 Simm = Cat(inst(31,25), inst(11,7)).asSInt（store）
  let simm := BitVec.signExtend 32 ((inst.extractLsb' 25 7) ++ (inst.extractLsb' 7 5))
  -- :102 Bimm = Cat(inst(31), inst(7), inst(30,25), inst(11,8), 0).asSInt（branch）
  let bimm := BitVec.signExtend 32
    ((inst.extractLsb' 31 1) ++ (inst.extractLsb' 7 1) ++
     (inst.extractLsb' 25 6) ++ (inst.extractLsb' 8 4) ++ 0#1)
  -- :103 Uimm = Cat(inst(31,12), 0.U(12.W))（lui, auipc；32 位无需扩展）
  let uimm := (inst.extractLsb' 12 20) ++ 0#12
  -- :104 Jimm = Cat(inst(31), inst(19,12), inst(20), inst(30,21), 0).asSInt（jal）
  let jimm := BitVec.signExtend 32
    ((inst.extractLsb' 31 1) ++ (inst.extractLsb' 12 8) ++
     (inst.extractLsb' 20 1) ++ (inst.extractLsb' 21 10) ++ 0#1)
  -- :105 Zimm = Cat(0.U(27.W), inst(19,15))（CSR I；高位全 0，符号扩展=零扩展）
  let zimm := BitVec.zeroExtend 32 (inst.extractLsb' 15 5)
  -- :106 Imm2 = inst(24,20).asSInt
  let imm2 := BitVec.signExtend 32 (inst.extractLsb' 20 5)
  -- :108 Vimm = Mux(imm_ext(6), Cat(imm_ext.tail(1), inst(19,15)).asSInt,
  --                              inst(19,15).asSInt)
  let vimm := if immExt.getLsbD 6
              then BitVec.signExtend 32 ((immExt.extractLsb' 0 6) ++ (inst.extractLsb' 15 5))
              else BitVec.signExtend 32 (inst.extractLsb' 15 5)
  -- :109 Iimm11L = inst(30,20).asSInt（注意：不含 inst(31)，见测试 I9）
  let i11l := BitVec.signExtend 32 (inst.extractLsb' 20 11)
  -- :110 Iimm11S = Cat(inst(30,25), inst(11,7)).asSInt
  let i11s := BitVec.signExtend 32 ((inst.extractLsb' 25 6) ++ (inst.extractLsb' 7 5))
  -- :114 MuxLookup(sel, Iimm & -2.S)（默认分支清 Iimm 的 bit0，见 D6/Q5）
  if sel = rfIMM_I then iimm
  else if sel = rfIMM_J then jimm
  else if sel = rfIMM_S then simm
  else if sel = rfIMM_B then bimm
  else if sel = rfIMM_U then uimm
  else if sel = rfIMM_2 then imm2
  else if sel = rfIMM_Z then zimm
  else if sel = rfIMM_V then vimm
  else if sel = rfIMM_L11 then i11l
  else if sel = rfIMM_S11 then i11s
  else iimm &&& 0xFFFFFFFE#32

/- ========================================================================= -/
/- 5. 数值回归测试（先测试；全部 `by decide`）                                 -/
/- =========================================================================-/

section RfRegressionTests

-- S1 写后下一拍：同址读旁路命中，前递新值
example : rfSOut (rfSStep rfSInit ⟨5#8, 5#8, 0xDEADBEEF#32, true⟩) = 0xDEADBEEF#32 := by decide
-- S2 再下一拍（无写）：读到 mem 中的值
example : rfSOut (rfSStep (rfSStep rfSInit ⟨5#8, 5#8, 0xDEADBEEF#32, true⟩)
    ⟨5#8, 0#8, 0#32, false⟩) = 0xDEADBEEF#32 := by decide
-- S3 同拍异址读写：读旧值（未初始化=0，D3），旁路不命中
example : rfSOut (rfSStep rfSInit ⟨7#8, 5#8, 0xDEADBEEF#32, true⟩) = 0#32 := by decide
-- S4 未初始化读为 0（D3 建模约定）
example : rfSOut (rfSStep rfSInit ⟨3#8, 0#8, 0#32, false⟩) = 0#32 := by decide
-- S5 两写两读互不干扰
example : rfSOut (rfSRun rfSInit
    [⟨5#8, 5#8, 0xAAAA#32, true⟩, ⟨7#8, 7#8, 0xBBBB#32, true⟩,
     ⟨5#8, 0#8, 0#32, false⟩]) = 0xAAAA#32 := by decide
example : rfSOut (rfSRun rfSInit
    [⟨5#8, 5#8, 0xAAAA#32, true⟩, ⟨7#8, 7#8, 0xBBBB#32, true⟩,
     ⟨7#8, 0#8, 0#32, false⟩]) = 0xBBBB#32 := by decide
-- S6 同址连续写：旁路前递最新值
example : rfSOut (rfSRun rfSInit
    [⟨5#8, 5#8, 0xAAAA#32, true⟩, ⟨5#8, 5#8, 0xBBBB#32, true⟩]) = 0xBBBB#32 := by decide

-- 向量 bank 测试场景：掩码只开 lane 0 与 lane 31
def rfVMask031 : RfVMask := fun t => decide (t.val = 0 ∨ t.val = 31)
def rfVRowNew : RfVRow := fun t => 0x1000#32 + BitVec.ofNat 32 t.val
/-- 拍 N：对地址 3 做掩码写（只开 lane 0/31），rd 全 lane 为新值 -/
def rfVS1 : RfVState := rfVStep rfVInit ⟨3#8, 3#8, rfVRowNew, true, rfVMask031⟩
/-- 拍 N+1：读地址 3（无写） -/
def rfVS2 : RfVState := rfVStep rfVS1 ⟨3#8, 0#8, rfVRowNew, false, rfVMask031⟩

-- V1 旁路命中：前递完整新行——包括掩码关闭的 lane 5（Q1 发散机制的第一步）
example : (rfVOut rfVS1) ⟨5, by decide⟩ = 0x1005#32 := by decide
example : (rfVOut rfVS1) ⟨0, by decide⟩ = 0x1000#32 := by decide
-- V2 mem 侧掩码合并：lane 0/31 更新为新值
example : (rfVOut rfVS2) ⟨0, by decide⟩ = 0x1000#32 := by decide
example : (rfVOut rfVS2) ⟨31, by decide⟩ = 0x101F#32 := by decide
-- V3 mem 侧掩码关闭的 lane 5 保留旧值（0）——与 V1 旁路读出的 0x1005 发散（Q1）
example : (rfVOut rfVS2) ⟨5, by decide⟩ = 0#32 := by decide
-- V4 发散的数值钉死：同一地址、相邻两拍，lane 5 先读出 0x1005 再读出 0
example : (rfVOut rfVS1) ⟨5, by decide⟩ ≠ (rfVOut rfVS2) ⟨5, by decide⟩ := by decide
-- V5 异址读写互不干扰；同拍异址读旧值
example : (rfVOut (rfVStep rfVInit ⟨4#8, 3#8, rfVRowNew, true, rfVMask031⟩)) ⟨0, by decide⟩
    = 0#32 := by decide
-- V6 v0 恒全 1（:61，D8）
example : rfVV0 ⟨7, by decide⟩ = 0xFFFFFFFF#32 := by decide
example : rfVV0 ⟨31, by decide⟩ = 0xFFFFFFFF#32 := by decide

-- ImmGen 测试向量（对照 RISC-V 立即数语义手算；指令字按字段拼装）
-- I1 IMM_I：ADDI x5,x6,-1 → imm=0xFFF 符号扩展
example : rfImmGen rfIMM_I 0xFFF30293#32 0#7 = 0xFFFFFFFF#32 := by decide
example : rfImmGen rfIMM_I 0x00530293#32 0#7 = 5#32 := by decide
-- I2 IMM_S：SW x5,-4(x6) → Cat(0x7F,0x1C)=0xFFC 符号扩展
example : rfImmGen rfIMM_S 0xFE532E23#32 0#7 = 0xFFFFFFFC#32 := by decide
-- I3 IMM_B：BEQ 偏移 -4 → Cat(1,1,0x3F,0xE,0)=0x1FFC（13 位）符号扩展
example : rfImmGen rfIMM_B 0xFE000EE3#32 0#7 = 0xFFFFFFFC#32 := by decide
example : rfImmGen rfIMM_B 0x00000463#32 0#7 = 8#32 := by decide   -- 偏移 +8
-- I4 IMM_U：LUI x5,0xABCDE → 高 20 位原样、低 12 位补 0
example : rfImmGen rfIMM_U 0xABCDE2B7#32 0#7 = 0xABCDE000#32 := by decide
-- I5 IMM_J：JAL 偏移 +256 与 -2
example : rfImmGen rfIMM_J 0x100002EF#32 0#7 = 0x00000100#32 := by decide
example : rfImmGen rfIMM_J 0xFFFFF2EF#32 0#7 = 0xFFFFFFFE#32 := by decide
-- I6 IMM_Z：CSRRSI uimm=0x1F，零扩展
example : rfImmGen rfIMM_Z 0x000FE2F3#32 0#7 = 31#32 := by decide
-- I7 IMM_2：SLLI shamt=31 → inst(24,20)=0b11111，5 位 asSInt 得 -1（inst(24) 是符号位，见 Q7）
example : rfImmGen rfIMM_2 0x01F31293#32 0#7 = 0xFFFFFFFF#32 := by decide
example : rfImmGen rfIMM_2 0x00F31293#32 0#7 = 15#32 := by decide
example : rfImmGen rfIMM_2 0x01031293#32 0#7 = 0xFFFFFFF0#32 := by decide
-- I8 IMM_V：imm_ext(6)=0 走 5 位 inst(19,15)；=1 走 11 位 Cat(imm_ext 低 6 位, inst(19,15))
example : rfImmGen rfIMM_V 0x01F31293#32 0#7 = 6#32 := by decide
example : rfImmGen rfIMM_V 0x01F31293#32 0x41#7 = 38#32 := by decide
example : rfImmGen rfIMM_V 0x00000293#32 0x7F#7 = 0xFFFFFFE0#32 := by decide
-- I9 IMM_L11：inst(30,20) 符号扩展；inst(31) 不参与（两词只差 bit31，结果相同）
example : rfImmGen rfIMM_L11 0xC0000293#32 0#7 = 0xFFFFFC00#32 := by decide
example : rfImmGen rfIMM_L11 0x40000293#32 0#7 = 0xFFFFFC00#32 := by decide
example : rfImmGen rfIMM_L11 0x15500093#32 0#7 = 0x155#32 := by decide
-- I10 IMM_S11：Cat(inst(30,25), inst(11,7)) 符号扩展
example : rfImmGen rfIMM_S11 0xFE532E23#32 0#7 = 0xFFFFFFFC#32 := by decide
example : rfImmGen rfIMM_S11 0x00000293#32 0#7 = 5#32 := by decide
-- I11 默认分支 quirk（:114，Q5）：sel=15/10 输出 Iimm 清 bit0
example : rfImmGen 0xF#4 0xFFF30293#32 0#7 = 0xFFFFFFFE#32 := by decide
example : rfImmGen 0xA#4 0x00530293#32 0#7 = 4#32 := by decide

end RfRegressionTests

/- ========================================================================= -/
/- 6. 正确性定理（后证明）                                                     -/
/- =========================================================================-/

/-- 展开 rfImmGen 及其常量的标准 simp 集（bv_decide 看不穿 def，须先展开） -/
macro "rfImm_unfold" : tactic =>
  `(tactic| simp only [rfImmGen, rfIMM_I, rfIMM_S, rfIMM_B, rfIMM_U, rfIMM_2,
    rfIMM_J, rfIMM_V, rfIMM_Z, rfIMM_S11, rfIMM_L11])

/-- 标量：写后下一拍同址读 → 旁路前递新值（:22,:25） -/
theorem rfS_bypass_next (s : RfSState) (a : BitVec 8) (v : BitVec 32) :
    rfSOut (rfSStep s ⟨a, a, v, true⟩) = v := by
  simp [rfSOut, rfSStep]

/-- 标量：写后两拍同址读 → 读到 mem 中的值（SyncReadMem 1 拍延迟，:25） -/
theorem rfS_read_after_write (s : RfSState) (a c : BitVec 8) (v x : BitVec 32) :
    rfSOut (rfSStep (rfSStep s ⟨a, a, v, true⟩) ⟨a, c, x, false⟩) = v := by
  simp [rfSOut, rfSStep, rf_read_write_same]

/-- 标量：同拍异址读写 → 读旧值，旁路不命中（D4） -/
theorem rfS_read_old_during_write (s : RfSState) (a b : BitVec 8) (v : BitVec 32)
    (h : a ≠ b) :
    rfSOut (rfSStep s ⟨a, b, v, true⟩) = rf_read s.mem a.toFin := by
  simp [rfSOut, rfSStep, beq_iff_eq, h]

/-- rfSStep 的 mem 投影（rfl，供 rw 使用） -/
theorem rfSStep_mem (s : RfSState) (i : RfSInputs) :
    (rfSStep s i).mem = if i.rdwen then rf_write s.mem i.rdidx.toFin i.rd else s.mem := rfl

/-- 标量：写不改其它地址（异地址读写互不干扰，复用 Base 的 rf_read_write_diff） -/
theorem rfS_write_preserves (s : RfSState) (i : RfSInputs) (a : BitVec 8)
    (h : a ≠ i.rdidx) :
    rf_read (rfSStep s i).mem a.toFin = rf_read s.mem a.toFin := by
  rw [rfSStep_mem]
  split
  · exact rf_read_write_diff _ _ _ _ (fun hc => h (BitVec.toFin_inj.mp hc.symm))
  · rfl

/-- 向量：写后下一拍同址读 → 旁路前递**完整新行**（:57-58；含掩码关闭 lane，Q1 机制一） -/
theorem rfV_bypass_forwards_full_row (s : RfVState) (a : BitVec 8) (v : RfVRow)
    (m : RfVMask) :
    rfVOut (rfVStep s ⟨a, a, v, true, m⟩) = v := by
  simp [rfVOut, rfVStep]

/-- 向量：写后两拍同址读 → 读到 mem 掩码合并行（:63-65；Q1 机制二，mem 侧正确） -/
theorem rfV_mem_masked_merge (s : RfVState) (a c : BitVec 8) (v x : RfVRow)
    (m m' : RfVMask) (t : Fin 32) :
    rfVOut (rfVStep (rfVStep s ⟨a, a, v, true, m⟩) ⟨a, c, x, false, m'⟩) t =
      (if m t then v t else s.mem a.toFin t) := by
  simp [rfVOut, rfVStep, rfVUpd, rfVRowUpd]

/-- Q1 发散定理：掩码写后，同址读在拍 N+1（旁路）与拍 N+2（mem）读到不同值。
    前提：lane t 被掩（m t = false）且新旧值在该 lane 不同。 -/
theorem rfV_bypass_mem_diverge (s : RfVState) (a c : BitVec 8) (v x : RfVRow)
    (m m' : RfVMask) (t : Fin 32)
    (hm : m t = false) (hne : v t ≠ s.mem a.toFin t) :
    rfVOut (rfVStep s ⟨a, a, v, true, m⟩) t ≠
      rfVOut (rfVStep (rfVStep s ⟨a, a, v, true, m⟩) ⟨a, c, x, false, m'⟩) t := by
  rw [rfV_bypass_forwards_full_row, rfV_mem_masked_merge]
  simp [hm, hne]

/-- 向量：同拍异址读写 → 读旧值 -/
theorem rfV_read_old_during_write (s : RfVState) (a b : BitVec 8) (v : RfVRow)
    (m : RfVMask) (h : a ≠ b) :
    rfVOut (rfVStep s ⟨a, b, v, true, m⟩) = s.mem a.toFin := by
  simp [rfVOut, rfVStep, beq_iff_eq, h]

/-- rfVStep 的 mem 投影（rfl，供 rw 使用） -/
theorem rfVStep_mem (s : RfVState) (i : RfVInputs) :
    (rfVStep s i).mem = if i.rdwen
      then rfVUpd s.mem i.rdidx.toFin (rfVRowUpd (s.mem i.rdidx.toFin) i.rd i.rdwmask)
      else s.mem := rfl

/-- 向量：写不改其它地址 -/
theorem rfV_write_preserves (s : RfVState) (i : RfVInputs) (a : BitVec 8)
    (h : a ≠ i.rdidx) (t : Fin 32) :
    (rfVStep s i).mem a.toFin t = s.mem a.toFin t := by
  rw [rfVStep_mem]
  split
  · rw [rfVUpd_diff _ _ _ _ (fun hc => h (BitVec.toFin_inj.mp hc.symm))]
  · rfl

/-- 掩码写逐 lane 语义：掩码开启取新值 -/
theorem rfVRowUpd_masked (o n : RfVRow) (m : RfVMask) (t : Fin 32) (h : m t = true) :
    rfVRowUpd o n m t = n t := by simp [rfVRowUpd, h]

/-- 掩码写逐 lane 语义：掩码关闭保留旧值 -/
theorem rfVRowUpd_unmasked (o n : RfVRow) (m : RfVMask) (t : Fin 32) (h : m t = false) :
    rfVRowUpd o n m t = o t := by simp [rfVRowUpd, h]

/-- v0 恒全 1（:61，D8） -/
theorem rfV_v0_all_ones (t : Fin 32) : rfVV0 t = 0xFFFFFFFF#32 := rfl

-- ImmGen 逐格式规约（自由变量 inst/immExt；规约右端独立书写，bv_decide 交叉验证）

theorem rfImm_I_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_I inst e = BitVec.signExtend 32 (inst.extractLsb' 20 12) := by
  rfImm_unfold; bv_decide

/-- IMM_I 移位形式：高 12 位符号扩展 ⇔ 算术右移 20 -/
theorem rfImm_I_spec_shift (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_I inst e = BitVec.sshiftRight' inst 20#32 := by
  rfImm_unfold; bv_decide

theorem rfImm_S_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_S inst e =
      BitVec.signExtend 32 ((inst.extractLsb' 25 7) ++ (inst.extractLsb' 7 5)) := by
  rfImm_unfold; bv_decide

theorem rfImm_B_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_B inst e =
      BitVec.signExtend 32
        ((inst.extractLsb' 31 1) ++ (inst.extractLsb' 7 1) ++
         (inst.extractLsb' 25 6) ++ (inst.extractLsb' 8 4) ++ 0#1) := by
  rfImm_unfold; bv_decide

/-- B/J 立即数 bit0 恒 0（拼接尾部的 0#1） -/
theorem rfImm_B_lsb_zero (inst : BitVec 32) (e : BitVec 7) :
    (rfImmGen rfIMM_B inst e).getLsbD 0 = false := by
  rfImm_unfold; bv_decide

/-- IMM_U 掩码形式：高 20 位原样、低 12 位清 0 -/
theorem rfImm_U_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_U inst e = inst &&& 0xFFFFF000#32 := by
  rfImm_unfold; bv_decide

theorem rfImm_J_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_J inst e =
      BitVec.signExtend 32
        ((inst.extractLsb' 31 1) ++ (inst.extractLsb' 12 8) ++
         (inst.extractLsb' 20 1) ++ (inst.extractLsb' 21 10) ++ 0#1) := by
  rfImm_unfold; bv_decide

theorem rfImm_J_lsb_zero (inst : BitVec 32) (e : BitVec 7) :
    (rfImmGen rfIMM_J inst e).getLsbD 0 = false := by
  rfImm_unfold; bv_decide

/-- IMM_Z 移位掩码形式：零扩展 5 位 = 右移 15 后掩码 -/
theorem rfImm_Z_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_Z inst e = (inst >>> 15#32) &&& 0x1F#32 := by
  rfImm_unfold; bv_decide

theorem rfImm_2_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_2 inst e = BitVec.signExtend 32 (inst.extractLsb' 20 5) := by
  rfImm_unfold; bv_decide

/-- IMM_V 两路规约（:108）：imm_ext(6) 选择 11 位拼接或 5 位切片 -/
theorem rfImm_V_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_V inst e =
      (if e.getLsbD 6
       then BitVec.signExtend 32 ((e.extractLsb' 0 6) ++ (inst.extractLsb' 15 5))
       else BitVec.signExtend 32 (inst.extractLsb' 15 5)) := by
  rfImm_unfold; bv_decide

theorem rfImm_L11_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_L11 inst e = BitVec.signExtend 32 (inst.extractLsb' 20 11) := by
  rfImm_unfold; bv_decide

theorem rfImm_S11_spec (inst : BitVec 32) (e : BitVec 7) :
    rfImmGen rfIMM_S11 inst e =
      BitVec.signExtend 32 ((inst.extractLsb' 25 6) ++ (inst.extractLsb' 7 5)) := by
  rfImm_unfold; bv_decide

/-- 默认分支 quirk（:114，Q5）：sel ≥ 10（非任何 IMM_*）时输出 Iimm 清 bit0 -/
theorem rfImm_default_quirk (sel : BitVec 4) (inst : BitVec 32) (e : BitVec 7)
    (h : 10#4 ≤ sel) :
    rfImmGen sel inst e = (BitVec.signExtend 32 (inst.extractLsb' 20 12)) &&& 0xFFFFFFFE#32 := by
  rfImm_unfold; bv_decide

/- ========================================================================= -/
/- 7. 公理审计（关键定理；bv_decide 会引入每个定理私有的 LRAT 检查 trust      -/
/-    公理，形如 `…._native.bv_decide.ax_…`，归档时注明）                     -/
/- =========================================================================-/

#print axioms rfS_read_after_write
#print axioms rfS_write_preserves
#print axioms rfV_mem_masked_merge
#print axioms rfV_bypass_mem_diverge
#print axioms rfImm_U_spec
#print axioms rfImm_default_quirk

end Ventus.Arith
