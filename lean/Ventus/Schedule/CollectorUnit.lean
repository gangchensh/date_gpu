/- ========================================================================= -/
/-                 Schedule/CollectorUnit.lean                               -/
/-  操作数收集单元（collectorUnit，WP2 收官上半）的 Lean 4 模型、测试与证明     -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/                    -/
/-      operandCollector.scala:49-323（class collectorUnit）                  -/
/-  例化点（活代码判定）：operandCollector.scala:529                           -/
/-    `VecInit(Seq.fill(num_collectorUnit)(Module(new collectorUnit).io))`，  -/
/-    num_collectorUnit = num_warp = 8（parameters.scala:19），每 warp 一个。 -/
/-  参数（top/parameters.scala，已核实）：num_thread=32(:9) num_bank=4(:18)    -/
/-    depth_regBank=8(:22) xLen=32(:47) depth_warp=3(:30) regidx_width=5(:23) -/
/-    regext_width=3(:25) widSliceHigh=min(2-1,3-1)=1(:34)                    -/
/-    SGPR_ID_WIDTH=log2Ceil(2048)=11(:149) VGPR_ID_WIDTH=log2Ceil(1024)      -/
/-    =10(:148) → sgpr_base 12 位、vgpr_base 11 位（:56-57 各 +1）。           -/
/-  译码常量（pipeline/DecodeUnit.scala:26-41，object IDecode，已 grep 核实）：-/
/-    B_R=3 A1_PC=0 A1_RS1=1 A1_VRS1=2 A1_IMM=3                              -/
/-    A3_PC=0 A3_VRS3=1 A3_FRS3=2 A3_SD=3                                    -/
/-    A2_SIZE=0 A2_RS2=1 A2_VRS2=2 A2_IMM=3                                  -/
/-  CtrlSigs 字段类型（scoreboard.scala:19-65，已核实）。                     -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. CtrlSigs 有 40+ 字段，collectorUnit 行为只触及本文件 CuCtrl 保留的     -/
/-      17 个字段（wid/inst/imm_ext/sel_imm/sel_alu1-3/branch/isvec/mask/      -/
/-      readmask/reg_idx1-3/pc/custom_signal_0）+ tag（身份占位，对应其余      -/
/-      不参与行为但随 controlReg 透传到 issue.bits.control 的字段，:61,185）。 -/
/-  D2. bankIn(k) 是 per-operand 返回端口；crossBar（:402-434）按 chosen%4     -/
/-      路由，保证端口 k 只携带 regOrder=k 的数据。模型中 bankIn 的 regOrder    -/
/-      仍为自由输入、:266-316 的四分支判定按源码照译；crossbar 保证单列为     -/
/-      假设 cuXbarOk，仅 T3（立即数捷径不被同拍 bankIn 覆盖）引用。           -/
/-  D3. rsAddr 公式（:110-125）：Chisel 中 sgpr_base(12 位)/vgpr_base(11 位)   -/
/-      与 regIdx(8 位) 各 >>>2 后相加（结果取操作数最大宽度），赋给 8 位      -/
/-      rsAddr 时截断低 8 位。和的低 8 位只依赖加数低 8 位，模型直接在 8 位    -/
/-      做加法，语义一致。bankID（:103-105）= wid(1,0)+regIdx(1,0)，2 位       -/
/-      截断加法（mod 4），与写回侧（:603-605）同式，见 Q4。                  -/
/-  D4. MuxLookup 建模为 if-else 链。regIdxWire(2)/rsTypeWire(2)（:189-195,    -/
/-      :207-213）与 :268-280,:288-299,:303-308 的键均覆盖 2 位全域，          -/
/-      MuxLookup 默认分支不可达。                                            -/
/-  D5. validWire（:78,:161,:202,:260）全仓无任何消费者（已 grep 确认），     -/
/-      属调试残留死线，不建模（Q2）。rsRead（:73,:264-285）是单根共享线，     -/
/-      只有 regOrder=0 分支写它并立即消费（custom 路径 :281-285），建模为     -/
/-      局部 let；crossbar 保证下同拍至多一个 regOrder=0 返回，无并发写冲突    -/
/-      （Q5 对源码裸形态的分析）。                                           -/
/-  D6. ImmGen（:83）直接复用 Ventus.Arith.RegFile 的 rfImmGen；其输入选择     -/
/-      （:168-179 MuxLookup）建模为 cuImmOut：s_idle 取输入指令、s_add 取     -/
/-      controlReg、s_out 及非法态取 0（MuxLookup 默认 0.U）。                 -/
/-  D7. 无 RegInit 的寄存器（controlReg/rsType/regIdx/mask，:60,67,70,72）上   -/
/-      电值建模为 0/false（cuInit）；本文件定理均不依赖这些初值（T1 归纳只    -/
/-      用 RegInit 保证的 state=s_idle、valid=0、ready=0）。rsReg 有           -/
/-      RegInit(0)（:71），customCtrlReg 有 RegInit(false)（:80）。            -/
/-  D8. bankIdLookup/addrLookupScalar/addrLookupVector（:89-98）在              -/
/-      collectorUnit 内无任何消费者（全仓 grep 确认，顶层 :583-591 的同名     -/
/-      查表同样无消费者），死代码，不建模（Q6）。                              -/
/-  D9. 状态机按现行代码建模：:138 被注释掉的旧 issue.valid 条件、:152-153     -/
/-      被注释掉的旧 s_add→s_out 条件均不采用（Q7）。状态编码 s_idle=0、       -/
/-      s_add=1、s_out=2（:85 Enum(3) 顺序）。                                 -/
/-  D10. s_out 拍 valid/ready 无条件清零（:258-262，不门控于 issue.fire），    -/
/-      照译；这保证 T1 的 s_out 不变式在反压滞留时仍成立（valid=ready=0）。   -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类，死锁链 CU 段，重点】masked 向量指令（control.mask=1）时           -/
/-      readyWire(3)=0（:248 的 !mask 分支不触发），ready(3) 只能由            -/
/-      regOrder=3 的 bankIn 返回置位（:311-315）。但 mask 读请求 rsType(3)    -/
/-      恒为 0（:214），operandArbiter（:362-365）只放行 rsType=1/2 →          -/
/-      mask 请求永不授予 → crossbar 端口 3 对该 CU 永不置 valid →             -/
/-      bankIn(3) 永不 fire → CU 永久滞留 s_add，issue.valid 永不置位，        -/
/-      control.ready 永不恢复（该 warp 的 CU 死锁，且 instDemux 不再向它      -/
/-      分配新指令）。CU 级定理 cuWmask_deadlock 钉死"无 regOrder=3 返回 ⇒     -/
/-      永不到 s_out"；与主会话查明的顶层事实（:362-365）合成完整死锁链。      -/
/-  Q2【III 类/死逻辑】validWire（:78,:161,:202,:260）无消费者，调试残留。    -/
/-  Q3【I 类候选，潜伏 bug，被系统时序掩蔽】:129 第二析取支                    -/
/-      `io.control.fire && !readyWire(i)` 在 CU 接口层面是活的（定理          -/
/-      cuQ129_bankInRdy_accept：接受拍 bankIn(i).ready = !readyWire(i)，      -/
/-      对需要寄存器读的操作数为高）。真实系统中 crossbar 响应经 RegNext       -/
/-      （:549-552）+ SyncReadMem 1 拍延迟，接受拍不可能有同拍 valid 返回，    -/
/-      故该析取支在系统内不可达（防御逻辑）。但若它真触发（如同拍返回），     -/
/-      :303-306 的 regOrder=2 分支用旧 controlReg.sel_alu3/isvec 配新指令的   -/
/-      imm（:168-179 在 s_idle 取输入指令）——:268/:288 对 rsType 有           -/
/-      Mux(io.control.fire,...) 保护、:271-275/:290-295 对 regIdx 有          -/
/-      MuxLookup(state) 保护，唯独 :303 的 sel_alu3/:306 的 isvec 直取旧      -/
/-      controlReg，前后不一致。建议：:303 改为与 :268 同款的 Mux 选择。        -/
/-  Q4【观察，无 bug】bankID 截断加法：读侧 :103-105 与写回侧 :603-605 同为    -/
/-      2 位 + 2 位 mod-4 加法（bankID 本就是 mod num_bank 语义），两侧一致。  -/
/-  Q5【观察】rsRead 单线共享（:73）：裸形态下若同拍两个端口 fire 且都判       -/
/-      regOrder=0，后写（i 大者）胜，rsReg(0) 得到混合结果；crossbar 路由     -/
/-      （:416-429 按 chosen%4）保证同拍 regOrder 互不重复，实际不可达。       -/
/-  Q6【I 类，面积浪费】:89-98 三个查表（bankIdLookup/addrLookupScalar/        -/
/-      addrLookupVector）无条件例化但无消费者；顶层 :583-591 同样。查表会      -/
/-      综合成实际硬件（264 项 bankIdLookup ROM），属死硬件。                  -/
/-  Q7【注释残留】:138 旧 issue.valid 条件、:152-153 旧转移条件注释掉未删。   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Arith.RegFile
import Std.Tactic.BVDecide

namespace Ventus.Schedule

open Ventus.Arith (rfImmGen rfIMM_I)

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 常量（operandCollector.scala:85；DecodeUnit.scala:26-41）                -/
/- ========================================================================= -/

def cuSIdle : BitVec 2 := 0  -- :85 s_idle
def cuSAdd  : BitVec 2 := 1  -- :85 s_add
def cuSOut  : BitVec 2 := 2  -- :85 s_out

def cuB_R     : BitVec 2 := 3  -- DecodeUnit.scala:26
def cuA1_PC   : BitVec 2 := 0  -- :30
def cuA1_RS1  : BitVec 2 := 1  -- :27
def cuA1_VRS1 : BitVec 2 := 2  -- :28
def cuA1_IMM  : BitVec 2 := 3  -- :29
def cuA3_PC   : BitVec 2 := 0  -- :35
def cuA3_VRS3 : BitVec 2 := 1  -- :32
def cuA3_FRS3 : BitVec 2 := 2  -- :34
def cuA3_SD   : BitVec 2 := 3  -- :33
def cuA2_SIZE : BitVec 2 := 0  -- :41
def cuA2_RS2  : BitVec 2 := 1  -- :38
def cuA2_VRS2 : BitVec 2 := 2  -- :40
def cuA2_IMM  : BitVec 2 := 3  -- :39

/-- 向量寄存器行：num_thread=32 个 32 位 lane（:27-28 的 Vec(num_thread, UInt(xLen.W))） -/
abbrev CuRow : Type := Fin 32 → BitVec 32

def cuRow0 : CuRow := fun _ => 0#32

/-- VecInit.fill(num_thread)(v) 广播 -/
def cuBcast (v : BitVec 32) : CuRow := fun _ => v

/- ========================================================================= -/
/- 2. 接口切片（D1）与状态                                                    -/
/- ========================================================================= -/

/-- CtrlSigs 的行为相关切片（D1；字段类型对照 scoreboard.scala:19-65） -/
structure CuCtrl where
  tag             : BitVec 8   -- 身份占位（透传字段的代表）
  wid             : BitVec 3   -- depth_warp=3
  inst            : BitVec 32
  imm_ext         : BitVec 7   -- :58 UInt((1+6).W)
  sel_imm         : BitVec 4
  sel_alu1        : BitVec 2
  sel_alu2        : BitVec 2
  sel_alu3        : BitVec 2
  branch          : BitVec 2
  isvec           : Bool
  mask            : Bool
  readmask        : Bool
  reg_idx1        : BitVec 8   -- regidx_width+regext_width = 8
  reg_idx2        : BitVec 8
  reg_idx3        : BitVec 8
  pc              : BitVec 32
  custom_signal_0 : Bool
deriving DecidableEq

def cuCtrl0 : CuCtrl :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, false, false, false, 0, 0, 0, 0, false⟩

/-- crossbar2CU（:24-29） -/
structure CuBankIn where
  regOrder : BitVec 2
  data     : CuRow
  v0       : CuRow

/-- 单拍输入：control（:51）、bankIn×4（:52，valid/bits 分列便于定理陈述）、
    issue.ready（:54）、sgpr_base/vgpr_base（:56-57） -/
structure CuInputs where
  controlValid : Bool
  ctrl         : CuCtrl
  bv0 : Bool
  bv1 : Bool
  bv2 : Bool
  bv3 : Bool
  bb0 : CuBankIn
  bb1 : CuBankIn
  bb2 : CuBankIn
  bb3 : CuBankIn
  issueReady   : Bool
  sgprBase     : Fin 8 → BitVec 12  -- SGPR_ID_WIDTH+1 = 12
  vgprBase     : Fin 8 → BitVec 11  -- VGPR_ID_WIDTH+1 = 11

/-- 第 k 个 bankIn 端口的 valid（k ≥ 4 时归到 3，只用 0..3） -/
def CuInputs.bankV (i : CuInputs) (k : Nat) : Bool :=
  if k = 0 then i.bv0 else if k = 1 then i.bv1 else if k = 2 then i.bv2 else i.bv3

/-- 第 k 个 bankIn 端口的 bits -/
def CuInputs.bankB (i : CuInputs) (k : Nat) : CuBankIn :=
  if k = 0 then i.bb0 else if k = 1 then i.bb1 else if k = 2 then i.bb2 else i.bb3

/-- crossbar 路由保证（D2）：端口 k 只携带 regOrder=k（crossBar :416-429） -/
def cuXbarOk (i : CuInputs) : Prop :=
  (i.bankB 0).regOrder = 0#2 ∧ (i.bankB 1).regOrder = 1#2 ∧
  (i.bankB 2).regOrder = 2#2 ∧ (i.bankB 3).regOrder = 3#2

/-- collectorUnit 状态（:60-86）：controlReg/rsType/regIdx 拆四字段，
    ready/valid 打包 BitVec 4（orR/相等比较方便），rsReg×3 + mask + 状态机 -/
structure CuState where
  controlReg    : CuCtrl        -- :60
  rsType0 : BitVec 2            -- :67
  rsType1 : BitVec 2
  rsType2 : BitVec 2
  rsType3 : BitVec 2
  regIdx0 : BitVec 8            -- :70
  regIdx1 : BitVec 8
  regIdx2 : BitVec 8
  regIdx3 : BitVec 8
  ready         : BitVec 4      -- :68 RegInit(false)
  valid         : BitVec 4      -- :69 RegInit(false)
  rsReg0 : CuRow                -- :71 RegInit(0)
  rsReg1 : CuRow
  rsReg2 : CuRow
  vMask         : Fin 32 → Bool -- :72
  customCtrlReg : Bool          -- :80 RegInit(false)
  state         : BitVec 2      -- :86 RegInit(s_idle)

def CuState.rsTypeAt (s : CuState) (k : Nat) : BitVec 2 :=
  if k = 0 then s.rsType0 else if k = 1 then s.rsType1
  else if k = 2 then s.rsType2 else s.rsType3

def CuState.regIdxAt (s : CuState) (k : Nat) : BitVec 8 :=
  if k = 0 then s.regIdx0 else if k = 1 then s.regIdx1
  else if k = 2 then s.regIdx2 else s.regIdx3

def cuInit : CuState :=
  { controlReg := cuCtrl0
  , rsType0 := 0, rsType1 := 0, rsType2 := 0, rsType3 := 0
  , regIdx0 := 0, regIdx1 := 0, regIdx2 := 0, regIdx3 := 0
  , ready := 0#4, valid := 0#4
  , rsReg0 := cuRow0, rsReg1 := cuRow0, rsReg2 := cuRow0
  , vMask := fun _ => false
  , customCtrlReg := false
  , state := cuSIdle }

/- ========================================================================= -/
/- 3. 组合逻辑：接受拍 Wire、握手、输出                                       -/
/- ========================================================================= -/

/-- control.ready（:140）：s_idle 且 valid.orR = 0 -/
def cuControlRdy (s : CuState) : Bool :=
  (s.state == cuSIdle) && (s.valid == 0#4)

/-- io.control.fire -/
def cuControlFire (s : CuState) (i : CuInputs) : Bool :=
  i.controlValid && cuControlRdy s

/-- readyWire 各比特（:223-254 的四个捷径条件，D4 展开） -/
def cuRw0 (c : CuCtrl) : Bool := (c.sel_alu1 == cuA1_IMM) || (c.sel_alu1 == cuA1_PC)   -- :223-231
def cuRw1 (c : CuCtrl) : Bool := (c.sel_alu2 == cuA2_IMM) || (c.sel_alu2 == cuA2_SIZE) -- :233-241
def cuRw2 (c : CuCtrl) : Bool := (c.sel_alu3 == cuA3_PC) && (c.branch != cuB_R)        -- :243-247
def cuRw3 (c : CuCtrl) : Bool := !c.mask                                               -- :248-254

def cuRwK (c : CuCtrl) (k : Nat) : Bool :=
  if k = 0 then cuRw0 c else if k = 1 then cuRw1 c
  else if k = 2 then cuRw2 c else cuRw3 c

/-- readyWire 打包（:203 清零 + :226/:230/:236/:240/:246/:253 条件置位的净效果） -/
def cuReadyWire (c : CuCtrl) : BitVec 4 :=
  (if cuRwK c 0 then 1#4 else 0#4) ||| (if cuRwK c 1 then 2#4 else 0#4) |||
  (if cuRwK c 2 then 4#4 else 0#4) ||| (if cuRwK c 3 then 8#4 else 0#4)

/-- regIdxWire(2)（:189-195，MuxLookup 四键覆盖全域） -/
def cuRegIdxWire2 (c : CuCtrl) : BitVec 8 :=
  if c.sel_alu3 == cuA3_PC then (if c.branch == cuB_R then c.reg_idx1 else c.reg_idx3)
  else if c.sel_alu3 == cuA3_VRS3 then c.reg_idx3
  else if c.sel_alu3 == cuA3_SD then
    (if c.isvec && !c.readmask then c.reg_idx3 else c.reg_idx2)
  else c.reg_idx3  -- A3_FRS3；A3_SD 已含其上，四键覆盖 2 位全域

/-- regIdxWire(k)（:187-196） -/
def cuRegIdxWire (c : CuCtrl) (k : Nat) : BitVec 8 :=
  if k = 0 then c.reg_idx1 else if k = 1 then c.reg_idx2
  else if k = 2 then cuRegIdxWire2 c else 0#8  -- :196 mask 端口恒 0

/-- rsTypeWire(2)（:207-213） -/
def cuRsTypeWire2 (c : CuCtrl) : BitVec 2 :=
  if c.sel_alu3 == cuA3_PC then (if c.branch == cuB_R then 1#2 else 3#2)
  else if c.sel_alu3 == cuA3_VRS3 then 2#2
  else if c.sel_alu3 == cuA3_SD then (if c.isvec then 2#2 else 1#2)
  else 1#2  -- A3_FRS3

/-- rsTypeWire(k)（:205-214）：0/3 的地址公式走 scalar 分支（:120-126 otherwise） -/
def cuRsTypeWire (c : CuCtrl) (k : Nat) : BitVec 2 :=
  if k = 0 then c.sel_alu1 else if k = 1 then c.sel_alu2
  else if k = 2 then cuRsTypeWire2 c else 0#2  -- :214 mask 端口恒 0

/-- ImmGen 输入选择与输出（:168-179，D6） -/
def cuImmOut (s : CuState) (c : CuCtrl) : BitVec 32 :=
  if s.state == cuSIdle then rfImmGen c.sel_imm c.inst c.imm_ext
  else if s.state == cuSAdd then
    rfImmGen s.controlReg.sel_imm s.controlReg.inst s.controlReg.imm_ext
  else rfImmGen 0#4 0#32 0#7

/-- CU2Arbiter 请求（:30-37） -/
structure CuArbReq where
  rsAddr : BitVec 8
  bankID : BitVec 2
  rsType : BitVec 2

/-- outArbiterIO(k).bits（:101-127；地址宽度处理见 D3） -/
def cuOutArbBits (s : CuState) (i : CuInputs) (k : Nat) : CuArbReq :=
  let acc := cuControlFire s i  -- :103-105 的 Mux 条件（fire 蕴含 s_idle）
  let rt := if acc then cuRsTypeWire i.ctrl k else s.rsTypeAt k
  let idx := if acc then cuRegIdxWire i.ctrl k else s.regIdxAt k
  let wid := if acc then i.ctrl.wid else s.controlReg.wid
  let base8 := if rt == 2#2  -- :114-119 向量；:108-113 与 :120-126 标量
    then ((i.vgprBase wid.toFin) >>> 2).extractLsb' 0 8
    else ((i.sgprBase wid.toFin) >>> 2).extractLsb' 0 8
  { rsAddr := base8 + (idx >>> 2)
    bankID := (wid.extractLsb' 0 2) + (idx.extractLsb' 0 2)
    rsType := rt }

/-- outArbiterIO(k).valid（:131-137 MuxLookup(state, false)） -/
def cuOutArbValidK (s : CuState) (i : CuInputs) (k : Nat) : Bool :=
  if s.state == cuSIdle then cuControlFire s i && !cuRwK i.ctrl k      -- :134
  else if s.state == cuSAdd then
    (((s.valid >>> (BitVec.ofNat 4 k)) &&& 1#4) == 1#4) &&
    !(((s.ready >>> (BitVec.ofNat 4 k)) &&& 1#4) == 1#4)               -- :135
  else false

/-- bankIn(k).ready（:129；第二析取支的可达性见 Q3/cuQ129_bankInRdy_accept） -/
def cuBankInRdyK (s : CuState) (i : CuInputs) (k : Nat) : Bool :=
  ((s.state == cuSAdd) && !(((s.ready >>> (BitVec.ofNat 4 k)) &&& 1#4) == 1#4)) ||
  (cuControlFire s i && !cuRwK i.ctrl k)

/-- bankIn(k).fire -/
def cuBankFireK (s : CuState) (i : CuInputs) (k : Nat) : Bool :=
  i.bankV k && cuBankInRdyK s i k

/-- issue.valid（:139，现行代码；:138 注释掉的旧条件不采用，D9） -/
def cuIssueValid (s : CuState) : Bool := s.state == cuSOut

def cuIssueFire (s : CuState) (i : CuInputs) : Bool :=
  cuIssueValid s && i.issueReady

/-- issueIO（:39-45） -/
structure CuIssueBits where
  alu_src1 : CuRow
  alu_src2 : CuRow
  alu_src3 : CuRow
  vmask   : Fin 32 → Bool
  control : CuCtrl

/-- issue.bits（:61,319-322） -/
def cuIssueBits (s : CuState) : CuIssueBits :=
  ⟨s.rsReg0, s.rsReg1, s.rsReg2, s.vMask, s.controlReg⟩

/- ========================================================================= -/
/- 4. 单拍转移                                                                -/
/- ========================================================================= -/

/-- 状态机次态（:142-159，D9） -/
def cuStateTrans (s : CuState) (i : CuInputs) : BitVec 2 :=
  if s.state == cuSIdle then                                          -- :142
    if cuControlFire s i then                                         -- :144
      (if cuReadyWire i.ctrl == 0xF#4 then cuSOut else cuSAdd)        -- :145-146
    else cuSIdle                                                      -- :148
  else if s.state == cuSAdd then                                      -- :149
    (if s.valid == s.ready then cuSOut else cuSAdd)                   -- :150-154
  else if s.state == cuSOut then                                      -- :155
    (if cuIssueFire s i then cuSIdle else cuSOut)                     -- :156-158
  else cuSIdle                                                        -- :159

/-- s_idle 接受拍的寄存器更新（:181-256 的 is(s_idle) 分支） -/
def cuAccept (s : CuState) (i : CuInputs) : CuState :=
  if cuControlFire s i then                                           -- :184
    let c := i.ctrl
    let imm := cuImmOut s c
    { s with
      controlReg := c                                                 -- :185
    , regIdx0 := c.reg_idx1                                           -- :187,:197
    , regIdx1 := c.reg_idx2                                           -- :188,:198
    , regIdx2 := cuRegIdxWire2 c                                      -- :189-195,:199
    , regIdx3 := 0#8                                                  -- :196,:200
    , rsType0 := c.sel_alu1                                           -- :205,:216
    , rsType1 := c.sel_alu2                                           -- :206,:217
    , rsType2 := cuRsTypeWire2 c                                      -- :207-213,:218
    , rsType3 := 0#2                                                  -- :214,:219
    , customCtrlReg := c.custom_signal_0                              -- :215,:220
    , valid := 0xF#4                                                  -- :201
    , ready := cuReadyWire c                                          -- :203 + 捷径置位
    , rsReg0 := if c.sel_alu1 == cuA1_IMM then cuBcast imm             -- :223-226
                else if c.sel_alu1 == cuA1_PC then cuBcast c.pc        -- :227-230
                else s.rsReg0
    , rsReg1 := if c.sel_alu2 == cuA2_IMM then cuBcast imm             -- :233-236
                else if c.sel_alu2 == cuA2_SIZE then cuBcast 4#32      -- :237-240
                else s.rsReg1
    , rsReg2 := if (c.sel_alu3 == cuA3_PC) && (c.branch != cuB_R)
                then cuBcast (imm + c.pc)                              -- :243-246
                else s.rsReg2
    , vMask := if !c.mask                                              -- :248-251
               then (fun x => if c.isvec then true else (x.val == 0))
               else s.vMask }
  else s

/-- bankIn 一个端口的返回处理（:264-318；rsRead 建模为局部 let，D5）。
    rdy' 统一为 `ready ||| (1 <<< regOrder)`——源码四分支分别置 ready(0..3)（:286,
    :301,:310,:315），与 `1 <<< regOrder` 逐位一致。pre 为拍前状态（fire/Mux 选择用）。 -/
def cuBankPort (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat) : CuState :=
  if cuBankFireK pre i k then                                         -- :266
    let b := i.bankB k
    let imm := cuImmOut pre i.ctrl
    let fire := cuControlFire pre i
    let rdy' := st.ready ||| (1#4 <<< b.regOrder.zeroExtend 4)
    if b.regOrder == 0#2 then                                         -- :267 operand1
      let rt0 := if fire then i.ctrl.sel_alu1 else pre.rsType0        -- :268 的 Mux
      let idxNe0 := if pre.state == cuSIdle then (i.ctrl.reg_idx1 != 0#8)   -- :271-274
                    else if pre.state == cuSAdd then (pre.regIdx0 != 0#8)
                    else false                                        -- :271 MuxLookup 默认
      let rsRead := if rt0 == cuA1_RS1                                -- :270-278
                    then (if idxNe0 then cuBcast (b.data ⟨0, by decide⟩) else cuRow0)
                    else if rt0 == cuA1_VRS1 then b.data              -- :279
                    else cuRow0                                       -- :268 MuxLookup 默认
      let custom := if fire then i.ctrl.custom_signal_0 else pre.customCtrlReg  -- :281
      let v0' := if custom then cuBcast (rsRead ⟨0, by decide⟩ + imm) else rsRead  -- :282-284
      { st with rsReg0 := v0', ready := rdy' }
    else if b.regOrder == 1#2 then                                    -- :287 operand2
      let rt1 := if fire then i.ctrl.sel_alu2 else pre.rsType1        -- :288
      let idxNe0 := if pre.state == cuSIdle then (i.ctrl.reg_idx2 != 0#8)   -- :290-294
                    else if pre.state == cuSAdd then (pre.regIdx1 != 0#8)
                    else false
      let v1' := if rt1 == cuA2_RS2                                   -- :290-298
                 then (if idxNe0 then cuBcast (b.data ⟨0, by decide⟩) else cuRow0)
                 else if rt1 == cuA2_VRS2 then b.data                 -- :299
                 else cuRow0                                          -- :288 默认
      { st with rsReg1 := v1', ready := rdy' }
    else if b.regOrder == 2#2 then                                    -- :302 operand3
      let v2' := if pre.controlReg.sel_alu3 == cuA3_PC                -- :304（旧 controlReg，Q3）
                 then cuBcast (imm + b.data ⟨0, by decide⟩)
                 else if pre.controlReg.sel_alu3 == cuA3_VRS3 then b.data  -- :305
                 else if pre.controlReg.sel_alu3 == cuA3_SD then           -- :306
                   (if pre.controlReg.isvec then b.data else cuBcast (b.data ⟨0, by decide⟩))
                 else if pre.controlReg.sel_alu3 == cuA3_FRS3              -- :307
                 then cuBcast (b.data ⟨0, by decide⟩)
                 else cuRow0                                               -- :303 默认（不可达）
      { st with rsReg2 := v2', ready := rdy' }
    else                                                              -- :311 regOrder=3 mask
      let vm := fun x => (b.v0 ⟨0, by decide⟩).getLsbD x.val          -- :312-314 v0(0) 的第 x 位
      { st with vMask := vm, ready := rdy' }
  else st

/-- 接受/状态机/s_out 清零（:258-262，D10）之后、bankIn 之前的前缀状态 -/
def cuPreBank (s : CuState) (i : CuInputs) : CuState :=
  if s.state == cuSOut then
    { (cuAccept s i) with state := cuStateTrans s i, valid := 0#4, ready := 0#4 }
  else
    { (cuAccept s i) with state := cuStateTrans s i }

/-- 单拍转移：先 accept/状态机/s_out 清零，再按端口序 0→3 处理 bankIn（程序序） -/
def cuStep (s : CuState) (i : CuInputs) : CuState :=
  cuBankPort s i (cuBankPort s i (cuBankPort s i (cuBankPort s i (cuPreBank s i) 0) 1) 2) 3

/-- 多拍运行 -/
def cuRun (s : CuState) (ins : List CuInputs) : CuState := ins.foldl cuStep s

/- ========================================================================= -/
/- 5. 数值回归测试（先测试；单拍 decide，多拍 native_decide）                  -/
/- ========================================================================= -/

section CuRegressionTests

-- 接受拍 Wire 译码回归（:189-195,:207-213,:223-254）
example : cuRegIdxWire2 { cuCtrl0 with sel_alu3 := cuA3_PC, branch := cuB_R, reg_idx1 := 5#8, reg_idx3 := 6#8 } = 5#8 := by decide
example : cuRegIdxWire2 { cuCtrl0 with sel_alu3 := cuA3_PC, branch := 0#2, reg_idx1 := 5#8, reg_idx3 := 6#8 } = 6#8 := by decide
example : cuRegIdxWire2 { cuCtrl0 with sel_alu3 := cuA3_SD, isvec := true, readmask := false, reg_idx2 := 7#8, reg_idx3 := 6#8 } = 6#8 := by decide
example : cuRegIdxWire2 { cuCtrl0 with sel_alu3 := cuA3_SD, isvec := true, readmask := true, reg_idx2 := 7#8, reg_idx3 := 6#8 } = 7#8 := by decide
example : cuRegIdxWire2 { cuCtrl0 with sel_alu3 := cuA3_SD, isvec := false, reg_idx2 := 7#8, reg_idx3 := 6#8 } = 7#8 := by decide
example : cuRegIdxWire2 { cuCtrl0 with sel_alu3 := cuA3_FRS3, reg_idx3 := 6#8 } = 6#8 := by decide
example : cuRsTypeWire2 { cuCtrl0 with sel_alu3 := cuA3_PC, branch := cuB_R } = 1#2 := by decide
example : cuRsTypeWire2 { cuCtrl0 with sel_alu3 := cuA3_PC, branch := 0#2 } = 3#2 := by decide
example : cuRsTypeWire2 { cuCtrl0 with sel_alu3 := cuA3_VRS3 } = 2#2 := by decide
example : cuRsTypeWire2 { cuCtrl0 with sel_alu3 := cuA3_SD, isvec := true } = 2#2 := by decide
example : cuRsTypeWire2 { cuCtrl0 with sel_alu3 := cuA3_SD, isvec := false } = 1#2 := by decide
example : cuRsTypeWire2 { cuCtrl0 with sel_alu3 := cuA3_FRS3 } = 1#2 := by decide
example : cuReadyWire { cuCtrl0 with sel_alu1 := cuA1_IMM, sel_alu2 := cuA2_SIZE, sel_alu3 := cuA3_PC, branch := 0#2, mask := false } = 0xF#4 := by decide
example : cuReadyWire { cuCtrl0 with sel_alu1 := cuA1_RS1, sel_alu2 := cuA2_RS2, sel_alu3 := cuA3_PC, branch := 0#2, mask := false } = 0xC#4 := by decide
example : cuReadyWire { cuCtrl0 with sel_alu1 := cuA1_VRS1, sel_alu2 := cuA2_VRS2, sel_alu3 := cuA3_VRS3, mask := true } = 0#4 := by decide

-- 测试基础设施
def cuRowOf (v : BitVec 32) : CuRow :=
  fun t => if t.val = 0 then v else 0xDEAD0000#32 + BitVec.ofNat 32 t.val
def cuRowA : CuRow := fun t => 0x1000#32 + BitVec.ofNat 32 t.val
def cuRowB : CuRow := fun t => 0x2000#32 + BitVec.ofNat 32 t.val
def cuRowC : CuRow := fun t => 0x3000#32 + BitVec.ofNat 32 t.val

def cuBI0 : CuBankIn := ⟨0#2, cuRow0, cuRow0⟩

def cuSgprB : Fin 8 → BitVec 12 := fun w => BitVec.ofNat 12 (w.val * 64)
def cuVgprB : Fin 8 → BitVec 11 := fun w => BitVec.ofNat 11 (w.val * 32)

def cuInNop : CuInputs :=
  ⟨false, cuCtrl0, false, false, false, false, cuBI0, cuBI0, cuBI0, cuBI0,
   false, cuSgprB, cuVgprB⟩

/- ---- 场景 1：标量指令（rs1/rs2 标量读 + A3_PC 立即数捷径，:270-278 广播） ---- -/

def cuCtrlScalar : CuCtrl :=
  { cuCtrl0 with sel_alu1 := cuA1_RS1, sel_alu2 := cuA2_RS2, sel_alu3 := cuA3_PC, branch := 0#2, reg_idx1 := 5#8, reg_idx2 := 7#8, sel_imm := rfIMM_I, inst := 0x00530293#32, pc := 0x1000#32 }   -- imm = 5（RegFile.lean 测试 I1 同向量）

def cuInScalar0 : CuInputs := { cuInNop with controlValid := true, ctrl := cuCtrlScalar }
def cuInScalar1 : CuInputs :=
  { cuInNop with bv0 := true, bb0 := ⟨0#2, cuRowOf 0xAAAA#32, cuRow0⟩ }
def cuInScalar2 : CuInputs :=
  { cuInNop with bv1 := true, bb1 := ⟨1#2, cuRowOf 0xBBBB#32, cuRow0⟩ }
def cuInScalar4 : CuInputs := { cuInNop with issueReady := true }

def cuSs1 := cuStep cuInit cuInScalar0      -- 接受拍
def cuSs2 := cuStep cuSs1 cuInScalar1       -- bankIn(0) 返回 rs1
def cuSs3 := cuStep cuSs2 cuInScalar2       -- bankIn(1) 返回 rs2
def cuSs4 := cuStep cuSs3 cuInNop           -- valid==ready → s_out
def cuSs5 := cuStep cuSs4 cuInScalar4       -- issue.fire → s_idle

-- 接受拍输出：端口 0/1 发出标量读请求（:103-126,:134），端口 2/3 有捷径不发请求
example : cuOutArbValidK cuInit cuInScalar0 0 = true := by decide
example : (cuOutArbBits cuInit cuInScalar0 0).rsAddr = 1#8 := by decide  -- (0>>>2)+(5>>>2)
example : (cuOutArbBits cuInit cuInScalar0 0).bankID = 1#2 := by decide  -- 0 + 5(1,0)
example : (cuOutArbBits cuInit cuInScalar0 0).rsType = 1#2 := by decide
example : cuOutArbValidK cuInit cuInScalar0 1 = true := by decide
example : (cuOutArbBits cuInit cuInScalar0 1).rsAddr = 1#8 := by decide  -- (7>>>2)=1
example : (cuOutArbBits cuInit cuInScalar0 1).bankID = 3#2 := by decide  -- 0 + 7(1,0)
example : cuOutArbValidK cuInit cuInScalar0 2 = false := by decide       -- A3_PC 捷径
example : cuOutArbValidK cuInit cuInScalar0 3 = false := by decide       -- !mask 捷径

-- 接受后：s_add，valid=1111，ready=1100（bit2/bit3 捷径），rsReg2 = imm+pc 广播
example : cuSs1.state = cuSAdd := by decide
example : cuSs1.valid = 0xF#4 := by decide
example : cuSs1.ready = 0xC#4 := by decide
example : cuSs1.rsReg2 ⟨7, by decide⟩ = 0x1005#32 := by native_decide
-- 标量指令无 mask：仅 lane0（:250）
example : cuSs1.vMask ⟨0, by decide⟩ = true := by native_decide
example : cuSs1.vMask ⟨3, by decide⟩ = false := by native_decide

-- bankIn(0) 返回：regIdx(0)=5≠0 → data(0) 广播（:270-278）
example : cuSs2.ready = 0xD#4 := by native_decide
example : cuSs2.rsReg0 ⟨5, by decide⟩ = 0xAAAA#32 := by native_decide
example : cuSs2.rsReg0 ⟨9, by decide⟩ = 0xAAAA#32 := by native_decide

-- bankIn(1) 返回：ready 集齐
example : cuSs3.ready = 0xF#4 := by native_decide
example : cuSs3.rsReg1 ⟨2, by decide⟩ = 0xBBBB#32 := by native_decide

-- 集齐后下一拍 s_out（:150-154 比较的是拍前寄存器值）
example : cuSs4.state = cuSOut := by native_decide
-- issue.bits（:61,319-322）：广播语义与 controlReg 保持
example : (cuIssueBits cuSs4).alu_src1 ⟨3, by decide⟩ = 0xAAAA#32 := by native_decide
example : (cuIssueBits cuSs4).alu_src2 ⟨11, by decide⟩ = 0xBBBB#32 := by native_decide
example : (cuIssueBits cuSs4).alu_src3 ⟨0, by decide⟩ = 0x1005#32 := by native_decide
example : (cuIssueBits cuSs4).vmask ⟨0, by decide⟩ = true := by native_decide
example : (cuIssueBits cuSs4).vmask ⟨1, by decide⟩ = false := by native_decide
example : (cuIssueBits cuSs4).control = cuCtrlScalar := by native_decide

-- issue.fire → s_idle 且 valid/ready 清零（T4 的测试面）
example : cuSs5.state = cuSIdle := by native_decide
example : cuSs5.valid = 0#4 := by native_decide
example : cuSs5.ready = 0#4 := by native_decide
example : cuControlRdy cuSs5 = true := by native_decide

/- ---- 场景 1b：x0 语义——reg_idx1=0 的标量 rs1 读得全 0（:270-278 的 orR 判零） ---- -/

def cuCtrlX0 : CuCtrl := { cuCtrlScalar with reg_idx1 := 0#8 }
def cuSx1 := cuStep cuInit { cuInNop with controlValid := true, ctrl := cuCtrlX0 }
def cuSx2 := cuStep cuSx1 { cuInNop with bv0 := true, bb0 := ⟨0#2, cuRowOf 0xAAAA#32, cuRow0⟩ }

example : cuSx2.rsReg0 ⟨0, by decide⟩ = 0#32 := by native_decide
example : cuSx2.rsReg0 ⟨13, by decide⟩ = 0#32 := by native_decide
example : cuSx2.ready = 0xD#4 := by native_decide  -- ready(0) 照常置位

/- ---- 场景 2：向量指令（vs1/vs2/vs3 + mask 读，四组返回次序打乱） ---- -/

def cuCtrlVec : CuCtrl :=
  { cuCtrl0 with sel_alu1 := cuA1_VRS1, sel_alu2 := cuA2_VRS2, sel_alu3 := cuA3_VRS3, reg_idx1 := 9#8, reg_idx2 := 10#8, reg_idx3 := 11#8, isvec := true, mask := true }

def cuInVec0 : CuInputs := { cuInNop with controlValid := true, ctrl := cuCtrlVec }
-- 拍1：端口 0 与端口 2 同拍返回（并发收集）
def cuInVec1 : CuInputs :=
  { cuInNop with bv0 := true, bb0 := ⟨0#2, cuRowA, cuRow0⟩, bv2 := true, bb2 := ⟨2#2, cuRowB, cuRow0⟩ }
-- 拍2：mask 返回（v0(0) = 0xA5A5A5A5）
def cuInVec2 : CuInputs :=
  { cuInNop with bv3 := true, bb3 := ⟨3#2, cuRow0, fun _ => 0xA5A5A5A5#32⟩ }
-- 拍3：端口 1 返回
def cuInVec3 : CuInputs := { cuInNop with bv1 := true, bb1 := ⟨1#2, cuRowC, cuRow0⟩ }
def cuInVec5 : CuInputs := { cuInNop with issueReady := true }

def cuSv1 := cuStep cuInit cuInVec0
def cuSv2 := cuStep cuSv1 cuInVec1
def cuSv3 := cuStep cuSv2 cuInVec2
def cuSv4 := cuStep cuSv3 cuInVec3
def cuSv5 := cuStep cuSv4 cuInNop
def cuSv6 := cuStep cuSv5 cuInVec5

-- 接受拍：四端口全发请求；rsType(3)=0（mask 请求，Q1 死锁链的源头）
example : cuOutArbValidK cuInit cuInVec0 0 = true := by decide
example : cuOutArbValidK cuInit cuInVec0 1 = true := by decide
example : cuOutArbValidK cuInit cuInVec0 2 = true := by decide
example : cuOutArbValidK cuInit cuInVec0 3 = true := by decide
example : (cuOutArbBits cuInit cuInVec0 0).rsAddr = 2#8 := by decide  -- (9>>>2)
example : (cuOutArbBits cuInit cuInVec0 0).rsType = 2#2 := by decide
example : (cuOutArbBits cuInit cuInVec0 2).rsAddr = 2#8 := by decide  -- (11>>>2)
example : (cuOutArbBits cuInit cuInVec0 2).bankID = 3#2 := by decide
example : (cuOutArbBits cuInit cuInVec0 3).rsAddr = 0#8 := by decide  -- regIdx(3)=0
example : (cuOutArbBits cuInit cuInVec0 3).bankID = 0#2 := by decide
example : (cuOutArbBits cuInit cuInVec0 3).rsType = 0#2 := by decide  -- :214

example : cuSv1.state = cuSAdd := by decide
example : cuSv1.ready = 0#4 := by decide
-- 同拍并发收集端口 0 与 2：rsReg0 取向量数据（:279），rsReg2 走 A3_VRS3（:305）
example : cuSv2.ready = 0x5#4 := by native_decide
example : cuSv2.rsReg0 ⟨17, by decide⟩ = 0x1011#32 := by native_decide
example : cuSv2.rsReg2 ⟨2, by decide⟩ = 0x2002#32 := by native_decide
-- mask 返回：mask(x) = v0(0) 第 x 位（:312-314）；0xA5A5A5A5 bit0=1 bit1=0 bit7=1 bit31=1
example : cuSv3.ready = 0xD#4 := by native_decide
example : cuSv3.vMask ⟨0, by decide⟩ = true := by native_decide
example : cuSv3.vMask ⟨1, by decide⟩ = false := by native_decide
example : cuSv3.vMask ⟨7, by decide⟩ = true := by native_decide
example : cuSv3.vMask ⟨31, by decide⟩ = true := by native_decide
-- 端口 1 最后返回，集齐
example : cuSv4.ready = 0xF#4 := by native_decide
example : cuSv4.rsReg1 ⟨9, by decide⟩ = 0x3009#32 := by native_decide
example : cuSv5.state = cuSOut := by native_decide
-- issue.bits：乱序收集结果正确
example : (cuIssueBits cuSv5).alu_src1 ⟨17, by decide⟩ = 0x1011#32 := by native_decide
example : (cuIssueBits cuSv5).alu_src2 ⟨9, by decide⟩ = 0x3009#32 := by native_decide
example : (cuIssueBits cuSv5).alu_src3 ⟨2, by decide⟩ = 0x2002#32 := by native_decide
example : (cuIssueBits cuSv5).vmask ⟨0, by decide⟩ = true := by native_decide
example : (cuIssueBits cuSv5).vmask ⟨1, by decide⟩ = false := by native_decide
example : (cuIssueBits cuSv5).control = cuCtrlVec := by native_decide
example : cuSv6.state = cuSIdle := by native_decide

/- ---- 场景 3：全立即数指令——接受拍 readyWire 全 1，直接 s_idle→s_out（:146） ---- -/

def cuCtrlImm : CuCtrl :=
  { cuCtrl0 with sel_alu1 := cuA1_IMM, sel_alu2 := cuA2_IMM, sel_alu3 := cuA3_PC, branch := 0#2, sel_imm := rfIMM_I, inst := 0x00530293#32, pc := 0x2000#32 }

def cuInImm0 : CuInputs := { cuInNop with controlValid := true, ctrl := cuCtrlImm }
def cuSi1 := cuStep cuInit cuInImm0
def cuSi2 := cuStep cuSi1 { cuInNop with issueReady := true }

example : cuReadyWire cuCtrlImm = 0xF#4 := by decide
-- 全捷径：接受拍不发任何读请求
example : cuOutArbValidK cuInit cuInImm0 0 = false := by decide
example : cuOutArbValidK cuInit cuInImm0 1 = false := by decide
example : cuOutArbValidK cuInit cuInImm0 2 = false := by decide
example : cuOutArbValidK cuInit cuInImm0 3 = false := by decide
-- 直接进 s_out；alu_src1/2 = imm 广播、alu_src3 = imm+pc 广播
example : cuSi1.state = cuSOut := by decide
example : (cuIssueBits cuSi1).alu_src1 ⟨20, by decide⟩ = 5#32 := by native_decide
example : (cuIssueBits cuSi1).alu_src2 ⟨20, by decide⟩ = 5#32 := by native_decide
example : (cuIssueBits cuSi1).alu_src3 ⟨20, by decide⟩ = 0x2005#32 := by native_decide
example : (cuIssueBits cuSi1).vmask ⟨0, by decide⟩ = true := by native_decide
example : (cuIssueBits cuSi1).vmask ⟨5, by decide⟩ = false := by native_decide
example : cuSi2.state = cuSIdle := by native_decide
example : cuSi2.valid = 0#4 := by native_decide
example : cuSi2.ready = 0#4 := by native_decide

/- ---- 场景 4：无 mask 向量指令——mask 全 true（:248-251）；A2_SIZE 广播 4（:238） ---- -/

def cuCtrlVecNoMask : CuCtrl :=
  { cuCtrl0 with sel_alu1 := cuA1_IMM, sel_alu2 := cuA2_SIZE, sel_alu3 := cuA3_PC, branch := 0#2, isvec := true, mask := false, sel_imm := rfIMM_I, inst := 0x00530293#32, pc := 0#32 }

def cuSm1 := cuStep cuInit { cuInNop with controlValid := true, ctrl := cuCtrlVecNoMask }

example : cuSm1.state = cuSOut := by decide
example : cuSm1.vMask ⟨0, by decide⟩ = true := by native_decide
example : cuSm1.vMask ⟨15, by decide⟩ = true := by native_decide
example : cuSm1.vMask ⟨31, by decide⟩ = true := by native_decide
example : (cuIssueBits cuSm1).alu_src2 ⟨3, by decide⟩ = 4#32 := by native_decide

/- ---- 场景 5：W-mask 死锁（Q1 的 CU 级数值见证）——masked 向量指令，
     操作数 0 正常返回、regOrder=3 永不返回 ⇒ 永久滞留 s_add、control.ready 不再恢复 ---- -/

def cuCtrlMasked : CuCtrl :=
  { cuCtrl0 with sel_alu1 := cuA1_VRS1, reg_idx1 := 1#8, isvec := true, mask := true }

def cuTrDead : List CuInputs :=
  [ { cuInNop with controlValid := true, ctrl := cuCtrlMasked }
  , { cuInNop with bv0 := true, bb0 := ⟨0#2, cuRowA, cuRow0⟩ }  -- vs1 照常返回
  , cuInNop, cuInNop, cuInNop ]

theorem cuT_deadlock_state : (cuRun cuInit cuTrDead).state = cuSAdd := by native_decide
theorem cuT_deadlock_rdy : cuControlRdy (cuRun cuInit cuTrDead) = false := by native_decide
-- ready = 0111：默认字段带来的 A2_SIZE/A3_PC 捷径（bit1/bit2）+ port0 返回（bit0），
-- 唯独 mask 的 bit3 永远等不到返回
theorem cuT_deadlock_ready : (cuRun cuInit cuTrDead).ready = 7#4 := by native_decide
theorem cuT_deadlock_ready3 : ((cuRun cuInit cuTrDead).ready &&& 8#4) = 0#4 := by native_decide

end CuRegressionTests

/- ========================================================================= -/
/- 6. 结构保持引理（证明基础设施）                                            -/
/- ========================================================================= -/

theorem cuBv2_cases (x : BitVec 2) :
    x = cuSIdle ∨ x = cuSAdd ∨ x = cuSOut ∨ x = 3#2 := by
  unfold cuSIdle cuSAdd cuSOut; bv_decide

theorem cuBv2_plain (x : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 ∨ x = 3#2 := by bv_decide

theorem cuControlFire_state (s : CuState) (i : CuInputs) (h : cuControlFire s i = true) :
    s.state = cuSIdle := by
  simp only [cuControlFire, cuControlRdy, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.1

theorem cuControlFire_false_of_not_idle (s : CuState) (i : CuInputs)
    (hs : s.state ≠ cuSIdle) : cuControlFire s i = false := by
  have h1 : (s.state == cuSIdle) = false := by simp [hs]
  simp [cuControlFire, cuControlRdy, h1]

theorem cuBankFireK_false (s : CuState) (i : CuInputs) (k : Nat)
    (hs : s.state ≠ cuSAdd) (hf : cuControlFire s i = false) :
    cuBankFireK s i k = false := by
  have h1 : (s.state == cuSAdd) = false := by simp [hs]
  simp [cuBankFireK, cuBankInRdyK, h1, hf]

theorem cuBankFireK_bankV (s : CuState) (i : CuInputs) (k : Nat)
    (h : cuBankFireK s i k = true) : i.bankV k = true := by
  simp only [cuBankFireK, Bool.and_eq_true] at h
  exact h.1

-- cuPreBank 投影
theorem cuPreBank_state (s : CuState) (i : CuInputs) :
    (cuPreBank s i).state = cuStateTrans s i := by
  unfold cuPreBank; split <;> rfl

theorem cuPreBank_valid (s : CuState) (i : CuInputs) :
    (cuPreBank s i).valid =
      if s.state == cuSOut then 0#4 else (cuAccept s i).valid := by
  unfold cuPreBank; split <;> rfl

theorem cuPreBank_ready (s : CuState) (i : CuInputs) :
    (cuPreBank s i).ready =
      if s.state == cuSOut then 0#4 else (cuAccept s i).ready := by
  unfold cuPreBank; split <;> rfl

theorem cuPreBank_controlReg (s : CuState) (i : CuInputs) :
    (cuPreBank s i).controlReg = (cuAccept s i).controlReg := by
  unfold cuPreBank; split <;> rfl

theorem cuPreBank_rsReg0 (s : CuState) (i : CuInputs) :
    (cuPreBank s i).rsReg0 = (cuAccept s i).rsReg0 := by
  unfold cuPreBank; split <;> rfl

-- cuAccept 投影
theorem cuAccept_valid (s : CuState) (i : CuInputs) :
    (cuAccept s i).valid = if cuControlFire s i then 0xF#4 else s.valid := by
  unfold cuAccept; split <;> rfl

theorem cuAccept_ready (s : CuState) (i : CuInputs) :
    (cuAccept s i).ready = if cuControlFire s i then cuReadyWire i.ctrl else s.ready := by
  unfold cuAccept; split <;> rfl

theorem cuAccept_controlReg (s : CuState) (i : CuInputs) :
    (cuAccept s i).controlReg = if cuControlFire s i then i.ctrl else s.controlReg := by
  unfold cuAccept; split <;> rfl

-- cuBankPort 投影（保持字段；regOrder 二位枚举 + simp_all 消分支）
theorem cuBankPort_state (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat) :
    (cuBankPort pre i st k).state = st.state := by
  by_cases hf : cuBankFireK pre i k = true
  · rcases cuBv2_plain (i.bankB k).regOrder with h0|h0|h0|h0 <;> simp_all [cuBankPort]
  · simp [cuBankPort, hf]

theorem cuBankPort_valid (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat) :
    (cuBankPort pre i st k).valid = st.valid := by
  by_cases hf : cuBankFireK pre i k = true
  · rcases cuBv2_plain (i.bankB k).regOrder with h0|h0|h0|h0 <;> simp_all [cuBankPort]
  · simp [cuBankPort, hf]

theorem cuBankPort_controlReg (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat) :
    (cuBankPort pre i st k).controlReg = st.controlReg := by
  by_cases hf : cuBankFireK pre i k = true
  · rcases cuBv2_plain (i.bankB k).regOrder with h0|h0|h0|h0 <;> simp_all [cuBankPort]
  · simp [cuBankPort, hf]

/-- bankIn 对 ready 的净效果：按 regOrder 置位（:286,:301,:310,:315 的统一形式） -/
theorem cuBankPort_ready (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat) :
    (cuBankPort pre i st k).ready =
      st.ready ||| (if cuBankFireK pre i k then 1#4 <<< (i.bankB k).regOrder.zeroExtend 4
                   else 0#4) := by
  by_cases hf : cuBankFireK pre i k = true
  · rcases cuBv2_plain (i.bankB k).regOrder with h0|h0|h0|h0 <;>
      simp_all [cuBankPort] <;> bv_decide
  · simp [cuBankPort, hf]

/-- rsReg0 只被 regOrder=0 的返回改写（:267-286） -/
theorem cuBankPort_rsReg0 (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat)
    (h : cuBankFireK pre i k = false ∨ (i.bankB k).regOrder ≠ 0#2) :
    (cuBankPort pre i st k).rsReg0 = st.rsReg0 := by
  by_cases hf : cuBankFireK pre i k = true
  · have hr : (i.bankB k).regOrder ≠ 0#2 := by
      rcases h with h | h
      · exact absurd h (by simp [hf])
      · exact h
    rcases cuBv2_plain (i.bankB k).regOrder with h0|h0|h0|h0 <;> simp_all [cuBankPort]
  · simp [cuBankPort, hf]

/-- ready 只增 bit：bit0 已为 1 时经 bankIn 后仍为 1 -/
theorem cuBankPort_ready_bit0 (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat)
    (hb : (st.ready &&& 1#4) = 1#4) :
    ((cuBankPort pre i st k).ready &&& 1#4) = 1#4 := by
  rw [cuBankPort_ready]
  generalize (i.bankB k).regOrder = r
  by_cases hf : cuBankFireK pre i k = true <;> simp [hf] <;> bv_decide

/-- regOrder ≠ 3 时，`1 <<< regOrder` 不置 bit3（:286,:301,:310 三分支） -/
theorem cuBankShift_bit3 (r : BitVec 2) (h : r ≠ 3#2) :
    ((1#4 <<< r.zeroExtend 4) &&& 8#4) = 0#4 := by bv_decide

/-- ready 只增 bit：bit3 为 0 且本端口不是 regOrder=3 返回时，bit3 保持 0（W-mask 引理） -/
theorem cuBankPort_ready_bit3 (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat)
    (h : cuBankFireK pre i k = true → (i.bankB k).regOrder ≠ 3#2)
    (hb : (st.ready &&& 8#4) = 0#4) :
    ((cuBankPort pre i st k).ready &&& 8#4) = 0#4 := by
  rw [cuBankPort_ready]
  by_cases hf : cuBankFireK pre i k = true
  · have hr := cuBankShift_bit3 _ (h hf)
    simp only [hf, if_true]
    generalize (1#4 <<< (i.bankB k).regOrder.zeroExtend 4) = m at hr ⊢
    bv_decide
  · simp only [Bool.not_eq_true] at hf
    simp_all

/-- ready 只增 bit：全 1 保持全 1 -/
theorem cuBankPort_ready_full (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat)
    (hb : st.ready = 0xF#4) : (cuBankPort pre i st k).ready = 0xF#4 := by
  rw [cuBankPort_ready]
  generalize (i.bankB k).regOrder = r
  by_cases hf : cuBankFireK pre i k = true <;> simp [hf] <;> bv_decide

-- cuStep 投影（组合形式）
theorem cuStep_state (s : CuState) (i : CuInputs) :
    (cuStep s i).state = cuStateTrans s i := by
  simp [cuStep, cuBankPort_state, cuPreBank_state]

theorem cuStep_valid (s : CuState) (i : CuInputs) :
    (cuStep s i).valid =
      (if s.state == cuSOut then 0#4 else if cuControlFire s i then 0xF#4 else s.valid) := by
  simp [cuStep, cuBankPort_valid, cuPreBank_valid, cuAccept_valid]

theorem cuStep_controlReg (s : CuState) (i : CuInputs) :
    (cuStep s i).controlReg = if cuControlFire s i then i.ctrl else s.controlReg := by
  simp [cuStep, cuBankPort_controlReg, cuPreBank_controlReg, cuAccept_controlReg]

-- readyWire 位级事实
theorem cuReadyWire_bit0 (c : CuCtrl) :
    (cuReadyWire c &&& 1#4) = if cuRwK c 0 then 1#4 else 0#4 := by
  by_cases h0 : cuRwK c 0 = true <;> by_cases h1 : cuRwK c 1 = true <;>
    by_cases h2 : cuRwK c 2 = true <;> by_cases h3 : cuRwK c 3 = true <;>
    simp [cuReadyWire, h0, h1, h2, h3] <;> bv_decide

theorem cuReadyWire_bit3 (c : CuCtrl) :
    (cuReadyWire c &&& 8#4) = if cuRwK c 3 then 8#4 else 0#4 := by
  by_cases h0 : cuRwK c 0 = true <;> by_cases h1 : cuRwK c 1 = true <;>
    by_cases h2 : cuRwK c 2 = true <;> by_cases h3 : cuRwK c 3 = true <;>
    simp [cuReadyWire, h0, h1, h2, h3] <;> bv_decide

/-- readyWire(3)=0（masked 指令）时 readyWire 不可能全 1 ⇒ 接受后必走 s_add（:145） -/
theorem cuReadyWire_ne_full_of_rw3 (c : CuCtrl) (h : cuRwK c 3 = false) :
    cuReadyWire c ≠ 0xF#4 := by
  intro heq
  have hb := cuReadyWire_bit3 c
  rw [heq, h] at hb
  simp at hb

/- ========================================================================= -/
/- 7. 定理                                                                    -/
/- ========================================================================= -/

/- ---- T2：controlReg 保持（:61,185） ---- -/

theorem cuT2_controlReg_accept (s : CuState) (i : CuInputs) (hf : cuControlFire s i = true) :
    (cuStep s i).controlReg = i.ctrl := by
  simp [cuStep_controlReg, hf]

theorem cuT2_controlReg_hold (s : CuState) (i : CuInputs) (hf : cuControlFire s i = false) :
    (cuStep s i).controlReg = s.controlReg := by
  simp [cuStep_controlReg, hf]

/-- issue.bits.control 恒为 controlReg（:61），故接受后 issue 的控制字即接受时控制字 -/
theorem cuT2_issue_control (s : CuState) : (cuIssueBits s).control = s.controlReg := rfl

/- ---- T1：issue 完备性——从接受到 s_out 的不变量 ---- -/

/-- 可达状态不变式：state=idle ⇒ valid=0（才可再接受）；state=add ⇒ valid=1111；
    state=s_out ⇒ valid=ready（所需的全部 ready 已置位，:150-154 的进入条件保持） -/
def cuInv (s : CuState) : Prop :=
  s.state ≠ 3#2 ∧
  (s.state = cuSIdle → s.valid = 0#4) ∧
  (s.state = cuSAdd → s.valid = 0xF#4) ∧
  (s.state = cuSOut → s.valid = s.ready)

theorem cuInv_init : cuInv cuInit :=
  ⟨by decide, fun _ => rfl, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem cuInv_step (s : CuState) (i : CuInputs) (h : cuInv s) : cuInv (cuStep s i) := by
  obtain ⟨hne3, hid, had, hou⟩ := h
  have hst : (cuStep s i).state = cuStateTrans s i := cuStep_state s i
  have hvl : (cuStep s i).valid =
      (if s.state == cuSOut then 0#4 else if cuControlFire s i then 0xF#4 else s.valid) :=
    cuStep_valid s i
  rcases cuBv2_cases s.state with hs | hs | hs | hs
  · -- s_idle
    have hsi : (s.state == cuSIdle) = true := by simp [hs]
    have hsa : (s.state == cuSAdd) = false := by rw [hs]; decide
    have hso : (s.state == cuSOut) = false := by rw [hs]; decide
    by_cases hf : cuControlFire s i = true
    · by_cases hrw : cuReadyWire i.ctrl = 0xF#4
      · -- 全捷径 → s_out，valid' = ready' = 0xF
        have hstate : (cuStep s i).state = cuSOut := by
          rw [hst]; simp [cuStateTrans, hsi, hf, hrw]
        have hvalid : (cuStep s i).valid = 0xF#4 := by rw [hvl]; simp [hso, hf]
        have hready : (cuStep s i).ready = 0xF#4 := by
          have hpre : (cuPreBank s i).ready = 0xF#4 := by
            rw [cuPreBank_ready]; simp [hso, cuAccept_ready, hf, hrw]
          simp only [cuStep]
          exact cuBankPort_ready_full _ _ _ _ (cuBankPort_ready_full _ _ _ _
            (cuBankPort_ready_full _ _ _ _ (cuBankPort_ready_full _ _ _ _ hpre)))
        exact ⟨by rw [hstate]; decide,
          fun h' => absurd (hstate.symm.trans h') (by decide),
          fun h' => absurd (hstate.symm.trans h') (by decide),
          fun _ => hvalid.trans hready.symm⟩
      · -- 部分捷径 → s_add，valid' = 0xF
        have hstate : (cuStep s i).state = cuSAdd := by
          rw [hst]; simp [cuStateTrans, hsi, hf, beq_iff_eq, hrw]
        have hvalid : (cuStep s i).valid = 0xF#4 := by rw [hvl]; simp [hso, hf]
        exact ⟨by rw [hstate]; decide,
          fun h' => absurd (hstate.symm.trans h') (by decide),
          fun _ => hvalid,
          fun h' => absurd (hstate.symm.trans h') (by decide)⟩
    · -- 无 fire → 滞留 idle，valid' = 0
      have hstate : (cuStep s i).state = cuSIdle := by
        rw [hst]; simp [cuStateTrans, hsi, hf]
      have hvalid : (cuStep s i).valid = 0#4 := by rw [hvl]; simp [hso, hf, hid hs]
      exact ⟨by rw [hstate]; decide,
        fun _ => hvalid,
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun h' => absurd (hstate.symm.trans h') (by decide)⟩
  · -- s_add
    have hsi : (s.state == cuSIdle) = false := by rw [hs]; decide
    have hsa : (s.state == cuSAdd) = true := by simp [hs]
    have hso : (s.state == cuSOut) = false := by rw [hs]; decide
    have hf : cuControlFire s i = false :=
      cuControlFire_false_of_not_idle s i (by rw [hs]; decide)
    have hvalid : (cuStep s i).valid = 0xF#4 := by rw [hvl]; simp [hso, hf, had hs]
    by_cases hvr : s.valid = s.ready
    · -- valid==ready → s_out；ready 必已为 0xF，bankIn 只增 bit 保持 0xF
      have hstate : (cuStep s i).state = cuSOut := by
        rw [hst]; simp [cuStateTrans, hsi, hsa, hvr]
      have hready : (cuStep s i).ready = 0xF#4 := by
        have hsr : s.ready = 0xF#4 := hvr.symm.trans (had hs)
        have hpre : (cuPreBank s i).ready = 0xF#4 := by
          rw [cuPreBank_ready]; simp [hso, cuAccept_ready, hf, hsr]
        simp only [cuStep]
        exact cuBankPort_ready_full _ _ _ _ (cuBankPort_ready_full _ _ _ _
          (cuBankPort_ready_full _ _ _ _ (cuBankPort_ready_full _ _ _ _ hpre)))
      exact ⟨by rw [hstate]; decide,
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun _ => hvalid.trans hready.symm⟩
    · -- 未集齐 → 滞留 s_add
      have hstate : (cuStep s i).state = cuSAdd := by
        rw [hst]; simp [cuStateTrans, hsi, hsa, beq_iff_eq, hvr]
      exact ⟨by rw [hstate]; decide,
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun _ => hvalid,
        fun h' => absurd (hstate.symm.trans h') (by decide)⟩
  · -- s_out：valid'/ready' 清零（D10）；issue.fire ⇔ 回 idle
    have hsi : (s.state == cuSIdle) = false := by rw [hs]; decide
    have hsa : (s.state == cuSAdd) = false := by rw [hs]; decide
    have hso : (s.state == cuSOut) = true := by simp [hs]
    have hf : cuControlFire s i = false :=
      cuControlFire_false_of_not_idle s i (by rw [hs]; decide)
    have hvalid : (cuStep s i).valid = 0#4 := by rw [hvl]; simp [hso]
    have hready : (cuStep s i).ready = 0#4 := by
      have hbf : ∀ k, cuBankFireK s i k = false :=
        fun k => cuBankFireK_false s i k (by rw [hs]; decide) hf
      have hpre : (cuPreBank s i).ready = 0#4 := by rw [cuPreBank_ready]; simp [hso]
      simp only [cuStep]
      rw [cuBankPort_ready, cuBankPort_ready, cuBankPort_ready, cuBankPort_ready, hpre]
      simp [hbf]
    by_cases hif : cuIssueFire s i = true
    · have hstate : (cuStep s i).state = cuSIdle := by
        rw [hst]; simp [cuStateTrans, hsi, hsa, hso, hif]
      exact ⟨by rw [hstate]; decide,
        fun _ => hvalid,
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun h' => absurd (hstate.symm.trans h') (by decide)⟩
    · have hstate : (cuStep s i).state = cuSOut := by
        rw [hst]; simp [cuStateTrans, hsi, hsa, hso, hif]
      exact ⟨by rw [hstate]; decide,
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun h' => absurd (hstate.symm.trans h') (by decide),
        fun _ => hvalid.trans hready.symm⟩
  · exact absurd hs hne3

/-- T1（run 形式）：从 cuInit 出发任意拍后不变式保持 -/
theorem cuT1_run (s : CuState) (ins : List CuInputs) (h : cuInv s) :
    cuInv (cuRun s ins) := by
  induction ins generalizing s with
  | nil => exact h
  | cons j js ih =>
    show cuInv (cuRun (cuStep s j) js)
    exact ih (cuStep s j) (cuInv_step s j h)

/-- T1 推論：issue.valid（state=s_out）⇒ 接受时所需的全部 ready 已置位（valid=ready） -/
theorem cuT1_sout_valid_eq_ready (ins : List CuInputs)
    (h : (cuRun cuInit ins).state = cuSOut) :
    (cuRun cuInit ins).valid = (cuRun cuInit ins).ready :=
  (cuT1_run cuInit ins cuInv_init).2.2.2 h

/- ---- T4：s_out 拍 issue.fire ⇒ 下一拍 s_idle 且 valid/ready 全清（:155-158,258-262） ---- -/

theorem cuT4_sout_fire (s : CuState) (i : CuInputs)
    (hs : s.state = cuSOut) (hr : i.issueReady = true) :
    (cuStep s i).state = cuSIdle ∧ (cuStep s i).valid = 0#4 ∧ (cuStep s i).ready = 0#4 := by
  have hso : (s.state == cuSOut) = true := by simp [hs]
  have hsi : (s.state == cuSIdle) = false := by rw [hs]; decide
  have hsa : (s.state == cuSAdd) = false := by rw [hs]; decide
  have hcf : cuControlFire s i = false :=
    cuControlFire_false_of_not_idle s i (by rw [hs]; decide)
  have hif : cuIssueFire s i = true := by simp [cuIssueFire, cuIssueValid, hso, hr]
  refine ⟨?_, ?_, ?_⟩
  · rw [cuStep_state]; simp [cuStateTrans, hsi, hsa, hso, hif]
  · rw [cuStep_valid]; simp [hso]
  · have hbf : ∀ k, cuBankFireK s i k = false :=
      fun k => cuBankFireK_false s i k (by rw [hs]; decide) hcf
    have hpre : (cuPreBank s i).ready = 0#4 := by rw [cuPreBank_ready]; simp [hso]
    simp only [cuStep]
    rw [cuBankPort_ready, cuBankPort_ready, cuBankPort_ready, cuBankPort_ready, hpre]
    simp [hbf]

/- ---- T3：立即数捷径正确（:223-226 经 rfImmGen，复用 RegFile.lean 的 ImmGen 模型） ---- -/

theorem cuT3_imm_shortcut (s : CuState) (i : CuInputs)
    (hf : cuControlFire s i = true) (hsel : i.ctrl.sel_alu1 = cuA1_IMM)
    (hx : cuXbarOk i) :
    (cuStep s i).rsReg0 = cuBcast (rfImmGen i.ctrl.sel_imm i.ctrl.inst i.ctrl.imm_ext) ∧
      ((cuStep s i).ready &&& 1#4) = 1#4 := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hs : s.state = cuSIdle := cuControlFire_state s i hf
  have hso : (s.state == cuSOut) = false := by rw [hs]; decide
  have hacc0 : (cuAccept s i).rsReg0 =
      cuBcast (rfImmGen i.ctrl.sel_imm i.ctrl.inst i.ctrl.imm_ext) := by
    simp [cuAccept, hf, hsel, cuImmOut, hs, cuA1_IMM]
  have haccR : (cuAccept s i).ready = cuReadyWire i.ctrl := by simp [cuAccept_ready, hf]
  have hrw0 : cuRwK i.ctrl 0 = true := by simp [cuRwK, cuRw0, hsel, cuA1_IMM]
  have hf0 : cuBankFireK s i 0 = false := by
    have hsa : (s.state == cuSAdd) = false := by rw [hs]; decide
    simp [cuBankFireK, cuBankInRdyK, hsa, hf, hrw0]
  constructor
  · simp only [cuStep]
    rw [cuBankPort_rsReg0 s i _ 3 (Or.inr (by rw [hx3]; decide)),
        cuBankPort_rsReg0 s i _ 2 (Or.inr (by rw [hx2]; decide)),
        cuBankPort_rsReg0 s i _ 1 (Or.inr (by rw [hx1]; decide)),
        cuBankPort_rsReg0 s i _ 0 (Or.inl hf0),
        cuPreBank_rsReg0, hacc0]
  · have hpreR : ((cuPreBank s i).ready &&& 1#4) = 1#4 := by
      rw [cuPreBank_ready]; simp [hso, haccR, cuReadyWire_bit0, hrw0]
    simp only [cuStep]
    exact cuBankPort_ready_bit0 _ _ _ _ (cuBankPort_ready_bit0 _ _ _ _
      (cuBankPort_ready_bit0 _ _ _ _ (cuBankPort_ready_bit0 _ _ _ _ hpreR)))

/- ---- W-mask：masked 指令无 regOrder=3 返回 ⇒ 永不到 s_out（Q1，I 类死锁链 CU 段） ---- -/

/-- W-mask 不变式：滞留 s_add、valid(3)=1、ready(3)=0（mask 操作数未收齐） -/
def cuWmaskInv (s : CuState) : Prop :=
  s.state = cuSAdd ∧ (s.valid &&& 8#4) = 8#4 ∧ (s.ready &&& 8#4) = 0#4

/-- 接受 masked 指令（control.mask=1）即进入 W-mask 不变式
    （readyWire(3)=!mask=0 ⇒ :145 走 s_add 而非 s_out） -/
theorem cuWmask_accept (s : CuState) (i : CuInputs)
    (hf : cuControlFire s i = true) (hm : i.ctrl.mask = true)
    (h3 : ∀ k, cuBankFireK s i k = true → (i.bankB k).regOrder ≠ 3#2) :
    cuWmaskInv (cuStep s i) := by
  have hs : s.state = cuSIdle := cuControlFire_state s i hf
  have hsi : (s.state == cuSIdle) = true := by simp [hs]
  have hso : (s.state == cuSOut) = false := by rw [hs]; decide
  have hrw3 : cuRwK i.ctrl 3 = false := by simp [cuRwK, cuRw3, hm]
  have hrwf : cuReadyWire i.ctrl ≠ 0xF#4 := cuReadyWire_ne_full_of_rw3 _ hrw3
  refine ⟨?_, ?_, ?_⟩
  · rw [cuStep_state]; simp [cuStateTrans, hsi, hf, beq_iff_eq, hrwf]
  · have hvalid : (cuStep s i).valid = 0xF#4 := by rw [cuStep_valid]; simp [hso, hf]
    rw [hvalid]; decide
  · have hpre : ((cuPreBank s i).ready &&& 8#4) = 0#4 := by
      rw [cuPreBank_ready]
      simp [hso, cuAccept_ready, hf, cuReadyWire_bit3, hrw3]
    simp only [cuStep]
    exact cuBankPort_ready_bit3 _ _ _ _ (h3 3) (cuBankPort_ready_bit3 _ _ _ _ (h3 2)
      (cuBankPort_ready_bit3 _ _ _ _ (h3 1) (cuBankPort_ready_bit3 _ _ _ _ (h3 0) hpre)))

/-- W-mask 单拍保持：无 regOrder=3 返回 ⇒ 不变式保持（valid(3)=1 且 ready(3)=0
    ⇒ valid≠ready ⇒ :150-154 恒走 s_add） -/
theorem cuWmask_step (s : CuState) (i : CuInputs) (h : cuWmaskInv s)
    (h3 : ∀ k, cuBankFireK s i k = true → (i.bankB k).regOrder ≠ 3#2) :
    cuWmaskInv (cuStep s i) := by
  obtain ⟨hst, hv, hr⟩ := h
  have hsi : (s.state == cuSIdle) = false := by rw [hst]; decide
  have hsa : (s.state == cuSAdd) = true := by simp [hst]
  have hso : (s.state == cuSOut) = false := by rw [hst]; decide
  have hcf : cuControlFire s i = false :=
    cuControlFire_false_of_not_idle s i (by rw [hst]; decide)
  have hvr : s.valid ≠ s.ready := by
    intro heq
    rw [heq, hr] at hv
    exact absurd hv (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [cuStep_state]; simp [cuStateTrans, hsi, hsa, beq_iff_eq, hvr]
  · have hvalid : (cuStep s i).valid = s.valid := by rw [cuStep_valid]; simp [hso, hcf]
    rw [hvalid]; exact hv
  · have hpre : ((cuPreBank s i).ready &&& 8#4) = 0#4 := by
      rw [cuPreBank_ready]; simp [hso, cuAccept_ready, hcf, hr]
    simp only [cuStep]
    exact cuBankPort_ready_bit3 _ _ _ _ (h3 3) (cuBankPort_ready_bit3 _ _ _ _ (h3 2)
      (cuBankPort_ready_bit3 _ _ _ _ (h3 1) (cuBankPort_ready_bit3 _ _ _ _ (h3 0) hpre)))

/-- W-mask（run 形式）：输入序列从不携带 regOrder=3 的有效返回 ⇒ 永不离开 s_add，
    特别地永不进入 s_out（issue.valid 永不置位）。
    注：前提用 bankV（valid）而非 fire——对应顶层事实"crossbar 端口 3 永不置
    valid"（mask 请求 rsType(3)=0 在 operandArbiter :362-365 永不授予）。 -/
theorem cuWmask_run (s : CuState) (ins : List CuInputs) (h : cuWmaskInv s)
    (h3 : ∀ j ∈ ins, ∀ k, j.bankV k = true → (j.bankB k).regOrder ≠ 3#2) :
    cuWmaskInv (cuRun s ins) := by
  induction ins generalizing s with
  | nil => exact h
  | cons j js ih =>
    show cuWmaskInv (cuRun (cuStep s j) js)
    apply ih
    · exact cuWmask_step s j h
        (fun k hf => h3 j List.mem_cons_self k (cuBankFireK_bankV s j k hf))
    · intro j' hj' k hv
      exact h3 j' (List.mem_cons_of_mem j hj') k hv

/-- W-mask 死锁（完整链的 CU 段）：从 cuInit 接受一条 masked 指令后，只要
    regOrder=3 的返回从不出现（顶层 :362-365 保证），CU 永久滞留 s_add，
    control.ready 永不恢复（该 warp 的 CU 不再接受新指令）。 -/
theorem cuWmask_deadlock (i0 : CuInputs) (ins : List CuInputs)
    (hv0 : i0.controlValid = true) (hm : i0.ctrl.mask = true)
    (h3 : ∀ j ∈ (i0 :: ins), ∀ k, j.bankV k = true → (j.bankB k).regOrder ≠ 3#2) :
    (cuRun (cuStep cuInit i0) ins).state = cuSAdd ∧
      cuControlRdy (cuRun (cuStep cuInit i0) ins) = false := by
  have hfi : cuControlFire cuInit i0 = true := by
    simp [cuControlFire, cuControlRdy, hv0, cuInit]
  have h30 : ∀ k, cuBankFireK cuInit i0 k = true → (i0.bankB k).regOrder ≠ 3#2 :=
    fun k hf => h3 i0 List.mem_cons_self k (cuBankFireK_bankV cuInit i0 k hf)
  have hinv : cuWmaskInv (cuStep cuInit i0) := cuWmask_accept cuInit i0 hfi hm h30
  have h3' : ∀ j ∈ ins, ∀ k, j.bankV k = true → (j.bankB k).regOrder ≠ 3#2 :=
    fun j hj k hv => h3 j (List.mem_cons_of_mem i0 hj) k hv
  have hrun := cuWmask_run (cuStep cuInit i0) ins hinv h3'
  refine ⟨hrun.1, ?_⟩
  have hsi : ((cuRun (cuStep cuInit i0) ins).state == cuSIdle) = false := by
    rw [hrun.1]; decide
  simp [cuControlRdy, hsi]

/- ---- Q3：:129 第二析取支在 CU 接口层面的可达性 ---- -/

/-- 接受拍 bankIn(k).ready = !readyWire(k)：:129 的第二析取支在接口层面是活的
    （对需要寄存器读的操作数为高）；系统内不可达的论证见文件头 Q3。 -/
theorem cuQ129_bankInRdy_accept (s : CuState) (i : CuInputs) (k : Nat)
    (hf : cuControlFire s i = true) :
    cuBankInRdyK s i k = !cuRwK i.ctrl k := by
  have hs : s.state = cuSIdle := cuControlFire_state s i hf
  have hsa : (s.state == cuSAdd) = false := by rw [hs]; decide
  simp [cuBankInRdyK, hsa, hf]

/- ========================================================================= -/
/- 8. 公理审计（bv_decide 会引入每个定理私有的 LRAT 检查 trust 公理，           -/
/-    形如 `…._native.bv_decide.ax_…`；native_decide 多 Lean.ofReduceBool）   -/
/- ========================================================================= -/

#print axioms cuT1_run
#print axioms cuT1_sout_valid_eq_ready
#print axioms cuT2_controlReg_accept
#print axioms cuT2_issue_control
#print axioms cuT3_imm_shortcut
#print axioms cuT4_sout_fire
#print axioms cuWmask_accept
#print axioms cuWmask_step
#print axioms cuWmask_run
#print axioms cuWmask_deadlock
#print axioms cuQ129_bankInRdy_accept
#print axioms cuT_deadlock_state

end Ventus.Schedule
