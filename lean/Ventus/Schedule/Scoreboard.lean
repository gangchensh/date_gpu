/- ========================================================================= -/
/-                     Schedule/Scoreboard.lean                              -/
/-  发射记分板（Scoreboard）的 Lean 4 模型与冒险阻塞契约（M0 试点三）          -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/scoreboard.scala   -/
/-    （ScoreboardUtil 在 82-99 行；Scoreboard 在 100-143 行；                -/
/-      sel_alu/branch 常量在 pipeline/DecodeUnit.scala:23-41）               -/
/-  每 warp 一个 Scoreboard 实例（pipe.scala 中 scoreb(i)），本文件建模单实例。-/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. ScoreboardUtil 的 `_next` 是 Scala var 上的链式改写：同一拍内多次      -/
/-      set/clear 按程序序依次作用（后调用看到先调用的结果），`ens` 为任一     -/
/-      使能的或，ens 时 `_r := _next`（:90-97）。本模型用语义等价的          -/
/-      `List SbOp` + `List.foldl` 按序折叠实现（sbUtilStep），并用引理       -/
/-      sbUtilStep_set_clear 把"两操作（先 set 后 clear）"的常用情形固定为    -/
/-      组合形式 sbSetClear，便于 bv_decide。                                 -/
/-  D2. Chisel `1.U << addr`（:92）的结果宽度会被加宽再在 `_r := _next` 时    -/
/-      截断回 n 位；addr 为 8 位（≤ 255 < 256），1 位 util 的 addr 恒 0，    -/
/-      截断无语义效果。建模为 `1#n <<< BitVec.zeroExtend n addr`（BitVec     -/
/-      移位量 ≥ 位宽时结果为 0，与截断后语义一致）。                         -/
/-  D3. `readBypassed`（:87，读 _next 的旁路视图）在源码中无任何消费者，      -/
/-      不建模。后果：delay 只读当前 `_r`（:86），写回清除/发射置位都要下一   -/
/-      拍才反映到 delay（保守多停一拍，非 bug）。                            -/
/-  D4. MuxLookup（:121-127）建模为按键值顺序的 if-else 链。read3 的四个      -/
/-      键（A3_VRS3=1, A3_SD=3, A3_FRS3=2, A3_PC=0）已覆盖 2 位全域，        -/
/-      MuxLookup 的 default(false.B) 对 read3 不可达；read1/read2 的         -/
/-      default 覆盖 A1_PC/A1_IMM、A2_X/A2_IMM 等不读寄存器的选择。           -/
/-  D5. 1 位 util（beq/OpColV/OpColX/fence）用 BitVec 1 表示，与 256 位       -/
/-      util 共用同一套泛型机制（sbUtilStep/sbRead）。                        -/
/-  D6. wb_v_ctrl/wb_x_ctrl 只取 wvd/wxd/reg_idxw 三个字段（:110,:112）。     -/
/-  D7. if_ctrl 与 ibuffer_if_ctrl 是两个不同的 CtrlSigs 实例：set 用         -/
/-      if_ctrl（本拍发射的指令），delay 的九个读全用 ibuffer_if_ctrl         -/
/-      （ibuffer 头指令）。SbInputs 只含 if_ctrl；sbDelay 单独接收一个       -/
/-      SbCtrl 参数。                                                         -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1. scalarReg（zero=true）的 `_r` bit0 可被 set 置 1（:84 的 mask 不      -/
/-      屏蔽 bit0），只是读视图 r 屏蔽之（:89）。且任一后续使能操作（任何    -/
/-      地址的 set/clear）都会以 masked view 为折叠基底，把 _r 的 bit0 冲     -/
/-      掉。行为无害（x0 永不阻塞，定理 sb1_* 钉死），属实现细节。            -/
/-  Q2. 同拍同址 set 后 clear → clear 胜（后写胜，:109-110 的程序序）。对     -/
/-      vectorReg/scalarReg，"发射写 addr"与"写回清 addr"同拍同址的情形被     -/
/-      readw 的 WAW 检查（:129）+ 读非旁路（D3）联合阻止：写回当拍 readw     -/
/-      仍读到占用位=1，发射被 delay，故 set/clear 同拍同址不可达。clear      -/
/-      胜的优先级在此协议下无害。                                            -/
/-  Q3. OpColRegV/X 的同拍 in_fire/out_fire（:115-118）同样是 clear 胜：      -/
/-      若 output collector 允许"完成一个事务的同时新占一个事务"，占用位会    -/
/-      被错误冲掉（应为保持不变）。是否可触发取决于 op_col 通道外围协议，    -/
/-      本文件范围内无法判定，记为待查疑点（非断言 bug）。                    -/
/-  Q4. fenceReg 注释自承"LSU 重建后可取消"（:107），:108 有 CSR 相关 TODO。 -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Schedule

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 常量（DecodeUnit.scala:23-41）                                          -/
/- ========================================================================= -/

def sbB_R     : BitVec 2 := 3  -- DecodeUnit.scala:26（branch === B_R 用于 A3_PC 分支）

def sbA1_RS1  : BitVec 2 := 1  -- DecodeUnit.scala:27
def sbA1_VRS1 : BitVec 2 := 2  -- DecodeUnit.scala:28

def sbA2_RS2  : BitVec 2 := 1  -- DecodeUnit.scala:38
def sbA2_VRS2 : BitVec 2 := 2  -- DecodeUnit.scala:40

def sbA3_PC   : BitVec 2 := 0  -- DecodeUnit.scala:35
def sbA3_VRS3 : BitVec 2 := 1  -- DecodeUnit.scala:32
def sbA3_FRS3 : BitVec 2 := 2  -- DecodeUnit.scala:34
def sbA3_SD   : BitVec 2 := 3  -- DecodeUnit.scala:33

/- ========================================================================= -/
/- 2. ScoreboardUtil 泛型模型（scoreboard.scala:82-99）                       -/
/- ========================================================================= -/

/-- 单拍内对某个 util 的一次 set/clear 调用（:84-85） -/
inductive SbOp where
  | set   (en : Bool) (addr : BitVec 8)
  | clear (en : Bool) (addr : BitVec 8)

/-- 该操作的使能（对应 :95 的 `ens = ens || en` 中并入的项） -/
def SbOp.en : SbOp → Bool
  | .set en _ => en
  | .clear en _ => en

/-- `Mux(en, 1.U << addr, 0.U)`（:92），宽度截断见 D2 -/
def sbMask {n : Nat} (en : Bool) (addr : BitVec 8) : BitVec n :=
  if en then 1#n <<< BitVec.zeroExtend n addr else 0#n

/-- 读视图 `r`（:89）：zero=true 时 `(_r >> 1) << 1`（bit0 恒 0，为 x0 服务） -/
def sbView {n : Nat} (zero : Bool) (r : BitVec n) : BitVec n :=
  if zero then (r >>> 1#n) <<< 1#n else r

/-- `read(addr) = r(addr)`（:86）：读当前寄存器视图，非旁路。
    取位用移位形式（bv_decide 不支持变量 Nat 下标 getLsbD）。 -/
def sbRead {n : Nat} (zero : Bool) (r : BitVec n) (addr : BitVec 8) : Bool :=
  ((sbView zero r >>> BitVec.zeroExtend n addr) &&& 1#n) == 1#n

/-- 单个操作作用于 _next（:84-85 的 update 体） -/
def sbApplyOp {n : Nat} (next : BitVec n) (op : SbOp) : BitVec n :=
  match op with
  | .set en addr => next ||| sbMask en addr
  | .clear en addr => next &&& ~~~sbMask en addr

/-- 单拍状态转移（:90-97）：任一使能时 `_r := _next`，
    否则 `_r` 保持不变（注意：即使 zero=true 且 _r bit0=1，无使能也不冲刷，见 Q1）。
    _next 以读视图（masked view）为基底，按操作列表程序序折叠（D1）。 -/
def sbUtilStep {n : Nat} (zero : Bool) (r : BitVec n) (ops : List SbOp) : BitVec n :=
  if ops.any SbOp.en then ops.foldl sbApplyOp (sbView zero r) else r

/-- 常用情形"先 set 后 clear"的组合形式（:109-120 中每个 util 每拍恰好两次调用） -/
def sbSetClear {n : Nat} (zero : Bool) (r : BitVec n) (se : Bool) (sa : BitVec 8)
    (ce : Bool) (ca : BitVec 8) : BitVec n :=
  if se || ce then ((sbView zero r) ||| sbMask se sa) &&& ~~~sbMask ce ca else r

/-- 折叠形式与组合形式等价（把后续证明锚定到 sbSetClear 上） -/
theorem sbUtilStep_set_clear {n : Nat} (z : Bool) (r : BitVec n) (se ce : Bool)
    (sa ca : BitVec 8) :
    sbUtilStep z r [.set se sa, .clear ce ca] = sbSetClear z r se sa ce ca := by
  simp [sbUtilStep, sbSetClear, sbApplyOp, SbOp.en, List.foldl]

/- ========================================================================= -/
/- 3. Scoreboard 模型（scoreboard.scala:100-143）                             -/
/- ========================================================================= -/

/-- CtrlSigs 中被记分板使用的字段（:19-65 的子集；D7：if_ctrl 与
    ibuffer_if_ctrl 共用本类型） -/
structure SbCtrl where
  sel_alu1  : BitVec 2
  sel_alu2  : BitVec 2
  sel_alu3  : BitVec 2
  reg_idx1  : BitVec 8
  reg_idx2  : BitVec 8
  reg_idx3  : BitVec 8
  reg_idxw  : BitVec 8
  wvd       : Bool
  wxd       : Bool
  branch    : BitVec 2
  barrier   : Bool
  fence     : Bool
  mem       : Bool
  mask      : Bool
  isvec     : Bool
  readmask  : Bool

/-- scoreboardIO 的输入（:66-81，去掉只参与 delay 的 ibuffer_if_ctrl，见 D7） -/
structure SbInputs where
  if_fire    : Bool
  if_ctrl    : SbCtrl
  wb_v_fire  : Bool
  wb_v_wvd   : Bool
  wb_v_idxw  : BitVec 8
  wb_x_fire  : Bool
  wb_x_wxd   : Bool
  wb_x_idxw  : BitVec 8
  br_ctrl    : Bool
  fence_end  : Bool
  opColV_in  : Bool
  opColV_out : Bool
  opColX_in  : Bool
  opColX_out : Bool

/-- 六个 util 的 _r 状态（:102-107） -/
structure SbState where
  vectorReg : BitVec 256  -- :102
  scalarReg : BitVec 256  -- :103，zero=true
  beqReg    : BitVec 1    -- :104
  opColV    : BitVec 1    -- :105
  opColX    : BitVec 1    -- :106
  fenceReg  : BitVec 1    -- :107

/-- RegInit(0.U)（:88） -/
def sbInit : SbState := ⟨0#256, 0#256, 0#1, 0#1, 0#1, 0#1⟩

/-- 单拍状态转移（:109-120），严格按源码程序序：每个 util 内先 set 后 clear -/
def sbStep (s : SbState) (i : SbInputs) : SbState where
  vectorReg := sbUtilStep false s.vectorReg  -- :109-110
    [.set (i.if_fire && i.if_ctrl.wvd) i.if_ctrl.reg_idxw,
     .clear (i.wb_v_fire && i.wb_v_wvd) i.wb_v_idxw]
  scalarReg := sbUtilStep true s.scalarReg  -- :111-112
    [.set (i.if_fire && i.if_ctrl.wxd) i.if_ctrl.reg_idxw,
     .clear (i.wb_x_fire && i.wb_x_wxd) i.wb_x_idxw]
  beqReg := sbUtilStep false s.beqReg  -- :113-114
    [.set (i.if_fire && (i.if_ctrl.branch != 0#2 || i.if_ctrl.barrier)) 0#8,
     .clear i.br_ctrl 0#8]
  opColV := sbUtilStep false s.opColV  -- :115-116
    [.set i.opColV_in 0#8, .clear i.opColV_out 0#8]
  opColX := sbUtilStep false s.opColX  -- :117-118
    [.set i.opColX_in 0#8, .clear i.opColX_out 0#8]
  fenceReg := sbUtilStep false s.fenceReg  -- :119-120
    [.set (i.if_fire && i.if_ctrl.fence) 0#8, .clear i.fence_end 0#8]

-- 投影引理（rfl）：供 simp 展开结构投影
theorem sbStep_vectorReg (s : SbState) (i : SbInputs) :
    (sbStep s i).vectorReg = sbUtilStep false s.vectorReg
      [.set (i.if_fire && i.if_ctrl.wvd) i.if_ctrl.reg_idxw,
       .clear (i.wb_v_fire && i.wb_v_wvd) i.wb_v_idxw] := rfl

theorem sbStep_scalarReg (s : SbState) (i : SbInputs) :
    (sbStep s i).scalarReg = sbUtilStep true s.scalarReg
      [.set (i.if_fire && i.if_ctrl.wxd) i.if_ctrl.reg_idxw,
       .clear (i.wb_x_fire && i.wb_x_wxd) i.wb_x_idxw] := rfl

theorem sbStep_beqReg (s : SbState) (i : SbInputs) :
    (sbStep s i).beqReg = sbUtilStep false s.beqReg
      [.set (i.if_fire && (i.if_ctrl.branch != 0#2 || i.if_ctrl.barrier)) 0#8,
       .clear i.br_ctrl 0#8] := rfl

theorem sbStep_opColV (s : SbState) (i : SbInputs) :
    (sbStep s i).opColV = sbUtilStep false s.opColV
      [.set i.opColV_in 0#8, .clear i.opColV_out 0#8] := rfl

theorem sbStep_opColX (s : SbState) (i : SbInputs) :
    (sbStep s i).opColX = sbUtilStep false s.opColX
      [.set i.opColX_in 0#8, .clear i.opColX_out 0#8] := rfl

theorem sbStep_fenceReg (s : SbState) (i : SbInputs) :
    (sbStep s i).fenceReg = sbUtilStep false s.fenceReg
      [.set (i.if_fire && i.if_ctrl.fence) 0#8, .clear i.fence_end 0#8] := rfl

/- 九个阻塞源（:121-141），全部读 ibuffer_if_ctrl（记为 c） -/

/-- read1（:121）：sel_alu1 选择读 scalarReg/vectorReg 的 reg_idx1 -/
def sbRead1 (s : SbState) (c : SbCtrl) : Bool :=
  if c.sel_alu1 == sbA1_RS1 then sbRead true s.scalarReg c.reg_idx1
  else if c.sel_alu1 == sbA1_VRS1 then sbRead false s.vectorReg c.reg_idx1
  else false

/-- read2（:122） -/
def sbRead2 (s : SbState) (c : SbCtrl) : Bool :=
  if c.sel_alu2 == sbA2_RS2 then sbRead true s.scalarReg c.reg_idx2
  else if c.sel_alu2 == sbA2_VRS2 then sbRead false s.vectorReg c.reg_idx2
  else false

/-- read3（:123-127）：A3_SD 与 A3_PC 有特殊分支 -/
def sbRead3 (s : SbState) (c : SbCtrl) : Bool :=
  if c.sel_alu3 == sbA3_VRS3 then sbRead false s.vectorReg c.reg_idx3
  else if c.sel_alu3 == sbA3_SD then  -- :124
    (if c.isvec && !c.readmask then sbRead false s.vectorReg c.reg_idx3
     else if c.isvec then sbRead false s.vectorReg c.reg_idx2
     else sbRead true s.scalarReg c.reg_idx2)
  else if c.sel_alu3 == sbA3_FRS3 then sbRead true s.scalarReg c.reg_idx3  -- :125
  else  -- A3_PC = 0，四键覆盖 2 位全域（:126）
    (if c.branch == sbB_R then sbRead true s.scalarReg c.reg_idx1 else false)

/-- readm（:128）：mask 指令读 vectorReg(0)。注意 vectorReg 的 zero=false，
    故 v0 占用会阻塞（与 scalarReg 的 x0 永不阻塞形成对照） -/
def sbReadM (s : SbState) (c : SbCtrl) : Bool :=
  if c.mask then sbRead false s.vectorReg 0#8 else false

/-- readw（:129）：WAW——读本指令写址 -/
def sbReadW (s : SbState) (c : SbCtrl) : Bool :=
  (if c.wxd then sbRead true s.scalarReg c.reg_idxw else false) ||
  (if c.wvd then sbRead false s.vectorReg c.reg_idxw else false)

/-- readb（:130） -/
def sbReadB (s : SbState) : Bool := sbRead false s.beqReg 0#8

/-- read_op_colV / read_op_colX（:131-132） -/
def sbReadOpColV (s : SbState) : Bool := sbRead false s.opColV 0#8
def sbReadOpColX (s : SbState) : Bool := sbRead false s.opColX 0#8

/-- readf（:133）：mem 指令且 fence 未结束 -/
def sbReadF (s : SbState) (c : SbCtrl) : Bool :=
  c.mem && sbRead false s.fenceReg 0#8

/-- delay（:142）：九源之或 -/
def sbDelay (s : SbState) (c : SbCtrl) : Bool :=
  sbRead1 s c || sbRead2 s c || sbRead3 s c || sbReadM s c || sbReadW s c ||
  sbReadB s || sbReadF s c || sbReadOpColV s || sbReadOpColX s

/-- 多拍运行 -/
def sbRun (s : SbState) (ins : List SbInputs) : SbState := ins.foldl sbStep s

/- ========================================================================= -/
/- 4. 数值回归测试（先测试；全部 `by decide`）                                -/
/- ========================================================================= -/

section SbRegressionTests

/-- 全零控制字（不读寄存器、不触发任何阻塞源） -/
def sbCtrl0 : SbCtrl :=
  { sel_alu1 := 0#2, sel_alu2 := 0#2, sel_alu3 := 0#2,
    reg_idx1 := 0#8, reg_idx2 := 0#8, reg_idx3 := 0#8, reg_idxw := 0#8,
    wvd := false, wxd := false, branch := 0#2, barrier := false,
    fence := false, mem := false, mask := false, isvec := false, readmask := false }

/-- 空输入（一拍内无任何事件） -/
def sbInNop : SbInputs :=
  { if_fire := false, if_ctrl := sbCtrl0,
    wb_v_fire := false, wb_v_wvd := false, wb_v_idxw := 0#8,
    wb_x_fire := false, wb_x_wxd := false, wb_x_idxw := 0#8,
    br_ctrl := false, fence_end := false,
    opColV_in := false, opColV_out := false,
    opColX_in := false, opColX_out := false }

-- 场景输入
def sbInIssueV5 : SbInputs :=  -- 发射写 v5 的向量指令
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wvd := true, reg_idxw := 5#8 } }
def sbInIssueV4 : SbInputs :=
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wvd := true, reg_idxw := 4#8 } }
def sbInIssueV0 : SbInputs :=
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wvd := true, reg_idxw := 0#8 } }
def sbInIssueX0 : SbInputs :=  -- 发射写 x0 的标量指令
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wxd := true, reg_idxw := 0#8 } }
def sbInIssueX4 : SbInputs :=
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wxd := true, reg_idxw := 4#8 } }
def sbInWbV5 : SbInputs :=  -- 向量写回 v5
  { sbInNop with wb_v_fire := true, wb_v_wvd := true, wb_v_idxw := 5#8 }
def sbInWbV6 : SbInputs :=
  { sbInNop with wb_v_fire := true, wb_v_wvd := true, wb_v_idxw := 6#8 }
def sbInIssueAndWbV5 : SbInputs :=  -- 同拍发射写 v5 + 写回清 v5
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wvd := true, reg_idxw := 5#8 }, wb_v_fire := true, wb_v_wvd := true, wb_v_idxw := 5#8 }
def sbInBr : SbInputs :=  -- 发射分支指令
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with branch := 1#2 } }
def sbInBarrier : SbInputs :=  -- 发射 barrier 指令
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with barrier := true } }
def sbInBrCtrl : SbInputs := { sbInNop with br_ctrl := true }
def sbInIssueFence : SbInputs :=
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with fence := true } }
def sbInFenceEnd : SbInputs := { sbInNop with fence_end := true }
def sbInOpColVIn : SbInputs := { sbInNop with opColV_in := true }
def sbInOpColVOut : SbInputs := { sbInNop with opColV_out := true }

-- 场景读控制字
def sbCtrlReadV5 : SbCtrl := { sbCtrl0 with sel_alu1 := sbA1_VRS1, reg_idx1 := 5#8 }
def sbCtrlReadX0 : SbCtrl := { sbCtrl0 with sel_alu1 := sbA1_RS1, reg_idx1 := 0#8 }
def sbCtrlWriteX0 : SbCtrl := { sbCtrl0 with wxd := true, reg_idxw := 0#8 }
def sbCtrlWriteV5 : SbCtrl := { sbCtrl0 with wvd := true, reg_idxw := 5#8 }
def sbCtrlMem : SbCtrl := { sbCtrl0 with mem := true }
def sbCtrlMask : SbCtrl := { sbCtrl0 with mask := true }
def sbCtrlSDscalar : SbCtrl :=  -- A3_SD 标量路径：读 scalarReg(reg_idx2)
  { sbCtrl0 with sel_alu3 := sbA3_SD, isvec := false, reg_idx2 := 4#8 }
def sbCtrlSDvecMask : SbCtrl :=  -- A3_SD 向量+readmask 路径：读 vectorReg(reg_idx2)
  { sbCtrl0 with sel_alu3 := sbA3_SD, isvec := true, readmask := true, reg_idx2 := 4#8 }
def sbCtrlSDvecNoMask : SbCtrl :=  -- A3_SD 向量无 mask 路径：读 vectorReg(reg_idx3)
  { sbCtrl0 with sel_alu3 := sbA3_SD, isvec := true, readmask := false, reg_idx3 := 4#8 }
def sbCtrlPCBranch : SbCtrl :=  -- A3_PC 且 branch=B_R：读 scalarReg(reg_idx1)
  { sbCtrl0 with sel_alu3 := sbA3_PC, branch := sbB_R, reg_idx1 := 4#8 }
def sbCtrlPCNoBranch : SbCtrl :=
  { sbCtrl0 with sel_alu3 := sbA3_PC, branch := 0#2, reg_idx1 := 4#8 }

-- 场景状态
def sbSV5 : SbState := sbStep sbInit sbInIssueV5      -- v5 被占用
def sbSX4 : SbState := sbStep sbInit sbInIssueX4      -- x4 被占用
def sbSX4V4 : SbState := sbStep sbSX4 sbInIssueV4     -- x4、v4 均被占用
def sbSV0 : SbState := sbStep sbInit sbInIssueV0      -- v0 被占用

-- T1 RAW：发射写 v5 → 下拍读 v5 的指令被阻塞；发射当拍读不到（读非旁路，D3）
example : sbDelay sbInit sbCtrlReadV5 = false := by decide
example : sbSV5.vectorReg = 32#256 := by decide
example : sbDelay sbSV5 sbCtrlReadV5 = true := by decide

-- T2 写回清除：wb_v_fire 后下拍不再阻塞；异址清除不解阻塞
example : sbDelay (sbStep sbSV5 sbInWbV5) sbCtrlReadV5 = false := by decide
example : sbDelay (sbStep sbSV5 sbInWbV6) sbCtrlReadV5 = true := by decide

-- T3 x0 永不阻塞：刻意 set bit0，_r 内部 bit0=1（Q1），但读视图屏蔽
example : (sbStep sbInit sbInIssueX0).scalarReg = 1#256 := by decide
example : sbDelay (sbStep sbInit sbInIssueX0) sbCtrlReadX0 = false := by decide
example : sbDelay (sbStep sbInit sbInIssueX0) sbCtrlWriteX0 = false := by decide  -- WAW x0 亦不阻塞

-- T4 WAW：写址被占用时本指令阻塞
example : sbDelay sbSV5 sbCtrlWriteV5 = true := by decide

-- T5 分支/barrier 阻塞与 br_ctrl 解除
example : sbDelay (sbStep sbInit sbInBr) sbCtrl0 = true := by decide
example : sbDelay (sbStep sbInit sbInBarrier) sbCtrl0 = true := by decide
example : sbDelay (sbStep (sbStep sbInit sbInBr) sbInBrCtrl) sbCtrl0 = false := by decide

-- T6 同拍同址 set+clear → clear 胜（后写胜，:109-110 程序序）
example : sbDelay (sbStep sbSV5 sbInIssueAndWbV5) sbCtrlReadV5 = false := by decide

-- T7 OpCol 阻塞与解除
example : sbDelay (sbStep sbInit sbInOpColVIn) sbCtrl0 = true := by decide
example : sbDelay (sbStep (sbStep sbInit sbInOpColVIn) sbInOpColVOut) sbCtrl0 = false := by decide

-- T8 fence 阻塞（仅 mem 指令）与 fence_end 解除
example : sbDelay (sbStep sbInit sbInIssueFence) sbCtrlMem = true := by decide
example : sbDelay (sbStep sbInit sbInIssueFence) sbCtrl0 = false := by decide
example : sbDelay (sbStep (sbStep sbInit sbInIssueFence) sbInFenceEnd) sbCtrlMem = false := by decide

-- T9 A3_SD 三分支（:124）
example : sbDelay sbSX4 sbCtrlSDscalar = true := by decide
example : sbDelay sbSX4 sbCtrlSDvecMask = false := by decide
example : sbDelay sbSX4 sbCtrlSDvecNoMask = false := by decide
example : sbDelay sbSX4V4 sbCtrlSDvecMask = true := by decide
example : sbDelay sbSX4V4 sbCtrlSDvecNoMask = true := by decide

-- T10 A3_PC 分支（:126）
example : sbDelay sbSX4 sbCtrlPCBranch = true := by decide
example : sbDelay sbSX4 sbCtrlPCNoBranch = false := by decide

-- T11 readm：mask 指令读 vectorReg(0)，v0 占用即阻塞
example : sbDelay sbSV0 sbCtrlMask = true := by decide

-- T12 链式折叠语义（三操作按序作用，clear 最后生效）
example : sbUtilStep false 0#256 [.set true 3#8, .set true 4#8, .clear true 3#8] = 16#256 := by decide

end SbRegressionTests

/- ========================================================================= -/
/- 5. 阻塞契约（后证明）                                                      -/
/- ========================================================================= -/

/-- 位级核心引理：clear 后写胜。无论此前 set 了什么（任意使能/地址），
    同拍 clear 使能的地址在结果中读为 0；对 zero 标志任意成立。 -/
theorem sb_clear_wins {z : Bool} {r : BitVec 256} {se : Bool} {sa a : BitVec 8} :
    sbRead z (sbSetClear z r se sa true a) a = false := by
  unfold sbRead sbView sbSetClear sbMask
  bv_decide

/-- 位级核心引理：set 可见。set 使能的地址，只要同拍没有针对该地址的
    clear，结果中读为 1（vectorReg 等 zero=false 的 util）。 -/
theorem sb_set_visible {r : BitVec 256} {ce : Bool} {a ca : BitVec 8}
    (h : (ce && (ca == a)) = false) :
    sbRead false (sbSetClear false r true a ce ca) a = true := by
  unfold sbRead sbView sbSetClear sbMask
  bv_decide

/-- 位级核心引理（标量版）：zero=true 的读视图屏蔽 bit0，
    故需附加前提 a ≠ 0（x0 属于 SB1 的管辖，永不阻塞）。 -/
theorem sb_set_visible_scalar {r : BitVec 256} {ce : Bool} {a ca : BitVec 8}
    (h0 : (a == 0#8) = false) (h : (ce && (ca == a)) = false) :
    sbRead true (sbSetClear true r true a ce ca) a = true := by
  unfold sbRead sbView sbSetClear sbMask
  bv_decide

/-- SB1 x0 不变式：任意状态下 scalarReg 读地址 0 恒 false。
    注意无需对 run 归纳：读视图 `(_r >> 1) << 1`（:89）无条件屏蔽 bit0，
    与 _r 内部 bit0 是否被置位（Q1）无关——这是对任意状态成立的更强事实。 -/
theorem sb1_scalar_x0 (r : BitVec 256) : sbRead true r 0#8 = false := by
  unfold sbRead sbView
  bv_decide

/-- SB1（run 形式）：任意初始状态、任意输入序列后，scalarReg 读地址 0 恒 false -/
theorem sb1_run_scalar_x0 (s : SbState) (ins : List SbInputs) :
    sbRead true (sbRun s ins).scalarReg 0#8 = false :=
  sb1_scalar_x0 _

/-- SB2 RAW 契约：本拍 if_fire&wvd 置位 vectorReg 的地址 a，且无同拍针对 a 的
    写回清除，则下拍经 read1（sel_alu1=A1_VRS1, reg_idx1=a）读 a 的指令 delay=1。 -/
theorem sb2_raw (s : SbState) (i : SbInputs) (c : SbCtrl) (a : BitVec 8)
    (hif : i.if_fire = true) (hwvd : i.if_ctrl.wvd = true)
    (haddr : i.if_ctrl.reg_idxw = a)
    (hnc : (i.wb_v_fire && i.wb_v_wvd && (i.wb_v_idxw == a)) = false)
    (hsel : c.sel_alu1 = sbA1_VRS1) (hr1 : c.reg_idx1 = a) :
    sbDelay (sbStep s i) c = true := by
  have h1 : sbRead1 (sbStep s i) c = true := by
    simp only [sbRead1, sbStep_vectorReg, sbUtilStep_set_clear, hif, hwvd, haddr,
      hsel, hr1, sbA1_VRS1, sbA1_RS1, sbSetClear, sbView, sbMask, sbRead]
    bv_decide
  simp [sbDelay, h1]

/-- SB2（标量版）：wxd 置位 scalarReg 的地址 a（a ≠ 0），无同拍清除，
    下拍经 read1（A1_RS1）读 a 的指令 delay=1。a ≠ 0 是因为 x0 永不阻塞（SB1）。 -/
theorem sb2_raw_scalar (s : SbState) (i : SbInputs) (c : SbCtrl) (a : BitVec 8)
    (hif : i.if_fire = true) (hwxd : i.if_ctrl.wxd = true)
    (haddr : i.if_ctrl.reg_idxw = a) (ha0 : (a == 0#8) = false)
    (hnc : (i.wb_x_fire && i.wb_x_wxd && (i.wb_x_idxw == a)) = false)
    (hsel : c.sel_alu1 = sbA1_RS1) (hr1 : c.reg_idx1 = a) :
    sbDelay (sbStep s i) c = true := by
  have h1 : sbRead1 (sbStep s i) c = true := by
    simp only [sbRead1, sbStep_scalarReg, sbUtilStep_set_clear, hif, hwxd, haddr,
      hsel, hr1, sbA1_RS1, sbA1_VRS1, sbSetClear, sbView, sbMask, sbRead]
    bv_decide
  simp [sbDelay, h1]

/-- SB3 写回清除契约：wb_v 清除地址 a 后，下拍 vectorReg 在 a 处读为 0
    （该 util 不再因 a 阻塞）。注：实际无需"无同拍 set"前提——set 先于 clear
    （:109-110），clear 后写胜（sb_clear_wins），前提 hns 仅对应任务书表述。 -/
theorem sb3_wb_clear (s : SbState) (i : SbInputs) (a : BitVec 8)
    (hbf : i.wb_v_fire = true) (hbw : i.wb_v_wvd = true) (hba : i.wb_v_idxw = a)
    (hns : (i.if_fire && i.if_ctrl.wvd && (i.if_ctrl.reg_idxw == a)) = false) :
    sbRead false (sbStep s i).vectorReg a = false := by
  simp only [sbStep_vectorReg, sbUtilStep_set_clear, hbf, hbw, hba, Bool.and_true]
  exact sb_clear_wins

/-- SB4 同拍优先级：同拍同址 set 与 clear，结果位 = 0（clear 后写胜） -/
theorem sb4_clear_priority (s : SbState) (i : SbInputs) (a : BitVec 8)
    (hif : i.if_fire = true) (hwvd : i.if_ctrl.wvd = true)
    (haddr : i.if_ctrl.reg_idxw = a)
    (hbf : i.wb_v_fire = true) (hbw : i.wb_v_wvd = true) (hba : i.wb_v_idxw = a) :
    sbRead false (sbStep s i).vectorReg a = false := by
  simp only [sbStep_vectorReg, sbUtilStep_set_clear, hif, hwvd, haddr, hbf, hbw, hba,
    Bool.and_true]
  exact sb_clear_wins

/-- SB5 delay 完备性：delay=0 当且仅当九个阻塞源全不命中（:142 展开） -/
theorem sb5_delay_complete (s : SbState) (c : SbCtrl) :
    sbDelay s c = false ↔
      sbRead1 s c = false ∧ sbRead2 s c = false ∧ sbRead3 s c = false ∧
      sbReadM s c = false ∧ sbReadW s c = false ∧ sbReadB s = false ∧
      sbReadF s c = false ∧ sbReadOpColV s = false ∧ sbReadOpColX s = false := by
  simp [sbDelay, and_assoc]

/- 公理审计（bv_decide 会引入每个定理私有的 LRAT 检查 trust 公理，
   形如 `…._native.bv_decide.ax_…`，归档时注明） -/
#print axioms sb1_run_scalar_x0
#print axioms sb2_raw
#print axioms sb2_raw_scalar
#print axioms sb3_wb_clear
#print axioms sb4_clear_priority
#print axioms sb5_delay_complete

end Ventus.Schedule
