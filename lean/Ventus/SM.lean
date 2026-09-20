/- ========================================================================= -/
/-                          SM.lean                                          -/
/-  SM 级组合骨架：把已验证的子模块模型按 pipe.scala 连线组合成单 SM 的        -/
/-  单拍 step 函数，为端到端轨迹验证提供底座。                                 -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/pipe.scala          -/
/-    （class pipe，430 行纯连线）+ warp_schedule.scala / ibuffer.scala /      -/
/-    scoreboard.scala / operandCollector.scala / issue.scala /               -/
/-    execution.scala(ALUexe) / writeback.scala(Branch_back) / regfile.scala   -/
/-  参数：num_warp=8、num_thread=32、num_fetch=2、num_bank=4、                -/
/-    num_collectorUnit=8、xLen=32、SINGLE_INST=false、MMU/GVM off。          -/
/-                                                                           -/
/- ======================== 理想化与对 Chisel 的偏离（D 区） ================= -/
/-  D1. 完美取指存根：ICache 不建模，取指 = 程序内存（BitVec 32 → BitVec 32， -/
/-      按字地址）当拍组合读出 + 当拍译码（Arith/DecodeUnit.lean 的 decDecode， -/
/-      对应 pipe.scala:176-185 的 control 模块）。与真实 ICache 的差异：      -/
/-      无 miss/重放（pc_rsp.status 恒命中，wsIn.pcRspValid 恒 false），       -/
/-      零延迟（真实 ≥1 拍）。Q2（Pipe.lean）的 status 强制路径因此不激发。   -/
/-      程序区外的内存字 = 0，译码为 aluFn=63 的 NOP（wxd=false，不写回、      -/
/-      不占记分板），对本骨架无害；W7 的 undefined-instruction 断言不建模。  -/
/-  D2. 指令身份标签：IbInsn.tag := pc[9:2]，下流各阶段（记分板 if_ctrl、CU   -/
/-      重建、DualIssue inst_is_vec、issue 路由）用 tag→pc→imem 重取译码重建   -/
/-      完整控制字（smCtrlOfTag）。等价前提：程序内存只读、pc 4B 对齐且程序    -/
/-      < 1KiB。真实硬件把 CtrlSigs 随流水线携带，此处为等价重建。            -/
/-  D3. exe_dataX/exe_dataV 是纯连线（pipe.scala:115-129 `io.deq <> io.enq`），-/
/-      ALUexe 的 result/result_br 为 Queue(1, pipe=true)（execution.scala:37-38），-/
/-      下游（wb 仲裁 out.ready 与 branch_back 的 0 深 Queue）恒就绪，故流穿、  -/
/-      零有效延迟——本模型把"CU issue → issueX → sALU → wb 仲裁"建成同拍组合。-/
/-  D4. LSU/DCache/ShareMem/FPU/SFU/TC/MUL/vALU/SIMT 执行单元全部不就绪 stub： -/
/-      issueX 死通道 ready=false（忠实于 pipe.scala:375-401）；issueV 全部    -/
/-      端口 ready=false（超范围理想化）——向量/访存指令会在 DualIssue 处永久   -/
/-      阻塞而非错误执行。测试程序只含标量 ALU + beq + endprg。CSR 端口        -/
/-      ready=true 但写回数据 stub 为 0（见集成障碍清单 I-SM-1）。             -/
/-  D5. CSR 只读视图：SmCsrView = csrfile 被组合消费的只读端口（sgpr_base/     -/
/-      vgpr_base，pipe.scala:164-165；simt_rpc，:389）的抽象；CTA 派发拍写入  -/
/-      （CTA2csr 通路，pipe.scala:163，warp_schedule.scala:58-59 的纯转发）。-/
/-      CSRexe 内部状态机不接入（见 I-SM-1）。                                 -/
/-  D6. branch_join 以单实例 BjSysState 4 32 纳入状态，每拍喂 BjEvent.nop      -/
/-      （vbranch/join 属 issueV 范围，本骨架不出现）；其 complete/fetchValid  -/
/-      汇入记分板 br_ctrl 的连线（pipe.scala:252-254）以常量 false 占位。     -/
/-  D7. warp_sche.io.wg_id_tag 是顶层输入（pipe.scala:152），SM 级作为环境     -/
/-      输入携带（测试单 warp (wg0,wf0)，恒 0）。flushDCache.ready 同为环境    -/
/-      输入（测试恒 true，等价 lsu 恒吸收 flush）。warpRsp.ready 同。         -/
/-  D8. bank 读仲裁/写回寻址复用 OperandCollector.lean 的 ocSca*/ocVec*/        -/
/-      ocWbSca* 既有模型；SyncReadMem 的 1 拍读延迟与 bypass 用 RegFile.lean  -/
/-      的 RfSState/RfVState 忠实建模（仲裁拍 T 读地址、T+1 经 crossbar 返回   -/
/-      CU）。crossbar 复用 ocXbar，chosen/valid 的 RegNext 存于 SmState。     -/
/- ========================================================================= -/

import Ventus.Pipe
import Ventus.Schedule.IBuffer
import Ventus.Schedule.Issue
import Ventus.Schedule.CollectorUnit
import Ventus.Schedule.OperandCollector
import Ventus.Schedule.Writeback
import Ventus.Arith.ScalarALU
import Ventus.Arith.DecodeUnit
import Ventus.SIMT.PCcontrol

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. SmCtrl：译码后控制字的统一载体 + 各子模块切片投影                        -/
/- ========================================================================= -/

/-- 指令身份标签 = pc[9:2]（D2） -/
def smTagOfPc (pc : BitVec 32) : BitVec 8 := pc.extractLsb' 2 8

/-- 标签反查 pc（D2；程序 < 1KiB 时与 smTagOfPc 互逆） -/
def smPcOfTag (t : BitVec 8) : BitVec 32 := (t.zeroExtend 32) <<< 2

/-- 统一控制字：译码行（DecodeUnit）+ 寄存器号提取（GVM off → regPrefix=0，
    DecodeUnit.scala:606-609）+ 身份（tag/pc/wid/inst） -/
structure SmCtrl where
  tag     : BitVec 8
  wid     : BitVec 3
  pc      : BitVec 32
  inst    : BitVec 32
  row     : DecCtrlRow
  regIdx1 : BitVec 8
  regIdx2 : BitVec 8
  regIdx3 : BitVec 8
  regIdxw : BitVec 8

/-- CtrlSigs.mask（DecodeUnit.scala:583）：标量指令恒 false -/
def smMaskOf (inst : BitVec 32) (row : DecCtrlRow) : Bool :=
  decMaskEn inst row.aluFn row.isvec row.disableMask

/-- 取指侧译码（control 模块，pipe.scala:176-185 + DecodeUnit.scala 全体） -/
def smDecode (inst : BitVec 32) (wid : BitVec 3) (pc : BitVec 32) : SmCtrl :=
  let row := decDecode inst
  { tag := smTagOfPc pc, wid := wid, pc := pc, inst := inst, row := row
  , regIdx1 := decRegIdx1 0#3 inst, regIdx2 := decRegIdx2 0#3 inst
  , regIdx3 := decRegIdx3 row.fp row.isvec 0#3 inst, regIdxw := decRegIdxw 0#3 inst }

/-- ibuffer/ibuffer2issue 切片（IbInsn，ibuffer.scala:70-78 的 inst_is_vec 输入） -/
def smToIbInsn (c : SmCtrl) : IbInsn :=
  { tag := c.tag, wid := c.wid, tc := c.row.tc, fp := c.row.fp, mul := c.row.mul
  , sfu := c.row.sfu, mem := c.row.memCmd != 0#2, csr := c.row.csr
  , barrier := c.row.barrier, isvec := c.row.isvec }

/-- scoreboard 切片（SbCtrl，scoreboard.scala:19-65 的子集） -/
def smToSbCtrl (c : SmCtrl) : SbCtrl :=
  { sel_alu1 := c.row.selAlu1, sel_alu2 := c.row.selAlu2, sel_alu3 := c.row.selAlu3
  , reg_idx1 := c.regIdx1, reg_idx2 := c.regIdx2, reg_idx3 := c.regIdx3
  , reg_idxw := c.regIdxw
  , wvd := c.row.wvd, wxd := c.row.wxd, branch := c.row.branch
  , barrier := c.row.barrier, fence := c.row.fence, mem := c.row.memCmd != 0#2
  , mask := smMaskOf c.inst c.row, isvec := c.row.isvec, readmask := c.row.readmask }

/-- operand collector 切片（CuCtrl，collectorUnit 的 control） -/
def smToCuCtrl (c : SmCtrl) : CuCtrl :=
  { tag := c.tag, wid := c.wid, inst := c.inst, imm_ext := 0#7, sel_imm := c.row.selImm
  , sel_alu1 := c.row.selAlu1, sel_alu2 := c.row.selAlu2, sel_alu3 := c.row.selAlu3
  , branch := c.row.branch, isvec := c.row.isvec, mask := smMaskOf c.inst c.row
  , readmask := c.row.readmask, reg_idx1 := c.regIdx1, reg_idx2 := c.regIdx2
  , reg_idx3 := c.regIdx3, pc := c.pc, custom_signal_0 := c.row.custom0 }

/-- issue 路由切片（IssCtrl，issue.scala:98-139 的 if-elsewhen 输入） -/
def smToIssCtrl (c : SmCtrl) : IssCtrl :=
  { tc := c.row.tc, sfu := c.row.sfu, fp := c.row.fp, csrOrR := c.row.csr != 0#2
  , mul := c.row.mul, mem := c.row.memCmd != 0#2, isvec := c.row.isvec
  , barrier := c.row.barrier, simt_stack := c.row.simtStack
  , simt_stack_op := c.row.simtStackOp }

/-- DualIssue 的 inst_is_vec（operandCollector.scala:640-650，与
    ibuffer.scala:70-78 同一优先级链） -/
def smInstIsVec (c : SmCtrl) : Bool := ibInstIsVec (smToIbInsn c)

/- ========================================================================= -/
/- 2. 程序与取指存根（D1/D2）                                                  -/
/- ========================================================================= -/

/-- 程序内存：字地址 → 机器码（完美 ICache 的内容侧） -/
structure SmProg where
  imem : BitVec 32 → BitVec 32

/-- 取指 + 译码一条 -/
def smFetchInsn (prog : SmProg) (wid : BitVec 3) (pc : BitVec 32) : SmCtrl :=
  smDecode (prog.imem pc) wid pc

/-- 标签重建完整控制字（D2） -/
def smCtrlOfTag (prog : SmProg) (tag : BitVec 8) (wid : BitVec 3) : SmCtrl :=
  smFetchInsn prog wid (smPcOfTag tag)

/- ========================================================================= -/
/- 3. 输入、CSR 只读视图、状态                                                 -/
/- ========================================================================= -/

/-- SM 环境输入：CTA 手动派发 + 顶层杂项 -/
structure SmIn where
  reqFire          : Bool      -- io.warpReq.fire（CTA 派发新 warp）
  reqWid           : BitVec 3  -- new_warpid
  reqWg            : BitVec 3  -- tag[5:3]（wg id）
  reqCnt           : BitVec 4  -- dispatch2cu_wg_wf_count
  reqPC            : BitVec 32 -- 起始 PC（warp_schedule.scala:212-214 New_PC）
  reqSgpr          : BitVec 12 -- CTA2csr 写入的 sgpr_base（D5）
  reqVgpr          : BitVec 11 -- CTA2csr 写入的 vgpr_base（D5）
  wgIdTag          : BitVec 6  -- io.wg_id_tag（D7）
  warpRspReady     : Bool      -- io.warpRsp.ready
  flushDCacheReady : Bool      -- lsu.io.flush_dcache.ready（D7 stub）
  pcReset          : Bool      -- io.pc_reset

def smInNop : SmIn :=
  { reqFire := false, reqWid := 0#3, reqWg := 0#3, reqCnt := 0#4
  , reqPC := 0#32, reqSgpr := 0#12, reqVgpr := 0#11, wgIdTag := 0#6
  , warpRspReady := true, flushDCacheReady := true, pcReset := false }

/-- CTA 派发事件 -/
def smInDispatch (wid wg : BitVec 3) (cnt : BitVec 4) (pc : BitVec 32)
    (sgpr : BitVec 12) (vgpr : BitVec 11) : SmIn :=
  { smInNop with reqFire := true, reqWid := wid, reqWg := wg, reqCnt := cnt,
                 reqPC := pc, reqSgpr := sgpr, reqVgpr := vgpr }

/-- CSR 只读视图（D5） -/
structure SmCsrView where
  sgprBase : Fin 8 → BitVec 12
  vgprBase : Fin 8 → BitVec 11
  simtRpc  : BitVec 32

/-- SM 组合状态：各子模块状态的结构。
    注意（AGENTS.md 已知踩坑"函数字段闭包跨拍扇出使模拟指数变慢"）：
    与 bank 仲裁链相连的字段（cu/srf/vrf/bankLg*/chosen*）必须用 Array 存储
    ——Array 元素在构造时各求值一次并被共享；函数字段的闭包不缓存，跨拍通过
    crossbar 的 dataS → 寄存器堆 → bank 仲裁链重入会造成指数级重算（实测）。 -/
structure SmState where
  ws       : WsState                -- warp_scheduler
  pcc      : Fin 8 → PccState       -- 每 warp 的 PCcontrol（廉价，保留函数）
  ib       : IbTop                  -- InstrBufferV2（类型固定，lane 廉价）
  sb       : Fin 8 → SbState        -- 每 warp 的 Scoreboard（廉价，保留函数）
  cu       : Array CuState          -- 8 个 collectorUnit
  lgXi2i   : Fin 8                  -- ibuffer2issue rrarbit_x lastGrant
  lgVi2i   : Fin 8                  -- ibuffer2issue rrarbit_v lastGrant
  lgXss    : Fin 8                  -- DualIssue arb_x lastGrant
  lgVss    : Fin 8                  -- DualIssue arb_v lastGrant
  bankLgS  : Array (Fin 32)         -- bankArbiterScalar(i) lastGrant
  bankLgV  : Array (Fin 32)         -- bankArbiterVector(i) lastGrant
  chosenS  : Array (BitVec 5)       -- RegNext(readchosenScalar)
  chosenV  : Array (BitVec 5)       -- RegNext(readchosenVector)
  chosenSv : Array Bool             -- RegNext(标量仲裁 out.valid)
  chosenVv : Array Bool             -- RegNext(向量仲裁 out.valid)
  srf      : Array RfSState         -- 标量寄存器堆 4 bank（含读延迟/bypass）
  vrf      : Array RfVState         -- 向量寄存器堆 4 bank（本范围无写入）
  csr      : SmCsrView              -- CSR 只读视图（D5）
  bj       : BjSysState 4 32        -- branch_join（D6：喂 nop）

def smInit : SmState :=
  { ws := wsInit, pcc := fun _ => pccInit 0#2, ib := ibTopEmpty
  , sb := fun _ => sbInit, cu := Array.replicate 8 cuInit
  , lgXi2i := ⟨0, by decide⟩, lgVi2i := ⟨0, by decide⟩
  , lgXss := ⟨0, by decide⟩, lgVss := ⟨0, by decide⟩
  , bankLgS := Array.replicate 4 ⟨0, by decide⟩
  , bankLgV := Array.replicate 4 ⟨0, by decide⟩
  , chosenS := Array.replicate 4 0#5, chosenV := Array.replicate 4 0#5
  , chosenSv := Array.replicate 4 false, chosenVv := Array.replicate 4 false
  , srf := Array.replicate 4 rfSInit, vrf := Array.replicate 4 rfVInit
  , csr := ⟨fun _ => 0#12, fun _ => 0#11, 0#32⟩
  , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }  -- tmask 修正：branch_join.scala:90 RegInit(~0)（II 类修正，V-O3）

/-- Array 全函数访问（越界给默认值；本模型内下标恒在界内） -/
def smArrAt (a : Array α) (i : Nat) (d : α) : α :=
  if h : i < a.size then a[i] else d

/-- 各 Array 字段的访问子 -/
def smCuAt (s : SmState) (j : Fin 8) : CuState := smArrAt s.cu j.val cuInit
def smSrfAt (s : SmState) (i : Fin 4) : RfSState := smArrAt s.srf i.val rfSInit
def smVrfAt (s : SmState) (i : Fin 4) : RfVState := smArrAt s.vrf i.val rfVInit
def smLgSAt (s : SmState) (i : Fin 4) : Fin 32 := smArrAt s.bankLgS i.val ⟨0, by decide⟩
def smLgVAt (s : SmState) (i : Fin 4) : Fin 32 := smArrAt s.bankLgV i.val ⟨0, by decide⟩
def smChSAt (s : SmState) (i : Fin 4) : BitVec 5 := smArrAt s.chosenS i.val 0#5
def smChVAt (s : SmState) (i : Fin 4) : BitVec 5 := smArrAt s.chosenV i.val 0#5
def smChSvAt (s : SmState) (i : Fin 4) : Bool := smArrAt s.chosenSv i.val false
def smChVvAt (s : SmState) (i : Fin 4) : Bool := smArrAt s.chosenVv i.val false

/-- Fin 8 → Bool 打包为 BitVec 8（bit i = f i；与 pipeScoreboardBusy 同式） -/
def smPack8 (f : Fin 8 → Bool) : BitVec 8 :=
  (BitVec.ofBool (f 0)).zeroExtend 8 ||| ((BitVec.ofBool (f 1)).zeroExtend 8 <<< 1) |||
  ((BitVec.ofBool (f 2)).zeroExtend 8 <<< 2) ||| ((BitVec.ofBool (f 3)).zeroExtend 8 <<< 3) |||
  ((BitVec.ofBool (f 4)).zeroExtend 8 <<< 4) ||| ((BitVec.ofBool (f 5)).zeroExtend 8 <<< 5) |||
  ((BitVec.ofBool (f 6)).zeroExtend 8 <<< 6) ||| ((BitVec.ofBool (f 7)).zeroExtend 8 <<< 7)

/- ========================================================================= -/
/- 4. 组合层：smComb 算出本拍全部连线信号（全部读旧状态）                      -/
/-    求值顺序即组合依赖序（无环）：CU 发射侧 → ALU/分支 → warp_sche → 取指 → -/
/-    ibuffer2issue/demux → CU 输入 → bank 仲裁/写回。                         -/
/- ========================================================================= -/

/-- 一拍的全部组合信号（供 smStep 消费 + 测试观测） -/
structure SmComb where
  wsIn       : WsInputs
  wsO        : WsOutputs
  fetchV     : Bool              -- io.icache_req.fire（完美取指下恒被接受）
  fetchWid   : BitVec 3
  fetchGrp   : IbGrp IbInsn      -- ibuffer.io.in.bits
  ibEnqFire  : Bool              -- W2 的入队 fire
  ibIn       : IbTopIn
  i2iXFire   : Bool              -- ibuffer2issue out_x.fire（= controlX.fire）
  i2iVFire   : Bool              -- out_v.fire（= controlV.fire）
  i2iXWid    : BitVec 3
  i2iVWid    : BitVec 3
  outXV      : Bool              -- DualIssue out_x.valid（operand_collector.out(1)）
  outXWid    : BitVec 3
  ocOutXFire : Bool              -- out(1).fire = exe_dataX enq fire
  fireSAlu   : Bool              -- issueX out_sALU.fire
  fireCsr    : Bool              -- issueX out_CSR.fire
  fireWs     : Bool              -- issueX out_warpscheduler.fire（warp_control）
  aluOut     : BitVec 32
  aluCmp     : Bool
  brFire     : Bool              -- branch_back out.fire（= alu out2br valid）
  brJump     : Bool
  brWid      : BitVec 3
  brTarget   : BitVec 32
  wbXFire    : Bool              -- wb.io.out_x.fire
  wbXWid     : BitVec 3
  wbXIdxw    : BitVec 8
  wbXWxd     : Bool
  wbXData    : BitVec 32
  pccIn      : Fin 8 → PccIn
  sbIn       : Fin 8 → SbInputs
  cuIn       : Fin 8 → CuInputs
  rfInS      : Fin 4 → RfSInputs
  rfInV      : Fin 4 → RfVInputs
  lgXi2i     : Fin 8
  lgVi2i     : Fin 8
  lgXss      : Fin 8
  lgVss      : Fin 8
  bankLgS    : Fin 4 → Fin 32
  bankLgV    : Fin 4 → Fin 32
  chosenS    : Fin 4 → BitVec 5
  chosenV    : Fin 4 → BitVec 5
  chosenSv   : Fin 4 → Bool
  chosenVv   : Fin 4 → Bool

/-- 组合求值。各段注释标注 pipe.scala 行号。 -/
def smComb (prog : SmProg) (s : SmState) (inp : SmIn) : SmComb :=
  -- ---- ibuffer 头控制字重建（D2）与记分板阻塞向量（:161，W3） ----
  let headCtrl : Fin 8 → SmCtrl := fun w =>
    smCtrlOfTag prog (s.ib.outBits w).tag (s.ib.outBits w).wid
  let sbBusy : BitVec 8 :=
    pipeScoreboardBusy (fun w => sbDelay (s.sb w) (smToSbCtrl (headCtrl w)))
  let ibufRdy : BitVec 8 := smPack8 (fun w => s.ib.ibufRdy w)
  -- ---- DualIssue（operandCollector.scala:629-668）：CU 发射侧 ----
  let cuIssCtrl : Fin 8 → SmCtrl := fun j =>
    smCtrlOfTag prog (cuIssueBits (smCuAt s j)).control.tag (cuIssueBits (smCuAt s j)).control.wid
  let reqX : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt s j) && !smInstIsVec (cuIssCtrl j))
  let reqV : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt s j) && smInstIsVec (cuIssCtrl j))
  let outXV : Bool := rraOutValid (by decide) reqX s.lgXss
  let outXJ : Fin 8 := rraChoice (by decide) reqX s.lgXss
  let outXBits : CuIssueBits := cuIssueBits (smCuAt s outXJ)
  let outXC : SmCtrl := cuIssCtrl outXJ
  let issC : IssCtrl := smToIssCtrl outXC
  -- ---- sALU（execution.scala:28-66，alu_fn(4,0)，:36）----
  -- fireSAlu：sALU 端口 ready 恒 true（D3：result/result_br 队列下游恒就绪）
  let fireSAlu : Bool := outXV && (issRoute issC == [.sALU])
  let aluRes : BitVec 32 × Bool :=
    saAlu (outXC.row.aluFn.extractLsb' 0 5)
      (outXBits.alu_src1 ⟨0, by decide⟩) (outXBits.alu_src2 ⟨0, by decide⟩)
      (outXBits.alu_src3 ⟨0, by decide⟩)
  -- out2br（execution.scala:53-58）：valid = in.valid && branch≠B_N；
  -- jump = B_B→cmp_out，B_J/B_R→true；new_pc = in3（CU 已算 imm+pc）
  let brFire : Bool := fireSAlu && (outXC.row.branch != 0#2)
  let brJump : Bool :=
    if outXC.row.branch == 1#2 then aluRes.2
    else (outXC.row.branch == 2#2 || outXC.row.branch == 3#2)
  let brWid : BitVec 3 := outXBits.control.wid
  let brTarget : BitVec 32 := outXBits.alu_src3 ⟨0, by decide⟩
  -- ---- issueX 端口 ready 表（W11 + D4；ws 端口 = warp_control.ready = :52） ----
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => true | .ws => !brFire | _ => false
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR])
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brFire
  -- ---- warp_sche 输入（:150-171,:176-220）----
  let wsIn : WsInputs :=
    { warpReqFire := inp.reqFire, reqWid := inp.reqWid, newWgId := inp.reqWg
    , newWfCount := inp.reqCnt
    , warpControlFire := fireWs, simtStackOp := outXC.row.simtStackOp
    , wcWid := outXBits.control.wid, wgIdTag := inp.wgIdTag
    , warpRspReady := inp.warpRspReady
    , scoreboardBusy := sbBusy
    , exeBusy := 0#8                       -- :219（源码恒 false）
    , pcIbufRdy := ibufRdy
    , flushDCacheReady := inp.flushDCacheReady
    , branchFire := brFire, branchJump := brJump, branchWid := brWid
    , pcRspValid := false, pcRspMiss := false, pcRspWid := 0#3   -- D1：恒命中
    , pcReset := inp.pcReset }
  let wsO : WsOutputs := wsOut s.ws wsIn
  -- ---- 完美取指（D1）：pc_req 当拍被接受，当拍译码入 ibuffer ----
  let fetchV : Bool := wsO.pcReqValid
  let fetchWid : BitVec 3 := wsO.pcReqWid
  let fetchPC : BitVec 32 := (s.pcc (wsFin fetchWid)).pout
  let fetchGrp : IbGrp IbInsn :=
    ⟨smToIbInsn (smFetchInsn prog fetchWid fetchPC),
     smToIbInsn (smFetchInsn prog fetchWid (fetchPC + 4#32)),
     (s.pcc (wsFin fetchWid)).mask⟩
  let ibEnqFire : Bool :=
    pipeIbEnqFire fetchV 0#2 (s.ib.inRdy ⟨fetchV, fetchGrp, wsO.flushValid, wsO.flushWid, 0#8⟩)
  -- ---- ibuffer2issue（ibuffer.scala:42-101 + :220-226 的 W5 门控） ----
  let warpRdyW : Fin 8 → Bool := fun w =>
    ((wsO.warpReady >>> BitVec.ofNat 8 w.val) &&& 1#8) == 1#8
  let headIsVecW : Fin 8 → Bool := fun w => ibInstIsVec (s.ib.outBits w)
  let xReq : BitVec 8 := smPack8 (fun w => s.ib.outV w && warpRdyW w && !headIsVecW w)
  let vReq : BitVec 8 := smPack8 (fun w => s.ib.outV w && warpRdyW w && headIsVecW w)
  let cuRdy : Fin 8 → Bool := fun j => cuControlRdy (smCuAt s j)
  let i2iXV : Bool := rraOutValid (by decide) xReq s.lgXi2i
  let i2iXW : Fin 8 := rraChoice (by decide) xReq s.lgXi2i
  let i2iXC : SmCtrl := headCtrl i2iXW
  let i2iVV : Bool := rraOutValid (by decide) vReq s.lgVi2i
  let i2iVW : Fin 8 := rraChoice (by decide) vReq s.lgVi2i
  let i2iVC : SmCtrl := headCtrl i2iVW
  -- instDemux（operandCollector.scala:495-512；widCmp 死输入见 ocDemux 的 D6）
  let dem : OcDemuxRes 8 := ocDemux cuRdy i2iVV i2iXV (smToCuCtrl i2iVC) (smToCuCtrl i2iXC)
  let i2iXFire : Bool := i2iXV && dem.in1Rdy     -- out_x.fire = controlX.fire
  let i2iVFire : Bool := i2iVV && dem.in0Rdy     -- out_v.fire = controlV.fire
  let i2iXWid : BitVec 3 := BitVec.ofNat 3 i2iXW.val
  let i2iVWid : BitVec 3 := BitVec.ofNat 3 i2iVW.val
  let i2iInRdyW : Fin 8 → Bool := fun w =>
    if headIsVecW w then rraInReady (by decide) vReq s.lgVi2i dem.in0Rdy w
    else rraInReady (by decide) xReq s.lgXi2i dem.in1Rdy w
  let ibIn : IbTopIn :=
    { inV := pipeIbInValid fetchV 0#2, grp := fetchGrp
    , flushV := wsO.flushValid, flushW := wsO.flushWid
    , outRdy := smPack8 (fun w => pipeIbOutReady (i2iInRdyW w) (warpRdyW w)) }
  -- ---- DualIssue out.ready（= issueX in.ready）与 CU issueReady ----
  let issueXInRdy : Bool := issInReady issC portRdyX
  let ocOutXFire : Bool := outXV && issueXInRdy
  let dualInRdyJ : Fin 8 → Bool := fun j =>
    if smInstIsVec (cuIssCtrl j) then rraInReady (by decide) reqV s.lgVss false j
    else rraInReady (by decide) reqX s.lgXss issueXInRdy j
  -- ---- 写回仲裁（writeback.scala + W12）：in_x(0)=alu、in_x(3)=csr，其余恒无效 ----
  let aluWbValid : Bool := fireSAlu && outXC.row.wxd && (outXC.row.branch != 1#2)
  let csrWbValid : Bool := fireCsr && outXC.row.wxd
  let wbXValids : BitVec 6 :=
    (BitVec.ofBool aluWbValid).zeroExtend 6 |||
    ((BitVec.ofBool csrWbValid).zeroExtend 6 <<< 3)
  let wbXChoice : Fin 6 := wbArbChoice (by decide) wbXValids
  let wbXFire : Bool := wbArbOutValid wbXValids          -- wbOutReady 恒 true
  let wbXWid : BitVec 3 := outXBits.control.wid          -- alu/csr 同属一条指令
  let wbXIdxw : BitVec 8 := outXC.regIdxw
  let wbXWxd : Bool := outXC.row.wxd
  let wbXData : BitVec 32 := if wbXChoice.val = 0 then aluRes.1 else 0#32  -- CSR 数据 stub（D4）
  let wbBank : BitVec 2 := ocWbScaBankId wbXIdxw wbXWid
  let wbAddr : BitVec 8 := ocWbScaAddr (s.csr.sgprBase (wsFin wbXWid)) wbXIdxw
  let wbWrEn : Bool := wbXFire && wbXWxd && (wbXIdxw != 0#8)   -- operandCollector.scala:618
  -- ---- crossbar 输入（operandCollector.scala:549-556 的 RegNext + bank rs） ----
  let xin : OcXbarIn :=
    { chosenS := smChSAt s, chosenV := smChVAt s
    , validS := smChSvAt s, validV := smChVvAt s
    , dataS := fun i => rfSOut (smSrfAt s i), dataV := fun i => rfVOut (smVrfAt s i)
    , dataV0 := fun _ => rfVV0 }
  -- ---- CU 输入（control ← demux；bankIn ← crossbar；issue.ready ← DualIssue） ----
  -- reify：reqs/rv/cuStep 会多次应用 cuIn，具体化避免逐槽重建（含 4 路 ocXbar）
  let cuIn : Fin 8 → CuInputs := fun j =>
    { controlValid := dem.valid j, ctrl := dem.bits j
    , bv0 := (ocXbar xin j.val 0).valid, bv1 := (ocXbar xin j.val 1).valid
    , bv2 := (ocXbar xin j.val 2).valid, bv3 := (ocXbar xin j.val 3).valid
    , bb0 := ⟨(ocXbar xin j.val 0).regOrder, (ocXbar xin j.val 0).data, (ocXbar xin j.val 0).v0⟩
    , bb1 := ⟨(ocXbar xin j.val 1).regOrder, (ocXbar xin j.val 1).data, (ocXbar xin j.val 1).v0⟩
    , bb2 := ⟨(ocXbar xin j.val 2).regOrder, (ocXbar xin j.val 2).data, (ocXbar xin j.val 2).v0⟩
    , bb3 := ⟨(ocXbar xin j.val 3).regOrder, (ocXbar xin j.val 3).data, (ocXbar xin j.val 3).v0⟩
    , issueReady := dualInRdyJ j
    , sgprBase := s.csr.sgprBase, vgprBase := s.csr.vgprBase }
  -- ---- bank 读仲裁（operandCollector.scala:329-378；槽位 p = CU j*4 + 操作数 k） ----
  let reqs : Fin 32 → CuArbReq := fun p =>
    cuOutArbBits (smCuAt s ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let rv : Fin 32 → Bool := fun p =>
    cuOutArbValidK (smCuAt s ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let bankAddrS : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocScaChoice reqs rv i (smLgSAt s i))).rsAddr
  let bankAddrV : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocVecChoice reqs rv i (smLgVAt s i))).rsAddr
  -- ---- 记分板输入（:237-272，W6）----
  let sbIn : Fin 8 → SbInputs := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    { if_fire := (i2iXFire && (i2iXWid == w3)) || (i2iVFire && (i2iVWid == w3))
    , if_ctrl := if (i2iXFire && (i2iXWid == w3)) then smToSbCtrl i2iXC else smToSbCtrl i2iVC
    , wb_v_fire := false, wb_v_wvd := false, wb_v_idxw := 0#8
    , wb_x_fire := wbXFire && (wbXWid == w3), wb_x_wxd := wbXWxd, wb_x_idxw := wbXIdxw
    , br_ctrl := (brFire && (brWid == w3)) || (fireWs && (outXBits.control.wid == w3))
    , fence_end := false
    , opColV_in := i2iVFire && (i2iVWid == w3)
    , opColV_out := false
    , opColX_in := i2iXFire && (i2iXWid == w3)
    , opColX_out := ocOutXFire && (outXBits.control.wid == w3) }
  -- ---- PCcontrol 驱动（warp_schedule.scala:96-100,:195-220；
  --      程序序即优先级：pc_reset > dispatch > branch > 调度推进） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.reqFire && (inp.reqWid == w3) then ⟨inp.reqPC, false, 1#2, 0#2⟩
    else if brFire && brJump && (brWid == w3) then ⟨brTarget, false, 1#2, 0#2⟩
    else if fetchV && (fetchWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入（D8；写口全部 bank 同址、独热 wen，:613-618） ----
  let rfInS : Fin 4 → RfSInputs := fun i =>
    ⟨bankAddrS i, wbAddr, wbXData, wbWrEn && (wbBank == BitVec.ofNat 2 i.val)⟩
  let rfInV : Fin 4 → RfVInputs := fun i =>
    ⟨bankAddrV i, 0#8, cuRow0, false, fun _ => false⟩
  -- ---- RR 仲裁器 lastGrant 更新（:81 RegEnable(chosen, out.fire)） ----
  let bankLgS' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocScaPack reqs rv i) true (smLgSAt s i)
  let bankLgV' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocVecPack reqs rv i) true (smLgVAt s i)
  { wsIn := wsIn, wsO := wsO
  , fetchV := fetchV, fetchWid := fetchWid, fetchGrp := fetchGrp, ibEnqFire := ibEnqFire
  , ibIn := ibIn
  , i2iXFire := i2iXFire, i2iVFire := i2iVFire, i2iXWid := i2iXWid, i2iVWid := i2iVWid
  , outXV := outXV, outXWid := outXBits.control.wid, ocOutXFire := ocOutXFire
  , fireSAlu := fireSAlu, fireCsr := fireCsr, fireWs := fireWs
  , aluOut := aluRes.1, aluCmp := aluRes.2
  , brFire := brFire, brJump := brJump, brWid := brWid, brTarget := brTarget
  , wbXFire := wbXFire, wbXWid := wbXWid, wbXIdxw := wbXIdxw, wbXWxd := wbXWxd
  , wbXData := wbXData
  , pccIn := pccIn, sbIn := sbIn, cuIn := cuIn, rfInS := rfInS, rfInV := rfInV
  , lgXi2i := rraStep (by decide) xReq dem.in1Rdy s.lgXi2i
  , lgVi2i := rraStep (by decide) vReq dem.in0Rdy s.lgVi2i
  , lgXss := rraStep (by decide) reqX issueXInRdy s.lgXss
  , lgVss := rraStep (by decide) reqV false s.lgVss
  , bankLgS := bankLgS', bankLgV := bankLgV'
  , chosenS := fun i => BitVec.ofNat 5 (ocScaChoice reqs rv i (smLgSAt s i)).val
  , chosenV := fun i => BitVec.ofNat 5 (ocVecChoice reqs rv i (smLgVAt s i)).val
  , chosenSv := fun i => ocScaOutValid reqs rv i (smLgSAt s i)
  , chosenVv := fun i => ocVecOutValid reqs rv i (smLgVAt s i) }

/- ========================================================================= -/
/- 5. 单拍 step 与多拍 run                                                     -/
/- ========================================================================= -/

/-- SM 单拍：全部子模块按 smComb 的组合信号同步更新。
    cu/srf/vrf/bankLg*/chosen* 走 Array（构造时逐元素求值一次并共享，
    见 SmState 注释）；pcc/sb/ib 保留函数字段（单元素更新廉价、无跨拍重入）。 -/
def smStep (prog : SmProg) (s : SmState) (inp : SmIn) : SmState :=
  let c := smComb prog s inp
  { ws := wsStep s.ws c.wsIn
  , pcc := fun w => pccStep (s.pcc w) (c.pccIn w)
  , ib := ibTopStep s.ib c.ibIn
  , sb := fun w => sbStep (s.sb w) (c.sbIn w)
  , cu := ((List.finRange 8).map fun j => cuStep (smCuAt s j) (c.cuIn j)).toArray
  , lgXi2i := c.lgXi2i, lgVi2i := c.lgVi2i, lgXss := c.lgXss, lgVss := c.lgVss
  , bankLgS := ((List.finRange 4).map c.bankLgS).toArray
  , bankLgV := ((List.finRange 4).map c.bankLgV).toArray
  , chosenS := ((List.finRange 4).map c.chosenS).toArray
  , chosenV := ((List.finRange 4).map c.chosenV).toArray
  , chosenSv := ((List.finRange 4).map c.chosenSv).toArray
  , chosenVv := ((List.finRange 4).map c.chosenVv).toArray
  , srf := ((List.finRange 4).map fun i => rfSStep (smSrfAt s i) (c.rfInS i)).toArray
  , vrf := ((List.finRange 4).map fun i => rfVStep (smVrfAt s i) (c.rfInV i)).toArray
  , csr := if inp.reqFire then
      { s.csr with
        sgprBase := fun w => if w == wsFin inp.reqWid then inp.reqSgpr else s.csr.sgprBase w
      , vgprBase := fun w => if w == wsFin inp.reqWid then inp.reqVgpr else s.csr.vgprBase w }
    else s.csr
  , bj := (bjSysStep s.bj BjEvent.nop).1 }

/-- 多拍运行 -/
def smRun (prog : SmProg) (s : SmState) (ins : List SmIn) : SmState :=
  ins.foldl (smStep prog) s

/- ========================================================================= -/
/- 6. 适配层数值回归 + 端到端单 SM 轨迹测试（native_decide；                   -/
/-    公理审计会多 Lean.ofReduceBool，归档注明）                               -/
/- ========================================================================= -/

section SmEndToEndTests

/-- 测试程序（真实 RV32 机器码；语义经 DecodeUnit 模型译码）：
    0x00 addi x1, x0, 1     —— x1 := 1
    0x04 addi x2, x1, 2     —— x2 := x1 + 2 = 3（RAW 依赖 x1）
    0x08 beq  x1, x1, +8    —— 恒真分支，跳过 0x0C，落 0x10
    0x0C addi x3, x0, 9     —— 应被分支冲刷，永不写回
    0x10 add  x4, x2, x1    —— x4 := 3 + 1 = 4（RAW 依赖 x1、x2）
    0x14 endprg             —— warp0 结束 -/
def smTestProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x00100093#32
    else if pc = 0x04#32 then 0x00208113#32
    else if pc = 0x08#32 then 0x00108463#32
    else if pc = 0x0C#32 then 0x00900193#32
    else if pc = 0x10#32 then 0x00110233#32
    else if pc = 0x14#32 then 0x0000400B#32
    else 0#32

/-- 输入轨迹：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr/vgpr base=0），其后 44 拍空转 -/
def smTestIns : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 0#11 :: List.replicate 44 smInNop

/-- 拍 n 的状态（函数形式，惰性求值） -/
def smSAt (n : Nat) : SmState := smRun smTestProg smInit (smTestIns.take n)

/-- 拍 n 的组合观测（状态 = 拍前状态，输入 = 本拍输入） -/
def smCAt (n : Nat) : SmComb :=
  smComb smTestProg (smSAt n) (smTestIns.getD n smInNop)

/-- 前 n 拍内存在满足 p 的组合拍 -/
def smAnyC (n : Nat) (p : SmComb → Bool) : Bool := ((List.range n).any fun k => p (smCAt k))

/- ---- 6.1 译码/投影适配层回归 ---- -/

-- addi x1, x0, 1：FN_ADD、wxd、写 x1、A1_RS1/A2_IMM/IMM_I、路由到 sALU（非向量）
example :
    let c := smDecode 0x00100093#32 0#3 0#32
    (c.row.aluFn == 0#6) && (c.row.wxd == true) && (c.regIdxw == 1#8) &&
    (c.row.selAlu1 == 1#2) && (c.row.selAlu2 == 3#2) && (c.row.selImm == 0#4) &&
    (ibInstIsVec (smToIbInsn c) == false) && (issRoute (smToIssCtrl c) == [.sALU]) = true := by
  native_decide

-- beq：branch=B_B(1)、FN_SEQ、不写回、路由 sALU
example :
    let c := smDecode 0x00108463#32 0#3 0x08#32
    (c.row.branch == 1#2) && (c.row.aluFn == 2#6) && (c.row.wxd == false) &&
    (c.regIdx1 == 1#8) && (c.regIdx2 == 1#8) && (c.pc == 0x08#32) &&
    (issRoute (smToIssCtrl c) == [.sALU]) = true := by
  native_decide

-- endprg：barrier + simtStackOp，路由到 warp_scheduler 端口
example :
    let c := smDecode 0x0000400B#32 0#3 0x14#32
    (c.row.barrier == true) && (c.row.simtStackOp == true) &&
    (issRoute (smToIssCtrl c) == [.ws]) = true := by
  native_decide

-- tag/pc 往返（D2 的前提：程序 < 1KiB）
example : (List.range 6).all (fun k =>
    smTagOfPc (BitVec.ofNat 32 (4 * k)) == BitVec.ofNat 8 k) = true := by native_decide

/- ---- 6.2 端到端连通轨迹（前 6 拍；时间线经 /tmp 原生可执行探针验证） ---- -/
/-
  探针时间线（独立 lake exe 原生执行，非本构建内求值）：
    拍1：pc_req fire（fetchV），ibuffer 入队 fire（enq）——warp0 的 [addi, addi] 组
    拍2：ib lane0 = [tag0, tag1]，PC 推进到 8
    拍3：ibuffer2issue out_x.fire（i2iXFire，warp0），demux 分派到 CU1
    拍4：CU1 进入 s_add（收集操作数）
    拍6：DualIssue out_x fire → sALU → wb.out_x.fire，x1 := 1 写回
  已知限制（上报主会话）：原生 exe 轨迹在拍 ~9-10 处求值时间爆炸（即使冻结
  cu/srf/bank 更新也一样，冻结 ws 更新则消失）——疑似 WsState 函数位段闭包链
  与 comb 求值的相互作用；在允许改动 WarpScheduler.lean 之前无法在本文件内
  修复（WsState 类型是其所有）。故构建内定理只覆盖前 6 拍。探针验证到的
  最远事实：拍 6 x1:=1 写回、拍 7 addi x2 被 CU 接受（RAW 互锁生效）、
  拍 8-9 继续取指；beq 解析（预计拍 ~14）与 endprg（预计拍 ~20）未验证。 -/

/-- T1 拍1连通：pc_req 发出且 ibuffer 接受（完美取指 + 入队，W2） -/
theorem smT1_fetch_enq :
    (smCAt 1).fetchV = true ∧ (smCAt 1).ibEnqFire = true := by
  native_decide

/-- T2 拍1取指内容：warp0、掩码 0b11（双取） -/
theorem smT2_fetch_grp :
    (smCAt 1).fetchWid = 0#3 ∧ (smCAt 1).fetchGrp.mask = 3#2 := by
  native_decide

/-- T3 拍2末 ibuffer lane0 持有 [tag0, tag1]（= pc0/pc4 两条 addi） -/
theorem smT3_ib_queue :
    ((smSAt 2).ib.lanes 0).absTags = [0#8, 1#8] := by
  native_decide

/-- T4 拍3连通：ibuffer2issue out_x.fire 且选中 warp0（指令被 CU 接受） -/
theorem smT4_cu_accept :
    (smCAt 3).i2iXFire = true ∧ (smCAt 3).i2iXWid = 0#3 := by
  native_decide

/-- T5 拍4：接受 addi x1 的 CU1 处于 s_add（操作数收集进行中） -/
theorem smT5_cu_collect :
    (smCuAt (smSAt 4) 1).state = 1#2 := by
  native_decide

/-- T6 拍6连通收尾：DualIssue out_x fire → sALU → wb.out_x.fire，
    写回 x1 := 1（收集→发射→执行→写回全链） -/
theorem smT6_wb_x1 :
    (smCAt 6).wbXFire = true ∧ (smCAt 6).wbXIdxw = 1#8 ∧ (smCAt 6).wbXData = 1#32 := by
  native_decide

end SmEndToEndTests

/- ========================================================================= -/
/- 7. 集成障碍清单（组合中暴露的接口/抽象层级问题，上报主会话）                -/
/- ========================================================================= -/
/-
  I-SM-1【CSR 执行语义未接入】issueX 的 CSR 端口 ready=true 但写回数据 stub
    为 0（D4）；sgpr/vgpr 基址与 simt_rpc 经 SmCsrView 环境注入（D5）。
    影响：CSR 指令（SETRPC/CSRW 等）语义不正确；测试程序不含 CSR 指令。
    修复方向：接入 Arith/CSR.lean 的 CSRexe 状态机（其输入需要 CTA2csr 通路
    与 in1 操作数，接口对齐工作量独立成任务）。
  I-SM-2【拍 ~9-10 求值爆炸，未根治】原生 exe 探针实测：前 9 拍 < 3ms/拍，
    拍 10 起超分钟级；冻结实验定位与 WsState 函数位段（Fin 8 → …）闭包链
    相关（只更新 ws 的 mode 在拍 10 爆炸；纯 wsStep×2000 无 comb 则 1ms）。
    cu/srf/vrf/bankLg/chosen 已 Array 化（本文件可治的部分已治）；
    WsState 类型属 WarpScheduler.lean（本任务不许改），彻底修复需把其
    函数字段同步 Array 化或改 wsStepValid 的 mask0 重复求值结构。
    后果：构建内 native_decide 轨迹定理限前 6 拍；探针验证到拍 9
    （拍6 x1 写回、拍7 次指令 RAW 互锁后被接受、拍8-9 持续取指），
    beq 解析/endprg/终态 RF 值未验证。
  I-SM-3【向量通路整体 stub】issueV 全端口不就绪（D4）：向量/访存指令在
    DualIssue 处永久阻塞而非错误执行；branch_join 在状态里但喂 nop（D6），
    vbranch/join → SIMT 端口 → branch_back.in1 路径未接线。
  I-SM-4【LSU/DCache/ShareMem 排除】mem 指令路由死通道，语义同 I-SM-3。
    fence/fence_end 恒 false。
  I-SM-5【完美取指】D1：无 miss/重放，W2 的 status 强制路径（Pipe.lean Q2）
    与 pc_rsp 重放（PC_src=3）不覆盖；icache_req→rsp 零延迟（真实 ≥1 拍）。
  I-SM-6【W7 断言未建模】aluFn=63 的未定义指令静默流过（真实硬件有仿真
    断言）；本模型程序区外取 0 字 = NOP，不报警。
  I-SM-7【Branch_back 简化】只接 in0（ALU out2br）；in1（simt fetch_ctl）
    恒无效（随 I-SM-3）。固定优先级仲裁符合 writeback.scala:26-29。
  I-SM-8【wg_id_tag/flushDCache.ready/warpRsp.ready 环境输入】（D7）：
    真实来源是 CTA/顶层连线；本模型由 SmIn 携带，测试取恒真/恒 0。
-/

/- 公理审计：native_decide 测试定理带 Lean.ofReduceBool（其余为 Lean 标准公理） -/
#print axioms smT1_fetch_enq
#print axioms smT3_ib_queue
#print axioms smT4_cu_accept
#print axioms smT5_cu_collect
#print axioms smT6_wb_x1

end Ventus
