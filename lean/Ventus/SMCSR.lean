/- ========================================================================= -/
/-                          SMCSR.lean                                       -/
/-  SM 组合模型（向量写回版 SMVecWb）的 CSR 执行通路升级：CSRexe 真模型接入，    -/
/-  消除 SM.lean 第 7 节障碍 I-SM-1（"CSR 端口 ready=true 但写回数据 stub 为 0"）。-/
/-                                                                           -/
/-  真实链路（逐行对照）：                                                     -/
/-    pipe.scala:131        csrfile = Module(new CSRexe())                     -/
/-    pipe.scala:380        issueX.io.out_CSR <> csrfile.io.in                  -/
/-    pipe.scala:381        issueV.io.out_CSR.ready := false.B（V 侧恒堵，       -/
/-      smwComb 的 portRdyV `_ => false` 已忠实保留，本文件不动）；              -/
/-    issue.scala:84-85     out_CSR.bits.ctrl = inputBuf.bits.ctrl，            -/
/-      out_CSR.bits.in1 = inputBuf.bits.in1(0)（标量操作数 lane0）；           -/
/-    issue.scala:174-188   inst_is_vec：csr.orR → false（CSR 指令含 VSETVLI    -/
/-      一律走 X 侧——VSETVLI 译码行 isvec=Y 但 csr=CSR.S，见                     -/
/-      DecodeUnit.scala:417）；                                               -/
/-    CSR.scala:354-365     vCSR(wid).write := io.in.fire；result =              -/
/-      Queue(WriteScalarCtrl,1,pipe=true)，enq.bits.wb_wxd_rd =                -/
/-      vCSR(wid).wb_wxd_rd（组合读/覆写，当拍）；enq.valid = in.fire；          -/
/-    CSR.scala:359         in.ready = result.enq.ready & !CTA2csr.valid；      -/
/-      result 下游 wb.io.in_x(3) 恒吸收（writeback.scala 零深直连）⇒           -/
/-      enq.ready 恒 true，唯一阻塞源 = CTA 派发拍（warpReq.valid，              -/
/-      warp_schedule.scala:54 ready≡true ⇒ valid=fire）；                      -/
/-    pipe.scala:419        wb.io.in_x(3) <> csrfile.io.out（smwComb 的          -/
/-      wbXValids bit3 已有，只缺数据）；                                       -/
/-    pipe.scala:164-165    operand_collector 的 sgpr_base/vgpr_base ←           -/
/-      csrfile（本文件从 csrF 取值，替代 D5 的 SmCsrView 环境注入）；           -/
/-    pipe.scala:294        csrfile.io.simt_wid :=                               -/
/-      operand_collector.io.out(0).bits.control.wid（V 侧发射指令的 wid）⇒     -/
/-      simt_rpc 按 warp 索引（替代 smwComb 的全局单值 stub）；                  -/
/-    pipe.scala:163 + warp_schedule.scala:58-59  CTA2csr 纯转发 io.warpReq。    -/
/-                                                                           -/
/- ======================== 建模决策（对 SMVecWb.lean 的增量，C-D 区） ========= -/
/-  C-D0. smcsrComb 是 SMVecWb.lean smwComb 的全量复制 + 下列增量点              -/
/-      （SMVecWb.lean 只读；复制-增量纪律同 M-D0/W-D0）：                       -/
/-      (a) portRdyX 的 `.CSR => !inp.base.reqFire`（CSR.scala:359 的           -/
/-          !CTA2csr.valid；enq.ready 恒 true 的论据见上）；                     -/
/-      (b) fireCsr 同加 !reqFire 合取（in.fire = in.valid && in.ready）；      -/
/-      (c) wbXData 的 CSR 分支（wbXChoice=3）从 stub 0 升级为                   -/
/-          csrExeWbWxdRd（CSR.scala:364 的组合 wb_wxd_rd；result 队            -/
/-          pipe=true + deq 恒就绪 ⇒ fire 拍 = wb 拍，同拍直通）；               -/
/-      (d) sgprBase/vgprBase/simtRpc 全部改从 csrF（Fin 8 → CsrState）取：      -/
/-          cuIn 的两个 base、wbAddr/wbVAddr 的 base、bj 的 PCreconv             -/
/-          （simt_wid = V 侧发射 wid，pipe.scala:294）；                        -/
/-      (e) 状态新增 csrF；smcsrStep 每拍 csrExeStep（fireCsr 选中 warp 写 +     -/
/-          reqFire 选中 warp CTA 下发，CSR.scala:354-355）。                    -/
/-      (f) SmCsrView（s.smv.base.csr）成为死状态：step 仍按 smwStep 原样        -/
/-          更新（复制保真），但组合层不再读取。                                 -/
/-  C-D1. SmcsrIn = SmIn + warpReqData.CTAdata 中 SmIn 未携带的字段              -/
/-      （wf_size/lds_base/wf_tag/pds/knl/wgid_x/y/z/wg_id）。这些是真实         -/
/-      输入线（CTA2warp.scala:18-31），SM 级输入结构当初只暴露 6 个字段；       -/
/-      因 SM.lean 只读，在此以包装输入补齐。ctaWfCount/ctaSgpr/ctaVgpr/        -/
/-      ctaWid 复用 SmIn 的 reqCnt/reqSgpr/reqVgpr/reqWid。                      -/
/-  C-D2. CSR 写回数据时序：result Queue(1,pipe=true) 的 deq.ready =             -/
/-      wb.in_x(3).ready ≡ true（Writeback.lean D1）⇒ enq 当拍流出，            -/
/-      fireCsr 拍 = wbXFire 拍 = srf 写拍（与 sALU 同构，D3 的 CSR 实例）。     -/
/-  C-D3. rm（frm）到 fpu/sfu/tc 的输出不建模（三单元 stub，无消费者）；         -/
/-      lsu_tid/lsu_pds/lsu_numw 不建模（LSU 不在本变体；SMMem 的 M-D3 同）。    -/
/-  C-D4. csrF 为函数字段：8 个 CsrState 结构体廉价且仅被 CSR 通路读取，         -/
/-      不经 bank 仲裁链重入（AGENTS.md 闭包扇出坑不涉及）；监控器逐拍           -/
/-      具体化（SmmChk 同法）。                                                -/
/-                                                                           -/
/- ======================== Q 区（新踩坑/疑点/降级） ========================== -/
/-  Q1.（已决）SmIn 缺 CTAdata 字段 ⇒ C-D1 包装输入，不改 SM.lean。              -/
/-  Q2.（观察）CSR.scala:359 的 in.ready 不含 result 队 full 阻塞是因为           -/
/-      deq 恒就绪；若未来接入会反压的 wb，此处需改回 enq.ready 真值。           -/
/- ========================================================================= -/

import Ventus.SMVecWb
import Ventus.Arith.CSR

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 输入（C-D1）与变体状态（C-D0e）                                           -/
/- ========================================================================= -/

/-- SM CSR 变体输入：SmIn + warpReqData.CTAdata 的剩余字段（C-D1） -/
structure SmcsrIn where
  base       : SmIn
  ctaWfSize  : BitVec 6   -- dispatch2cu_wf_size_dispatch（WAVE_ITEM_WIDTH）
  ctaLdsBase : BitVec 18  -- dispatch2cu_lds_base_dispatch
  ctaWfTag   : BitVec 6   -- dispatch2cu_wf_tag_dispatch（TAG_WIDTH）
  ctaPdsBase : BitVec 32  -- dispatch2cu_pds_base_dispatch
  ctaKnlBase : BitVec 32  -- dispatch2cu_csr_knl_dispatch
  ctaWgidX   : BitVec 11
  ctaWgidY   : BitVec 11
  ctaWgidZ   : BitVec 11
  ctaWgId    : BitVec 32  -- dispatch2cu_wg_id

def smcsrInNop : SmcsrIn :=
  { base := smInNop, ctaWfSize := 0#6, ctaLdsBase := 0#18, ctaWfTag := 0#6
  , ctaPdsBase := 0#32, ctaKnlBase := 0#32
  , ctaWgidX := 0#11, ctaWgidY := 0#11, ctaWgidZ := 0#11, ctaWgId := 0#32 }

/-- CTA 派发输入（wf_tag 单独携带；其余 CTAdata 字段本场景取 0） -/
def smcsrInDispatch (wid wg : BitVec 3) (cnt : BitVec 4) (pc : BitVec 32)
    (sgpr : BitVec 12) (vgpr : BitVec 11) (wfTag : BitVec 6) : SmcsrIn :=
  { smcsrInNop with
    base := smInDispatch wid wg cnt pc sgpr vgpr, ctaWfTag := wfTag }

/-- SM CSR 变体状态：SmvState（smwComb 底座）+ 每 warp CSRFile（C-D0e） -/
structure SmcsrState where
  smv  : SmvState
  csrF : Fin 8 → CsrState   -- CSRexe 的 vCSR 数组（CSR.scala:337）

/-- 初始状态：底座原样 + 8 个 csrInit（rpc 可按场景预置，等价 RegInit 后
    软件 setrpc 的效果；本文件场景不需要 SIMT 汇合，恒 0） -/
def smcsrInitOf (v : SmvState) (f : Fin 8 → CsrState) : SmcsrState := ⟨v, f⟩

/- ========================================================================= -/
/- 2. CSRexe 输入装配（issue.scala:84-85 + CSR.scala:338-344 + CTA2csr）        -/
/- ========================================================================= -/

/-- csrExeData + CTA2csr 的单拍输入装配。
    addr = ctrl.inst(31,20)（CSR.scala:206）；in1 = exe 操作数 1 的 lane0
    （issue.scala:85）；write = in.fire（CSR.scala:354，per-warp 独热由
    csrPerWarpInput 完成）；custom0/isvec 来自译码行（:258/:262 的分支条件） -/
def smcsrCsrInp (c : SmCtrl) (bits : CuIssueBits) (fire : Bool) (inp : SmcsrIn) :
    CsrInputs :=
  { csrOp      := c.row.csr
  , addr       := c.inst.extractLsb' 20 12
  , in1        := bits.alu_src1 ⟨0, by decide⟩
  , write      := fire
  , custom0    := c.row.custom0
  , isvec      := c.row.isvec
  , ctaValid   := inp.base.reqFire
  , ctaWfCount := inp.base.reqCnt
  , ctaWfSize  := inp.ctaWfSize
  , ctaSgprBase := inp.base.reqSgpr
  , ctaVgprBase := inp.base.reqVgpr
  , ctaLdsBase := inp.ctaLdsBase
  , ctaWfTag   := inp.ctaWfTag
  , ctaPdsBase := inp.ctaPdsBase
  , ctaKnlBase := inp.ctaKnlBase
  , ctaWgidX   := inp.ctaWgidX
  , ctaWgidY   := inp.ctaWgidY
  , ctaWgidZ   := inp.ctaWgidZ
  , ctaWgId    := inp.ctaWgId }

/- ========================================================================= -/
/- 3. 组合层：smcsrComb = smwComb + C-D0 增量                                   -/
/- ========================================================================= -/

/-- 一拍的全部组合信号（SmwComb 全字段 + CSR 链字段） -/
structure SmcsrComb where
  wsIn       : WsInputs
  wsO        : WsOutputs
  fetchV     : Bool
  fetchWid   : BitVec 3
  ibEnqFire  : Bool
  ibIn       : IbTopIn
  i2iXFire   : Bool
  i2iVFire   : Bool
  i2iXWid    : BitVec 3
  i2iVWid    : BitVec 3
  outXV      : Bool
  outXWid    : BitVec 3
  ocOutXFire : Bool
  fireSAlu   : Bool
  fireCsr    : Bool
  fireWs     : Bool
  aluOut     : BitVec 32
  brFire     : Bool
  brJump     : Bool
  brWid      : BitVec 3
  brTarget   : BitVec 32
  wbXFire    : Bool
  wbXWid     : BitVec 3
  wbXIdxw    : BitVec 8
  wbXWxd     : Bool
  wbXData    : BitVec 32
  wbXChoice  : Fin 6           -- wb 仲裁 chosen（writeback.scala 固定优先级）
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
  -- ---- V-D0 继承的向量通路字段（同 SmwComb） ----
  outVV      : Bool
  outVWid    : BitVec 3
  issueVInRdy : Bool
  ocOutVFire : Bool
  fireVAlu   : Bool
  fireSimt   : Bool
  fireVBr    : Bool
  fireJoin   : Bool
  bjEv       : BjEvent 32
  bjOut      : BjOut 32
  bi         : BjBranchIn 32
  ifMask     : BitVec 32
  elseMask   : BitVec 32
  fcEnqRdy   : Bool
  fcEnqValid : Bool
  fcDeqValid : Bool
  fcDeqFire  : Bool
  fcDeqJump  : Bool
  fcDeqPC    : BitVec 32
  fcDeqWid   : BitVec 3
  brMFire    : Bool
  brMJump    : Bool
  brMWid     : BitVec 3
  brMTarget  : BitVec 32
  -- ---- W-D0b 继承：wb_v 写回链 ----
  exeMaskV   : BitVec 32
  wbVValid   : Bool
  wbVChoice  : Fin 6
  wbVFire    : Bool
  wbVWid     : BitVec 3
  wbVIdxw    : BitVec 8
  wbVWvd     : Bool
  wbVData    : RfVRow
  wbVOutData : RfVRow
  wbVMaskFn  : RfVMask
  wbVBank    : BitVec 2
  wbVAddr    : BitVec 8
  wbVWen     : Bool
  -- ---- C-D0 增量：CSR 执行链 ----
  outXCpc    : BitVec 32     -- ctrl.pc（CtrlSigs 实有字段；CSR.scala:142 引用）
  csrInp     : CsrInputs     -- csrExeData + CTA2csr 装配（CSR.scala:338-344）
  csrWbData  : BitVec 32     -- result.enq.bits.wb_wxd_rd（CSR.scala:364）

/-- 组合求值（逐段对应 SMVecWb.lean smwComb，差异处标 C-D0）。 -/
def smcsrComb (prog : SmProg) (s : SmcsrState) (inp : SmcsrIn) : SmcsrComb :=
  let sb0 := s.smv.base
  let csrF := s.csrF
  -- ---- ibuffer 头控制字重建与记分板阻塞向量（同 smwComb） ----
  let headCtrl : Fin 8 → SmCtrl := fun w =>
    smCtrlOfTag prog (sb0.ib.outBits w).tag (sb0.ib.outBits w).wid
  let sbBusy : BitVec 8 :=
    pipeScoreboardBusy (fun w => sbDelay (sb0.sb w) (smToSbCtrl (headCtrl w)))
  let ibufRdy : BitVec 8 := smPack8 (fun w => sb0.ib.ibufRdy w)
  -- ---- DualIssue：CU 发射侧（同 smwComb） ----
  let cuIssCtrl : Fin 8 → SmCtrl := fun j =>
    smCtrlOfTag prog (cuIssueBits (smCuAt sb0 j)).control.tag (cuIssueBits (smCuAt sb0 j)).control.wid
  let reqX : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sb0 j) && !smInstIsVec (cuIssCtrl j))
  let reqV : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sb0 j) && smInstIsVec (cuIssCtrl j))
  let outXV : Bool := rraOutValid (by decide) reqX sb0.lgXss
  let outXJ : Fin 8 := rraChoice (by decide) reqX sb0.lgXss
  let outXBits : CuIssueBits := cuIssueBits (smCuAt sb0 outXJ)
  let outXC : SmCtrl := cuIssCtrl outXJ
  let issC : IssCtrl := smToIssCtrl outXC
  let outVV : Bool := rraOutValid (by decide) reqV sb0.lgVss
  let outVJ : Fin 8 := rraChoice (by decide) reqV sb0.lgVss
  let outVBits : CuIssueBits := cuIssueBits (smCuAt sb0 outVJ)
  let outVC : SmCtrl := cuIssCtrl outVJ
  let issV : IssCtrl := smToIssCtrl outVC
  -- ---- sALU（同 smwComb） ----
  let fireSAlu : Bool := outXV && (issRoute issC == [.sALU])
  let aluRes : BitVec 32 × Bool :=
    saAlu (outXC.row.aluFn.extractLsb' 0 5)
      (outXBits.alu_src1 ⟨0, by decide⟩) (outXBits.alu_src2 ⟨0, by decide⟩)
      (outXBits.alu_src3 ⟨0, by decide⟩)
  let brFire : Bool := fireSAlu && (outXC.row.branch != 0#2)
  let brJump : Bool :=
    if outXC.row.branch == 1#2 then aluRes.2
    else (outXC.row.branch == 2#2 || outXC.row.branch == 3#2)
  let brWid : BitVec 3 := outXBits.control.wid
  let brTarget : BitVec 32 := outXBits.alu_src3 ⟨0, by decide⟩
  -- ---- vALU 等宽 + branch_join 事件 + fetch_ctl_buf（同 smwComb，
  --      唯 PCreconv 改按 simt_wid 索引 csrF，C-D0d；pipe.scala:294/:389） ----
  let cmpV : BitVec 32 :=
    smvCmpVec outVC.row.aluFn outVC.row.reverse
      outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let bi : BjBranchIn 32 :=
    { valuMask := exvIfMask cmpV
    , maskInit := smvMaskInit outVBits.vmask sb0.bj.tmask
    , PCbranch := outVBits.alu_src3 ⟨0, by decide⟩
    , PCexecute := outVC.pc
    , PCreconv := (csrF (wsFin outVBits.control.wid)).rpc }
  let fcEnqRdy : Bool := !s.smv.fcV || !brFire
  let portRdyV : IssPort → Bool := fun p => match p with
    | .vALU => if outVC.row.simtStack then fcEnqRdy else true
    | .SIMT => fcEnqRdy
    | _ => false
  let issueVInRdy : Bool := issInReady issV portRdyV
  let ocOutVFire : Bool := outVV && issueVInRdy
  let isVBr : Bool := issRoute issV == [.vALU, .SIMT]
  let isJoin : Bool := issRoute issV == [.SIMT]
  let fireVAlu : Bool := ocOutVFire && ((issRoute issV).any (fun t => decide (t = .vALU)))
  let fireSimt : Bool := ocOutVFire && (isVBr || isJoin)
  let bjEv : BjEvent 32 :=
    if !fireSimt then .nop
    else if isVBr then .branch bi
    else .join outVC.pc
  let bjOut : BjOut 32 := (bjSysStep sb0.bj bjEv).2
  let fcEnqValid : Bool := bjOut.fetchValid
  let fcDeqValid : Bool := s.smv.fcV || fcEnqValid
  let fcDeqFire : Bool := fcDeqValid && !brFire
  let fcDeqJump : Bool := if s.smv.fcV then s.smv.fcJ else bjOut.fetchJump
  let fcDeqPC : BitVec 32 := if s.smv.fcV then s.smv.fcPC else bjOut.fetchPC
  let fcDeqWid : BitVec 3 := if s.smv.fcV then s.smv.fcWid else outVBits.control.wid
  let brMFire : Bool := brFire || fcDeqFire
  let brMJump : Bool := if brFire then brJump else fcDeqJump
  let brMWid : BitVec 3 := if brFire then brWid else fcDeqWid
  let brMTarget : BitVec 32 := if brFire then brTarget else fcDeqPC
  -- ---- C-D0a/b：CSR 端口 ready = !CTA2csr.valid（CSR.scala:359） ----
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => !inp.base.reqFire | .ws => !brMFire | _ => false
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR]) && !inp.base.reqFire
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brMFire
  -- ---- warp_sche 输入（同 smwComb） ----
  let wsIn : WsInputs :=
    { warpReqFire := inp.base.reqFire, reqWid := inp.base.reqWid, newWgId := inp.base.reqWg
    , newWfCount := inp.base.reqCnt
    , warpControlFire := fireWs, simtStackOp := outXC.row.simtStackOp
    , wcWid := outXBits.control.wid, wgIdTag := inp.base.wgIdTag
    , warpRspReady := inp.base.warpRspReady
    , scoreboardBusy := sbBusy
    , exeBusy := 0#8
    , pcIbufRdy := ibufRdy
    , flushDCacheReady := inp.base.flushDCacheReady
    , branchFire := brMFire, branchJump := brMJump, branchWid := brMWid
    , pcRspValid := false, pcRspMiss := false, pcRspWid := 0#3
    , pcReset := inp.base.pcReset }
  let wsO : WsOutputs := wsOut sb0.ws wsIn
  -- ---- 完美取指（同 smwComb） ----
  let fetchV : Bool := wsO.pcReqValid
  let fetchWid : BitVec 3 := wsO.pcReqWid
  let fetchPC : BitVec 32 := (sb0.pcc (wsFin fetchWid)).pout
  let fetchGrp : IbGrp IbInsn :=
    ⟨smToIbInsn (smFetchInsn prog fetchWid fetchPC),
     smToIbInsn (smFetchInsn prog fetchWid (fetchPC + 4#32)),
     (sb0.pcc (wsFin fetchWid)).mask⟩
  let ibEnqFire : Bool :=
    pipeIbEnqFire fetchV 0#2 (sb0.ib.inRdy ⟨fetchV, fetchGrp, wsO.flushValid, wsO.flushWid, 0#8⟩)
  -- ---- ibuffer2issue + instDemux（同 smwComb） ----
  let warpRdyW : Fin 8 → Bool := fun w =>
    ((wsO.warpReady >>> BitVec.ofNat 8 w.val) &&& 1#8) == 1#8
  let headIsVecW : Fin 8 → Bool := fun w => ibInstIsVec (sb0.ib.outBits w)
  let xReq : BitVec 8 := smPack8 (fun w => sb0.ib.outV w && warpRdyW w && !headIsVecW w)
  let vReq : BitVec 8 := smPack8 (fun w => sb0.ib.outV w && warpRdyW w && headIsVecW w)
  let cuRdy : Fin 8 → Bool := fun j => cuControlRdy (smCuAt sb0 j)
  let i2iXV : Bool := rraOutValid (by decide) xReq sb0.lgXi2i
  let i2iXW : Fin 8 := rraChoice (by decide) xReq sb0.lgXi2i
  let i2iXC : SmCtrl := headCtrl i2iXW
  let i2iVV : Bool := rraOutValid (by decide) vReq sb0.lgVi2i
  let i2iVW : Fin 8 := rraChoice (by decide) vReq sb0.lgVi2i
  let i2iVC : SmCtrl := headCtrl i2iVW
  let dem : OcDemuxRes 8 := ocDemux cuRdy i2iVV i2iXV (smToCuCtrl i2iVC) (smToCuCtrl i2iXC)
  let i2iXFire : Bool := i2iXV && dem.in1Rdy
  let i2iVFire : Bool := i2iVV && dem.in0Rdy
  let i2iXWid : BitVec 3 := BitVec.ofNat 3 i2iXW.val
  let i2iVWid : BitVec 3 := BitVec.ofNat 3 i2iVW.val
  let i2iInRdyW : Fin 8 → Bool := fun w =>
    if headIsVecW w then rraInReady (by decide) vReq sb0.lgVi2i dem.in0Rdy w
    else rraInReady (by decide) xReq sb0.lgXi2i dem.in1Rdy w
  let ibIn : IbTopIn :=
    { inV := pipeIbInValid fetchV 0#2, grp := fetchGrp
    , flushV := wsO.flushValid, flushW := wsO.flushWid
    , outRdy := smPack8 (fun w => pipeIbOutReady (i2iInRdyW w) (warpRdyW w)) }
  let issueXInRdy : Bool := issInReady issC portRdyX
  let ocOutXFire : Bool := outXV && issueXInRdy
  let dualInRdyJ : Fin 8 → Bool := fun j =>
    if smInstIsVec (cuIssCtrl j) then rraInReady (by decide) reqV sb0.lgVss issueVInRdy j
    else rraInReady (by decide) reqX sb0.lgXss issueXInRdy j
  -- ---- C-D0e：CSR 输入装配（fireCsr 先于写回仲裁计算，供 csrInp.write） ----
  let csrInp : CsrInputs := smcsrCsrInp outXC outXBits fireCsr inp
  -- ---- 标量写回仲裁（C-D0c：CSR 分支数据 = csrExeWbWxdRd，CSR.scala:364） ----
  let aluWbValid : Bool := fireSAlu && outXC.row.wxd && (outXC.row.branch != 1#2)
  let csrWbValid : Bool := fireCsr && outXC.row.wxd
  let wbXValids : BitVec 6 :=
    (BitVec.ofBool aluWbValid).zeroExtend 6 |||
    ((BitVec.ofBool csrWbValid).zeroExtend 6 <<< 3)
  let wbXChoice : Fin 6 := wbArbChoice (by decide) wbXValids
  let wbXFire : Bool := wbArbOutValid wbXValids
  let wbXWid : BitVec 3 := outXBits.control.wid
  let wbXIdxw : BitVec 8 := outXC.regIdxw
  let wbXWxd : Bool := outXC.row.wxd
  let csrWbData : BitVec 32 := csrExeWbWxdRd csrF (wsFin outXBits.control.wid) csrInp
  let wbXData : BitVec 32 := if wbXChoice.val = 0 then aluRes.1 else csrWbData
  let wbBank : BitVec 2 := ocWbScaBankId wbXIdxw wbXWid
  let wbAddr : BitVec 8 := ocWbScaAddr ((csrF (wsFin wbXWid)).sgprBase) wbXIdxw
  let wbWrEn : Bool := wbXFire && wbXWxd && (wbXIdxw != 0#8)
  -- ---- wb_v 写回链（同 smwComb，唯 vgpr base 改自 csrF，C-D0d） ----
  let exeMaskV : BitVec 32 := smvMaskInit outVBits.vmask sb0.bj.tmask
  let wbVValid : Bool :=
    outVV && ((issRoute issV).any (fun t => decide (t = .vALU)))
      && outVC.row.wvd && !outVC.row.simtStack
  let wbVValids : BitVec 6 := (BitVec.ofBool wbVValid).zeroExtend 6
  let wbVChoice : Fin 6 := wbArbChoice (by decide) wbVValids
  let wbVFire : Bool := wbArbOutValid wbVValids
  let wbVWid : BitVec 3 := outVBits.control.wid
  let wbVIdxw : BitVec 8 := outVC.regIdxw
  let wbVWvd : Bool := outVC.row.wvd
  let wbVData : RfVRow := smwWbData outVC.row.aluFn outVC.row.reverse exeMaskV
    outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let wbVOutData : RfVRow := if wbVChoice.val = 0 then wbVData else cuRow0
  let wbVMaskFn : RfVMask := smwWbMaskFn exeMaskV
  let wbVBank : BitVec 2 := ocWbVecBankId wbVIdxw wbVWid
  let wbVAddr : BitVec 8 := ocWbVecAddr ((csrF (wsFin wbVWid)).vgprBase) wbVIdxw
  let wbVWen : Bool := wbVFire && wbVWvd
  -- ---- crossbar 输入（同 smwComb） ----
  let xin : OcXbarIn :=
    { chosenS := smChSAt sb0, chosenV := smChVAt sb0
    , validS := smChSvAt sb0, validV := smChVvAt sb0
    , dataS := fun i => rfSOut (smSrfAt sb0 i), dataV := fun i => rfVOut (smVrfAt sb0 i)
    , dataV0 := fun _ => rfVV0 }
  let cuIn : Fin 8 → CuInputs := fun j =>
    { controlValid := dem.valid j, ctrl := dem.bits j
    , bv0 := (ocXbar xin j.val 0).valid, bv1 := (ocXbar xin j.val 1).valid
    , bv2 := (ocXbar xin j.val 2).valid, bv3 := (ocXbar xin j.val 3).valid
    , bb0 := ⟨(ocXbar xin j.val 0).regOrder, (ocXbar xin j.val 0).data, (ocXbar xin j.val 0).v0⟩
    , bb1 := ⟨(ocXbar xin j.val 1).regOrder, (ocXbar xin j.val 1).data, (ocXbar xin j.val 1).v0⟩
    , bb2 := ⟨(ocXbar xin j.val 2).regOrder, (ocXbar xin j.val 2).data, (ocXbar xin j.val 2).v0⟩
    , bb3 := ⟨(ocXbar xin j.val 3).regOrder, (ocXbar xin j.val 3).data, (ocXbar xin j.val 3).v0⟩
    , issueReady := dualInRdyJ j
    , sgprBase := fun k => (csrF k).sgprBase, vgprBase := fun k => (csrF k).vgprBase }
  let reqs : Fin 32 → CuArbReq := fun p =>
    cuOutArbBits (smCuAt sb0 ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let rv : Fin 32 → Bool := fun p =>
    cuOutArbValidK (smCuAt sb0 ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let bankAddrS : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocScaChoice reqs rv i (smLgSAt sb0 i))).rsAddr
  let bankAddrV : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocVecChoice reqs rv i (smLgVAt sb0 i))).rsAddr
  -- ---- 记分板输入（同 smwComb） ----
  let sbIn : Fin 8 → SbInputs := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    { if_fire := (i2iXFire && (i2iXWid == w3)) || (i2iVFire && (i2iVWid == w3))
    , if_ctrl := if (i2iXFire && (i2iXWid == w3)) then smToSbCtrl i2iXC else smToSbCtrl i2iVC
    , wb_v_fire := wbVFire && (wbVWid == w3)
    , wb_v_wvd := wbVWvd
    , wb_v_idxw := wbVIdxw
    , wb_x_fire := wbXFire && (wbXWid == w3), wb_x_wxd := wbXWxd, wb_x_idxw := wbXIdxw
    , br_ctrl := (brMFire && (brMWid == w3)) || (fireWs && (outXBits.control.wid == w3))
        || (bjOut.complete && (outVBits.control.wid == w3))
    , fence_end := false
    , opColV_in := i2iVFire && (i2iVWid == w3)
    , opColV_out := ocOutVFire && (outVBits.control.wid == w3)
    , opColX_in := i2iXFire && (i2iXWid == w3)
    , opColX_out := ocOutXFire && (outXBits.control.wid == w3) }
  -- ---- PCcontrol 驱动（同 smwComb） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.base.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.base.reqFire && (inp.base.reqWid == w3) then ⟨inp.base.reqPC, false, 1#2, 0#2⟩
    else if brMFire && brMJump && (brMWid == w3) then ⟨brMTarget, false, 1#2, 0#2⟩
    else if fetchV && (fetchWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入（同 smwComb） ----
  let rfInS : Fin 4 → RfSInputs := fun i =>
    ⟨bankAddrS i, wbAddr, wbXData, wbWrEn && (wbBank == BitVec.ofNat 2 i.val)⟩
  let rfInV : Fin 4 → RfVInputs := fun i =>
    ⟨bankAddrV i, wbVAddr, wbVOutData, wbVWen && (wbVBank == BitVec.ofNat 2 i.val), wbVMaskFn⟩
  let bankLgS' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocScaPack reqs rv i) true (smLgSAt sb0 i)
  let bankLgV' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocVecPack reqs rv i) true (smLgSAt sb0 i)
  { wsIn := wsIn, wsO := wsO
  , fetchV := fetchV, fetchWid := fetchWid, ibEnqFire := ibEnqFire
  , ibIn := ibIn
  , i2iXFire := i2iXFire, i2iVFire := i2iVFire, i2iXWid := i2iXWid, i2iVWid := i2iVWid
  , outXV := outXV, outXWid := outXBits.control.wid, ocOutXFire := ocOutXFire
  , fireSAlu := fireSAlu, fireCsr := fireCsr, fireWs := fireWs
  , aluOut := aluRes.1
  , brFire := brFire, brJump := brJump, brWid := brWid, brTarget := brTarget
  , wbXFire := wbXFire, wbXWid := wbXWid, wbXIdxw := wbXIdxw, wbXWxd := wbXWxd
  , wbXData := wbXData, wbXChoice := wbXChoice
  , pccIn := pccIn, sbIn := sbIn, cuIn := cuIn, rfInS := rfInS, rfInV := rfInV
  , lgXi2i := rraStep (by decide) xReq dem.in1Rdy sb0.lgXi2i
  , lgVi2i := rraStep (by decide) vReq dem.in0Rdy sb0.lgVi2i
  , lgXss := rraStep (by decide) reqX issueXInRdy sb0.lgXss
  , lgVss := rraStep (by decide) reqV issueVInRdy sb0.lgVss
  , bankLgS := bankLgS', bankLgV := bankLgV'
  , chosenS := fun i => BitVec.ofNat 5 (ocScaChoice reqs rv i (smLgSAt sb0 i)).val
  , chosenV := fun i => BitVec.ofNat 5 (ocVecChoice reqs rv i (smLgSAt sb0 i)).val
  , chosenSv := fun i => ocScaOutValid reqs rv i (smLgSAt sb0 i)
  , chosenVv := fun i => ocVecOutValid reqs rv i (smLgSAt sb0 i)
  , outVV := outVV, outVWid := outVBits.control.wid
  , issueVInRdy := issueVInRdy, ocOutVFire := ocOutVFire
  , fireVAlu := fireVAlu, fireSimt := fireSimt
  , fireVBr := fireSimt && isVBr, fireJoin := fireSimt && isJoin
  , bjEv := bjEv, bjOut := bjOut, bi := bi
  , ifMask := bjIfMask bi, elseMask := bjElseMask bi
  , fcEnqRdy := fcEnqRdy, fcEnqValid := fcEnqValid
  , fcDeqValid := fcDeqValid, fcDeqFire := fcDeqFire
  , fcDeqJump := fcDeqJump, fcDeqPC := fcDeqPC, fcDeqWid := fcDeqWid
  , brMFire := brMFire, brMJump := brMJump, brMWid := brMWid, brMTarget := brMTarget
  , exeMaskV := exeMaskV, wbVValid := wbVValid, wbVChoice := wbVChoice
  , wbVFire := wbVFire, wbVWid := wbVWid, wbVIdxw := wbVIdxw, wbVWvd := wbVWvd
  , wbVData := wbVData, wbVOutData := wbVOutData, wbVMaskFn := wbVMaskFn
  , wbVBank := wbVBank, wbVAddr := wbVAddr, wbVWen := wbVWen
  -- C-D0 增量字段
  , outXCpc := outXC.pc, csrInp := csrInp, csrWbData := csrWbData }

/- ========================================================================= -/
/- 4. 单拍 step 与多拍 run（C-D0e：csrF 每拍 csrExeStep）                        -/
/- ========================================================================= -/

/-- SM CSR 变体单拍：与 smwStep 同形，唯组合信号来自 smcsrComb；
    csrF 更新 = CSR.scala:354-355 的独热路由（fireCsr 选中 warp 执行写链，
    reqFire 选中 warp 执行 CTA 下发链，二者互斥——in.ready 含 !CTA2csr.valid）。 -/
def smcsrStep (prog : SmProg) (s : SmcsrState) (inp : SmcsrIn) : SmcsrState :=
  let c := smcsrComb prog s inp
  let b0 := s.smv.base
  { smv :=
    { base :=
      { ws := wsStep b0.ws c.wsIn
      , pcc := fun w => pccStep (b0.pcc w) (c.pccIn w)
      , ib := ibTopStep b0.ib c.ibIn
      , sb := fun w => sbStep (b0.sb w) (c.sbIn w)
      , cu := ((List.finRange 8).map fun j => cuStep (smCuAt b0 j) (c.cuIn j)).toArray
      , lgXi2i := c.lgXi2i, lgVi2i := c.lgVi2i, lgXss := c.lgXss, lgVss := c.lgVss
      , bankLgS := ((List.finRange 4).map c.bankLgS).toArray
      , bankLgV := ((List.finRange 4).map c.bankLgV).toArray
      , chosenS := ((List.finRange 4).map c.chosenS).toArray
      , chosenV := ((List.finRange 4).map c.chosenV).toArray
      , chosenSv := ((List.finRange 4).map c.chosenSv).toArray
      , chosenVv := ((List.finRange 4).map c.chosenVv).toArray
      , srf := ((List.finRange 4).map fun i => rfSStep (smSrfAt b0 i) (c.rfInS i)).toArray
      , vrf := ((List.finRange 4).map fun i => rfVStep (smVrfAt b0 i) (c.rfInV i)).toArray
      , csr := if inp.base.reqFire then    -- C-D0f：死状态，按 smwStep 原样保留
          { b0.csr with
            sgprBase := fun w => if w == wsFin inp.base.reqWid then inp.base.reqSgpr else b0.csr.sgprBase w
          , vgprBase := fun w => if w == wsFin inp.base.reqWid then inp.base.reqVgpr else b0.csr.vgprBase w }
        else b0.csr
      , bj := (bjSysStep b0.bj c.bjEv).1 }
    , fcV := (s.smv.fcV && !c.fcDeqFire) || (c.fcEnqValid && !(c.fcDeqFire && !s.smv.fcV))
    , fcJ := if c.fcEnqValid && (c.fcDeqFire || !s.smv.fcV) then c.bjOut.fetchJump else s.smv.fcJ
    , fcPC := if c.fcEnqValid && (c.fcDeqFire || !s.smv.fcV) then c.bjOut.fetchPC else s.smv.fcPC
    , fcWid := if c.fcEnqValid && (c.fcDeqFire || !s.smv.fcV) then c.outVWid else s.smv.fcWid }
  , csrF := csrExeStep s.csrF c.fireCsr c.outXWid inp.base.reqWid c.csrInp }

/-- 多拍运行 -/
def smcsrRun (prog : SmProg) (s : SmcsrState) (ins : List SmcsrIn) : SmcsrState :=
  ins.foldl (smcsrStep prog) s

/- ========================================================================= -/
/- 5. 连线语义定理                                                              -/
/- ========================================================================= -/

/-- 连线：CSR 写回数据 = 选中 warp 的组合 wb_wxd_rd（CSR.scala:364；
    pipe 队 deq 恒就绪 ⇒ 同拍直通到 wb，C-D2） -/
theorem smcsrT_csrWbData_wire (prog : SmProg) (s : SmcsrState) (inp : SmcsrIn) :
    (smcsrComb prog s inp).csrWbData =
      csrExeWbWxdRd s.csrF (wsFin (smcsrComb prog s inp).outXWid)
        (smcsrComb prog s inp).csrInp := rfl

/-- 连线：wb 数据仲裁输出 = alu（choice 0）或 csrWbData（choice 3；alu/csr
    互斥——同一条指令不可能同时路由两端口，其余源恒无效） -/
theorem smcsrT_wbXData_sel (prog : SmProg) (s : SmcsrState) (inp : SmcsrIn) :
    (smcsrComb prog s inp).wbXData =
      (if (smcsrComb prog s inp).wbXChoice.val = 0
       then (smcsrComb prog s inp).aluOut
       else (smcsrComb prog s inp).csrWbData) := rfl

/-- step 后 csrF 的逐 warp 展开（CSR.scala:354-355 的独热路由）——
    模块级定理（CSR.lean 第 9 节）在整机层的引用支点 -/
theorem smcsrT_step_csrF (prog : SmProg) (s : SmcsrState) (inp : SmcsrIn) (k : Fin 8) :
    (smcsrStep prog s inp).csrF k =
      csrStep (s.csrF k) (csrPerWarpInput (smcsrComb prog s inp).csrInp
        (smcsrComb prog s inp).fireCsr (smcsrComb prog s inp).outXWid
        inp.base.reqWid (BitVec.ofNat 3 k.val)) := rfl

/-- I-33 整机引用钉死（模块级：CSR.lean `csr_step_dead_vcsr`，D2/Q5）：
    任意拍、任意 warp，vsetvli 等 isvec CSR 写永远不更新 vl——
    向量 CSR 是死状态，经 SM 整机 step 后依然成立。 -/
theorem smcsrT_i33_vl_dead (prog : SmProg) (s : SmcsrState) (inp : SmcsrIn) (k : Fin 8) :
    ((smcsrStep prog s inp).csrF k).vl = (s.csrF k).vl := by
  rw [smcsrT_step_csrF]; exact (csr_step_dead_vcsr _ _).2.2.2.2.2.2.1

/- I-32 的模块级引用（整机层证据见第 6 节轨迹判收的 frmAftFcsr=0）：
   CSR.lean `csr_fcsr_write_ignored`——寻址 fcsr(0x003) 的写静默丢弃。 -/

/- ========================================================================= -/
/- 6. 端到端轨迹：csrrw/csrrs/csrrc 读-改-写 + CTA CSR + vsetvli + I-32/I-33    -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 6.1）：                                 -/
/-    0x00 addi x5, x0, 0x25      ; 0x02500293  x5 := 0x25                     -/
/-    0x04 csrrw x1, mscratch, x5 ; 0x340290F3  mscratch:=0x25, x1:=0(旧)      -/
/-    0x08 addi x5, x0, 0x42      ; 0x04200293  x5 := 0x42                     -/
/-    0x0C csrrs x2, mscratch, x5 ; 0x3402A173  mscratch:=0x67, x2:=0x25(旧)   -/
/-    0x10 csrrc x3, mscratch, x5 ; 0x3402B1F3  mscratch:=0x25, x3:=0x67(旧)   -/
/-    0x14 csrrs x4, threadid, x0 ; 0x80002273  x4 := threadid = 3<<5 = 0x60   -/
/-    0x18 vsetvli x6, x5, 0      ; 0x0002F357  x6 := min(0x42,32) = 32        -/
/-    0x1C csrrw x7, fcsr, x5     ; 0x003293F3  I-32：写丢弃；x7 := fcsr = 0   -/
/-    0x20 csrrs x8, mscratch, x0 ; 0x34002473  x8 := 0x25（终态读回）         -/
/-    0x24 endprg                 ; 0x0000400B                                 -/
/-  派发：wf_tag=3 ⇒ CTA 下发 threadid = 0x60（CSR.scala:312）；其余 CTAdata 0。-/
/- ========================================================================= -/

section SmcsrEndToEnd

/-- CSR 测试程序 -/
def smcsrProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x02500293#32
    else if pc = 0x04#32 then 0x340290F3#32
    else if pc = 0x08#32 then 0x04200293#32
    else if pc = 0x0C#32 then 0x3402A173#32
    else if pc = 0x10#32 then 0x3402B1F3#32
    else if pc = 0x14#32 then 0x80002273#32
    else if pc = 0x18#32 then 0x0002F357#32
    else if pc = 0x1C#32 then 0x003293F3#32
    else if pc = 0x20#32 then 0x34002473#32
    else if pc = 0x24#32 then 0x0000400B#32
    else 0#32

/-- 初始状态：vrf 无预置（本场景纯标量）+ tmask 全 1 + 8 个 csrInit -/
def smcsrS0 : SmcsrState :=
  smcsrInitOf (smvInit (fun _ => 0#32) (fun _ => 0#32) 0#32) (fun _ => csrInit)

/-- 场景拍数 -/
def smcsrN : Nat := 48

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr/vgpr base=0、wf_tag=3） -/
def smcsrIns : List SmcsrIn :=
  smcsrInDispatch 0#3 0#3 1#4 0#32 0#12 0#11 3#6 :: List.replicate (smcsrN - 1) smcsrInNop

/- ---- 6.1 机器码译码回归（III 类自检） ---- -/

-- csrrw x1, mscratch, x5：CSRRW 行、csr=W、wxd、写 x1、X 侧路由 [.CSR]
example :
    let c := smDecode 0x340290F3#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "CSRRW")) && (c.row.csr == 1#2) &&
    (c.row.wxd == true) && (c.regIdxw == 1#8) && (c.regIdx1 == 5#8) &&
    (issRoute (smToIssCtrl c) == [.CSR]) &&
    (ibInstIsVec (smToIbInsn c) == false) &&
    (c.inst.extractLsb' 20 12 == csrAddrMscratch) = true := by native_decide

-- vsetvli x6, x5, 0：VSETVLI 行、csr=S、isvec=Y 但仍走 X 侧 [.CSR]
-- （issue.scala:180 的 csr.orR 优先于 isvec）
example :
    let c := smDecode 0x0002F357#32 0#3 0x18#32
    (c.row == (decRowOf decAllTables "VSETVLI")) && (c.row.csr == 2#2) &&
    (c.row.isvec == true) && (c.row.wxd == true) && (c.regIdxw == 6#8) &&
    (issRoute (smToIssCtrl c) == [.CSR]) &&
    (ibInstIsVec (smToIbInsn c) == false) = true := by native_decide

-- csrrs x4, threadid, x0：addr = 0x800（CTA 寄存器）
example :
    let c := smDecode 0x80002273#32 0#3 0x14#32
    (c.row == (decRowOf decAllTables "CSRRS")) &&
    (c.inst.extractLsb' 20 12 == csrAddrThreadid) && (c.regIdxw == 4#8) = true := by
  native_decide

-- csrrw x7, fcsr, x5：addr = 0x003（I-32 现场）
example :
    (smDecode 0x003293F3#32 0#3 0x1C#32).inst.extractLsb' 20 12 = csrAddrFcsr := by
  native_decide

/- ---- 6.2 监控器与轨迹判收 ---- -/

/-- 标量寄存器终态读取（bank/地址与写回链同式，sgprBase 取 csrF 真值） -/
def smcsrRdS (sf : SmcsrState) (idx : BitVec 8) : BitVec 32 :=
  let bank := ocWbScaBankId idx 0#3
  Base.rf_read (smSrfAt sf.smv.base ⟨bank.toNat, by have := bank.isLt; omega⟩).mem
    (ocWbScaAddr (sf.csrF ⟨0, by decide⟩).sgprBase idx).toFin

/-- 监控累积器：CSR 链事件时间线 + C-D2 同拍直通计数 + 终态判收 -/
structure SmcsrChk where
  tick       : Nat
  nCsr       : Nat          -- fireCsr 总数（应 7）
  wT         : Nat          -- csrrw mscratch fire 拍+1
  sT         : Nat          -- csrrs mscratch fire 拍+1
  cT         : Nat          -- csrrc mscratch fire 拍+1
  tidT       : Nat          -- csrrs threadid fire 拍+1
  vsetT      : Nat          -- vsetvli fire 拍+1
  fcsrT      : Nat          -- csrrw fcsr fire 拍+1
  finT       : Nat          -- 末次 csrrs mscratch fire 拍+1
  wOld       : BitVec 32    -- csrrw 写回旧值（应 0）
  sOld       : BitVec 32    -- csrrs 写回旧值（应 0x25）
  cOld       : BitVec 32    -- csrrc 写回旧值（应 0x67）
  tidVal     : BitVec 32    -- threadid 读回（应 0x60）
  vsetVal    : BitVec 32    -- vsetvli 写回 min(AVL,32)（应 32）
  fcsrVal    : BitVec 32    -- fcsr 读回（应 0）
  finVal     : BitVec 32    -- 终态 mscratch 读回（应 0x25）
  mscrAftC   : BitVec 32    -- csrrc 后 mscratch（应 0x25）
  vlAftVset  : BitVec 32    -- vsetvli 后 vl（I-33：应 0）
  frmAftFcsr : BitVec 3     -- fcsr 写后 frm（I-32：应 0）
  nWbX       : Nat          -- wbXFire 总数（2 addi + 7 csr = 9）
  mismWb     : Nat          -- fireCsr 拍同拍直通违例数（C-D2，应 0）
  finOk      : Bool
  deriving DecidableEq, Repr

def smcsrChk0 : SmcsrChk :=
  { tick := 0, nCsr := 0, wT := 0, sT := 0, cT := 0, tidT := 0, vsetT := 0
  , fcsrT := 0, finT := 0, wOld := 0#32, sOld := 0#32, cOld := 0#32
  , tidVal := 0#32, vsetVal := 0#32, fcsrVal := 0#32, finVal := 0#32
  , mscrAftC := 0#32, vlAftVset := 0#32, frmAftFcsr := 0#3
  , nWbX := 0, mismWb := 0, finOk := false }

/-- 监控单拍 -/
def smcsrMonStep (prog : SmProg) (acc : SmcsrChk × SmcsrState) (inp : SmcsrIn) :
    SmcsrChk × SmcsrState :=
  let (m, s) := acc
  let c := smcsrComb prog s inp
  let s' := smcsrStep prog s inp
  let t := m.tick
  let f0 := s'.csrF ⟨0, by decide⟩
  let m1 := { m with
      tick := t + 1
    , nCsr := m.nCsr + (if c.fireCsr then 1 else 0)
    , nWbX := m.nWbX + (if c.wbXFire then 1 else 0)
    , mismWb := m.mismWb +
        (if c.fireCsr &&
            !(c.wbXFire && (c.wbXData == c.csrWbData) && (c.wbXChoice.val == 3))
         then 1 else 0) }
  let m2 := if c.fireCsr && (c.outXCpc == 0x04#32)
      then { m1 with wT := t + 1, wOld := c.wbXData } else m1
  let m3 := if c.fireCsr && (c.outXCpc == 0x0C#32)
      then { m2 with sT := t + 1, sOld := c.wbXData } else m2
  let m4 := if c.fireCsr && (c.outXCpc == 0x10#32)
      then { m3 with cT := t + 1, cOld := c.wbXData, mscrAftC := f0.mscratch } else m3
  let m5 := if c.fireCsr && (c.outXCpc == 0x14#32)
      then { m4 with tidT := t + 1, tidVal := c.wbXData } else m4
  let m6 := if c.fireCsr && (c.outXCpc == 0x18#32)
      then { m5 with vsetT := t + 1, vsetVal := c.wbXData, vlAftVset := f0.vl } else m5
  let m7 := if c.fireCsr && (c.outXCpc == 0x1C#32)
      then { m6 with fcsrT := t + 1, fcsrVal := c.wbXData, frmAftFcsr := f0.frm } else m6
  let m8 := if c.fireCsr && (c.outXCpc == 0x20#32)
      then { m7 with finT := t + 1, finVal := c.wbXData } else m7
  (m8, s')

/-- 单遍跑完并给出全部检查结论（含终态判收） -/
def smcsrRunChk (prog : SmProg) (ins : List SmcsrIn) : SmcsrChk :=
  let (m, sf) := ins.foldl (smcsrMonStep prog) (smcsrChk0, smcsrS0)
  let f0 := sf.csrF ⟨0, by decide⟩
  { m with finOk :=
      (f0.mscratch == 0x25#32) && (f0.threadid == 0x60#32) &&
      (f0.vl == 0#32) && (f0.frm == 0#3) &&
      (sf.smv.base.ws.warpActive == 0#8) &&
      (smcsrRdS sf 1#8 == 0x00#32) && (smcsrRdS sf 2#8 == 0x25#32) &&
      (smcsrRdS sf 3#8 == 0x67#32) && (smcsrRdS sf 4#8 == 0x60#32) &&
      (smcsrRdS sf 6#8 == 0x20#32) && (smcsrRdS sf 7#8 == 0x00#32) &&
      (smcsrRdS sf 8#8 == 0x25#32) }

/-- 期望结论（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1）：
    csrrw(11) → csrrs(19) → csrrc(23) → tid(27) → vsetvli(31) → fcsr(35) →
    终读(39)；RMW 旧值链 0/0x25/0x67 与写后值 0x25/0x67/0x25 交替印证；
    7 次 fireCsr 全部同拍直通到 wb（choice=3、数据=csrWbData，mismWb=0）；
    9 次 wbXFire（+2 个 addi）。 -/
def smcsrExp : SmcsrChk :=
  { tick := smcsrN
  , nCsr := 7
  , wT := 11, sT := 19, cT := 23, tidT := 27, vsetT := 31, fcsrT := 35, finT := 39
  , wOld := 0x00#32, sOld := 0x25#32, cOld := 0x67#32
  , tidVal := 0x60#32, vsetVal := 0x20#32, fcsrVal := 0x00#32, finVal := 0x25#32
  , mscrAftC := 0x25#32, vlAftVset := 0#32, frmAftFcsr := 0#3
  , nWbX := 9, mismWb := 0
  , finOk := true }

/-- **场景主定理（CSR 执行语义端到端）**：csrrw/csrrs/csrrc 的读-改-写经
    CSRexe 通路（读旧值写回 + 新值入 csrF）、CTA 寄存器 threadid 按 warp
    返回（wf_tag<<5）、vsetvli 写回 min(AVL,32)、x1-x8 终态经真实写回链
    落入标量寄存器堆；I-32（fcsr 写丢弃，frm 不变）与 I-33（向量 CSR 死
    状态，vl 不变）在整机层钉死。对接引用：CSR.lean `csr_wb_isvec_min`/
    `csr_fcsr_write_ignored`/`csr_step_dead_vcsr`（模块级）、
    `smcsrT_i33_vl_dead`（本文件 step 级）、Writeback.lean A4（同拍直通）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smcsrTrace_ok : smcsrRunChk smcsrProg smcsrIns = smcsrExp := by
  native_decide

end SmcsrEndToEnd

/- ========================================================================= -/
/- 7. 公理审计                                                                 -/
/- ========================================================================= -/

#print axioms smcsrT_csrWbData_wire
#print axioms smcsrT_wbXData_sel
#print axioms smcsrT_step_csrF
#print axioms smcsrT_i33_vl_dead
#print axioms smcsrTrace_ok

end Ventus
