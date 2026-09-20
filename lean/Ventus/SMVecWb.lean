/- ========================================================================= -/
/-                          SMVecWb.lean                                     -/
/-  SMVec 组合变体的再扩展：把 vALU 非 SIMT 结果（wvd=1 向量指令）的写回链路    -/
/-  从 stub 升级为真模型，消除 SMVec.lean 第 7 节的障碍 V-O1（"假执行"）。      -/
/-                                                                           -/
/-  真实链路（逐行对照）：                                                     -/
/-    execution.scala:513-542  vALUv2 等宽分支 result.io.enq.bits 逐 lane 装配  -/
/-      （wb_wvd_rd/wvd_mask；:559 wvd_mask := in.bits.mask 为末赋值生效，      -/
/-       见 ExeVALU.lean D4/Q1）；                                             -/
/-    execution.scala:421      result = Queue(WriteVecCtrl,1,pipe=true)；      -/
/-    execution.scala:560      result.enq.valid = in.valid & wvd & !simt_stack；-/
/-    execution.scala:570      in.ready = Mux(simt, simt队, result队).enq.ready；-/
/-    pipe.scala:422           wb.io.in_v(0) <> valu.io.out；                  -/
/-    writeback.scala:52-61    in_v(i) 零深 Queue 直连 + Arbiter 固定优先级     -/
/-      （Writeback.lean D1/D2：全模块无寄存器，fire 拍 = 执行单元 fire 拍）；  -/
/-    pipe.scala:288-289       out_v → operand_collector.io.writeVecCtrl；     -/
/-    operandCollector.scala:603-604  wbVecBankId/wbVecBankAddr（vgpr_base     -/
/-      偏移）；:613-621 全 bank 广播 rd/rdwmask、独热 rdwen = wvd & valid      -/
/-      （**向量写使能无 reg_idxw.orR**——与标量 :622 不同，v0 可写）；          -/
/-    operandCollector.scala:624  writeVecCtrl.ready := true.B（恒吸收）；      -/
/-    pipe.scala:271           scoreb(out_v.bits.warp_id).wb_v_fire = out_v.fire；-/
/-    scoreboard.scala:110     vectorReg.clear(wb_v_fire & wb_v_ctrl.wvd, idxw)；-/
/-    regfile.scala:57-65      向量 bank 掩码写 + 旁路寄存器。                  -/
/-                                                                           -/
/- ======================== 建模决策（对 SMVec.lean 的增量，W-D 区） ========== -/
/-  W-D0. smwComb 是 SMVec.lean smvComb 的全量复制 + 下列增量点（SMVec.lean    -/
/-      只读；复制-增量纪律同 SMVec 对 SM.lean 的 V-D0）：                       -/
/-      (a) vALU 非 simt 端口 ready=true 的论据从"结果被丢弃"改为"result 队     -/
/-          enq.ready 恒 true"（下游 wb 恒吸收，见 W-D0b）——表达式不变，语义    -/
/-          升级；                                                             -/
/-      (b) 新增 wb_v 链组合：wbVValid/wbVValids/wbVChoice/wbVFire/wbVData/     -/
/-          wbVMask/wbVBank/wbVAddr/wbVWen（源码行号见上）；                    -/
/-      (c) 记分板输入 wb_v_fire/wb_v_wvd/wb_v_idxw 接真值（pipe.scala:271）；  -/
/-      (d) vrf 写口接真值（operandCollector.scala:613-621：全 bank 同址广播    -/
/-          rd/rdwmask，独热 wen）。                                           -/
/-  W-D1. 时序：result_v Queue(1,pipe=true) + wb 输入零深队列 + 仲裁无状态 +    -/
/-      out_v.ready≡true ⇒ vALU fire 拍 = wb out_v fire 拍 = bank 写拍 = busy   -/
/-      清除拍（同拍全链贯通）。这就是 Writeback.lean D5/A4 的连线事实，本文件  -/
/-      将其落入整机组合：不新增任何状态（SmvState 原样复用）。                 -/
/-  W-D2. 仲裁其余 in_v 源（fpu/lsu2wb/sfu/mul/tc，pipe.scala:423-427）恒       -/
/-      invalid——对应执行单元未建模、无输出（忠实：stub 单元不产出写回）；      -/
/-      仲裁结构（固定优先级 Arbiter + in_v(0) 最高优先级）原样建模。           -/
/-  W-D3. 写回掩码 = exe_dataV 的 mask = oc.mask & simt_stack.out_mask          -/
/-      （pipe.scala:366，复用 smvMaskInit）；wvd_mask 恒等于该 mask            -/
/-      （execution.scala:559 末赋值覆盖，ExeVALU.lean D4/Q1）。被掩 lane       -/
/-      由 regfile.scala:63-65 的掩码写保证不更新。                            -/
/-  W-D4. wbVData 逐 lane = exvLaneRdV2（vALUv2 等宽分支 :513-542，含 cmp       -/
/-      覆写 :530-535、VID :536-537、VMERGE :539-540；writemask 打包块          -/
/-      :544-552 当前配置不可达，DecodeUnit.scala:604 writemask≡0，不建模——     -/
/-      与 ExeVALU.lean D3 一致）。laneId = x.asUInt（:536）。                 -/
/- ========================================================================= -/

import Ventus.SMVec

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. wb_v 链的装配辅助（execution.scala:513-542/:559 + pipe.scala:366）        -/
/- ========================================================================= -/

/-- 写回数据行（execution.scala:513-542）：lane t = vALUv2 等宽分支的逐 lane
    结果（含比较覆写/VID/VMERGE），掩码实参 = exe_dataV mask 的第 t 位 -/
def smwWbData (fn : BitVec 6) (rev : Bool) (mask : BitVec 32)
    (r1 r2 r3 : Fin 32 → BitVec 32) : RfVRow :=
  fun t => exvLaneRdV2 fn rev (mask.getLsbD t.val) (r1 t) (r2 t) (r3 t) (BitVec.ofNat 32 t.val)

/-- 写掩码行（execution.scala:559 + operandCollector.scala:616 的 rdwmask） -/
def smwWbMaskFn (mask : BitVec 32) : RfVMask := fun t => mask.getLsbD t.val

/- ========================================================================= -/
/- 2. 组合层：smwComb = smvComb + W-D0 增量                                     -/
/- ========================================================================= -/

/-- 一拍的全部组合信号（SmvComb 全字段 + wb_v 链字段） -/
structure SmwComb where
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
  -- ---- V-D0 继承的向量通路字段（同 SmvComb） ----
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
  -- ---- W-D0b 增量：wb_v 写回链 ----
  exeMaskV   : BitVec 32         -- exe_dataV mask = oc.mask & out_mask（pipe.scala:366）
  wbVValid   : Bool              -- vALU result.enq.valid（execution.scala:560）
  wbVChoice  : Fin 6             -- wb 仲裁 chosen（writeback.scala:61）
  wbVFire    : Bool              -- wb.io.out_v.fire（ready≡true ⇒ = valid）
  wbVWid     : BitVec 3          -- out_v.bits.warp_id（execution.scala:556）
  wbVIdxw    : BitVec 8          -- out_v.bits.reg_idxw（:557）
  wbVWvd     : Bool              -- out_v.bits.wvd（:558）
  wbVData    : RfVRow            -- vALU 逐 lane 结果（:513-542）
  wbVOutData : RfVRow            -- 仲裁输出数据（in(chosen).bits，:61）
  wbVMaskFn  : RfVMask           -- out_v.bits.wvd_mask（:559）
  wbVBank    : BitVec 2          -- wbVecBankId（operandCollector.scala:603）
  wbVAddr    : BitVec 8          -- wbVecBankAddr（:604，含 vgpr_base 偏移）
  wbVWen     : Bool              -- bank 写使能 = wvd & valid（:621）

/-- 组合求值（逐段对应 SMVec.lean smvComb，差异处标 W-D0）。 -/
def smwComb (prog : SmProg) (s : SmvState) (inp : SmIn) : SmwComb :=
  let sb0 := s.base
  -- ---- ibuffer 头控制字重建与记分板阻塞向量（同 smvComb） ----
  let headCtrl : Fin 8 → SmCtrl := fun w =>
    smCtrlOfTag prog (sb0.ib.outBits w).tag (sb0.ib.outBits w).wid
  let sbBusy : BitVec 8 :=
    pipeScoreboardBusy (fun w => sbDelay (sb0.sb w) (smToSbCtrl (headCtrl w)))
  let ibufRdy : BitVec 8 := smPack8 (fun w => sb0.ib.ibufRdy w)
  -- ---- DualIssue：CU 发射侧（同 smvComb） ----
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
  -- ---- sALU（同 smvComb） ----
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
  -- ---- vALU 等宽 + branch_join 事件 + fetch_ctl_buf（同 smvComb） ----
  let cmpV : BitVec 32 :=
    smvCmpVec outVC.row.aluFn outVC.row.reverse
      outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let bi : BjBranchIn 32 :=
    { valuMask := exvIfMask cmpV
    , maskInit := smvMaskInit outVBits.vmask sb0.bj.tmask
    , PCbranch := outVBits.alu_src3 ⟨0, by decide⟩
    , PCexecute := outVC.pc
    , PCreconv := sb0.csr.simtRpc }
  let fcEnqRdy : Bool := !s.fcV || !brFire
  let portRdyV : IssPort → Bool := fun p => match p with
    -- W-D0a：非 simt 的 vALU 端口 ready=true——result 队（Queue(1,pipe=true)）
    -- enq.ready = !full || deq.ready，deq.ready = wb in_v(0).ready = 恒 true
    -- （writeback.scala:52-61 零深直连 + operandCollector.scala:624）
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
  let fcDeqValid : Bool := s.fcV || fcEnqValid
  let fcDeqFire : Bool := fcDeqValid && !brFire
  let fcDeqJump : Bool := if s.fcV then s.fcJ else bjOut.fetchJump
  let fcDeqPC : BitVec 32 := if s.fcV then s.fcPC else bjOut.fetchPC
  let fcDeqWid : BitVec 3 := if s.fcV then s.fcWid else outVBits.control.wid
  let brMFire : Bool := brFire || fcDeqFire
  let brMJump : Bool := if brFire then brJump else fcDeqJump
  let brMWid : BitVec 3 := if brFire then brWid else fcDeqWid
  let brMTarget : BitVec 32 := if brFire then brTarget else fcDeqPC
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => true | .ws => !brMFire | _ => false
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR])
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brMFire
  -- ---- warp_sche 输入（同 smvComb） ----
  let wsIn : WsInputs :=
    { warpReqFire := inp.reqFire, reqWid := inp.reqWid, newWgId := inp.reqWg
    , newWfCount := inp.reqCnt
    , warpControlFire := fireWs, simtStackOp := outXC.row.simtStackOp
    , wcWid := outXBits.control.wid, wgIdTag := inp.wgIdTag
    , warpRspReady := inp.warpRspReady
    , scoreboardBusy := sbBusy
    , exeBusy := 0#8
    , pcIbufRdy := ibufRdy
    , flushDCacheReady := inp.flushDCacheReady
    , branchFire := brMFire, branchJump := brMJump, branchWid := brMWid
    , pcRspValid := false, pcRspMiss := false, pcRspWid := 0#3
    , pcReset := inp.pcReset }
  let wsO : WsOutputs := wsOut sb0.ws wsIn
  -- ---- 完美取指（同 smvComb） ----
  let fetchV : Bool := wsO.pcReqValid
  let fetchWid : BitVec 3 := wsO.pcReqWid
  let fetchPC : BitVec 32 := (sb0.pcc (wsFin fetchWid)).pout
  let fetchGrp : IbGrp IbInsn :=
    ⟨smToIbInsn (smFetchInsn prog fetchWid fetchPC),
     smToIbInsn (smFetchInsn prog fetchWid (fetchPC + 4#32)),
     (sb0.pcc (wsFin fetchWid)).mask⟩
  let ibEnqFire : Bool :=
    pipeIbEnqFire fetchV 0#2 (sb0.ib.inRdy ⟨fetchV, fetchGrp, wsO.flushValid, wsO.flushWid, 0#8⟩)
  -- ---- ibuffer2issue + instDemux（同 smvComb） ----
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
  -- ---- 标量写回仲裁（同 smvComb） ----
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
  let wbXData : BitVec 32 := if wbXChoice.val = 0 then aluRes.1 else 0#32
  let wbBank : BitVec 2 := ocWbScaBankId wbXIdxw wbXWid
  let wbAddr : BitVec 8 := ocWbScaAddr (sb0.csr.sgprBase (wsFin wbXWid)) wbXIdxw
  let wbWrEn : Bool := wbXFire && wbXWxd && (wbXIdxw != 0#8)
  -- ---- W-D0b：wb_v 写回链（execution.scala:421/:556-560 → writeback.scala:52-61
  --      → operandCollector.scala:603-621） ----
  let exeMaskV : BitVec 32 := smvMaskInit outVBits.vmask sb0.bj.tmask   -- pipe.scala:366
  let wbVValid : Bool :=
    outVV && ((issRoute issV).any (fun t => decide (t = .vALU)))
      && outVC.row.wvd && !outVC.row.simtStack                          -- execution.scala:560
  let wbVValids : BitVec 6 := (BitVec.ofBool wbVValid).zeroExtend 6     -- in_v(1..5) 恒 invalid（W-D2）
  let wbVChoice : Fin 6 := wbArbChoice (by decide) wbVValids            -- writeback.scala:61
  let wbVFire : Bool := wbArbOutValid wbVValids                         -- out_v.ready≡true（:624）
  let wbVWid : BitVec 3 := outVBits.control.wid                         -- execution.scala:556
  let wbVIdxw : BitVec 8 := outVC.regIdxw                               -- :557
  let wbVWvd : Bool := outVC.row.wvd                                    -- :558
  let wbVData : RfVRow := smwWbData outVC.row.aluFn outVC.row.reverse exeMaskV
    outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3               -- :513-542（W-D4）
  let wbVOutData : RfVRow := if wbVChoice.val = 0 then wbVData else cuRow0  -- :61 仲裁输出
  let wbVMaskFn : RfVMask := smwWbMaskFn exeMaskV                       -- :559（W-D3）
  let wbVBank : BitVec 2 := ocWbVecBankId wbVIdxw wbVWid                -- operandCollector.scala:603
  let wbVAddr : BitVec 8 := ocWbVecAddr (sb0.csr.vgprBase (wsFin wbVWid)) wbVIdxw  -- :604
  let wbVWen : Bool := wbVFire && wbVWvd                                -- :621（向量无 reg_idxw.orR）
  -- ---- crossbar 输入（同 smvComb） ----
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
    , sgprBase := sb0.csr.sgprBase, vgprBase := sb0.csr.vgprBase }
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
  -- ---- 记分板输入（W-D0c：wb_v_* 接真值，pipe.scala:271 → scoreboard.scala:110） ----
  let sbIn : Fin 8 → SbInputs := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    { if_fire := (i2iXFire && (i2iXWid == w3)) || (i2iVFire && (i2iVWid == w3))
    , if_ctrl := if (i2iXFire && (i2iXWid == w3)) then smToSbCtrl i2iXC else smToSbCtrl i2iVC
    , wb_v_fire := wbVFire && (wbVWid == w3)          -- W-D0c（pipe.scala:271）
    , wb_v_wvd := wbVWvd                              -- scoreboard.scala:110 的 wvd 门
    , wb_v_idxw := wbVIdxw                            -- :110 的清除地址
    , wb_x_fire := wbXFire && (wbXWid == w3), wb_x_wxd := wbXWxd, wb_x_idxw := wbXIdxw
    , br_ctrl := (brMFire && (brMWid == w3)) || (fireWs && (outXBits.control.wid == w3))
        || (bjOut.complete && (outVBits.control.wid == w3))
    , fence_end := false
    , opColV_in := i2iVFire && (i2iVWid == w3)
    , opColV_out := ocOutVFire && (outVBits.control.wid == w3)
    , opColX_in := i2iXFire && (i2iXWid == w3)
    , opColX_out := ocOutXFire && (outXBits.control.wid == w3) }
  -- ---- PCcontrol 驱动（同 smvComb） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.reqFire && (inp.reqWid == w3) then ⟨inp.reqPC, false, 1#2, 0#2⟩
    else if brMFire && brMJump && (brMWid == w3) then ⟨brMTarget, false, 1#2, 0#2⟩
    else if fetchV && (fetchWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入（W-D0d：vrf 写口接真值，operandCollector.scala:613-621） ----
  let rfInS : Fin 4 → RfSInputs := fun i =>
    ⟨bankAddrS i, wbAddr, wbXData, wbWrEn && (wbBank == BitVec.ofNat 2 i.val)⟩
  let rfInV : Fin 4 → RfVInputs := fun i =>
    ⟨bankAddrV i, wbVAddr, wbVOutData, wbVWen && (wbVBank == BitVec.ofNat 2 i.val), wbVMaskFn⟩
  let bankLgS' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocScaPack reqs rv i) true (smLgSAt sb0 i)
  let bankLgV' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocVecPack reqs rv i) true (smLgVAt sb0 i)
  { wsIn := wsIn, wsO := wsO
  , fetchV := fetchV, fetchWid := fetchWid, ibEnqFire := ibEnqFire
  , ibIn := ibIn
  , i2iXFire := i2iXFire, i2iVFire := i2iVFire, i2iXWid := i2iXWid, i2iVWid := i2iVWid
  , outXV := outXV, outXWid := outXBits.control.wid, ocOutXFire := ocOutXFire
  , fireSAlu := fireSAlu, fireCsr := fireCsr, fireWs := fireWs
  , aluOut := aluRes.1
  , brFire := brFire, brJump := brJump, brWid := brWid, brTarget := brTarget
  , wbXFire := wbXFire, wbXWid := wbXWid, wbXIdxw := wbXIdxw, wbXWxd := wbXWxd
  , wbXData := wbXData
  , pccIn := pccIn, sbIn := sbIn, cuIn := cuIn, rfInS := rfInS, rfInV := rfInV
  , lgXi2i := rraStep (by decide) xReq dem.in1Rdy sb0.lgXi2i
  , lgVi2i := rraStep (by decide) vReq dem.in0Rdy sb0.lgVi2i
  , lgXss := rraStep (by decide) reqX issueXInRdy sb0.lgXss
  , lgVss := rraStep (by decide) reqV issueVInRdy sb0.lgVss
  , bankLgS := bankLgS', bankLgV := bankLgV'
  , chosenS := fun i => BitVec.ofNat 5 (ocScaChoice reqs rv i (smLgSAt sb0 i)).val
  , chosenV := fun i => BitVec.ofNat 5 (ocVecChoice reqs rv i (smLgVAt sb0 i)).val
  , chosenSv := fun i => ocScaOutValid reqs rv i (smLgSAt sb0 i)
  , chosenVv := fun i => ocVecOutValid reqs rv i (smLgVAt sb0 i)
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
  -- W-D0b 增量字段
  , exeMaskV := exeMaskV, wbVValid := wbVValid, wbVChoice := wbVChoice
  , wbVFire := wbVFire, wbVWid := wbVWid, wbVIdxw := wbVIdxw, wbVWvd := wbVWvd
  , wbVData := wbVData, wbVOutData := wbVOutData, wbVMaskFn := wbVMaskFn
  , wbVBank := wbVBank, wbVAddr := wbVAddr, wbVWen := wbVWen }

/- ========================================================================= -/
/- 3. 单拍 step 与多拍 run（SmvState 原样复用——wb_v 链全组合无状态，W-D1）      -/
/- ========================================================================= -/

/-- SM 向量写回变体单拍：与 smvStep 同形，唯组合信号来自 smwComb
    （rfInV/sbIn 的 wb_v 部分已是真值）。 -/
def smwStep (prog : SmProg) (s : SmvState) (inp : SmIn) : SmvState :=
  let c := smwComb prog s inp
  let b0 := s.base
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
    , csr := if inp.reqFire then
        { b0.csr with
          sgprBase := fun w => if w == wsFin inp.reqWid then inp.reqSgpr else b0.csr.sgprBase w
        , vgprBase := fun w => if w == wsFin inp.reqWid then inp.reqVgpr else b0.csr.vgprBase w }
      else b0.csr
    , bj := (bjSysStep b0.bj c.bjEv).1 }
  , fcV := (s.fcV && !c.fcDeqFire) || (c.fcEnqValid && !(c.fcDeqFire && !s.fcV))
  , fcJ := if c.fcEnqValid && (c.fcDeqFire || !s.fcV) then c.bjOut.fetchJump else s.fcJ
  , fcPC := if c.fcEnqValid && (c.fcDeqFire || !s.fcV) then c.bjOut.fetchPC else s.fcPC
  , fcWid := if c.fcEnqValid && (c.fcDeqFire || !s.fcV) then c.outVWid else s.fcWid }

/-- 多拍运行 -/
def smwRun (prog : SmProg) (s : SmvState) (ins : List SmIn) : SmvState :=
  ins.foldl (smwStep prog) s

/- ========================================================================= -/
/- 4. 连线语义与写回链定理                                                      -/
/- ========================================================================= -/

/-- 值保真（装配级）：wb 数据行 = vALUv2 等宽分支逐 lane 执行结果
    （execution.scala:513-542，复用 ExeVALU.lean 已验证的 exvLaneRdV2） -/
theorem smwT_wbData_fidelity (fn : BitVec 6) (rev : Bool) (mask : BitVec 32)
    (r1 r2 r3 : Fin 32 → BitVec 32) (t : Fin 32) :
    smwWbData fn rev mask r1 r2 r3 t =
      exvLaneRdV2 fn rev (mask.getLsbD t.val) (r1 t) (r2 t) (r3 t) (BitVec.ofNat 32 t.val) := rfl

/-- 连线：bank 写口数据 = wb 仲裁输出（operandCollector.scala:615 的 rd 广播） -/
theorem smwT_rfInV_rd_wire (prog : SmProg) (s : SmvState) (inp : SmIn) (i : Fin 4) :
    ((smwComb prog s inp).rfInV i).rd = (smwComb prog s inp).wbVOutData := rfl

/-- 连线：bank 写地址 = wbVecBankAddr（operandCollector.scala:614） -/
theorem smwT_rfInV_rdidx_wire (prog : SmProg) (s : SmvState) (inp : SmIn) (i : Fin 4) :
    ((smwComb prog s inp).rfInV i).rdidx = (smwComb prog s inp).wbVAddr := rfl

/-- 连线：bank 写使能 = (wvd & valid) 独热到 wbVecBankId
    （operandCollector.scala:613 的 rdwen:=false 默认 + :621 的单 bank 覆写） -/
theorem smwT_rfInV_wen_wire (prog : SmProg) (s : SmvState) (inp : SmIn) (i : Fin 4) :
    ((smwComb prog s inp).rfInV i).rdwen =
      ((smwComb prog s inp).wbVWen &&
        ((smwComb prog s inp).wbVBank == BitVec.ofNat 2 i.val)) := rfl

/-- 连线：bank 写掩码 = wvd_mask（operandCollector.scala:616） -/
theorem smwT_rfInV_mask_wire (prog : SmProg) (s : SmvState) (inp : SmIn) (i : Fin 4) :
    ((smwComb prog s inp).rfInV i).rdwmask = (smwComb prog s inp).wbVMaskFn := rfl

/-- 记分板清除连线（pipe.scala:271）：wb out_v.fire 只送达 out_v.bits.warp_id
    对应 warp 的记分板 -/
theorem smwT_sbIn_wbV_wire (prog : SmProg) (s : SmvState) (inp : SmIn) (w : Fin 8) :
    ((smwComb prog s inp).sbIn w).wb_v_fire =
      ((smwComb prog s inp).wbVFire &&
        ((smwComb prog s inp).wbVWid == BitVec.ofNat 3 w.val)) := rfl

/-- 同拍直通（Writeback.lean D1/A4 的整机实例）：wb out_v.fire = vALU 结果
    valid——固定优先级仲裁 + 唯一活源 in_v(0) + out.ready≡true，无排队无延迟 -/
theorem smwT_wbV_fire_eq_valid (prog : SmProg) (s : SmvState) (inp : SmIn) :
    (smwComb prog s inp).wbVFire = (smwComb prog s inp).wbVValid := by
  show wbArbOutValid (BitVec.zeroExtend 6 (BitVec.ofBool (smwComb prog s inp).wbVValid)) = _
  cases h : (smwComb prog s inp).wbVValid <;> decide

/-- 值保真（bank 级）：wb 写使能的 bank 写后，mem[wbVAddr] = 掩码合并的
    wb 数据行（regfile.scala:63-65 经 rfVStep；被掩 lane 保留旧值）。
    结合 smwT_rfInV_rd_wire 与 smwT_wbData_fidelity：写入值 = vALU 执行结果。 -/
theorem smwT_wb_value_fidelity (c : SmwComb) (rf : RfVState) (i : Fin 4) (t : Fin 32)
    (hwen : (c.rfInV i).rdwen = true)
    (hidx : (c.rfInV i).rdidx = c.wbVAddr)
    (hrd  : (c.rfInV i).rd = c.wbVOutData) :
    (rfVStep rf (c.rfInV i)).mem c.wbVAddr.toFin t =
      if (c.rfInV i).rdwmask t then c.wbVOutData t else rf.mem c.wbVAddr.toFin t := by
  rw [rfVStep_mem, hwen]
  simp [rfVUpd, rfVRowUpd, hidx, hrd]

/-- 整机形式：smwComb 装配下的值保真（hidx/hrd 由连线定理 rfl 供给） -/
theorem smwT_wb_value_fidelity_sm (prog : SmProg) (s : SmvState) (inp : SmIn)
    (i : Fin 4) (t : Fin 32)
    (hwen : ((smwComb prog s inp).rfInV i).rdwen = true) :
    (rfVStep (smVrfAt s.base i) ((smwComb prog s inp).rfInV i)).mem
        ((smwComb prog s inp).wbVAddr).toFin t =
      if ((smwComb prog s inp).rfInV i).rdwmask t
      then (smwComb prog s inp).wbVOutData t
      else (smVrfAt s.base i).mem ((smwComb prog s inp).wbVAddr).toFin t :=
  smwT_wb_value_fidelity _ _ _ _ hwen rfl rfl

/-- busy 清除时序（I-9 核销链 `wb_i9_clear_visible` 的整机实例化）：
    wb_v fire 拍（且无同拍同址 if set）后，目标 warp 记分板在 idxw 处的
    busy 位下一拍读为 0——写回拍即清除拍（scoreboard.scala:110 寄存、
    :88-97 下拍可见），与 Writeback.lean 的 I-9 时序链（wb_i9_gate_closed /
    wb_i9_clear_visible / wb_i9_timing / wb_i9_chain）对接。 -/
theorem smwT_wb_clears_busy (prog : SmProg) (s : SmvState) (inp : SmIn) (w : Fin 8)
    (hf : (smwComb prog s inp).wbVFire = true)
    (hw : (smwComb prog s inp).wbVWid = BitVec.ofNat 3 w.val)
    (hd : (smwComb prog s inp).wbVWvd = true)
    (hns : (((smwComb prog s inp).sbIn w).if_fire &&
        ((smwComb prog s inp).sbIn w).if_ctrl.wvd &&
        (((smwComb prog s inp).sbIn w).if_ctrl.reg_idxw ==
          (smwComb prog s inp).wbVIdxw)) = false) :
    sbRead false ((smwStep prog s inp).base.sb w).vectorReg
      (smwComb prog s inp).wbVIdxw = false := by
  have hbf : ((smwComb prog s inp).sbIn w).wb_v_fire = true := by
    show ((smwComb prog s inp).wbVFire &&
      ((smwComb prog s inp).wbVWid == BitVec.ofNat 3 w.val)) = true
    simp [hf, hw]
  have hbw : ((smwComb prog s inp).sbIn w).wb_v_wvd = true := hd
  have hba : ((smwComb prog s inp).sbIn w).wb_v_idxw =
      (smwComb prog s inp).wbVIdxw := rfl
  show sbRead false (sbStep (s.base.sb w) ((smwComb prog s inp).sbIn w)).vectorReg
    (smwComb prog s inp).wbVIdxw = false
  exact wb_i9_clear_visible _ _ _ hbf hbw hba hns

/- ========================================================================= -/
/- 5. 场景：vbranch（部分 lane 发散）→ if 路径内 vadd（掩码写回）→ join×3     -/
/-    汇合 → 全掩码 vadd 消费前者结果（RAW 全链路）→ endprg                    -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 5.1）：                                 -/
/-    0x00 vbeq v1, v2, +0x40    ; 0x0420805B  lane0 发散（同 SMVec 场景）     -/
/-    0x04 vadd.vv v3, v1, v2    ; 0x022081D7  if 路径体（tmask=0x1：仅        -/
/-                                             lane0 写回 v3，被掩 lane 不写） -/
/-    0x08 nop                  ; 0x00000013                                  -/
/-    0x0C join                 ; 0x0000205B  汇合点（= simtRpc 注入值）        -/
/-    0x10 vadd.vv v4, v3, v2    ; 0x02218257  汇合后全掩码：RAW 读 v3（依赖    -/
/-                                             第一条 vadd 的 wb_v 写回）       -/
/-    0x14 endprg               ; 0x0000400B                                  -/
/-    0x40 nop                  ; 0x00000013  else 路径体                       -/
/-    0x44 jal  x0, -0x38       ; 0xFC9FF06F  跳回汇合点 0x0C                  -/
/-  数据（初始状态预置，vgpr_base=16 ⇒ bank 内基址 16>>2=4）：                  -/
/-    v1 = [1,5,5,…]（bank1 addr4），v2 = [5,5,…]（bank2 addr4），              -/
/-    v3 预置 junk = [0x1000+t]（bank3 addr4）——被掩 lane 的旧值，              -/
/-    用于钉死"被掩 lane 不写"（若误写会覆盖 junk）。                           -/
/-  期望写回：vadd1 → bank3 addr4，掩码 0x1，lane0 := 1+5 = 6；                 -/
/-    vadd2 → bank0 addr5（4 + 4>>2），掩码全 1，lane0 := 6+5 = 11、           -/
/-    lane t≥1 := (0x1000+t)+5。                                              -/
/- ========================================================================= -/

def smwProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x0420805B#32
    else if pc = 0x04#32 then 0x022081D7#32
    else if pc = 0x08#32 then 0x00000013#32
    else if pc = 0x0C#32 then 0x0000205B#32
    else if pc = 0x10#32 then 0x02218257#32
    else if pc = 0x14#32 then 0x0000400B#32
    else if pc = 0x40#32 then 0x00000013#32
    else if pc = 0x44#32 then 0xFC9FF06F#32
    else 0#32

/-- v3 槽位的旧值（junk 行）：lane t = 0x1000+t -/
def smwJunkRow : RfVRow := fun t => 0x1000#32 + BitVec.ofNat 32 t.val

/-- 场景初始状态：v1/v2 预置（vgpr_base=16 ⇒ addr4）+ v3 junk + 汇合 PC 注入 -/
def smwS0 : SmvState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a => if a.val = 4 then smvV1Row else rfVInit.mem a }
    else if i.val = 2 then { rfVInit with mem := fun a => if a.val = 4 then smvV2Row else rfVInit.mem a }
    else if i.val = 3 then { rfVInit with mem := fun a => if a.val = 4 then smwJunkRow else rfVInit.mem a }
    else rfVInit).toArray
  { base := { smInit with
      vrf := vrf
    , csr := { smInit.csr with simtRpc := 0x0C#32 }
    , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
  , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- 场景拍数（程序规模与 SMVec 场景相同：8 条指令 + join 三次执行） -/
def smwN : Nat := 60

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr base=0、vgpr base=16），其后空转 -/
def smwIns : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smwN - 1) smInNop

/- ---- 5.1 机器码译码回归（III 类自检） ---- -/

-- vadd.vv v3, v1, v2（vm=1 无掩码）：VADD_VV 行、vd=3、vs1=1、vs2=2、wvd=1、
-- 非 simt、路由 vALU 单发
example :
    let c := smDecode 0x022081D7#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "VADD_VV")) && (c.regIdxw == 3#8) &&
    (c.regIdx1 == 1#8) && (c.regIdx2 == 2#8) && (c.row.wvd == true) &&
    (c.row.simtStack == false) && (c.row.reverse == true) &&
    (ibInstIsVec (smToIbInsn c) == true) &&
    (issRoute (smToIssCtrl c) == [.vALU]) = true := by native_decide

-- vadd.vv v4, v3, v2：vd=4、vs1=3
example :
    let c := smDecode 0x02218257#32 0#3 0x10#32
    (c.row == (decRowOf decAllTables "VADD_VV")) && (c.regIdxw == 4#8) &&
    (c.regIdx1 == 3#8) && (c.regIdx2 == 2#8) && (c.row.wvd == true) = true := by
  native_decide

-- 写回侧地址/ bank（vgpr_base=16，warp0）：v3 → bank3 addr4；v4 → bank0 addr5
example : (ocWbVecBankId 3#8 0#3 == 3#2) && (ocWbVecAddr 16#11 3#8 == 4#8) = true := by
  native_decide
example : (ocWbVecBankId 4#8 0#3 == 0#2) && (ocWbVecAddr 16#11 4#8 == 5#8) = true := by
  native_decide

-- 装配级数值：vadd1 的 wb 数据行（lane0=6、lane1=10；掩码 0x1）
example :
    let d := smwWbData (decRowOf decAllTables "VADD_VV").aluFn true 0x00000001#32
      smvV1Row smvV2Row (fun _ => 0#32)
    (d ⟨0, by decide⟩ == 6#32) && (d ⟨1, by decide⟩ == 10#32) = true := by native_decide

/- ---- 5.2 监控器与轨迹判收 ---- -/

/-- 监控累积器：写回事件捕拍 + busy 位前后视图 + 分支/汇合时间线 + 终态判收 -/
structure SmwChk where
  tick        : Nat
  vbrT        : Nat          -- vbranch 双发 fire 拍+1
  tmAftVbr    : BitVec 32    -- 分支拍后 tmask（应 = 0x1）
  wb1T        : Nat          -- vadd1（v3）wb out_v.fire 拍+1
  exe1T       : Nat          -- vadd1 的 vALU fire 拍+1（应 = wb1T，同拍直通）
  wb1Bank     : BitVec 2
  wb1Addr     : BitVec 8
  wb1Mask     : BitVec 32
  wb1D0       : BitVec 32
  wb1D1       : BitVec 32
  busy3AtWb1  : Bool         -- 写回拍前 busy(v3)（应 true）
  busy3AftWb1 : Bool         -- 写回拍后 busy(v3)（应 false，清除注册）
  wb2T        : Nat          -- vadd2（v4）wb fire 拍+1
  wb2Bank     : BitVec 2
  wb2Addr     : BitVec 8
  wb2Mask     : BitVec 32
  wb2D0       : BitVec 32
  wb2D1       : BitVec 32
  busy4AtWb2  : Bool
  busy4AftWb2 : Bool
  joinsSeen   : Nat
  join1T      : Nat
  join2T      : Nat
  join3T      : Nat
  tmAftJ2     : BitVec 32    -- join2 后 tmask（应恢复全 1）
  colCnt      : Nat          -- branch_back in0/in1 同拍竞争次数（应 0）
  fcBlk       : Nat          -- fetch_ctl enq 被堵次数（应 0）
  endT        : Nat          -- endprg 拍+1
  finOk       : Bool
  deriving DecidableEq, Repr

/-- 监控单拍 -/
def smwMonStep (prog : SmProg) (acc : SmwChk × SmvState) (inp : SmIn) : SmwChk × SmvState :=
  let (m, s) := acc
  let c := smwComb prog s inp
  let s' := smwStep prog s inp
  let t := m.tick
  let m1 := if c.fireVBr && m.vbrT == 0 then
      { m with tick := t + 1, vbrT := t + 1, tmAftVbr := s'.base.bj.tmask }
    else { m with tick := t + 1 }
  let m2 := if c.wbVFire && c.wbVIdxw == 3#8 && m1.wb1T == 0 then
      { m1 with
          wb1T := t + 1, exe1T := if c.fireVAlu then t + 1 else 0
        , wb1Bank := c.wbVBank, wb1Addr := c.wbVAddr, wb1Mask := c.exeMaskV
        , wb1D0 := c.wbVOutData ⟨0, by decide⟩, wb1D1 := c.wbVOutData ⟨1, by decide⟩
        , busy3AtWb1 := sbRead false (s.base.sb ⟨0, by decide⟩).vectorReg 3#8
        , busy3AftWb1 := sbRead false (s'.base.sb ⟨0, by decide⟩).vectorReg 3#8 }
    else m1
  let m3 := if c.wbVFire && c.wbVIdxw == 4#8 && m2.wb2T == 0 then
      { m2 with
          wb2T := t + 1
        , wb2Bank := c.wbVBank, wb2Addr := c.wbVAddr, wb2Mask := c.exeMaskV
        , wb2D0 := c.wbVOutData ⟨0, by decide⟩, wb2D1 := c.wbVOutData ⟨1, by decide⟩
        , busy4AtWb2 := sbRead false (s.base.sb ⟨0, by decide⟩).vectorReg 4#8
        , busy4AftWb2 := sbRead false (s'.base.sb ⟨0, by decide⟩).vectorReg 4#8 }
    else m2
  let m4 := if c.fireJoin then
      if m3.joinsSeen == 0 then { m3 with joinsSeen := 1, join1T := t + 1 }
      else if m3.joinsSeen == 1 then
        { m3 with joinsSeen := 2, join2T := t + 1, tmAftJ2 := s'.base.bj.tmask }
      else { m3 with joinsSeen := m3.joinsSeen + 1, join3T := t + 1 }
    else m3
  let m5 := { m4 with
      colCnt := m4.colCnt + (if c.brFire && c.fcDeqValid then 1 else 0)
    , fcBlk := m4.fcBlk + (if c.fcEnqValid && !c.fcEnqRdy then 1 else 0)
    , endT := if c.fireWs && c.outXWid == 0#3 && m4.endT == 0 then t + 1 else m4.endT }
  (m5, s')

/-- 空监控记录 -/
def smwChk0 : SmwChk :=
  { tick := 0, vbrT := 0, tmAftVbr := 0#32
  , wb1T := 0, exe1T := 0, wb1Bank := 0#2, wb1Addr := 0#8, wb1Mask := 0#32
  , wb1D0 := 0#32, wb1D1 := 0#32, busy3AtWb1 := false, busy3AftWb1 := false
  , wb2T := 0, wb2Bank := 0#2, wb2Addr := 0#8, wb2Mask := 0#32
  , wb2D0 := 0#32, wb2D1 := 0#32, busy4AtWb2 := false, busy4AftWb2 := false
  , joinsSeen := 0, join1T := 0, join2T := 0, join3T := 0, tmAftJ2 := 0#32
  , colCnt := 0, fcBlk := 0, endT := 0, finOk := false }

/-- 单遍跑完输入轨迹并给出全部检查结论（含终态判收） -/
def smwRunChk (prog : SmProg) (ins : List SmIn) : SmwChk :=
  let (m, sf) := ins.foldl (smwMonStep prog) (smwChk0, smwS0)
  { m with finOk :=
      -- SIMT 栈/掩码恢复（同 SMVec 场景判收）
      (sf.base.bj.tmask == 0xFFFFFFFF#32) && (sf.base.bj.stack.wr == 0) &&
      (sf.base.ws.warpActive == 0#8) &&
      -- v3（bank3 addr4）：lane0 被写为 6；被掩 lane1/lane31 保留 junk（不被写）
      ((smVrfAt sf.base ⟨3, by decide⟩).mem ⟨4, by decide⟩ ⟨0, by decide⟩ == 6#32) &&
      ((smVrfAt sf.base ⟨3, by decide⟩).mem ⟨4, by decide⟩ ⟨1, by decide⟩ == 0x1001#32) &&
      ((smVrfAt sf.base ⟨3, by decide⟩).mem ⟨4, by decide⟩ ⟨31, by decide⟩ == 0x101F#32) &&
      -- v4（bank0 addr5）：RAW 读到 v3 新值——lane0=11、lane1=0x1006、lane31=0x1024
      ((smVrfAt sf.base ⟨0, by decide⟩).mem ⟨5, by decide⟩ ⟨0, by decide⟩ == 11#32) &&
      ((smVrfAt sf.base ⟨0, by decide⟩).mem ⟨5, by decide⟩ ⟨1, by decide⟩ == 0x1006#32) &&
      ((smVrfAt sf.base ⟨0, by decide⟩).mem ⟨5, by decide⟩ ⟨31, by decide⟩ == 0x1024#32) &&
      (wsMask0 sf.base.ws.endprgCnt sf.base.ws.wgValid == 0#8) &&
      ((List.finRange 8).all fun j => !(sf.base.ws.wgValid j)) }

/-- 期望结论（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1） -/
def smwExp : SmwChk :=
  { tick := smwN
  , vbrT := 7, tmAftVbr := 0x00000001#32                       -- 拍6：takeif，tmask := if 掩码
  , wb1T := 11, exe1T := 11                                    -- 拍10：vALU fire = wb fire（同拍）
  , wb1Bank := 3#2, wb1Addr := 4#8                             -- v3 → bank3 addr4（vgpr_base=16）
  , wb1Mask := 0x00000001#32                                   -- 仅 lane0（tmask=0x1）
  , wb1D0 := 6#32, wb1D1 := 10#32                              -- 1+5 / 5+5（lane1 算出但被掩）
  , busy3AtWb1 := true, busy3AftWb1 := false                   -- 写回拍 busy(v3) 清除
  , wb2T := 37, wb2Bank := 0#2, wb2Addr := 5#8                 -- v4 → bank0 addr5
  , wb2Mask := 0xFFFFFFFF#32                                   -- 汇合后全掩码
  , wb2D0 := 11#32, wb2D1 := 0x1006#32                         -- RAW：6+5 / 0x1001+5
  , busy4AtWb2 := true, busy4AftWb2 := false
  , joinsSeen := 3, join1T := 17, join2T := 29, join3T := 33
  , tmAftJ2 := 0xFFFFFFFF#32                                   -- join2 后掩码恢复
  , colCnt := 0, fcBlk := 0
  , endT := 39
  , finOk := true }

/-- 主定理：vbranch（lane0 发散）→ if 路径内 vadd1 经 wb_v 链写回 v3
    （bank3 addr4，掩码 0x1——仅 lane0 落值 6，被掩 lane 保留 junk，RAW 互锁
    busy(v3) 写回拍清除）→ join×3 汇合（掩码恢复全 1）→ vadd2 全链路 RAW
    读到 v3 新值（lane0=11，lane t≥1 = junk+5）→ endprg；全程 branch_back/
    fetch_ctl_buf 无竞争，终态寄存器堆/warp 簿记全部符合手算期望。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smwTrace_ok : smwRunChk smwProg smwIns = smwExp := by
  native_decide

/- ========================================================================= -/
/- 6. 障碍清单与发现（上报主会话）                                             -/
/- ========================================================================= -/
/-
  V-O1【障碍，已在本文件解除】SMVec.lean 第 7 节的 vALU 非 SIMT 结果写回 stub
    已接通：wbVValid/wbVFire（execution.scala:560 + writeback.scala:52-61）→
    writeVecCtrl（pipe.scala:288-289）→ 向量 bank 写口（operandCollector.scala:
    613-621，vgpr_base 偏移寻址）→ 记分板 wb_v_fire 清除（pipe.scala:271 →
    scoreboard.scala:110）。全链同拍贯通（W-D1，Writeback.lean D1/A4 的整机
    实例，smwT_wbV_fire_eq_valid 钉死 fire=valid）。60 拍整机轨迹判收
    （smwTrace_ok）：掩码写回（被掩 lane 不写，junk 行钉死）、vgpr_base 偏移
    寻址、RAW 全链路（vadd2 读到 vadd1 的写回值）、busy 清除时序（写回拍
    busy=1、拍后=0）全部与手算一致。SMVec.lean/SM.lean 未改动；若主会话决定
    回合，增量点即 W-D0 的 (a)-(d) 四处。

  W-O1【模型边界，非 bug】wb 仲裁 in_v(1..5)（fpu/lsu2wb/sfu/mul/tc）恒
    invalid（W-D2）——这些执行单元未建模，其向量写回源不会出现；仲裁的
    多源竞争/优先级行为在本变体不可观测（Writeback.lean 第 1-2 节的模块级
    定理 wb_arb_* 已覆盖仲裁语义本身）。
  W-O2【模型边界】vALU 写回在同拍直通语义下不建模 result_v 队列的占用反压
    （Queue(1,pipe=true) 满且下游堵时 enq.ready=false）。下游 out_v.ready
    恒 true（operandCollector.scala:624），反压不可达；若未来接入会反压的
    单元（如 LSU 共享写回口），需把 result_v 队列升级为状态。
  W-O3【I 类观察】向量 bank 写使能无 reg_idxw.orR 保护（operandCollector.
    scala:621，标量 :622 有）——reg_idxw=0（v0）的向量写回会真实写物理
    bank（vgpr_base>>2 行）。与 regfile.scala:61 的"v0 读出恒全 1 常量"
    并存：写 v0 落入 mem 但读出侧永远看不到（读 v0 走 rfVV0 常量）。若软件
    把 v0 当普通寄存器写后读，读到的仍是全 1——语义上 v0 被硬编码为掩码
    常量寄存器，属设计意图；但 wvd=1 且 vd=0 的指令会静默浪费一次 bank 写，
    且该物理行被写脏（若 v0 的物理行与"vgpr_base>>2"指向的其它逻辑寄存器
    别名……vgpr 分配不相交（Writeback.lean A1）下无别名，无害）。记录。
  W-O4【既有结论的整机复核】RegFile.lean Q1（旁路不看写掩码）在本场景
    不触发：wb1（拍10）后 v3 的首次读地址呈现不早于拍11（busy 清除可见拍），
    旁路寄存器已过期——与 Writeback.lean I-9 核销链一致（smwT_wb_clears_busy
    即其 clear_visible 环节的整机实例化）。

  I 类审查（本范围逐行对照 execution.scala:507-571、writeback.scala:44-61、
  pipe.scala:271-272/:288-289/:416-427、operandCollector.scala:593-624、
  scoreboard.scala:109-110、regfile.scala:57-65）：未发现新 I 类 bug
  （W-O3 为观察项）。
-/

/- 公理审计：native_decide 定理带 Lean.ofReduceBool（预期，AGENTS.md 已备案） -/
#print axioms smwT_wbData_fidelity
#print axioms smwT_rfInV_rd_wire
#print axioms smwT_rfInV_wen_wire
#print axioms smwT_sbIn_wbV_wire
#print axioms smwT_wbV_fire_eq_valid
#print axioms smwT_wb_value_fidelity
#print axioms smwT_wb_value_fidelity_sm
#print axioms smwT_wb_clears_busy
#print axioms smwTrace_ok

end Ventus
