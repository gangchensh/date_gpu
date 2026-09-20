/- ========================================================================= -/
/-                          SMVec.lean                                       -/
/-  SM 组合骨架的向量通路变体：把 SM.lean 的 D4（issueV 全端口 stub）与         -/
/-  D6（branch_join 每拍喂 nop）两处升级为真模型，使 vbranch/join 的           -/
/-  SIMT 分支分化-汇合场景在整机轨迹中可构造可验证（SMTrace 障碍 F-SMT-2）。   -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    pipe.scala:366（exe_dataV mask = oc.mask & simt_stack.out_mask）、      -/
/-    :371-401（issueV/issueX 端口接线）、:382（out_SIMT→branch_ctl）、        -/
/-    :387-390（if_mask/fetch_ctl/pc_reconv）、:252-254（br_ctrl 三来源）、    -/
/-    issue.scala:57-139（out_SIMT bits 装配与路由）、                         -/
/-    execution.scala:507-571（vALUv2 等宽分支）、branch_join.scala 全体、     -/
/-    writeback.scala:14-29（Branch_back 固定优先级仲裁）。                   -/
/-                                                                           -/
/- ======================== 建模决策 / 对 SM.lean 的增量（V-D 区） ============ -/
/-  V-D0. smvComb 是 SM.lean smComb 的全量复制 + 下列增量点（SM.lean 只读）： -/
/-      (a) DualIssue v 侧：issueVInRdy 由 issInReady × portRdyV 给出（原      -/
/-          恒 false），ocOutVFire/dualInRdyJ 的 v 分支/lgVss 更新相应接线；  -/
/-      (b) vALU 等宽模型：vbranch 当拍逐 lane 求 cmp（exvLaneAlu），          -/
/-          if_mask = ~cmp（execution.scala:563，exvIfMask）；                -/
/-      (c) branch_join 真事件：vbranch 双发 fire → BjEvent.branch（mask_init -/
/-          = CU vmask ∧ out_mask，:366）；join fire → BjEvent.join（PCexecute -/
/-          = ctrl.pc）；complete → 记分板 br_ctrl 第三来源（:254）；          -/
/-      (d) fetch_ctl_buf（Queue(1,flow=true)，branch_join.scala:86）建模为   -/
/-          SmvState 的 1 项队列 fcV/fcJ/fcPC/fcWid，经 Branch_back（in0=alu  -/
/-          优先）与 alu out2br 合并后送 warp_sche.io.branch / pcc / 记分板   -/
/-          （:252）；warp_control.ready = !branch.fire（warp_schedule:52）   -/
/-          相应改用合并后的 brMFire。                                        -/
/-  V-D1. vALU 同拍直通：vALUv2 等宽分支 + result2simt Queue(1,pipe=true) +   -/
/-      if_mask_buf Queue(0) + branch_ctl_buf Queue(1,flow=true) 在下游就绪    -/
/-      时当拍贯通（与 BranchJoin.lean D1 一致）。唯一建模的反压是             -/
/-      fetch_ctl_buf 满（fcV=true 且 alu 分支占用 branch_back）时 SIMT/vALU  -/
/-      端口不就绪（fcEnqRdy = !fcV || !brFire；enq.ready = !full ||          -/
/-      deq.ready，deq.ready = !in0.valid = !brFire）。vALU 对非 simt 指令     -/
/-      ready=true 但其结果写回（wb_v 链）不建模——结果被丢弃（障碍 V-O2，     -/
/-      场景只用 wvd=0 的 vbranch/join）。                                    -/
/-  V-D2. branch_join 单 warp 单实例（BranchJoin.lean D2：各 warp 栈独立）；   -/
/-      深度沿用 SmState 既定的 4（≠ 实际 32；本场景嵌套深度 ≤1，不触及       -/
/-      上界；栈深语义由 BranchJoin/BranchJoinBounds/BranchJoinOverflow 的     -/
/-      参数化定理覆盖）。input_wid→out_mask 的 mux（:260）以单 tmask 代替，  -/
/-      场景单 warp，等价。                                                   -/
/-  V-D3. smvInit 将 bj.tmask 置为全 1（branch_join.scala:90 的               -/
/-      RegInit(~0.U)）——SM.lean 的 smInit 置 0#32，与源码不符（在 SM.lean   -/
/-      中因 D6 喂 nop 不可观测；本变体修正，见观察项 V-O4）。                -/
/-  V-D4. pc_reconv = csrfile.io.simt_rpc（pipe.scala:389）：CSRexe 未建模    -/
/-      （I-SM-1），simtRpc 由 SmCsrView 环境注入（同 SM.lean D5 的           -/
/-      sgpr/vgpr base）。场景在初始状态注入汇合 PC。                         -/
/-  V-D5. issueV 其余端口（TC/SFU/vFPU/MUL/LSU/CSR/ws/sALU）仍 ready=false    -/
/-      （pipe.scala:375-401 的另一实例 ready 绑 false；本变体只接            -/
/-      vALU/SIMT 两端口）。                                                  -/
/-  V-D6. 场景以初始状态预置向量寄存器堆（vrf bank 内容），代替向量写回通路   -/
/-      （V-O2）做测试数据建立；读通路（bank 仲裁→SyncReadMem 1 拍→crossbar） -/
/-      是 smComb 既有忠实模型，原样复用。                                     -/
/- ========================================================================= -/

import Ventus.SM
import Ventus.Arith.ExeVALU
import Ventus.SIMT.BranchJoin
import Std.Tactic.BVDecide

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 变体状态：SmState + fetch_ctl_buf（1 项 flow 队列，V-D1）                 -/
/- ========================================================================= -/

structure SmvState where
  base : SmState
  fcV   : Bool        -- fetch_ctl_buf 占用
  fcJ   : Bool        -- 缓存项 jump
  fcPC  : BitVec 32   -- 缓存项 new_pc
  fcWid : BitVec 3    -- 缓存项 wid

/-- 初始状态：smInit + bj.tmask 全 1（V-D3）+ vrf 预置（V-D6）+ simtRpc 注入（V-D4） -/
def smvInit (v1row v2row : RfVRow) (rpc : BitVec 32) : SmvState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a => if a.val = 0 then v1row else rfVInit.mem a }
    else if i.val = 2 then { rfVInit with mem := fun a => if a.val = 0 then v2row else rfVInit.mem a }
    else rfVInit).toArray
  { base := { smInit with
      vrf := vrf
    , csr := { smInit.csr with simtRpc := rpc }
    , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
  , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/- ========================================================================= -/
/- 2. vALU 等宽分支的逐 lane 组合（V-D0b）与 mask_init 装配（V-D0c）            -/
/- ========================================================================= -/

/-- 逐 lane cmp_out 打包（execution.scala:530-535 的 alu.map(_.cmp_out).asUInt；
    lane x ↔ bit x） -/
def smvCmpVec (fn : BitVec 6) (rev : Bool) (r1 r2 r3 : Fin 32 → BitVec 32) : BitVec 32 :=
  (List.finRange 32).foldl (fun acc x =>
    if (exvLaneAlu fn rev (r1 x) (r2 x) (r3 x)).2
    then acc ||| (1#32 <<< (BitVec.ofNat 32 x.val)) else acc) 0#32

/-- mask_init（issue.scala:71 `out_SIMT.bits.mask_init := inputBuf.bits.mask`，
    而 exe_dataV mask = oc.mask & out_mask，pipe.scala:366） -/
def smvMaskInit (vmask : Fin 32 → Bool) (outMask : BitVec 32) : BitVec 32 :=
  (List.finRange 32).foldl (fun acc x =>
    if vmask x && outMask.getLsbD x.val
    then acc ||| (1#32 <<< (BitVec.ofNat 32 x.val)) else acc) 0#32

/- ========================================================================= -/
/- 3. 组合层：smvComb = smComb + V-D0 增量                                      -/
/- ========================================================================= -/

structure SmvComb where
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
  brFire     : Bool              -- alu out2br valid（= branch_back in0.valid）
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
  -- ---- V-D0 增量：向量通路 ----
  outVV      : Bool              -- DualIssue out_v.valid
  outVWid    : BitVec 3
  issueVInRdy : Bool
  ocOutVFire : Bool              -- out(0).fire = exe_dataV enq fire
  fireVAlu   : Bool              -- issueV out_vALU.fire
  fireSimt   : Bool              -- issueV out_SIMT.fire
  fireVBr    : Bool              -- 双发 vbranch fire
  fireJoin   : Bool              -- SIMT-only join fire
  bjEv       : BjEvent 32        -- 本拍喂给 branch_join 的事件
  bjOut      : BjOut 32
  bi         : BjBranchIn 32     -- vbranch 事件的装配（观测用）
  ifMask     : BitVec 32         -- bjIfMask bi
  elseMask   : BitVec 32         -- bjElseMask bi
  fcEnqRdy   : Bool
  fcEnqValid : Bool
  fcDeqValid : Bool
  fcDeqFire  : Bool
  fcDeqJump  : Bool
  fcDeqPC    : BitVec 32
  fcDeqWid   : BitVec 3
  brMFire    : Bool              -- branch_back 合并输出（→ warp_sche.io.branch）
  brMJump    : Bool
  brMWid     : BitVec 3
  brMTarget  : BitVec 32

/-- 组合求值（逐段对应 SM.lean smComb，差异处标 V-D0）。 -/
def smvComb (prog : SmProg) (s : SmvState) (inp : SmIn) : SmvComb :=
  let sb0 := s.base
  -- ---- ibuffer 头控制字重建与记分板阻塞向量（同 smComb） ----
  let headCtrl : Fin 8 → SmCtrl := fun w =>
    smCtrlOfTag prog (sb0.ib.outBits w).tag (sb0.ib.outBits w).wid
  let sbBusy : BitVec 8 :=
    pipeScoreboardBusy (fun w => sbDelay (sb0.sb w) (smToSbCtrl (headCtrl w)))
  let ibufRdy : BitVec 8 := smPack8 (fun w => sb0.ib.ibufRdy w)
  -- ---- DualIssue：CU 发射侧（x 侧同 smComb；v 侧为 V-D0a 增量） ----
  let cuIssCtrl : Fin 8 → SmCtrl := fun j =>
    smCtrlOfTag prog (cuIssueBits (smCuAt sb0 j)).control.tag (cuIssueBits (smCuAt sb0 j)).control.wid
  let reqX : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sb0 j) && !smInstIsVec (cuIssCtrl j))
  let reqV : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sb0 j) && smInstIsVec (cuIssCtrl j))
  let outXV : Bool := rraOutValid (by decide) reqX sb0.lgXss
  let outXJ : Fin 8 := rraChoice (by decide) reqX sb0.lgXss
  let outXBits : CuIssueBits := cuIssueBits (smCuAt sb0 outXJ)
  let outXC : SmCtrl := cuIssCtrl outXJ
  let issC : IssCtrl := smToIssCtrl outXC
  -- V-D0a：v 侧仲裁
  let outVV : Bool := rraOutValid (by decide) reqV sb0.lgVss
  let outVJ : Fin 8 := rraChoice (by decide) reqV sb0.lgVss
  let outVBits : CuIssueBits := cuIssueBits (smCuAt sb0 outVJ)
  let outVC : SmCtrl := cuIssCtrl outVJ
  let issV : IssCtrl := smToIssCtrl outVC
  -- ---- sALU（同 smComb） ----
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
  -- ---- V-D0bcd：vALU 等宽 + branch_join 事件 + fetch_ctl_buf ----
  let cmpV : BitVec 32 :=
    smvCmpVec outVC.row.aluFn outVC.row.reverse
      outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let bi : BjBranchIn 32 :=
    { valuMask := exvIfMask cmpV
    , maskInit := smvMaskInit outVBits.vmask sb0.bj.tmask   -- :366（V-D0c）
    , PCbranch := outVBits.alu_src3 ⟨0, by decide⟩          -- issue.scala:71 in3(0)
    , PCexecute := outVC.pc                                 -- :72 ctrl.pc
    , PCreconv := sb0.csr.simtRpc }                         -- :389 simt_rpc（V-D4）
  -- fetch_ctl_buf 握手（V-D1）：enq.ready = !full || deq.ready；deq.ready = !in0.valid
  let fcEnqRdy : Bool := !s.fcV || !brFire
  let portRdyV : IssPort → Bool := fun p => match p with
    | .vALU => if outVC.row.simtStack then fcEnqRdy else true   -- V-D1：非 simt 结果丢弃（V-O2）
    | .SIMT => fcEnqRdy
    | _ => false                                                -- V-D5
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
  -- fetch_ctl_buf 出队（branch_back in1；flow 直通）
  let fcEnqValid : Bool := bjOut.fetchValid
  let fcDeqValid : Bool := s.fcV || fcEnqValid
  let fcDeqFire : Bool := fcDeqValid && !brFire
  let fcDeqJump : Bool := if s.fcV then s.fcJ else bjOut.fetchJump
  let fcDeqPC : BitVec 32 := if s.fcV then s.fcPC else bjOut.fetchPC
  let fcDeqWid : BitVec 3 := if s.fcV then s.fcWid else outVBits.control.wid
  -- ---- Branch_back 合并（writeback.scala:20-29，in0=alu 优先） ----
  let brMFire : Bool := brFire || fcDeqFire
  let brMJump : Bool := if brFire then brJump else fcDeqJump
  let brMWid : BitVec 3 := if brFire then brWid else fcDeqWid
  let brMTarget : BitVec 32 := if brFire then brTarget else fcDeqPC
  -- ---- issueX 端口 ready 表（.ws 改用合并后的 brMFire，warp_schedule.scala:52） ----
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => true | .ws => !brMFire | _ => false
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR])
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brMFire
  -- ---- warp_sche 输入（branch 三字段改用 brM*，:150-171/:252） ----
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
  -- ---- 完美取指（同 smComb D1） ----
  let fetchV : Bool := wsO.pcReqValid
  let fetchWid : BitVec 3 := wsO.pcReqWid
  let fetchPC : BitVec 32 := (sb0.pcc (wsFin fetchWid)).pout
  let fetchGrp : IbGrp IbInsn :=
    ⟨smToIbInsn (smFetchInsn prog fetchWid fetchPC),
     smToIbInsn (smFetchInsn prog fetchWid (fetchPC + 4#32)),
     (sb0.pcc (wsFin fetchWid)).mask⟩
  let ibEnqFire : Bool :=
    pipeIbEnqFire fetchV 0#2 (sb0.ib.inRdy ⟨fetchV, fetchGrp, wsO.flushValid, wsO.flushWid, 0#8⟩)
  -- ---- ibuffer2issue + instDemux（同 smComb） ----
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
  -- ---- DualIssue out.ready（V-D0a：v 侧 = issueVInRdy）与 CU issueReady ----
  let issueXInRdy : Bool := issInReady issC portRdyX
  let ocOutXFire : Bool := outXV && issueXInRdy
  let dualInRdyJ : Fin 8 → Bool := fun j =>
    if smInstIsVec (cuIssCtrl j) then rraInReady (by decide) reqV sb0.lgVss issueVInRdy j
    else rraInReady (by decide) reqX sb0.lgXss issueXInRdy j
  -- ---- 写回仲裁（同 smComb；wb_v 仍 stub，V-D6） ----
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
  -- ---- crossbar 输入（同 smComb） ----
  let xin : OcXbarIn :=
    { chosenS := smChSAt sb0, chosenV := smChVAt sb0
    , validS := smChSvAt sb0, validV := smChVvAt sb0
    , dataS := fun i => rfSOut (smSrfAt sb0 i), dataV := fun i => rfVOut (smVrfAt sb0 i)
    , dataV0 := fun _ => rfVV0 }
  -- ---- CU 输入（同 smComb，issueReady 经 V-D0a 的 dualInRdyJ） ----
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
  -- ---- bank 读仲裁（同 smComb） ----
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
  -- ---- 记分板输入（V-D0c：br_ctrl 加 complete 来源；V-D0a：opColV_out 接线） ----
  let sbIn : Fin 8 → SbInputs := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    { if_fire := (i2iXFire && (i2iXWid == w3)) || (i2iVFire && (i2iVWid == w3))
    , if_ctrl := if (i2iXFire && (i2iXWid == w3)) then smToSbCtrl i2iXC else smToSbCtrl i2iVC
    , wb_v_fire := false, wb_v_wvd := false, wb_v_idxw := 0#8
    , wb_x_fire := wbXFire && (wbXWid == w3), wb_x_wxd := wbXWxd, wb_x_idxw := wbXIdxw
    , br_ctrl := (brMFire && (brMWid == w3)) || (fireWs && (outXBits.control.wid == w3))
        || (bjOut.complete && (outVBits.control.wid == w3))   -- :254（V-D0c）
    , fence_end := false
    , opColV_in := i2iVFire && (i2iVWid == w3)
    , opColV_out := ocOutVFire && (outVBits.control.wid == w3)   -- V-D0a
    , opColX_in := i2iXFire && (i2iXWid == w3)
    , opColX_out := ocOutXFire && (outXBits.control.wid == w3) }
  -- ---- PCcontrol 驱动（branch 用 brM*；优先级序同 smComb） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.reqFire && (inp.reqWid == w3) then ⟨inp.reqPC, false, 1#2, 0#2⟩
    else if brMFire && brMJump && (brMWid == w3) then ⟨brMTarget, false, 1#2, 0#2⟩
    else if fetchV && (fetchWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入（同 smComb；vrf 写口仍 stub，V-D6） ----
  let rfInS : Fin 4 → RfSInputs := fun i =>
    ⟨bankAddrS i, wbAddr, wbXData, wbWrEn && (wbBank == BitVec.ofNat 2 i.val)⟩
  let rfInV : Fin 4 → RfVInputs := fun i =>
    ⟨bankAddrV i, 0#8, cuRow0, false, fun _ => false⟩
  -- ---- RR 仲裁器 lastGrant 更新（V-D0a：lgVss 用真 ready） ----
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
  -- V-D0 增量字段
  , outVV := outVV, outVWid := outVBits.control.wid
  , issueVInRdy := issueVInRdy, ocOutVFire := ocOutVFire
  , fireVAlu := fireVAlu, fireSimt := fireSimt
  , fireVBr := fireSimt && isVBr, fireJoin := fireSimt && isJoin
  , bjEv := bjEv, bjOut := bjOut, bi := bi
  , ifMask := bjIfMask bi, elseMask := bjElseMask bi
  , fcEnqRdy := fcEnqRdy, fcEnqValid := fcEnqValid
  , fcDeqValid := fcDeqValid, fcDeqFire := fcDeqFire
  , fcDeqJump := fcDeqJump, fcDeqPC := fcDeqPC, fcDeqWid := fcDeqWid
  , brMFire := brMFire, brMJump := brMJump, brMWid := brMWid, brMTarget := brMTarget }

/- ========================================================================= -/
/- 4. 单拍 step 与多拍 run                                                     -/
/- ========================================================================= -/

/-- SM 向量变体单拍：标量部分与 smStep 相同；bj 喂真事件；fetch_ctl_buf 按
    1 项 flow 队列语义更新（V-D1：enq 与 deq 同拍时直通不占用）。 -/
def smvStep (prog : SmProg) (s : SmvState) (inp : SmIn) : SmvState :=
  let c := smvComb prog s inp
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
    , bj := (bjSysStep b0.bj c.bjEv).1 }                          -- V-D0c：真事件
  , fcV := (s.fcV && !c.fcDeqFire) || (c.fcEnqValid && !(c.fcDeqFire && !s.fcV))
  , fcJ := if c.fcEnqValid && (c.fcDeqFire || !s.fcV) then c.bjOut.fetchJump else s.fcJ
  , fcPC := if c.fcEnqValid && (c.fcDeqFire || !s.fcV) then c.bjOut.fetchPC else s.fcPC
  , fcWid := if c.fcEnqValid && (c.fcDeqFire || !s.fcV) then c.outVWid else s.fcWid }

/-- 多拍运行 -/
def smvRun (prog : SmProg) (s : SmvState) (ins : List SmIn) : SmvState :=
  ins.foldl (smvStep prog) s

/- ========================================================================= -/
/- 5. 连线语义引理（定义即得的"连线事实" + 模块级定理的整机实例化）              -/
/- ========================================================================= -/

/-- bj 状态更新 = 模块级 bjSysStep 作用于本拍装配的事件（连线即定义） -/
theorem smvT_bj_step_wire (prog : SmProg) (s : SmvState) (inp : SmIn) :
    (smvStep prog s inp).base.bj = (bjSysStep s.base.bj (smvComb prog s inp).bjEv).1 := rfl

/-- 掩码划分在整机装配下保持：if/else 掩码不相交且拼回 mask_init
    （bjT4_mask_partition 在 SM 层装配的 BjBranchIn 上的实例化） -/
theorem smvT_mask_partition (bi : BjBranchIn 32) :
    bjIfMask bi &&& bjElseMask bi = 0 ∧ bjIfMask bi ||| bjElseMask bi = bi.maskInit :=
  bjT4_mask_partition bi

/-- I-3 契约链（Pipe.lean B-I3a 的 depth=4 实例）：vbranch 事件的 complete 与
    fetchValid 互补——至少其一成立，故当拍 beqReg 必有一条清除路径 -/
theorem smvT_complete_or_fetch (s : BjSysState 4 32) (bi : BjBranchIn 32) :
    ((bjSysStep s (.branch bi)).2.complete || (bjSysStep s (.branch bi)).2.fetchValid) = true := by
  by_cases h : bjTakeif bi <;> simp [bjSysStep, h]

/-- join 恒走 fetch_ctl 路径（B-I3b 的 depth=4 实例） -/
theorem smvT_join_fetch (s : BjSysState 4 32) (pc : BitVec 32) :
    (bjSysStep s (.join pc)).2.fetchValid = true := rfl

/- ========================================================================= -/
/- 6. 场景：vbranch（部分 lane 发散）→ 双路径 → join×2 汇合 → 掩码恢复          -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 6.1）：                                 -/
/-    0x00 vbeq v1, v2, +0x40   ; 0x0420805B  else 路径目标 0x40               -/
/-    0x04 addi x1, x0, 1       ; 0x00100093  if 路径体（标量 marker）          -/
/-    0x08 nop                  ; 0x00000013                                  -/
/-    0x0C join                 ; 0x0000205B  汇合点（= simtRpc 注入值）        -/
/-    0x10 addi x3, x0, 1       ; 0x00100193  汇合后                           -/
/-    0x14 endprg               ; 0x0000400B                                  -/
/-    0x40 addi x2, x0, 1       ; 0x00100113  else 路径体                       -/
/-    0x44 jal  x0, -0x38       ; 0xFC9FF06F  跳回汇合点 0x0C                  -/
/-  数据（V-D6 预置）：v1 = [1,5,5,…]，v2 = [5,5,…] → cmp=0xFFFFFFFE，          -/
/-  if_mask=0x00000001（1 lane）< else_mask=0xFFFFFFFE（31 lane）→ takeif，     -/
/-  先走 if 路径（fallthrough，complete 清 beqReg），join1 弹路径项跳 0x40      -/
/-  换 else 掩码，join2 弹 RPC 项跳 0x0C 恢复全掩码，join3 空栈 fallthrough。   -/
/-  形态与 BranchJoin.lean 测试 A 同构（takeif + join×3），即其整机级重现。     -/
/- ========================================================================= -/

def smvProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x0420805B#32
    else if pc = 0x04#32 then 0x00100093#32
    else if pc = 0x08#32 then 0x00000013#32
    else if pc = 0x0C#32 then 0x0000205B#32
    else if pc = 0x10#32 then 0x00100193#32
    else if pc = 0x14#32 then 0x0000400B#32
    else if pc = 0x40#32 then 0x00100113#32
    else if pc = 0x44#32 then 0xFC9FF06F#32
    else 0#32

/-- 预置向量数据（V-D6）：lane0 发散（1≠5），其余 lane 相等 -/
def smvV1Row : RfVRow := fun t => if t.val = 0 then 1#32 else 5#32
def smvV2Row : RfVRow := fun _ => 5#32

/-- 场景初始状态：汇合 PC = 0x0C（V-D4 注入） -/
def smvS0 : SmvState := smvInit smvV1Row smvV2Row 0x0C#32

/- ---- 6.1 机器码译码回归（III 类自检） ---- -/

-- vbeq v1, v2, +0x40：VBEQ 行、rs1=v1、rs2=v2、B 型 imm=0x40、双发路由
example :
    let c := smDecode 0x0420805B#32 0#3 0x00#32
    (c.row == (decRowOf decAllTables "VBEQ")) && (c.regIdx1 == 1#8) && (c.regIdx2 == 2#8) &&
    (rfImmGen rfIMM_B c.inst 0#7 == 0x40#32) && (c.row.branch == 1#2) &&
    (c.row.simtStack == true) && (c.row.simtStackOp == false) &&
    (ibInstIsVec (smToIbInsn c) == true) &&
    (issRoute (smToIssCtrl c) == [.vALU, .SIMT]) = true := by native_decide

-- join：SIMT-only 路由
example :
    let c := smDecode 0x0000205B#32 0#3 0x0C#32
    (c.row == (decRowOf decAllTables "JOIN")) &&
    (issRoute (smToIssCtrl c) == [.SIMT]) &&
    (ibInstIsVec (smToIbInsn c) == true) = true := by native_decide

-- jal x0, -0x38 @ 0x44：B_J、imm=-56（落 0x0C）
example :
    let c := smDecode 0xFC9FF06F#32 0#3 0x44#32
    (c.row.branch == 2#2) && (c.row.selImm == rfIMM_J) &&
    (rfImmGen rfIMM_J c.inst 0#7 == 0xFFFFFFC8#32) = true := by native_decide

-- 发射侧装配：vbranch 的 bi 各字段（在 v1/v2 预置行上的逐 lane 结果）
example :
    let cmpV := smvCmpVec (decRowOf decAllTables "VBEQ").aluFn false smvV1Row smvV2Row (fun _ => 0x40#32)
    (cmpV == 0xFFFFFFFE#32) && (exvIfMask cmpV == 0x00000001#32) = true := by native_decide

example :
    (smvMaskInit (fun _ => true) 0xFFFFFFFF#32 == 0xFFFFFFFF#32) = true := by native_decide

/- ---- 6.2 输入轨迹与监控器（拍号 = 输入索引；记录值 = 拍号+1，0 表未见） ---- -/

/-- 场景拍数（endprg 于拍 38 fire，簿记随后数拍内回收） -/
def smvN : Nat := 60

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr/vgpr base=0），其后空转。
    wg0 的 wgIdTag=0 与 smInNop 默认一致，无需回填（探针核实簿记全回收）。 -/
def smvIns : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 0#11 :: List.replicate (smvN - 1) smInNop

/-- 监控累积器：关键点事件捕拍 + 事件装配字段 + 栈/掩码演化 + 异常计数 -/
structure SmvChk where
  tick       : Nat
  vbrT       : Nat                  -- vbranch SIMT 双发 fire 拍+1
  vbrComplete : Bool                -- complete（takeif → 应 true）
  vbrFetch   : Bool                 -- fetchValid（takeif → 应 false）
  ifMask     : BitVec 32            -- 分支拍 bjIfMask
  elseMask   : BitVec 32            -- 分支拍 bjElseMask
  biValu     : BitVec 32            -- 装配的 bi 各字段（连线观测）
  biMaskInit : BitVec 32
  biPcBranch : BitVec 32
  biPcExec   : BitVec 32
  biPcReconv : BitVec 32
  tmAftVbr   : BitVec 32            -- 分支拍后 tmask/wr/rd
  wrAftVbr   : BitVec (bjPtrWidth 4)
  rdAftVbr   : BitVec (bjPtrWidth 4)
  joinsSeen  : Nat
  join1T     : Nat
  j1popPC    : BitVec 32
  j1popMask  : BitVec 32
  tmAftJ1    : BitVec 32
  join2T     : Nat
  j2popPC    : BitVec 32
  j2popMask  : BitVec 32
  tmAftJ2    : BitVec 32
  wrAftJ2    : BitVec (bjPtrWidth 4)
  rdAftJ2    : BitVec (bjPtrWidth 4)
  join3T     : Nat
  j3jump     : Bool                 -- join3（空栈）应无跳转
  colCnt     : Nat                  -- branch_back in0/in1 同拍竞争次数（应 0）
  fcBlk      : Nat                  -- fetch_ctl enq 被堵次数（应 0）
  wbX1       : Nat                  -- x1 写回拍+1
  wbD1       : BitVec 32
  wbX2       : Nat
  wbD2       : BitVec 32
  wbX3       : Nat
  wbD3       : BitVec 32
  endT       : Nat                  -- endprg（warp_control fire）拍+1
  finOk      : Bool
  deriving DecidableEq, Repr

/-- 监控单拍（comb 观测拍前状态与输入，step 后状态捕栈/掩码演化） -/
def smvMonStep (prog : SmProg) (acc : SmvChk × SmvState) (inp : SmIn) : SmvChk × SmvState :=
  let (m, s) := acc
  let c := smvComb prog s inp
  let s' := smvStep prog s inp
  let t := m.tick
  let m1 := if c.fireVBr && m.vbrT == 0 then
      { m with
          tick := t + 1, vbrT := t + 1
        , vbrComplete := c.bjOut.complete, vbrFetch := c.bjOut.fetchValid
        , ifMask := c.ifMask, elseMask := c.elseMask
        , biValu := c.bi.valuMask, biMaskInit := c.bi.maskInit
        , biPcBranch := c.bi.PCbranch, biPcExec := c.bi.PCexecute, biPcReconv := c.bi.PCreconv
        , tmAftVbr := s'.base.bj.tmask
        , wrAftVbr := s'.base.bj.stack.wr, rdAftVbr := s'.base.bj.stack.rd }
    else { m with tick := t + 1 }
  let m2 := if c.fireJoin then
      if m1.joinsSeen == 0 then
        { m1 with
            joinsSeen := 1, join1T := t + 1
          , j1popPC := c.bjOut.popPC, j1popMask := c.bjOut.popMask
          , tmAftJ1 := s'.base.bj.tmask }
      else if m1.joinsSeen == 1 then
        { m1 with
            joinsSeen := 2, join2T := t + 1
          , j2popPC := c.bjOut.popPC, j2popMask := c.bjOut.popMask
          , tmAftJ2 := s'.base.bj.tmask
          , wrAftJ2 := s'.base.bj.stack.wr, rdAftJ2 := s'.base.bj.stack.rd }
      else
        { m1 with joinsSeen := m1.joinsSeen + 1, join3T := t + 1, j3jump := c.fcDeqJump }
    else m1
  let m3 := { m2 with
      colCnt := m2.colCnt + (if c.brFire && c.fcDeqValid then 1 else 0)
    , fcBlk := m2.fcBlk + (if c.fcEnqValid && !c.fcEnqRdy then 1 else 0)
    , endT := if c.fireWs && c.outXWid == 0#3 && m2.endT == 0 then t + 1 else m2.endT }
  let m4 := if !(c.wbXFire && c.wbXWxd && c.wbXWid == 0#3) then m3
    else if c.wbXIdxw == 1#8 && m3.wbX1 == 0 then { m3 with wbX1 := t + 1, wbD1 := c.wbXData }
    else if c.wbXIdxw == 2#8 && m3.wbX2 == 0 then { m3 with wbX2 := t + 1, wbD2 := c.wbXData }
    else if c.wbXIdxw == 3#8 && m3.wbX3 == 0 then { m3 with wbX3 := t + 1, wbD3 := c.wbXData }
    else m3
  (m4, s')

/-- 单遍跑完输入轨迹并给出全部检查结论（含终态判收） -/
def smvRunChk (prog : SmProg) (ins : List SmIn) : SmvChk :=
  let init : SmvChk × SmvState :=
    ({ tick := 0, vbrT := 0, vbrComplete := false, vbrFetch := false
     , ifMask := 0#32, elseMask := 0#32
     , biValu := 0#32, biMaskInit := 0#32, biPcBranch := 0#32
     , biPcExec := 0#32, biPcReconv := 0#32
     , tmAftVbr := 0#32, wrAftVbr := 0, rdAftVbr := 0
     , joinsSeen := 0
     , join1T := 0, j1popPC := 0#32, j1popMask := 0#32, tmAftJ1 := 0#32
     , join2T := 0, j2popPC := 0#32, j2popMask := 0#32, tmAftJ2 := 0#32
     , wrAftJ2 := 0, rdAftJ2 := 0
     , join3T := 0, j3jump := false
     , colCnt := 0, fcBlk := 0
     , wbX1 := 0, wbD1 := 0#32, wbX2 := 0, wbD2 := 0#32, wbX3 := 0, wbD3 := 0#32
     , endT := 0, finOk := false }, smvS0)
  let (m, sf) := ins.foldl (smvMonStep prog) init
  { m with finOk :=
      (sf.base.bj.tmask == 0xFFFFFFFF#32) && (sf.base.bj.stack.wr == 0) &&
      (sf.base.ws.warpActive == 0#8) &&
      (Base.rf_read (smSrfAt sf.base ⟨1, by decide⟩).mem ⟨0, by decide⟩ == 1#32) &&
      (Base.rf_read (smSrfAt sf.base ⟨2, by decide⟩).mem ⟨0, by decide⟩ == 1#32) &&
      (Base.rf_read (smSrfAt sf.base ⟨3, by decide⟩).mem ⟨0, by decide⟩ == 1#32) &&
      (wsMask0 sf.base.ws.endprgCnt sf.base.ws.wgValid == 0#8) &&
      ((List.finRange 8).all fun j => !(sf.base.ws.wgValid j)) }

/-- 期望结论（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1） -/
def smvExp : SmvChk :=
  { tick := smvN
  , vbrT := 7, vbrComplete := true, vbrFetch := false          -- 拍6：takeif，无 fetch
  , ifMask := 0x00000001#32, elseMask := 0xFFFFFFFE#32         -- 1 lane vs 31 lane
  , biValu := 0x00000001#32, biMaskInit := 0xFFFFFFFF#32
  , biPcBranch := 0x40#32, biPcExec := 0x00#32, biPcReconv := 0x0C#32
  , tmAftVbr := 0x00000001#32, wrAftVbr := 2, rdAftVbr := 1    -- push 两项，走 if 掩码
  , joinsSeen := 3
  , join1T := 17, j1popPC := 0x40#32, j1popMask := 0xFFFFFFFE#32
  , tmAftJ1 := 0xFFFFFFFE#32                                   -- 拍16：弹路径项→else 路径
  , join2T := 29, j2popPC := 0x0C#32, j2popMask := 0xFFFFFFFF#32
  , tmAftJ2 := 0xFFFFFFFF#32, wrAftJ2 := 0, rdAftJ2 := 7       -- 拍28：弹 RPC 项，掩码恢复（rd 回绕，同测试 A）
  , join3T := 33, j3jump := false                              -- 拍32：空栈 fallthrough
  , colCnt := 0, fcBlk := 0                                    -- branch_back/fetch_ctl_buf 无竞争无阻塞
  , wbX1 := 11, wbD1 := 1#32, wbX2 := 23, wbD2 := 1#32, wbX3 := 37, wbD3 := 1#32
  , endT := 39                                                 -- 拍38：endprg
  , finOk := true }

/-- 主定理：vbranch（lane0 发散）→ if 路径 → join1 跳 else 路径（0x40，掩码
    0xFFFFFFFE）→ jal 回汇合点 → join2 弹 RPC 项恢复全掩码 → join3 空栈
    fallthrough → 汇合后 addi → endprg；全程 branch_back/fetch_ctl_buf 无竞争，
    终态掩码/栈/寄存器堆/warp 簿记全部符合手算期望。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smvTrace_ok : smvRunChk smvProg smvIns = smvExp := by
  native_decide

/- ---- 6.3 与 BranchJoin 模块级测试的整机版对照（测试 A 形态的重现） ---- -/

/-- 场景在 branch_join 接口上的期望事件流（与 BranchJoin 测试 A 同构：
    takeif 分支 + 三次 join；PC 换成整机程序的 0x00/0x40/0x0C） -/
def smvExpEvents : List (BjEvent 32) :=
  [.branch ⟨0x00000001#32, 0xFFFFFFFF#32, 0x40#32, 0x00#32, 0x0C#32⟩,
   .join 0x0C#32, .join 0x0C#32, .join 0x0C#32]

/-- 整机连线的 branch_join 终态 = 模块级 bjRun 对同一事件流的终态
    （tmask/wr/rd/两项栈内容逐点相等）——即"装配的事件流忠实送达模块语义" -/
theorem smvT_module_replay :
    let sfin := smvRun smvProg smvS0 smvIns
    let bfin := bjRun smvS0.base.bj smvExpEvents
    sfin.base.bj.tmask = bfin.tmask ∧
    sfin.base.bj.stack.wr = bfin.stack.wr ∧
    sfin.base.bj.stack.rd = bfin.stack.rd ∧
    sfin.base.bj.stack.mem ⟨0, by decide⟩ = bfin.stack.mem ⟨0, by decide⟩ ∧
    sfin.base.bj.stack.mem ⟨1, by decide⟩ = bfin.stack.mem ⟨1, by decide⟩ ∧
    bfin.stack.mem ⟨0, by decide⟩ = ⟨0x0C#32, 0x0C#32, 0xFFFFFFFF#32⟩ ∧   -- RPC 项
    bfin.stack.mem ⟨1, by decide⟩ = ⟨0x0C#32, 0x40#32, 0xFFFFFFFE#32⟩ := by -- 路径项
  native_decide

/-- 掩码恢复的符号化组合：模块级 bjT2_mask_restore 实例化到本场景事件
    （前提 hdiv/hwr/hovf/hj1/hj2 由数值事实供给——这正是"连线事实"：
    整机装配的 PC 序列使两次 join 均为有效 pop） -/
theorem smvT_mask_restore_scene :
    let s0 := smvS0.base.bj
    let bi : BjBranchIn 32 := ⟨0x00000001#32, 0xFFFFFFFF#32, 0x40#32, 0x00#32, 0x0C#32⟩
    (bjSysStep (bjSysStep (bjSysStep s0 (.branch bi)).1 (.join 0x0C#32)).1 (.join 0x0C#32)).1.tmask
      = s0.tmask ∧
    (bjSysStep (bjSysStep s0 (.branch bi)).1 (.join 0x0C#32)).1.tmask
      = (bjPushentry bi).newMask := by
  exact bjT2_mask_restore smvS0.base.bj
    ⟨0x00000001#32, 0xFFFFFFFF#32, 0x40#32, 0x00#32, 0x0C#32⟩
    (by native_decide) (by native_decide) (by native_decide)
    0x0C#32 0x0C#32 (by native_decide) (by native_decide)

/- ========================================================================= -/
/- 7. 障碍清单与发现（上报主会话）                                             -/
/- ========================================================================= -/
/-
  F-SMT-2【障碍，已在本文件解除】SMTrace 的 S3 场景（vbranch/join 的 SIMT
    分化-汇合）不可构造的根因 = SM.lean D4/D6 两处 stub。本文件以组合变体
    （V-D0 增量）接通 issueV 的 vALU/SIMT 两端口 + branch_join 真事件 +
    fetch_ctl_buf/Branch_back 双路径回 warp_sche，场景在 60 拍整机轨迹上
    全程判收（smvTrace_ok），且与 BranchJoin 模块级测试 A 同构对照
    （smvT_module_replay）。SM.lean/SMTrace.lean 未改动；若主会话决定把
    变体回合进 SM.lean，增量点即 V-D0 的 (a)-(d) 四处。

  V-O1【残留 stub】vALU 非 SIMT 结果写回链未接：wb 仲裁 in_v、记分板
    wb_v_*、vrf 写口仍 stub（同 SM.lean D4 残余）。vALU 端口对非 simt 指令
    ready=true，结果被静默丢弃（V-D1 已注明）。后果：wvd=1 的向量指令在本
    变体中会"假执行"（记分板/CU 正常回收但寄存器不写）。若后续场景需要
    向量算数指令，须先接 wb_v 链。
  V-O2【残留 stub】issueV 的 LSU/SFU/MUL/TC/vFPU 端口仍 ready=false
    （V-D5）；访存/超越函数向量指令在 DualIssue 处永久阻塞。CSR 执行语义
    仍属 I-SM-1（simtRpc 经 V-D4 环境注入绕过 SETRPC）。
  V-O3【II 类观察】SM.lean smInit 的 bj.tmask := 0#32 与
    branch_join.scala:90 `thread_masks = RegInit(~0.U)` 不符。在 SM.lean
    中因 D6（每拍喂 nop）不可观测，无实际危害；本变体 smvInit 已修正为全 1
    （V-D3）。若 SM.lean 将来启用 bj，须同步修正。
  V-O4【模型边界，非 bug】fetch_ctl_buf/Branch_back 的反压与竞争路径已
    建模（fcV 队列 + in0 优先）但场景未覆盖（colCnt=0、fcBlk=0 已被
    smvTrace_ok 钉死）；多 warp 共享 branch_join 时 input_wid→out_mask 的
    mux（pipe.scala:293,:260）以单实例代替（V-D2），多 warp 场景需 8 实例。
  V-O5【模型边界】branch_join 栈深 4 ≠ 实际 32（沿用 SmState 既定；本场景
    嵌套深度 1）；v0 读出为 rfVV0 全 1 stub（VBEQ/JOIN 的 disableMask=1，
    不读 v0，本场景无影响）。

  I 类审查（本范围逐行对照 pipe.scala:115-129/:232-254/:366/:371-401、
  issue.scala:57-139、branch_join.scala 全体、writeback.scala:14-29、
  warp_schedule.scala:51-52/:73-86/:201-206）：未发现新 I 类 bug。
  契约链 B-I3（complete/fetch_ctl 互补 ⇒ beqReg 当拍必清，Pipe.lean）在
  整机轨迹上生效：拍 6 vbranch takeif 走 complete 路径、拍 16/28/32 三次
  join 走 fetch_ctl 路径，记分板无死锁，warp 顺利推进至 endprg 并全簿记
  回收（finOk）。pipe.scala:390 的 `pc_reconv.valid := issueV.io.out_SIMT
  .valid`（valid 不带 ready、源码附 "todo check this" 注释）经审查无溢出：
  PC_reconv_buf.ready 与 branch_ctl_buf.ready 在 branch/join 两分支恒相等
  （branch_join.scala:123-133），enq 只在消费拍 fire。
-/

/- 公理审计：native_decide 定理带 Lean.ofReduceBool（预期，AGENTS.md 已备案） -/
#print axioms smvT_bj_step_wire
#print axioms smvT_mask_partition
#print axioms smvT_complete_or_fetch
#print axioms smvTrace_ok
#print axioms smvT_module_replay
#print axioms smvT_mask_restore_scene

end Ventus
