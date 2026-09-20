/- ========================================================================= -/
/-                          SMICache.lean                                    -/
/-  SM 组合骨架的真实 ICache 变体：把 SM.lean 的 D1 完美取指 stub 替换为       -/
/-  Mem/ICache.lean 的真实 ICache 模型（miss/MSHR/refill + pc_rsp 重放链），  -/
/-  内存侧接一个简单 L2 stub。                                                -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    pipeline/pipe.scala:133-134（externalFlushPipe = flush|flushCache）、   -/
/-      :153-155（pc_rsp 直通 + status 强制）、:176-187（control/ibuffer      -/
/-      由 icache_rsp 驱动）、:216（icache_rsp.ready = ibuffer.in.ready）、    -/
/-    pipeline/warp_schedule.scala:96-100（probe = pcControl(next_warp)）、   -/
/-      :194-199（pc_rsp miss → PC_src=3 重放）、:75-76（flushCache）、       -/
/-    top/GPGPU_top_nocache.scala:59-81（pipe↔ICache 连线）、:60（invalidate） -/
/-  取指通路外的 SM 组合语义与 SM.lean 完全一致（逐行复刻 smComb/smStep，       -/
/-  仅取指段改写）。                                                          -/
/-                                                                           -/
/- ======================== 理想化与对 Chisel 的偏离（D 区） ================= -/
/-  D-ic1. L2 stub：单 outstanding、固定 1 拍延迟、请求侧空闲即 ready、        -/
/-      响应侧恒被吸收（memRsp_Q 深 2 且单 outstanding ⇒ 不会溢出）。          -/
/-      块内容 = 程序内存函数 prog.imem 的 32 个连续字（128B 块）。非功能      -/
/-      简化：真实 L2/主存有仲裁与多拍延迟；功能侧（数据内容、握手方向）忠实。-/
/-  D-ic2. 取指数据通路忠实（响应 64 位切片译码，pipe.scala:178-180）；但      -/
/-      下流的指令身份重建沿用 SM.lean D2（tag→pc→imem 重取译码）。一致性      -/
/-      前提：L2 stub 供的就是同一 prog.imem ⇒ 两条数据路径同源。             -/
/-  D-ic3. icache invalidate 恒 false（GPGPU_top_nocache.scala:60 接顶层      -/
/-      io.icache_invalidate，本范围无 fence.i）。                             -/
/-  D-ic4. pc_rsp 是 ValidIO（无 ready），icache_rsp.ready 只进 ibuffer 反压  -/
/-      与 status 强制（Q2，Pipe.lean W2 已机证）——本变体两条路径都接。       -/
/-  D-ic5. 继承 SM.lean 的 D2-D8（向量/LSU/CSR stub、branch_join 喂 nop 等）， -/
/-      测试程序同 smTestProg（6 条指令，全在 128B 块 0 内）。                -/
/- ========================================================================= -/

import Ventus.SM
import Ventus.Mem.ICache

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith Ventus.Mem

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. L2 stub（D-ic1）                                                        -/
/- ========================================================================= -/

/-- L2 stub 状态：单 outstanding 在途请求 -/
structure SmicL2 where
  pending : Bool          -- 有在途请求（下一拍应答）
  src     : BitVec 5      -- memReq.a_source（MSHR entry idx，透传回 d_source）
  addr    : BitVec 32     -- 块基址（128B 对齐）

def smicL2Init : SmicL2 := ⟨false, 0#5, 0#32⟩

/-- 块内容装配：字 k = prog.imem(base + 4k)，放在 bit [32k+31 : 32k]
    （对应 ICache 数据通路 icDataSt1 的 blockOffset*32 切片约定） -/
def smicMemBlock (prog : SmProg) (base : BitVec 32) : BitVec 1024 :=
  (List.range 32).foldl (fun acc k =>
    acc ||| ((prog.imem (base + BitVec.ofNat 32 (4 * k))).zeroExtend 1024 <<< (32 * k))) 0#1024

/-- memRsp.d.valid：锁存后下一拍应答（固定 1 拍延迟） -/
def smicL2RspV (l : SmicL2) : Bool := l.pending

/-- memRsp.d.bits（d_source 透传；无在途请求时数据恒 0，不被消费） -/
def smicL2Rsp (prog : SmProg) (l : SmicL2) : IcMemRsp :=
  ⟨l.src, if l.pending then smicMemBlock prog l.addr else 0#1024⟩

/-- memReq.a.ready：单 outstanding ⇒ 空闲才可接受 -/
def smicL2Rdy (l : SmicL2) : Bool := !l.pending

/-- L2 单拍：本拍应答（pending）被 memRsp_Q 吸收（恒吸收，D-ic1）；
    空闲且 memReq fire 时锁存新请求 -/
def smicL2Step (l : SmicL2) (reqFire : Bool) (reqA : BitVec 32) (reqS : BitVec 5) : SmicL2 :=
  if reqFire && !l.pending then ⟨true, reqS, reqA⟩ else ⟨false, 0#5, 0#32⟩

/- ========================================================================= -/
/- 2. 组合状态与输入                                                          -/
/- ========================================================================= -/

/-- SM + ICache + L2 组合状态 -/
structure SmicState where
  sm : SmState
  ic : IcState
  l2 : SmicL2

def smicInit : SmicState := ⟨smInit, icInit, smicL2Init⟩

/-- 一拍的全部组合信号：SM 侧（base，语义同 SmComb）+ 取指/内存侧观测 -/
structure SmicComb where
  base    : SmComb
  reqV    : Bool           -- io.icache_req.fire（coreReq.ready≡true，:262）
  reqWid  : BitVec 3
  reqPC   : BitVec 32      -- probe 地址 = pcControl(next_warp).PC_next
  reqMask : BitVec 2
  rspV    : Bool           -- io.icache_rsp.valid（= fire2 && !ov2）
  rspSt   : BitVec 2       -- 原始 status（ibuffer/control 门控读它，Q2）
  rspStF  : BitVec 2       -- warp_sche 看到的强制 status（pipe.scala:155）
  rspWid  : BitVec 3
  rspAddr : BitVec 32
  memReqV : Bool           -- icache → L2 请求有效
  memReqA : BitVec 32
  memRspV : Bool           -- L2 → icache 响应有效（本拍）
  icIn    : IcIn           -- 本拍 ICache 输入（供 smicStep 消费）

/- ========================================================================= -/
/- 3. 组合层：smicComb（取指段走真实 ICache；其余逐行同 smComb）               -/
/- ========================================================================= -/

def smicComb (prog : SmProg) (s : SmicState) (inp : SmIn) : SmicComb :=
  let sm := s.sm
  -- ---- ibuffer 头控制字重建（SM.lean D2 沿用，D-ic2）与记分板阻塞向量 ----
  let headCtrl : Fin 8 → SmCtrl := fun w =>
    smCtrlOfTag prog (sm.ib.outBits w).tag (sm.ib.outBits w).wid
  let sbBusy : BitVec 8 :=
    pipeScoreboardBusy (fun w => sbDelay (sm.sb w) (smToSbCtrl (headCtrl w)))
  let ibufRdy : BitVec 8 := smPack8 (fun w => sm.ib.ibufRdy w)
  -- ---- DualIssue（operandCollector.scala:629-668）：CU 发射侧 ----
  let cuIssCtrl : Fin 8 → SmCtrl := fun j =>
    smCtrlOfTag prog (cuIssueBits (smCuAt sm j)).control.tag (cuIssueBits (smCuAt sm j)).control.wid
  let reqX : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sm j) && !smInstIsVec (cuIssCtrl j))
  let reqV' : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sm j) && smInstIsVec (cuIssCtrl j))
  let outXV : Bool := rraOutValid (by decide) reqX sm.lgXss
  let outXJ : Fin 8 := rraChoice (by decide) reqX sm.lgXss
  let outXBits : CuIssueBits := cuIssueBits (smCuAt sm outXJ)
  let outXC : SmCtrl := cuIssCtrl outXJ
  let issC : IssCtrl := smToIssCtrl outXC
  -- ---- sALU（execution.scala:28-66）----
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
  -- ---- issueX 端口 ready 表（W11 + SM.lean D4）----
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => true | .ws => !brFire | _ => false
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR])
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brFire
  -- ---- ICache 响应（旧状态 st2 组合读出；GPGPU_top_nocache.scala:70-76）----
  let rspV : Bool := icRspValidOut s.ic
  let rspSt : BitVec 2 := icRspStatus s.ic
  let rspWid : BitVec 3 := icRspWarp s.ic
  let rspAddr : BitVec 32 := icRspAddr s.ic
  let rspData : BitVec 64 := icRspData s.ic
  let rspMask : BitVec 2 := s.ic.mask2          -- coreRsp.bits.mask（:75）
  -- ---- control 模块：响应数据切片译码（pipe.scala:176-185）----
  let rspC0 : SmCtrl := smDecode (rspData.extractLsb' 0 32) rspWid rspAddr
  let rspC1 : SmCtrl := smDecode (rspData.extractLsb' 32 32) rspWid (rspAddr + 4#32)
  let fetchGrp : IbGrp IbInsn :=
    ⟨smToIbInsn rspC0, smToIbInsn rspC1, pipeInstMask rspV rspSt rspMask⟩
  -- ---- icache_rsp.ready = ibuffer.in.ready（:216）与 status 强制（:155，Q2）----
  let ibRdy : Bool := sm.ib.ibufRdy (wsFin rspWid)
  let rspStF : BitVec 2 := pipePcRspStatus ibRdy rspSt
  let rspMissF : Bool := (rspStF &&& 1#2) == 1#2
  -- ---- warp_sche 输入（pc_rsp 接真实响应，:153-155/:75-76）----
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
    , branchFire := brFire, branchJump := brJump, branchWid := brWid
    , pcRspValid := rspV, pcRspMiss := rspMissF, pcRspWid := rspWid
    , pcReset := inp.pcReset }
  let wsO : WsOutputs := wsOut sm.ws wsIn
  -- ---- probe 请求（warp_schedule.scala:96-100；coreReq 恒 ready）----
  let reqV : Bool := wsO.pcReqValid
  let reqWid : BitVec 3 := wsO.pcReqWid
  let reqPC : BitVec 32 := (sm.pcc (wsFin reqWid)).pout
  let reqMask : BitVec 2 := (sm.pcc (wsFin reqWid)).mask
  -- ---- externalFlushPipe（pipe.scala:133-134 → ICache flush）----
  let icFlV : Bool := pipeExtFlushValid wsO.flushValid wsO.flushCacheValid
  let icFlW : BitVec 3 := pipeExtFlushBits wsO.flushValid wsO.flushWid wsO.flushCacheWid
  -- ---- ibuffer 入队（:187 用原始 status，Q2）----
  let ibEnqFire : Bool := pipeIbEnqFire rspV rspSt ibRdy
  -- ---- ibuffer2issue（ibuffer.scala:42-101 + :220-226 的 W5 门控）----
  let warpRdyW : Fin 8 → Bool := fun w =>
    ((wsO.warpReady >>> BitVec.ofNat 8 w.val) &&& 1#8) == 1#8
  let headIsVecW : Fin 8 → Bool := fun w => ibInstIsVec (sm.ib.outBits w)
  let xReq : BitVec 8 := smPack8 (fun w => sm.ib.outV w && warpRdyW w && !headIsVecW w)
  let vReq : BitVec 8 := smPack8 (fun w => sm.ib.outV w && warpRdyW w && headIsVecW w)
  let cuRdy : Fin 8 → Bool := fun j => cuControlRdy (smCuAt sm j)
  let i2iXV : Bool := rraOutValid (by decide) xReq sm.lgXi2i
  let i2iXW : Fin 8 := rraChoice (by decide) xReq sm.lgXi2i
  let i2iXC : SmCtrl := headCtrl i2iXW
  let i2iVV : Bool := rraOutValid (by decide) vReq sm.lgVi2i
  let i2iVW : Fin 8 := rraChoice (by decide) vReq sm.lgVi2i
  let i2iVC : SmCtrl := headCtrl i2iVW
  let dem : OcDemuxRes 8 := ocDemux cuRdy i2iVV i2iXV (smToCuCtrl i2iVC) (smToCuCtrl i2iXC)
  let i2iXFire : Bool := i2iXV && dem.in1Rdy
  let i2iVFire : Bool := i2iVV && dem.in0Rdy
  let i2iXWid : BitVec 3 := BitVec.ofNat 3 i2iXW.val
  let i2iVWid : BitVec 3 := BitVec.ofNat 3 i2iVW.val
  let i2iInRdyW : Fin 8 → Bool := fun w =>
    if headIsVecW w then rraInReady (by decide) vReq sm.lgVi2i dem.in0Rdy w
    else rraInReady (by decide) xReq sm.lgXi2i dem.in1Rdy w
  let ibIn : IbTopIn :=
    { inV := pipeIbInValid rspV rspSt, grp := fetchGrp
    , flushV := wsO.flushValid, flushW := wsO.flushWid
    , outRdy := smPack8 (fun w => pipeIbOutReady (i2iInRdyW w) (warpRdyW w)) }
  -- ---- DualIssue out.ready 与 CU issueReady ----
  let issueXInRdy : Bool := issInReady issC portRdyX
  let ocOutXFire : Bool := outXV && issueXInRdy
  let dualInRdyJ : Fin 8 → Bool := fun j =>
    if smInstIsVec (cuIssCtrl j) then rraInReady (by decide) reqV' sm.lgVss false j
    else rraInReady (by decide) reqX sm.lgXss issueXInRdy j
  -- ---- 写回仲裁（writeback.scala + W12）----
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
  let wbAddr : BitVec 8 := ocWbScaAddr (sm.csr.sgprBase (wsFin wbXWid)) wbXIdxw
  let wbWrEn : Bool := wbXFire && wbXWxd && (wbXIdxw != 0#8)
  -- ---- crossbar 输入 ----
  let xin : OcXbarIn :=
    { chosenS := smChSAt sm, chosenV := smChVAt sm
    , validS := smChSvAt sm, validV := smChVvAt sm
    , dataS := fun i => rfSOut (smSrfAt sm i), dataV := fun i => rfVOut (smVrfAt sm i)
    , dataV0 := fun _ => rfVV0 }
  -- ---- CU 输入 ----
  let cuIn : Fin 8 → CuInputs := fun j =>
    { controlValid := dem.valid j, ctrl := dem.bits j
    , bv0 := (ocXbar xin j.val 0).valid, bv1 := (ocXbar xin j.val 1).valid
    , bv2 := (ocXbar xin j.val 2).valid, bv3 := (ocXbar xin j.val 3).valid
    , bb0 := ⟨(ocXbar xin j.val 0).regOrder, (ocXbar xin j.val 0).data, (ocXbar xin j.val 0).v0⟩
    , bb1 := ⟨(ocXbar xin j.val 1).regOrder, (ocXbar xin j.val 1).data, (ocXbar xin j.val 1).v0⟩
    , bb2 := ⟨(ocXbar xin j.val 2).regOrder, (ocXbar xin j.val 2).data, (ocXbar xin j.val 2).v0⟩
    , bb3 := ⟨(ocXbar xin j.val 3).regOrder, (ocXbar xin j.val 3).data, (ocXbar xin j.val 3).v0⟩
    , issueReady := dualInRdyJ j
    , sgprBase := sm.csr.sgprBase, vgprBase := sm.csr.vgprBase }
  -- ---- bank 读仲裁 ----
  let reqs : Fin 32 → CuArbReq := fun p =>
    cuOutArbBits (smCuAt sm ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let rv : Fin 32 → Bool := fun p =>
    cuOutArbValidK (smCuAt sm ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let bankAddrS : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocScaChoice reqs rv i (smLgSAt sm i))).rsAddr
  let bankAddrV : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocVecChoice reqs rv i (smLgVAt sm i))).rsAddr
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
  -- ---- PCcontrol 驱动（warp_schedule.scala:96-100,:194-220；
  --      程序序即优先级：pc_reset > dispatch > branch > miss 重放 > 调度推进） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.reqFire && (inp.reqWid == w3) then ⟨inp.reqPC, false, 1#2, 0#2⟩
    else if brFire && brJump && (brWid == w3) then ⟨brTarget, false, 1#2, 0#2⟩
    else if rspV && rspMissF && (rspWid == w3) then ⟨rspAddr, false, 3#2, rspMask⟩
    else if reqV && (reqWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入 ----
  let rfInS : Fin 4 → RfSInputs := fun i =>
    ⟨bankAddrS i, wbAddr, wbXData, wbWrEn && (wbBank == BitVec.ofNat 2 i.val)⟩
  let rfInV : Fin 4 → RfVInputs := fun i =>
    ⟨bankAddrV i, 0#8, cuRow0, false, fun _ => false⟩
  -- ---- RR 仲裁器 lastGrant 更新 ----
  let bankLgS' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocScaPack reqs rv i) true (smLgSAt sm i)
  let bankLgV' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocVecPack reqs rv i) true (smLgVAt sm i)
  -- ---- ICache 本拍输入（GPGPU_top_nocache.scala:60-81 + L2 stub）----
  let icIn : IcIn :=
    { reqValid := reqV, reqAddr := reqPC, reqMask := reqMask, reqWarp := reqWid
    , flushValid := icFlV, flushWarp := icFlW
    , rspValid := smicL2RspV s.l2, rspBits := smicL2Rsp prog s.l2
    , memReady := smicL2Rdy s.l2, invalidate := false }
  { base :=
    { wsIn := wsIn, wsO := wsO
    , fetchV := rspV, fetchWid := rspWid, fetchGrp := fetchGrp, ibEnqFire := ibEnqFire
    , ibIn := ibIn
    , i2iXFire := i2iXFire, i2iVFire := i2iVFire, i2iXWid := i2iXWid, i2iVWid := i2iVWid
    , outXV := outXV, outXWid := outXBits.control.wid, ocOutXFire := ocOutXFire
    , fireSAlu := fireSAlu, fireCsr := fireCsr, fireWs := fireWs
    , aluOut := aluRes.1, aluCmp := aluRes.2
    , brFire := brFire, brJump := brJump, brWid := brWid, brTarget := brTarget
    , wbXFire := wbXFire, wbXWid := wbXWid, wbXIdxw := wbXIdxw, wbXWxd := wbXWxd
    , wbXData := wbXData
    , pccIn := pccIn, sbIn := sbIn, cuIn := cuIn, rfInS := rfInS, rfInV := rfInV
    , lgXi2i := rraStep (by decide) xReq dem.in1Rdy sm.lgXi2i
    , lgVi2i := rraStep (by decide) vReq dem.in0Rdy sm.lgVi2i
    , lgXss := rraStep (by decide) reqX issueXInRdy sm.lgXss
    , lgVss := rraStep (by decide) reqV' false sm.lgVss
    , bankLgS := bankLgS', bankLgV := bankLgV'
    , chosenS := fun i => BitVec.ofNat 5 (ocScaChoice reqs rv i (smLgSAt sm i)).val
    , chosenV := fun i => BitVec.ofNat 5 (ocVecChoice reqs rv i (smLgVAt sm i)).val
    , chosenSv := fun i => ocScaOutValid reqs rv i (smLgSAt sm i)
    , chosenVv := fun i => ocVecOutValid reqs rv i (smLgVAt sm i) }
  , reqV := reqV, reqWid := reqWid, reqPC := reqPC, reqMask := reqMask
  , rspV := rspV, rspSt := rspSt, rspStF := rspStF, rspWid := rspWid, rspAddr := rspAddr
  , memReqV := icMemReqValid s.ic, memReqA := icMemReqAddr s.ic
  , memRspV := smicL2RspV s.l2
  , icIn := icIn }

/- ========================================================================= -/
/- 4. 单拍 step 与多拍 run                                                    -/
/- ========================================================================= -/

/-- ICache 状态 reify：原为 IcMshrState 函数字段的每拍具体化（防闭包扇出
    爆炸）。第 20 波起 ICache.lean 已在源头 Array 化（IcMshrState 四字段 +
    wayValid + rspQ.mem，闭包扇出根治），物化职责内化进 icMshrStep，
    本函数退化为恒等（保留调用点不动）。 -/
def smicIcReify (ic : IcState) : IcState := ic

/-- 组合单拍：SM 部分按 smicComb 连线同步更新（字段更新同 smStep），
    ICache 走 icStep，L2 stub 消费 memReq（fire = valid && ready 双侧一致）。

    reify 注记（AGENTS.md"每拍 reifyState 具体化"）：SmState 的 pcc/sb/ib 是
    函数字段，`fun w => f (s.x w) ...` 闭包逐拍嵌套后，跨拍经 outRdy→xReq→
    outV 等链路重入形成扇出重算（实测 11 拍 66s、12 拍 >280s）。此处每拍先
    把 8 个 warp 的新值装入 Array、再包成查表闭包——逐点语义与 smStep 相同
    （界内查表 = 原式），但每 warp 每拍至多求值一次，斩断跨拍重入链。 -/
def smicStep (prog : SmProg) (s : SmicState) (inp : SmIn) : SmicState :=
  let c := smicComb prog s inp
  let sm := s.sm
  let pccArr := ((List.finRange 8).map fun w => pccStep (sm.pcc w) (c.base.pccIn w)).toArray
  let sbArr  := ((List.finRange 8).map fun w => sbStep (sm.sb w) (c.base.sbIn w)).toArray
  let ibArr  := ((List.finRange 8).map fun w =>
    (sm.ib.lanes w).step (ibTopLaneIn c.base.ibIn w)).toArray
  { sm :=
    { ws := wsStep sm.ws c.base.wsIn
    , pcc := fun w => smArrAt pccArr w.val (pccInit 0#2)
    , ib := ⟨fun w => smArrAt ibArr w.val IbLane.empty⟩
    , sb := fun w => smArrAt sbArr w.val sbInit
    , cu := ((List.finRange 8).map fun j => cuStep (smCuAt sm j) (c.base.cuIn j)).toArray
    , lgXi2i := c.base.lgXi2i, lgVi2i := c.base.lgVi2i
    , lgXss := c.base.lgXss, lgVss := c.base.lgVss
    , bankLgS := ((List.finRange 4).map c.base.bankLgS).toArray
    , bankLgV := ((List.finRange 4).map c.base.bankLgV).toArray
    , chosenS := ((List.finRange 4).map c.base.chosenS).toArray
    , chosenV := ((List.finRange 4).map c.base.chosenV).toArray
    , chosenSv := ((List.finRange 4).map c.base.chosenSv).toArray
    , chosenVv := ((List.finRange 4).map c.base.chosenVv).toArray
    , srf := ((List.finRange 4).map fun i => rfSStep (smSrfAt sm i) (c.base.rfInS i)).toArray
    , vrf := ((List.finRange 4).map fun i => rfVStep (smVrfAt sm i) (c.base.rfInV i)).toArray
    , csr := if inp.reqFire then
        { sm.csr with
          sgprBase := fun w => if w == wsFin inp.reqWid then inp.reqSgpr else sm.csr.sgprBase w
        , vgprBase := fun w => if w == wsFin inp.reqWid then inp.reqVgpr else sm.csr.vgprBase w }
      else sm.csr
    , bj := (bjSysStep sm.bj BjEvent.nop).1 }
  , ic := smicIcReify (icStep s.ic c.icIn)
  , l2 := smicL2Step s.l2 (icMemReqValid s.ic && smicL2Rdy s.l2)
      (icMemReqAddr s.ic) (icMemReqSource s.ic) }

/-- 多拍运行 -/
def smicRun (prog : SmProg) (s : SmicState) (ins : List SmIn) : SmicState :=
  ins.foldl (smicStep prog) s

/- ========================================================================= -/
/- 5. 轨迹观测与测试（native_decide；公理审计多 Lean.ofReduceBool）            -/
/- ========================================================================= -/

-- ---- 5.1 轨迹访问器与观测谓词 ----

section SmicTests

/-- 拍 n 的状态 -/
def smicSAt (n : Nat) : SmicState := smicRun smTestProg smicInit (smTestIns.take n)

/-- 拍 n 的组合观测 -/
def smicCAt (n : Nat) : SmicComb :=
  smicComb smTestProg (smicSAt n) (smTestIns.getD n smInNop)

/-- 第二趟输入：k=45 再次派发 warp0（wg0/wf1/pc=0）。第一趟结束后块 0 已在
    ICache 中 ⇒ 第二趟是全命中轨迹（暖缓存 ≡ 完美取指的理想情形） -/
def smicIns2 : List SmIn :=
  smTestIns ++ smInDispatch 0#3 0#3 1#4 0#32 0#12 0#11 :: List.replicate 25 smInNop

/-- 第二趟的拍 n 状态/组合观测 -/
def smicSAt2 (n : Nat) : SmicState := smicRun smTestProg smicInit (smicIns2.take n)
def smicCAt2 (n : Nat) : SmicComb :=
  smicComb smTestProg (smicSAt2 n) (smicIns2.getD n smInNop)

/-- 写回事件流（有效且 wxd 的 wb.out_x 拍，取 (idxw, data)）：完美取指版 -/
def smWbEv (n : Nat) : List (BitVec 8 × BitVec 32) :=
  (List.range n).filterMap fun k =>
    let c := smCAt k
    if c.wbXFire && c.wbXWxd then some (c.wbXIdxw, c.wbXData) else none

/-- 写回事件流：真实 ICache 版（第一趟，含 miss） -/
def smicWbEv (n : Nat) : List (BitVec 8 × BitVec 32) :=
  (List.range n).filterMap fun k =>
    let c := (smicCAt k).base
    if c.wbXFire && c.wbXWxd then some (c.wbXIdxw, c.wbXData) else none

/-- 写回事件流：真实 ICache 版（区间 [lo, hi)，供第二趟用） -/
def smicWbEv2 (lo hi : Nat) : List (BitVec 8 × BitVec 32) :=
  (List.range' lo (hi - lo)).filterMap fun k =>
    let c := (smicCAt2 k).base
    if c.wbXFire && c.wbXWxd then some (c.wbXIdxw, c.wbXData) else none

/-- 本拍是 ICache 原始 miss 响应（raw status(0)=1，缓存侧未命中） -/
def smicRspRawMiss (c : SmicComb) : Bool := c.rspV && (c.rspSt &&& 1#2 == 1#2)

/-- 本拍 warp_sche 视角的 miss（强制 status(0)=1；含 Q2 的 ibuf 满强制） -/
def smicRspMiss (c : SmicComb) : Bool := c.rspV && (c.rspStF &&& 1#2 == 1#2)

-- ---- 5.2 miss 轨迹（第一趟，冷缓存） ----

/-- T1 首个响应即 miss：拍 3 对 warp0@pc0 回 status=01，ibuffer 不入队，
    且同拍 PCcontrol 走 PC_src=3 重放回填（warp_schedule.scala:194-198；
    New_PC=响应地址 0、mask_i=响应掩码 0b11） -/
theorem smicT1_first_miss_replay :
    (smicCAt 3).rspV = true ∧ (smicCAt 3).rspSt = 1#2 ∧
    (smicCAt 3).base.ibEnqFire = false ∧
    (smicCAt 3).base.pccIn 0 = ⟨0#32, false, 3#2, 3#2⟩ := by
  native_decide

/-- T2 取指停顿：完美取指版拍 1 即入队（SM.lean smT1），真实版前 8 拍
    无任何入队——miss/refill/重放的取指延迟 = 8 拍 -/
theorem smicT2_fetch_stall :
    ((List.range 9).all fun k => !(smicCAt k).base.ibEnqFire) = true ∧
    (smCAt 1).ibEnqFire = true := by
  native_decide

/-- T3 refill 与重试 probe 碰撞 → I-23 假 miss 在整机轨迹浮现：
    拍 4 L2 数据到达（memRspV，refill 与 pc0 的重试 probe 同拍碰撞）；
    拍 6 该 probe 的响应 status=11（假 miss | MSHR busy 阻塞）——块已填入
    仍判 miss；同拍再次 PC_src=3 重放 pc0。整机经重放链自愈。 -/
theorem smicT3_false_miss_replay :
    (smicCAt 4).memRspV = true ∧
    (smicCAt 6).rspV = true ∧ (smicCAt 6).rspSt = 3#2 ∧
    (smicCAt 6).rspAddr = 0#32 ∧ (smicCAt 6).rspWid = 0#3 ∧
    (smicCAt 6).base.pccIn 0 = ⟨0#32, false, 3#2, 3#2⟩ := by
  native_decide

/-- T3b 假 miss 未造成重复取块：全程 memReq 只发一次（拍 3）——
    假 miss 被 MSHR busy 反压挡住（status=11 而非 01，无重复分配） -/
theorem smicT3b_no_duplicate_memreq :
    ((List.range 45).filter fun k => (smicCAt k).memReqV) = [3] := by
  native_decide

/-- T4 refill 后命中、取指恢复：拍 9 首个命中响应（status=00）且入队；
    拍 10 末 warp0 的 ibuffer 持有 [tag0, tag1]（= pc0/pc4 两条 addi） -/
theorem smicT4_hit_enq :
    (smicCAt 9).rspV = true ∧ (smicCAt 9).rspSt = 0#2 ∧
    (smicCAt 9).base.ibEnqFire = true ∧
    ((smicSAt 10).sm.ib.lanes 0).absTags = [0#8, 1#8] := by
  native_decide

/-- T5 精化（具体程序上的写回流一致）：真实 ICache 版（含 miss/重放/
    假 miss）与完美取指版在同一程序下写回事件序列逐项相等，且内容 =
    x1:=1, x2:=3, x4:=4（beq 跳过 x3，endprg 不写回）。 -/
theorem smicT5_wb_refine :
    smicWbEv 45 = smWbEv 45 ∧
    smWbEv 45 = [(1#8, 1#32), (2#8, 3#32), (4#8, 4#32)] := by
  native_decide

/-- T6 程序终止：拍 45 时 warp0 已 endprg 退出（warp_active 清空） -/
theorem smicT6_endprg : (smicSAt 45).sm.ws.warpActive = 0#8 := by
  native_decide

-- ---- 5.3 全命中轨迹（第二趟，暖缓存） ----

/-- T7 全命中（缓存侧）：第二趟（拍 45 起）无任何**原始** miss 响应；
    命中取指延迟 = probe→enq 2 拍（拍 46 首发 probe、拍 48 入队，
    st1+st2 两级流水，对比完美版的 0 拍与冷缓存首取的 8 拍） -/
theorem smicT7_all_hit :
    ((List.range' 45 26).all fun k => !smicRspRawMiss (smicCAt2 k)) = true ∧
    ((List.range' 45 3).all fun k => !(smicCAt2 k).base.ibEnqFire) = true ∧
    (smicCAt2 48).base.ibEnqFire = true := by
  native_decide

/-- T7b Q2 status 强制路径的整机见证（pipe.scala:155）：拍 51 ibuffer 满，
    命中响应（raw status=00）被强制为 miss（warp_sche 视角 status=01），
    不入队并重放 pc=0x18；指令不丢——拍 57 该组重新入队（rspAddr=0x18）。
    （第一趟拍 12 同样激发一次。） -/
theorem smicT7b_q2_forced_replay :
    (smicCAt2 51).rspV = true ∧ (smicCAt2 51).rspSt = 0#2 ∧
    (smicCAt2 51).rspStF = 1#2 ∧ (smicCAt2 51).base.ibEnqFire = false ∧
    (smicCAt2 57).base.ibEnqFire = true ∧ (smicCAt2 57).rspAddr = 0x18#32 := by
  native_decide

/-- T8 暖缓存 ≡ 完美取指（写回流）：第二趟的写回事件 = 第一趟 = 完美版
    （含 Q2 强制重放在内的全套真实机制下，最终写回仍一致） -/
theorem smicT8_warm_refine :
    smicWbEv2 45 71 = [(1#8, 1#32), (2#8, 3#32), (4#8, 4#32)] := by
  native_decide

end SmicTests

/- 公理审计：native_decide 测试定理带 Lean.ofReduceBool（其余为 Lean 标准公理） -/
#print axioms smicT1_first_miss_replay
#print axioms smicT2_fetch_stall
#print axioms smicT3_false_miss_replay
#print axioms smicT3b_no_duplicate_memreq
#print axioms smicT4_hit_enq
#print axioms smicT5_wb_refine
#print axioms smicT6_endprg
#print axioms smicT7_all_hit
#print axioms smicT7b_q2_forced_replay
#print axioms smicT8_warm_refine

end Ventus
