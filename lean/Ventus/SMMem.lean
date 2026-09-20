/- ========================================================================= -/
/-                          SMMem.lean                                       -/
/-  SM 组合模型（向量写回版 SMVecWb）的访存通路升级：LSU + ShareMem + MSHR +    -/
/-  LSU2WB 真模型接入，消除 SMVecWb.lean 的 W-O2/SM 系列障碍 I-SM-4            -/
/-  （"LSU 端口堵死，访存指令不可发射"）。                                      -/
/-                                                                           -/
/-  真实链路（逐行对照）：                                                     -/
/-    pipe.scala:376        issueV.io.out_LSU <> lsu.io.lsu_req（LSU 在 V 侧）  -/
/-    pipe.scala:377        issueX.io.out_LSU.ready := false.B（X 侧恒堵，      -/
/-      标量访存指令若到 issueX 将永久卡死——忠实保留，见 M-O5）；               -/
/-    LSU.scala:551         InputFIFO = Queue(vExeData,1,pipe=true)；           -/
/-    LSU.scala:572-579     ShiftBoard×8：lsu_req 的 full 门控 + fence_end；    -/
/-    LSU.scala:113-489     AddrCalculate（= Mem/LSU.lean 的 LsuState/lsuStep， -/
/-      smax = sharemem_size = 0x20000，pipe 例化 LSU.scala:548/554）；          -/
/-    pipe.scala:414        lsu.io.shared_req <> io.shared_req（→ ShareMem）；  -/
/-    GPGPU_top.scala:488   setIdx 8→10 零扩展（**I-21 断点**：addr(16,15) 丢） -/
/-    Mem/ShareMem.lean     SharedMemory（SmState/smStep，sm 前缀）；            -/
/-    LSU.scala:560-563     rspArbiter = Arbiter(DCacheCoreRsp_np,2)：           -/
/-      in(0)=dcache_rsp（本变体 stub 恒 invalid，M-O2）、in(1)=shared_rsp；     -/
/-    LSU.scala:565         Coalscer = MSHRv2（Mem/MSHR.lean，mshr 前缀）；     -/
/-    pipe.scala:412        lsu.io.lsu_rsp <> lsu2wb.io.lsu_rsp；               -/
/-    LSU.scala:490-529     LSU2WB 组合桥（wxd→out_x / wfd→out_v / isWrite→自消） -/
/-    pipe.scala:418,424    wb.io.in_x(2)/in_v(2) <> lsu2wb.out_x/out_v；        -/
/-    pipe.scala:271        scoreb(wid).wb_v_fire = wb.out_v.fire（LSU load 的   -/
/-      busy 清除走与 vALU 相同的写回链）；                                     -/
/-    pipe.scala:241        scoreb(i).fence_end := lsu.io.fence_end(i)（本文件   -/
/-      从 false stub 升级为 ShiftBoard 真空值）。                              -/
/-                                                                           -/
/- ======================== 建模决策（对 SMVecWb.lean 的增量，M-D 区） ======== -/
/-  M-D0. smmComb 是 SMVecWb.lean smwComb 的全量复制 + 下列增量点（SMVecWb.lean -/
/-      只读；复制-增量纪律同 W-D0/V-D0）：                                     -/
/-      (a) portRdyV 增加 `.LSU => lsuReqRdyT`（LSU.scala:578-579 的            -/
/-          ShiftBoard full 门控 + InputFIFO enq.ready）；portRdyX 的 .LSU 仍   -/
/-          落 `_ => false`（pipe.scala:377，忠实）；                           -/
/-      (b) 新增 LSU 顶层装配状态：InputFIFO（1 项 pipe 队列）+ ShiftBoard×8 +  -/
/-          AddrCalculate(LsuState) + ShareMem(SmState) + MSHRv2(MshrState)，   -/
/-          见 SmmState；                                                       -/
/-      (c) wb 仲裁 in_x(2)/in_v(2) 接 LSU2WB 真值（pipe.scala:418/:424）；     -/
/-      (d) 记分板 fence_end 接 lsu.io.fence_end(i)（pipe.scala:241）；         -/
/-      (e) wsIn.flushDCacheReady 从环境输入改接 lsuFlushRdy（pipe.scala:171，  -/
/-          flush_dcache.ready = AddrCalculate s_idle）；LsuIn.flushValid 接    -/
/-          wsO.flushDCacheValid（pipe.scala:169；wsOut 该字段只读状态——        -/
/-          WarpScheduler.lean:370，提前计算破组合环，定理 smmT_flushV_wire     -/
/-          钉死与 wsO 一致）。                                                 -/
/-  M-D1. InputFIFO（Queue(1,pipe=true)）：deq.valid = full || enq.valid；      -/
/-      deq.bits = full ? 寄存 : enq.bits；enq.ready = !full || deq.ready；     -/
/-      maybe_full 仅当 do_enq≠do_deq 时更新为 do_enq。                         -/
/-  M-D2. lsu_req.fire = issueV out_LSU.fire = ocOutVFire && route==[.LSU]，    -/
/-      与 InputFIFO enq.fire 同值（门控同一信号展开）；监控器逐拍断言二者       -/
/-      一致（mismFire 计数器钉死，见第 6 节）。                                -/
/-  M-D3. csr_tid/csr_pds/csr_numw 恒 0：SmCsrView 无 lsu_* 字段（SM.lean D5    -/
/-      只读视图未覆盖）。这三个输入仅参与 vls12 形地址（LSU.scala:150）；       -/
/-      unit-stride/gather/strided 路径不引用 ⇒ 本文件场景（VLE32/VSE32）       -/
/-      不受影响；VLS12/VSS12 寻址不忠实，列边界 M-O4。csr_wid 输出             -/
/-      （LSU.scala:134）的 CSR 回读环不建模。                                  -/
/-  M-D4. DCache/L2 保持 stub：dcache_req.ready 恒 true（flush 能完成），       -/
/-      dcache_rsp 恒 invalid（LSU.scala:560 的 in(0)）⇒ rspArbiter 恒选        -/
/-      in(1)=shared_rsp；shared_rsp.ready = MSHR from_dcache.ready =           -/
/-      state.isIdle（MSHR.scala:45）。global（非 LDS）地址的请求被接受但       -/
/-      永无响应 ⇒ MSHR 条目悬挂——场景只走 LDS，列边界 M-O2。                  -/
/-  M-D5. MSHR tag 的 mask 在 LSU 侧是 Fin 32 → Bool（Mem/LSU.lean D13）、      -/
/-      在 MSHR 侧是 BitVec 32（Mem/MSHR.lean :103）；smmPackMask/解包桥接，     -/
/-      全 1 掩码往返一致由轨迹判收覆盖（场景全掩码）。                          -/
/- ========================================================================= -/

import Ventus.SMVecWb
import Ventus.Mem.LSU
import Ventus.Mem.ShareMem
import Ventus.Mem.MSHR

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 变体状态与类型桥接                                                       -/
/- =========================================================================-/

/-- SM 访存变体状态：SmvState（smwComb 底座）+ LSU 顶层装配 + ShareMem + MSHR。
    （M-D0b；InputFIFO 为 1 项 pipe 队列 ⇒ full+bits 两字段） -/
structure SmmState where
  base     : SmvState                 -- smwComb 底座（SM+SIMT+wb_v 全通）
  fifoFull : Bool                     -- InputFIFO maybe_full（LSU.scala:551）
  fifoBits : Mem.LsuVExe              -- InputFIFO ram
  boards   : BitVec 3 → BitVec 4      -- ShiftBoard×8 taps（LSU.scala:572-576）
  lsu      : Mem.LsuState             -- AddrCalculate（:113-489）
  shm      : Mem.SmState              -- SharedMemory（ShareMem.scala:55-195）
  mshr     : Mem.MshrState            -- MSHRv2（MSHR.scala:31-108）

/-- 初始状态：底座全初值 + 访存子系统全初值 -/
def smmInitOf (v : SmvState) : SmmState :=
  { base := v, fifoFull := false, fifoBits := Mem.lsuVExe0
  , boards := fun _ => 0#4, lsu := Mem.lsuInit, shm := Mem.smInit, mshr := Mem.mshrInit }

/-- 逐 lane 掩码打包（LSU 侧 Fin 32 → Bool ⇒ MSHR 侧 BitVec 32，M-D5） -/
def smmPackMask (m : Fin 32 → Bool) : BitVec 32 :=
  (List.finRange 32).foldl
    (fun acc l => if m l then acc ||| (1#32 <<< (BitVec.ofNat 32 l.val)) else acc) 0#32

/-- SmCtrl（译码控制字）→ LsuCtrl 切片（Mem/LSU.lean D3 的 16 字段；
    mop/aq/rl/is_vls12 取自 DecodeUnit 的派生函数） -/
def smmLsuCtrlOf (c : SmCtrl) : Mem.LsuCtrl :=
  { wid          := c.wid
  , reg_idxw     := c.regIdxw
  , mem_cmd      := c.row.memCmd
  , mop          := decMop c.row.readmask c.inst          -- DecodeUnit.scala:578
  , mem_whb      := c.row.memWhb
  , alu_fn       := c.row.aluFn
  , isvec        := c.row.isvec
  , disable_mask := c.row.disableMask
  , is_vls12     := decIsVls12 c.row.aluFn                -- :595
  , mem_unsigned := c.row.memUnsigned
  , atomic       := c.row.atomic
  , aq           := decAq c.row.atomic c.inst             -- :626
  , rl           := decRl c.row.atomic c.inst             -- :627
  , fence        := c.row.fence
  , wxd          := c.row.wxd
  , wvd          := c.row.wvd }

/-- issueV out_LSU.bits = exe_dataV（pipe.scala:360-366 → issue.scala:66：
    out_LSU.bits := inputBuf.bits） -/
def smmLsuReqBits (c : SmCtrl) (bits : CuIssueBits) (mask : BitVec 32) : Mem.LsuVExe :=
  { in1 := bits.alu_src1, in2 := bits.alu_src2, in3 := bits.alu_src3
  , mask := fun t => mask.getLsbD t.val
  , ctrl := smmLsuCtrlOf c }

/-- LSU to_shared.bits → ShareMem coreReq.bits（pipe.scala:414 →
    GPGPU_top.scala:488：**setIdx 8→10 零扩展，I-21 断点**） -/
def smmShReqOf (r : Mem.LsuSharedReq) : Mem.SmCoreReq :=
  { instrId := r.instrId
  , isWrite := r.isWrite
  , setIdx  := r.setIdx.zeroExtend 10
  , perLaneAddr := fun l => ⟨r.active l, r.blkOff l, r.word1H l⟩
  , data    := r.data }

/-- AddrCalculate to_mshr tag → MSHRv2 tag（mask 打包，M-D5） -/
def smmMshrTagOf (t : Mem.LsuMshrTag) : Mem.MshrTag :=
  ⟨t.warp_id, t.wfd, t.wxd, t.reg_idxw, smmPackMask t.mask, t.unsigned, t.isvec,
   t.wordOffset1H, t.isWrite⟩

/-- MSHRv2 输出 tag → LSU2WB 侧 tag（mask 解包，M-D5） -/
def smmWbTagOf (t : Mem.MshrTag) : Mem.LsuMshrTag :=
  ⟨t.warp_id, t.wfd, t.wxd, t.reg_idxw, (fun l => t.mask.getLsbD l.val),
   t.unsigned, t.isvec, t.wordOffset1H, t.isWrite⟩

/- ========================================================================= -/
/- 2. 组合层：smmComb = smwComb + M-D0 增量                                     -/
/- =========================================================================-/

/-- 一拍的全部组合信号（SmwComb 全字段 + 访存链字段） -/
structure SmmComb where
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
  -- ---- W-D0b 继承的 wb_v 写回链（仲裁后值，LSU 源已并入） ----
  exeMaskV   : BitVec 32
  wbVValid   : Bool              -- vALU 源 valid（execution.scala:560）
  wbVChoice  : Fin 6
  wbVFire    : Bool
  wbVWid     : BitVec 3
  wbVIdxw    : BitVec 8
  wbVWvd     : Bool
  wbVData    : RfVRow            -- vALU 逐 lane 结果
  wbVOutData : RfVRow            -- 仲裁输出（含 LSU 源）
  wbVMaskFn  : RfVMask
  wbVBank    : BitVec 2
  wbVAddr    : BitVec 8
  wbVWen     : Bool
  wbXValids  : BitVec 6          -- M-D0c：含 in_x(2)=lsu2wb
  wbVValids  : BitVec 6          -- M-D0c：含 in_v(2)=lsu2wb
  wbXChoice  : Fin 6
  -- ---- M-D0 增量：访存链 ----
  wsFlushDV    : Bool            -- warp_sche flushDCache.valid（WarpScheduler.lean:370）
  lsuReqV      : Bool            -- issueV out_LSU.valid（issue.scala:114-117）
  lsuReqWid    : BitVec 3        -- lsu_req.bits.ctrl.wid
  lsuReqBits   : Mem.LsuVExe     -- lsu_req.bits
  lsuReqRdyT   : Bool            -- lsu_req.ready（LSU.scala:578）
  fireLsu      : Bool            -- lsu_req.fire（= out_LSU.fire）
  fifoEnqValid : Bool            -- InputFIFO enq.valid（:579 门控后）
  fifoEnqRdy   : Bool            -- InputFIFO enq.ready（pipe 队列）
  fifoEnqFire  : Bool
  fifoDeqValid : Bool            -- from_fifo.valid
  fifoDeqBits  : Mem.LsuVExe     -- from_fifo.bits
  fifoDeqFire  : Bool            -- AddrCalculate 接受（:295）
  lsuIn        : Mem.LsuIn
  lsuOut       : Mem.LsuOut
  lsuShFire    : Bool            -- to_shared.fire（LSU.scala:313）
  shIn         : Mem.SmIn        -- ShareMem coreReq/coreRsp.ready
  shRspV       : Bool            -- shared_rsp.valid（= rspArbiter out.valid，M-D4）
  mshrIn       : Mem.MshrIn
  mshrDcF      : Bool            -- MSHR from_dcache.fire
  rspValid     : Bool            -- lsu_rsp.valid（MSHR to_pipe.valid，:106）
  rspTag       : Mem.LsuMshrTag  -- lsu_rsp.bits.tag
  rspData      : Mem.LsuRow      -- lsu_rsp.bits.data
  rspWid       : BitVec 3
  lsuWbXV      : Bool            -- LSU2WB out_x.valid（LSU.scala:509-511）
  lsuWbVV      : Bool            -- LSU2WB out_v.valid（:513-515）
  lsuRspRdy    : Bool            -- lsu_rsp.ready（:516-520）
  lsuRspFire   : Bool            -- lsu_rsp.fire（ShiftBoard right，:575）

/-- 组合求值（逐段对应 SMVecWb.lean smwComb，差异处标 M-D0）。 -/
def smmComb (prog : SmProg) (s : SmmState) (inp : SmIn) : SmmComb :=
  let sb0 := s.base.base
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
  -- ---- vALU 等宽 + branch_join 事件 + fetch_ctl_buf（同 smwComb） ----
  let cmpV : BitVec 32 :=
    smvCmpVec outVC.row.aluFn outVC.row.reverse
      outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let bi : BjBranchIn 32 :=
    { valuMask := exvIfMask cmpV
    , maskInit := smvMaskInit outVBits.vmask sb0.bj.tmask
    , PCbranch := outVBits.alu_src3 ⟨0, by decide⟩
    , PCexecute := outVC.pc
    , PCreconv := sb0.csr.simtRpc }
  let fcEnqRdy : Bool := !s.base.fcV || !brFire
  -- ---- M-D0e：flushDCache.valid 提前算（wsOut 该字段只读状态，
  --      WarpScheduler.lean:370；破 portRdyV → lsuIn → wsO 文本环） ----
  let wsFlushDV : Bool := wsMask0 sb0.ws.endprgCnt sb0.ws.wgValid != 0#8
  -- ---- M-D0a/M-D0b：LSU 顶层装配（LSU.scala:551-579） ----
  let exeMaskV : BitVec 32 := smvMaskInit outVBits.vmask sb0.bj.tmask   -- pipe.scala:366
  let lsuReqBits : Mem.LsuVExe := smmLsuReqBits outVC outVBits exeMaskV
  let lsuReqWid : BitVec 3 := outVBits.control.wid
  let lsuReqV : Bool := outVV && (issRoute issV == [.LSU])              -- issue.scala:114-117
  let fifoDeqRdy : Bool := (s.lsu.state == Mem.lsuSIdle) && !wsFlushDV  -- from_fifo.ready（:136）
  let fifoEnqRdy : Bool := !s.fifoFull || fifoDeqRdy                    -- Queue(1,pipe) enq.ready
  let lsuReqRdyT : Bool := Mem.lsuReqReady s.boards lsuReqWid fifoEnqRdy  -- :578
  let portRdyV : IssPort → Bool := fun p => match p with
    | .vALU => if outVC.row.simtStack then fcEnqRdy else true
    | .SIMT => fcEnqRdy
    -- M-D0a：LSU 端口 ready = lsu_req.ready（pipe.scala:376 → issue.scala:117）
    | .LSU => lsuReqRdyT
    | _ => false
  let issueVInRdy : Bool := issInReady issV portRdyV
  let ocOutVFire : Bool := outVV && issueVInRdy
  let isVBr : Bool := issRoute issV == [.vALU, .SIMT]
  let isJoin : Bool := issRoute issV == [.SIMT]
  let fireVAlu : Bool := ocOutVFire && ((issRoute issV).any (fun t => decide (t = .vALU)))
  let fireSimt : Bool := ocOutVFire && (isVBr || isJoin)
  -- M-D2：lsu_req.fire（issue 侧与 InputFIFO enq 同一握手）
  let fireLsu : Bool := ocOutVFire && (issRoute issV == [.LSU])
  let fifoEnqValid : Bool := Mem.lsuReqValidGated s.boards lsuReqWid lsuReqV  -- :579
  let fifoEnqFire : Bool := fifoEnqValid && fifoEnqRdy
  let fifoDeqValid : Bool := s.fifoFull || fifoEnqValid                       -- pipe 直通
  let fifoDeqBits : Mem.LsuVExe := if s.fifoFull then s.fifoBits else lsuReqBits
  let fifoDeqFire : Bool := fifoDeqValid && fifoDeqRdy
  -- AddrCalculate 输入（LSU.scala:554-578；mshrReady/idxEntry 来自 MSHRv2）
  let lsuMshrV : Bool := Mem.lsuMshrValid s.lsu                              -- :204
  let lsuIn : Mem.LsuIn :=
    { fifoValid   := fifoDeqValid
    , fifoBits    := fifoDeqBits
    , flushValid  := wsFlushDV                                               -- pipe.scala:169
    , mshrReady   := Mem.mshrAddrRdy s.mshr                                  -- MSHR.scala:46
    , idxEntry    := if lsuMshrV && Mem.mshrAddrRdy s.mshr
                     then Mem.mshrValidEntry s.mshr else 0#3                 -- :47（mshrIdxEntry）
    , dcacheReady := true                                                    -- M-D4 stub
    , sharedReady := Mem.smReqReady s.shm                                    -- ShareMem.scala:194
    , csrTid := 0#32, csrPds := 0#32, csrNumw := 0#32 }                      -- M-D3
  let lsuOut : Mem.LsuOut := Mem.lsuOutputs s.lsu lsuIn
  let lsuShFire : Bool := lsuOut.sharedValid && lsuIn.sharedReady
  -- ShareMem 输入（pipe.scala:413-414；rspReady = rspArbiter in(1).ready，M-D4）
  let shIn : Mem.SmIn :=
    { reqValid := lsuOut.sharedValid
    , req := smmShReqOf lsuOut.sharedBits
    , rspReady := Mem.mshrDcRdy s.mshr }                                     -- MSHR.scala:45
  let shRspV : Bool := Mem.smRspValid s.shm
  let shRsp : Mem.SmCoreRsp := Mem.smRspBits s.shm
  -- MSHR 输出（to_pipe，MSHR.scala:97-106）→ LSU2WB（LSU.scala:490-529）
  let rspValid : Bool := Mem.mshrOutValid s.mshr
  let rspTagM : Mem.MshrTag := Mem.mshrOutTag s.mshr
  let rspTag : Mem.LsuMshrTag := smmWbTagOf rspTagM
  let rspData : Mem.LsuRow := Mem.mshrOutData s.mshr
  let rspWid : BitVec 3 := rspTag.warp_id
  let lsuWbXV : Bool := rspValid && rspTag.wxd
  let lsuWbVV : Bool := rspValid && !rspTag.wxd && rspTag.wfd
  let bjEv : BjEvent 32 :=
    if !fireSimt then .nop
    else if isVBr then .branch bi
    else .join outVC.pc
  let bjOut : BjOut 32 := (bjSysStep sb0.bj bjEv).2
  let fcEnqValid : Bool := bjOut.fetchValid
  let fcDeqValid : Bool := s.base.fcV || fcEnqValid
  let fcDeqFire : Bool := fcDeqValid && !brFire
  let fcDeqJump : Bool := if s.base.fcV then s.base.fcJ else bjOut.fetchJump
  let fcDeqPC : BitVec 32 := if s.base.fcV then s.base.fcPC else bjOut.fetchPC
  let fcDeqWid : BitVec 3 := if s.base.fcV then s.base.fcWid else outVBits.control.wid
  let brMFire : Bool := brFire || fcDeqFire
  let brMJump : Bool := if brFire then brJump else fcDeqJump
  let brMWid : BitVec 3 := if brFire then brWid else fcDeqWid
  let brMTarget : BitVec 32 := if brFire then brTarget else fcDeqPC
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => true | .ws => !brMFire | _ => false
    -- M-D0a：X 侧 .LSU 落 `_ => false`（pipe.scala:377，忠实）
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR])
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brMFire
  -- ---- warp_sche 输入（M-D0e：flushDCacheReady 接 lsuFlushRdy，pipe.scala:171） ----
  let wsIn : WsInputs :=
    { warpReqFire := inp.reqFire, reqWid := inp.reqWid, newWgId := inp.reqWg
    , newWfCount := inp.reqCnt
    , warpControlFire := fireWs, simtStackOp := outXC.row.simtStackOp
    , wcWid := outXBits.control.wid, wgIdTag := inp.wgIdTag
    , warpRspReady := inp.warpRspReady
    , scoreboardBusy := sbBusy
    , exeBusy := 0#8
    , pcIbufRdy := ibufRdy
    , flushDCacheReady := Mem.lsuFlushRdy s.lsu                  -- M-D0e（原：环境输入 stub）
    , branchFire := brMFire, branchJump := brMJump, branchWid := brMWid
    , pcRspValid := false, pcRspMiss := false, pcRspWid := 0#3
    , pcReset := inp.pcReset }
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
  -- ---- 标量写回仲裁（M-D0c：in_x(2) 接 lsu2wb.out_x，pipe.scala:418） ----
  let aluWbValid : Bool := fireSAlu && outXC.row.wxd && (outXC.row.branch != 1#2)
  let csrWbValid : Bool := fireCsr && outXC.row.wxd
  let wbXValids : BitVec 6 :=
    (BitVec.ofBool aluWbValid).zeroExtend 6 |||
    ((BitVec.ofBool lsuWbXV).zeroExtend 6 <<< 2) |||          -- M-D0c
    ((BitVec.ofBool csrWbValid).zeroExtend 6 <<< 3)
  let wbXChoice : Fin 6 := wbArbChoice (by decide) wbXValids
  let wbXFire : Bool := wbArbOutValid wbXValids
  let wbXWid : BitVec 3 := if wbXChoice.val = 2 then rspTag.warp_id else outXBits.control.wid
  let wbXIdxw : BitVec 8 := if wbXChoice.val = 2 then rspTag.reg_idxw else outXC.regIdxw
  let wbXWxd : Bool := if wbXChoice.val = 2 then rspTag.wxd else outXC.row.wxd
  let wbXData : BitVec 32 :=
    if wbXChoice.val = 0 then aluRes.1
    else if wbXChoice.val = 2 then rspData ⟨0, by decide⟩      -- LSU2WB :499
    else 0#32
  let wbBank : BitVec 2 := ocWbScaBankId wbXIdxw wbXWid
  let wbAddr : BitVec 8 := ocWbScaAddr (sb0.csr.sgprBase (wsFin wbXWid)) wbXIdxw
  let wbWrEn : Bool := wbXFire && wbXWxd && (wbXIdxw != 0#8)
  -- ---- W-D0b：wb_v 写回链（M-D0c：in_v(2) 接 lsu2wb.out_v，pipe.scala:424） ----
  let wbVValid : Bool :=
    outVV && ((issRoute issV).any (fun t => decide (t = .vALU)))
      && outVC.row.wvd && !outVC.row.simtStack                          -- execution.scala:560
  let wbVValids : BitVec 6 :=
    (BitVec.ofBool wbVValid).zeroExtend 6 |||
    ((BitVec.ofBool lsuWbVV).zeroExtend 6 <<< 2)                        -- M-D0c
  let wbVChoice : Fin 6 := wbArbChoice (by decide) wbVValids            -- writeback.scala:61
  let wbVFire : Bool := wbArbOutValid wbVValids                         -- out_v.ready≡true（:624）
  let wbVWid : BitVec 3 := if wbVChoice.val = 2 then rspTag.warp_id else outVBits.control.wid
  let wbVIdxw : BitVec 8 := if wbVChoice.val = 2 then rspTag.reg_idxw else outVC.regIdxw
  let wbVWvd : Bool := if wbVChoice.val = 2 then rspTag.wfd else outVC.row.wvd
  let wbVData : RfVRow := smwWbData outVC.row.aluFn outVC.row.reverse exeMaskV
    outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3               -- :513-542（W-D4）
  let wbVOutData : RfVRow :=
    if wbVChoice.val = 0 then wbVData
    else if wbVChoice.val = 2 then rspData                              -- LSU2WB :501-504
    else cuRow0
  let wbVMaskFn : RfVMask :=
    if wbVChoice.val = 2 then (fun t => rspTagM.mask.getLsbD t.val)     -- LSU2WB :503
    else smwWbMaskFn exeMaskV
  let wbVBank : BitVec 2 := ocWbVecBankId wbVIdxw wbVWid                -- operandCollector.scala:603
  let wbVAddr : BitVec 8 := ocWbVecAddr (sb0.csr.vgprBase (wsFin wbVWid)) wbVIdxw  -- :604
  let wbVWen : Bool := wbVFire && wbVWvd                                -- :621（向量无 reg_idxw.orR）
  -- ---- LSU2WB lsu_rsp.ready（LSU.scala:516-520；out_x/out_v.ready = 仲裁 in(2)
  --      ready，out.ready≡true（operandCollector.scala:623-624）） ----
  let lsuRspRdy : Bool :=
    Mem.lsu2wbRspReady ⟨rspValid, ⟨rspTag, rspData⟩,
      wbArbInReady wbXValids true ⟨2, by decide⟩,
      wbArbInReady wbVValids true ⟨2, by decide⟩⟩
  let lsuRspFire : Bool := rspValid && lsuRspRdy
  -- MSHR 输入（LSU.scala:566-570：from_addr←to_mshr、from_dcache←rspArbiter、
  -- to_pipe.ready←lsu2wb lsu_rsp.ready）
  let mshrIn : Mem.MshrIn :=
    { addrValid := lsuMshrV
    , addrTag := smmMshrTagOf lsuOut.mshrTag
    , dcValid := shRspV                                                 -- M-D4（in0 恒 invalid）
    , rspId := shRsp.instrId
    , rspData := shRsp.data
    , rspMask := smmPackMask shRsp.activeMask
    , outReady := lsuRspRdy }
  let mshrDcF : Bool := Mem.mshrDcFire s.mshr mshrIn
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
  -- ---- 记分板输入（M-D0d：fence_end 接 lsu.io.fence_end(i)，pipe.scala:241） ----
  let sbIn : Fin 8 → SbInputs := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    { if_fire := (i2iXFire && (i2iXWid == w3)) || (i2iVFire && (i2iVWid == w3))
    , if_ctrl := if (i2iXFire && (i2iXWid == w3)) then smToSbCtrl i2iXC else smToSbCtrl i2iVC
    , wb_v_fire := wbVFire && (wbVWid == w3)          -- pipe.scala:271
    , wb_v_wvd := wbVWvd
    , wb_v_idxw := wbVIdxw
    , wb_x_fire := wbXFire && (wbXWid == w3), wb_x_wxd := wbXWxd, wb_x_idxw := wbXIdxw
    , br_ctrl := (brMFire && (brMWid == w3)) || (fireWs && (outXBits.control.wid == w3))
        || (bjOut.complete && (outVBits.control.wid == w3))
    , fence_end := Mem.lsuSbEmpty (s.boards w3)                       -- M-D0d（原：false stub）
        (Mem.lsuSbLeftOf fireLsu lsuReqWid w3)
        (Mem.lsuSbRightOf lsuRspFire rspWid w3)
    , opColV_in := i2iVFire && (i2iVWid == w3)
    , opColV_out := ocOutVFire && (outVBits.control.wid == w3)
    , opColX_in := i2iXFire && (i2iXWid == w3)
    , opColX_out := ocOutXFire && (outXBits.control.wid == w3) }
  -- ---- PCcontrol 驱动（同 smwComb） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.reqFire && (inp.reqWid == w3) then ⟨inp.reqPC, false, 1#2, 0#2⟩
    else if brMFire && brMJump && (brMWid == w3) then ⟨brMTarget, false, 1#2, 0#2⟩
    else if fetchV && (fetchWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入（同 smwComb，W-D0d） ----
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
  , exeMaskV := exeMaskV, wbVValid := wbVValid, wbVChoice := wbVChoice
  , wbVFire := wbVFire, wbVWid := wbVWid, wbVIdxw := wbVIdxw, wbVWvd := wbVWvd
  , wbVData := wbVData, wbVOutData := wbVOutData, wbVMaskFn := wbVMaskFn
  , wbVBank := wbVBank, wbVAddr := wbVAddr, wbVWen := wbVWen
  , wbXValids := wbXValids, wbVValids := wbVValids, wbXChoice := wbXChoice
  -- M-D0 增量字段
  , wsFlushDV := wsFlushDV
  , lsuReqV := lsuReqV, lsuReqWid := lsuReqWid, lsuReqBits := lsuReqBits
  , lsuReqRdyT := lsuReqRdyT, fireLsu := fireLsu
  , fifoEnqValid := fifoEnqValid, fifoEnqRdy := fifoEnqRdy, fifoEnqFire := fifoEnqFire
  , fifoDeqValid := fifoDeqValid, fifoDeqBits := fifoDeqBits, fifoDeqFire := fifoDeqFire
  , lsuIn := lsuIn, lsuOut := lsuOut, lsuShFire := lsuShFire
  , shIn := shIn, shRspV := shRspV
  , mshrIn := mshrIn, mshrDcF := mshrDcF
  , rspValid := rspValid, rspTag := rspTag, rspData := rspData, rspWid := rspWid
  , lsuWbXV := lsuWbXV, lsuWbVV := lsuWbVV
  , lsuRspRdy := lsuRspRdy, lsuRspFire := lsuRspFire }

/- ========================================================================= -/
/- 3. 单拍 step 与多拍 run                                                      -/
/- =========================================================================-/

/-- SM 访存变体单拍：底座部分与 smwStep 同形（组合信号来自 smmComb），
    外加 LSU 顶层装配/AddrCalculate/ShareMem/MSHRv2 四个子系统的转移。 -/
def smmStep (prog : SmProg) (s : SmmState) (inp : SmIn) : SmmState :=
  let c := smmComb prog s inp
  let b0 := s.base.base
  { base :=
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
    , fcV := (s.base.fcV && !c.fcDeqFire) || (c.fcEnqValid && !(c.fcDeqFire && !s.base.fcV))
    , fcJ := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.bjOut.fetchJump else s.base.fcJ
    , fcPC := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.bjOut.fetchPC else s.base.fcPC
    , fcWid := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.outVWid else s.base.fcWid }
  -- ---- M-D1：InputFIFO（LSU.scala:551 的 Queue(1,pipe=true)） ----
  , fifoFull := if c.fifoEnqFire != c.fifoDeqFire then c.fifoEnqFire else s.fifoFull
  , fifoBits := if c.fifoEnqFire then c.lsuReqBits else s.fifoBits
  -- ---- ShiftBoard×8（LSU.scala:572-576：left=lsu_req.fire、right=lsu_rsp.fire） ----
  , boards := Mem.lsuSbStepAll s.boards c.fireLsu c.lsuReqWid c.lsuRspFire c.rspWid
  -- ---- AddrCalculate（:113-489；smax = sharemem_size = 0x20000，D1/LSUexe:554） ----
  , lsu := Mem.lsuStep Mem.lsuSmaxDefault s.lsu c.lsuIn
  -- ---- ShareMem（ShareMem.scala:55-195） ----
  , shm := Mem.smStep s.shm c.shIn
  -- ---- MSHRv2（MSHR.scala:31-108） ----
  , mshr := Mem.mshrStep s.mshr c.mshrIn }

/-- 多拍运行 -/
def smmRun (prog : SmProg) (s : SmmState) (ins : List SmIn) : SmmState :=
  ins.foldl (smmStep prog) s

/- ========================================================================= -/
/- 4. 连线语义定理（装配级 rfl / 与模块级定理的对接引用）                        -/
/- ========================================================================= -/

/-- 连线：ShareMem 请求 setIdx = LSU 8 位 setIdx 的零扩展——**I-21 断点钉死**
    （LSU.scala:171/216 → GPGPU_top.scala:488；addr(16,15) 在此丢弃。
    模块级别名证据见 ShareMem.lean 的 smI21_alias/smI21_dead_rows/smI21_witness） -/
theorem smmT_shreq_setidx_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    ((smmComb prog s inp).shIn.req.setIdx) =
      ((smmComb prog s inp).lsuOut.sharedBits.setIdx).zeroExtend 10 := rfl

/-- 连线：MSHR 分配 tag = AddrCalculate to_mshr tag（LSU.scala:566） -/
theorem smmT_mshr_addrTag_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    ((smmComb prog s inp).mshrIn.addrTag) =
      smmMshrTagOf ((smmComb prog s inp).lsuOut.mshrTag) := rfl

/-- 连线：MSHR from_dcache.valid = shared_rsp.valid（rspArbiter in(0)=dcache_rsp
    恒 invalid 的 M-D4 简化，LSU.scala:560-563） -/
theorem smmT_mshr_dcvalid_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    ((smmComb prog s inp).mshrIn.dcValid) = (smmComb prog s inp).shRspV := rfl

/-- wb 有效位的位 2 = LSU2WB 源（纯位代数：其余源只占位 0/3） -/
theorem smmT_wbValids_bit2 (a l c : Bool) :
    (((BitVec.ofBool a).zeroExtend 6 ||| ((BitVec.ofBool l).zeroExtend 6 <<< 2) |||
      ((BitVec.ofBool c).zeroExtend 6 <<< 3)) &&& 4#6) =
      ((BitVec.ofBool l).zeroExtend 6 <<< 2) := by
  cases a <;> cases l <;> cases c <;> decide

/-- wb 有效位（仅位 0/2）的位 2 = LSU2WB 源（向量侧形态） -/
theorem smmT_wbVValids_bit2 (v l : Bool) :
    (((BitVec.ofBool v).zeroExtend 6 ||| ((BitVec.ofBool l).zeroExtend 6 <<< 2)) &&& 4#6) =
      ((BitVec.ofBool l).zeroExtend 6 <<< 2) := by
  cases v <;> cases l <;> decide

/-- 连线：LSU2WB out_v.valid 并入 wb 仲裁 in_v(2)（pipe.scala:424） -/
theorem smmT_wbVValids_lsu_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    ((smmComb prog s inp).wbVValids &&& (1#6 <<< 2)) =
      ((BitVec.ofBool (smmComb prog s inp).lsuWbVV).zeroExtend 6 <<< 2) :=
  smmT_wbVValids_bit2 _ _

/-- 连线：LSU2WB out_x.valid 并入 wb 仲裁 in_x(2)（pipe.scala:418） -/
theorem smmT_wbXValids_lsu_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    ((smmComb prog s inp).wbXValids &&& (1#6 <<< 2)) =
      ((BitVec.ofBool (smmComb prog s inp).lsuWbXV).zeroExtend 6 <<< 2) :=
  smmT_wbValids_bit2 _ _ _

/-- 连线：lsu_rsp.ready = LSU2WB 路由（LSU.scala:516-520） -/
theorem smmT_lsuRspRdy_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    (smmComb prog s inp).lsuRspRdy =
      Mem.lsu2wbRspReady ⟨(smmComb prog s inp).rspValid,
        ⟨(smmComb prog s inp).rspTag, (smmComb prog s inp).rspData⟩,
        wbArbInReady (smmComb prog s inp).wbXValids true ⟨2, by decide⟩,
        wbArbInReady (smmComb prog s inp).wbVValids true ⟨2, by decide⟩⟩ := rfl

/-- 连线：ShiftBoard 步进 = left(lsu_req.fire)/right(lsu_rsp.fire)
    （LSU.scala:574-575） -/
theorem smmT_boards_step_wire (prog : SmProg) (s : SmmState) (inp : SmIn) :
    (smmStep prog s inp).boards =
      Mem.lsuSbStepAll s.boards (smmComb prog s inp).fireLsu
        (smmComb prog s inp).lsuReqWid (smmComb prog s inp).lsuRspFire
        (smmComb prog s inp).rspWid := rfl

/-- 连线：fence_end 接 ShiftBoard 当拍后空（pipe.scala:241 → LSU.scala:577） -/
theorem smmT_fenceEnd_wire (prog : SmProg) (s : SmmState) (inp : SmIn) (w : Fin 8) :
    ((smmComb prog s inp).sbIn w).fence_end =
      Mem.lsuSbEmpty (s.boards (BitVec.ofNat 3 w.val))
        (Mem.lsuSbLeftOf (smmComb prog s inp).fireLsu
          (smmComb prog s inp).lsuReqWid (BitVec.ofNat 3 w.val))
        (Mem.lsuSbRightOf (smmComb prog s inp).lsuRspFire
          (smmComb prog s inp).rspWid (BitVec.ofNat 3 w.val)) := rfl

/- ========================================================================= -/
/- 5. 场景 A：向量 store → load 的 LDS 端到端（写读一致）                        -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 5.1）：                                 -/
/-    0x00 lui  x1, 0x70000   ; 0x700000B7  x1 := 0x70000000（LDS_BASE）        -/
/-    0x04 vse32.v v1, (x1)   ; 0x0200E0A7  32 lane 写 LDS[0x00..0x7C]          -/
/-    0x08 vle32.v v2, (x1)   ; 0x0200E107  读回 → v2                           -/
/-    0x0C endprg             ; 0x0000400B                                    -/
/-  数据（初始状态预置，vgpr_base=16 ⇒ bank 内基址 4）：                          -/
/-    v1 = [0xAB00+t]（bank1 addr4）。全掩码（vm=1，规避 I-12 死锁现场）；        -/
/-    单 set 单 tag（基址 128B 对齐）⇒ LSU 单请求、ShareMem 无 bank 冲突、        -/
/-    MSHR 单响应完成。                                                        -/
/-  期望：v2（bank2 addr4）全 lane = v1 行；ShareMem bank b 行 0 = 0xAB00+b；    -/
/-    事件链 lsu_req.fire → MSHR 分配 → shared_req.fire → 响应 → lsu_rsp.fire    -/
/-    →（store 无写回）/（load：→ LSU2WB out_v → wb 仲裁 in_v(2) → bank 写 +     -/
/-    busy(v2) 清除）。                                                        -/
/- ========================================================================= -/

/-- v1 数据行：lane t = 0xAB00 + t -/
def smmRowA : RfVRow := fun t => 0xAB00#32 + BitVec.ofNat 32 t.val

def smmProgA : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x700000B7#32
    else if pc = 0x04#32 then 0x0200E0A7#32
    else if pc = 0x08#32 then 0x0200E107#32
    else if pc = 0x0C#32 then 0x0000400B#32
    else 0#32

/-- 场景 A 初始状态：v1 预置（bank1 addr4）+ tmask 全 1 -/
def smmS0A : SmmState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a => if a.val = 4 then smmRowA else rfVInit.mem a }
    else rfVInit).toArray
  smmInitOf
    { base := { smInit with
        vrf := vrf
      , csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- 场景拍数 -/
def smmNA : Nat := 64

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr base=0、vgpr base=16），其后空转 -/
def smmInsA : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smmNA - 1) smInNop

/- ---- 5.1 机器码译码回归（III 类自检） ---- -/

-- lui x1, 0x70000：LUI 行、rd=1、wxd=1、路由 sALU
example :
    let c := smDecode 0x700000B7#32 0#3 0x00#32
    (c.row == (decRowOf decAllTables "LUI")) && (c.regIdxw == 1#8) &&
    (c.row.wxd == true) && (issRoute (smToIssCtrl c) == [.sALU]) = true := by
  native_decide

-- vse32.v v1, (x1)：VSE32_V 行、vs3=1（regIdx3）、rs1=1、mem_cmd=M_XWR、
-- wvd=0、isvec=1、mem_whb=W、路由 LSU 单发、无掩码读（vm=1，规避 I-12）
example :
    let c := smDecode 0x0200E0A7#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "VSE32_V")) && (c.regIdx3 == 1#8) &&
    (c.regIdx1 == 1#8) && (c.row.memCmd == 2#2) && (c.row.wvd == false) &&
    (c.row.isvec == true) && (c.row.memWhb == 3#2) &&
    (issRoute (smToIssCtrl c) == [.LSU]) &&
    (smMaskOf c.inst c.row == false) = true := by native_decide

-- vle32.v v2, (x1)：VLE32_V 行、vd=2（regIdxw）、mem_cmd=M_XRD、wvd=1、路由 LSU
example :
    let c := smDecode 0x0200E107#32 0#3 0x08#32
    (c.row == (decRowOf decAllTables "VLE32_V")) && (c.regIdxw == 2#8) &&
    (c.regIdx1 == 1#8) && (c.row.memCmd == 1#2) && (c.row.wvd == true) &&
    (c.row.isvec == true) && (issRoute (smToIssCtrl c) == [.LSU]) = true := by
  native_decide

-- LSU 侧控制字切片：store 的 isWrite 位、load 的 mop=0（unit stride）
example :
    (smmLsuCtrlOf (smDecode 0x0200E0A7#32 0#3 0x04#32)).mem_cmd = 2#2 ∧
    (smmLsuCtrlOf (smDecode 0x0200E107#32 0#3 0x08#32)).mop = 0#2 := by
  native_decide

-- 地址链数值：unit stride（mop=0）下 lane x 地址 = base + 4x（LSU.scala:153-154）
example :
    let v : Mem.LsuVExe := ⟨fun _ => 0x70000000#32, fun _ => 0, smmRowA,
      fun _ => true, smmLsuCtrlOf (smDecode 0x0200E0A7#32 0#3 0x04#32)⟩
    (Mem.lsuLaneAddr v 0 0 0 ⟨0, by decide⟩ == 0x70000000#32) &&
    (Mem.lsuLaneAddr v 0 0 0 ⟨31, by decide⟩ == 0x7000007C#32) &&
    (Mem.lsuAllShared Mem.lsuSmaxDefault v 0 0 0 == true) &&
    (Mem.lsuSetOf (Mem.lsuLaneAddr v 0 0 0 ⟨31, by decide⟩) == 0#8) = true := by
  native_decide

/- ---- 5.2 监控器与轨迹判收 ---- -/

/-- 监控累积器：访存链事件时间线 + 终态判收 -/
structure SmmChk where
  tick       : Nat
  luiWbT     : Nat          -- LUI 标量写回拍+1
  stT        : Nat          -- 第一个 store lsu_req.fire 拍+1
  st2T       : Nat          -- 第二个 store lsu_req.fire 拍+1（场景 B）
  stAllocT   : Nat          -- store MSHR 分配拍+1
  shmWT      : Nat          -- store shared_req fire 拍+1
  shmWRspT   : Nat          -- store 响应进 MSHR（from_dcache.fire）拍+1
  stRspT     : Nat          -- store lsu_rsp.fire（释放 MSHR 条目）拍+1
  ldT        : Nat          -- load lsu_req.fire 拍+1
  ldAllocT   : Nat
  shmRT      : Nat
  shmRRspT   : Nat
  ldWbT      : Nat          -- load wb_v fire（in_v(2) 源）拍+1
  ldWbD0     : BitVec 32    -- wb 数据 lane0（应 = 0xAB00）
  ldWbD31    : BitVec 32    -- lane31（应 = 0xAB1F）
  busyAtWb   : Bool         -- 写回拍前 busy(v2)（应 true）
  busyAftWb  : Bool         -- 写回拍后 busy(v2)（应 false）
  mismFire   : Nat          -- fireLsu ≠ fifoEnqFire 拍数（M-D2，应 0）
  nShReq     : Nat          -- shared_req fire 总数（A 应 2）
  endT       : Nat          -- endprg 拍+1
  finOk      : Bool
  deriving DecidableEq, Repr

/-- 空监控记录 -/
def smmChk0 : SmmChk :=
  { tick := 0, luiWbT := 0, stT := 0, st2T := 0, stAllocT := 0, shmWT := 0, shmWRspT := 0
  , stRspT := 0, ldT := 0, ldAllocT := 0, shmRT := 0, shmRRspT := 0
  , ldWbT := 0, ldWbD0 := 0#32, ldWbD31 := 0#32
  , busyAtWb := false, busyAftWb := false, mismFire := 0, nShReq := 0
  , endT := 0, finOk := false }

/-- ShareMem bank b 行 0 的字（小端字节拼装） -/
def smmShmWord (s : SmmState) (b : Fin 32) : BitVec 32 :=
  Mem.smBytesToWord (fun j => (s.shm.banks b).mem ⟨0, by decide⟩ j)

/-- 监控单拍（ldIdxw = 本场景 load 的目的寄存器号，busy 捕拍用） -/
def smmMonStep (ldIdxw : BitVec 8) (prog : SmProg) (acc : SmmChk × SmmState)
    (inp : SmIn) : SmmChk × SmmState :=
  let (m, s) := acc
  let c := smmComb prog s inp
  let s' := smmStep prog s inp
  let t := m.tick
  let isWrReq : Bool := Mem.lsuMemCmdWr c.lsuReqBits.ctrl.mem_cmd
  let m1 := { m with
      tick := t + 1
    , mismFire := m.mismFire + (if c.fireLsu != c.fifoEnqFire then 1 else 0)
    , nShReq := m.nShReq + (if c.lsuShFire then 1 else 0)
    , endT := if c.fireWs && c.outXWid == 0#3 && m.endT == 0 then t + 1 else m.endT }
  let m2 := if c.wbXFire && c.wbXIdxw == 1#8 && m1.luiWbT == 0 then { m1 with luiWbT := t + 1 } else m1
  let m3 := if c.fireLsu && isWrReq then
      if m2.stT == 0 then { m2 with stT := t + 1 }
      else if m2.st2T == 0 then { m2 with st2T := t + 1 } else m2
    else m2
  let m4 := if Mem.mshrAddrFire s.mshr c.mshrIn && c.mshrIn.addrTag.isWrite && m3.stAllocT == 0
      then { m3 with stAllocT := t + 1 } else m3
  let m5 := if c.lsuShFire && c.shIn.req.isWrite && m4.shmWT == 0 then { m4 with shmWT := t + 1 } else m4
  let m6 := if c.mshrDcF && (Mem.smRspBits s.shm).isWrite && m5.shmWRspT == 0
      then { m5 with shmWRspT := t + 1 } else m5
  let m7 := if c.lsuRspFire && c.rspTag.isWrite && m6.stRspT == 0 then { m6 with stRspT := t + 1 } else m6
  let m8 := if c.fireLsu && !isWrReq && m7.ldT == 0 then { m7 with ldT := t + 1 } else m7
  let m9 := if Mem.mshrAddrFire s.mshr c.mshrIn && !c.mshrIn.addrTag.isWrite && m8.ldAllocT == 0
      then { m8 with ldAllocT := t + 1 } else m8
  let m10 := if c.lsuShFire && !c.shIn.req.isWrite && m9.shmRT == 0 then { m9 with shmRT := t + 1 } else m9
  let m11 := if c.mshrDcF && !(Mem.smRspBits s.shm).isWrite && m10.shmRRspT == 0
      then { m10 with shmRRspT := t + 1 } else m10
  let m12 := if c.wbVFire && c.wbVChoice.val == 2 && m11.ldWbT == 0 then
      { m11 with
          ldWbT := t + 1
        , ldWbD0 := c.wbVOutData ⟨0, by decide⟩, ldWbD31 := c.wbVOutData ⟨31, by decide⟩
        , busyAtWb := sbRead false (s.base.base.sb ⟨0, by decide⟩).vectorReg ldIdxw
        , busyAftWb := sbRead false (s'.base.base.sb ⟨0, by decide⟩).vectorReg ldIdxw }
    else m11
  (m12, s')

/-- 单遍跑完输入轨迹并给出全部检查结论（含终态判收） -/
def smmRunChkA (prog : SmProg) (ins : List SmIn) : SmmChk :=
  let (m, sf) := ins.foldl (smmMonStep 2#8 prog) (smmChk0, smmS0A)
  { m with finOk :=
      -- v2（bank2 addr4）全 32 lane == v1 行（LDS 写读一致，整机级）
      (List.finRange 32).all (fun t =>
        (smVrfAt sf.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == smmRowA t) &&
      -- ShareMem 低区行 0：bank b = 0xAB00+b（store 落盘抽查）
      (smmShmWord sf ⟨0, by decide⟩ == 0xAB00#32) &&
      (smmShmWord sf ⟨5, by decide⟩ == 0xAB05#32) &&
      (smmShmWord sf ⟨31, by decide⟩ == 0xAB1F#32) &&
      -- warp 收尾与子系统归位
      (sf.base.base.ws.warpActive == 0#8) &&
      (wsMask0 sf.base.base.ws.endprgCnt sf.base.base.ws.wgValid == 0#8) &&
      (sf.lsu.state == Mem.lsuSIdle) && (sf.fifoFull == false) &&
      (sf.mshr.used == 0#8) && (sf.boards 0#3 == 0#4) &&
      -- M-D2 装配一致性：全程 fireLsu = fifoEnqFire
      (m.mismFire == 0) && (m.nShReq == 2) }

/-- 期望结论（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1）。
    store：lsu_req.fire(9) → MSHR 分配(10) → shared_req.fire(11) → 响应入
    MSHR(13) → lsu_rsp.fire 释放条目(14)；load 与 store 发射重叠（fifo 空即
    放行，13）→ 分配(16) → shared_req.fire(17) → 响应(19) → wb_v fire(20)：
    in_v(2) 仲裁通过、lane0/31 数据正确、busy(v2) 写回拍清除（I-9 链的 LSU
    实例）；endprg(15)；终态 v2 全 lane = v1 行、ShareMem 行 0 = v1 行、
    LSU/ShareMem/MSHR/ShiftBoard 全部归位。 -/
def smmExpA : SmmChk :=
  { tick := smmNA
  , luiWbT := 5
  , stT := 9, st2T := 0, stAllocT := 10, shmWT := 11, shmWRspT := 13, stRspT := 14
  , ldT := 13, ldAllocT := 16, shmRT := 17, shmRRspT := 19
  , ldWbT := 20, ldWbD0 := 0x0000AB00#32, ldWbD31 := 0x0000AB1F#32
  , busyAtWb := true, busyAftWb := false
  , mismFire := 0, nShReq := 2, endT := 15
  , finOk := true }

/-- **场景 A 主定理（LDS 写读一致，端到端）**：lui → vse32（32 lane 写
    LDS[0x70000000..0x7C]）→ vle32 读回 → v2 全 lane = v1 行；事件时间线、
    busy 清除、子系统归位全部符合手算。对接引用：ShareMem 模块级写读一致性
    （ShareMem.lean `smT1_read_rsp`）、MSHR 分配/释放（MSHR.lean
    `mshr_outFire_entry_cleared`）、LSU2WB 路由（LSU.lean `lsu2wb_rspFire_iff`）、
    写回同拍直通（Writeback.lean A4 / SMVecWb.lean `smwT_wbV_fire_eq_valid`）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smmTraceA_ok : smmRunChkA smmProgA smmInsA = smmExpA := by
  native_decide

/- ========================================================================= -/
/- 6. 场景 B：I-21 的整机级演示——LDS 高区写 → 低区读得脏数据                     -/
/-                                                                           -/
/-  I-21（doc/03 已确认）：LSU to_shared.setIdx 只有 8 位（addr(14,7)），        -/
/-  ShareMem 需 10 位（NSets=1024），GPGPU_top.scala:488 零扩展对接 ⇒           -/
/-  addr(16,15) 丢弃，LDS 高 96KB 与低 32KB 逐字节别名。模块级证据：            -/
/-  ShareMem.lean smI21_alias/smI21_dead_rows/smI21_witness。本节把它推到       -/
/-  **整机级**：真实程序（lui×2 + vse32×2 + vle32）在完整 SM+LSU+ShareMem+MSHR  -/
/-  模型上演示"高区写静默污染低区"。                                           -/
/-                                                                           -/
/-  程序（warp0）：                                                            -/
/-    0x00 lui  x1, 0x70000   ; 0x700000B7  x1 := 0x70000000（低区基址）        -/
/-    0x04 lui  x2, 0x70008   ; 0x70008137  x2 := 0x70008000（高区 +32KB）      -/
/-    0x08 vse32.v v1, (x1)   ; 0x0200E0A7  低区写 v1 行（0xAB00+t）            -/
/-    0x0C vse32.v v3, (x2)   ; 0x020161A7  高区写 v3 行（0xCD00+t）            -/
/-    0x10 vle32.v v4, (x1)   ; 0x0200E207  读低区 → v4                         -/
/-    0x14 endprg             ; 0x0000400B                                    -/
/-  别名机制（模型内逐步可查）：高区地址 0x70008000+4x 的 tag=addr(31,15) 与     -/
/-  低区不同 ⇒ LSU 拆成独立请求（两笔 store 各占一个 MSHR 条目）；但 8 位        -/
/-  setIdx 同为 0x00 ⇒ ShareMem 行 0 被高区写覆盖；低区读从行 0 取数 ⇒           -/
/-  v4 = v3 行 ≠ v1 行。                                                       -/
/- ========================================================================= -/

/-- v3 数据行（高区写）：lane t = 0xCD00 + t -/
def smmRowB : RfVRow := fun t => 0xCD00#32 + BitVec.ofNat 32 t.val

def smmProgB : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x700000B7#32
    else if pc = 0x04#32 then 0x70008137#32
    else if pc = 0x08#32 then 0x0200E0A7#32
    else if pc = 0x0C#32 then 0x020161A7#32
    else if pc = 0x10#32 then 0x0200E207#32
    else if pc = 0x14#32 then 0x0000400B#32
    else 0#32

/-- 场景 B 初始状态：v1（bank1 addr4）与 v3（bank3 addr4）预置 -/
def smmS0B : SmmState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a => if a.val = 4 then smmRowA else rfVInit.mem a }
    else if i.val = 3 then { rfVInit with mem := fun a => if a.val = 4 then smmRowB else rfVInit.mem a }
    else rfVInit).toArray
  smmInitOf
    { base := { smInit with
        vrf := vrf
      , csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- 场景拍数 -/
def smmNB : Nat := 80

/-- 输入：拍 0 派发 warp0，其后空转 -/
def smmInsB : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smmNB - 1) smInNop

/- ---- 6.1 机器码译码回归（III 类自检） ---- -/

-- lui x2, 0x70008：LUI 行、rd=2
example :
    let c := smDecode 0x70008137#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "LUI")) && (c.regIdxw == 2#8) = true := by
  native_decide

-- vse32.v v3, (x2)：VSE32_V 行、vs3=3、rs1=2
example :
    let c := smDecode 0x020161A7#32 0#3 0x0C#32
    (c.row == (decRowOf decAllTables "VSE32_V")) && (c.regIdx3 == 3#8) &&
    (c.regIdx1 == 2#8) && (c.row.memCmd == 2#2) = true := by native_decide

-- vle32.v v4, (x1)：VLE32_V 行、vd=4
example :
    let c := smDecode 0x0200E207#32 0#3 0x10#32
    (c.row == (decRowOf decAllTables "VLE32_V")) && (c.regIdxw == 4#8) &&
    (c.row.memCmd == 1#2) && (c.row.wvd == true) = true := by native_decide

-- 别名链数值：高区基址的 8 位 setIdx 截断为 0（= 低区），tag 不同（拆请求），
-- ShareMem 行址相同（I-21 机制三环节；模块级 bv_decide 版见 ShareMem.lean
-- smI21_alias/smI21_dead_rows）
example :
    (Mem.lsuSetOf 0x70008040#32 == 0#8) && (Mem.lsuSetOf 0x70000040#32 == 0#8) &&
    (Mem.lsuTagOf 0x70008040#32 != Mem.lsuTagOf 0x70000040#32) &&
    (Mem.smSetIdxOfAddr 0x70008040#32 == Mem.smSetIdxOfAddr 0x70000040#32) = true := by
  native_decide

/- ---- 6.2 轨迹判收 ---- -/

/-- 单遍跑完并判收：v4 全 lane = v3 行（脏数据！）、v4 ≠ v1 行（本应读回
    v1——别名污染的直接证据）、ShareMem 行 0 被高区数据覆盖、子系统归位 -/
def smmRunChkB (prog : SmProg) (ins : List SmIn) : SmmChk :=
  let (m, sf) := ins.foldl (smmMonStep 4#8 prog) (smmChk0, smmS0B)
  { m with finOk :=
      -- **I-21 整机现象**：低区读回的是高区写入的脏数据
      (List.finRange 32).all (fun t =>
        (smVrfAt sf.base.base ⟨0, by decide⟩).mem ⟨5, by decide⟩ t == smmRowB t) &&
      -- 反证对照：不是本应读到的 v1 行（lane0 采样：0xCD00 ≠ 0xAB00）
      ((smVrfAt sf.base.base ⟨0, by decide⟩).mem ⟨5, by decide⟩ ⟨0, by decide⟩ == 0xCD00#32) &&
      (0xCD00#32 != smmRowA ⟨0, by decide⟩) &&
      -- ShareMem 低区行 0 被高区写覆盖（硅片侧证据）
      (smmShmWord sf ⟨0, by decide⟩ == 0xCD00#32) &&
      (smmShmWord sf ⟨31, by decide⟩ == 0xCD1F#32) &&
      -- warp 收尾与子系统归位
      (sf.base.base.ws.warpActive == 0#8) &&
      (wsMask0 sf.base.base.ws.endprgCnt sf.base.base.ws.wgValid == 0#8) &&
      (sf.lsu.state == Mem.lsuSIdle) && (sf.fifoFull == false) &&
      (sf.mshr.used == 0#8) && (sf.boards 0#3 == 0#4) &&
      (m.mismFire == 0) && (m.nShReq == 3) && (m.st2T != 0) }

/-- 期望结论（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1） -/
def smmExpB : SmmChk :=
  { tick := smmNB
  , luiWbT := 5
  , stT := 11, st2T := 15, stAllocT := 12, shmWT := 13, shmWRspT := 15, stRspT := 16
  , ldT := 19, ldAllocT := 21, shmRT := 22, shmRRspT := 25
  , ldWbT := 26, ldWbD0 := 0x0000CD00#32, ldWbD31 := 0x0000CD1F#32
  , busyAtWb := true, busyAftWb := false
  , mismFire := 0, nShReq := 3, endT := 21
  , finOk := true }

/-- **场景 B 主定理（I-21 整机级演示）**：低区写 v1（0xAB00+t）→ 高区
    （+32KB）写 v3（0xCD00+t）→ 读低区得 v3 行——8 位 setIdx 截断
    （smmT_shreq_setidx_wire 钉死的对接点）使高区写静默覆盖低区，整机行为
    层面坐实 I-21。与模块级证据（ShareMem.lean `smI21_witness`）一致；
    时间线显示两笔 store 被 tag 分组拆为两个独立 ShareMem 请求（stT=11、
    st2T=15、nShReq=3），各自正常完成——污染无任何异常信号，纯静默数据
    错误。（单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smmTraceB_ok : smmRunChkB smmProgB smmInsB = smmExpB := by
  native_decide

/- ========================================================================= -/
/- 7. 障碍清单与发现（上报主会话）                                             -/
/- ========================================================================= -/
/-
  I-SM-4【障碍，已在本文件解除】SM 系列组合模型的 LSU 端口堵死（portRdyV 的
    `_ => false`）已接通：issueV out_LSU → LSU 顶层装配（InputFIFO pipe 队列
    + ShiftBoard×8 + full 门控，LSU.scala:551-579）→ AddrCalculate
    （Mem/LSU.lean 原样例化，smax=0x20000）→ ShareMem（Mem/ShareMem.lean
    原样例化，setIdx 8→10 零扩展对接 = I-21 断点）→ rspArbiter（M-D4 简化）
    → MSHRv2（Mem/MSHR.lean 原样例化）→ LSU2WB（LSU.scala:490-529）→
    wb 仲裁 in_x(2)/in_v(2)（pipe.scala:418/:424）→ 寄存器堆写口与记分板
    清除（pipe.scala:271/:288-289）。fence_end 从 false stub 升级为
    ShiftBoard 真空值（pipe.scala:241）；flushDCache 双向握手接通
    （pipe.scala:169-171，wsIn.flushDCacheReady := lsuFlushRdy）。
    两条整机轨迹判收：smmTraceA_ok（LDS 写读一致，64 拍）与 smmTraceB_ok
    （I-21 整机演示，80 拍）。SMVecWb.lean 未改动；若主会话决定回合，增量点
    即 M-D0 的 (a)-(e) 五处。

  M-O1【模型边界，非 bug】DCache/L2 未接入（M-D4）：dcache_req.ready 恒真、
    dcache_rsp 恒 invalid。后果：(i) 非 LDS（global）地址的访存请求被 DCache
    stub 吞掉且无响应 → MSHR 条目悬挂（真实硬件会由 L1D/L2 服务）——场景
    只用 LDS 地址，不可达；(ii) flush_dcache 请求被接受即完成，真实 L1D 会
    回 activeMask=0 的 coreRsp（LSU.lean Q8 的 MSHR 伪响应扰动未建模）。
    升级路径：接 Mem/DCache.lean（dc 前缀）+ 单 outstanding L2 stub。

  M-O2【模型边界】csr_tid/csr_pds/csr_numw 恒 0（M-D3）：SmCsrView 无 lsu_*
    字段。仅影响 VLS12/VSS12 的分段地址公式（LSU.scala:150）；unit-stride/
    strided/gather 与标量访存不受影响。升级需在 SmCsrView 增加三字段并在
    CTA 派发输入中携带（SmIn 需扩字段——动 SM.lean，留主会话决策）。

  M-O3【I 类观察】标量访存指令（LW/SW 等 isvec=false 且 mem=1）经
    ibuffer2issue 路由到 issueX（operandCollector.scala:640-650 的 isvec
    判别），而 pipe.scala:377 `issueX.io.out_LSU.ready := false.B` 恒堵 →
    issue.scala:114-117 的 mem 分支 inputBuf.ready 永假 → **标量 load/store
    在 issueX 永久卡死**（死锁形态与 I-12 同族：请求方等永不就绪的下游）。
    本模型忠实复现（portRdyX 的 .LSU 落 `_ => false`）；场景用向量访存
    规避。现行内核约定全部访存走向量形式（VLE/VSE/VLS12）故未暴露；RV32I
    标量访存语义上属设计缺陷。建议主会话核查是否已录 doc/03（与 I-12
    分属不同模块：I-12 在 collectorUnit，本条在 issueX 连线）。

  M-O4【既有结论的整机复核】I-22（MSHR to_pipe.valid 可回撤）在本集成下
    无害的结论（LSU.lean Q13 全链核查）于整机轨迹中复验：两场景
    lsuRspRdy 全链同拍贯通（out.ready≡true），未观测到回撤——与
    `lsu2wb_rspFire_iff`/`mshr_noWithdraw_violated` 的下游判定一致。

  M-O5【装配一致性】M-D2 的 "issue 侧 LSU fire = InputFIFO enq fire"
    由监控器 mismFire 计数器在两场景 144 拍全程钉死为 0。

  I 类审查（本范围逐行对照 pipe.scala:136-138/:169-171/:231/:241/:271/
  :288-289/:360-427、LSU.scala:530-586、issue.scala:98-139）：
  新发现 M-O3（标量访存 issueX 死锁，待主会话定级归档）；其余机制
  （ShiftBoard 门控、fence_end、LSU2WB 路由、rspArbiter 优先级）与模块级
  审查结论一致，未见新疑点。

  II 类：smmPackMask（LSU 侧 Fin 32 → Bool ⇒ MSHR 侧 BitVec 32）与解包
  （smmWbTagOf）的往返一致性未做符号定理，由两场景全掩码轨迹覆盖；
  部分掩码路径（发散分支内的访存）留待后续波次。

  III 类：5.1/6.1 的译码回归（机器码 → 译码行/寄存器号/路由/LSU 控制字
  切片）全部 native_decide 通过，排除了场景程序自身的编码错误。
-/

/- 公理审计：native_decide 定理带 Lean.ofReduceBool（预期，AGENTS.md 已备案） -/
#print axioms smmT_shreq_setidx_wire
#print axioms smmT_mshr_addrTag_wire
#print axioms smmT_mshr_dcvalid_wire
#print axioms smmT_wbValids_bit2
#print axioms smmT_wbVValids_bit2
#print axioms smmT_wbVValids_lsu_wire
#print axioms smmT_wbXValids_lsu_wire
#print axioms smmT_lsuRspRdy_wire
#print axioms smmT_boards_step_wire
#print axioms smmT_fenceEnd_wire
#print axioms smmTraceA_ok
#print axioms smmTraceB_ok

end Ventus
