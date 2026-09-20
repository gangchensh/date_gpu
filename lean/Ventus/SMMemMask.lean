/- ========================================================================= -/
/-                          SMMemMask.lean                                   -/
/-  部分掩码访存的整机轨迹：vbeq 发散 → 两条路径各在部分掩码下 vse32 →           -/
/-  汇合后全掩码 vle32 读回。消除 SMMem.lean §7 的留白（场景 A/B 均为全掩码）。  -/
/-                                                                           -/
/-  掩码链路（逐行对照）：                                                     -/
/-    pipe.scala:366        exe_dataV.mask = oc.mask & simt_stack.out_mask       -/
/-      （smwComb/smmComb 的 exeMaskV = smvMaskInit outVBits.vmask bj.tmask）；  -/
/-    LSU.scala:134 等      LsuVExe.mask（逐 lane Bool）→ AddrCalculate 的       -/
/-      active lane 过滤 → to_shared.perLaneAddr.active（SMMem M-D5）；          -/
/-    ShareMem.scala:145-154 perLaneAddr.active → DataAccess 写使能/字节使能     -/
/-      （被掩 lane 的 SRAM 不翻字节——本文件的 snapW1 断言在整机层钉死）；       -/
/-    LSU.scala:490-529     load 响应经 LSU2WB 的 wvd_mask 回写 vrf              -/
/-      （被掩 lane 的 vrf 行不更新——SMVecWb W-D3 已在 vALU 侧钉死同型事实）。   -/
/-                                                                           -/
/-  场景设计：vbeq v1,v2 使 lane0 发散（if_mask=0x00000001），两路径互补掩码     -/
/-  各写一笔 store 到不同 ShareMem 行（row0/row1），汇合后全掩码 load 读 row0：   -/
/-  lane0 读到 if 路径新值，lane1-31 读到从未被写的预置旧值——"被掩 lane 不写、   -/
/-  读回新/旧值按 lane 正确"两件事同时判收。                                    -/
/-                                                                           -/
/- ======================== Q 区（新踩坑/疑点/降级） ========================== -/
/-  Q1.（观察，非 bug 结论）本场景时间线 ldWb(44) 晚于 endprg(41)：endprg 不      -/
/-      等待 outstanding LSU load 的写回。单 warp 场景无害（v4 仍正确落值）；     -/
/-      若 warp 槽被新 CTA 复用且 sgpr/vgpr base 改变，滞留写回是否污染新 warp    -/
/-      的寄存器区，值得后续多 warp 场景验证（真实硬件靠软件在 endprg 前 fence    -/
/-      规避的可能性未排除——暂不列 I 类，记观察）。                             -/
/-  Q2.（踩坑）Array.set 走 Fin 索引重载要有效性证明；预置 SRAM 内容改用          -/
/-      Array.ofFn 逐行构造（sramInit 的 memArr 是 Array (Array (BitVec w))，    -/
/-      SramState.mem 是 getD 投影）。                                          -/
/- ========================================================================= -/

import Ventus.SMMem

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 场景：vbeq 发散 → 部分掩码 vse32×2 → 全掩码 vle32 读回                    -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 §2）：                                  -/
/-    0x00 lui  x1, 0x70000    ; 0x700000B7  x1 := 0x70000000（LDS 基址）      -/
/-    0x04 vbeq v1, v2, +0x40  ; 0x0420805B  else 目标 0x44；lane0 发散         -/
/-    0x08 vse32.v v3, (x1)    ; 0x0200E1A7  if 路径：掩码 0x1 写 row0 lane0    -/
/-    0x0C join                ; 0x0000205B  汇合点（simtRpc 注入值）           -/
/-    0x10 vle32.v v4, (x1)    ; 0x0200E207  汇合后全掩码读 row0 → v4           -/
/-    0x14 endprg              ; 0x0000400B                                   -/
/-    0x44 addi x2, x1, 0x80   ; 0x08008113  x2 := base+0x80（row1）           -/
/-    0x48 vse32.v v5, (x2)    ; 0x020162A7  else 路径：掩码 ~1 写 row1         -/
/-    0x4C jal  x0, -0x40      ; 0xFC1FF06F  跳回汇合点 0x0C                   -/
/-  数据（vgpr_base=16 ⇒ v_k 在 bank k%4、addr 4+k/4）：                        -/
/-    v1(b1,a4)=[1,5,…] 对比行；v2(b2,a4)=[5,…]；v3(b3,a4)=0xAB00+t（if 写）；  -/
/-    v5(b1,a5)=0xCD00+t（else 写）；v4(b0,a5)=load 目的。                      -/
/-  ShareMem 预置：row0/row1 全部 32 bank = 0xEE00+b（旧值标记）。              -/
/- ========================================================================= -/

/-- 数据行 -/
def smmmRowV1 : RfVRow := fun t => if t.val = 0 then 1#32 else 5#32
def smmmRowV2 : RfVRow := fun _ => 5#32
def smmmRowV3 : RfVRow := fun t => 0xAB00#32 + BitVec.ofNat 32 t.val
def smmmRowV5 : RfVRow := fun t => 0xCD00#32 + BitVec.ofNat 32 t.val

/-- 测试程序 -/
def smmmProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x700000B7#32
    else if pc = 0x04#32 then 0x0420805B#32
    else if pc = 0x08#32 then 0x0200E1A7#32
    else if pc = 0x0C#32 then 0x0000205B#32
    else if pc = 0x10#32 then 0x0200E207#32
    else if pc = 0x14#32 then 0x0000400B#32
    else if pc = 0x44#32 then 0x08008113#32
    else if pc = 0x48#32 then 0x020162A7#32
    else if pc = 0x4C#32 then 0xFC1FF06F#32
    else 0#32

/-- ShareMem 预置：row0/row1 每 bank 字 = 0xEE00+bank（小端：byte0=b,byte1=0xEE） -/
def smmmShmInit : Mem.SmState :=
  { Mem.smInit with
    banks := fun b =>
      let init := Mem.sramInit 1024 4 8
      let r : Array (BitVec 8) := #[BitVec.ofNat 8 b.val, 0xEE#8, 0#8, 0#8]
      { init with
        memArr := Array.ofFn fun (a : Fin 1024) =>
          if a.val == 0 || a.val == 1 then r else Array.replicate 4 0#8 } }

/-- 场景初始状态：vrf 预置 + tmask 全 1 + simtRpc=0x0C + ShareMem 预置 -/
def smmmS0 : SmmState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a =>
        if a.val = 4 then smmmRowV1 else if a.val = 5 then smmmRowV5 else rfVInit.mem a }
    else if i.val = 2 then { rfVInit with mem := fun a =>
        if a.val = 4 then smmmRowV2 else rfVInit.mem a }
    else if i.val = 3 then { rfVInit with mem := fun a =>
        if a.val = 4 then smmmRowV3 else rfVInit.mem a }
    else rfVInit).toArray
  let s := smmInitOf
    { base := { smInit with
        vrf := vrf
      , csr := { smInit.csr with simtRpc := 0x0C#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }
  { s with shm := smmmShmInit }

/-- 场景拍数 -/
def smmmN : Nat := 80

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr=0、vgpr=16），其后空转 -/
def smmmIns : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smmmN - 1) smInNop

/-- ShareMem bank b 第 row 行的字（小端字节拼装；smmShmWord 的行参数版） -/
def smmmShmWord (s : SmmState) (row : Nat) (b : Fin 32) : BitVec 32 :=
  if h : row < 1024 then Mem.smBytesToWord (fun j => (s.shm.banks b).mem ⟨row, h⟩ j)
  else 0#32

/- ========================================================================= -/
/- 2. 机器码译码回归（III 类自检）                                              -/
/- ========================================================================= -/

-- vbeq v1, v2, +0x40 @ 0x04：VBEQ 行、双发路由、imm=0x40（else 落 0x44）
example :
    let c := smDecode 0x0420805B#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "VBEQ")) && (c.regIdx1 == 1#8) &&
    (c.regIdx2 == 2#8) && (rfImmGen rfIMM_B c.inst 0#7 == 0x40#32) &&
    (issRoute (smToIssCtrl c) == [.vALU, .SIMT]) = true := by native_decide

-- vse32 v3, (x1)：vs3=3、rs1=1、M_XWR、路由 LSU
example :
    let c := smDecode 0x0200E1A7#32 0#3 0x08#32
    (c.row == (decRowOf decAllTables "VSE32_V")) && (c.regIdx3 == 3#8) &&
    (c.regIdx1 == 1#8) && (c.row.memCmd == 2#2) &&
    (issRoute (smToIssCtrl c) == [.LSU]) = true := by native_decide

-- vse32 v5, (x2)：vs3=5、rs1=2
example :
    let c := smDecode 0x020162A7#32 0#3 0x48#32
    (c.row == (decRowOf decAllTables "VSE32_V")) && (c.regIdx3 == 5#8) &&
    (c.regIdx1 == 2#8) && (issRoute (smToIssCtrl c) == [.LSU]) = true := by
  native_decide

-- vle32 v4, (x1)：vd=4、M_XRD、wvd
example :
    let c := smDecode 0x0200E207#32 0#3 0x10#32
    (c.row == (decRowOf decAllTables "VLE32_V")) && (c.regIdxw == 4#8) &&
    (c.row.memCmd == 1#2) && (c.row.wvd == true) = true := by native_decide

-- jal x0, -0x40 @ 0x4C：imm=-64（落 0x0C）
example :
    let c := smDecode 0xFC1FF06F#32 0#3 0x4C#32
    (c.row.branch == 2#2) && (rfImmGen rfIMM_J c.inst 0#7 == 0xFFFFFFC0#32) = true := by
  native_decide

/- ========================================================================= -/
/- 3. 监控器与轨迹判收                                                          -/
/- ========================================================================= -/

/-- 监控累积器：发散/掩码事件 + 被掩 lane 快照 + 终态判收 -/
structure SmmmChk where
  tick       : Nat
  vbrT       : Nat          -- vbeq SIMT fire 拍+1
  ifMask     : BitVec 32    -- 分支拍 if 掩码（应 0x00000001）
  elseMask   : BitVec 32    -- 分支拍 else 掩码（应 0xFFFFFFFE）
  tmAftVbr   : BitVec 32    -- 分支拍后 tmask（应 = ifMask，takeif）
  st1T       : Nat          -- if 路径 store fire 拍+1
  st1M0      : Bool         -- 其 LSU 掩码 lane0（应 true）
  st1M1      : Bool         -- 其 LSU 掩码 lane1（应 false）
  st2T       : Nat          -- else 路径 store fire 拍+1
  st2M0      : Bool         -- 其 LSU 掩码 lane0（应 false）
  st2M1      : Bool         -- 其 LSU 掩码 lane1（应 true）
  snapW0     : BitVec 32    -- st2 fire 拍 row0 bank0 快照（应 0xAB00，已写）
  snapW1     : BitVec 32    -- st2 fire 拍 row0 bank1 快照（应 0xEE01——被掩未写）
  snapR1W0   : BitVec 32    -- st2 fire 拍 row1 bank0 快照（应 0xEE00，未写）
  ldT        : Nat          -- load fire 拍+1
  ldWbT      : Nat          -- load wb_v fire 拍+1
  nShReq     : Nat          -- shared_req fire 总数（应 3：2 store + 1 load）
  mismFire   : Nat          -- fireLsu ≠ fifoEnqFire 拍数（应 0）
  endT       : Nat          -- endprg 拍+1
  finOk      : Bool
  deriving DecidableEq, Repr

def smmmChk0 : SmmmChk :=
  { tick := 0, vbrT := 0, ifMask := 0#32, elseMask := 0#32, tmAftVbr := 0#32
  , st1T := 0, st1M0 := false, st1M1 := false
  , st2T := 0, st2M0 := false, st2M1 := false
  , snapW0 := 0#32, snapW1 := 0#32, snapR1W0 := 0#32
  , ldT := 0, ldWbT := 0, nShReq := 0, mismFire := 0, endT := 0, finOk := false }

/-- 监控单拍 -/
def smmmMonStep (prog : SmProg) (acc : SmmmChk × SmmState) (inp : SmIn) :
    SmmmChk × SmmState :=
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
  let m2 := if c.fireVBr && m1.vbrT == 0 then
      { m1 with vbrT := t + 1, ifMask := c.ifMask, elseMask := c.elseMask
              , tmAftVbr := s'.base.base.bj.tmask }
    else m1
  let m3 := if c.fireLsu && isWrReq then
    if m2.st1T == 0 then
      { m2 with st1T := t + 1
              , st1M0 := c.lsuReqBits.mask ⟨0, by decide⟩
              , st1M1 := c.lsuReqBits.mask ⟨1, by decide⟩ }
    else if m2.st2T == 0 then
      { m2 with st2T := t + 1
              , st2M0 := c.lsuReqBits.mask ⟨0, by decide⟩
              , st2M1 := c.lsuReqBits.mask ⟨1, by decide⟩
              , snapW0 := smmmShmWord s 0 ⟨0, by decide⟩
              , snapW1 := smmmShmWord s 0 ⟨1, by decide⟩
              , snapR1W0 := smmmShmWord s 1 ⟨0, by decide⟩ }
    else m2
  else m2
  let m4 := if c.fireLsu && !isWrReq && m3.ldT == 0 then { m3 with ldT := t + 1 } else m3
  let m5 := if c.wbVFire && c.wbVChoice.val == 2 && m4.ldWbT == 0
      then { m4 with ldWbT := t + 1 } else m4
  (m5, s')

/-- 单遍跑完并给出全部检查结论（含终态判收） -/
def smmmRunChk (prog : SmProg) (ins : List SmIn) : SmmmChk :=
  let (m, sf) := ins.foldl (smmmMonStep prog) (smmmChk0, smmmS0)
  { m with finOk :=
      -- row0 全 32 bank per-lane 判收：bank0 = 0xAB00（if 路径新值），
      -- bank b≥1 = 0xEE00+b（被掩 lane 保留预置旧值）
      (List.finRange 32).all (fun b =>
        smmmShmWord sf 0 b ==
          (if b.val = 0 then 0xAB00#32 else 0xEE00#32 + BitVec.ofNat 32 b.val)) &&
      -- row1 全 32 bank per-lane 判收：bank0 = 0xEE00（else 写中被掩），
      -- bank b≥1 = 0xCD00+b（else 路径新值）
      (List.finRange 32).all (fun b =>
        smmmShmWord sf 1 b ==
          (if b.val = 0 then 0xEE00#32 else 0xCD00#32 + BitVec.ofNat 32 b.val)) &&
      -- v4 全 32 lane 读回判收：lane0 = 0xAB00（新值），lane t≥1 = 0xEE00+t（旧值）
      (List.finRange 32).all (fun t =>
        (smVrfAt sf.base.base ⟨0, by decide⟩).mem ⟨5, by decide⟩ t ==
          (if t.val = 0 then 0xAB00#32 else 0xEE00#32 + BitVec.ofNat 32 t.val)) &&
      -- warp 收尾与子系统归位
      (sf.base.base.ws.warpActive == 0#8) &&
      (sf.lsu.state == Mem.lsuSIdle) && (sf.fifoFull == false) &&
      (sf.mshr.used == 0#8) && (sf.boards 0#3 == 0#4) &&
      (m.mismFire == 0) && (m.nShReq == 3) }

/-- 期望结论（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1）：
    vbeq(9，takeif，tmask→0x1) → if-store(13，掩码 lane0) → else-store(25，
    掩码 lane1-31；同拍快照 row0=[0xAB00,0xEE01,…] 钉死被掩 lane 未写) →
    load(39) → endprg(41) → load 写回(44)。-/
def smmmExp : SmmmChk :=
  { tick := smmmN
  , vbrT := 9
  , ifMask := 0x00000001#32, elseMask := 0xFFFFFFFE#32, tmAftVbr := 0x00000001#32
  , st1T := 13, st1M0 := true, st1M1 := false
  , st2T := 25, st2M0 := false, st2M1 := true
  , snapW0 := 0xAB00#32, snapW1 := 0xEE01#32, snapR1W0 := 0xEE00#32
  , ldT := 39, ldWbT := 44
  , nShReq := 3, mismFire := 0, endT := 41
  , finOk := true }

/-- **场景主定理（部分掩码 LDS 写读，端到端）**：vbeq 发散后两条路径各在
    部分掩码（0x00000001 / 0xFFFFFFFE）下 vse32——被掩 lane 的 ShareMem 字节
    不翻（中迹快照 snapW1=0xEE01 钉死字节使能链）；汇合后全掩码 vle32 读回，
    v4 逐 lane = 新值（lane0）/旧值（lane1-31）；终态 ShareMem row0/row1 全
    32 bank per-lane 符合预期。对接引用：SMVec.lean `smvTrace_ok`（同一
    takeif+join×3 形态）、ShareMem.lean 字节使能写（smT1 系列）、
    SMMem.lean `smmTraceA_ok`（LSU/MSHR/LSU2WB 全链，本场景复用 smmComb）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smmmTrace_ok : smmmRunChk smmmProg smmmIns = smmmExp := by
  native_decide

/- ========================================================================= -/
/- 4. 公理审计                                                                 -/
/- ========================================================================= -/

#print axioms smmmTrace_ok

end Ventus
