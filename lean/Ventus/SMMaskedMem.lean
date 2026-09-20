/- ========================================================================= -/
/-                        SMMaskedMem.lean                                   -/
/-  I-12 死锁的整机级演示：一条 vm=0 的 masked 向量访存指令（vle32.v v2,       -/
/-  (x1), v0.t）进入 collectorUnit 后，mask 读请求的 rsType(3)=0 被 bank       -/
/-  双仲裁器滤除（operandCollector.scala:214 vs :362-365），crossbar 永不       -/
/-  返回 regOrder=3 ⇒ CU 永停 s_add、control.ready 不恢复、该 warp 的          -/
/-  OpColV 永不清除 ⇒ warp 永滞、endprg 永不发射、LSU/ShareMem 全程无请求。    -/
/-                                                                           -/
/-  既有证据链（本文件是其整机层收口，非重复）：                                -/
/-    CU 级：CollectorUnit.lean `cuWmask_deadlock`（无 regOrder=3 返回 ⇒        -/
/-      永停 s_add 且 control.ready=false）；                                  -/
/-    OC 系统级：OperandCollector.lean `ocA_filter_rt0`/`ocA_no_grant3`/       -/
/-      `ocXbar_port3_never_valid`/`ocI12_deadlock_system`；                   -/
/-    模块级结论见 doc/03-bug发现报告.md I-12【已确认】。                      -/
/-  本文件新增：在 SMMem.lean 的全机组合（warp_sche/ibuffer/记分板/CU×8/       -/
/-  bank 仲裁/crossbar/寄存器堆/LSU/ShareMem/MSHR 全真）下，真实机器码程序      -/
/-  驱动出同一死锁形态，并给出有界停滞 witness（见 §4 注释）。                 -/
/-                                                                           -/
/-  命名说明：任务简报要求 smmm 前缀；SMMemMask.lean（波 26，部分掩码正常      -/
/-  通路轨迹）已占用 smmm* 原名（smmmProg/smmmTrace_ok 等），本文件采用        -/
/-  smmmDl*（dl = deadlock）以避免集成时撞名。                                -/
/-                                                                           -/
/-  简报任务 B(b) 的交代：vmsbf 类 mask 生成指令不在 DecodeUnit 译码表内       -/
/-  （掩码相关仅 VMERGE_VVM/VXM/VIM 三行，且 VMERGE 因 disableMask=N 强制      -/
/-  mask=1，本身即 I-12 受害者——"生成 mask 再被 masked 访存消费"的场景在       -/
/-  本硬件上不可达，消费侧必死锁）；带掩码写回语义的组合（wbVMaskFn、被掩      -/
/-  lane 不写）已由 SMMemMask.lean 的 vbeq 发散 + 部分掩码 vse32/vle32 轨迹    -/
/-  （smmmTrace_ok）覆盖。故本文件只做 B(a)：I-12 整机死锁 witness。           -/
/- ========================================================================= -/

import Ventus.SMMem

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 场景：lui（备地址）→ masked vle32（vm=0，I-12 现场）→ endprg（不可达）    -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 §2）：                                  -/
/-    0x00 lui  x1, 0x70000        ; 0x700000B7  x1 := 0x70000000（LDS 基址）  -/
/-    0x04 vle32.v v2, (x1), v0.t  ; 0x0000E107  vm=0 ⇒ decode mask=1          -/
/-                                   （= 场景 A 的 0x0200E107 清 bit25）       -/
/-    0x08 endprg                  ; 0x0000400B  永不可达（记分板 opColV 不清）  -/
/- ========================================================================= -/

/-- I-12 死锁演示程序 -/
def smmmDlProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x700000B7#32
    else if pc = 0x04#32 then 0x0000E107#32
    else if pc = 0x08#32 then 0x0000400B#32
    else 0#32

/-- 初始状态：无 vrf 预置（load 永不写回，终态 v2 应保持全 0 初值）+ tmask 全 1 -/
def smmmDlS0 : SmmState :=
  smmInitOf
    { base := { smInit with
        csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- 场景拍数（接受发生在拍 5（accT=6），其后 34 拍全为停滞 witness） -/
def smmmDlN : Nat := 40

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr=0、vgpr=16），其后全空转 -/
def smmmDlIns : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smmmDlN - 1) smInNop

/- ========================================================================= -/
/- 2. 机器码译码回归（III 类自检）                                              -/
/- ========================================================================= -/

-- masked vle32（vm=0）：VLE32_V 行、vd=2、rs1=1、M_XRD、wvd、isvec、路由 LSU，
-- 关键差异：**smMaskOf = true**（vm=0 ⇒ DecodeUnit.scala:588 的 ~inst(25) 项置位）
example :
    let c := smDecode 0x0000E107#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "VLE32_V")) && (c.regIdxw == 2#8) &&
    (c.regIdx1 == 1#8) && (c.row.memCmd == 1#2) && (c.row.wvd == true) &&
    (c.row.isvec == true) && (issRoute (smToIssCtrl c) == [.LSU]) &&
    (smMaskOf c.inst c.row == true) = true := by native_decide

-- 对照：同指令 vm=1（0x0200E107，场景 A 用过的）mask=false——唯 bit25 之差决定生死
example :
    let c := smDecode 0x0200E107#32 0#3 0x04#32
    (smMaskOf c.inst c.row == false) && (issRoute (smToIssCtrl c) == [.LSU]) = true := by
  native_decide

/- ========================================================================= -/
/- 3. 监控器与有界停滞 witness                                                 -/
/- ========================================================================= -/

/-- 监控累积器：死锁事件与停滞计数 -/
structure SmmmDlChk where
  tick       : Nat
  accT       : Nat          -- masked load 被某 CU 接受（control.fire）拍+1（0=未发生）
  accCu      : Fin 8        -- 接受它的 CU 编号
  stuck      : Nat          -- 接受后该 CU 处于 s_add 的拍数（应 = N - accT）
  nLsu       : Nat          -- lsu_req.fire 总数（应 0：请求永远到不了 LSU）
  nSh        : Nat          -- shared_req.fire 总数（应 0）
  nMskRsp    : Nat          -- 任一 CU 收到 regOrder=3 bank 返回的拍数（应 0，根因钉死）
  endT       : Nat          -- endprg 发射拍+1（应 0：warp 永滞）
  finOk      : Bool
  deriving DecidableEq, Repr

def smmmDlChk0 : SmmmDlChk :=
  { tick := 0, accT := 0, accCu := ⟨0, by decide⟩, stuck := 0
  , nLsu := 0, nSh := 0, nMskRsp := 0, endT := 0, finOk := false }

/-- 监控单拍 -/
def smmmDlMonStep (prog : SmProg) (acc : SmmmDlChk × SmmState) (inp : SmIn) :
    SmmmDlChk × SmmState :=
  let (m, s) := acc
  let c := smmComb prog s inp
  let s' := smmStep prog s inp
  let t := m.tick
  -- 根因观测量：本拍是否有任一 CU 的任一 bankIn 端口收到 regOrder=3 的返回
  -- （ocXbar_port3_never_valid 的整机计数版；rsType=0 被双仲裁器滤除 ⇒ 恒 0）
  let mskRsp : Bool := (List.finRange 8).any fun j =>
    let ci := c.cuIn j
    (ci.bv0 && (ci.bb0.regOrder == 3#2)) || (ci.bv1 && (ci.bb1.regOrder == 3#2)) ||
    (ci.bv2 && (ci.bb2.regOrder == 3#2)) || (ci.bv3 && (ci.bb3.regOrder == 3#2))
  -- masked load（tag=1，pc 0x04）被某 CU 接受的事件（control.fire；全程序唯一向量指令）
  let accJ : Option (Fin 8) := (List.finRange 8).find? fun j =>
    (c.cuIn j).controlValid && ((c.cuIn j).ctrl.tag == 1#8)
  let m1 := { m with
      tick := t + 1
    , nLsu := m.nLsu + (if c.fireLsu then 1 else 0)
    , nSh := m.nSh + (if c.lsuShFire then 1 else 0)
    , nMskRsp := m.nMskRsp + (if mskRsp then 1 else 0)
    , endT := if c.fireWs && (c.outXWid == 0#3) && (m.endT == 0) then t + 1 else m.endT }
  let m2 := match accJ with
    | some j => if m1.accT == 0 then { m1 with accT := t + 1, accCu := j } else m1
    | none => m1
  -- 停滞计数：接受拍（t = accT-1）观测的还是接受前的 s_idle；拍 t ≥ accT 起
  -- 组合输入状态里的该 CU 应恒处 s_add（永不停滞逃逸）
  let m3 := if (m2.accT != 0) && Nat.ble m2.accT t &&
        ((smCuAt s.base.base m2.accCu).state == cuSAdd)
      then { m2 with stuck := m2.stuck + 1 } else m2
  (m3, s')

/-- 单遍跑完并给出全部检查结论（含终态判收） -/
def smmmDlRunChk (prog : SmProg) (ins : List SmIn) : SmmmDlChk :=
  let (m, sf) := ins.foldl (smmmDlMonStep prog) (smmmDlChk0, smmmDlS0)
  let cu := smCuAt sf.base.base m.accCu
  { m with finOk :=
      -- 接受确实发生
      (m.accT != 0) &&
      -- 有界停滞 witness：接受后每一拍该 CU 都在 s_add（40 拍窗口内零逃逸）
      (m.stuck + m.accT == smmmDlN) &&
      -- 死锁的可观测后果：访存子系统全程静默、warp 永不结束
      (m.nLsu == 0) && (m.nSh == 0) && (m.endT == 0) &&
      -- 根因计数：全程无任何 regOrder=3 的 bank 返回（I-12 过滤的整机投影）
      (m.nMskRsp == 0) &&
      -- 终态 CU 形态：滞留 s_add、仍持有该指令（tag=1 ⇔ pc 0x04）、
      -- mask 槽 rsType3=0（operandCollector.scala:214 的现场）、
      -- valid(3)=1（在等 mask 操作数）、ready(3)=0（永远等不到）、
      -- control.ready=false（CU 被永久占用）
      (cu.state == cuSAdd) &&
      (cu.controlReg.tag == 1#8) &&
      (cu.rsType3 == 0#2) &&
      (((cu.valid >>> 3#4) &&& 1#4) == 1#4) &&
      (((cu.ready >>> 3#4) &&& 1#4) == 0#4) &&
      (cuControlRdy cu == false) &&
      -- warp 永滞：warp0 仍活跃（endprg 未发射）、记分板 OpColV 未清除
      (sf.base.base.ws.warpActive == 1#8) &&
      (sbReadOpColV (sf.base.base.sb ⟨0, by decide⟩) == true) &&
      -- load 永不写回：v2（vgpr_base=16 ⇒ bank2 addr4）全 lane 保持初值 0
      ((List.finRange 32).all fun t =>
        (smVrfAt sf.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == 0#32) }

/- ========================================================================= -/
/- 4. 主定理                                                                   -/
/-                                                                           -/
/-  有界停滞 witness 的读法（死锁的可观测截断）：                                -/
/-  拍 0 派发后环境输入恒为 smInNop——模型输入空间内除新 CTA 派发（reqFire）     -/
/-  外无其他环境自由度，而 warp0 死锁与新派发正交（派发只动其他 warp 槽位与     -/
/-  CSR 基址）。stuck + accT = N 表示：自接受拍起，窗口内每一拍该 CU 都停在     -/
/-  s_add，且期间 LSU/ShareMem 零请求、endprg 零发射、OpColV 零清除——这正是    -/
/-  cuWmask_deadlock（CU 级"永不"）在 40 拍有限窗口内的可观测截断。            -/
/-  无限延伸由模块级定理闭环：ocI12_deadlock_system 已证明 crossbar 真实驱动    -/
/-  下 regOrder=3 永不返回（与输入无关），故该停滞形态对所有后续拍保持。        -/
/- ========================================================================= -/

/-- 接受拍钉死（文档化用；accT = 拍号+1） -/
example : (smmmDlRunChk smmmDlProg smmmDlIns).accT = 6 := by native_decide

/-- **I-12 整机级死锁演示**：vm=0 的 vle32.v 经全机真实链路（取指 → ibuffer →
    ibuffer2issue → demux → CU 接受）后，mask 读请求 rsType(3)=0 被 bank
    双仲裁器滤除（全程零 regOrder=3 返回），CU 永停 s_add、valid(3)=1、
    ready(3)=0、control.ready 不恢复；LSU/ShareMem 全程零请求；warp0 的
    OpColV 永不清除、endprg 永不发射、warp 永不退役；v2 永不写回。
    一条比特之差（inst(25)：vm）区分正常通路（SMMem 场景 A，64 拍完成写读）
    与永久死锁（本场景）。接受拍 = 5（上条 example 钉死 accT=6=拍号+1）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smmmDlTrace_deadlock :
    (smmmDlRunChk smmmDlProg smmmDlIns).finOk = true := by
  native_decide

/- ========================================================================= -/
/- 5. 公理审计                                                                 -/
/- ========================================================================= -/

#print axioms smmmDlTrace_deadlock

end Ventus
