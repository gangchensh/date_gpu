/- ========================================================================= -/
/-                     Schedule/I4Fix.lean                                   -/
/-  I-4 修复方案的形式化验证（本项目首个"修复即验证"任务）                       -/
/-                                                                           -/
/-  背景（doc/03-bug发现报告.md I-4，已闭环）：                                -/
/-    scoreboard.scala:115-118 中 `OpColRegV.set(op_colV_in_fire)` 后         -/
/-    `OpColRegV.clear(op_colV_out_fire)`，ScoreboardUtil 链式语义后写胜       -/
/-   （Scoreboard.lean 的 sb_clear_wins），同拍 in_fire+out_fire 时占用位      -/
/-    被错误清除 → 同 warp 第三条指令 C 可在 B 收集期间进入另一 CU 并抢先      -/
/-    发射（witness：OperandCollector.lean 的 ocI4_C_issues_before_B，ungated  -/
/-    2-CU 缩放系统）。                                                       -/
/-                                                                           -/
/-  修复（03 报告 I-4 修复建议之一）：:115-118 的 set/clear 程序序对调          -/
/-    （先清后置），即同拍合并语义改"置位胜"。本文件把修复版建为原模型的        -/
/-    变体（不动原文件），验证四件事：                                         -/
/-    (1) 修复有效性：同拍 in+out 后占用位保持 1（i4f_race_gone，对照          -/
/-        i4f_orig_race_loses）；位级规约 i4f_occFix_spec：                    -/
/-        occ' = in || (occ && !out)——占用位精确跟踪"该 warp 有指令在          -/
/-        collector 内"的事件流（一致性不变式的事件形式）。                    -/
/-    (2) 回归安全性：修复只改变竞态拍行为——无同拍 in+out 的输入序列上          -/
/-        修复版与原版本逐步等价（i4f_sbRun_equiv，归纳）；位级                -/
/-        i4f_swap_irrelevant（256 位一般形式）。                              -/
/-    (3) 组合层面：重建 2-CU 缩放 witness 系统并接上**真实门控**              -/
/-        （controlV.fire(w) 当拍要求 warp_ready(w)，而 warp_ready ⊇           -/
/-        ¬read_op_colV：pipe.scala:223/:161 + warp_schedule.scala:181 +       -/
/-        scoreboard.scala:131,142，全程组合无寄存器级）。修复版门控下：       -/
/-        "占用位 ⟺ 该 warp 有指令在 CU 内"是归纳不变式                        -/
/-        （i4fSys_run_inv_fix / i4f_occ_tracks_busy），且任意时刻至多一个     -/
/-        CU 持有该 warp 的指令（i4f_no_two_busy_fix）——乱序场景（C 先于 B     -/
/-        issue）的机制前提（两 CU 同时持有同 warp 指令）不成立                -/
/-        （i4f_witness_shape_unreachable）。                                  -/
/-    (4) 修复前后数值对照（第 6 节 native_decide）：ungated 下原版本竞态拍    -/
/-        占用位错误归零（i4fT_race_orig）、修复版保持（i4fT_race_fix）；      -/
/-        gated 下 witness 输入序列中 C 被门控拦截（i4fT_gated_C_blocked）；   -/
/-        gated 修复版完整顺序轨迹（i4fT_B_issues_first / i4fT_C_after_B）。   -/
/-                                                                           -/
/-  ★ 重要发现（上报主会话，关涉 03 报告 I-4 可达性段落）：门控是**全组合**    -/
/-    的（ibuffer→ibuffer2issue→controlV 无寄存器级，ibuffer.scala:42-101      -/
/-    RRArbiter 直连 + pipe.scala:288 直连），故 controlV.fire(w) 当拍         -/
/-    occ(w)=0；而 out_fire(w) 要求 w 的指令已在 CU 内（occ(w)=1）。同拍       -/
/-    in+out 需要 occ 当拍既 0 又 1——从复位起不可自举                          -/
/-    （i4fSys_run_eq_orig：门控下原版本与修复版逐步等价，竞态拍永不出现；     -/
/-    i4f_no_two_busy_orig：原版本门控下同样不会双占用）。即 I-4 的            -/
/-    "同拍 in+out 可达"论断依赖外围协议变化（如门控路径插入流水级）。修复     -/
/-    的意义是防御纵深：门控一旦被打破，修复版占用位仍正确（i4fT_race_fix）， -/
/-    而原版本立即产生"占用位=0 但指令在 CU 内"的破窗（i4fT_race_orig）。      -/
/-                                                                           -/
/-  公理审计：bv_decide 定理带每定理私有的 LRAT trust 公理；多拍数值测试用     -/
/-    native_decide（多 Lean.ofReduceBool），按 AGENTS.md 归档注明。           -/
/- ========================================================================= -/

import Ventus.Schedule.Scoreboard
import Ventus.Schedule.OperandCollector
import Std.Tactic.BVDecide

namespace Ventus.Schedule

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 修复版位级语义：同拍合并"置位胜"（先清后置）                              -/
/- ========================================================================= -/

/-- 修复版"先 clear 后 set"组合形式（对照 Scoreboard.lean 的 sbSetClear；
    对应 scoreboard.scala:115-118 的 set/clear 程序序对调） -/
def i4fSbClearSet {n : Nat} (zero : Bool) (r : BitVec n) (se : Bool) (sa : BitVec 8)
    (ce : Bool) (ca : BitVec 8) : BitVec n :=
  if se || ce then ((sbView zero r) &&& ~~~sbMask ce ca) ||| sbMask se sa else r

/-- 折叠形式与组合形式等价（对照 sbUtilStep_set_clear） -/
theorem i4f_sbUtilStep_clear_set {n : Nat} (z : Bool) (r : BitVec n) (se ce : Bool)
    (sa ca : BitVec 8) :
    sbUtilStep z r [.clear ce ca, .set se sa] = i4fSbClearSet z r se sa ce ca := by
  simp [sbUtilStep, i4fSbClearSet, sbApplyOp, SbOp.en, List.foldl, Bool.or_comm]

/-- 修复版 OpColReg 单拍（:115-118 对调后形态：先 clear 后 set） -/
def i4fSbOpColFix (r : BitVec 1) (inF outF : Bool) : BitVec 1 :=
  sbUtilStep false r [.clear outF 0#8, .set inF 0#8]

/-- 原版本 OpColReg 单拍（:115-118 现状：先 set 后 clear；对照用） -/
def i4fSbOpColOrig (r : BitVec 1) (inF outF : Bool) : BitVec 1 :=
  sbUtilStep false r [.set inF 0#8, .clear outF 0#8]

/- ========================================================================= -/
/- 2. 修复有效性                                                              -/
/- ========================================================================= -/

/-- 修复核心（符号）：同拍同址 set 与 clear，**set 胜**——无论同拍 clear
    针对何址，set 使能的地址在结果中读为 1（对照原版 sb_clear_wins）。 -/
theorem i4f_set_wins {r : BitVec 256} {ce : Bool} {a ca : BitVec 8} :
    sbRead false (i4fSbClearSet false r true a ce ca) a = true := by
  unfold sbRead sbView i4fSbClearSet sbMask
  bv_decide

/-- 修复不破坏正常清除：无同拍 set 时，clear 使能的地址结果读为 0 -/
theorem i4f_clear_works {r : BitVec 256} {sa a : BitVec 8} :
    sbRead false (i4fSbClearSet false r false sa true a) a = false := by
  unfold sbRead sbView i4fSbClearSet sbMask
  bv_decide

/-- **I-4 竞态消除**：同拍 in+out 后修复版占用位保持 1（任意前态 r） -/
theorem i4f_race_gone (r : BitVec 1) :
    i4fSbOpColFix r true true = 1#1 := by
  unfold i4fSbOpColFix
  rw [i4f_sbUtilStep_clear_set]
  unfold i4fSbClearSet sbView sbMask
  bv_decide

/-- 对照（原版本 bug 钉死）：同拍 in+out 后占用位被错误清 0（任意前态 r） -/
theorem i4f_orig_race_loses (r : BitVec 1) :
    i4fSbOpColOrig r true true = 0#1 := by
  unfold i4fSbOpColOrig
  rw [sbUtilStep_set_clear]
  unfold sbSetClear sbView sbMask
  bv_decide

/-- 修复版占用位事件规约（一致性不变式的事件形式）：
    occ' = in || (occ && !out)——"新占用"或"原有占用且未出队" -/
theorem i4f_occFix_spec (r : BitVec 1) (i o : Bool) :
    (i4fSbOpColFix r i o == 1#1) = (i || ((r == 1#1) && !o)) := by
  unfold i4fSbOpColFix
  rw [i4f_sbUtilStep_clear_set]
  unfold i4fSbClearSet sbView sbMask
  bv_decide

/-- 原版本占用位事件规约（对照）：occ' = (in || occ) && !out -/
theorem i4f_occOrig_spec (r : BitVec 1) (i o : Bool) :
    (i4fSbOpColOrig r i o == 1#1) = ((i || (r == 1#1)) && !o) := by
  unfold i4fSbOpColOrig
  rw [sbUtilStep_set_clear]
  unfold sbSetClear sbView sbMask
  bv_decide

-- 数值回归（位级，by decide）
theorem i4fT_bit_orig_race : i4fSbOpColOrig 1#1 true true = 0#1 := by decide
theorem i4fT_bit_fix_race  : i4fSbOpColFix 1#1 true true = 1#1 := by decide
theorem i4fT_bit_fix_clear : i4fSbOpColFix 1#1 false true = 0#1 := by decide
theorem i4fT_bit_fix_set   : i4fSbOpColFix 0#1 true false = 1#1 := by decide
theorem i4fT_bit_fix_hold  : i4fSbOpColFix 1#1 false false = 1#1 := by decide

/- ========================================================================= -/
/- 3. 回归安全性：修复版与原版本在无竞态输入上逐步等价                          -/
/- ========================================================================= -/

/-- 修复版 Scoreboard 单拍：**仅** OpColRegV/X 两处（:115-118）set/clear
    顺序对调，其余四个 util 与原版本逐字相同（vectorReg/scalarReg 的同拍
    同址 set+clear 由协议排除，见 Scoreboard.lean Q2，不属于 I-4 修复范围） -/
def i4fSbStepFix (s : SbState) (i : SbInputs) : SbState where
  vectorReg := sbUtilStep false s.vectorReg
    [.set (i.if_fire && i.if_ctrl.wvd) i.if_ctrl.reg_idxw,
     .clear (i.wb_v_fire && i.wb_v_wvd) i.wb_v_idxw]
  scalarReg := sbUtilStep true s.scalarReg
    [.set (i.if_fire && i.if_ctrl.wxd) i.if_ctrl.reg_idxw,
     .clear (i.wb_x_fire && i.wb_x_wxd) i.wb_x_idxw]
  beqReg := sbUtilStep false s.beqReg
    [.set (i.if_fire && (i.if_ctrl.branch != 0#2 || i.if_ctrl.barrier)) 0#8,
     .clear i.br_ctrl 0#8]
  opColV := i4fSbOpColFix s.opColV i.opColV_in i.opColV_out
  opColX := i4fSbOpColFix s.opColX i.opColX_in i.opColX_out
  fenceReg := sbUtilStep false s.fenceReg
    [.set (i.if_fire && i.if_ctrl.fence) 0#8, .clear i.fence_end 0#8]

/-- 修复版多拍运行 -/
def i4fSbRunFix (s : SbState) (ins : List SbInputs) : SbState :=
  ins.foldl i4fSbStepFix s

/-- 位级一般形式（256 位）：无同拍同址 set+clear 冲突时，先清后置与先置后清
    结果相同——修复只改变竞态拍的行为 -/
theorem i4f_swap_irrelevant {r : BitVec 256} {se ce : Bool} {sa ca : BitVec 8}
    (h : (se && ce && (sa == ca)) = false) :
    sbSetClear false r se sa ce ca = i4fSbClearSet false r se sa ce ca := by
  unfold sbSetClear i4fSbClearSet sbView sbMask
  bv_decide

/-- 1 位（OpColReg）形式：无同拍 in+out 时原版本 = 修复版 -/
theorem i4f_orig_eq_fix_of_no_race (r : BitVec 1) (i o : Bool) (h : (i && o) = false) :
    i4fSbOpColOrig r i o = i4fSbOpColFix r i o := by
  unfold i4fSbOpColOrig i4fSbOpColFix
  rw [sbUtilStep_set_clear, i4f_sbUtilStep_clear_set]
  unfold sbSetClear i4fSbClearSet sbView sbMask
  bv_decide

/-- 单拍等价：本拍 OpColV/X 均无同拍 in+out，则修复版单拍 = 原版本单拍 -/
theorem i4f_sbStepFix_eq_orig (s : SbState) (i : SbInputs)
    (hV : (i.opColV_in && i.opColV_out) = false)
    (hX : (i.opColX_in && i.opColX_out) = false) :
    i4fSbStepFix s i = sbStep s i := by
  simp only [i4fSbStepFix, sbStep, SbState.mk.injEq]
  refine ⟨trivial, trivial, trivial, ?_, ?_, trivial⟩
  · exact (i4f_orig_eq_fix_of_no_race s.opColV i.opColV_in i.opColV_out hV).symm
  · exact (i4f_orig_eq_fix_of_no_race s.opColX i.opColX_in i.opColX_out hX).symm

/-- **回归安全性（归纳）**：输入序列全程无同拍 in+out（V/X 两通道分别），
    则修复版与原版本整条轨迹逐步等价 -/
theorem i4f_sbRun_equiv (s : SbState) (ins : List SbInputs)
    (hV : ∀ j ∈ ins, (j.opColV_in && j.opColV_out) = false)
    (hX : ∀ j ∈ ins, (j.opColX_in && j.opColX_out) = false) :
    i4fSbRunFix s ins = sbRun s ins := by
  induction ins generalizing s with
  | nil => rfl
  | cons j js ih =>
    show i4fSbRunFix (i4fSbStepFix s j) js = sbRun (sbStep s j) js
    rw [i4f_sbStepFix_eq_orig s j (hV j List.mem_cons_self)
      (hX j List.mem_cons_self)]
    exact ih (sbStep s j)
      (fun k hk => hV k (List.mem_cons_of_mem j hk))
      (fun k hk => hX k (List.mem_cons_of_mem j hk))

-- 数值回归（记分板级，by decide）
/-- 无竞态序列：修复版与原版本占用位一致（in 序列） -/
theorem i4fT_sb_norace_in :
    (i4fSbRunFix sbInit [sbInOpColVIn]).opColV = (sbRun sbInit [sbInOpColVIn]).opColV := by decide
/-- 无竞态序列：修复版与原版本占用位一致（in 后 out） -/
theorem i4fT_sb_norace_inout :
    (i4fSbRunFix sbInit [sbInOpColVIn, sbInOpColVOut]).opColV =
      (sbRun sbInit [sbInOpColVIn, sbInOpColVOut]).opColV := by decide
/-- 竞态拍：原版本占用位被错误清 0 -/
theorem i4fT_sb_race_orig :
    (sbRun sbInit [{ sbInNop with opColV_in := true, opColV_out := true }]).opColV = 0#1 := by decide
/-- 竞态拍：修复版占用位保持 1 -/
theorem i4fT_sb_race_fix :
    (i4fSbRunFix sbInit [{ sbInNop with opColV_in := true, opColV_out := true }]).opColV = 1#1 := by decide

/- ========================================================================= -/
/- 4. 组合层面：带真实门控的 2-CU 缩放系统                                     -/
/-    门控依据：controlV.fire(w) ⟸ ibuffer2issue out_v.fire(w) ⟸              -/
/-    warp_ready(w)（pipe.scala:223）⟸ ¬scoreboard_busy(w)（pipe.scala:161,   -/
/-    warp_schedule.scala:181）⟸ ¬read_op_colV（scoreboard.scala:131,142）。  -/
/-    全程组合（ibuffer2issue 的 RRArbiter 直连 out_v，pipe.scala:288 直连     -/
/-    controlV），故门控与 controlV.fire 同拍——用 occ 当拍值门控即忠实模型。  -/
/-    输入抽象：offer=true 表示"ibuffer 头有该 warp 指令且其余阻塞源不命中"。  -/
/- ========================================================================= -/

/-- witness 系统状态：2 个 CU + 单 warp 的 OpColRegV 占用位 -/
structure I4fSysState where
  cu0 : CuState
  cu1 : CuState
  occ : BitVec 1

/-- 单拍输入：新指令提供 + bankIn(0) 返回（广播两 CU，缩放抽象，同 ocWitStep
    的共享 issueRdy 处理）+ 下游 issue ready -/
structure I4fSysIn where
  offer    : Bool
  bits     : CuCtrl
  bkV      : Bool
  bkB      : CuBankIn
  issueRdy : Bool

/-- CU 持有 warp 指令 ⟺ 状态非 s_idle（cuInv 排除 state=3 后即 s_add/s_out） -/
def i4fCuBusy (c : CuState) : Bool := !(c.state == cuSIdle)

/-- 两个 CU 的 control.ready（demux 的 outRdy） -/
def i4fRdy2 (c0 c1 : CuState) : Fin 2 → Bool :=
  fun j => if j.val = 0 then cuControlRdy c0 else cuControlRdy c1

/-- 送入 CU j 的单拍输入（bankIn 仅端口 0 可返回，其余端口恒无效） -/
def i4fCuIn (d : OcDemuxRes 2) (i : I4fSysIn) (j : Fin 2) : CuInputs :=
  ⟨d.valid j, d.bits j, i.bkV, false, false, false, i.bkB, cuBI0, cuBI0, cuBI0,
   i.issueRdy, cuSgprB, cuVgprB⟩

/-- 门控版 demux 决策：controlV.valid = offer ∧ 占用位当拍为 0 -/
def i4fDemuxD (s : I4fSysState) (i : I4fSysIn) : OcDemuxRes 2 :=
  ocDemux (i4fRdy2 s.cu0 s.cu1) (i.offer && (s.occ == 0#1)) false i.bits cuCtrl0

/-- Fin 2 的两个端口常量（统一定义，保证 rw 匹配时语法一致） -/
def i4fJ0 : Fin 2 := ⟨0, by decide⟩
def i4fJ1 : Fin 2 := ⟨1, by decide⟩

/-- 门控版单拍：f 为占用位单拍函数（修复版/原版本可替换）。
    occ 更新的事件：in = controlV.fire（pipe.scala:262）、out = out(0).fire
    （:263；本缩放系统中 DualIssueIO 仲裁简化为"任一 CU issue.fire"，在
    ≤1 CU 忙的不变式下与仲裁一致）。 -/
def i4fSysStepG (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (i : I4fSysIn) : I4fSysState :=
  let d := i4fDemuxD s i
  ⟨cuStep s.cu0 (i4fCuIn d i i4fJ0), cuStep s.cu1 (i4fCuIn d i i4fJ1),
   f s.occ ((i.offer && (s.occ == 0#1)) && d.in0Rdy)
     (cuIssueFire s.cu0 (i4fCuIn d i i4fJ0) || cuIssueFire s.cu1 (i4fCuIn d i i4fJ1))⟩

/-- 非门控版单拍（对照/破窗实验用；即 OperandCollector.lean ocWitStep 的
    语义 + 占用位跟踪） -/
def i4fSysStepU (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (i : I4fSysIn) : I4fSysState :=
  let d := ocDemux (i4fRdy2 s.cu0 s.cu1) i.offer false i.bits cuCtrl0
  ⟨cuStep s.cu0 (i4fCuIn d i i4fJ0), cuStep s.cu1 (i4fCuIn d i i4fJ1),
   f s.occ (i.offer && d.in0Rdy)
     (cuIssueFire s.cu0 (i4fCuIn d i i4fJ0) || cuIssueFire s.cu1 (i4fCuIn d i i4fJ1))⟩

/-- 多拍运行（门控版/非门控版） -/
def i4fSysRunG (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (ins : List I4fSysIn) : I4fSysState :=
  ins.foldl (i4fSysStepG f) s

def i4fSysRunU (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (ins : List I4fSysIn) : I4fSysState :=
  ins.foldl (i4fSysStepU f) s

/-- 初态：两 CU 空、占用位 0 -/
def i4fSysInit : I4fSysState := ⟨cuInit, cuInit, 0#1⟩

/-- 系统不变式：CU 各自的可达不变式（cuInv）+ **占用位 ⟺ 该 warp 有指令在
    collector 内** + 至多一个 CU 持有该 warp 的指令 -/
def i4fSysInv (s : I4fSysState) : Prop :=
  cuInv s.cu0 ∧ cuInv s.cu1 ∧
    ((s.occ == 1#1) = (i4fCuBusy s.cu0 || i4fCuBusy s.cu1)) ∧
    ¬(i4fCuBusy s.cu0 = true ∧ i4fCuBusy s.cu1 = true)

/- ---- 投影与接口引理 ---- -/

theorem i4fSysStepG_cu0 (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (i : I4fSysIn) :
    (i4fSysStepG f s i).cu0 = cuStep s.cu0 (i4fCuIn (i4fDemuxD s i) i i4fJ0) := rfl

theorem i4fSysStepG_cu1 (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (i : I4fSysIn) :
    (i4fSysStepG f s i).cu1 = cuStep s.cu1 (i4fCuIn (i4fDemuxD s i) i i4fJ1) := rfl

theorem i4fSysStepG_occ (f : BitVec 1 → Bool → Bool → BitVec 1) (s : I4fSysState)
    (i : I4fSysIn) :
    (i4fSysStepG f s i).occ =
      f s.occ ((i.offer && (s.occ == 0#1)) && (i4fDemuxD s i).in0Rdy)
        (cuIssueFire s.cu0 (i4fCuIn (i4fDemuxD s i) i i4fJ0) ||
          cuIssueFire s.cu1 (i4fCuIn (i4fDemuxD s i) i i4fJ1)) := rfl

/-- i4fCuIn 的 control.fire 只取决于 demux 的 valid 与本 CU 的 ready -/
theorem i4f_controlFire_cuIn (s : CuState) (d : OcDemuxRes 2) (i : I4fSysIn) (j : Fin 2) :
    cuControlFire s (i4fCuIn d i j) = (d.valid j && cuControlRdy s) := rfl

/-- i4fCuIn 的 issue.fire 只取决于本 CU 状态与共享 issueRdy -/
theorem i4f_issueFire_cuIn (s : CuState) (d : OcDemuxRes 2) (i : I4fSysIn) (j : Fin 2) :
    cuIssueFire s (i4fCuIn d i j) = ((s.state == cuSOut) && i.issueRdy) := rfl

/-- i4fCuIn 的 issueReady 字段归一化（rw 链语法对齐用） -/
theorem i4f_cuIn_issueReady (d : OcDemuxRes 2) (i : I4fSysIn) (j : Fin 2) :
    (i4fCuIn d i j).issueReady = i.issueRdy := rfl

/- ---- CU 级辅助引理 ---- -/

/-- BitVec 1 双值性（门控 Bool 化用） -/
theorem i4f_bv1_ne (x : BitVec 1) : (x == 0#1) = !(x == 1#1) := by bv_decide

/-- 状态互斥：s_add 与 s_out 不兼得 -/
theorem i4f_st_add_out_excl (st : BitVec 2) :
    ((st == cuSAdd) && (st == cuSOut)) = false := by
  unfold cuSAdd cuSOut
  bv_decide

/-- 可达状态下（cuInv）：CU 忙 ⟺ s_add 或 s_out -/
theorem i4f_busy_iff (s : CuState) (h : cuInv s) :
    i4fCuBusy s = ((s.state == cuSAdd) || (s.state == cuSOut)) := by
  obtain ⟨hne3, -, -, -⟩ := h
  rcases cuBv2_cases s.state with hs | hs | hs | hs
  · have h1 : (s.state == cuSIdle) = true := by simp [hs]
    have h2 : (s.state == cuSAdd) = false := by rw [hs]; decide
    have h3 : (s.state == cuSOut) = false := by rw [hs]; decide
    simp [i4fCuBusy, h1, h2, h3]
  · have h1 : (s.state == cuSIdle) = false := by rw [hs]; decide
    have h2 : (s.state == cuSAdd) = true := by simp [hs]
    simp [i4fCuBusy, h1, h2]
  · have h1 : (s.state == cuSIdle) = false := by rw [hs]; decide
    have h3 : (s.state == cuSOut) = true := by simp [hs]
    simp [i4fCuBusy, h1, h3]
  · exact absurd hs hne3

/-- 可达状态下（cuInv）：control.ready ⟺ 不忙（s_idle ⇒ valid=0） -/
theorem i4f_controlRdy_eq_not_busy (s : CuState) (h : cuInv s) :
    cuControlRdy s = !i4fCuBusy s := by
  obtain ⟨-, hid, -, -⟩ := h
  by_cases hs : (s.state == cuSIdle) = true
  · have hst : s.state = cuSIdle := beq_iff_eq.mp hs
    have hv : s.valid = 0#4 := hid hst
    simp [cuControlRdy, i4fCuBusy, hs, hv]
  · have hs' : (s.state == cuSIdle) = false := by
      cases hh : (s.state == cuSIdle) with
      | false => rfl
      | true => exact absurd hh hs
    simp [cuControlRdy, i4fCuBusy, hs']

/-- CU 忙位的单拍递推：接受即忙；s_add 保持忙；s_out 仅在 issue.fire 时转闲 -/
theorem i4f_cuStep_busy (s : CuState) (i : CuInputs) (h : cuInv s) :
    i4fCuBusy (cuStep s i) =
      (cuControlFire s i ||
        ((s.state == cuSAdd) || ((s.state == cuSOut) && !i.issueReady))) := by
  obtain ⟨hne3, -, -, -⟩ := h
  have hst := cuStep_state s i
  unfold i4fCuBusy
  rw [hst]
  unfold cuStateTrans cuControlFire cuControlRdy cuIssueFire cuIssueValid
    cuSIdle cuSAdd cuSOut
  generalize hgs : s.state = st
  rw [hgs] at hne3
  have h3 : (st == 3#2) = false := by
    cases hh : (st == 3#2) with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp hh) hne3
  generalize s.valid = v
  generalize s.ready = r
  generalize cuReadyWire i.ctrl = w
  generalize i.controlValid = cv
  generalize i.issueReady = ir
  bv_decide

/- ---- demux 引理（valid/in0Rdy 不依赖 bits，先剥离再数值化） ---- -/

/-- ocDemux 的 valid 字段定义展开（rfl） -/
theorem i4f_demux_valid_def {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool)
    (b0 b1 : CuCtrl) (j : Fin n) :
    (ocDemux outRdy in0V in1V b0 b1).valid j =
      ((ocOrR outRdy && decide (j.val = ocPrioLowest outRdy) && in0V) ||
        (ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) && in1V)) := rfl

/-- ocDemux 的 in0Rdy 字段定义展开（rfl） -/
theorem i4f_demux_in0Rdy_def {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool)
    (b0 b1 : CuCtrl) :
    (ocDemux outRdy in0V in1V b0 b1).in0Rdy = ocOrR outRdy := rfl

/-- CU0 收到 controlV ⟺ CU0 ready 且门控放行（最低 ready 优先，:497） -/
theorem i4f_demuxD_valid0 (s : I4fSysState) (i : I4fSysIn) :
    (i4fDemuxD s i).valid i4fJ0 = (cuControlRdy s.cu0 && (i.offer && (s.occ == 0#1))) := by
  unfold i4fDemuxD i4fRdy2
  rw [i4f_demux_valid_def]
  cases h0 : cuControlRdy s.cu0 <;> cases h1 : cuControlRdy s.cu1 <;>
    cases hp : (i.offer && (s.occ == 0#1)) <;> decide

/-- CU1 收到 controlV ⟺ CU0 不 ready、CU1 ready 且门控放行 -/
theorem i4f_demuxD_valid1 (s : I4fSysState) (i : I4fSysIn) :
    (i4fDemuxD s i).valid i4fJ1 =
      (!cuControlRdy s.cu0 && cuControlRdy s.cu1 && (i.offer && (s.occ == 0#1))) := by
  unfold i4fDemuxD i4fRdy2
  rw [i4f_demux_valid_def]
  cases h0 : cuControlRdy s.cu0 <;> cases h1 : cuControlRdy s.cu1 <;>
    cases hp : (i.offer && (s.occ == 0#1)) <;> decide

/-- controlV.ready ⟺ 任一 CU ready（:501） -/
theorem i4f_demuxD_in0Rdy (s : I4fSysState) (i : I4fSysIn) :
    (i4fDemuxD s i).in0Rdy = (cuControlRdy s.cu0 || cuControlRdy s.cu1) := by
  unfold i4fDemuxD i4fRdy2
  rw [i4f_demux_in0Rdy_def]
  cases h0 : cuControlRdy s.cu0 <;> cases h1 : cuControlRdy s.cu1 <;> decide

/- ========================================================================= -/
/- 5. 组合定理：不变式归纳 + 乱序不可能 + 门控下修复版≡原版本                   -/
/- ========================================================================= -/

theorem i4fSys_init_inv : i4fSysInv i4fSysInit :=
  ⟨cuInv_init, cuInv_init, by decide, by decide⟩

/-- **不变式单拍保持（修复版门控）** -/
theorem i4fSys_step_inv_fix (s : I4fSysState) (i : I4fSysIn) (h : i4fSysInv s) :
    i4fSysInv (i4fSysStepG i4fSbOpColFix s i) := by
  obtain ⟨hinv0, hinv1, hocc, hnot2⟩ := h
  have hb0 := i4f_busy_iff s.cu0 hinv0
  have hb1 := i4f_busy_iff s.cu1 hinv1
  have hr0 := i4f_controlRdy_eq_not_busy s.cu0 hinv0
  have hr1 := i4f_controlRdy_eq_not_busy s.cu1 hinv1
  have hoccB : (s.occ == 1#1) =
      (((s.cu0.state == cuSAdd) || (s.cu0.state == cuSOut)) ||
        ((s.cu1.state == cuSAdd) || (s.cu1.state == cuSOut))) := by
    rw [hocc, hb0, hb1]
  have hnot2B : ¬(((s.cu0.state == cuSAdd) || (s.cu0.state == cuSOut)) = true ∧
      ((s.cu1.state == cuSAdd) || (s.cu1.state == cuSOut)) = true) := by
    rw [← hb0, ← hb1]; exact hnot2
  have hx0 : ((s.cu0.state == cuSAdd) && (s.cu0.state == cuSOut)) = false :=
    i4f_st_add_out_excl _
  have hx1 : ((s.cu1.state == cuSAdd) && (s.cu1.state == cuSOut)) = false :=
    i4f_st_add_out_excl _
  have hcf0 : cuControlFire s.cu0 (i4fCuIn (i4fDemuxD s i) i i4fJ0) =
      (cuControlRdy s.cu0 && (i.offer && (s.occ == 0#1))) := by
    rw [i4f_controlFire_cuIn, i4f_demuxD_valid0]
    cases h0 : cuControlRdy s.cu0 <;> cases hp : (i.offer && (s.occ == 0#1)) <;> decide
  have hcf1 : cuControlFire s.cu1 (i4fCuIn (i4fDemuxD s i) i i4fJ1) =
      (!cuControlRdy s.cu0 && cuControlRdy s.cu1 && (i.offer && (s.occ == 0#1))) := by
    rw [i4f_controlFire_cuIn, i4f_demuxD_valid1]
    cases h0 : cuControlRdy s.cu0 <;> cases h1 : cuControlRdy s.cu1 <;>
      cases hp : (i.offer && (s.occ == 0#1)) <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cuInv_step s.cu0 _ hinv0
  · exact cuInv_step s.cu1 _ hinv1
  · -- 占用位 ⟺ busy（关键结合式：occ' = in || (occ && !out)，纯 Bool 验证）
    rw [i4fSysStepG_occ, i4f_occFix_spec, i4fSysStepG_cu0, i4fSysStepG_cu1,
      i4f_cuStep_busy _ _ hinv0, i4f_cuStep_busy _ _ hinv1, hcf0, hcf1,
      i4f_demuxD_in0Rdy, i4f_issueFire_cuIn, i4f_issueFire_cuIn,
      i4f_cuIn_issueReady, i4f_cuIn_issueReady, hr0, hr1, hb0, hb1, i4f_bv1_ne]
    revert hoccB hnot2B hx0 hx1
    generalize (s.cu0.state == cuSAdd) = a0
    generalize (s.cu0.state == cuSOut) = o0
    generalize (s.cu1.state == cuSAdd) = a1
    generalize (s.cu1.state == cuSOut) = o1
    generalize (s.occ == 1#1) = ob
    generalize i.offer = off
    generalize i.issueRdy = ir
    cases a0 <;> cases o0 <;> cases a1 <;> cases o1 <;> cases ob <;> cases off <;>
      cases ir <;> decide
  · -- 至多一个 CU 忙
    rw [i4fSysStepG_cu0, i4fSysStepG_cu1,
      i4f_cuStep_busy _ _ hinv0, i4f_cuStep_busy _ _ hinv1, hcf0, hcf1,
      i4f_cuIn_issueReady, i4f_cuIn_issueReady, hr0, hr1, hb0, hb1, i4f_bv1_ne]
    revert hoccB hnot2B hx0 hx1
    generalize (s.cu0.state == cuSAdd) = a0
    generalize (s.cu0.state == cuSOut) = o0
    generalize (s.cu1.state == cuSAdd) = a1
    generalize (s.cu1.state == cuSOut) = o1
    generalize (s.occ == 1#1) = ob
    generalize i.offer = off
    generalize i.issueRdy = ir
    cases a0 <;> cases o0 <;> cases a1 <;> cases o1 <;> cases ob <;> cases off <;>
      cases ir <;> decide

/-- **不变式归纳（修复版门控，任意输入序列）** -/
theorem i4fSys_run_inv_fix (s : I4fSysState) (ins : List I4fSysIn) (h : i4fSysInv s) :
    i4fSysInv (i4fSysRunG i4fSbOpColFix s ins) := by
  induction ins generalizing s with
  | nil => exact h
  | cons j js ih =>
    show i4fSysInv (i4fSysRunG i4fSbOpColFix (i4fSysStepG i4fSbOpColFix s j) js)
    exact ih _ (i4fSys_step_inv_fix s j h)

/-- **一致性不变式（run 形式）**：任意输入序列后，占用位 ⟺ 该 warp 有指令在
    collector 内 -/
theorem i4f_occ_tracks_busy (ins : List I4fSysIn) :
    ((i4fSysRunG i4fSbOpColFix i4fSysInit ins).occ == 1#1) =
      (i4fCuBusy (i4fSysRunG i4fSbOpColFix i4fSysInit ins).cu0 ||
        i4fCuBusy (i4fSysRunG i4fSbOpColFix i4fSysInit ins).cu1) :=
  (i4fSys_run_inv_fix i4fSysInit ins i4fSys_init_inv).2.2.1

/-- **I-4 乱序不可能（修复版门控）**：任意输入序列后，不存在两个 CU 同时持有
    该 warp 的指令——乱序场景（C 先于 B issue，ocI4_C_issues_before_B）的
    机制前提不成立 -/
theorem i4f_no_two_busy_fix (ins : List I4fSysIn) :
    ¬(i4fCuBusy (i4fSysRunG i4fSbOpColFix i4fSysInit ins).cu0 = true ∧
      i4fCuBusy (i4fSysRunG i4fSbOpColFix i4fSysInit ins).cu1 = true) :=
  (i4fSys_run_inv_fix i4fSysInit ins i4fSys_init_inv).2.2.2

/-- witness 的具体形态（CU0 持 B 滞留 s_add、CU1 持 C 可发射 s_out）在修复版
    门控下不可达 -/
theorem i4f_witness_shape_unreachable (ins : List I4fSysIn) :
    ¬((i4fSysRunG i4fSbOpColFix i4fSysInit ins).cu0.state = cuSAdd ∧
      (i4fSysRunG i4fSbOpColFix i4fSysInit ins).cu1.state = cuSOut) := by
  intro ⟨h0, h1⟩
  exact i4f_no_two_busy_fix ins
    ⟨by rw [i4fCuBusy, h0]; decide, by rw [i4fCuBusy, h1]; decide⟩

/-- 门控下不变式 ⟹ 本拍无竞态（in ⟹ occ=0；out ⟹ 有 CU 在 s_out ⟹ occ=1），
    故修复版与原版本单拍相同 -/
theorem i4fSys_step_eq_orig (s : I4fSysState) (i : I4fSysIn) (h : i4fSysInv s) :
    i4fSysStepG i4fSbOpColFix s i = i4fSysStepG i4fSbOpColOrig s i := by
  obtain ⟨hinv0, hinv1, hocc, hnot2⟩ := h
  have hb0 := i4f_busy_iff s.cu0 hinv0
  have hb1 := i4f_busy_iff s.cu1 hinv1
  have houtF_occ : ((s.cu0.state == cuSOut) || (s.cu1.state == cuSOut)) = true →
      (s.occ == 0#1) = false := by
    intro ho
    have hbusy : (i4fCuBusy s.cu0 || i4fCuBusy s.cu1) = true := by
      rw [hb0, hb1]
      cases h0 : (s.cu0.state == cuSOut) <;> cases h1 : (s.cu1.state == cuSOut) <;>
        simp_all
    have h1 : (s.occ == 1#1) = true := hocc.trans hbusy
    rw [i4f_bv1_ne, h1]
    decide
  have hnr : (((i.offer && (s.occ == 0#1)) && (i4fDemuxD s i).in0Rdy) &&
      (cuIssueFire s.cu0 (i4fCuIn (i4fDemuxD s i) i i4fJ0) ||
        cuIssueFire s.cu1 (i4fCuIn (i4fDemuxD s i) i i4fJ1))) = false := by
    rw [i4f_issueFire_cuIn, i4f_issueFire_cuIn]
    by_cases ho : ((s.cu0.state == cuSOut) || (s.cu1.state == cuSOut)) = true
    · -- out 侧可能 fire：不变式 ⟹ occ=1 ⟹ 门控关闭（in 侧为 false）
      have hf := houtF_occ ho
      simp [hf]
    · -- out 侧两析取支均 false，整个 out 事件为 false
      have ho' : ((s.cu0.state == cuSOut) || (s.cu1.state == cuSOut)) = false := by
        cases hh : ((s.cu0.state == cuSOut) || (s.cu1.state == cuSOut)) with
        | false => rfl
        | true => exact absurd hh ho
      have h0 : (s.cu0.state == cuSOut) = false := by
        cases hh : (s.cu0.state == cuSOut) with
        | false => rfl
        | true => rw [hh] at ho'; simp at ho'
      have h1 : (s.cu1.state == cuSOut) = false := by
        cases hh : (s.cu1.state == cuSOut) with
        | false => rfl
        | true => rw [hh] at ho'; simp at ho'
      simp [h0, h1]
  -- 仅 occ 字段不同；无竞态时两版占用位更新相同
  simp only [i4fSysStepG, I4fSysState.mk.injEq]
  exact ⟨trivial, trivial, (i4f_orig_eq_fix_of_no_race s.occ _ _ hnr).symm⟩

/-- **门控下修复版与原版本逐步等价（run 形式）**——竞态拍在门控下从复位起
    不可自举：controlV.fire(w) 当拍要求 occ(w)=0（全组合门控），而
    out_fire(w) 要求 occ(w)=1（w 的指令在 CU 内） -/
theorem i4fSys_run_eq_orig (s : I4fSysState) (ins : List I4fSysIn) (h : i4fSysInv s) :
    i4fSysRunG i4fSbOpColFix s ins = i4fSysRunG i4fSbOpColOrig s ins := by
  induction ins generalizing s with
  | nil => rfl
  | cons j js ih =>
    show i4fSysRunG i4fSbOpColFix (i4fSysStepG i4fSbOpColFix s j) js =
      i4fSysRunG i4fSbOpColOrig (i4fSysStepG i4fSbOpColOrig s j) js
    rw [i4fSys_step_eq_orig s j h]
    exact ih _ (i4fSys_step_eq_orig s j h ▸ i4fSys_step_inv_fix s j h)

/-- 推论：原版本门控下同样不会双占用（竞态不可达 + 不变式自保持） -/
theorem i4f_no_two_busy_orig (ins : List I4fSysIn) :
    ¬(i4fCuBusy (i4fSysRunG i4fSbOpColOrig i4fSysInit ins).cu0 = true ∧
      i4fCuBusy (i4fSysRunG i4fSbOpColOrig i4fSysInit ins).cu1 = true) := by
  rw [← i4fSys_run_eq_orig i4fSysInit ins i4fSys_init_inv]
  exact i4f_no_two_busy_fix ins

/- ========================================================================= -/
/- 6. 数值回归（修复前后对照；多拍轨迹用 native_decide）                        -/
/- ========================================================================= -/

/-- witness 输入：拍 T warp5 的 B（向量读，滞留 s_add）到达 -/
def i4fW0 : I4fSysIn := ⟨true, ocI4ctrlB, false, cuBI0, false⟩
/-- 拍 T+1：同 warp 的 C（全立即数）到达 -/
def i4fW1 : I4fSysIn := ⟨true, ocI4ctrlC, false, cuBI0, false⟩
/-- 拍 T+2：下游 issue ready -/
def i4fW2 : I4fSysIn := ⟨false, cuCtrl0, false, cuBI0, true⟩

/-- gated 修复版 witness 重放终态 -/
def i4fWs3 := i4fSysRunG i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]

/-- **witness 轨迹在修复版门控下不再乱序**：C 被门控拦截（CU1 始终空闲），
    B 滞留 CU0 的 s_add，占用位保持 1（对照 OperandCollector.lean 的
    ocI4_C_issues_before_B：ungated 时 C 拍 T+2 已可发射） -/
theorem i4fT_gated_C_blocked :
    i4fWs3.cu1.state = cuSIdle ∧ i4fWs3.cu0.state = cuSAdd ∧
      i4fWs3.cu0.controlReg = ocI4ctrlB ∧ i4fWs3.occ = 1#1 := by native_decide

/-- gated 下原版本与修复版数值一致（本序列无竞态，印证 i4fSys_run_eq_orig） -/
theorem i4fT_gated_fix_eq_orig :
    (i4fSysRunG i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).occ =
      (i4fSysRunG i4fSbOpColOrig i4fSysInit [i4fW0, i4fW1, i4fW2]).occ ∧
    (i4fSysRunG i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).cu0.state =
      (i4fSysRunG i4fSbOpColOrig i4fSysInit [i4fW0, i4fW1, i4fW2]).cu0.state ∧
    (i4fSysRunG i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).cu1.state =
      (i4fSysRunG i4fSbOpColOrig i4fSysInit [i4fW0, i4fW1, i4fW2]).cu1.state := by
  native_decide

/-- 竞态拍输入（ungated）：拍 T 全立即数指令 A 进 CU0（接受拍直进 s_out） -/
def i4fU0 : I4fSysIn := ⟨true, ocI4ctrlC, false, cuBI0, false⟩
/-- 拍 T+1：A 经 out(0) 发射（out_fire）同拍 B 被 CU1 接收（in_fire）——竞态 -/
def i4fU1 : I4fSysIn := ⟨true, ocI4ctrlB, false, cuBI0, true⟩

/-- **破窗对照（ungated 原版本）**：竞态拍后占用位被错误清 0，而 B 仍在
    CU1 的 s_add——"占用位=0 但指令在 collector 内"的 I-4 破窗态 -/
theorem i4fT_race_orig :
    (i4fSysRunU i4fSbOpColOrig i4fSysInit [i4fU0, i4fU1]).occ = 0#1 ∧
      (i4fSysRunU i4fSbOpColOrig i4fSysInit [i4fU0, i4fU1]).cu1.state = cuSAdd ∧
      (i4fSysRunU i4fSbOpColOrig i4fSysInit [i4fU0, i4fU1]).cu1.controlReg = ocI4ctrlB := by
  native_decide

/-- **修复有效（ungated 修复版）**：同一竞态拍后占用位保持 1，正确跟踪
    CU1 内的 B -/
theorem i4fT_race_fix :
    (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fU0, i4fU1]).occ = 1#1 ∧
      (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fU0, i4fU1]).cu1.state = cuSAdd ∧
      (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fU0, i4fU1]).cu1.controlReg = ocI4ctrlB := by
  native_decide

/-- ungated 下即便修复版占用位正确，collector 内部无同 warp 去重（:566 死
    代码）仍乱序：C 拍 T+2 已发射离开（回 s_idle），B 仍滞留 s_add——
    印证修复通过门控起作用，与报告修复建议二（恢复 widCmp 去重）互补 -/
theorem i4fT_ungated_fix_still_oob :
    (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).cu1.state = cuSIdle ∧
      (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).cu1.controlReg = ocI4ctrlC ∧
      (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).cu0.state = cuSAdd ∧
      (i4fSysRunU i4fSbOpColFix i4fSysInit [i4fW0, i4fW1, i4fW2]).cu0.controlReg = ocI4ctrlB := by
  native_decide

/-- 顺序恢复的正例轨迹（gated 修复版）：B（向量读）先进 CU0，C 被门控至 B
    发射后才进入 -/
def i4fP0 : I4fSysIn := ⟨true, ocI4ctrlB, false, cuBI0, false⟩   -- B 到达
def i4fP1 : I4fSysIn := ⟨true, ocI4ctrlC, true, cuBI0, false⟩    -- C 被拦截；bankIn 返回 B 的 rs1
def i4fP2 : I4fSysIn := ⟨true, ocI4ctrlC, false, cuBI0, false⟩   -- C 被拦截；B 集齐
def i4fP3 : I4fSysIn := ⟨true, ocI4ctrlC, false, cuBI0, true⟩    -- C 被拦截；B 发射
def i4fP4 : I4fSysIn := ⟨true, ocI4ctrlC, false, cuBI0, false⟩   -- C 进入 CU0

def i4fPs4 := i4fSysRunG i4fSbOpColFix i4fSysInit [i4fP0, i4fP1, i4fP2, i4fP3]
def i4fPs5 := i4fSysRunG i4fSbOpColFix i4fSysInit [i4fP0, i4fP1, i4fP2, i4fP3, i4fP4]

/-- B 先发射：B 的 issue 完成后 CU0 回 s_idle、占用位清 0，CU1 全程空闲 -/
theorem i4fT_B_issues_first :
    i4fPs4.cu0.state = cuSIdle ∧ i4fPs4.occ = 0#1 ∧ i4fPs4.cu1.state = cuSIdle := by
  native_decide

/-- C 严格在 B 发射后才进入 collector 并到达 s_out（程序序保持） -/
theorem i4fT_C_after_B :
    i4fPs5.cu0.state = cuSOut ∧ i4fPs5.cu0.controlReg = ocI4ctrlC ∧
      i4fPs5.cu1.state = cuSIdle := by native_decide

/- ========================================================================= -/
/- 7. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms i4f_set_wins
#print axioms i4f_clear_works
#print axioms i4f_race_gone
#print axioms i4f_orig_race_loses
#print axioms i4f_occFix_spec
#print axioms i4f_occOrig_spec
#print axioms i4f_swap_irrelevant
#print axioms i4f_orig_eq_fix_of_no_race
#print axioms i4f_sbStepFix_eq_orig
#print axioms i4f_sbRun_equiv
#print axioms i4f_cuStep_busy
#print axioms i4fSys_step_inv_fix
#print axioms i4fSys_run_inv_fix
#print axioms i4f_occ_tracks_busy
#print axioms i4f_no_two_busy_fix
#print axioms i4f_witness_shape_unreachable
#print axioms i4fSys_step_eq_orig
#print axioms i4fSys_run_eq_orig
#print axioms i4f_no_two_busy_orig
#print axioms i4fT_gated_C_blocked
#print axioms i4fT_race_orig
#print axioms i4fT_race_fix
#print axioms i4fT_ungated_fix_still_oob
#print axioms i4fT_B_issues_first
#print axioms i4fT_C_after_B

end Ventus.Schedule
