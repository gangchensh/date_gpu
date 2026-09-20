/- ========================================================================= -/
/-                     SIMT/PCcontrol.lean                                   -/
/-  SIMT 每 warp PC/取指掩码寄存器 PCcontrol 的 Lean 4 模型（WP1 收尾小件）   -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/PCcontrol.scala     -/
/-  例化上下文（已核实）：                                                    -/
/-    warp_schedule.scala:78  VecInit(Seq.fill(num_warp)(Module(new PCcontrol))) -/
/-    parameters.scala:38,41,47  num_fetch = 2, icache_align = 8, xLen = 32   -/
/-  驱动纪律（warp_schedule.scala，建模假设与规约陈述的依据）：                -/
/-    :84-89  默认所有实例 PC_replay=true（保持）、PC_src=0、mask_i=0；       -/
/-    :96-100 调度选中 next_warp：PC_replay=(!pc_req.ready)|(!pc_ready)，     -/
/-             PC_src=2（顺序推进），pc_req.bits.addr/mask 当拍组合读出        -/
/-             PC_next/mask_o；                                              -/
/-    :195-198 icache miss 响应 replay：PC_src=3，New_PC/mask_i 回填；        -/
/-    :202-204 分支跳转：PC_src=1，New_PC=branch 目标；                       -/
/-    :212-214 CTA 派发新 warp：PC_src=1，New_PC=start_pc；                   -/
/-    :218-220 初始化：when(io.pc_reset) 内所有实例 PC_src=1、PC_replay=false、-/
/-             New_PC=warp_init_addr(b)（:83，全 0）。                        -/
/-    io.pc_reset 来源：GPGPU_top.scala:355-360 复位后前 5 拍拉高（cnt<5），  -/
/-    第 6 拍起拉低；GPGPU_top_nocache.scala:38 同为前 5 拍。                 -/
/-                                                                           -/
/- ======================== 建模假设 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 单 warp 单实例建模：num_warp=8 个 PCcontrol 实例完全独立、无交互      -/
/-      （各自 Reg，输入由 warp_schedule 按 wid 分发），故只建模单实例。      -/
/-  D2. mask 是无复位初值的 Reg（:27），模型把初始 mask 作为参数 m            -/
/-      （pccInit），pout 有 RegInit 0（:26）。所有 mask 相关定理以"先写      -/
/-      后读"或"与初值无关"形式陈述（T4 / pccReset_deterministic），不依赖    -/
/-      初值选取——见审查备注 R1。                                             -/
/-  D3. align 中 `pc_aligned + (i*4).U >= pc`（:33-35）在 Chisel 是 33 位    -/
/-      加法后的无符号比较；num_fetch=2 时 pc_aligned ≤ 0xFFFFFFF8，          -/
/-      +4 ≤ 0xFFFFFFFC，32 位内不溢出，模型用 32 位加法，语义一致。          -/
/-  D4. PC_src=0 按代码行为"保持"建模（:54-56 otherwise）；:39 注释           -/
/-      "PC_src=0:PC+4" 为陈旧注释，不据此建模——见审查备注 R2。               -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.SIMT

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 状态、输入与组合逻辑（PCcontrol.scala:16-61）                            -/
/- ========================================================================= -/

/-- PCcontrol 状态：pout（RegInit 0，:26）与 mask（无初值 Reg，:27，见 D2）。
    num_fetch = 2（parameters.scala:38），故掩码宽 2。 -/
structure PccState where
  pout : BitVec 32
  mask : BitVec 2
deriving DecidableEq, Repr

/-- 初始状态：pout = 0（:26）；mask 初值未定，建模为参数 m（D2）。 -/
def pccInit (m : BitVec 2) : PccState := ⟨0, m⟩

/-- 输入 io（:18-23）：New_PC / PC_replay / PC_src / mask_i。 -/
structure PccIn where
  newPC  : BitVec 32
  replay : Bool
  src    : BitVec 2
  maskI  : BitVec 2
deriving DecidableEq, Repr

/-- align 的掩码部分（:32-35）：bit i = 1 ↔ pc ≤ pc_aligned + 4i。
    offset_mask = icache_align-1 = 7（:30），pc_aligned = pc & ~7（:31）。 -/
def pccAlignMask (pc : BitVec 32) : BitVec 2 :=
  let aligned := pc &&& 0xFFFFFFF8#32
  (if pc ≤ aligned then 1#2 else 0#2) ||| (if pc ≤ aligned + 4#32 then 2#2 else 0#2)

/-- align（:29-37）：(pc_aligned, pc_mask)。 -/
def pccAlign (pc : BitVec 32) : BitVec 32 × BitVec 2 :=
  (pc &&& 0xFFFFFFF8#32, pccAlignMask pc)

/-- 单拍转移（:40-57）：优先链 PC_replay > PC_src=2 > =1 > =3 > 保持。
    PC_src=2：pout += num_fetch<<2 = 8，mask 全 1（:43-45）；
    PC_src=1：pout/mask ← align(New_PC)（:46-50）；
    PC_src=3：pout ← New_PC，mask ← mask_i（:51-53）；
    otherwise（含 PC_src=0）：保持（:54-56，见 D4/R2）。 -/
def pccStep (s : PccState) (i : PccIn) : PccState :=
  if i.replay then s
  else if i.src = 2#2 then ⟨s.pout + 8#32, 3#2⟩
  else if i.src = 1#2 then ⟨(pccAlign i.newPC).1, (pccAlign i.newPC).2⟩
  else if i.src = 3#2 then ⟨i.newPC, i.maskI⟩
  else s

/-- io.PC_next := pout（:58）。 -/
def pccPCNext (s : PccState) : BitVec 32 := s.pout
/-- io.mask_o := mask（:59）。 -/
def pccMaskO (s : PccState) : BitVec 2 := s.mask

/-- 多拍迭代（run）。 -/
def pccRun (s : PccState) (es : List PccIn) : PccState := es.foldl pccStep s

/- ========================================================================= -/
/- 2. 具体数值测试（by decide；单拍/短轨迹均为字面量归约）                     -/
/- ========================================================================= -/

section PccTests

/- ---- align 数值回归（:29-37） ---- -/

-- pc 8B 对齐：aligned = pc，两槽全取（0b11）
theorem pccTestAlign0 : pccAlign 0x0#32 = (0x0#32, 0b11#2) := by decide
theorem pccTestAlign8 : pccAlign 0x8#32 = (0x8#32, 0b11#2) := by decide
theorem pccTestAlign10 : pccAlign 0x10#32 = (0x10#32, 0b11#2) := by decide
-- pc = aligned+4（对齐块第二槽）：只取高槽（0b10）
theorem pccTestAlign4 : pccAlign 0x4#32 = (0x0#32, 0b10#2) := by decide
theorem pccTestAlignC : pccAlign 0xC#32 = (0x8#32, 0b10#2) := by decide
-- 最高对齐块，加法不溢出（D3）
theorem pccTestAlignHi : pccAlign 0xFFFFFFFC#32 = (0xFFFFFFF8#32, 0b10#2) := by decide
-- 非 4B 对齐边界（RV32I 合法 PC 不会出现，见 R3）：pc%8=1 → 0b10；pc%8=5 → 0b00
theorem pccTestAlign1 : pccAlign 0x1#32 = (0x0#32, 0b10#2) := by decide
theorem pccTestAlign5 : pccAlign 0x5#32 = (0x0#32, 0b00#2) := by decide

/- ---- 优先链各分支（:40-57） ---- -/

/-- 顺序推进事件：调度选中且握手就绪（warp_schedule.scala:96-100，
    PC_replay=false、PC_src=2）。 -/
def pccSeqIn : PccIn := ⟨0, false, 2#2, 0⟩

/-- pc_reset 初始化事件（warp_schedule.scala:218-220，New_PC=warp_init_addr=0）。 -/
def pccResetIn : PccIn := ⟨0#32, false, 1#2, 0#2⟩

-- PC_replay 优先于 PC_src=2：保持（:40-42）
theorem pccTestReplay :
    pccStep ⟨0x100#32, 0b10#2⟩ ⟨0x200#32, true, 2#2, 0b01#2⟩ = ⟨0x100#32, 0b10#2⟩ := by
  decide
-- PC_src=2 顺序推进：pout+8、mask 全 1（:43-45）
theorem pccTestSeq :
    pccStep ⟨0x100#32, 0b10#2⟩ pccSeqIn = ⟨0x108#32, 0b11#2⟩ := by
  decide
-- PC_src=1 分支跳转：pout/mask ← align(New_PC)（:46-50）
theorem pccTestBranch :
    pccStep ⟨0x100#32, 0b10#2⟩ ⟨0x204#32, false, 1#2, 0b01#2⟩ = ⟨0x200#32, 0b10#2⟩ := by
  decide
-- PC_src=3 miss replay 回填：pout ← New_PC，mask ← mask_i（:51-53）
theorem pccTestMiss :
    pccStep ⟨0x100#32, 0b10#2⟩ ⟨0x180#32, false, 3#2, 0b01#2⟩ = ⟨0x180#32, 0b01#2⟩ := by
  decide
-- PC_src=0 保持（:54-56，按代码建模，见 R2）
theorem pccTestHold :
    pccStep ⟨0x100#32, 0b10#2⟩ ⟨0x200#32, false, 0#2, 0b01#2⟩ = ⟨0x100#32, 0b10#2⟩ := by
  decide
-- 连续 4 拍顺序推进：pout = 0x100 + 4×8 = 0x120
theorem pccTestRunSeq :
    (pccRun ⟨0x100#32, 0b11#2⟩ (List.replicate 4 pccSeqIn)).pout = 0x120#32 := by
  decide
-- pc_reset 首拍：mask 被确定化为 align(0)=0b11（与初值无关，配合 T4，见 R1）
theorem pccTestReset :
    pccStep (pccInit 0b00#2) pccResetIn = ⟨0#32, 0b11#2⟩ := by
  decide

end PccTests

/- ========================================================================= -/
/- 3. 一般性定理                                                              -/
/- ========================================================================= -/

/-- T1a align 对齐正确性（:30-31）：pc_aligned 低 3 位清零、不超过 pc、
    与 pc 差 < 8（即 pc 低 3 位清零的唯一 8B 对齐下取整）。 -/
theorem pccT1a_align (pc : BitVec 32) :
    (pccAlign pc).1 &&& 7#32 = 0 ∧ (pccAlign pc).1 ≤ pc ∧ pc - (pccAlign pc).1 ≤ 7#32 := by
  simp only [pccAlign]
  constructor
  · bv_decide
  · constructor <;> bv_decide

/-- T1b 掩码逐位规约（:33-35）：bit 0 ↔ pc ≤ pc_aligned；bit 1 ↔ pc ≤ pc_aligned+4。 -/
theorem pccT1b_mask_bit0 (pc : BitVec 32) :
    (pccAlign pc).2.getLsbD 0 = true ↔ pc ≤ pc &&& 0xFFFFFFF8#32 := by
  simp only [pccAlign, pccAlignMask]
  bv_decide

theorem pccT1b_mask_bit1 (pc : BitVec 32) :
    (pccAlign pc).2.getLsbD 1 = true ↔ pc ≤ (pc &&& 0xFFFFFFF8#32) + 4#32 := by
  simp only [pccAlign, pccAlignMask]
  bv_decide

/-- T1c 掩码高位连续 1：bit 0 置位蕴含 bit 1 置位（mask ∈ {00,10,11}，永不出现 01）；
    且 pc 4B 对齐时掩码由对齐偏移唯一确定（8B 对齐 → 0b11，否则 0b10）。 -/
theorem pccT1c_mask_contiguous (pc : BitVec 32) :
    (pccAlign pc).2.getLsbD 0 = true → (pccAlign pc).2.getLsbD 1 = true := by
  simp only [pccAlign, pccAlignMask]
  bv_decide

theorem pccT1c_mask_word_aligned (pc : BitVec 32) (h : pc &&& 3#32 = 0) :
    (pccAlign pc).2 = if pc &&& 7#32 = 0 then 0b11#2 else 0b10#2 := by
  simp only [pccAlign, pccAlignMask]
  bv_decide

/-- T2 优先链规约：各输入组合下的下一状态（分段函数，:40-57）。 -/
theorem pccT2_replay (s : PccState) (i : PccIn) (hr : i.replay = true) :
    pccStep s i = s := by
  simp [pccStep, hr]

theorem pccT2_seq (s : PccState) (i : PccIn)
    (hr : i.replay = false) (hs : i.src = 2#2) :
    pccStep s i = ⟨s.pout + 8#32, 3#2⟩ := by
  simp [pccStep, hr, hs]

theorem pccT2_src1 (s : PccState) (i : PccIn)
    (hr : i.replay = false) (hs : i.src = 1#2) :
    pccStep s i = ⟨(pccAlign i.newPC).1, (pccAlign i.newPC).2⟩ := by
  simp [pccStep, hr, hs]

theorem pccT2_src3 (s : PccState) (i : PccIn)
    (hr : i.replay = false) (hs3 : i.src = 3#2) :
    pccStep s i = ⟨i.newPC, i.maskI⟩ := by
  simp [pccStep, hr, hs3]

theorem pccT2_hold (s : PccState) (i : PccIn)
    (hr : i.replay = false) (hs2 : i.src ≠ 2#2) (hs1 : i.src ≠ 1#2) (hs3 : i.src ≠ 3#2) :
    pccStep s i = s := by
  simp [pccStep, hr, hs2, hs1, hs3]

/-- T3 顺序取指推进（无 replay/分支干预时，:43-45）：连续 n 拍顺序推进后
    pout = 初值 + 8n（BitVec 回绕忠实建模 2^32 溢出）。run 归纳。 -/
theorem pccT3_seq_advance (s : PccState) (n : Nat) :
    (pccRun s (List.replicate n pccSeqIn)).pout = s.pout + 8#32 * BitVec.ofNat 32 n := by
  induction n generalizing s with
  | zero => simp [pccRun]
  | succ k ih =>
      rw [List.replicate_succ, pccRun, List.foldl_cons]
      show ((List.replicate k pccSeqIn).foldl pccStep (pccStep s pccSeqIn)).pout = _
      rw [← pccRun, ih (pccStep s pccSeqIn)]
      have hstep : (pccStep s pccSeqIn).pout = s.pout + 8#32 := by
        simp [pccStep, pccSeqIn]
      have h1 : (8#32 : BitVec 32) * BitVec.ofNat 32 1 = 8#32 := by decide
      rw [hstep, ← BitVec.ofNat_add_ofNat, BitVec.mul_add, h1]
      generalize 8#32 * BitVec.ofNat 32 k = x
      bv_decide

/-- T4 PC_src=1 后 mask_o/pout 完全由 New_PC 决定（:46-50），与转移前状态无关
    —— 覆盖 mask 无复位初值（:27）的"先写后读"纪律：首次 PC_src=1 写入后，
    mask_o 下一拍等于 align 掩码，初值不确定性被消除（见 R1）。 -/
theorem pccT4_src1_determines (s s' : PccState) (i : PccIn)
    (hr : i.replay = false) (hs : i.src = 1#2) :
    pccStep s i = ⟨(pccAlign i.newPC).1, pccAlignMask i.newPC⟩ ∧
    pccStep s i = pccStep s' i := by
  constructor <;> simp [pccStep, hr, hs, pccAlign]

/-- 复位窗口确定化：pc_reset 拍（warp_schedule.scala:218-220，顶层复位后前 5 拍
    拉高，GPGPU_top.scala:355-360）后，任意初始 mask 下状态均为 ⟨0, 0b11⟩。
    即现行顶层驱动下 mask 的未定初值在首次读出前必被覆盖（R1 的形式化）。 -/
theorem pccReset_deterministic (m : BitVec 2) :
    pccStep (pccInit m) pccResetIn = ⟨0#32, 0b11#2⟩ := by
  rw [(pccT4_src1_determines (pccInit m) (pccInit 0#2) pccResetIn rfl rfl).2]
  decide

/- ========================================================================= -/
/- 4. 审查备注（逐行对照 PCcontrol.scala + 驱动侧 warp_schedule.scala）        -/
/-                                                                           -/
/-  R1（I 类观察，现行配置不可观测）：mask 是无复位初值的 Reg（:27）。        -/
/-     首次组合读出发生在调度时（warp_schedule.scala:100 mask := mask_o）。   -/
/-     现行顶层 pc_reset 在复位后前 5 拍拉高（GPGPU_top.scala:355-360，       -/
/-     nocache 版 :38），期间所有 warp 实例被 PC_src=1 写入 mask=align(0)     -/
/-     =0b11，且 warpReq 派发（:212-214）先于该 warp 首次调度（warp 未派发   -/
/-     不会被调度器选中），故首次读出前必有写入——pccReset_deterministic /     -/
/-     T4 已形式化"一次 PC_src=1 写入即消除初值不确定性"。风险残留：该安全   -/
/-     性依赖片外契约（顶层必须给足 ≥1 拍复位窗口），PCcontrol 模块自身不保   -/
/-     证；若模块被复用到无 pc_reset 的场景，首拍 mask_o 为未定值。建议：     -/
/-     mask 改 RegInit（最小改动，`RegInit(0.U(num_fetch.W))`）。另注：       -/
/-     warp_init_addr 全 0（warp_schedule.scala:83）与 pout 的 RegInit(0)     -/
/-     重复，复位写 pout 无实际效果，复位窗口的实际作用是确定化 mask。       -/
/-  R2（III 类/文档，无功能影响）：:39 注释 "PC_src=0:PC+4 PC_src=1:new PC   -/
/-     PC_src=2:PC" 与代码不符——otherwise 分支（:54-56，含 PC_src=0）为保     -/
/-     持，且注释对 2/3 的说明也与 :43-53 不符。陈旧注释，模型按代码建模     -/
/-     （D4）。建议删除或更正该注释。                                        -/
/-  R3（I 类观察，RV32I 下不可观测）：align 对非 4B 对齐的 New_PC 会丢线程   -/
/-     槽——pc%8 ∈ {5,6,7} 时 mask=0b00（pccTestAlign5 实测），分支到该地    -/
/-     址将使首拍取指掩码全 0（无任何线程取到目标指令）。Ventus 为 RV32I     -/
/-     （ALU.scala:14，docs/Ventus-GPGPU-doc.md:68，无 C 扩展），合法 PC      -/
/-     恒 4B 对齐，pc%4=0 时 mask ∈ {0b11, 0b10}（T1c），故不可观测；若      -/
/-     未来引入 RVC（2B 对齐指令），此处需重审。                             -/
/-  R4（健壮性说明，非 bug）：优先链中 PC_replay 分支（:40-42）与 otherwise -/
/-     分支行为相同（均保持），PC_replay=true 时 PC_src 任意值均被掩蔽，     -/
/-     T2_replay 覆盖；D3 已论证 align 加法 32 位不溢出。                    -/
/- ========================================================================= -/

/- ---- 公理审计（全部定理应仅剩 Lean 标准公理；测试节 by decide 不引入额外
       公理） ---- -/

#print axioms pccT1a_align
#print axioms pccT1b_mask_bit0
#print axioms pccT1b_mask_bit1
#print axioms pccT1c_mask_contiguous
#print axioms pccT1c_mask_word_aligned
#print axioms pccT2_replay
#print axioms pccT2_seq
#print axioms pccT2_src1
#print axioms pccT2_src3
#print axioms pccT2_hold
#print axioms pccT3_seq_advance
#print axioms pccT4_src1_determines
#print axioms pccReset_deterministic

end Ventus.SIMT
