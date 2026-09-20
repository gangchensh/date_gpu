/- ========================================================================= -/
/-                     Arith/DecodeUnitProps.lean                            -/
/-  译码表全表性质——核销契约缺口 G1（Contracts.lean 登记册 H-DECODE-1）        -/
/-                                                                           -/
/-  背景：ExeSFU.lean 的 Q3/Q4/Q12「无声丢指令不可达」分析依赖三条译码侧性质：  -/
/-    (a) SFU 指令（sfu=1）isvec ⟺ wvd，且标量（isvec=0）⇒ wxd=1              -/
/-        （DecodeUnit.scala:225-228,237-238,344-355；破窗见 ExeSFU Q3）      -/
/-    (b) 标量指令 mask = 0x1（单 lane0 有效）：译码侧条件是 c.mask=0          -/
/-        （DecodeUnit.scala:588 的 `& isvec` 合取项），collector 在           -/
/-        operandCollector.scala:250 的 `!c.mask` 分支逐 lane 生成             -/
/-        mask(x) := Mux(isvec, true, x==0)（破窗见 ExeSFU Q4）               -/
/-    (c) FPU 指令（fp=1）wvd/wxd 恰一（破窗见 ExeSFU Q12）                   -/
/-                                                                           -/
/-  方法：表是全枚举数据（265 行 + 默认行）。先定义行判别函数，用               -/
/-  native_decide 证「全表行满足」，默认行 decide，再经 decDecode_mem          -/
/-  （译码输出必为默认行或某表行）提升到任意指令的 decDecode 输出。             -/
/-                                                                           -/
/-  结论：三条性质在全表 265 行 + 默认行上全部成立，无反例行——                 -/
/-  ExeSFU Q3/Q4/Q12 的破窗在真实译码输出上不可达（确认，非 bug）。            -/
/-  SFU 行清单（19 行，sfu=1）：DIV/DIVU/REM/REMU、FDIV_S/FSQRT_S、            -/
/-  VREM/VREMU/VDIV/VDIVU(_VV/_VX)、VFDIV_VV/VF、VFRDIV_VF、VFSQRT_V、VFEXP_V  -/
/- ========================================================================= -/
import Ventus.Arith.DecodeUnit

namespace Ventus.Arith

/- ========================================================================= -/
/- 1. 行判别函数与全表判别定理                                                 -/
/- ========================================================================= -/

/-- 【H-DECODE-1(a) 行判别】SFU 行（sfu=1）须满足：isvec=wvd、
    标量（isvec=0）⇒ wxd=1、wvd/wxd 互斥（wvd≠wxd）。 -/
def decH1aRowOk (r : DecCtrlRow) : Bool :=
  !r.sfu || ((r.isvec == r.wvd) && (r.isvec || r.wxd) && (r.wvd != r.wxd))

/-- 【H-DECODE-1(c) 行判别】FPU 行（fp=1）wvd/wxd 恰一（wvd≠wxd）。 -/
def decH1cRowOk (r : DecCtrlRow) : Bool :=
  !r.fp || (r.wvd != r.wxd)

/-- operandCollector.scala:250 的 `!c.mask` 分支逐 lane 生成（num_thread=32）：
    mask(x) := Mux(isvec, true, x==0)——标量仅 lane0 有效（0x1），
    向量无掩码时全 lane 有效（0xFFFFFFFF）。 -/
def decHColMask (isvec : Bool) : BitVec 32 := if isvec then 0xFFFFFFFF#32 else 1#32

/-- (a) 全表行判别通过 -/
theorem decH1aRows_all :
    (decAllTables.map DecEntry.row).all decH1aRowOk = true := by native_decide

/-- (a) 默认行判别通过（sfu=0，前件不成立） -/
theorem decH1a_default : decH1aRowOk decDefaultRow = true := by decide

/-- (c) 全表行判别通过 -/
theorem decH1cRows_all :
    (decAllTables.map DecEntry.row).all decH1cRowOk = true := by native_decide

/-- (c) 默认行判别通过（fp=0，前件不成立） -/
theorem decH1c_default : decH1cRowOk decDefaultRow = true := by decide

/- ========================================================================= -/
/- 2. 值域提升：decDecode 输出必为默认行或某表行 ⇒ 继承全表判别性质             -/
/- ========================================================================= -/

/-- 四张表各自的行都是全表拼接的行 -/
theorem decH_mem_allTables {r : DecCtrlRow}
    (h : r ∈ decTableIMF.map DecEntry.row ∨ r ∈ decTableV.map DecEntry.row ∨
      r ∈ decTableVL.map DecEntry.row ∨ r ∈ decTableVC.map DecEntry.row) :
    r ∈ decAllTables.map DecEntry.row := by
  simp only [decAllTables, List.map_append, List.mem_append]
  rcases h with h1 | h2 | h3 | h4
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr h2))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr h4

/-- decDecode 的值域（decDecode_mem）继承全表判别性质 -/
theorem decH_rowOf_decode {P : DecCtrlRow → Bool} (inst : BitVec 32)
    (hall : (decAllTables.map DecEntry.row).all P = true)
    (hdef : P decDefaultRow = true) : P (decDecode inst) = true := by
  rcases decDecode_mem inst with hd | h
  · rw [hd]; exact hdef
  · exact (List.all_eq_true.mp hall) _ (decH_mem_allTables h)

/- ========================================================================= -/
/- 3. 行级引理（Bool 逐字段分情形）                                            -/
/- ========================================================================= -/

theorem decH1a_row {r : DecCtrlRow} (hok : decH1aRowOk r = true) (h : r.sfu = true) :
    r.isvec = r.wvd ∧ (r.isvec = false → r.wxd = true) ∧
    (r.wvd = true → r.wxd = false) := by
  cases hv : r.isvec <;> cases hw : r.wvd <;> cases hx : r.wxd <;>
    simp_all [decH1aRowOk]

theorem decH1c_row {r : DecCtrlRow} (hok : decH1cRowOk r = true) (h : r.fp = true) :
    r.wvd ≠ r.wxd := by
  cases hv : r.wvd <;> cases hx : r.wxd <;> simp_all [decH1cRowOk]

/- ========================================================================= -/
/- 4. 主定理：H-DECODE-1 三条性质对任意指令的 decDecode 输出成立                 -/
/- ========================================================================= -/

/-- 【H-DECODE-1(a)】任意指令译码结果：sfu=1 ⇒ isvec=wvd ∧
    标量（isvec=0）⇒ wxd=1 ∧ wvd=1 ⇒ wxd=0。
    ExeSFU Q3 破窗（isvec=1 ∧ wvd=0 的 SFU 事务被无声丢弃）因此在真实
    译码输出上不可达。 -/
theorem decH1a (inst : BitVec 32) (h : (decDecode inst).sfu = true) :
    (decDecode inst).isvec = (decDecode inst).wvd ∧
    ((decDecode inst).isvec = false → (decDecode inst).wxd = true) ∧
    ((decDecode inst).wvd = true → (decDecode inst).wxd = false) :=
  decH1a_row (decH_rowOf_decode inst decH1aRows_all decH1a_default) h

/-- 【H-DECODE-1(b) 译码侧条件】标量指令（isvec=0）mask 使能恒 0
    （DecodeUnit.scala:588 的 `& isvec` 合取项），与 disableMask/aluFn/inst
    无关。比 dec_mask_scalar_off 多覆盖 disableMask=1 的情形。 -/
theorem decH1b_maskEn_off (inst : BitVec 32) (aluFn : BitVec 6) (dm : Bool) :
    decMaskEn inst aluFn false dm = false := by
  dec_unfold; bv_decide

/-- 【H-DECODE-1(b)】标量译码结果（isvec=0）：collector 必走
    operandCollector.scala:250 的 `!c.mask` 分支，生成 mask = 0x1
    （仅 lane0 有效）。ExeSFU Q4 破窗（标量 mask 置位于其它 lane ⇒ 取到
    dummy 1/1 结果）因此在真实译码输出上不可达。 -/
theorem decH1b (inst : BitVec 32) (h : (decDecode inst).isvec = false) :
    decMaskEn inst (decDecode inst).aluFn (decDecode inst).isvec
        (decDecode inst).disableMask = false ∧
    decHColMask (decDecode inst).isvec = 1#32 := by
  refine ⟨?_, ?_⟩
  · rw [h]; exact decH1b_maskEn_off _ _ _
  · simp [decHColMask, h]

/-- 【H-DECODE-1(c)】任意指令译码结果：fp=1 ⇒ wvd≠wxd（恰一置位）。
    ExeSFU Q12 破窗（wvd=wxd=0 结果丢弃 / wvd=wxd=1 out_x 侧丢失）因此在
    真实译码输出上不可达。 -/
theorem decH1c (inst : BitVec 32) (h : (decDecode inst).fp = true) :
    (decDecode inst).wvd ≠ (decDecode inst).wxd :=
  decH1c_row (decH_rowOf_decode inst decH1cRows_all decH1c_default) h

/-- 【H-DECODE-1 合体，与 Contracts.lean `specSfuDecodeOk` 同形】SFU 指令译码
    结果满足 (a)+(b)+(c)：isvec=wvd、标量 ⇒ wxd=1 且 collector mask=0x1、
    wvd=1 ⇒ wxd=0。 -/
theorem decH1_sfu_specOk (inst : BitVec 32) (h : (decDecode inst).sfu = true) :
    (decDecode inst).isvec = (decDecode inst).wvd ∧
    ((decDecode inst).isvec = false → (decDecode inst).wxd = true) ∧
    ((decDecode inst).isvec = false → decHColMask (decDecode inst).isvec = 1#32) ∧
    ((decDecode inst).wvd = true → (decDecode inst).wxd = false) := by
  obtain ⟨h1, h2, h3⟩ := decH1a inst h
  exact ⟨h1, h2, fun hv => by simp [decHColMask, hv], h3⟩

/- ========================================================================= -/
/- 5. 判别函数数值回归（钉死代表性表行，防表/判别函数被误改）                   -/
/- ========================================================================= -/

-- 标量整除：sfu=1, isvec=0, wvd=0, wxd=1（DecodeUnit.scala:225）
example : decH1aRowOk (decRowOf decAllTables "DIV") = true ∧
    (decRowOf decAllTables "DIV").isvec = false ∧
    (decRowOf decAllTables "DIV").wvd = false ∧
    (decRowOf decAllTables "DIV").wxd = true := by decide
-- 向量整除：sfu=1, isvec=1, wvd=1, wxd=0（DecodeUnit.scala:344-351）
example : decH1aRowOk (decRowOf decAllTables "VDIV_VV") = true ∧
    (decRowOf decAllTables "VDIV_VV").isvec = true ∧
    (decRowOf decAllTables "VDIV_VV").wvd = true ∧
    (decRowOf decAllTables "VDIV_VV").wxd = false := by decide
-- 标量浮点：fp=1, wvd=0, wxd=1（DecodeUnit.scala:234）
example : decH1cRowOk (decRowOf decAllTables "FADD_S") = true ∧
    (decRowOf decAllTables "FADD_S").wvd = false ∧
    (decRowOf decAllTables "FADD_S").wxd = true := by decide
-- 向量浮点：fp=1, wvd=1, wxd=0（DecodeUnit.scala:259）
example : decH1cRowOk (decRowOf decAllTables "VFMUL_VV") = true ∧
    (decRowOf decAllTables "VFMUL_VV").wvd = true ∧
    (decRowOf decAllTables "VFMUL_VV").wxd = false := by decide
-- collector mask 生成：标量 0x1 / 向量无掩码全 1（operandCollector.scala:250）
example : decHColMask false = 1#32 ∧ decHColMask true = 0xFFFFFFFF#32 := by decide

/- ========================================================================= -/
/- 6. 公理审计（native_decide 定理含 Lean.ofReduceBool，归档注明）              -/
/- ========================================================================= -/

#print axioms decH1aRows_all
#print axioms decH1cRows_all
#print axioms decH1a
#print axioms decH1b
#print axioms decH1c
#print axioms decH1_sfu_specOk

end Ventus.Arith
