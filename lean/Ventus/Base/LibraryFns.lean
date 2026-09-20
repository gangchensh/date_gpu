/- ========================================================================= -/
/-                        LibraryFns.lean                                    -/
/-  CoralNPU 通用纯函数库的形式化：翻译 + 数学规约 + 可执行测试                -/
/-                                                                            -/
/-  移植记录：2026-08-25 自 coralNPU/lean/CoralNPU/Base/LibraryFns.lean        -/
/-  逐行移植（"移植即重审"）：除 CoralNPU.Base → Ventus.Base 改名、修订下方    -/
/-  Cat 注释（本项目 Defs.lean 已是修复后版本）外，定义/定理/证明逐行对应；    -/
/-  文件末尾新增 LibraryFnsRegressionTests 一节（移植重审的判收依据）。        -/
/-                                                                            -/
/-  翻译来源：                                                                -/
/-  - original/coralnpu-main/hdl/chisel/src/common/MathUtil.scala（Clamp）    -/
/-  - original/coralnpu-main/hdl/chisel/src/common/Library.scala              -/
/-                                                                            -/
/-  跳过（按任务约定）：IrrevocableChecker / MakeIrrevocable（握手契约，涉     -/
/-  时序断言）；MakeWireBundle / MakeValid / MakeInvalid / MakeDecoupled /    -/
/-  SafeMuxUpTo1H（Chisel 元编程/接口工具，无语义内容）；MuBi4（枚举字面量）； -/
/-  UIntToVec（位切片重解释，已被 Rotate/Shift 的逐元素视角覆盖）；MuxUpTo1H  -/
/-  （依赖 PopCount 断言的 Mux1H 变体）。                                     -/
/-                                                                            -/
/-  建模说明：                                                                -/
/-  - Vec[T] 建模为 `Fin n → Bits w`；Chisel `Vec.asUInt` 使 index 0 位于最   -/
/-    低位（见 chisel-lang.org cookbook：「leftmost Bool in Vec is low order  -/
/-    bit」），故 rotateLeft 使元素 o 移至下标 (o + shift) % n。              -/
/-  - 位拼接使用 Lean 标准库 `BitVec.append`（`++`，左操作数在高位）。        -/
/-    审查记录：coralNPU 原版 Defs.lean 的 `Cat` 曾未将 hi 左移（已修复）；    -/
/-    本项目 Defs.lean 移植的是修复后版本（语义正确，见 Defs.lean 审查注释）， -/
/-    本文件不使用它，统一用 `BitVec.append`。                                -/
/-  本文件零 sorry。                                                         -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. MuxOR（Library.scala:20-28）                                           -/
/- ========================================================================= -/

/-- `MuxOR(valid, data: UInt)`：valid 时选通 data，否则输出 0。
    用于对多个被独热选通的总线做 OR 归约（未被选通的源贡献 0）。 -/
def muxOR {n : Nat} (valid : Bit) (data : Bits n) : Bits n :=
  Mux valid data (bits_zero n)

/-- `MuxOR(valid, data: Bool)`：Bool 版本。 -/
def muxORBool (valid data : Bit) : Bit :=
  Mux valid data b0

theorem muxOR_true {n : Nat} (data : Bits n) : muxOR b1 data = data := by
  simp [muxOR, Mux, b1]

theorem muxOR_false {n : Nat} (data : Bits n) : muxOR b0 data = bits_zero n := by
  simp [muxOR, Mux, b0]

theorem muxORBool_true (data : Bit) : muxORBool b1 data = data := by
  simp [muxORBool, Mux, b1]

theorem muxORBool_false (data : Bit) : muxORBool b0 data = b0 := by
  simp [muxORBool, Mux, b0]

/-- 规约：选通结果为 0 当且仅当未选通或数据本身为 0 -/
theorem muxOR_eq_zero_iff {n : Nat} (valid : Bit) (data : Bits n) :
    muxOR valid data = bits_zero n ↔ valid = b0 ∨ data = bits_zero n := by
  cases valid <;> simp [muxOR, Mux, b0]

/-- OR 归约语义：至多一个源被选通时，OR 归约等价于逐一路选（真值表） -/
theorem muxOR_or_of_not_both {n : Nat} (v1 v2 : Bit) (d1 d2 : Bits n)
    (h : ¬(v1 = b1 ∧ v2 = b1)) :
    muxOR v1 d1 ||| muxOR v2 d2 = Mux v1 d1 (Mux v2 d2 (bits_zero n)) := by
  cases v1 <;> cases v2 <;> simp_all [muxOR, Mux, b1, bits_zero]

-- 可执行测试
example : muxOR true 0xAB#8 = 0xAB#8 := by decide
example : muxOR false 0xAB#8 = 0x00#8 := by decide
example : muxORBool true true = true := by decide
example : muxORBool true false = false := by decide
example : muxOR true 0x0F#8 ||| muxOR false 0xF0#8 = 0x0F#8 := by decide

/- ========================================================================= -/
/- 2. ForceZero（Library.scala:98-102）                                      -/
/- ========================================================================= -/

/-- `ForceZero`：ValidIO 建模为 `(valid, bits)` 序对；invalid 时将 bits 归零
    （阻止无效数据下传，降低动态功耗）。 -/
def forceZero {w : Nat} (input : Bool × Bits w) : Bool × Bits w :=
  (input.1, Mux input.1 input.2 (bits_zero w))

theorem forceZero_invalid {w : Nat} (b : Bits w) :
    forceZero (false, b) = (false, bits_zero w) := by
  simp [forceZero, Mux]

theorem forceZero_valid {w : Nat} (b : Bits w) :
    forceZero (true, b) = (true, b) := by
  simp [forceZero, Mux]

-- 可执行测试（LibraryTest.scala:84-100 的用例）
example : (forceZero (false, 9001#32)).2 = 0#32 := by decide
example : (forceZero (true, 9001#32)).2 = 9001#32 := by decide

/- ========================================================================= -/
/- 3. Clz（Library.scala:104-108）                                           -/
/- ========================================================================= -/

/-- `Clz`：前导零计数。
    源码为 `PriorityEncoder(Cat(1.U(1.W), Reverse(bits)))`：Chisel 的
    `PriorityEncoder` 返回最低置位位下标；`Reverse` 后原最高位位于 bit 0，
    故结果即前导零个数；顶端拼接的常数 1 保证 `bits = 0` 时结果为 `n`。
    此处直接以数学形式定义：x ≠ 0 时 clz x = n − (最高置位位下标 + 1)。 -/
def clz {n : Nat} (x : Bits n) : Nat :=
  if x = 0 then n else n - 1 - Nat.log2 x.toNat

/-- 辅助：BitVec 非零当且仅当其 toNat 非零 -/
theorem toNat_ne_zero_of_ne {n : Nat} {x : Bits n} (h : x ≠ 0) : x.toNat ≠ 0 := by
  intro hz
  exact h (BitVec.toNat_inj.mp (by simpa using hz))

/-- x = 0 时 clz = n（顶端常数 1 的作用） -/
theorem clz_zero (n : Nat) : clz (0 : Bits n) = n := by
  simp [clz]

/-- x ≠ 0 时 clz x = n − (⌊log2 x⌋ + 1)，即 n − (最高置位位下标 + 1) -/
theorem clz_of_ne_zero {n : Nat} (x : Bits n) (h : x ≠ 0) :
    clz x = n - (Nat.log2 x.toNat + 1) := by
  have h0 := toNat_ne_zero_of_ne h
  have hlt : Nat.log2 x.toNat < n := (Nat.log2_lt h0).mpr x.isLt
  unfold clz
  rw [if_neg h]
  omega

/-- clz 有界：0 ≤ clz x ≤ n -/
theorem clz_le {n : Nat} (x : Bits n) : clz x ≤ n := by
  unfold clz
  split
  · exact Nat.le_refl n
  · omega

/-- 主规约：最高置位位恰好位于下标 n − 1 − clz x -/
theorem clz_spec {n : Nat} (x : Bits n) (h : x ≠ 0) :
    2 ^ (n - 1 - clz x) ≤ x.toNat ∧ x.toNat < 2 ^ (n - clz x) := by
  have h0 := toNat_ne_zero_of_ne h
  have hlt : Nat.log2 x.toNat < n := (Nat.log2_lt h0).mpr x.isLt
  unfold clz
  rw [if_neg h]
  have e1 : n - 1 - (n - 1 - x.toNat.log2) = x.toNat.log2 := by omega
  have e2 : n - (n - 1 - x.toNat.log2) = x.toNat.log2 + 1 := by omega
  rw [e1, e2]
  exact ⟨Nat.log2_self_le h0, Nat.lt_log2_self⟩

/-- clz x = n 当且仅当 x = 0 -/
theorem clz_eq_n_iff {n : Nat} (x : Bits n) : clz x = n ↔ x = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact hx
    · have h0 := toNat_ne_zero_of_ne hx
      have hn : 0 < n := by
        by_cases hn0 : n = 0
        · subst hn0; have hlt := x.isLt; simp at hlt; omega
        · omega
      have hlt : Nat.log2 x.toNat < n := (Nat.log2_lt h0).mpr x.isLt
      rw [clz_of_ne_zero x hx] at h
      omega
  · intro h; subst h; exact clz_zero n

-- 可执行测试（32 位特化抽查）
example : clz (0#32) = 32 := by decide
example : clz (0x80000000#32) = 0 := by decide
example : clz (0x00000001#32) = 31 := by decide
example : clz (0x0000000F#32) = 28 := by decide
example : clz (0x00F00000#32) = 8 := by decide
example : clz (1#4) = 3 := by decide
example : clz (0xF#4) = 0 := by decide

/- ========================================================================= -/
/- 4. Zip32（Library.scala:111-129）                                         -/
/- ========================================================================= -/

/-- `Zip32`：按 sz 将一对 32 位字的半字/字节交错（zip）。
    源码逐行对应：zipHalf = sz(0)|sz(1)，zipBytes = sz(0)。
    拼接用 `BitVec.append`（`++`，左操作数在高位）。 -/
def zip32 (sz : Bits 3) (a0 b0 : Bits 32) : Bits 64 :=
  let zipHalf : Bool := sz[[0]] || sz[[1]]
  let a1 : Bits 32 := (Mux zipHalf b0[[15,0]] a0[[31,16]]) ++ a0[[15,0]]
  let b1 : Bits 32 := b0[[31,16]] ++ (Mux zipHalf a0[[31,16]] b0[[15,0]])
  let zipBytes : Bool := sz[[0]]
  let a2 : Bits 32 :=
    a1[[31,24]] ++ (Mux zipBytes (a1[[15,8]] ++ a1[[23,16]]) a1[[23,8]]) ++ a1[[7,0]]
  let b2 : Bits 32 :=
    b1[[31,24]] ++ (Mux zipBytes (b1[[15,8]] ++ b1[[23,16]]) b1[[23,8]]) ++ b1[[7,0]]
  b2 ++ a2

/-- 规约（整字模式 sz=4）：out = b ++ a -/
theorem zip32_words (a b : Bits 32) : zip32 4#3 a b = b ++ a := by
  simp [zip32, get_bits, bit_at, Mux]
  bv_decide

/-- 规约（半字模式 sz=2）：out = (bhi ++ ahi) ++ (blo ++ alo) -/
theorem zip32_halves (a b : Bits 32) :
    zip32 2#3 a b = (b[[31,16]] ++ a[[31,16]]) ++ (b[[15,0]] ++ a[[15,0]]) := by
  simp [zip32, get_bits, bit_at, Mux]
  bv_decide

/-- 规约（字节模式 sz=1）：高/低半字各自字节交错 -/
theorem zip32_bytes (a b : Bits 32) :
    zip32 1#3 a b =
      (b[[31,24]] ++ (a[[31,24]] ++ b[[23,16]]) ++ a[[23,16]]) ++
      (b[[15,8]] ++ (a[[15,8]] ++ b[[7,0]]) ++ a[[7,0]]) := by
  simp [zip32, get_bits, bit_at, Mux]
  bv_decide

-- 可执行测试（LibraryTest.scala:102-127 的用例）
example : zip32 4#3 5#32 3163#32 = ((3163 <<< 32) ||| 5 : Nat) := by decide
example : zip32 2#3 ((7 <<< 16) ||| 3 : Bits 32) ((11 <<< 16) ||| 5 : Bits 32)
    = ((11 <<< 48) ||| (7 <<< 32) ||| (5 <<< 16) ||| 3 : Nat) := by decide
example : zip32 1#3 ((37 <<< 16) ||| (7 <<< 8) ||| 3 : Bits 32)
                    ((43 <<< 16) ||| (11 <<< 8) ||| 5 : Bits 32)
    = ((43 <<< 40) ||| (37 <<< 32) ||| (11 <<< 24) ||| (7 <<< 16) ||| (5 <<< 8) ||| 3 : Nat) := by
  decide

/- ========================================================================= -/
/- 5. Contains（Library.scala:138-142）                                      -/
/- ========================================================================= -/

/-- `Contains`：无符号区间判定 start ≤ idx < end -/
def contains {w : Nat} (idx start fin : Bits w) : Bool :=
  decide (start.toNat ≤ idx.toNat ∧ idx.toNat < fin.toNat)

theorem contains_eq_true_iff {w : Nat} (idx start fin : Bits w) :
    contains idx start fin = true ↔ start.toNat ≤ idx.toNat ∧ idx.toNat < fin.toNat := by
  simp [contains]

theorem contains_start {w : Nat} (start fin : Bits w) (h : start.toNat < fin.toNat) :
    contains start start fin = true := by
  simp [contains, h]

theorem contains_end_lt {w : Nat} (idx start fin : Bits w)
    (h : contains idx start fin = true) : idx.toNat < fin.toNat :=
  (contains_eq_true_iff idx start fin).mp h |>.2

-- 可执行测试
example : contains 5#8 3#8 8#8 = true := by decide
example : contains 8#8 3#8 8#8 = false := by decide
example : contains 2#8 3#8 8#8 = false := by decide

/- ========================================================================= -/
/- 6. RotateVectorLeft/Right、ShiftVectorLeft/Right                          -/
/-    （Library.scala:144-186）                                              -/
/-                                                                            -/
/-  Chisel `Vec.asUInt` 使 index 0 位于最低位，`rotateLeft` 向高位循环移动， -/
/-  故元素 o 移至下标 (o + shift) % n，即 out[j] = in[(j − shift) mod n]。    -/
/-  （源码注释「Result[i] = data[(i + shift) % data.size]」与实现/测试相反， -/
/-  见 RotateVectorRight 对称情形；LibraryTest.scala:129-175 的期望与这里的  -/
/-  定义一致。）                                                              -/
/- ========================================================================= -/

/-- `RotateVectorLeft`：out[j] = data[(j − shift) mod n] -/
def rotateVecLeft {n w : Nat} (hn : 0 < n) (data : Fin n → Bits w) (shift : Nat) :
    Fin n → Bits w :=
  fun j => data ⟨(j.val + (n - shift % n)) % n, Nat.mod_lt _ hn⟩

/-- `RotateVectorRight`：out[j] = data[(j + shift) mod n] -/
def rotateVecRight {n w : Nat} (hn : 0 < n) (data : Fin n → Bits w) (shift : Nat) :
    Fin n → Bits w :=
  fun j => data ⟨(j.val + shift % n) % n, Nat.mod_lt _ hn⟩

/-- 主规约（对应 LibraryTest.scala:129-151）：input[o] = output[(o + shift) % n] -/
theorem rotateVecLeft_spec {n w : Nat} (hn : 0 < n) (data : Fin n → Bits w)
    {o shift : Nat} (ho : o < n) (hs : shift < n) :
    rotateVecLeft hn data shift ⟨(o + shift) % n, Nat.mod_lt _ hn⟩ = data ⟨o, ho⟩ := by
  unfold rotateVecLeft
  congr 1
  apply Fin.ext
  show ((o + shift) % n + (n - shift % n)) % n = o
  rw [Nat.mod_eq_of_lt hs]
  by_cases h : o + shift < n
  · rw [Nat.mod_eq_of_lt h]
    have e : o + shift + (n - shift) = o + n := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt ho]
  · have h' : n ≤ o + shift := by omega
    rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (show o + shift - n < n by omega)]
    have e : o + shift - n + (n - shift) = o := by omega
    rw [e, Nat.mod_eq_of_lt ho]

/-- 主规约（对应 LibraryTest.scala:153-175）：input[o] = output[(o − shift) mod n] -/
theorem rotateVecRight_spec {n w : Nat} (hn : 0 < n) (data : Fin n → Bits w)
    {o shift : Nat} (ho : o < n) (hs : shift < n) :
    rotateVecRight hn data shift ⟨(o + n - shift) % n, Nat.mod_lt _ hn⟩ = data ⟨o, ho⟩ := by
  unfold rotateVecRight
  congr 1
  apply Fin.ext
  show ((o + n - shift) % n + shift % n) % n = o
  rw [Nat.mod_eq_of_lt hs]
  by_cases h : shift ≤ o
  · have h1 : n ≤ o + n - shift := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (show o + n - shift - n < n by omega)]
    have e : o + n - shift - n + shift = o := by omega
    rw [e, Nat.mod_eq_of_lt ho]
  · have h1 : o + n - shift < n := by omega
    rw [Nat.mod_eq_of_lt h1]
    have e : o + n - shift + shift = o + n := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt ho]

/-- shift 按 n 取模即得全部行为 -/
theorem rotateVecLeft_mod {n w : Nat} (hn : 0 < n) (data : Fin n → Bits w) (shift : Nat) :
    rotateVecLeft hn data shift = rotateVecLeft hn data (shift % n) := by
  unfold rotateVecLeft
  congr 1
  funext j
  congr 1
  apply Fin.ext
  show (j.val + (n - shift % n)) % n = (j.val + (n - shift % n % n)) % n
  rw [Nat.mod_mod]

/-- `ShiftVectorLeft`：元素向高下标移动 shift 位，空位补 0（不循环） -/
def shiftVecLeft {n w : Nat} (data : Fin n → Bits w) (shift : Nat) : Fin n → Bits w :=
  fun j => if h : shift ≤ j.val then
             data ⟨j.val - shift, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
           else bits_zero w

/-- `ShiftVectorRight`：元素向低下标移动 shift 位，空位补 0（不循环） -/
def shiftVecRight {n w : Nat} (data : Fin n → Bits w) (shift : Nat) : Fin n → Bits w :=
  fun j => if h : j.val + shift < n then data ⟨j.val + shift, h⟩ else bits_zero w

/-- 主规约：j ≥ shift 时 out[j] = data[j − shift] -/
theorem shiftVecLeft_of_le {n w : Nat} (data : Fin n → Bits w) {shift : Nat}
    (j : Fin n) (h : shift ≤ j.val) :
    shiftVecLeft data shift j
      = data ⟨j.val - shift, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ := by
  unfold shiftVecLeft; rw [dif_pos h]

/-- 主规约：j < shift 时 out[j] = 0（空位补零） -/
theorem shiftVecLeft_of_lt {n w : Nat} (data : Fin n → Bits w) {shift : Nat}
    (j : Fin n) (h : j.val < shift) :
    shiftVecLeft data shift j = bits_zero w := by
  unfold shiftVecLeft; rw [dif_neg (by omega)]

/-- 对应 LibraryTest.scala:177-203：input[o] = output[o + shift] -/
theorem shiftVecLeft_spec {n w : Nat} (data : Fin n → Bits w) {o shift : Nat}
    (h : o + shift < n) :
    shiftVecLeft data shift ⟨o + shift, h⟩
      = data ⟨o, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h⟩ := by
  rw [shiftVecLeft_of_le _ _ (Nat.le_add_left shift o)]
  congr 1
  apply Fin.ext
  show o + shift - shift = o
  omega

/-- 主规约：j + shift < n 时 out[j] = data[j + shift] -/
theorem shiftVecRight_spec {n w : Nat} (data : Fin n → Bits w) {o shift : Nat}
    (ho : o < n) (h : o + shift < n) :
    shiftVecRight data shift ⟨o, ho⟩ = data ⟨o + shift, h⟩ := by
  unfold shiftVecRight; rw [dif_pos h]

/-- 主规约：j + shift ≥ n 时 out[j] = 0（空位补零） -/
theorem shiftVecRight_of_ge {n w : Nat} (data : Fin n → Bits w) {shift : Nat}
    (j : Fin n) (h : n ≤ j.val + shift) :
    shiftVecRight data shift j = bits_zero w := by
  unfold shiftVecRight; rw [dif_neg (by omega)]

-- 可执行测试：4 元素 × 8 位向量
section VecTests

abbrev v4 : Fin 4 → Bits 8 := fun i => BitVec.ofNat 8 i.val

-- rotateVecLeft：input[o] = output[(o + shift) % n]
example : rotateVecLeft (by decide) v4 1 ⟨1, by decide⟩ = 0#8 := by decide
example : rotateVecLeft (by decide) v4 3 ⟨0, by decide⟩ = 1#8 := by decide
example : rotateVecLeft (by decide) v4 2 ⟨3, by decide⟩ = 1#8 := by decide
-- rotateVecRight：input[o] = output[(o − shift) mod n]
example : rotateVecRight (by decide) v4 1 ⟨0, by decide⟩ = 1#8 := by decide
example : rotateVecRight (by decide) v4 2 ⟨1, by decide⟩ = 3#8 := by decide
-- shiftVecLeft：o + shift < n 时 output[o+shift] = input[o]，j < shift 时为 0
example : shiftVecLeft v4 2 ⟨3, by decide⟩ = 1#8 := by decide
example : shiftVecLeft v4 2 ⟨1, by decide⟩ = 0#8 := by decide
-- shiftVecRight：output[o] = input[o+shift]，j + shift ≥ n 时为 0
example : shiftVecRight v4 2 ⟨0, by decide⟩ = 2#8 := by decide
example : shiftVecRight v4 2 ⟨3, by decide⟩ = 0#8 := by decide

end VecTests

/- ========================================================================= -/
/- 7. OneHotInOrder（Library.scala:188-195）                                 -/
/- ========================================================================= -/

/-- `OneHotInOrder`：检查布尔序列是否「先真后假」（1100 合法，1101 非法）。
    源码检测相邻的 false→true 跳变；此处以等价的递归形式定义。 -/
def oneHotInOrder : List Bool → Bool
  | [] => true
  | [_] => true
  | false :: true :: _ => false
  | _ :: b :: rest => oneHotInOrder (b :: rest)

theorem oneHotInOrder_true_cons (l : List Bool) :
    oneHotInOrder (true :: l) = oneHotInOrder l := by
  cases l with
  | nil => rfl
  | cons b r => cases b <;> cases r <;> rfl

theorem oneHotInOrder_false_false (l : List Bool) :
    oneHotInOrder (false :: false :: l) = oneHotInOrder (false :: l) := rfl

theorem oneHotInOrder_false_true (l : List Bool) :
    oneHotInOrder (false :: true :: l) = false := rfl

theorem oneHotInOrder_replicate (k m : Nat) :
    oneHotInOrder (List.replicate k true ++ List.replicate m false) = true := by
  induction k generalizing m with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.replicate_succ]
      cases m with
      | zero => rfl
      | succ m' =>
        rw [List.replicate_succ] at ih ⊢
        rw [oneHotInOrder_false_false]; exact ih
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, oneHotInOrder_true_cons]
    exact ih m

/-- 主规约：oneHotInOrder l = true 当且仅当 l 是「k 个 true 后接 m 个 false」 -/
theorem oneHotInOrder_spec (l : List Bool) :
    oneHotInOrder l = true ↔ ∃ k m, l = List.replicate k true ++ List.replicate m false := by
  constructor
  · intro h
    induction l with
    | nil => exact ⟨0, 0, rfl⟩
    | cons a t ih =>
      cases t with
      | nil =>
        cases a
        · exact ⟨0, 1, rfl⟩
        · exact ⟨1, 0, rfl⟩
      | cons b r =>
        cases a <;> cases b
        · rw [oneHotInOrder_false_false] at h
          obtain ⟨k, m, hm⟩ := ih h
          cases k with
          | zero =>
            simp only [List.replicate_zero, List.nil_append] at hm
            exact ⟨0, m + 1, by
              rw [List.replicate_zero, List.nil_append, List.replicate_succ, ← hm]⟩
          | succ k' =>
            rw [List.replicate_succ, List.cons_append] at hm
            simp only [List.cons.injEq] at hm
            exact absurd hm.1 (by decide)
        · rw [oneHotInOrder_false_true] at h
          exact absurd h (by decide)
        · rw [oneHotInOrder_true_cons] at h
          obtain ⟨k, m, hm⟩ := ih h
          cases k with
          | zero =>
            simp only [List.replicate_zero, List.nil_append] at hm
            exact ⟨1, m, by
              rw [show List.replicate 1 true = [true] from rfl, List.singleton_append, ← hm]⟩
          | succ k' =>
            rw [List.replicate_succ, List.cons_append] at hm
            simp only [List.cons.injEq] at hm
            exact absurd hm.1 (by decide)
        · rw [oneHotInOrder_true_cons] at h
          obtain ⟨k, m, hm⟩ := ih h
          exact ⟨k + 1, m, by rw [List.replicate_succ, List.cons_append, hm]⟩
  · rintro ⟨k, m, rfl⟩
    exact oneHotInOrder_replicate k m

-- 可执行测试（Library.scala:188 注释中的用例：1100 OK，1101 NOT OK）
example : oneHotInOrder [true, true, false, false] = true := by decide
example : oneHotInOrder [true, true, false, true] = false := by decide
example : oneHotInOrder [] = true := by decide
example : oneHotInOrder [false, false] = true := by decide
example : oneHotInOrder [false, true] = false := by decide

/- ========================================================================= -/
/- 8. LoopingCounter（Library.scala:197-226）                                -/
/- ========================================================================= -/

/-- `LoopingCounter`：循环计数器状态（Chisel Bundle），
    curr 在 [0, max] 内递增，到达 max（isFull）后回到 0。 -/
structure LoopingCounter (w : Nat) where
  curr : Bits w
  max  : Bits w
  deriving DecidableEq

namespace LoopingCounter

/-- `isEnabled`：max ≠ 0 时启用（Library.scala:203） -/
def isEnabled (c : LoopingCounter w) : Bool := c.max != 0

/-- `isFull`：curr 到达 max（Library.scala:205） -/
def isFull (c : LoopingCounter w) : Bool := c.curr == c.max

/-- `next`：满则归零，否则加一；max 不变（Library.scala:207-211） -/
def next (c : LoopingCounter w) : LoopingCounter w :=
  { curr := Mux c.isFull (bits_zero w) (c.curr + 1)
  , max  := c.max }

/-- `reset`：curr 归零，max 不变（Library.scala:213-217） -/
def reset (c : LoopingCounter w) : LoopingCounter w := { curr := bits_zero w, max := c.max }

/-- `LoopingCounter.apply`：初态 curr = 0（Library.scala:220-226） -/
def init (max : Bits w) : LoopingCounter w := { curr := bits_zero w, max := max }

/-- 循环不变量：curr ≤ max（curr 可以达到 max，见 isFull 定义） -/
def Inv (c : LoopingCounter w) : Prop := c.curr.toNat ≤ c.max.toNat

theorem isEnabled_eq_true_iff {w : Nat} (c : LoopingCounter w) :
    c.isEnabled = true ↔ c.max ≠ 0 := by
  simp [isEnabled]

theorem isFull_eq_true_iff {w : Nat} (c : LoopingCounter w) :
    c.isFull = true ↔ c.curr = c.max := by
  simp [isFull]

theorem next_max {w : Nat} (c : LoopingCounter w) : c.next.max = c.max := rfl

theorem next_curr_of_full {w : Nat} (c : LoopingCounter w) (h : c.isFull = true) :
    c.next.curr = bits_zero w := by
  simp [next, Mux, h]

theorem next_curr_of_not_full {w : Nat} (c : LoopingCounter w) (h : c.isFull = false) :
    c.next.curr = c.curr + 1 := by
  simp [next, Mux, h]

theorem reset_curr {w : Nat} (c : LoopingCounter w) : c.reset.curr = bits_zero w := rfl

theorem init_inv {w : Nat} (m : Bits w) : Inv (init m) := by
  simp [Inv, init, bits_zero]

/-- 不变量保持：next 维持 curr ≤ max -/
theorem next_preserves_inv {w : Nat} (c : LoopingCounter w) (h : Inv c) : Inv c.next := by
  by_cases hf : c.curr = c.max
  · have hfull : c.isFull = true := beq_iff_eq.mpr hf
    unfold Inv
    rw [next_curr_of_full c hfull]
    simp [bits_zero]
  · have hlt : c.curr.toNat < c.max.toNat :=
      Nat.lt_of_le_of_ne h (fun e => hf (BitVec.toNat_inj.mp e))
    have hfull : c.isFull = false := beq_eq_false_iff_ne.mpr hf
    unfold Inv
    rw [next_curr_of_not_full c hfull, next_max]
    have h1 : (1 : Bits w).toNat = 1 := by
      rw [show (1 : Bits w) = BitVec.ofNat w 1 from rfl, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := c.max.isLt; omega)
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by have := c.max.isLt; omega)]
    omega

/-- 步进：对状态连续应用 k 次 next -/
def stepN (c : LoopingCounter w) : Nat → LoopingCounter w
  | 0 => c
  | k + 1 => (stepN c k).next

theorem stepN_zero {w : Nat} (c : LoopingCounter w) : stepN c 0 = c := rfl

theorem stepN_max {w : Nat} (c : LoopingCounter w) (k : Nat) :
    (stepN c k).max = c.max := by
  induction k with
  | zero => rfl
  | succ k ih => simp [stepN, next, ih]

/-- 不变量在任意步数后保持：curr 始终 ≤ max -/
theorem stepN_inv {w : Nat} (c : LoopingCounter w) (h : Inv c) (k : Nat) :
    Inv (stepN c k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact next_preserves_inv _ ih

/-- 计数规约：从初态走 k（≤ max）步后 curr = k -/
theorem stepN_curr_toNat {w : Nat} (m : Bits w) (k : Nat) (hk : k ≤ m.toNat) :
    (stepN (init m) k).curr.toNat = k := by
  induction k with
  | zero => simp [stepN, init, bits_zero]
  | succ k ih =>
    have hk' : k ≤ m.toNat := by omega
    have hcur : (stepN (init m) k).curr.toNat = k := ih hk'
    have hlt : k < m.toNat := by omega
    have hne : (stepN (init m) k).curr ≠ m := by
      intro e; rw [e] at hcur; omega
    have hfull : (stepN (init m) k).isFull = false :=
      beq_eq_false_iff_ne.mpr (by rw [stepN_max]; exact hne)
    have h1 : (1 : Bits w).toNat = 1 := by
      rw [show (1 : Bits w) = BitVec.ofNat w 1 from rfl, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := m.isLt; omega)
    rw [stepN, next_curr_of_not_full _ hfull, BitVec.toNat_add, hcur, h1,
        Nat.mod_eq_of_lt (by have := m.isLt; omega)]

/-- 循环规约：从初态走 max + 1 步回到初态（模 max + 1 循环） -/
theorem stepN_cycle {w : Nat} (m : Bits w) :
    stepN (init m) (m.toNat + 1) = init m := by
  have hcur : (stepN (init m) m.toNat).curr = m :=
    BitVec.toNat_inj.mp (by rw [stepN_curr_toNat m m.toNat (Nat.le_refl _)])
  have hfull : (stepN (init m) m.toNat).isFull = true :=
    beq_iff_eq.mpr (by rw [stepN_max]; exact hcur)
  have hmax : (stepN (init m) m.toNat).max = m := by rw [stepN_max]; rfl
  rw [stepN]
  simp only [next, hfull, hmax]
  rfl

end LoopingCounter

-- 可执行测试：宽度 4、max = 3 的计数器
example : (LoopingCounter.init 3#4).isEnabled = true := by decide
example : (LoopingCounter.init 0#4).isEnabled = false := by decide
example : (LoopingCounter.stepN (LoopingCounter.init 3#4) 2).curr = 2#4 := by decide
example : (LoopingCounter.stepN (LoopingCounter.init 3#4) 3).curr = 3#4 := by decide
example : (LoopingCounter.stepN (LoopingCounter.init 3#4) 3).isFull = true := by decide
example : (LoopingCounter.stepN (LoopingCounter.init 3#4) 4).curr = 0#4 := by decide
example : LoopingCounter.stepN (LoopingCounter.init 3#4) 4 = LoopingCounter.init 3#4 := by decide
example : (LoopingCounter.init 0#4).next = LoopingCounter.init 0#4 := by decide
example : (LoopingCounter.stepN (LoopingCounter.init 3#4) 2).reset.curr = 0#4 := by decide

/- ========================================================================= -/
/- 9. Clamp（MathUtil.scala:19-23）                                          -/
/- ========================================================================= -/

/-- `Clamp`：SInt 有符号钳位，Mux(x > min, Mux(x < max, x, max), min)。 -/
def clamp {w : Nat} (x lo hi : Bits w) : Bits w :=
  Mux (decide (lo.toInt < x.toInt)) (Mux (decide (x.toInt < hi.toInt)) x hi) lo

/-- x ≤ lo 时结果为 lo（注意源码用严格大于，x = lo 时也取 lo，数值相同） -/
theorem clamp_of_le_lo {w : Nat} (x lo hi : Bits w) (h : x.toInt ≤ lo.toInt) :
    clamp x lo hi = lo := by
  unfold clamp Mux
  simp [show ¬(lo.toInt < x.toInt) from by omega]

/-- lo < x < hi 时结果为 x -/
theorem clamp_of_in_range {w : Nat} (x lo hi : Bits w)
    (h1 : lo.toInt < x.toInt) (h2 : x.toInt < hi.toInt) :
    clamp x lo hi = x := by
  unfold clamp Mux
  simp [h1, h2]

/-- lo < x 且 hi ≤ x 时结果为 hi -/
theorem clamp_of_ge_hi {w : Nat} (x lo hi : Bits w)
    (h1 : lo.toInt < x.toInt) (h2 : hi.toInt ≤ x.toInt) :
    clamp x lo hi = hi := by
  unfold clamp Mux
  simp [h1, show ¬(x.toInt < hi.toInt) from by omega]

/-- 主规约：lo ≤ hi 时钳位结果落在 [lo, hi] 内（有符号语义） -/
theorem clamp_inbounds {w : Nat} (x lo hi : Bits w) (h : lo.toInt ≤ hi.toInt) :
    lo.toInt ≤ (clamp x lo hi).toInt ∧ (clamp x lo hi).toInt ≤ hi.toInt := by
  unfold clamp Mux
  by_cases h1 : lo.toInt < x.toInt <;> by_cases h2 : x.toInt < hi.toInt <;>
    simp [h1, h2] <;> omega

-- 可执行测试（8 位有符号：0xF6 = −10，0xFB = −5）
example : clamp (0xF6#8) (0xFB#8) (0x05#8) = 0xFB#8 := by decide   -- −10 → −5
example : clamp (0x00#8) (0xFB#8) (0x05#8) = 0x00#8 := by decide   -- 0 在界内
example : clamp (0x10#8) (0xFB#8) (0x05#8) = 0x05#8 := by decide   -- 16 → 5
example : clamp (0x05#8) (0xFB#8) (0x05#8) = 0x05#8 := by decide   -- 上界处
example : clamp (0xFB#8) (0xFB#8) (0x05#8) = 0xFB#8 := by decide   -- 下界处

/- ========================================================================= -/
/- 10. 数值回归测试（移植重审补充；源文件已有测试保留在各节内，本节补充：     -/
/-     含自由变量的定理的具体数值实例、边界输入、此前无覆盖的函数路径）       -/
/- ========================================================================= -/

section LibraryFnsRegressionTests

-- muxOR_eq_zero_iff / muxOR_or_of_not_both 的数值实例
example : muxOR b1 (0x00 : Bits 8) = 0x00 := by decide          -- 选通但数据为 0 → 0
example : muxOR b0 (0x0F : Bits 8) ||| muxOR b1 (0xF0 : Bits 8)
    = Mux b0 (0x0F : Bits 8) (Mux b1 (0xF0 : Bits 8) (bits_zero 8)) := by decide

-- forceZero：完整序对（valid 标志透传；源文件只测了 .2）
example : forceZero (false, (0xDEADBEEF : Bits 32)) = (false, (0 : Bits 32)) := by decide
example : forceZero (true, (0x1234 : Bits 32)) = (true, (0x1234 : Bits 32)) := by decide

-- clz：补充实例 + clz_spec / clz_eq_n_iff 的数值实例
example : clz (0xFF : Bits 8) = 0 := by decide
example : clz (0x01 : Bits 8) = 7 := by decide
example : clz (0 : Bits 16) = 16 := by decide
example : 2 ^ (8 - 1 - clz (0x0F : Bits 8)) ≤ (0x0F : Bits 8).toNat
    ∧ (0x0F : Bits 8).toNat < 2 ^ (8 - clz (0x0F : Bits 8)) := by decide
example : 2 ^ (8 - 1 - clz (0x10 : Bits 8)) ≤ (0x10 : Bits 8).toNat
    ∧ (0x10 : Bits 8).toNat < 2 ^ (8 - clz (0x10 : Bits 8)) := by decide

-- zip32 边界：sz=0 与 sz=4 同为整字模式（zipHalf/zipBytes 均为 false）
example : zip32 0#3 5#32 3163#32 = zip32 4#3 5#32 3163#32 := by decide

-- contains 边界：下界含（contains_start 实例）、空区间、start > end
example : contains 3#8 3#8 8#8 = true := by decide
example : contains 5#8 5#8 5#8 = false := by decide
example : contains 7#8 8#8 3#8 = false := by decide

-- rotate/shift：shift ≥ n 的取模/补零行为（rotateVecLeft_mod 等定理的数值实例）
example : rotateVecLeft (by decide) (fun i : Fin 4 => BitVec.ofNat 8 i.val) 5 ⟨0, by decide⟩
    = rotateVecLeft (by decide) (fun i : Fin 4 => BitVec.ofNat 8 i.val) 1 ⟨0, by decide⟩ := by
  decide
example : rotateVecRight (by decide) (fun i : Fin 4 => BitVec.ofNat 8 i.val) 4 ⟨2, by decide⟩
    = 2#8 := by decide
example : shiftVecLeft (fun i : Fin 4 => BitVec.ofNat 8 i.val) 4 ⟨0, by decide⟩ = 0#8 := by decide
example : shiftVecRight (fun i : Fin 4 => BitVec.ofNat 8 i.val) 9 ⟨1, by decide⟩ = 0#8 := by decide

-- oneHotInOrder 补充实例（oneHotInOrder_spec / oneHotInOrder_replicate 的数值实例）
example : oneHotInOrder [true] = true := by decide
example : oneHotInOrder [true, false, true] = false := by decide
example : oneHotInOrder (List.replicate 3 true ++ List.replicate 2 false) = true := by decide

-- LoopingCounter：满宽 max 的完整循环（stepN_cycle / stepN_curr_toNat 的数值实例）
example : LoopingCounter.stepN (LoopingCounter.init 15#4) 16 = LoopingCounter.init 15#4 := by
  decide
example : (LoopingCounter.stepN (LoopingCounter.init 5#4) 3).curr.toNat = 3 := by decide
example : (LoopingCounter.stepN (LoopingCounter.init 0#4) 5).curr = 0#4 := by decide

-- clamp：负区间实例 + clamp_inbounds 的数值实例
example : clamp (0x80 : Bits 8) (0xF6 : Bits 8) (0x0A : Bits 8) = 0xF6 := by decide  -- −128 → −10
example : clamp (0x7F : Bits 8) (0xF6 : Bits 8) (0x0A : Bits 8) = 0x0A := by decide  -- 127 → 10
example : (0xFB#8).toInt ≤ (clamp (0xF6#8) (0xFB#8) (0x05#8)).toInt
    ∧ (clamp (0xF6#8) (0xFB#8) (0x05#8)).toInt ≤ (0x05#8).toInt := by decide

end LibraryFnsRegressionTests

end Ventus.Base
