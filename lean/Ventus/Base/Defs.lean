/- ========================================================================= -/
/-                           Defs.lean                                       -/
/-  位向量、寄存器文件、存储器等基础定义                                      -/
/-  直接使用 Lean 标准库中的 BitVec 与 Fin 类型                              -/
/-                                                                           -/
/-  移植自 coralNPU/lean/CoralNPU/Base/Defs.lean（2026-08-25），              -/
/-  移植时逐函数重审（"移植即重审"，Cat bug 教训），审查结论见各节注释。      -/
/- ========================================================================= -/

namespace Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 位类型与位向量别名                                                     -/
/- ========================================================================= -/

abbrev Bit := Bool

def b0 : Bit := false
def b1 : Bit := true

abbrev Bits (n : Nat) := BitVec n
abbrev Word := Bits 32

def bits_zero (n : Nat) : Bits n := BitVec.ofNat n 0
def bits_ones  (n : Nat) : Bits n := BitVec.allOnes n
def nat2bits   (n v : Nat) : Bits n := BitVec.ofNat n v
def bits2nat   {n : Nat} (bv : Bits n) : Nat := bv.toNat

/- 位访问：标准位编号 i=0 为最低位（与 Coq 中 bit_at 语义一致）。
   审查：i ≥ n 时返回 b0（越界默认 0），与注释一致，OK。 -/
def bit_at {n : Nat} (bv : Bits n) (i : Nat) : Bit :=
  if h : i < n then bv.getLsbD i else b0

/- 位切片：提取 [hi, lo]（含），结果中索引 0 对应原向量的 bit lo。
   审查：守卫 lo ≤ hi ∧ hi < n，越界返回全 0，与注释一致，OK。 -/
def get_bits {n : Nat} (bv : Bits n) (hi lo : Nat) : Bits (hi - lo + 1) :=
  if h : lo ≤ hi ∧ hi < n then
    bv.extractLsb' lo (hi - lo + 1)
  else
    bits_zero (hi - lo + 1)

/- 单比特提取简写 -/
notation:1024 x "[[" hi "," lo "]]" => get_bits x hi lo
notation:1024 x "[[" i "]]" => bit_at x i

/- 位拼接：hi 在高位，lo 在低位（与 Coq Cat 语义一致）。
   审查（重点，历史 Cat bug 发生处）：`hi.zeroExtend (n+m) <<< n` 把 hi 左移 n 位，
   与低 n 位的 lo 按位或——正确实现拼接语义。coralNPU 2026-08-19 已修复原版
   "直接 OR 未移位"的 bug，此处移植的是修复后版本。 -/
def Cat {m n : Nat} (hi : Bits m) (lo : Bits n) : Bits (n + m) :=
  (hi.zeroExtend (n + m) <<< n) ||| lo.zeroExtend (n + m)

infixl:55 " @ " => Cat

/- Cat 回归测试：拼接语义固定 -/
example : Cat (0xA : Bits 4) (0x5 : Bits 4) = (0xA5 : Bits 8) := by decide
example : Cat (0x0 : Bits 4) (0xF : Bits 4) = (0x0F : Bits 8) := by decide
example : Cat (1 : Bits 1) (0 : Bits 1) = (2 : Bits 2) := by decide
example : Cat (0xFF : Bits 8) (0x00 : Bits 8) = (0xFF00 : Bits 16) := by decide

/- 位复制 -/
def Fill (n : Nat) (b : Bit) : Bits n :=
  if b then BitVec.allOnes n else BitVec.ofNat n 0

/- 零扩展：结果宽度 n + m -/
def ZeroExt {n : Nat} (m : Nat) (bv : Bits n) : Bits (n + m) :=
  bv.zeroExtend (n + m)

/- 符号扩展：结果宽度 n + m -/
def SignExt {n : Nat} (m : Nat) (bv : Bits n) : Bits (n + m) :=
  bv.signExtend (n + m)

/- ========================================================================= -/
/- 2. 位运算                                                                 -/
/- ========================================================================= -/

def bits_not {n : Nat} (a : Bits n) : Bits n := ~~~a
def bits_and {n : Nat} (a b : Bits n) : Bits n := a &&& b
def bits_or  {n : Nat} (a b : Bits n) : Bits n := a ||| b
def bits_xor {n : Nat} (a b : Bits n) : Bits n := a ^^^ b
def bits_add {n : Nat} (a b : Bits n) : Bits n := a + b
def bits_sub {n : Nat} (a b : Bits n) : Bits n := a - b
def bits_mul {n : Nat} (a b : Bits n) : Bits n := a * b
/- 审查：除零返回 0。注意这与 RISC-V 语义（除零得全 1）不同——这是基础库约定，
   建模具体模块（如 IntDivMod）时须按 Chisel 源码确认实际行为，不得默认本约定。 -/
def bits_div {n : Nat} (a b : Bits n) : Bits n :=
  if b = bits_zero n then bits_zero n else a / b

/- 相等比较返回 Bit -/
def bits_eq {n : Nat} (a b : Bits n) : Bit :=
  a = b

/- 无符号小于：a < b -/
def bits_ltu {n : Nat} (a b : Bits n) : Bit :=
  a.toNat < b.toNat

/- 无符号大于等于/小于等于/大于 -/
def bits_geu {n : Nat} (a b : Bits n) : Bit := ¬bits_ltu a b
def bits_gtu {n : Nat} (a b : Bits n) : Bit := bits_ltu b a
def bits_leu {n : Nat} (a b : Bits n) : Bit := ¬bits_ltu b a

/- 有符号小于：比较符号位后再按无符号比较。
   审查：符号不同则负者小；符号相同退化为无符号比较（同号时 toNat 序与补码序一致），正确。 -/
def bits_lts {n : Nat} (a b : Bits n) : Bit :=
  let sign_a := a.msb
  let sign_b := b.msb
  if sign_a && !sign_b then true
  else if !sign_a && sign_b then false
  else bits_ltu a b

def bits_ges {n : Nat} (a b : Bits n) : Bit := ¬bits_lts a b

/- 移位操作 -/
def bits_shl {n : Nat} (a : Bits n) (amt : Nat) : Bits n := a <<< amt
def bits_shr {n : Nat} (a : Bits n) (amt : Nat) : Bits n := a >>> amt
def bits_sar {n : Nat} (a : Bits n) (amt : Nat) : Bits n := a.sshiftRight amt

/- 不等比较 -/
def bits_neq {n : Nat} (a b : Bits n) : Bit := ¬bits_eq a b

/- 运算符记号 -/
infixl:40 " .& " => bits_and
infixl:50 " .| " => bits_or
infixl:45 " .^ " => bits_xor
infixl:50 " .+ " => bits_add
infixl:50 " .- " => bits_sub
infixl:40 " .* " => bits_mul
infixl:40 " ./ " => bits_div
infixl:70 " .== " => bits_eq
infixl:70 " .!= " => bits_neq
infixl:70 " .< " => bits_ltu
infixl:70 " .>= " => bits_geu
infixl:70 " .> " => bits_gtu
infixl:70 " .<= " => bits_leu
infixl:56 " .<< " => bits_shl
infixl:56 " .>> " => bits_shr
notation:65 ".~" x => bits_not x

/- ========================================================================= -/
/- 3. 寄存器文件与存储器                                                     -/
/- ========================================================================= -/

abbrev XLEN : Nat := 32
def NREGS : Nat := 32

def RegFile (n w : Nat) : Type := Fin n → Bits w

def rf_read {n w : Nat} (rf : RegFile n w) (i : Fin n) : Bits w :=
  rf i

def rf_write {n w : Nat} (rf : RegFile n w) (i : Fin n) (v : Bits w) : RegFile n w :=
  fun j => if i = j then v else rf j

def rf_zero (n w : Nat) : RegFile n w :=
  fun _ => bits_zero w

def Memory (size w : Nat) : Type := Fin size → Bits w

def mem_read {size w : Nat} (mem : Memory size w) (addr : Fin size) : Bits w :=
  mem addr

def mem_write {size w : Nat} (mem : Memory size w) (addr : Fin size) (v : Bits w) : Memory size w :=
  fun j => if addr = j then v else mem j

def mem_zero (size w : Nat) : Memory size w :=
  fun _ => bits_zero w

/- ========================================================================= -/
/- 4. 多路选择器与辅助函数                                                   -/
/- ========================================================================= -/

def Mux {A : Type} (sel : Bit) (t f : A) : A :=
  if sel then t else f

macro "IF" c:term "THEN" t:term "ELSE" e:term : term =>
  `(Mux $c $t $e)

/- 将 Word 转换为存储器地址（字节地址转字地址） -/
def word_to_addr {size : Nat} (w : Word) (h : size > 0) : Option (Fin size) :=
  let addr := w.toNat / 4
  if h' : addr < size then some ⟨addr, h'⟩ else none

/- 寄存器索引转换 -/
def reg_idx (r : Bits 5) : Fin NREGS :=
  let idx := r.toNat % NREGS
  have h : idx < NREGS := Nat.mod_lt _ (by decide)
  ⟨idx, h⟩

/- 程序加载辅助函数 -/
def load_program_aux {size w : Nat} (mem : Memory size w)
    (prog : List (Bits w)) (addr : Nat) (h : size > 0) : Memory size w :=
  match prog with
  | [] => mem
  | inst :: rest =>
    if h' : addr < size then
      load_program_aux (mem_write mem ⟨addr, h'⟩ inst) rest (addr + 1) h
    else
      mem

/- 写后读引理 -/
theorem rf_read_write_same {n w : Nat} (rf : RegFile n w) (i : Fin n) (v : Bits w) :
    rf_read (rf_write rf i v) i = v := by
  simp [rf_read, rf_write]

theorem rf_read_write_diff {n w : Nat} (rf : RegFile n w) (i j : Fin n) (v : Bits w)
    (h : i ≠ j) : rf_read (rf_write rf i v) j = rf_read rf j := by
  simp [rf_read, rf_write, h]

theorem mem_read_write_same {size w : Nat} (mem : Memory size w) (addr : Fin size) (v : Bits w) :
    mem_read (mem_write mem addr v) addr = v := by
  simp [mem_read, mem_write]

theorem mem_read_write_diff {size w : Nat} (mem : Memory size w) (a1 a2 : Fin size) (v : Bits w)
    (h : a1 ≠ a2) : mem_read (mem_write mem a1 v) a2 = mem_read mem a2 := by
  simp [mem_read, mem_write, h]

/- ========================================================================= -/
/- 5. 数值回归测试（移植重审的判收依据，全部 `by decide`）                    -/
/- ========================================================================= -/

section DefsRegressionTests

open Ventus.Base

-- bit_at / get_bits
example : bit_at (0b1010 : Bits 4) 0 = false := by decide
example : bit_at (0b1010 : Bits 4) 1 = true := by decide
example : bit_at (0b1010 : Bits 4) 9 = false := by decide        -- 越界默认 0
example : (0xAB : Bits 8)[[7, 4]] = (0xA : Bits 4) := by decide
example : (0xAB : Bits 8)[[3, 0]] = (0xB : Bits 4) := by decide
example : (0xAB : Bits 8)[[9, 2]] = (0 : Bits 8) := by decide    -- 越界全 0

-- Fill / ZeroExt / SignExt
example : Fill 4 true = (0xF : Bits 4) := by decide
example : Fill 4 false = (0x0 : Bits 4) := by decide
example : ZeroExt 4 (0xB : Bits 4) = (0x0B : Bits 8) := by decide
example : SignExt 4 (0xB : Bits 4) = (0xFB : Bits 8) := by decide
example : SignExt 4 (0x5 : Bits 4) = (0x05 : Bits 8) := by decide

-- 位运算
example : bits_add (0xFF : Bits 8) 1 = 0 := by decide            -- 回绕
example : bits_sub (0 : Bits 8) 1 = 0xFF := by decide
example : bits_mul (0x10 : Bits 8) 0x10 = 0 := by decide         -- 溢出截断
example : bits_div (7 : Bits 8) 2 = 3 := by decide
example : bits_div (7 : Bits 8) 0 = 0 := by decide               -- 除零约定：0
example : bits_not (0x0F : Bits 8) = 0xF0 := by decide

-- 比较
example : bits_eq (5 : Bits 8) 5 = true := by decide
example : bits_neq (5 : Bits 8) 6 = true := by decide
example : bits_ltu (0xFF : Bits 8) 0 = false := by decide
example : bits_lts (0xFF : Bits 8) 0 = true := by decide         -- -1 < 0（有符号）
example : bits_lts (0x80 : Bits 8) 0x7F = true := by decide      -- -128 < 127
example : bits_lts (0xFE : Bits 8) 0xFF = true := by decide      -- -2 < -1
example : bits_ges (0 : Bits 8) 0xFF = true := by decide         -- 0 ≥ -1

-- 移位
example : bits_shl (1 : Bits 8) 7 = 0x80 := by decide
example : bits_shr (0x80 : Bits 8) 7 = 1 := by decide
example : bits_sar (0x80 : Bits 8) 7 = 0xFF := by decide         -- 算术右移符号扩展

-- RegFile / Memory 写后读
example : rf_read (rf_write (rf_zero 4 8) ⟨2, by decide⟩ 0xAB) ⟨2, by decide⟩ = 0xAB := by decide
example : rf_read (rf_write (rf_zero 4 8) ⟨2, by decide⟩ 0xAB) ⟨1, by decide⟩ = 0 := by decide
example : mem_read (mem_write (mem_zero 4 8) ⟨3, by decide⟩ 0xCD) ⟨3, by decide⟩ = 0xCD := by decide

-- Mux / word_to_addr / reg_idx
example : Mux true (1 : Bits 8) 2 = 1 := by decide
example : Mux false (1 : Bits 8) 2 = 2 := by decide
example : word_to_addr (16 : Word) (by decide : 8 > 0) = some ⟨4, by decide⟩ := by decide
example : word_to_addr (0x1C : Word) (by decide : 8 > 0) = some ⟨7, by decide⟩ := by decide
example : word_to_addr (0x20 : Word) (by decide : 8 > 0) = none := by decide  -- 越界
example : reg_idx (31 : Bits 5) = ⟨31, by decide⟩ := by decide
example : reg_idx (0 : Bits 5) = ⟨0, by decide⟩ := by decide

end DefsRegressionTests

end Ventus.Base
