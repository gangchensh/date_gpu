/- ========================================================================= -/
/-                          MemLaws.lean                                     -/
/-  存储接口契约库：读/写/初始化定律 + 两个模型实例 + 通用便捷引理            -/
/-                                                                            -/
/-  设计决策（项目约定）：大存储（TCM/SRAM/Cache）不做 `Fin n → BitVec w`     -/
/-  具体建模；上层定理一律以 `[MemLaws M Addr Data]` 实例参数对任意满足       -/
/-  读写律的存储全称量化。本文件零 axiom、零 sorry。                          -/
/-                                                                            -/
/-  移植自 coralNPU/lean/CoralNPU/Base/MemLaws.lean（2026-08-25），           -/
/-  移植时逐定义重审（"移植即重审"，Cat bug 教训）：全部定义/定理与文档       -/
/-  注释语义核对一致，无疑点；补加的数值回归测试见文末第 6 节。               -/
/- ========================================================================= -/

/- ## 使用说明

   上层模块以 `[MemLaws M Addr Data]` 实例参数陈述定理，存储状态抽象为任意
   类型 `M`，只通过 `read / write / init / initData` 四条接口与三条定律交互：

     theorem my_load_store {M : Type} [MemLaws M Word (Bits 32)]
         (m : M) (a : Word) (v : Bits 32) :
         MemLaws.read (MemLaws.write m a v) a = v :=
       MemLaws.read_write_same m a v

   模型选择：
   - 小存储 / 可执行测试：用 `RegFile n w`（即 `Fin n → BitVec w`），
     实例 `instMemLawsRegFile` 已注册（`Memory size w` 展开后同一类型，同样适用）；
   - 32 位全地址空间的 TCM 抽象：用稀疏表 `SparseMem Addr Data`
     （未写地址读取返回 `Inhabited.default`，对 `BitVec w` 即全 0），实例已注册。

   注意：`MemLaws.init` / `MemLaws.initData` 的地址/数据（或存储）类型是显式参数，
   请用便捷形式 `MemLaws.initOf M` / `MemLaws.initDataOf M`（类型由实例推断）。
-/

import Ventus.Base.Defs

namespace Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 存储接口契约                                                           -/
/- ========================================================================= -/

/-- 存储接口契约：类型 `M` 是存储状态，`Addr` 为地址、`Data` 为数据。
    任何满足下列三条读写定律的类型均可作为上层定理的存储模型。
    `Addr`/`Data` 标为 `outParam`：由存储类型 `M` 经实例推断。 -/
class MemLaws (M : Type) (Addr : outParam Type) (Data : outParam Type) [DecidableEq Addr] where
  /-- 读操作 -/
  read : M → Addr → Data
  /-- 写操作 -/
  write : M → Addr → Data → M
  /-- 初始（上电/复位）存储状态 -/
  init : M
  /-- 初始状态下任意地址的读出值（约定值，如全 0） -/
  initData : Data
  /-- 写后读同址：读到刚写入的值 -/
  read_write_same : ∀ (m : M) (a : Addr) (v : Data),
    read (write m a v) a = v
  /-- 写后读异址：不影响其他地址的内容 -/
  read_write_diff : ∀ (m : M) (a b : Addr) (v : Data),
    a ≠ b → read (write m a v) b = read m b
  /-- 初始化读：初始状态任意地址读出约定值 -/
  read_init : ∀ a : Addr, read init a = initData

namespace MemLaws

/-- `init` 的便捷形式：以存储类型 `M` 为显式参数，地址/数据类型由实例（outParam）推断 -/
abbrev initOf (M : Type) {Addr Data : Type} [DecidableEq Addr] [self : MemLaws M Addr Data] : M :=
  MemLaws.init

/-- `initData` 的便捷形式：以存储类型 `M` 为显式参数 -/
abbrev initDataOf (M : Type) {Addr Data : Type} [DecidableEq Addr] [self : MemLaws M Addr Data] : Data :=
  MemLaws.initData M

end MemLaws

/- ========================================================================= -/
/- 2. 通用便捷引理（对任意 MemLaws 实例成立，上层证明实际使用的形态）        -/
/- ========================================================================= -/

namespace MemLaws

variable {M Addr Data : Type} [DecidableEq Addr] [MemLaws M Addr Data]

/-- 写后读的分支形式：同址得新值，异址保持原值 -/
theorem read_write (m : M) (a b : Addr) (v : Data) :
    read (write m a v) b = (if b = a then v else read m b) := by
  by_cases h : b = a
  · subst h; simp [read_write_same]
  · simp [read_write_diff m a b v (Ne.symm h), h]

/-- 写覆盖：同一地址连续写两次，后写覆盖先写 -/
theorem read_write_shadow (m : M) (a b : Addr) (u v : Data) :
    read (write (write m a u) a v) b = read (write m a v) b := by
  simp only [read_write]
  by_cases h : b = a <;> simp [h]

/-- 写读交换：两个不同地址的写入可交换（读视角下结果相同） -/
theorem read_write_comm (m : M) (a b c : Addr) (u v : Data) (hab : a ≠ b) :
    read (write (write m a u) b v) c = read (write (write m b v) a u) c := by
  simp only [read_write]
  by_cases hca : c = a
  · subst hca; simp [hab]
  · by_cases hcb : c = b
    · subst hcb; simp [Ne.symm hab]
    · simp [hca, hcb]

/-- 初始化后写再读：同址得写入值，异址得初始约定值 -/
theorem read_write_init (a b : Addr) (v : Data) :
    read (write (initOf M) a v) b = (if b = a then v else initDataOf M) := by
  show read (write (initOf M) a v) b = (if b = a then v else MemLaws.initData M)
  rw [read_write, read_init]

/-- 两次写入都不命中：读出值与原始存储一致 -/
theorem read_write_write_diff (m : M) (a b c : Addr) (u v : Data)
    (hca : c ≠ a) (hcb : c ≠ b) :
    read (write (write m a u) b v) c = read m c := by
  rw [read_write_diff (write m a u) b c v (Ne.symm hcb),
      read_write_diff m a c u (Ne.symm hca)]

end MemLaws

/- ========================================================================= -/
/- 3. 实例一：函数模型 `RegFile n w`（小存储 / 可执行测试用）                -/
/- ========================================================================= -/

/-- `Fin n → BitVec w` 的 MemLaws 实例，定律直接复用 Defs.lean 的写后读引理 -/
instance instMemLawsRegFile {n w : Nat} : MemLaws (RegFile n w) (Fin n) (Bits w) where
  read := rf_read
  write := rf_write
  init := rf_zero n w
  initData := bits_zero w
  read_write_same := fun m a v => rf_read_write_same m a v
  read_write_diff := fun m a b v h => rf_read_write_diff m a b v h
  read_init := fun _ => rfl

/- ========================================================================= -/
/- 4. 实例二：稀疏关联表 `SparseMem`（32 位全地址空间 TCM 抽象用）           -/
/-                                                                            -/
/-  语义：存储为 `Addr → Option Data` 的部分映射；已写地址读出 `some` 的值， -/
/-  未写地址读出 `Inhabited.default`（对 `BitVec w` 即全 0）。`init` 为空表。 -/
/- ========================================================================= -/

/-- 稀疏存储：仅记录被写过的地址，适合 32 位全地址空间等大地址空间抽象 -/
structure SparseMem (Addr : Type) (Data : Type) [Inhabited Data] where
  /-- 部分映射：`none` 表示该地址从未被写入 -/
  table : Addr → Option Data

namespace SparseMem

variable {Addr Data : Type} [DecidableEq Addr] [Inhabited Data]

/-- 读：已写地址读出写入值，未写地址读出默认值 -/
def read (m : SparseMem Addr Data) (a : Addr) : Data :=
  (m.table a).getD default

/-- 写：在地址 `a` 处记录新值，其余地址不变 -/
def write (m : SparseMem Addr Data) (a : Addr) (v : Data) : SparseMem Addr Data :=
  ⟨fun b => if b = a then some v else m.table b⟩

/-- 初始状态：空表，任何地址都读出默认值 -/
def init : SparseMem Addr Data :=
  ⟨fun _ => none⟩

/-- 稀疏表的 MemLaws 实例 -/
instance instMemLawsSparseMem : MemLaws (SparseMem Addr Data) Addr Data where
  read := read
  write := write
  init := init
  initData := default
  read_write_same := by intro m a v; simp [read, write]
  read_write_diff := by intro m a b v h; simp [read, write, Ne.symm h]
  read_init := by intro a; rfl

end SparseMem

/- ========================================================================= -/
/- 5. 可执行测试：实例一在深度 4、宽度 8 上的写后读 / 初始化读               -/
/- ========================================================================= -/

section ExecutableTests

/-- 测试用小存储：深度 4、宽度 8 -/
abbrev TestMem : Type := RegFile 4 8

-- 写后读同址：读到刚写入的值
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestMem) (1 : Fin 4) 0xAB#8) (1 : Fin 4)
      = 0xAB#8 := by
  decide

-- 写后读异址：读到初始值 0
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestMem) (1 : Fin 4) 0xAB#8) (2 : Fin 4)
      = 0x00#8 := by
  decide

-- 初始化读：任意地址读出 0
example : MemLaws.read (MemLaws.initOf TestMem) (0 : Fin 4) = 0x00#8 := by decide
example : MemLaws.read (MemLaws.initOf TestMem) (3 : Fin 4) = 0x00#8 := by decide

-- 异地址两次写互不影响
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestMem) (0 : Fin 4) 0x11#8)
        (3 : Fin 4) 0x22#8)
      (0 : Fin 4) = 0x11#8 := by
  decide

-- 同地址两次写：后写覆盖先写
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestMem) (2 : Fin 4) 0x55#8)
        (2 : Fin 4) 0xAA#8)
      (2 : Fin 4) = 0xAA#8 := by
  decide

-- 稀疏实例的使用形态示例：32 位地址空间（Word 地址、字节数据），走通用定律
example (a : Word) (v : Bits 8) :
    MemLaws.read (MemLaws.write (MemLaws.initOf (SparseMem Word (Bits 8))) a v) a = v :=
  MemLaws.read_write_same (MemLaws.initOf (SparseMem Word (Bits 8))) a v

end ExecutableTests

/- ========================================================================= -/
/- 6. 数值回归测试（2026-08-25 移植重审时补加，全部 `by decide`）             -/
/-                                                                            -/
/-  覆盖源文件中无可执行测试的部分：                                          -/
/-  - SparseMem 的具体数值行为（源文件只有走通用定律的自由变量示例）；        -/
/-  - 第 2 节通用便捷引理的具体数值实例（引理含自由变量，无法直接 decide，    -/
/-    按其陈述给出具体地址/数值的实例）。                                     -/
/- ========================================================================= -/

section MemLawsRegressionTests

/-- 测试用稀疏存储：4 位地址、8 位数据 -/
abbrev TestSparseMem : Type := SparseMem (Bits 4) (Bits 8)

-- SparseMem.read / write / init：初始化读任意地址得默认值 0
example : MemLaws.read (MemLaws.initOf TestSparseMem) (0x0 : Bits 4) = 0x00#8 := by decide
example : MemLaws.read (MemLaws.initOf TestSparseMem) (0xF : Bits 4) = 0x00#8 := by decide

-- SparseMem：写后读同址，读到刚写入的值
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestSparseMem) (0x3 : Bits 4) 0xAB#8)
      (0x3 : Bits 4) = 0xAB#8 := by
  decide

-- SparseMem：写后读异址，读出默认值 0
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestSparseMem) (0x3 : Bits 4) 0xAB#8)
      (0x4 : Bits 4) = 0x00#8 := by
  decide

-- SparseMem：异地址两次写互不影响
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestSparseMem) (0x1 : Bits 4) 0x11#8)
        (0x2 : Bits 4) 0x22#8)
      (0x1 : Bits 4) = 0x11#8 := by
  decide

-- SparseMem：同地址两次写，后写覆盖先写
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestSparseMem) (0x5 : Bits 4) 0x55#8)
        (0x5 : Bits 4) 0xAA#8)
      (0x5 : Bits 4) = 0xAA#8 := by
  decide

-- read_write（分支形式）同址分支的具体实例（RegFile）
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestMem) (1 : Fin 4) 0xAB#8) (1 : Fin 4)
      = (if (1 : Fin 4) = (1 : Fin 4) then 0xAB#8
         else MemLaws.read (MemLaws.initOf TestMem) (1 : Fin 4)) := by
  decide

-- read_write（分支形式）异址分支的具体实例（SparseMem）
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestSparseMem) (0x3 : Bits 4) 0xAB#8)
      (0x7 : Bits 4)
      = (if (0x7 : Bits 4) = (0x3 : Bits 4) then 0xAB#8
         else MemLaws.read (MemLaws.initOf TestSparseMem) (0x7 : Bits 4)) := by
  decide

-- read_write_shadow 的具体实例（RegFile）：覆盖写后与只写后者读数一致
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestMem) (2 : Fin 4) 0x55#8)
        (2 : Fin 4) 0xAA#8)
      (0 : Fin 4)
      = MemLaws.read (MemLaws.write (MemLaws.initOf TestMem) (2 : Fin 4) 0xAA#8) (0 : Fin 4) := by
  decide

-- read_write_comm 的具体实例（SparseMem）：两个不同地址写入可交换
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestSparseMem) (0x1 : Bits 4) 0x11#8)
        (0x2 : Bits 4) 0x22#8)
      (0x2 : Bits 4)
      = MemLaws.read
        (MemLaws.write (MemLaws.write (MemLaws.initOf TestSparseMem) (0x2 : Bits 4) 0x22#8)
          (0x1 : Bits 4) 0x11#8)
        (0x2 : Bits 4) := by
  decide

-- read_write_init 的具体实例（RegFile）：init 后写，异址读出初始约定值 0
example :
    MemLaws.read (MemLaws.write (MemLaws.initOf TestMem) (1 : Fin 4) 0xAB#8) (3 : Fin 4)
      = 0x00#8 := by
  decide

-- read_write_write_diff 的具体实例（RegFile）：两次写入都不命中，读出原值
example :
    MemLaws.read
      (MemLaws.write (MemLaws.write (MemLaws.initOf TestMem) (0 : Fin 4) 0x11#8)
        (1 : Fin 4) 0x22#8)
      (3 : Fin 4)
      = MemLaws.read (MemLaws.initOf TestMem) (3 : Fin 4) := by
  decide

end MemLawsRegressionTests

end Ventus.Base
