/- ========================================================================= -/
/-                        DefsSpec.lean                                      -/
/-  Defs.lean 基础函数的规约与数值回归套件                                    -/
/-                                                                            -/
/-  移植自 coralNPU/lean/CoralNPU/Base/DefsSpec.lean（2026-08-25），           -/
/-  移植时逐定义/逐定理重审（"移植即重审"），审查结论见本文件报告与各节注释。 -/
/-                                                                            -/
/-  背景：Defs.lean 的 `Cat` 曾存在「hi 未左移」bug（直接 OR 而非拼接），      -/
/-  已修复为 `(hi.zeroExtend (n+m) <<< n) ||| lo.zeroExtend (n+m)`。本文件：   -/
/-  1. 从修复后的定义证明 Cat 的一般性正确性定理（toNat 主定理 + 位级规约      -/
/-     + 与标准库 `BitVec.append` 的桥接）；                                   -/
/-  2. 对 Defs.lean 全部公共纯函数做数值回归（`by decide`，含 0/全 1/符号位/   -/
/-     跨拼接边界/移位 0 与满宽等边界），防止再潜伏 Cat 类 bug。               -/
/-  本文件零 sorry。                                                         -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. Cat 的一般性正确性定理                                                  -/
/- ========================================================================= -/

/-- Cat 主定理（toNat 规约）：拼接的数值语义为 hi * 2^n + lo。
    证明路径：toNat_or → toNat_shiftLeft → zeroExtend 经 setWidth 归约为原值，
    关键不重叠事实由 `Nat.shiftLeft_add_eq_or_of_lt`（lo < 2^n）给出。
    审查：命题与 Cat 定义（hi 左移 n 位后与 lo 按位或）语义一致，OK。 -/
theorem cat_toNat {m n : Nat} (hi : Bits m) (lo : Bits n) :
    bits2nat (Cat hi lo) = bits2nat hi * 2 ^ n + bits2nat lo := by
  unfold Cat bits2nat
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  simp only [BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth_of_le (show m ≤ n + m by omega),
    BitVec.toNat_setWidth_of_le (show n ≤ n + m by omega)]
  have hlt : hi.toNat <<< n < 2 ^ (n + m) := by
    rw [Nat.shiftLeft_eq, Nat.add_comm n m, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hi.isLt (Nat.two_pow_pos n)
  rw [Nat.mod_eq_of_lt hlt, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt]

/-- Cat 位级规约（低位部分）：i < n 时取 lo 的第 i 位。
    审查：前提 i < n 保证两侧 bit_at 均不越界（不触发越界默认 b0 分支），OK。 -/
theorem cat_bit_at_lo {m n : Nat} (hi : Bits m) (lo : Bits n) (i : Nat) (h : i < n) :
    (Cat hi lo)[[i]] = lo[[i]] := by
  unfold bit_at Cat
  rw [dif_pos (show i < n + m by omega), dif_pos h]
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth,
      BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  simp [h, show i < n + m by omega]

/-- Cat 位级规约（高位部分）：n ≤ i < n + m 时取 hi 的第 i − n 位。
    审查：前提保证 i 落在 hi 占据的高位区间、i − n < m 不越界，OK。 -/
theorem cat_bit_at_hi {m n : Nat} (hi : Bits m) (lo : Bits n) (i : Nat)
    (h1 : n ≤ i) (h2 : i < n + m) :
    (Cat hi lo)[[i]] = hi[[i - n]] := by
  unfold bit_at Cat
  rw [dif_pos h2, dif_pos (show i - n < m by omega)]
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth,
      BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  rw [BitVec.getLsbD_of_ge _ _ h1]
  simp [h2, show ¬(i < n) from by omega, show i - n < n + m by omega]

/-- 桥接：Cat 与标准库 `BitVec.append` 一致（仅宽度指标差一个加法交换）。
    审查：BitVec.append hi lo : Bits (m + n)，cast (Nat.add_comm m n) 把宽度
    指标转成 n + m，与 Cat 结果宽度一致；toNat 规约由 cat_toNat 提供，OK。 -/
theorem cat_eq_append_cast {m n : Nat} (hi : Bits m) (lo : Bits n) :
    Cat hi lo = (hi ++ lo).cast (Nat.add_comm m n) := by
  apply BitVec.toNat_inj.mp
  have h1 : (Cat hi lo).toNat = hi.toNat * 2 ^ n + lo.toNat := cat_toNat hi lo
  rw [BitVec.toNat_cast, BitVec.toNat_append, h1,
      ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt lo.isLt]

/-- 拼合还原：任意 16 位向量等于其高 8 位与低 8 位的 Cat（bv_decide 抽查） -/
example (x : BitVec 16) : Cat x[[15,8]] x[[7,0]] = x := by
  simp [Cat, get_bits]
  bv_decide

/-- ZeroExt 与「高位拼 0」一致 -/
example (x : BitVec 8) : ZeroExt 8 x = Cat (0#8) x := by
  simp [Cat, ZeroExt]

/-- SignExt 与「高位拼符号位复制」一致 -/
example (x : BitVec 8) : SignExt 8 x = Cat (Fill 8 x[[7]]) x := by
  simp [Cat, SignExt, Fill, bit_at]
  bv_decide

/- ========================================================================= -/
/- 2. 数值回归套件（by decide）                                              -/
/- ========================================================================= -/

section Regression

/- ---- bit_at（含越界 → b0） ---- -/
example : bit_at (0xA5#8) 0 = true := by decide   -- 0xA5 = 1010_0101
example : bit_at (0xA5#8) 1 = false := by decide
example : bit_at (0xA5#8) 7 = true := by decide   -- MSB
example : bit_at (0xA5#8) 8 = false := by decide  -- 越界
example : bit_at (0xA5#8) 100 = false := by decide -- 远越界
example : (0x00#8)[[3]] = false := by decide
example : (0xFF#8)[[3]] = true := by decide

/- ---- get_bits（含整宽、单比特、非法区间） ---- -/
example : (0xAB#8)[[3,0]] = 0xB#4 := by decide
example : (0xAB#8)[[7,4]] = 0xA#4 := by decide
example : (0xAB#8)[[7,0]] = 0xAB#8 := by decide   -- 整宽
example : (0xAB#8)[[0,0]] = 1#1 := by decide      -- 单比特
example : (0xAB#8)[[9,8]] = 0#2 := by decide      -- hi ≥ n → 全 0
example : (0xDEADBEEF#32)[[31,16]] = 0xDEAD#16 := by decide
example : (0xDEADBEEF#32)[[15,0]] = 0xBEEF#16 := by decide

/- ---- Fill ---- -/
example : Fill 8 true = 0xFF#8 := by decide
example : Fill 8 false = 0x00#8 := by decide
example : Fill 4 true = 0xF#4 := by decide
example : Fill 32 false = 0#32 := by decide

/- ---- ZeroExt / SignExt ---- -/
example : ZeroExt 4 (0xAB#8) = 0x0AB#12 := by decide
example : ZeroExt 8 (0xFF#8) = 0x00FF#16 := by decide
example : ZeroExt 0 (0xAB#8) = 0xAB#8 := by decide -- 扩展 0 位
example : SignExt 4 (0xFB#8) = 0xFFB#12 := by decide -- 负数（符号位 1）
example : SignExt 4 (0x0B#8) = 0x00B#12 := by decide -- 正数
example : SignExt 8 (0x80#8) = 0xFF80#16 := by decide -- 最小负数

/- ---- Cat（@ 记号，含跨边界位检查、混合宽度） ---- -/
example : (0xA#4) @ (0x5#4) = 0xA5#8 := by decide
example : (0x80#8) @ (0x01#8) = 0x8001#16 := by decide
example : ((0x80#8) @ (0x01#8))[[15]] = true := by decide  -- 跨边界：hi 的 MSB
example : ((0x80#8) @ (0x01#8))[[8]] = false := by decide  -- 跨边界：hi 的 LSB
example : ((0x80#8) @ (0x01#8))[[0]] = true := by decide   -- lo 的 LSB
example : (0x1#1) @ (0x00#8) = 0x100#9 := by decide        -- 混合宽度
example : bits2nat ((0xAB#8) @ (0xCD#8)) = 0xABCD := by decide
example : (0x0#8) @ (0x0#8) = 0#16 := by decide            -- 全 0
example : (0xFF#8) @ (0xFF#8) = 0xFFFF#16 := by decide     -- 全 1

/- ---- bits_not / and / or / xor ---- -/
example : (.~ (0x0F#8)) = 0xF0#8 := by decide
example : (.~ (0x00#8)) = 0xFF#8 := by decide
example : ((0xF0#8) .& (0x3C#8)) = 0x30#8 := by decide
example : ((0xFF#8) .& (0x00#8)) = 0x00#8 := by decide
example : ((0xF0#8) .| (0x0F#8)) = 0xFF#8 := by decide
example : ((0xA5#8) .| (0x00#8)) = 0xA5#8 := by decide
example : ((0xFF#8) .^ (0xFF#8)) = 0x00#8 := by decide
example : ((0xA5#8) .^ (0x5A#8)) = 0xFF#8 := by decide

/- ---- bits_add / sub / mul / div（含回绕与除零） ---- -/
example : ((0x01#8) .+ (0x01#8)) = 0x02#8 := by decide
example : ((0xFF#8) .+ (0x01#8)) = 0x00#8 := by decide  -- 溢出回绕
example : ((0x05#8) .- (0x03#8)) = 0x02#8 := by decide
example : ((0x00#8) .- (0x01#8)) = 0xFF#8 := by decide  -- 借位回绕
example : ((0x0F#8) .* (0x0F#8)) = 0xE1#8 := by decide
example : ((0x10#8) .* (0x10#8)) = 0x00#8 := by decide  -- 乘法溢出截断
example : ((0xFF#8) ./ (0x10#8)) = 0x0F#8 := by decide
example : ((0xAB#8) ./ (0x00#8)) = 0x00#8 := by decide  -- 除零约定为 0
example : ((0x07#8) ./ (0x02#8)) = 0x03#8 := by decide  -- 向下取整
example : ((0xFFFFFFFF#32) .+ (0x1#32)) = 0#32 := by decide -- 32 位回绕

/- ---- 比较族（eq/neq/ltu/geu/gtu/leu） ---- -/
example : ((0xA#4) .== (0xA#4)) = true := by decide
example : ((0xA#4) .== (0xB#4)) = false := by decide
example : ((0xA#4) .!= (0xB#4)) = true := by decide
example : ((0xA#4) .!= (0xA#4)) = false := by decide
example : ((0x00#8) .< (0xFF#8)) = true := by decide
example : ((0xFF#8) .< (0x00#8)) = false := by decide
example : ((0xFF#8) .> (0x00#8)) = true := by decide
example : ((0x05#8) .> (0x05#8)) = false := by decide
example : ((0x05#8) .>= (0x05#8)) = true := by decide
example : ((0x05#8) .<= (0x05#8)) = true := by decide
example : ((0xFF#8) .<= (0x00#8)) = false := by decide

/- ---- 有符号比较 bits_lts / bits_ges（8 位：0x80 = −128，0xFF = −1） ---- -/
example : bits_lts (0xFF#8) (0x01#8) = true := by decide   -- −1 < 1
example : bits_lts (0x01#8) (0xFF#8) = false := by decide  -- 1 ≥ −1（无符号 1 < 255，符号语义相反）
example : bits_lts (0x80#8) (0x7F#8) = true := by decide   -- −128 < 127
example : bits_lts (0xFE#8) (0xFF#8) = true := by decide   -- −2 < −1（同号走无符号比较）
example : bits_lts (0x05#8) (0x05#8) = false := by decide
example : bits_ges (0x01#8) (0xFF#8) = true := by decide
example : bits_ges (0x05#8) (0x05#8) = true := by decide

/- ---- 移位（含移位 0、满宽、算术右移符号保持） ---- -/
example : ((0x01#8) .<< 7) = 0x80#8 := by decide
example : ((0x01#8) .<< 0) = 0x01#8 := by decide   -- 移位 0
example : ((0x01#8) .<< 8) = 0x00#8 := by decide   -- 满宽左移清零
example : ((0xFF#8) .<< 4) = 0xF0#8 := by decide
example : ((0x80#8) .>> 7) = 0x01#8 := by decide
example : ((0x80#8) .>> 0) = 0x80#8 := by decide
example : ((0x80#8) .>> 8) = 0x00#8 := by decide   -- 满宽右移清零
example : ((0xFF#8) .>> 4) = 0x0F#8 := by decide
example : bits_sar (0xF0#8) 2 = 0xFC#8 := by decide        -- −16 ≫ 2 = −4
example : bits_sar (0x80#8) 7 = 0xFF#8 := by decide        -- −128 ≫ 7 = −1
example : bits_sar (0x40#8) 2 = 0x10#8 := by decide        -- 正数算术=逻辑
example : bits_sar (0x80000000#32) 31 = 0xFFFFFFFF#32 := by decide
example : bits_sar (0x55#8) 0 = 0x55#8 := by decide

/- ---- bits_zero / bits_ones / nat2bits / bits2nat ---- -/
example : bits_zero 8 = 0#8 := by decide
example : bits_ones 8 = 0xFF#8 := by decide
example : bits_ones 32 = 0xFFFFFFFF#32 := by decide
example : nat2bits 8 300 = 0x2C#8 := by decide   -- 超宽截断（300 mod 256 = 44）
example : bits2nat (0xFF#8) = 255 := by decide
example : bits2nat (nat2bits 16 1000) = 1000 := by decide -- 往返

/- ---- Mux / IF-THEN-ELSE ---- -/
example : Mux true (0xA#4) (0xB#4) = 0xA#4 := by decide
example : Mux false (0xA#4) (0xB#4) = 0xB#4 := by decide
example : (IF true THEN (1#8) ELSE (2#8)) = 1#8 := by decide
example : (IF false THEN (1#8) ELSE (2#8)) = 2#8 := by decide

/- ---- word_to_addr / reg_idx ---- -/
example : word_to_addr (0x10#32) (show 0 < 64 by decide) = some ⟨4, by decide⟩ := by decide
example : word_to_addr (0x03#32) (show 0 < 64 by decide) = some ⟨0, by decide⟩ := by decide
example : word_to_addr (0xFFFFFFFF#32) (show 0 < 64 by decide) = none := by decide
example : reg_idx (0x1F#5) = (31 : Fin 32) := by decide
example : reg_idx (0x00#5) = (0 : Fin 32) := by decide

/- ---- RegFile / Memory 写读 ---- -/
example : rf_read (rf_write (rf_zero 4 8) (1 : Fin 4) 0xAB#8) (1 : Fin 4) = 0xAB#8 := by decide
example : rf_read (rf_write (rf_zero 4 8) (1 : Fin 4) 0xAB#8) (2 : Fin 4) = 0x00#8 := by decide
example : mem_read (mem_write (mem_zero 4 8) ⟨3, by decide⟩ 0x5A#8) ⟨3, by decide⟩
    = 0x5A#8 := by decide

end Regression

/- ========================================================================= -/
/- 3. 定理的数值实例回归（移植时新增）                                        -/
/- 第 1 节的四条定理均含自由变量，无法整体 `by decide`；按项目纪律给出具体    -/
/- 数值实例，把定理陈述的语义钉死在可执行测试上。                             -/
/- ========================================================================= -/

section SpecRegression

/- ---- cat_toNat 数值实例（含混合宽度） ---- -/
example : bits2nat (Cat (0xAB : Bits 8) (0xCD : Bits 8))
    = bits2nat (0xAB : Bits 8) * 2 ^ 8 + bits2nat (0xCD : Bits 8) := by decide
example : bits2nat ((0x1 : Bits 1) @ (0x00 : Bits 8))
    = bits2nat (0x1 : Bits 1) * 2 ^ 8 + bits2nat (0x00 : Bits 8) := by decide
example : bits2nat ((0x0 : Bits 4) @ (0xF : Bits 4))
    = bits2nat (0x0 : Bits 4) * 2 ^ 4 + bits2nat (0xF : Bits 4) := by decide

/- ---- cat_bit_at_lo 数值实例（含低位边界 i = 0 与 i = n − 1） ---- -/
example : ((0xA5 : Bits 8) @ (0x3C : Bits 8))[[0]] = (0x3C : Bits 8)[[0]] := by decide
example : ((0xA5 : Bits 8) @ (0x3C : Bits 8))[[7]] = (0x3C : Bits 8)[[7]] := by decide
example : ((0xA5 : Bits 8) @ (0x3C : Bits 8))[[3]] = (0x3C : Bits 8)[[3]] := by decide

/- ---- cat_bit_at_hi 数值实例（含拼接边界 i = n 与最高位 i = n + m − 1） ---- -/
example : ((0xA5 : Bits 8) @ (0x3C : Bits 8))[[8]] = (0xA5 : Bits 8)[[8 - 8]] := by decide
example : ((0xA5 : Bits 8) @ (0x3C : Bits 8))[[15]] = (0xA5 : Bits 8)[[15 - 8]] := by decide
example : ((0xA5 : Bits 8) @ (0x3C : Bits 8))[[11]] = (0xA5 : Bits 8)[[11 - 8]] := by decide

/- ---- cat_eq_append_cast 数值实例 ---- -/
example : Cat (0xA : Bits 4) (0x5 : Bits 4)
    = ((0xA : Bits 4) ++ (0x5 : Bits 4)).cast (Nat.add_comm 4 4) := by decide
example : Cat (0x80 : Bits 8) (0x01 : Bits 8)
    = ((0x80 : Bits 8) ++ (0x01 : Bits 8)).cast (Nat.add_comm 8 8) := by decide

/- ---- 拼合还原 / ZeroExt / SignExt 桥接的数值实例 ---- -/
example : Cat (0xDEAD : Bits 16)[[15,8]] (0xDEAD : Bits 16)[[7,0]]
    = (0xDEAD : Bits 16) := by decide
example : ZeroExt 8 (0xA5 : Bits 8) = Cat (0x00 : Bits 8) (0xA5 : Bits 8) := by decide
example : SignExt 8 (0x80 : Bits 8)
    = Cat (Fill 8 (0x80 : Bits 8)[[7]]) (0x80 : Bits 8) := by decide
example : SignExt 8 (0x7F : Bits 8)
    = Cat (Fill 8 (0x7F : Bits 8)[[7]]) (0x7F : Bits 8) := by decide

end SpecRegression

end Ventus.Base
