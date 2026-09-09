import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace Int

/-- 表示 n 能否被 a 和 b 的非负整数线性组合凑出 -/
def Representable (a b n : ℤ) : Prop :=
  ∃ x y : ℤ, x ≥ 0 ∧ y ≥ 0 ∧ a * x + b * y = n

variable {a b : ℤ}

/-- 辅助引理 1：代数恒等移项 -/
lemma sylvester_algebraic_rearrange {x y : ℤ} (h : a * x + b * y = a * b - a - b) :
    a * (b - 1 - x) = b * (y + 1) := by
  sorry

/-- 辅助引理 2：由互质性推导 a ∣ (y + 1) -/
lemma dvd_y_add_one_of_coprime (h_coprime : IsCoprime a b) {x y : ℤ}
    (h_eq : a * (b - 1 - x) = b * (y + 1)) :
    a ∣ (y + 1) := by
  sorry

/-- 定理第一部分（不可表示性）：ab - a - b 绝对凑不出来 -/
theorem sylvester_unrepresentable
    (ha : a ≥ 2) (hb : b ≥ 2) (h_coprime : IsCoprime a b) :
    ¬ Representable a b (a * b - a - b) := by
  sorry

/-- 定理第二部分（可表示性）：大于 ab - a - b 的任意整数都能凑出来 -/
theorem sylvester_representable_of_gt
    (ha : a ≥ 2) (hb : b ≥ 2) (h_coprime : IsCoprime a b)
    {n : ℤ} (hn : n > a * b - a - b) :
    Representable a b n := by
  sorry

end Int
