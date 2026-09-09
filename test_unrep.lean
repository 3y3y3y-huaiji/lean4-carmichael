import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace Int

def Representable (a b n : ℤ) : Prop :=
  ∃ x y : ℤ, x ≥ 0 ∧ y ≥ 0 ∧ a * x + b * y = n

variable {a b : ℤ}

lemma sylvester_algebraic_rearrange {x y : ℤ} (h : a * x + b * y = a * b - a - b) :
    a * (b - 1 - x) = b * (y + 1) := by
  linear_combination -h

lemma dvd_y_add_one_of_coprime (h_coprime : IsCoprime a b) {x y : ℤ}
    (h_eq : a * (b - 1 - x) = b * (y + 1)) :
    a ∣ (y + 1) := by
  have hdvd : a ∣ b * (y + 1) := ⟨b - 1 - x, h_eq.symm⟩
  exact h_coprime.dvd_of_dvd_mul_left hdvd

theorem sylvester_unrepresentable
    (ha : a ≥ 2) (hb : b ≥ 2) (h_coprime : IsCoprime a b) :
    ¬ Representable a b (a * b - a - b) := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have h_eq := sylvester_algebraic_rearrange hxy
  have hdvd := dvd_y_add_one_of_coprime h_coprime h_eq
  rcases hdvd with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    have : 0 < y + 1 := by omega
    nlinarith
  have h_sub : a * (b - 1 - x) = a * (b * k) := by
    calc
      a * (b - 1 - x) = b * (y + 1) := h_eq
      _ = b * (a * k) := by rw [hk]
      _ = a * (b * k) := by ring
  have ha_pos : a ≠ 0 := by omega
  have h_cancel := mul_left_cancel₀ ha_pos h_sub
  nlinarith

end Int
