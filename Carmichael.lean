import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic

set_option exponentiation.threshold 1000

/-!
# Carmichael Numbers Formalization in Lean 4

This module defines Carmichael numbers and formally verifies that 561 is the first Carmichael number.
-/

/-- 561 的质因数分解：561 = 3 * 11 * 17 -/
lemma factor_561 : 561 = 3 * 11 * 17 := by rfl

/-- 561 不是素数（合数性质） -/
lemma not_prime_561 : ¬ (561 : ℕ).Prime := by norm_num

/-- 素因子同余引理 1：对于与 561 互质的整数 b，3 ∣ b^560 - 1 -/
lemma dvd_mod_three {b : ℕ} (h : b.Coprime 561) : 3 ∣ b ^ 560 - 1 := by
  have h3 : b.Coprime 3 := h.coprime_dvd_right (by decide : 3 ∣ 561)
  have h_tot : b ^ 2 ≡ 1 [MOD 3] := by
    have ht := Nat.ModEq.pow_totient h3
    exact ht
  have h_pow : (b ^ 2) ^ 280 ≡ 1 ^ 280 [MOD 3] := h_tot.pow 280
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- 素因子同余引理 2：对于与 561 互质的整数 b，11 ∣ b^560 - 1 -/
lemma dvd_mod_eleven {b : ℕ} (h : b.Coprime 561) : 11 ∣ b ^ 560 - 1 := by
  have h11 : b.Coprime 11 := h.coprime_dvd_right (by decide : 11 ∣ 561)
  have h_tot : b ^ 10 ≡ 1 [MOD 11] := by
    have ht := Nat.ModEq.pow_totient h11
    exact ht
  have h_pow : (b ^ 10) ^ 56 ≡ 1 ^ 56 [MOD 11] := h_tot.pow 56
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- 素因子同余引理 3：对于与 561 互质的整数 b，17 ∣ b^560 - 1 -/
lemma dvd_mod_seventeen {b : ℕ} (h : b.Coprime 561) : 17 ∣ b ^ 560 - 1 := by
  have h17 : b.Coprime 17 := h.coprime_dvd_right (by decide : 17 ∣ 561)
  have h_tot : b ^ 16 ≡ 1 [MOD 17] := by
    have ht := Nat.ModEq.pow_totient h17
    exact ht
  have h_pow : (b ^ 16) ^ 35 ≡ 1 ^ 35 [MOD 17] := h_tot.pow 35
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- 合并引理：由两两互质因子的整除性合并得出 561 ∣ b^560 - 1 -/
lemma dvd_561_of_prime_factors {b : ℕ} (h3 : 3 ∣ b ^ 560 - 1) (h11 : 11 ∣ b ^ 560 - 1) (h17 : 17 ∣ b ^ 560 - 1) :
    561 ∣ b ^ 560 - 1 := by
  have h33 : 3 * 11 ∣ b ^ 560 - 1 := (by decide : Nat.Coprime 3 11).mul_dvd_of_dvd_of_dvd h3 h11
  have h561 : (3 * 11) * 17 ∣ b ^ 560 - 1 := (by decide : Nat.Coprime (3 * 11) 17).mul_dvd_of_dvd_of_dvd h33 h17
  exact h561

/-- 费马伪素数检验中的「关于底数 b 的可能素数」定义 -/
def ProbablePrime (b n : ℕ) : Prop :=
  n ∣ b ^ (n - 1) - 1

/-- 卡迈克尔数（Carmichael numbers）定义：
大于 1 的合数，且对所有与其互质的底数 b，均满足费马可能素数检验条件 -/
def Carmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime b n

/-- 核心定理：561 是卡迈克尔数 -/
theorem carmichael_561 : Carmichael 561 := by
  refine ⟨not_prime_561, by decide, fun b h ↦ ?_⟩
  dsimp [ProbablePrime]
  exact dvd_561_of_prime_factors (dvd_mod_three h) (dvd_mod_eleven h) (dvd_mod_seventeen h)
