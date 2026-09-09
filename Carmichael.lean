/-
Copyright (c) 2026 Carmichael Formalization Contributors. All rights reserved.
SPDX-License-Identifier: Apache-2.0 OR MulanPSL-2.0
Released under Apache 2.0 OR MulanPSL-2.0 license as described in the file LICENSE.
Authors: Carmichael Formalization Contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic

set_option exponentiation.threshold 1000

/-!
# Carmichael Numbers and the Counterexample 561

This module provides the formal definition of Carmichael numbers (absolute Fermat pseudoprimes)
and formally verifies that 561 is the first Carmichael number.

## Motivation & Mathlib Relation

In `Mathlib.NumberTheory.FermatPsp`, Fermat pseudoprimes are formalized, and the documentation notes:
> "Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet
> defined in this file)."

This module addresses that missing definition in Mathlib4 by:
1. Defining `Nat.ProbablePrime b n` stating that `n ∣ b ^ (n - 1) - 1`.
2. Defining `Nat.Carmichael n` stating that `n` is a composite natural number `n > 1` such that
   every base `b` coprime to `n` satisfies the Fermat probable prime condition.
3. Formally proving `carmichael_561`, showing that 561 is indeed a Carmichael number.

## Main Definitions and Theorems

- `factor_561`: The prime factorization `561 = 3 * 11 * 17`.
- `not_prime_561`: Proof that 561 is not prime.
- `dvd_mod_three`: For any `b` coprime to 561, `3 ∣ b ^ 560 - 1`.
- `dvd_mod_eleven`: For any `b` coprime to 561, `11 ∣ b ^ 560 - 1`.
- `dvd_mod_seventeen`: For any `b` coprime to 561, `17 ∣ b ^ 560 - 1`.
- `dvd_561_of_prime_factors`: Combines divisibility by 3, 11, 17 into divisibility by 561.
- `Nat.ProbablePrime`: Fermat probable primality condition for base `b` and number `n`.
- `Nat.Carmichael`: Definition of Carmichael numbers.
- `carmichael_561`: Main theorem establishing that 561 is a Carmichael number.

## References

- Korselt, A. (1899). "Problème chinois". L'Intermédiaire des Mathématiciens.
- Mathlib4: `Mathlib.NumberTheory.FermatPsp`.
-/

/-- Prime factorization of 561: `561 = 3 * 11 * 17`. -/
lemma factor_561 : 561 = 3 * 11 * 17 := by rfl

/-- 561 is composite (not a prime number). -/
lemma not_prime_561 : ¬ (561 : ℕ).Prime := by norm_num

/-- Divisibility lemma for prime factor 3: for any base `b` coprime to 561, `3 ∣ b ^ 560 - 1`. -/
lemma dvd_mod_three {b : ℕ} (h : b.Coprime 561) : 3 ∣ b ^ 560 - 1 := by
  have h_pow := (Nat.ModEq.pow_totient (h.coprime_dvd_right (by decide : 3 ∣ 561))).pow 280
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- Divisibility lemma for prime factor 11: for any base `b` coprime to 561, `11 ∣ b ^ 560 - 1`. -/
lemma dvd_mod_eleven {b : ℕ} (h : b.Coprime 561) : 11 ∣ b ^ 560 - 1 := by
  have h_pow := (Nat.ModEq.pow_totient (h.coprime_dvd_right (by decide : 11 ∣ 561))).pow 56
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- Divisibility lemma for prime factor 17: for any base `b` coprime to 561, `17 ∣ b ^ 560 - 1`. -/
lemma dvd_mod_seventeen {b : ℕ} (h : b.Coprime 561) : 17 ∣ b ^ 560 - 1 := by
  have h_pow := (Nat.ModEq.pow_totient (h.coprime_dvd_right (by decide : 17 ∣ 561))).pow 35
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- Divisibility combination lemma: if 3, 11, and 17 each divide `b ^ 560 - 1`,
then their product `561` divides `b ^ 560 - 1`. -/
lemma dvd_561_of_prime_factors {b : ℕ} (h3 : 3 ∣ b ^ 560 - 1) (h11 : 11 ∣ b ^ 560 - 1) (h17 : 17 ∣ b ^ 560 - 1) :
    561 ∣ b ^ 560 - 1 :=
  (by decide : Nat.Coprime (3 * 11) 17).mul_dvd_of_dvd_of_dvd
    ((by decide : Nat.Coprime 3 11).mul_dvd_of_dvd_of_dvd h3 h11) h17

namespace Nat

/-- A natural number `n` is a probable prime to base `b` if `n ∣ b ^ (n - 1) - 1`. -/
def ProbablePrime (b n : ℕ) : Prop :=
  n ∣ b ^ (n - 1) - 1

/-- A Carmichael number is a composite natural number `n > 1` such that for every base `b`
coprime to `n`, `n` is a probable prime to base `b` (`n ∣ b ^ (n - 1) - 1`). -/
def Carmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime b n

/-- Main theorem: 561 is a Carmichael number. -/
theorem carmichael_561 : Carmichael 561 :=
  ⟨not_prime_561, by decide, fun b h ↦
    dvd_561_of_prime_factors (dvd_mod_three h) (dvd_mod_eleven h) (dvd_mod_seventeen h)⟩

end Nat

export Nat (Carmichael ProbablePrime carmichael_561)
