/-
Copyright (c) 2026 Carmichael Formalization Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmichael Formalization Contributors
-/
import Mathlib.NumberTheory.FermatPsp
import Mathlib.Tactic.NormNum.Prime

set_option exponentiation.threshold 1000

/-!
# Carmichael Numbers

This module formalizes Carmichael numbers (absolute Fermat pseudoprimes) and integrates
directly with `Mathlib.NumberTheory.FermatPsp`.

A Carmichael number is a composite natural number `n > 1` that passes the Fermat primality test
for all bases `b` coprime to `n`, i.e., `ProbablePrime n b` holds for all `b` with `b.Coprime n`.

## Main Definitions and Theorems

- `Nat.Carmichael`: Definition of Carmichael numbers.
- `Nat.Carmichael.not_prime`: A Carmichael number is not prime.
- `Nat.Carmichael.one_lt`: A Carmichael number is strictly greater than 1.
- `Nat.Carmichael.probablePrime`: A Carmichael number is a probable prime to any coprime base.
- `carmichael_561`: Proof that 561 is a Carmichael number (positive witness).
- `not_carmichael_nine`: Proof that 9 is not a Carmichael number (negative sanity check).

## References

- A. Korselt, *Problème chinois*, L'Intermédiaire des Mathématiciens 6 (1899), 142–143.
- `Mathlib.NumberTheory.FermatPsp`.
-/

/-- Prime factorization of 561: `561 = 3 * 11 * 17`. -/
lemma factor_561 : 561 = 3 * 11 * 17 := by rfl

/-- 561 is composite (not prime). -/
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

/-- A natural number `n` is a Carmichael number if it is composite, greater than 1,
and passes the Fermat primality test for all bases `b` coprime to `n`. -/
def Carmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime n b

/-- A Carmichael number is composite (not prime). -/
lemma Carmichael.not_prime {n : ℕ} (h : Carmichael n) : ¬ n.Prime :=
  h.1

/-- A Carmichael number is strictly greater than 1. -/
lemma Carmichael.one_lt {n : ℕ} (h : Carmichael n) : 1 < n :=
  h.2.1

/-- A Carmichael number is a Fermat probable prime to any coprime base. -/
lemma Carmichael.probablePrime {n : ℕ} (h : Carmichael n) {b : ℕ} (hb : b.Coprime n) :
    ProbablePrime n b :=
  h.2.2 b hb

/-- Positive witness: 561 is a Carmichael number. -/
theorem carmichael_561 : Carmichael 561 :=
  ⟨not_prime_561, by decide, fun b h ↦
    dvd_561_of_prime_factors (dvd_mod_three h) (dvd_mod_eleven h) (dvd_mod_seventeen h)⟩

/-- Negative sanity check: 9 is not a Carmichael number because it fails the Fermat primality test
for base 2 (`gcd(2, 9) = 1` but `9 ∤ 2^8 - 1`). -/
theorem not_carmichael_nine : ¬ Carmichael 9 := fun h ↦
  (by decide : ¬ (9 ∣ 2 ^ (9 - 1) - 1)) (h.probablePrime (by decide : Nat.Coprime 2 9))

end Nat

export Nat (Carmichael carmichael_561 not_carmichael_nine)

#print axioms Nat.carmichael_561
#print axioms Nat.not_carmichael_nine
#lint
