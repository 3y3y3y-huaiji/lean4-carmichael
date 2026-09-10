/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Carmichael
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.Exponent

/-!
# Korselt's Criterion for Carmichael Numbers

This module formalizes and machine-checks Korselt's Criterion (1899) for Carmichael numbers
in Lean 4, leveraging Mathlib's pre-existing Carmichael lambda function
(`Mathlib.NumberTheory.ArithmeticFunction.Carmichael`).

## Mathematical Strategy: The Tripartite Equivalence

For any composite integer `n > 1`, we establish:
`Nat.Carmichael n ↔ ArithmeticFunction.carmichael n ∣ n - 1 ↔ Korselt Condition`.

## Main Results

- `Nat.carmichael_iff_carmichael_dvd`: Step 1 bridging `Nat.Carmichael` with `carmichael n ∣ n - 1`.
- `Nat.carmichael_dvd_iff_korselt`: Step 2 bridging `carmichael n ∣ n - 1` with Korselt's condition.
- `Nat.carmichael_iff_korselt`: Step 3 (Main Theorem: Korselt's Criterion).

## References

* A. Korselt, *Problème chinois*, L'Intermédiaire des Mathématiciens 6 (1899), 142–143.
-/

open ArithmeticFunction

namespace Nat

/-- **Step 1**: A composite natural number `n > 1` is a Carmichael number if and only if
the Carmichael function `carmichael n` divides `n - 1`. -/
theorem carmichael_iff_carmichael_dvd (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ ArithmeticFunction.carmichael n ∣ n - 1 := by
  have hn0 : n ≠ 0 := by lia
  have : NeZero n := ⟨hn0⟩
  have h_exp : ArithmeticFunction.carmichael n = Monoid.exponent (ZMod n)ˣ :=
    carmichael_eq_exponent hn0
  rw [h_exp, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  constructor
  · intro hc g
    have hcop := ZMod.val_coe_unit_coprime g
    have hpp := hc.probablePrime hcop
    dsimp [ProbablePrime] at hpp
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← ZMod.natCast_zmod_val (g : ZMod n)]
    rw [← Nat.cast_pow]
    have hb_pos : 1 ≤ (g : ZMod n).val := by
      by_contra! h0
      have hz : (g : ZMod n).val = 0 := by lia
      rw [hz, Nat.Coprime, Nat.gcd_zero_left] at hcop
      subst hcop
      lia
    have hpow_ge : 1 ≤ (g : ZMod n).val ^ (n - 1) :=
      Nat.one_le_pow (n - 1) _ hb_pos
    have hmodeq : 1 ≡ (g : ZMod n).val ^ (n - 1) [MOD n] :=
      Nat.modEq_of_dvd' hpow_ge hpp
    rw [← Nat.cast_one (R := ZMod n)]
    exact ((ZMod.natCast_eq_natCast_iff 1 ((g : ZMod n).val ^ (n - 1)) n).mpr hmodeq).symm
  · intro hg
    refine ⟨hcomp, hn, fun b hb ↦ ?_⟩
    dsimp [ProbablePrime]
    let u : (ZMod n)ˣ := ZMod.unitOfCoprime b hb
    have hu := hg u
    have hu_val : ((u ^ (n - 1) : (ZMod n)ˣ) : ZMod n) = (1 : ZMod n) := by
      rw [hu, Units.val_one]
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime b hb, ← Nat.cast_pow,
      ← Nat.cast_one (R := ZMod n)] at hu_val
    have hmodeq : (b ^ (n - 1) : ℕ) ≡ 1 [MOD n] :=
      (ZMod.natCast_eq_natCast_iff (b ^ (n - 1)) 1 n).mp hu_val
    exact hmodeq.symm.dvd'

/-- The Carmichael function of a prime `p` is `p - 1`. -/
lemma carmichael_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.carmichael p = p - 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : (2 : ℕ) = 2 ^ 1 := by rfl
    rw [h2, carmichael_two_pow_of_le_two (by decide)]
    rfl
  · have hp1 : (p : ℕ) = p ^ 1 := by rw [pow_one]
    rw [hp1, carmichael_pow_of_prime_ne_two 1 hp hp2, pow_one, Nat.totient_prime hp]

/-- For any prime `p` and power `k ≥ 1`, `p - 1` divides `carmichael (p ^ k)`. -/
lemma prime_sub_one_dvd_carmichael_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    p - 1 ∣ ArithmeticFunction.carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  · subst hp2
    have : 2 - 1 = 1 := rfl
    rw [this]
    exact one_dvd _
  · rw [carmichael_pow_of_prime_ne_two k hp hp2, totient_prime_pow hp hk]
    exact ⟨p ^ (k - 1), mul_comm _ _⟩

/-- For any prime `p` and power `k ≥ 2`, `p` divides `carmichael (p ^ k)`. -/
lemma prime_dvd_carmichael_pow_of_two_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) :
    p ∣ ArithmeticFunction.carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hk2 : k = 2
    · subst hk2
      rw [carmichael_two_pow_of_le_two (by decide)]
      exact dvd_rfl
    · rw [carmichael_two_pow_of_ne_two hk2]
      exact dvd_pow_self 2 (by lia)
  · rw [carmichael_pow_of_prime_ne_two k hp hp2, totient_prime_pow hp (by lia)]
    have hdvd : p ∣ p ^ (k - 1) := dvd_pow_self p (by lia)
    exact dvd_mul_of_dvd_left hdvd (p - 1)

/-- If `p ∣ n` and `p ∣ n - 1` with `1 ≤ n`, then `p ∣ 1`. -/
lemma dvd_one_of_dvd_and_dvd_sub_one {p n : ℕ} (hpn : p ∣ n) (hpn1 : p ∣ n - 1) (hn : 1 ≤ n) :
    p ∣ 1 := by
  have h_add : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hp_add : p ∣ (n - 1) + 1 := h_add.symm ▸ hpn
  exact (Nat.dvd_add_right hpn1).mp hp_add

/-- **Step 2**: The Carmichael function divides `n - 1` if and only if `n` is square-free
and `p - 1 ∣ n - 1` for all prime divisors `p ∣ n`. -/
theorem carmichael_dvd_iff_korselt (n : ℕ) (hn : 1 < n) :
    ArithmeticFunction.carmichael n ∣ n - 1 ↔
    Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) := by
  have hn0 : n ≠ 0 := by lia
  have : NeZero n := ⟨hn0⟩
  rw [carmichael_factorization n]
  constructor
  · intro h_div
    have h_korselt : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) := by
      intro p hp hpn
      have hp_mem : p ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpn, hn0⟩
      have hdvd_lcm : carmichael (p ^ n.factorization p) ∣
          n.primeFactors.lcm fun q ↦ carmichael (q ^ n.factorization q) :=
        Finset.dvd_lcm hp_mem
      have hdvd_total : carmichael (p ^ n.factorization p) ∣ n - 1 :=
        hdvd_lcm.trans h_div
      have h1le : 1 ≤ n.factorization p :=
        (hp.dvd_iff_one_le_factorization hn0).mp hpn
      have hp_sub : p - 1 ∣ carmichael (p ^ n.factorization p) :=
        prime_sub_one_dvd_carmichael_pow hp h1le
      exact hp_sub.trans hdvd_total
    refine ⟨?_, h_korselt⟩
    rw [squarefree_iff_factorization_le_one hn0]
    intro p
    by_cases hp : p.Prime
    · by_contra! h2le
      have hpn : p ∣ n := by
        rw [hp.dvd_iff_one_le_factorization hn0]
        lia
      have hp_mem : p ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpn, hn0⟩
      have hdvd_lcm : carmichael (p ^ n.factorization p) ∣
          n.primeFactors.lcm fun q ↦ carmichael (q ^ n.factorization q) :=
        Finset.dvd_lcm hp_mem
      have hdvd_total : carmichael (p ^ n.factorization p) ∣ n - 1 :=
        hdvd_lcm.trans h_div
      have hp_dvd : p ∣ carmichael (p ^ n.factorization p) :=
        prime_dvd_carmichael_pow_of_two_le hp h2le
      have hp_dvd_n1 : p ∣ n - 1 := hp_dvd.trans hdvd_total
      have hp_dvd_one : p ∣ 1 := dvd_one_of_dvd_and_dvd_sub_one hpn hp_dvd_n1 (by lia)
      exact hp.not_dvd_one hp_dvd_one
    · rw [factorization_eq_zero_of_not_prime _ hp]
      exact zero_le_one
  · rintro ⟨h_sq, h_korselt⟩
    rw [Finset.lcm_dvd_iff]
    intro p hp_mem
    rw [Nat.mem_primeFactors] at hp_mem
    rcases hp_mem with ⟨hp, hpn, -⟩
    have h_fac : n.factorization p = 1 :=
      factorization_eq_one_of_squarefree h_sq hp hpn
    rw [h_fac, pow_one, carmichael_prime hp]
    exact h_korselt p hp hpn

/-- **Korselt's Criterion (1899)**: A composite positive integer `n > 1` is a Carmichael number
if and only if `n` is square-free and `p - 1 ∣ n - 1` for all prime divisors `p ∣ n`. -/
theorem carmichael_iff_korselt (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) :=
  (carmichael_iff_carmichael_dvd n hn hcomp).trans (carmichael_dvd_iff_korselt n hn)

end Nat

export Nat (carmichael_iff_carmichael_dvd carmichael_dvd_iff_korselt carmichael_iff_korselt)
