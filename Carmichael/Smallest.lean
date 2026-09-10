/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Carmichael
import Carmichael.Korselt
import Mathlib.Tactic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factors

/-!
# 561 is the Smallest Carmichael Number

This module formally proves that 561 is the strictly smallest Carmichael number,
directly resolving the open TODO in Mathlib's Carmichael module:
Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561.

## Mathematical Strategy

Any Carmichael number `n` is odd (`IsCarmichael.odd`), squarefree, and has at least 3 distinct
prime factors. Using Korselt's criterion, every odd candidate `n < 561` is eliminated:
- `n ≤ 2` contradicts `2 < n`.
- Primes are eliminated because Carmichael numbers are composite.
- Numbers divisible by a square `p * p ∣ n` violate squarefreeness.
- Products of two distinct primes `p * q` cannot satisfy Korselt's condition.
- The remaining composite candidates with ≥ 3 prime factors fail Korselt's condition
  `p - 1 ∣ n - 1` for at least one prime factor `p ∣ n`.

## Main Theorems

- `Nat.not_isCarmichael_of_lt_561`: No natural number `n < 561` is a Carmichael number.
- `Nat.isCarmichael_min`: If `n` is a Carmichael number, then `561 ≤ n`.
- `Nat.not_carmichael_of_lt_561`: Corollary for `Nat.Carmichael`.
- `Nat.carmichael_min`: Corollary for `Nat.Carmichael`.
-/

namespace Nat

/-- A Carmichael number is a composite natural number `n > 2` that passes the Fermat primality test
for all bases `b` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  2 < n ∧ ¬ n.Prime ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime n b

/-- IsCarmichael n is equivalent to Nat.Carmichael n. -/
theorem isCarmichael_iff_carmichael {n : ℕ} : n.IsCarmichael ↔ Nat.Carmichael n := by
  constructor
  · rintro ⟨hn, hp, hpp⟩
    exact ⟨hp, by omega, hpp⟩
  · rintro ⟨hp, hn, hpp⟩
    refine ⟨?_, hp, hpp⟩
    by_contra! hle
    have : n = 2 := by omega
    subst this
    exact hp Nat.prime_two

/-- Korselt's criterion for IsCarmichael: 
 is Carmichael iff 2 < n, composite,
squarefree, and p - 1 ∣ n - 1 for all prime divisors p ∣ n. -/
theorem isCarmichael_iff_korselt {n : ℕ} :
    n.IsCarmichael ↔ 2 < n ∧ ¬ n.Prime ∧ Squarefree n ∧
      ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) := by
  constructor
  · rintro ⟨h2, hp, hpp⟩
    have h1 : 1 < n := by omega
    have hc : Nat.Carmichael n := ⟨hp, h1, hpp⟩
    have hk := (carmichael_iff_korselt n h1 hp).mp hc
    exact ⟨h2, hp, hk.1, hk.2⟩
  · rintro ⟨h2, hp, hsq, hk⟩
    have h1 : 1 < n := by omega
    have hc := (carmichael_iff_korselt n h1 hp).mpr ⟨hsq, hk⟩
    exact isCarmichael_iff_carmichael.mpr hc

/-- Any Carmichael number is odd. -/
theorem IsCarmichael.odd {n : ℕ} (h : n.IsCarmichael) : Odd n := by
  have hk := isCarmichael_iff_korselt.mp h
  rcases hk with ⟨h2, hcomp, hsq, hkdiv⟩
  rw [Nat.odd_iff]
  by_contra! heven
  have h2dvd : 2 ∣ n := by omega
  rcases h2dvd with ⟨m, rfl⟩
  have hm1 : 1 < m := by omega
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hpm : m.minFac ∣ m := Nat.minFac_dvd m
  have hpn : m.minFac ∣ 2 * m := dvd_mul_of_dvd_right hpm 2
  have hp2 : m.minFac ≠ 2 := by
    intro h_two
    rcases hpm with ⟨k, hk⟩
    have h4 : 2 * 2 ∣ 2 * m := by
      use k
      rw [hk, h_two]
      ring
    have hunit : IsUnit (2 : ℕ) := hsq 2 h4
    have : (2 : ℕ) = 1 := isUnit_iff_eq_one.mp hunit
    revert this
    decide
  have hmod1 : m.minFac % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h2divp : 2 ∣ m.minFac - 1 := by omega
  have hdiv_n1 : m.minFac - 1 ∣ 2 * m - 1 := hkdiv m.minFac hp hpn
  have h2div_n1 : 2 ∣ 2 * m - 1 := h2divp.trans hdiv_n1
  have h2div1 : 2 ∣ 1 := by
    have h_add : (2 * m - 1) + 1 = 2 * m := by omega
    have h2_dvd_2m : 2 ∣ (2 * m - 1) + 1 := by
      rw [h_add]
      exact dvd_mul_right 2 m
    exact (Nat.dvd_add_right h2div_n1).mp h2_dvd_2m
  revert h2div1
  decide

/-- A product of two distinct primes cannot be a Carmichael number. -/
theorem not_isCarmichael_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ¬ (p * q).IsCarmichael := by
  intro h
  have hk := isCarmichael_iff_korselt.mp h
  have hq_dvd : q ∣ p * q := ⟨p, mul_comm p q⟩
  have hdiv : q - 1 ∣ p * q - 1 := hk.2.2.2 q hq hq_dvd
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hid : p * q - 1 = p * (q - 1) + (p - 1) := by
    have h1 : 1 ≤ p * q := by nlinarith
    have h2 : 1 ≤ q := by omega
    have h3 : 1 ≤ p := by omega
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    push_cast
    ring
  have h_sum : q - 1 ∣ p * (q - 1) + (p - 1) := hid ▸ hdiv
  have h_left : q - 1 ∣ p * (q - 1) := dvd_mul_left (q - 1) p
  have hdiv_sub : q - 1 ∣ p - 1 := (Nat.dvd_add_right h_left).mp h_sum
  have hpos : 0 < p - 1 := by omega
  have hle : q - 1 ≤ p - 1 := Nat.le_of_dvd hpos hdiv_sub
  omega

/-- If p * p ∣ n with p non-unit, then 
 is not Carmichael (fails squarefreeness). -/
theorem not_isCarmichael_of_sq_dvd {n p : ℕ} (hpn : p * p ∣ n) (hp : ¬ IsUnit p) :
    ¬ n.IsCarmichael := by
  intro h
  have hk := isCarmichael_iff_korselt.mp h
  exact hp (hk.2.2.1 p hpn)

/-- If a prime factor p ∣ n does not satisfy p - 1 ∣ n - 1, then 
 is not Carmichael. -/
theorem not_isCarmichael_of_prime_factor_not_dvd {n p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hndiv : ¬ (p - 1 ∣ n - 1)) :
    ¬ n.IsCarmichael := by
  intro h
  have hk := isCarmichael_iff_korselt.mp h
  exact hndiv (hk.2.2.2 p hp hpn)

/-- There are no Carmichael numbers strictly less than 561. -/
theorem not_isCarmichael_of_lt_561 {n : ℕ} (hn : n < 561) : ¬ n.IsCarmichael := by
  intro h
  have ho := h.odd
  rcases ho with ⟨k, rfl⟩
  have hk : k < 280 := by omega
  interval_cases k
  · have := h.1
    omega

  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 7 + 1 = 3 * 5 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 10 + 1 = 3 * 7 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 16 + 1 = 3 * 11 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 17 + 1 = 5 * 7 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 19 + 1 = 3 * 13 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 7) (by decide) (by decide) h
  · have ht : 2 * 25 + 1 = 3 * 17 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 27 + 1 = 5 * 11 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 28 + 1 = 3 * 19 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 32 + 1 = 5 * 13 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 34 + 1 = 3 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · have ht : 2 * 38 + 1 = 7 * 11 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 42 + 1 = 5 * 17 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 43 + 1 = 3 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 45 + 1 = 7 * 13 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 46 + 1 = 3 * 31 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 47 + 1 = 5 * 19 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 7)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 55 + 1 = 3 * 37 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 57 + 1 = 5 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 59 + 1 = 7 * 17 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 11) (by decide) (by decide) h
  · have ht : 2 * 61 + 1 = 3 * 41 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 64 + 1 = 3 * 43 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 66 + 1 = 7 * 19 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 70 + 1 = 3 * 47 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 71 + 1 = 11 * 13 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 72 + 1 = 5 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 7) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 77 + 1 = 5 * 31 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 79 + 1 = 3 * 53 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 80 + 1 = 7 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 11)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 13) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · have ht : 2 * 88 + 1 = 3 * 59 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 91 + 1 = 3 * 61 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 92 + 1 = 5 * 37 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 93 + 1 = 11 * 17 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 5)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 100 + 1 = 3 * 67 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 101 + 1 = 7 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 102 + 1 = 5 * 41 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 104 + 1 = 11 * 19 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 106 + 1 = 3 * 71 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 107 + 1 = 5 * 43 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 108 + 1 = 7 * 31 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 109 + 1 = 3 * 73 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 110 + 1 = 13 * 17 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 7)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 117 + 1 = 5 * 47 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 118 + 1 = 3 * 79 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 7) (by decide) (by decide) h
  · have ht : 2 * 123 + 1 = 13 * 19 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 124 + 1 = 3 * 83 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 126 + 1 = 11 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 5)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 129 + 1 = 7 * 37 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 132 + 1 = 5 * 53 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 133 + 1 = 3 * 89 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 7)
      (by norm_num) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 19)
      (by norm_num) (by decide) (by decide) h
  · have ht : 2 * 143 + 1 = 7 * 41 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 17) (by decide) (by decide) h
  · have ht : 2 * 145 + 1 = 3 * 97 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 147 + 1 = 5 * 59 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 149 + 1 = 13 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 150 + 1 = 7 * 43 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 151 + 1 = 3 * 101 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 152 + 1 = 5 * 61 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 154 + 1 = 3 * 103 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 159 + 1 = 11 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 160 + 1 = 3 * 107 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 161 + 1 = 17 * 19 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · have ht : 2 * 163 + 1 = 3 * 109 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 164 + 1 = 7 * 47 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 167 + 1 = 5 * 67 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 169 + 1 = 3 * 113 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 170 + 1 = 11 * 31 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 7) (by decide) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 23)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 177 + 1 = 5 * 71 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 7)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 19) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 11) (by decide) (by decide) h
  · have ht : 2 * 182 + 1 = 5 * 73 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 185 + 1 = 7 * 53 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · have ht : 2 * 188 + 1 = 13 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 190 + 1 = 3 * 127 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 11)
      (by norm_num) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 195 + 1 = 17 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 196 + 1 = 3 * 131 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 197 + 1 = 5 * 79 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 7)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 201 + 1 = 13 * 31 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 203 + 1 = 11 * 37 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 205 + 1 = 3 * 137 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 206 + 1 = 7 * 59 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 207 + 1 = 5 * 83 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 208 + 1 = 3 * 139 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · have ht : 2 * 213 + 1 = 7 * 61 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 11)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 5)
      (by norm_num) (by decide) (by decide) h
  · have ht : 2 * 218 + 1 = 19 * 23 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 222 + 1 = 5 * 89 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 223 + 1 = 3 * 149 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 225 + 1 = 11 * 41 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 226 + 1 = 3 * 151 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 5)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 31)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 234 + 1 = 7 * 67 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 235 + 1 = 3 * 157 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 236 + 1 = 11 * 43 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 240 + 1 = 13 * 37 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 7)
      (by norm_num) (by decide) (by decide) h
  · have ht : 2 * 242 + 1 = 5 * 97 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 244 + 1 = 3 * 163 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 246 + 1 = 17 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 248 + 1 = 7 * 71 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 250 + 1 = 3 * 167 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 252 + 1 = 5 * 101 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 13) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 255 + 1 = 7 * 73 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 257 + 1 = 5 * 103 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 258 + 1 = 11 * 47 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 259 + 1 = 3 * 173 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 5) (by decide) (by decide) h
  · have ht : 2 * 263 + 1 = 17 * 31 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 23) (by decide) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 266 + 1 = 13 * 41 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 267 + 1 = 5 * 107 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 268 + 1 = 3 * 179 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_sq_dvd (p := 7) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 271 + 1 = 3 * 181 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 272 + 1 = 5 * 109 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact h.2.1 (by norm_num)
  · exact not_isCarmichael_of_sq_dvd (p := 3) (by decide) (by decide) h
  · have ht : 2 * 275 + 1 = 19 * 29 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · have ht : 2 * 276 + 1 = 7 * 79 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
  · exact not_isCarmichael_of_prime_factor_not_dvd (p := 5)
      (by norm_num) (by decide) (by decide) h
  · exact h.2.1 (by norm_num)
  · have ht : 2 * 279 + 1 = 13 * 43 := rfl
    rw [ht] at h
    exact not_isCarmichael_mul_primes (by norm_num) (by norm_num) (by decide) h
/-- 561 is the minimal Carmichael number. -/
theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n := by
  by_contra! h
  exact not_isCarmichael_of_lt_561 h hn

/-- There are no Carmichael numbers strictly less than 561 (formulation for Nat.Carmichael). -/
theorem not_carmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ Nat.Carmichael n := by
  intro hc
  exact not_isCarmichael_of_lt_561 h (isCarmichael_iff_carmichael.mpr hc)

/-- 561 is the minimal Carmichael number (formulation for Nat.Carmichael). -/
theorem carmichael_min {n : ℕ} (hn : Nat.Carmichael n) : 561 ≤ n :=
  isCarmichael_min (isCarmichael_iff_carmichael.mpr hn)

end Nat

export Nat (IsCarmichael isCarmichael_iff_carmichael isCarmichael_iff_korselt
  not_isCarmichael_mul_primes not_isCarmichael_of_sq_dvd
  not_isCarmichael_of_prime_factor_not_dvd not_isCarmichael_of_lt_561
  isCarmichael_min not_carmichael_of_lt_561 carmichael_min)

