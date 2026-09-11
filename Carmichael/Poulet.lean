/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Carmichael.Smallest
import Mathlib.NumberTheory.FermatPsp

/-!
# 341 is the Smallest Poulet Number (Base 2 Fermat Pseudoprime)

This module formally establishes that 341 is the strictly smallest Poulet number
(Fermat pseudoprime to base 2) in Lean 4 with Mathlib4.

## Mathematical Overview

A Poulet number (or Sarrus number, or Fermat pseudoprime to base 2) is an odd composite
number `n ≥ 2` that satisfies the Fermat congruence to base 2:
  `2^(n - 1) ≡ 1 [MOD n]`

341 is composite because `341 = 11 * 31`. Since `2^10 = 1024 ≡ 1 [MOD 341]`, we have
`2^340 = (2^10)^34 ≡ 1^34 = 1 [MOD 341]`, making 341 the first Fermat pseudoprime to base 2.

## Main Results

- `Nat.IsPoulet`: Definition of base-2 Fermat pseudoprime.
- `Nat.isPoulet_iff_fermatPsp`: Logical equivalence with Mathlib's `Nat.FermatPsp n 2`.
- `Nat.isPoulet_of_isCarmichael`: Every Carmichael number is a Poulet number.
- `Nat.isPoulet_341`: 341 is a Poulet number.
- `Nat.fermatPsp_two_341`: 341 is a Fermat pseudoprime to base 2 (`Nat.FermatPsp 341 2`).
- `Nat.not_isPoulet_of_lt_341`: No natural number strictly less than 341 is a Poulet number.
- `Nat.not_fermatPsp_two_of_lt_341`: No `n < 341` is a Fermat pseudoprime to base 2.
- `Nat.isPoulet_min`: Minimality of 341 (`∀ n, IsPoulet n → 341 ≤ n`).
-/

set_option exponentiation.threshold 1000
set_option maxRecDepth 200000

namespace Nat

/-- A Poulet number (or Fermat pseudoprime to base 2) is a composite natural number `n ≥ 2`
such that `2^(n - 1) ≡ 1 [MOD n]`. -/
def IsPoulet (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 2 ≤ n ∧ 2^(n - 1) ≡ 1 [MOD n]

/-- `IsPoulet n` is logically equivalent to Mathlib's native `Nat.FermatPsp n 2`. -/
theorem isPoulet_iff_fermatPsp {n : ℕ} : IsPoulet n ↔ Nat.FermatPsp n 2 := by
  constructor
  · rintro ⟨hp, h2, hmod⟩
    refine ⟨?_, hp, by omega⟩
    exact (probablePrime_iff_modEq n (by decide)).mpr hmod
  · rintro ⟨hpp, hp, h1⟩
    have hmod := (probablePrime_iff_modEq n (by decide)).mp hpp
    exact ⟨hp, by omega, hmod⟩

/-- Any odd natural number is coprime to 2. -/
theorem coprime_two_of_odd {n : ℕ} (h : Odd n) : Nat.Coprime 2 n := by
  apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
  intro hdvd
  have hmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [Nat.odd_iff] at h
  omega

/-- Any Carmichael number is a Poulet number (base 2 Fermat pseudoprime). -/
theorem isPoulet_of_isCarmichael {n : ℕ} (h : IsCarmichael n) : IsPoulet n := by
  have h2lt := h.1
  have hcomp := h.2.1
  have hodd := h.odd
  have hcop : Nat.Coprime 2 n := coprime_two_of_odd hodd
  have hpp : ProbablePrime n 2 := h.2.2 2 hcop
  have hmod := (probablePrime_iff_modEq n (by decide)).mp hpp
  exact ⟨hcomp, by omega, hmod⟩

/-- Fast computable boolean decider checking whether `n` is certified NOT a Poulet number.
For numbers below 341, every candidate is either `< 2`, prime (verified via `isPrimeDec`),
or fails Fermat's congruence `2^(n-1) ≡ 1 [MOD n]`. -/
def isNotPouletDec (n : ℕ) : Bool :=
  if n < 2 then true
  else if isPrimeDec n then true
  else decide (2 ^ (n - 1) % n ≠ 1)

/-- Full verification decider that checks all natural numbers strictly below `N`
are not Poulet numbers. -/
def checkPouletBound (N : ℕ) : Bool :=
  (List.range N).all isNotPouletDec

/-- Soundness of `isNotPouletDec`: if `isNotPouletDec n = true` for `n < 341`,
then `n` is not a Poulet number. -/
theorem not_isPoulet_of_dec {n : ℕ} (hn341 : n < 341) (hdec : isNotPouletDec n = true) :
    ¬ IsPoulet n := by
  intro ⟨hcomp, h2le, hmod⟩
  unfold isNotPouletDec at hdec
  split_ifs at hdec with hlt hp
  · omega
  · have hn561 : n < 561 := by omega
    have hprime : n.Prime := (isPrimeDec_iff hn561).mp hp
    exact hcomp hprime
  · simp only [decide_eq_true_iff] at hdec
    have hmodeq : 2 ^ (n - 1) % n = 1 % n := hmod
    have h1mod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1mod] at hmodeq
    exact hdec hmodeq

/-- Soundness of `checkPouletBound`: if `checkPouletBound N = true` for `N ≤ 341`,
then no natural number strictly below `N` is a Poulet number. -/
theorem checkPouletBound_sound {N : ℕ} (hN : N ≤ 341) (h : checkPouletBound N = true) :
    ∀ n < N, ¬ IsPoulet n := by
  intro n hn
  unfold checkPouletBound at h
  rw [List.all_eq_true] at h
  have hn341 : n < 341 := by omega
  have hmem : n ∈ List.range N := List.mem_range.mpr hn
  exact not_isPoulet_of_dec hn341 (h n hmem)

/-- 341 is a Poulet number (base 2 Fermat pseudoprime). -/
theorem isPoulet_341 : IsPoulet 341 := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- 341 is a Fermat pseudoprime to base 2 in Mathlib's native formulation. -/
theorem fermatPsp_two_341 : Nat.FermatPsp 341 2 :=
  isPoulet_iff_fermatPsp.mp isPoulet_341

/-- There are no Poulet numbers strictly less than 341. -/
theorem not_isPoulet_of_lt_341 {n : ℕ} (hn : n < 341) : ¬ IsPoulet n := by
  have h_dec : checkPouletBound 341 = true := by decide
  exact checkPouletBound_sound (by omega) h_dec n hn

/-- There are no Fermat pseudoprimes to base 2 strictly less than 341. -/
theorem not_fermatPsp_two_of_lt_341 {n : ℕ} (hn : n < 341) : ¬ Nat.FermatPsp n 2 := by
  intro h
  exact not_isPoulet_of_lt_341 hn (isPoulet_iff_fermatPsp.mpr h)

/-- 341 is the minimal Poulet number: any Poulet number is at least 341. -/
theorem isPoulet_min : ∀ n, IsPoulet n → 341 ≤ n := by
  intro n hn
  by_contra! hlt
  exact not_isPoulet_of_lt_341 hlt hn

end Nat

export Nat (IsPoulet isPoulet_iff_fermatPsp isPoulet_of_isCarmichael
  coprime_two_of_odd isNotPouletDec checkPouletBound
  not_isPoulet_of_dec checkPouletBound_sound isPoulet_341
  fermatPsp_two_341 not_isPoulet_of_lt_341 not_fermatPsp_two_of_lt_341
  isPoulet_min)
