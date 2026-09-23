/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.Tactic.Linarith

/-!
# 561 is the Smallest Carmichael Number

This module proves that 561 is the strictly smallest Carmichael number, resolving
the open TODO in Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`.

The proof implements an extensible modular funnel reflection architecture:
`Bitwise Parity Gate → Small Prime Trial Division (≤ 23) → Base-2/3 Fermat Witness Early Exit`.
Every candidate below 561 is refuted without Peano primality recursion.
-/

namespace Nat

/-- Parity gate: immediate rejection of `n ≤ 2` or even numbers. -/
def isEvenOrSmall (n : ℕ) : Bool :=
  n ≤ 2 || n % 2 == 0

lemma not_isEvenOrSmall_of_isCarmichael {n : ℕ} (hc : n.IsCarmichael) :
    isEvenOrSmall n = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold isEvenOrSmall at h
  simp only [Bool.or_eq_true, decide_eq_true_iff, beq_iff_eq] at h
  have := hc.two_lt
  obtain ⟨k, rfl⟩ := hc.odd
  rcases h with hle | heven <;> lia

/-- Trial division gate: checks if `n` has no divisors `d` in `2 ≤ d < 24` with `d * d ≤ n`. -/
def isPrimeTrial (n : ℕ) : Bool :=
  (List.range' 2 22).all (fun d => decide (n < d * d) || n % d != 0)

lemma not_isPrimeTrial_of_isCarmichael {n : ℕ} (hn : n < 561) (hc : n.IsCarmichael) :
    isPrimeTrial n = false := by
  rw [Bool.eq_false_iff]
  intro hall
  unfold isPrimeTrial at hall
  have h_sqle := minFac_sq_le_self (by have := hc.two_lt; lia) hc.not_prime
  have h_mf_lt : minFac n < 24 := by
    by_contra! h24
    have : 24 ^ 2 ≤ minFac n ^ 2 := by nlinarith
    lia
  have hp : 2 ≤ minFac n := (minFac_prime (by have := hc.two_lt; lia)).two_le
  have hd_mem : minFac n ∈ List.range' 2 22 := by
    rw [List.mem_range']
    refine ⟨minFac n - 2, by lia, by lia⟩
  have hall_dvd := List.all_eq_true.mp hall (minFac n) hd_mem
  simp only [Bool.or_eq_true, decide_eq_true_iff, bne_iff_ne, ne_eq] at hall_dvd
  rcases hall_dvd with hgt | hdvd
  · lia
  · exact hdvd (Nat.mod_eq_zero_of_dvd (minFac_dvd n))

/-- Fermat witness early-exit gate: checks if base 2 (or base 3 for 341) refutes primality. -/
def isFermatWitness (n : ℕ) : Bool :=
  if n == 341 then !decide (ProbablePrime 341 3)
  else !decide (ProbablePrime n 2)

lemma not_isFermatWitness_of_isCarmichael {n : ℕ} (hc : n.IsCarmichael) :
    isFermatWitness n = false := by
  unfold isFermatWitness
  split_ifs with h341
  · have hn341 : n = 341 := beq_iff_eq.mp h341
    subst hn341
    simp [hc.probablePrime_of_coprime (by decide : Nat.Coprime 3 341)]
  · simp [hc.probablePrime_of_coprime (Nat.coprime_two_left.mpr hc.odd)]

/-- Modular funnel filter for candidate Carmichael numbers below 561. -/
def isCarmichaelCandidate (n : ℕ) : Bool :=
  if isEvenOrSmall n then false
  else if isPrimeTrial n then false
  else !isFermatWitness n

theorem isCarmichaelCandidate_of_isCarmichael {n : ℕ} (hn : n < 561) (hc : n.IsCarmichael) :
    isCarmichaelCandidate n = true := by
  unfold isCarmichaelCandidate
  simp [not_isEvenOrSmall_of_isCarmichael hc, not_isPrimeTrial_of_isCarmichael hn hc,
    not_isFermatWitness_of_isCarmichael hc]

set_option exponentiation.threshold 1000
set_option maxRecDepth 10000

/-- Bounded verifier checking that no natural number below N is Carmichael. -/
def checkCarmichaelBound (N : ℕ) : Bool :=
  (List.range N).all (fun n => !isCarmichaelCandidate n)

theorem checkCarmichaelBound_sound {N : ℕ} (hN : N ≤ 561) (h : checkCarmichaelBound N = true) :
    ∀ n < N, ¬ n.IsCarmichael := by
  intro n hn
  have hn_lt : n < 561 := by lia
  unfold checkCarmichaelBound at h
  have hall := List.all_eq_true.mp h n (List.mem_range.mpr hn)
  simp only [Bool.not_eq_true'] at hall
  intro hc
  have hcand := isCarmichaelCandidate_of_isCarmichael hn_lt hc
  rw [hall] at hcand
  contradiction

theorem not_isCarmichael_of_lt_561 {n : ℕ} (hn : n < 561) : ¬ n.IsCarmichael :=
  checkCarmichaelBound_sound (le_refl 561) (by decide) n hn

theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n :=
  not_lt.mp (fun h => not_isCarmichael_of_lt_561 h hn)

end Nat
