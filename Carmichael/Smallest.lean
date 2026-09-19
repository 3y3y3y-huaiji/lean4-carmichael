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

The proof uses computational reflection via Fermat witness refutation:
every natural number below 561 is either at most 2, even, prime (witnessed by
trial division up to `√560 < 24`), or an odd composite failing the Fermat
test for base 2 (or base 3 for 341).
-/

namespace Nat

/-- Computable decision predicate for candidate Carmichael numbers below 561. -/
def isCarmichaelCandidate (n : ℕ) : Bool :=
  if n ≤ 2 || n % 2 == 0 then false
  else if (List.range' 2 22).all (fun d => decide (n < d * d) || n % d != 0) then false
  else if n == 341 then decide (ProbablePrime 341 3)
  else decide (ProbablePrime n 2)

theorem isCarmichaelCandidate_of_isCarmichael {n : ℕ} (hn : n < 561) (hc : n.IsCarmichael) :
    isCarmichaelCandidate n = true := by
  unfold isCarmichaelCandidate
  split_ifs with h2 hall h341
  · simp only [Bool.or_eq_true, decide_eq_true_iff] at h2
    rcases h2 with hle | heven
    · have := hc.two_lt; lia
    · obtain ⟨k, rfl⟩ := hc.odd; lia
  · have h_sqle := minFac_sq_le_self (by lia) hc.not_prime
    have h_mf_lt : minFac n < 24 := by
      by_contra! h24
      have : 24 ^ 2 ≤ minFac n ^ 2 := by nlinarith
      lia
    have hp : 2 ≤ minFac n := (minFac_prime (by lia)).two_le
    have hd_mem : minFac n ∈ List.range' 2 22 := by
      rw [List.mem_range']
      refine ⟨minFac n - 2, by lia, by lia⟩
    have hall_dvd := List.all_eq_true.mp hall (minFac n) hd_mem
    simp only [Bool.or_eq_true, decide_eq_true_iff, bne_iff_ne, ne_eq] at hall_dvd
    rcases hall_dvd with hgt | hdvd
    · lia
    · exact hdvd (Nat.mod_eq_zero_of_dvd (minFac_dvd n))
  · have hn341 : n = 341 := beq_iff_eq.mp h341
    subst hn341
    have hcop : Nat.Coprime 3 341 := by decide
    have hpp := hc.probablePrime_of_coprime hcop
    exact decide_eq_true hpp
  · have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hc.odd
    have hpp := hc.probablePrime_of_coprime hcop
    exact decide_eq_true hpp

set_option exponentiation.threshold 1000
set_option maxRecDepth 2000

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

theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n := by
  by_contra! h
  exact not_isCarmichael_of_lt_561 h hn

end Nat
