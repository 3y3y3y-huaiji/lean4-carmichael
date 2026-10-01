/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.Tactic.Linarith
import Carmichael.Tactic

/-!
# 561 is the Smallest Carmichael Number

This module proves that 561 is the strictly smallest Carmichael number, resolving
the open TODO in Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`.

The proof implements an extensible modular funnel reflection architecture:
`Bitwise Parity Gate → Small Prime Trial Division (≤ 23) → Dual-Base Fermat Gate (Bases 2 & 3)`.
-/

namespace Nat

/-- Parity gate: immediate rejection of `n ≤ 2` or even numbers. -/
def isEvenOrSmall (n : ℕ) : Bool :=
  n ≤ 2 || n % 2 == 0

lemma not_isEvenOrSmall_of_isCarmichael {n : ℕ} (hc : n.IsCarmichael) :
    isEvenOrSmall n = false := by
  obtain ⟨k, rfl⟩ := hc.odd; have := hc.two_lt; simp [isEvenOrSmall]; grind

/-- Bounded trial division gate: checks if `n` has no divisors `d` in `2 ≤ d < bound`
with `d * d ≤ n`. -/
def isPrimeTrial (bound : ℕ) (n : ℕ) : Bool :=
  (List.range' 2 (bound - 2)).all (fun d => decide (n < d * d) || n % d != 0)

lemma not_isPrimeTrial_of_isCarmichael {bound n : ℕ} (hn : n < bound ^ 2) (hc : n.IsCarmichael) :
    isPrimeTrial bound n = false := by
  rw [Bool.eq_false_iff]; intro hall
  have hp : 2 ≤ minFac n := (minFac_prime (by grind [hc.two_lt])).two_le
  have h_sq := minFac_sq_le_self (by grind [hc.two_lt]) hc.not_prime
  have h_lt : minFac n < bound := by
    by_contra! hge
    have : bound ^ 2 ≤ minFac n ^ 2 := by nlinarith
    nlinarith
  have hmem : minFac n ∈ List.range' 2 (bound - 2) :=
    List.mem_range'.mpr ⟨minFac n - 2, by omega, by omega⟩
  have hdvd := List.all_eq_true.mp hall _ hmem
  simp only [Bool.or_eq_true, decide_eq_true_iff, bne_iff_ne, ne_eq] at hdvd
  rcases hdvd with hlt | hndvd <;> [nlinarith; exact hndvd (Nat.mod_eq_zero_of_dvd (minFac_dvd n))]

/-- A list of candidate bases witnesses that `n` is not a Carmichael number
if for some base `b ∈ bases` coprime to `n`, `n` fails the Fermat test. -/
def hasFermatWitness (n : ℕ) (bases : List ℕ := [2, 3]) : Bool :=
  bases.any fun b => decide (b.Coprime n) && !decide (ProbablePrime n b)

lemma not_hasFermatWitness_of_isCarmichael {n : ℕ} (bases : List ℕ) (hc : n.IsCarmichael) :
    hasFermatWitness n bases = false := by
  simp [hasFermatWitness, List.any_eq_false]
  intro b _ hb
  simp [hc.probablePrime_of_coprime hb]

/-- Composite candidate decider combining all filter stages. -/
def isCarmichaelCandidate (n : ℕ) (bound : ℕ := 24) (bases : List ℕ := [2, 3]) : Bool :=
  if isEvenOrSmall n then false
  else if isPrimeTrial bound n then false
  else !hasFermatWitness n bases

theorem isCarmichaelCandidate_of_isCarmichael {bound n : ℕ}
    (hn : n < bound ^ 2) (hc : n.IsCarmichael) :
    isCarmichaelCandidate n bound [2, 3] = true := by
  simp [isCarmichaelCandidate, not_isEvenOrSmall_of_isCarmichael hc,
    not_isPrimeTrial_of_isCarmichael hn hc, not_hasFermatWitness_of_isCarmichael [2, 3] hc]
/-- Exhaustive verifier ensuring no candidates exist below `N`. -/
def checkCarmichaelBound (N : ℕ) (bound : ℕ := 24) (bases : List ℕ := [2, 3]) : Bool :=
  (List.range N).all (fun n => !isCarmichaelCandidate n bound bases)

theorem checkCarmichaelBound_sound {N bound : ℕ} (hN : N ≤ bound ^ 2)
    (h : checkCarmichaelBound N bound [2, 3] = true) :
    ∀ n < N, ¬ n.IsCarmichael := fun n hn hc => by
  simpa [isCarmichaelCandidate_of_isCarmichael (by nlinarith) hc] using
    List.all_eq_true.mp h n (List.mem_range.mpr hn)

theorem not_isCarmichael_of_lt_561 {n : ℕ} (hn : n < 561) : ¬ n.IsCarmichael :=
  checkCarmichaelBound_sound (bound := 24) (by decide) (by decide +kernel) n hn

/-- 561 is the smallest Carmichael number. -/
theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n :=
  not_lt.mp (not_isCarmichael_of_lt_561 · hn)

/-- 561 is a Carmichael number certified via the Korselt reflection tactic. -/
theorem isCarmichael_561 : (561 : ℕ).IsCarmichael := by
  carmichael

end Nat
