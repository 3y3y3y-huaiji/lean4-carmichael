/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.CarmichaelNumber

/-!
# 561 is the Smallest Carmichael Number

This module proves that 561 is the strictly smallest Carmichael number, resolving
the open TODO in Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`.
-/

namespace Nat

/-- Small primes up to 37, sufficient to witness Korselt divisibility failure for candidates. -/
def smallPrimes : List ℕ := (List.range 38).filter (fun p => decide p.Prime)

lemma mem_smallPrimes_prime {p : ℕ} (h : p ∈ smallPrimes) : p.Prime :=
  of_decide_eq_true (List.mem_filter.mp h).2

/-- Computable certificate that `n` is not a Carmichael number. -/
def isNotCarmichael (n : ℕ) : Bool :=
  if n ≤ 2 then true
  else if n % 2 = 0 then true
  else if (List.range' 2 22).any (fun d => n % (d * d) == 0) then true
  else if smallPrimes.any (fun p =>
    if n % p == 0 then
      (n - 1) % (p - 1) != 0 || (decide ((n / p).Prime) && (n - 1) % ((n / p) - 1) != 0)
    else false
  ) then true
  else decide n.Prime

/-- Soundness of `isNotCarmichael`: if certified, `n` is not Carmichael. -/
theorem not_isCarmichael_of_dec {n : ℕ} (h : isNotCarmichael n = true) : ¬ n.IsCarmichael := by
  intro hc
  unfold isNotCarmichael at h
  split_ifs at h with h2 heven hsq hk
  · have := hc.1; omega
  · rcases hc.odd with ⟨k, rfl⟩; omega
  · rw [List.any_eq_true] at hsq
    rcases hsq with ⟨d, hd_mem, hd_div⟩
    have hd_ge : 2 ≤ d := by rcases List.mem_range'.mp hd_mem with ⟨i, -, rfl⟩; omega
    have hdiv : d * d ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hd_div)
    have hu := isUnit_iff_eq_one.mp (hc.squarefree d hdiv)
    omega
  · rw [List.any_eq_true] at hk
    rcases hk with ⟨p, hp_mem, hcond⟩
    have hkorselt := isCarmichael_iff_korselt.mp hc |>.2.2.2
    split_ifs at hcond with hdvd
    have hp_dvd : p ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hdvd)
    simp only [Bool.or_eq_true, decide_eq_true_iff, Bool.and_eq_true] at hcond
    rcases hcond with hp_fail | ⟨hq_prime, hq_fail⟩
    · exact (bne_iff_ne.mp hp_fail)
        (Nat.dvd_iff_mod_eq_zero.mp (hkorselt p (mem_smallPrimes_prime hp_mem) hp_dvd))
    · exact (bne_iff_ne.mp hq_fail)
        (Nat.dvd_iff_mod_eq_zero.mp (hkorselt (n / p) hq_prime (Nat.div_dvd_of_dvd hp_dvd)))
  · exact hc.2.1 (of_decide_eq_true h)

/-- Bounded verifier checking that no natural number below `N` is Carmichael. -/
def checkCarmichaelBound (N : ℕ) : Bool := (List.range N).all isNotCarmichael
theorem checkCarmichaelBound_sound {N : ℕ} (h : checkCarmichaelBound N = true) :
    ∀ n < N, ¬ n.IsCarmichael := fun n hn =>
  not_isCarmichael_of_dec ((List.all_eq_true.mp h) n (List.mem_range.mpr hn))
set_option maxRecDepth 10000 in
/-- There are no Carmichael numbers strictly less than 561. -/
theorem not_isCarmichael_of_lt_561 {n : ℕ} (hn : n < 561) : ¬ n.IsCarmichael :=
  checkCarmichaelBound_sound (by decide) n hn
/-- 561 is the minimal Carmichael number. -/
theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n :=
  not_lt.mp (not_isCarmichael_of_lt_561 · hn)
/-- Any number with at most 2 prime factors is not Carmichael. -/
theorem not_isCarmichael_of_card_primeFactors_le_two {n : ℕ} (h : n.primeFactors.card ≤ 2) :
    ¬ n.IsCarmichael := fun hc => by have := hc.three_le_card_primeFactors; omega
end Nat
