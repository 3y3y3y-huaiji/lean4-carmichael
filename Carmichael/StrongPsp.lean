/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.Tactic

/-!
# 2047 is the Smallest Strong Pseudoprime to Base 2

This module formally establishes that 2047 is the strictly smallest strong pseudoprime
(Miller-Rabin pseudoprime) to base 2 in Lean 4 with Mathlib4.

## Mathematical Overview

A natural number 
 is a strong pseudoprime to base  if it is an odd composite number 
 ≥ 3
that passes the Miller-Rabin primality test to base : writing 
 - 1 = d * 2^s with d odd,
either:
- ^d ≡ 1 [MOD n], or
- ∃ r < s, b^(d * 2^r) ≡ n - 1 [MOD n].

2047 is the 11th Mersenne number ^{11} - 1 = 23 \times 89$. Since  - 1 = 2046 = 1023 \times 2^1$,
we have  = 1023$ and  = 1$. Because  = 11 \times 93$,
2^{1023} = (2^{11})^{93} \equiv 1^{93} = 1 \pmod{2047},
making 2047 the first strong pseudoprime to base 2.

## Main Results

- Nat.oddPart, Nat.twoPowerPart: Computable decomposition  - 1 = d \cdot 2^s$.
- Nat.oddPart_mul_twoPowerPart: Specification  \cdot 2^s = n - 1$.
- Nat.IsStrongPsp: Standard mathematical definition of base- strong pseudoprime.
- Nat.isPrimeDec2047: Trial division prime decider for all numbers  < 2047$.
- Nat.isNotStrongPspDec2: Computable decider certifying that $ is not a base-2 strong pseudoprime.
- Nat.isNotStrongPspDec2_sound: Soundness of the single-candidate decider.
- Nat.checkStrongPspBound2: Bounded reflection checker for  < N$.
- Nat.checkStrongPspBound2_sound: Soundness of the bounded checker.
- Nat.smallest_strong_psp_two: No natural number  < 2047$ is a strong pseudoprime to base 2.
- Nat.strong_psp_2047: 2047 is a strong pseudoprime to base 2.
- Nat.isStrongPsp_min: Minimality: any base-2 strong pseudoprime is $\ge 2047$.
-/

set_option exponentiation.threshold 3000
set_option maxRecDepth 500000

namespace Nat

/-- Auxiliary function to decompose m into (d, s) such that m = d * 2^s with d odd. -/
def splitTwoAux : ℕ → ℕ → ℕ × ℕ
| 0, m => (m, 0)
| fuel + 1, m =>
  if m = 0 then (0, 0)
  else if m % 2 = 0 then
    let res := splitTwoAux fuel (m / 2)
    (res.1, res.2 + 1)
  else
    (m, 0)

/-- Computable decomposition of m into (d, s) such that m = d * 2^s. -/
def splitTwo (m : ℕ) : ℕ × ℕ := splitTwoAux m m

/-- The odd factor d in the 2-adic decomposition 
 - 1 = d * 2^s. -/
def oddPart (n : ℕ) : ℕ := (splitTwo (n - 1)).1

/-- The exponent s of 2 in the 2-adic decomposition 
 - 1 = d * 2^s. -/
def twoPowerPart (n : ℕ) : ℕ := (splitTwo (n - 1)).2

lemma splitTwoAux_spec : ∀ (fuel m : ℕ), m ≤ fuel →
    (splitTwoAux fuel m).1 * 2 ^ (splitTwoAux fuel m).2 = m
| 0, 0, _ => by simp [splitTwoAux]
| 0, m + 1, h => by omega
| fuel + 1, m, h => by
  rw [splitTwoAux]
  split_ifs with h0 heven
  · subst h0
    simp
  · have hdiv_le : m / 2 ≤ fuel := by omega
    have ih := splitTwoAux_spec fuel (m / 2) hdiv_le
    dsimp only
    rw [pow_succ', ← mul_assoc, mul_right_comm, ih]
    have hmod := Nat.div_add_mod m 2
    omega
  · simp

lemma splitTwo_spec (m : ℕ) : (splitTwo m).1 * 2 ^ (splitTwo m).2 = m :=
  splitTwoAux_spec m m (le_refl m)

/-- The fundamental decomposition equality: oddPart n * 2 ^ (twoPowerPart n) = n - 1. -/
theorem oddPart_mul_twoPowerPart (n : ℕ) :
    oddPart n * 2 ^ twoPowerPart n = n - 1 :=
  splitTwo_spec (n - 1)

/-- Auxiliary lemma: for any non-zero m ≤ fuel, (splitTwoAux fuel m).1 is odd. -/
lemma splitTwoAux_odd : ∀ (fuel m : ℕ), m ≤ fuel → m ≠ 0 →
    (splitTwoAux fuel m).1 % 2 ≠ 0
| 0, 0, _, hne => by contradiction
| 0, _ + 1, hle, _ => by omega
| fuel + 1, m, hle, hne => by
  rw [splitTwoAux]
  split_ifs with h0 heven
  · contradiction
  · have hdiv_le : m / 2 ≤ fuel := by omega
    have hdiv_ne : m / 2 ≠ 0 := by omega
    exact splitTwoAux_odd fuel (m / 2) hdiv_le hdiv_ne
  · exact heven

/-- For any 
 ≥ 2, oddPart n is odd. -/
theorem odd_oddPart {n : ℕ} (hn : 2 ≤ n) : Odd (oddPart n) := by
  have hm : n - 1 ≠ 0 := by omega
  have hmod := splitTwoAux_odd (n - 1) (n - 1) (le_refl (n - 1)) hm
  rw [Nat.odd_iff]
  have h1 : oddPart n = (splitTwoAux (n - 1) (n - 1)).1 := rfl
  rw [h1]
  exact Nat.mod_two_ne_zero.mp hmod

/-- A natural number n is a strong pseudoprime (Miller-Rabin pseudoprime) to base b if
it is an odd composite number n ≥ 3 such that either b^d ≡ 1 [MOD n] or
∃ r < s, b^(d * 2^r) ≡ n - 1 [MOD n], where n - 1 = d * 2^s with d odd.
For n < 3, even n, or prime n, IsStrongPsp b n is False. -/
def IsStrongPsp (b : ℕ) (n : ℕ) : Prop :=
  3 ≤ n ∧ Odd n ∧ ¬ n.Prime ∧
    (b ^ (oddPart n) ≡ 1 [MOD n] ∨
      ∃ r < twoPowerPart n, b ^ (oddPart n * 2 ^ r) ≡ n - 1 [MOD n])

lemma not_isStrongPsp_of_lt_three {b n : ℕ} (h : n < 3) : ¬ IsStrongPsp b n := by
  intro ⟨h3, _⟩
  omega

lemma not_isStrongPsp_of_even {b n : ℕ} (h : Even n) : ¬ IsStrongPsp b n := by
  intro ⟨_, hodd, _⟩
  rw [Nat.odd_iff] at hodd
  rw [Nat.even_iff] at h
  omega

lemma not_isStrongPsp_of_prime {b n : ℕ} (h : n.Prime) : ¬ IsStrongPsp b n := by
  intro hpsp
  exact hpsp.2.2.1 h

/-- Odd prime divisors up to $\lfloor\sqrt{2047}\rfloor = 45$. -/
def testPrimes2047 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

/-- Computable prime decider for natural numbers strictly below 2047. -/
def isPrimeDec2047 (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else testPrimes2047.all (fun p => decide (p ≥ n) || decide (n % p ≠ 0))

theorem prime_le_43_mem_testPrimes {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (h43 : p ≤ 43) :
    p ∈ testPrimes2047 := by
  interval_cases p <;> first | decide | (revert hp; decide)

theorem isPrimeDec2047_prime {n : ℕ} (hn : n < 2047) (h : isPrimeDec2047 n = true) :
    Nat.Prime n := by
  unfold isPrimeDec2047 at h
  split_ifs at h with hlt h2 heven
  · subst h2
    exact Nat.prime_two
  · by_contra hnp
    have h2le : 2 ≤ n := by omega
    have hp_prime : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hp_dvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hp_ne2 : Nat.minFac n ≠ 2 := by
      intro hp2
      have : 2 ∣ n := hp2 ▸ hp_dvd
      have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      contradiction
    have hp_ge3 : 3 ≤ Nat.minFac n := by
      have := hp_prime.two_le
      omega
    have hp_lt : Nat.minFac n < n := (Nat.not_prime_iff_minFac_lt h2le).mp hnp
    have hdiv_ge2 : 2 ≤ n / Nat.minFac n := by
      have hmul : n = Nat.minFac n * (n / Nat.minFac n) := (Nat.mul_div_cancel' hp_dvd).symm
      by_contra! hlt
      interval_cases (n / Nat.minFac n)
      · omega
      · omega
    have hq : Nat.minFac n ≤ n / Nat.minFac n :=
      Nat.minFac_le_of_dvd hdiv_ge2 (Nat.div_dvd_of_dvd hp_dvd)
    have h_mul_div : Nat.minFac n * (n / Nat.minFac n) = n := Nat.mul_div_cancel' hp_dvd
    have h_sq : Nat.minFac n * Nat.minFac n ≤ n := by
      have h_le : Nat.minFac n * Nat.minFac n ≤ Nat.minFac n * (n / Nat.minFac n) :=
        Nat.mul_le_mul_left (Nat.minFac n) hq
      rwa [h_mul_div] at h_le
    have hp_le_43 : Nat.minFac n ≤ 43 := by
      by_contra! h44
      have hp47 : 47 ≤ Nat.minFac n := by
        by_contra! hlt
        interval_cases Nat.minFac n <;> revert hp_prime <;> decide
      have h2209 : 47 * 47 ≤ Nat.minFac n * Nat.minFac n := Nat.mul_le_mul hp47 hp47
      omega
    have hp_mem : Nat.minFac n ∈ testPrimes2047 :=
      prime_le_43_mem_testPrimes hp_prime hp_ge3 hp_le_43
    rw [List.all_eq_true] at h
    have hspec := h (Nat.minFac n) hp_mem
    simp only [Bool.or_eq_true, decide_eq_true_iff] at hspec
    rcases hspec with hge | hne
    · omega
    · rw [Nat.dvd_iff_mod_eq_zero] at hp_dvd
      exact hne hp_dvd

theorem isPrimeDec2047_iff {n : ℕ} (hn : n < 2047) :
    isPrimeDec2047 n = true ↔ Nat.Prime n := by
  constructor
  · exact isPrimeDec2047_prime hn
  · intro hp
    unfold isPrimeDec2047
    split_ifs with hlt h2 heven
    · have := hp.two_le
      omega
    · rfl
    · have ho := hp.eq_two_or_odd
      rcases ho with rfl | ho
      · omega
      · omega
    · rw [List.all_eq_true]
      intro p hp_mem
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      by_cases hle : p < n
      · right
        intro hmod
        have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have heq := (Nat.dvd_prime hp).mp hdvd
        rcases heq with rfl | rfl
        · revert hp_mem
          decide
        · omega
      · left
        omega

/-- Computable decider certifying that 
 is NOT a strong pseudoprime to base 2.
Returns 	rue if 
 < 3, 
 is even, or 
 is detected prime.
For odd composite candidates below 2047, verifies that the Miller-Rabin test base 2 fails. -/
def isNotStrongPspDec2 (n : ℕ) : Bool :=
  if n < 3 then true
  else if n % 2 = 0 then true
  else if n < 2047 then
    if isPrimeDec2047 n then true
    else
      let d := oddPart n
      let s := twoPowerPart n
      decide (2 ^ d % n ≠ 1) &&
        (List.range s).all (fun r => decide (2 ^ (d * 2 ^ r) % n ≠ (n - 1) % n))
  else false

/-- Soundness of isNotStrongPspDec2: if isNotStrongPspDec2 n = true,
then n is not a strong pseudoprime to base 2. -/
theorem isNotStrongPspDec2_sound {n : ℕ} (h : isNotStrongPspDec2 n = true) :
    ¬ IsStrongPsp 2 n := by
  intro ⟨h3, hodd, hcomp, hmr⟩
  unfold isNotStrongPspDec2 at h
  split_ifs at h with hlt heven hlt2047 hp
  · omega
  · rw [Nat.odd_iff] at hodd
    omega
  · have hprime : n.Prime := (isPrimeDec2047_iff hlt2047).mp hp
    exact hcomp hprime
  · simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range] at h
    rcases h with ⟨hd_ne, hall⟩
    rcases hmr with h1 | ⟨r, hr_lt, hr_eq⟩
    · have h1mod : 2 ^ oddPart n % n = 1 % n := h1
      have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1n] at h1mod
      exact hd_ne h1mod
    · have hspec := hall r hr_lt
      have hmod_eq : 2 ^ (oddPart n * 2 ^ r) % n = (n - 1) % n := hr_eq
      exact hspec hmod_eq

/-- Bounded verification checker: returns true if all 
 < N are certified not strong pseudoprimes
to base 2. -/
def checkStrongPspBound2 (N : ℕ) : Bool :=
  (List.range N).all isNotStrongPspDec2

/-- Soundness of checkStrongPspBound2: if checkStrongPspBound2 N = true,
then no natural number strictly below N is a strong pseudoprime to base 2. -/
theorem checkStrongPspBound2_sound {N : ℕ} (h : checkStrongPspBound2 N = true) :
    ∀ n < N, ¬ IsStrongPsp 2 n := by
  intro n hn
  unfold checkStrongPspBound2 at h
  rw [List.all_eq_true] at h
  have hmem : n ∈ List.range N := List.mem_range.mpr hn
  exact isNotStrongPspDec2_sound (h n hmem)

/-- 2047 is the strictly smallest strong pseudoprime to base 2: no natural number strictly less
than 2047 is a strong pseudoprime to base 2. -/
theorem smallest_strong_psp_two : ∀ n < 2047, ¬ IsStrongPsp 2 n := by
  have h_dec : checkStrongPspBound2 2047 = true := by decide
  exact checkStrongPspBound2_sound h_dec

/-- 2047 is a strong pseudoprime to base 2 (composite, passes Miller-Rabin test base 2). -/
theorem strong_psp_2047 : IsStrongPsp 2 2047 := by
  refine ⟨by decide, by decide, ?_, Or.inl ?_⟩
  · intro hp
    have hfac : 23 ∣ 2047 := ⟨89, by decide⟩
    have hcases := (Nat.dvd_prime hp).mp hfac
    rcases hcases with h1 | h2
    · revert h1; decide
    · revert h2; decide
  · show 2 ^ (oddPart 2047) ≡ 1 [MOD 2047]
    decide

/-- 2047 is the minimum strong pseudoprime to base 2: any strong pseudoprime to base 2
is at least 2047. -/
theorem isStrongPsp_min : ∀ n, IsStrongPsp 2 n → 2047 ≤ n := by
  intro n hn
  by_contra! hlt
  exact smallest_strong_psp_two n hlt hn

end Nat

export Nat (IsStrongPsp oddPart twoPowerPart oddPart_mul_twoPowerPart odd_oddPart
  not_isStrongPsp_of_lt_three not_isStrongPsp_of_even not_isStrongPsp_of_prime
  testPrimes2047 isPrimeDec2047 isPrimeDec2047_prime isPrimeDec2047_iff
  isNotStrongPspDec2 isNotStrongPspDec2_sound checkStrongPspBound2
  checkStrongPspBound2_sound smallest_strong_psp_two strong_psp_2047
  isStrongPsp_min)
