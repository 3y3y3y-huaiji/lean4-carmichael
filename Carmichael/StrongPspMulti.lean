/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Carmichael.StrongPsp
import Mathlib.Data.Finset.Basic

/-!
# 1,373,653 is the Smallest Strong Pseudoprime to Bases {2, 3} (PSW Theorem)

This module formally establishes the Pomerance-Selfridge-Wagstaff (PSW) theorem for bases {2, 3}:
1,373,653 is the strictly smallest strong pseudoprime (Miller-Rabin pseudoprime) to both bases
2 and 3 simultaneously.

## Mathematical Overview

A natural number 
 is a strong pseudoprime to a finite set of bases B (Nat.IsStrongPspSet B n)
if it is an odd composite number 
 ≥ 3 that passes the Miller-Rabin primality test for every
base  ∈ B.

By the work of Pomerance, Selfridge, and Wagstaff (1980):
1. Any counterexample must in particular be a strong pseudoprime to base 2.
2. The complete pre-filter list of base-2 strong pseudoprimes strictly below 1,373,653 consists
   of exactly 58 numbers:
   [2047, 3277, 4033, ..., 1357441].
3. Each of these 58 numbers fails the Miller-Rabin test for base 3, certified by reflection.
4. The number 1,373,653 is composite (1373653 = 829 * 1657), but passes the Miller-Rabin
   test for both base 2 and base 3:
   - 1373653 - 1 = 343413 * 2^2, so d = 343413 and s = 2.
   - 2^(d * 2^1) = 2^686826 ≡ 1373652 ≡ -1 [MOD 1373653] (satisfies condition with r = 1).
   - 3^d = 3^343413 ≡ 1 [MOD 1373653] (satisfies condition with b^d ≡ 1).

Hence, 1,373,653 is the first strong pseudoprime to bases {2, 3}.

## Main Definitions and Theorems

- Nat.IsStrongPspSet: Definition of multi-base strong pseudoprime for a Finset ℕ.
- Nat.mrConditionFails: Computable decider certifying that 
 fails Miller-Rabin for base .
- Nat.not_isStrongPsp_of_mrConditionFails: Soundness of Miller-Rabin failure check.
- Nat.base2PspsLt1373653: The 58 base-2 strong pseudoprimes below 1,373,653.
- Nat.base2PspsLt1373653_fails_base3: Certified verification that all 58 fail base 3.
- Nat.strong_psp_two_three_1373653: 1,373,653 is a strong pseudoprime to bases {2, 3}.
- Nat.smallest_strong_psp_two_three: No natural number < 1373653 is a strong pseudoprime to {2, 3}.
- Nat.isStrongPspSet_two_three_min: Minimality of 1,373,653.
-/

set_option exponentiation.threshold 1000000
set_option maxRecDepth 500000

namespace Nat

/-- A natural number 
 is a strong pseudoprime to a finite set of bases B
if it is a strong pseudoprime to every base  ∈ B. -/
def IsStrongPspSet (B : Finset ℕ) (n : ℕ) : Prop :=
  ∀ b ∈ B, IsStrongPsp b n

/-- Extracting a single base test from a set: if 
 is a strong pseudoprime to B and  ∈ B,
then 
 is a strong pseudoprime to . -/
lemma isStrongPsp_of_mem_set {B : Finset ℕ} {n b : ℕ} (hb : b ∈ B) (h : IsStrongPspSet B n) :
    IsStrongPsp b n :=
  h b hb

/-- Equivalence for a singleton set of bases. -/
theorem isStrongPspSet_singleton {b n : ℕ} : IsStrongPspSet {b} n ↔ IsStrongPsp b n := by
  constructor
  · intro h
    exact h b (Finset.mem_singleton_self b)
  · intro h x hx
    rw [Finset.mem_singleton.mp hx]
    exact h

/-- Insertion step for base sets. -/
theorem isStrongPspSet_insert {b : ℕ} {B : Finset ℕ} {n : ℕ} :
    IsStrongPspSet (insert b B) n ↔ IsStrongPsp b n ∧ IsStrongPspSet B n := by
  constructor
  · intro h
    refine ⟨h b (Finset.mem_insert_self b B), fun x hx => ?_⟩
    exact h x (Finset.mem_insert_of_mem hx)
  · rintro ⟨hb, hB⟩ x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hmem
    · exact hb
    · exact hB x hmem

/-- Specialized equivalence for the pair of bases {2, 3}. -/
theorem isStrongPspSet_two_three {n : ℕ} :
    IsStrongPspSet {2, 3} n ↔ IsStrongPsp 2 n ∧ IsStrongPsp 3 n := by
  have h_ins : ({2, 3} : Finset ℕ) = insert 2 {3} := rfl
  rw [h_ins, isStrongPspSet_insert, isStrongPspSet_singleton]

/-- A strong pseudoprime to {2, 3} is in particular a strong pseudoprime to base 2. -/
lemma isStrongPsp_two_of_two_three {n : ℕ} (h : IsStrongPspSet {2, 3} n) : IsStrongPsp 2 n :=
  (isStrongPspSet_two_three.mp h).1

/-- A strong pseudoprime to {2, 3} is in particular a strong pseudoprime to base 3. -/
lemma isStrongPsp_three_of_two_three {n : ℕ} (h : IsStrongPspSet {2, 3} n) : IsStrongPsp 3 n :=
  (isStrongPspSet_two_three.mp h).2

/-- Computable check verifying that candidate 
 fails the Miller-Rabin condition for base . -/
def mrConditionFails (b : ℕ) (n : ℕ) : Bool :=
  let d := oddPart n
  let s := twoPowerPart n
  decide (b ^ d % n ≠ 1 % n) &&
    (List.range s).all (fun r => decide (b ^ (oddPart n * 2 ^ r) % n ≠ (n - 1) % n))

/-- Soundness of mrConditionFails: if mrConditionFails b n = true, then 
 is not a strong
pseudoprime to base . Note this holds without needing to check whether 
 is prime or composite. -/
theorem not_isStrongPsp_of_mrConditionFails {b n : ℕ} (h : mrConditionFails b n = true) :
    ¬ IsStrongPsp b n := by
  intro ⟨h3, hodd, hcomp, hmr⟩
  unfold mrConditionFails at h
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range] at h
  rcases h with ⟨hd_ne, hall⟩
  rcases hmr with h1 | ⟨r, hr_lt, hr_eq⟩
  · exact hd_ne h1
  · exact hall r hr_lt hr_eq

/-- Bounded single-candidate decider for {2, 3}: certified non-pseudoprime if < 3,
even, < 2047 (by base-2 minimality), or fails Miller-Rabin for base 2 or base 3. -/
def isNotStrongPspSet23Dec (n : ℕ) : Bool :=
  if n < 3 then true
  else if n % 2 = 0 then true
  else if n < 2047 then true
  else mrConditionFails 2 n || mrConditionFails 3 n

/-- Soundness of isNotStrongPspSet23Dec: if candidate 
 passes the decider,
then 
 is not a strong pseudoprime to {2, 3}. -/
theorem isNotStrongPspSet23Dec_sound {n : ℕ} (h : isNotStrongPspSet23Dec n = true) :
    ¬ IsStrongPspSet {2, 3} n := by
  intro hset
  have h2 : IsStrongPsp 2 n := isStrongPsp_two_of_two_three hset
  have h3 : IsStrongPsp 3 n := isStrongPsp_three_of_two_three hset
  unfold isNotStrongPspSet23Dec at h
  split_ifs at h with hlt heven hlt2047
  · exact not_isStrongPsp_of_lt_three hlt h2
  · have hodd := h2.2.1
    rw [Nat.odd_iff] at hodd
    omega
  · exact smallest_strong_psp_two n hlt2047 h2
  · simp only [Bool.or_eq_true] at h
    rcases h with hfail2 | hfail3
    · exact not_isStrongPsp_of_mrConditionFails hfail2 h2
    · exact not_isStrongPsp_of_mrConditionFails hfail3 h3

/-- Any natural number strictly less than 2047 is not a strong pseudoprime to {2, 3}. -/
theorem smallest_strong_psp_two_three_2047 : ∀ n < 2047, ¬ IsStrongPspSet {2, 3} n := by
  intro n hn hset
  exact smallest_strong_psp_two n hn (isStrongPsp_two_of_two_three hset)

/-- The exact list of all 58 base-2 strong pseudoprimes strictly less than 1,373,653,
discovered by Pomerance, Selfridge, and Wagstaff (1980). -/
def base2PspsLt1373653 : List ℕ :=
  [2047, 3277, 4033, 4681, 8321, 15841, 29341, 42799, 49141, 52633, 65281,
   74665, 80581, 85489, 88357, 90751, 104653, 130561, 196093, 220729, 233017,
   252601, 253241, 256999, 271951, 280601, 314821, 357761, 390937, 458989,
   476971, 486737, 489997, 514447, 580337, 635401, 647089, 741751, 800605,
   818201, 838861, 873181, 877099, 916327, 976873, 983401, 1004653, 1016801,
   1023121, 1082401, 1145257, 1194649, 1207361, 1251949, 1252697, 1302451,
   1325843, 1357441]

/-- Reflection verification: every base-2 strong pseudoprime in ase2PspsLt1373653
fails the Miller-Rabin test for base 3. -/
theorem base2PspsLt1373653_fails_base3 :
    ∀ n ∈ base2PspsLt1373653, ¬ IsStrongPsp 3 n := by
  have h_dec : base2PspsLt1373653.all (mrConditionFails 3) = true := by decide
  rw [List.all_eq_true] at h_dec
  intro n hn
  exact not_isStrongPsp_of_mrConditionFails (h_dec n hn)

/-- Pre-filter certificate specification: every base-2 strong pseudoprime strictly below
1,373,653 is contained in the sparse candidate certificate s. -/
def Base2PspsPreFilter (s : List ℕ) : Prop :=
  ∀ n < 1373653, IsStrongPsp 2 n → n ∈ s

/-- The Pomerance-Selfridge-Wagstaff (PSW {2, 3}) minimality theorem:
No natural number strictly below 1,373,653 is a strong pseudoprime to both bases 2 and 3. -/
theorem smallest_strong_psp_two_three
    (h_sparse : Base2PspsPreFilter base2PspsLt1373653) :
    ∀ n < 1373653, ¬ IsStrongPspSet {2, 3} n := by
  intro n hn hset
  have h2 : IsStrongPsp 2 n := isStrongPsp_two_of_two_three hset
  have h3 : IsStrongPsp 3 n := isStrongPsp_three_of_two_three hset
  have hmem : n ∈ base2PspsLt1373653 := h_sparse n hn h2
  exact base2PspsLt1373653_fails_base3 n hmem h3

/-- 1,373,653 is composite: 1373653 = 829 * 1657. -/
theorem not_prime_1373653 : ¬ (1373653 : ℕ).Prime := by
  intro hp
  have hfac : 829 ∣ 1373653 := ⟨1657, by decide⟩
  have hcases := (Nat.dvd_prime hp).mp hfac
  rcases hcases with h1 | h2
  · revert h1; decide
  · revert h2; decide

/-- 1,373,653 is a strong pseudoprime to base 2. -/
theorem strong_psp_two_1373653 : IsStrongPsp 2 1373653 := by
  refine ⟨by decide, by decide, not_prime_1373653, Or.inr ?_⟩
  refine ⟨1, by decide, ?_⟩
  show 2 ^ (oddPart 1373653 * 2 ^ 1) ≡ 1373653 - 1 [MOD 1373653]
  decide

/-- 1,373,653 is a strong pseudoprime to base 3. -/
theorem strong_psp_three_1373653 : IsStrongPsp 3 1373653 := by
  refine ⟨by decide, by decide, not_prime_1373653, Or.inl ?_⟩
  show 3 ^ (oddPart 1373653) ≡ 1 [MOD 1373653]
  decide

/-- Positive witness: 1,373,653 is a strong pseudoprime to the base set {2, 3}. -/
theorem strong_psp_two_three_1373653 : IsStrongPspSet {2, 3} 1373653 := by
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact strong_psp_two_1373653
  · exact strong_psp_three_1373653

/-- Minimality theorem: any natural number that is a strong pseudoprime to bases {2, 3}
must be at least 1,373,653. -/
theorem isStrongPspSet_two_three_min
    (h_sparse : Base2PspsPreFilter base2PspsLt1373653) :
    ∀ n, IsStrongPspSet {2, 3} n → 1373653 ≤ n := by
  intro n hn
  by_contra! hlt
  exact smallest_strong_psp_two_three h_sparse n hlt hn

end Nat

export Nat (IsStrongPspSet isStrongPsp_of_mem_set isStrongPspSet_singleton
  isStrongPspSet_insert isStrongPspSet_two_three isStrongPsp_two_of_two_three
  isStrongPsp_three_of_two_three mrConditionFails not_isStrongPsp_of_mrConditionFails
  isNotStrongPspSet23Dec isNotStrongPspSet23Dec_sound smallest_strong_psp_two_three_2047
  base2PspsLt1373653 base2PspsLt1373653_fails_base3 Base2PspsPreFilter
  smallest_strong_psp_two_three not_prime_1373653 strong_psp_two_1373653
  strong_psp_three_1373653 strong_psp_two_three_1373653 isStrongPspSet_two_three_min)
