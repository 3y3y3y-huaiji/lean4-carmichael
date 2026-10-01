/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.Data.Nat.Factors
import Lean

/-!
# Carmichael Number Certification Tactic

Automated verification tactic `carmichael` certifying Carmichael numbers via Korselt's criterion.
Emits a computational certificate checked by the Lean 4 kernel via `by decide`.
-/

open Lean Elab Tactic Meta Nat

namespace Nat

lemma coprime_list_prod {p : ℕ} {ps : List ℕ} (h : ∀ q ∈ ps, Nat.Coprime p q) :
    Nat.Coprime p ps.prod :=
  coprime_list_prod_right_iff.mpr h

lemma list_prod_dvd_of_pairwise_coprime {z : ℕ} :
    ∀ (l : List ℕ), l.Pairwise Nat.Coprime → (∀ p ∈ l, p ∣ z) → l.prod ∣ z
  | [], _, _ => one_dvd z
  | p :: ps, .cons h1 h2, hdvd =>
    (coprime_list_prod h1).mul_dvd_of_dvd_of_dvd (hdvd p (.head ps))
      (list_prod_dvd_of_pairwise_coprime ps h2 fun q hq => hdvd q (.tail p hq))

lemma dvd_sub_one_of_prime_dvd {b n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hdiv : p - 1 ∣ n - 1) (hb : b.Coprime n) : p ∣ b ^ (n - 1) - 1 := by
  obtain ⟨k, hk⟩ := hdiv
  have h := (Nat.ModEq.pow_totient (hb.coprime_dvd_right hpn)).pow k
  rw [Nat.totient_prime hp, ← Nat.pow_mul, ← hk, one_pow] at h
  exact h.symm.dvd'

lemma pairwise_coprime_of_pairwise_lt_primes {l : List ℕ}
    (hprimes : ∀ p ∈ l, p.Prime) (hlt : l.Pairwise (· < ·)) : l.Pairwise Nat.Coprime :=
  hlt.imp_of_mem fun ha hb hlt =>
    (Nat.coprime_primes (hprimes _ ha) (hprimes _ hb)).2 (Nat.ne_of_lt hlt)

/-- Korselt certificate checker: verifies that `factors` is a strictly increasing list
of prime factors of `n` satisfying Korselt divisibility conditions. -/
def checkKorseltCert (n : ℕ) (factors : List ℕ) : Bool :=
  2 < n && 2 ≤ factors.length && factors.Pairwise (· < ·) && factors.prod == n &&
  factors.all (fun p => decide p.Prime && (n - 1) % (p - 1) == 0 && (n % p == 0))

/-- Soundness of Korselt certificate checker: any number with a valid certificate is Carmichael. -/
theorem checkKorseltCert_sound {n : ℕ} {factors : List ℕ}
    (h : checkKorseltCert n factors = true) : n.IsCarmichael := by
  simp only [checkKorseltCert, Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨hn2, hlen⟩, hsorted⟩, hprod⟩, hall⟩
  rw [List.all_eq_true] at hall
  have hprops : ∀ p ∈ factors, p.Prime ∧ (p - 1 ∣ n - 1) ∧ (p ∣ n) := fun p hp => by
    have hp' := hall p hp
    simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hp'
    exact ⟨hp'.1.1, Nat.dvd_of_mod_eq_zero hp'.1.2, Nat.dvd_of_mod_eq_zero hp'.2⟩
  refine ⟨hn2, ?_, fun b hb => ?_⟩
  · match factors, hlen with
    | p :: q :: rest, _ =>
      rw [← hprod, List.prod_cons, List.prod_cons]
      have hp := (hprops p (by simp)).1.two_le
      have hq := (hprops q (by simp)).1.two_le
      have hr : 1 ≤ rest.prod := List.one_le_prod (fun x hx => (hprops x (by simp [hx])).1.pos)
      exact Nat.not_prime_mul (by grind) (by nlinarith)
  · rw [← hprod]
    exact list_prod_dvd_of_pairwise_coprime factors
      (pairwise_coprime_of_pairwise_lt_primes (fun p hp => (hprops p hp).1) hsorted)
      fun p hp => hprod ▸ dvd_sub_one_of_prime_dvd (hprops p hp).1 (hprops p hp).2.2
        (hprops p hp).2.1 hb

/-- Automated Carmichael certification tactic. -/
elab "carmichael" : tactic => withMainContext do
  let target ← getMainTarget
  match target.getAppFnArgs with
  | (``Nat.IsCarmichael, #[nExpr]) =>
    let nExpr ← whnf nExpr
    let some nVal ← getNatValue? nExpr
      | throwError "Expected concrete natural number literal in IsCarmichael"
    let f := nVal.primeFactorsList
    if !checkKorseltCert nVal f then
      throwError m!"{nVal} is not a Carmichael number (failed Korselt criterion with factors {f})"
    let fnId := mkIdent ``checkKorseltCert_sound
    evalTactic (← `(tactic| exact ($fnId (n := $(quote nVal)) (factors := $(quote f)) (by decide))))
  | _ => throwError "Expected goal of the form `Nat.IsCarmichael n`"

/-- 1105 is certified as a Carmichael number via the automated `carmichael` tactic. -/
theorem isCarmichael_1105 : (1105 : ℕ).IsCarmichael := by
  carmichael

end Nat
