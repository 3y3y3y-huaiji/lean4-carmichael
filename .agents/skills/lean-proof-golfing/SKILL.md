---
name: lean-proof-golfing
description: >-
  Guidelines, compression patterns, and tactic hierarchies derived from Mathematics in Lean and
  Mathlib community best practices. Eliminates AI-generated verbose boilerplate, prevents
  reinventing the wheel, and enforces idiomatic, compact, review-ready Lean 4 formalization.
---

# Lean 4 & Mathlib Proof Golfing & Idiomatic Style Guide

This skill distills the foundational methodologies of *Mathematics in Lean* (MIL) and the review
standards of Mathlib maintainers into actionable, automated rules. Its purpose is to eliminate
"AI spaghetti proofs" (verbose `have` chains, redundant lemmas, manual rewrites) and produce
clean, idiomatic, and highly compressed mathematical formalizations.

---

## 1. The Core Golden Rule: "Tactic-First, Never Manual"

Mathlib maintains a rich suite of automated decision procedures. A major failure mode of AI is
manually reconstructing proofs using 10+ lines of rewrite lemmas when a single modern tactic solves
the goal.

### The Mathlib Tactic Hierarchy

| Domain / Problem | Idiomatic Tactic | Anti-Pattern (AI Fluff to Avoid) |
| :--- | :--- | :--- |
| **Natural/Integer Linear Arithmetic** | `omega` | Manually chaining `Nat.le_trans`, `Nat.add_le_add_right`, `Nat.lt_of_le_of_lt` |
| **Ring & Polynomial Identities** | `ring` | Manual `Nat.mul_add`, `Nat.add_assoc`, `Nat.mul_comm` rewrites |
| **Modular Arithmetic & Subtraction** | `zify; grind` | Trying to prove $(p-1) + (q-1)p = pq - 1$ in Nat without handling underflow |
| **Concrete Numerical Calculation** | `norm_num` | Manually evaluating 3 * 11 * 17 = 561 or prime factorization |
| **Finite Domain / Bound Reflection** | `decide` | Writing manual induction or casing over 500 candidate numbers |
| **First-Order Logic & Finishing** | `grind` / `aesop` | 15 lines of nested `intro`, `cases`, `constructor`, `exact` |

---

## 2. The 5 Principles of Proof Golfing (Anti-AI Fluff)

### Rule 1: Never Reinvent Lemmas (Use Mathlib First)
- Before writing any helper lemma, check if Mathlib already has it (`exact?`, `apply?`, or search Mathlib docs).
- If Mathlib already defines a concept (e.g. `Nat.IsCarmichael`), **never redefine it**. Always import and extend the official definition.

### Rule 2: Eliminate Intermediate `have` Chains
- **AI Anti-Pattern**: Creating 5 consecutive `have` steps that each merely feed into the next line:
  ```lean
  -- BAD (AI style: 10 lines of fluff)
  have h1 : a ? b := by omega
  have h2 : b ? c := by omega
  have h3 : a ? c := Nat.le_trans h1 h2
  exact h3
  ```
- **Mathlib Idiomatic**:
  ```lean
  -- GOOD (Mathlib style: 1 line)
  omega
  ```

### Rule 3: Transition to Integer Semantics (`zify`)
In number theory, natural number subtraction (`p - 1`) truncates at 0, which makes pure Nat algebraic manipulations notoriously painful.
- **Felix's Golden Idiom**: Use `zify` to cast into Int, then let `grind` or `ring` solve it:
  ```lean
  have eq : p - 1 + (q - 1) * p = p * q - 1 := by zify; grind
  ```
  This single line replaces 30 lines of manual case-analysis on `p ? 1` and `q ? 1`!

### Rule 4: Favor Term-Mode for Simple Implications
- If a proof only takes hypotheses and passes them to a known theorem:
  ```lean
  -- BAD:
  intro hn
  exact hn.not_prime

  -- GOOD:
  exact fun hn ? hn.not_prime
  ```

### Rule 5: Computational Reflection for Finite Search
When proving that no number below N satisfies a property:
1. Define a computable decidable predicate `P_dec (n : ?) : Bool`.
2. Prove soundness: `P_dec n = false ? ? P n`.
3. Prove the bounded theorem in **1 line** using `decide`:
   ```lean
   theorem not_P_below_N : ? n < N, ? P n := by decide
   ```
   Do not branch into case splits for individual numbers!

---

## 3. Case Study: How Felix Proved "No Carmichael Number Has Exactly 2 Prime Factors" in 15 Lines

In `Mathlib.NumberTheory.CarmichaelNumber`:
```lean
theorem IsCarmichael.three_le_card_primeFactors (h : IsCarmichael n) :
    3 ? n.primeFactors.card := by
  obtain ?_, _, hs, h? := isCarmichael_iff_korselt.mp h
  have h0 : n.primeFactors.card ? 0 := by grind [primeFactors_eq_empty]
  have h1 : n.primeFactors.card ? 1 := by
    grind [squarefree_and_prime_pow_iff_prime, isPrimePow_iff_card_primeFactors_eq_one]
  by_contra h3
  have h2 : n.primeFactors.card = 2 := by grind
  obtain ?p, q, pq, hp, hq, hn? := (squarefree_and_primeFactors_card_eq_two_iff n).mp ?hs, h2?
  contrapose! pq
  have eq : p - 1 + (q - 1) * p = p * q - 1 := by zify; grind
  rw [? tsub_le_tsub_iff_right hp.one_le]
  refine le_of_dvd (tsub_pos_of_lt hp.one_lt) ((Nat.dvd_add_left ?p, rfl?).mp ?_)
  rw [eq, hn]
  exact h q hq (Dvd.intro_left p hn)
```
**Takeaways from Felix's Code**:
- Used `obtain ?...?` instead of multiple `rcases`.
- Used `grind` for card-elimination steps.
- Used `zify; grind` for the core identity $(p-1) + (q-1)p = pq - 1$.
- Zero redundant lemmas, total length: 16 lines.

---

## 4. Pre-PR Golfing Checklist

Before submitting any code to Mathlib:
- [ ] Are all line widths strictly <= 100 characters?
- [ ] Did you search Mathlib for existing definitions before writing new ones?
- [ ] Can any `have` block be replaced by `omega`, `ring`, `norm_num`, or `grind`?
- [ ] Are there natural number subtractions that can be simplified using `zify`?
- [ ] Is computational reflection (`decide`) used for bounded finite checks?
- [ ] Did you run `#lint` and ensure 0 warnings?
