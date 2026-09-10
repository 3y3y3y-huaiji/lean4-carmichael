# feat(NumberTheory/CarmichaelNumber): prove 561 is the smallest Carmichael number

This PR resolves the open TODO in `Mathlib.NumberTheory.CarmichaelNumber`:
> *"TODO: Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561."*

## Summary

We formally establish that $561$ is the strictly smallest Carmichael number, proving that there are no Carmichael numbers strictly less than $561$.

The proof executes in approximately 17 seconds on a single core without hitting recursion depth or heartbeat limits.

## Mathematical Outline & Computational Efficiency

Rather than a brute-force search over all integers $< 561$, we combine theoretical pruning with concrete candidate elimination:

1. **Theoretical Pruning**:
   - Every Carmichael number is odd (`IsCarmichael.odd`).
   - Every Carmichael number has at least 3 distinct prime factors (`three_le_card_primeFactors`).
   - Semiprimes ($p \times q$) cannot be Carmichael numbers (`not_isCarmichael_mul_primes`).
   - Candidates divisible by any square $p^2$ violate squarefreeness (`IsCarmichael.squarefree`).
2. **Candidate Elimination**:
   - Only 279 odd candidate branches $< 561$ are considered.
   - For all odd numbers $< 561$, each is either prime, divisible by a square, a product of two primes, or fails Korselt's divisibility condition $(p - 1) \mid (n - 1)$ for some prime factor $p \mid n$.

## Main Declarations

- `Nat.not_isCarmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ n.IsCarmichael`
- `Nat.isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n`
- `Nat.not_isCarmichael_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : ¬ (p * q).IsCarmichael`

## Quality Checks

- [x] Zero `sorry`, zero warnings.
- [x] Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`).
- [x] Lines $\le 100$ characters.
- [x] Passes all Mathlib linters (`#lint`).

---
<!-- Explicit LLM declaration per community guidelines -->
*Note: Parts of the formalization and proof search were generated and verified with assistance from an LLM.*

