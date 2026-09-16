Resolves the open TODO in `Mathlib.NumberTheory.CarmichaelNumber`:
> *"TODO: Prove (in a computationally efficient manner) that there are no Carmichael numbers
> less than 561."*

### Mathematical Summary

We formally establish that 561 is the strictly smallest Carmichael number, proving that
there are no Carmichael numbers strictly less than 561:

- Defines `Nat.Korselt (n : ℕ) : Prop` characterizing squarefree integers whose prime divisors
  `p ∣ n` satisfy `(p - 1) ∣ (n - 1)`.
- Establishes side-condition-free equivalence `carmichael_iff_korselt (n : ℕ)`:
  `Nat.Carmichael n ↔ 1 < n ∧ ¬ n.Prime ∧ Nat.Korselt n`.
- Verifies that 561 is the strictly smallest Carmichael number (`Nat.isCarmichael_min`)
  via candidate elimination in ~17 seconds.

### Main Declarations

- `Nat.Korselt`
- `Nat.carmichael_iff_korselt`
- `Nat.korseltDec`
- `Nat.not_isCarmichael_of_lt_561`
- `Nat.isCarmichael_min`

### Acknowledgments

We thank Felix Pernegger for suggesting the characterization via `ArithmeticFunction.carmichael`,
and for helpful discussions on Lean 4 formalization style and proof simplification.

---

### LLM Disclosure
- [x] This PR was prepared with the assistance of an LLM. All proofs and statements have been formally verified by Lean 4 and checked for correctness.


