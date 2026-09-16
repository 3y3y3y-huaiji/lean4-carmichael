# Mathlib4 Upstream PR Submission Roadmap

This document outlines the 4-stage pull request strategy to upstream the Carmichael and
pseudoprime formalization into Mathlib4. Each stage is self-contained, review-scoped, and
formatted according to Mathlib PR conventions.

---

## Staging Overview

- **Stage 1**: `Carmichael.Korselt`, `Carmichael.Smallest`
  - Target: `Mathlib.NumberTheory.Carmichael`
  - Milestone: Korselt's criterion & 561 minimality
- **Stage 2**: `Carmichael.Poulet`
  - Target: `Mathlib.NumberTheory.FermatPsp`
  - Milestone: Poulet numbers & 341 minimality
- **Stage 3**: `Carmichael.StrongPsp`
  - Target: `Mathlib.NumberTheory.StrongPsp`
  - Milestone: Base-2 strong pseudoprimes & 2047 minimality
- **Stage 4**: `Carmichael.StrongPspMulti`
  - Target: `Mathlib.NumberTheory.StrongPsp`
  - Milestone: Multi-base PSW {2, 3} & deterministic primality test

---

## Stage 1: Carmichael Numbers, Korselt's Criterion & 561 Minimality

### Upstream Branch
`upstream/carmichael-korselt-561`

### Target Files
- `Mathlib/NumberTheory/Carmichael.lean`
- `Mathlib/NumberTheory/Carmichael/Korselt.lean`
- `Mathlib/NumberTheory/Carmichael/Smallest.lean`

### PR Title
```text
feat(NumberTheory/Carmichael): formalize Korselt criterion and 561 minimality
```

### PR Description
```markdown
Addresses the open TODO in `Mathlib.NumberTheory.CarmichaelNumber`:
"Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561."

### Mathematical Changes
- Define `Nat.Korselt (n : ℕ) : Prop` characterizing squarefree integers whose prime divisors
  `p ∣ n` satisfy `(p - 1) ∣ (n - 1)`.
- Prove side-condition-free equivalence `carmichael_iff_korselt (n : ℕ)`:
  `Nat.Carmichael n ↔ 1 < n ∧ ¬ n.Prime ∧ Nat.Korselt n`.
- Implement verified decision procedure `korseltDec (n : ℕ) : Bool` via `korseltDec_iff`.
- Prove that 561 is the strictly smallest Carmichael number (`Nat.not_isCarmichael_of_lt_561`,
  `Nat.isCarmichael_min`), using computational reflection via `checkCarmichaelBound`.

### Main Declarations
- `Nat.Korselt`
- `Nat.carmichael_iff_korselt`
- `Nat.korseltDec`
- `Nat.not_isCarmichael_of_lt_561`
- `Nat.isCarmichael_min`

### LLM Disclosure
- [x] This PR was prepared with the assistance of an LLM. All proofs and statements have
  been formally verified by Lean 4 and checked for correctness.
```

---

## Stage 2: Poulet Numbers & 341 Minimality

### Upstream Branch
`upstream/poulet-341-minimality`

### Target Files
- `Mathlib/NumberTheory/FermatPsp.lean`
- `Mathlib/NumberTheory/Poulet.lean`

### PR Title
```text
feat(NumberTheory/FermatPsp): formalize Poulet numbers and 341 minimality
```

### PR Description
```markdown
Formalizes Poulet numbers (base-2 Fermat pseudoprimes) and proves 341 minimality.

### Mathematical Changes
- Define `Nat.IsPoulet (n : ℕ) : Prop := ¬ n.Prime ∧ 2 ≤ n ∧ 2^(n - 1) ≡ 1 [MOD n]`.
- Bridge with Mathlib native definition: `isPoulet_iff_fermatPsp : IsPoulet n ↔ Nat.FermatPsp n 2`.
- Prove hierarchy inclusion: `isPoulet_of_isCarmichael : Nat.IsCarmichael n → Nat.IsPoulet n`.
- Verify positive witness `isPoulet_341 : IsPoulet 341` and `fermatPsp_two_341`.
- Prove 341 is the strictly smallest Poulet number (`not_isPoulet_of_lt_341`, `isPoulet_min`).

### Main Declarations
- `Nat.IsPoulet`
- `Nat.isPoulet_iff_fermatPsp`
- `Nat.isPoulet_of_isCarmichael`
- `Nat.isPoulet_341`
- `Nat.not_isPoulet_of_lt_341`
- `Nat.isPoulet_min`

### LLM Disclosure
- [x] This PR was prepared with the assistance of an LLM. All proofs and statements have
  been formally verified by Lean 4 and checked for correctness.
```

---

## Stage 3: Base-2 Strong Pseudoprimes & 2047 Minimality

### Upstream Branch
`upstream/strong-psp-2047-minimality`

### Target Files
- `Mathlib/NumberTheory/StrongPsp.lean`

### PR Title
```text
feat(NumberTheory/StrongPsp): formalize base-2 strong pseudoprimes and 2047 minimality
```

### PR Description
```markdown
Formalizes Miller-Rabin strong pseudoprimes to base 2 and proves 2047 minimality.

### Mathematical Changes
- Implement constructive 2-adic decomposition `oddPart (n : ℕ)` and `twoPowerPart (n : ℕ)`
  satisfying `d * 2^s = n - 1` with `d` odd.
- Define `Nat.MillerRabinCond (b : ℕ) (n : ℕ) : Prop` and decider `Nat.millerRabinPass`.
- Define `Nat.IsStrongPsp (b : ℕ) (n : ℕ) : Prop` and decider `Nat.isStrongPspDec`.
- Prove hierarchy theorem: `isPoulet_of_isStrongPsp_two : IsStrongPsp 2 n → IsPoulet n`.
- Verify positive witness `strong_psp_2047 : IsStrongPsp 2 2047` via 2047 = 23 * 89.
- Prove 2047 is the strictly smallest base-2 strong pseudoprime (`smallest_strong_psp_two`,
  `isStrongPsp_min`).

### Main Declarations
- `Nat.oddPart`, `Nat.twoPowerPart`
- `Nat.MillerRabinCond`, `Nat.millerRabinPass`
- `Nat.IsStrongPsp`
- `Nat.isPoulet_of_isStrongPsp_two`
- `Nat.strong_psp_2047`
- `Nat.smallest_strong_psp_two`
- `Nat.isStrongPsp_min`

### LLM Disclosure
- [x] This PR was prepared with the assistance of an LLM. All proofs and statements have
  been formally verified by Lean 4 and checked for correctness.
```

---

## Stage 4: Multi-Base Strong Pseudoprimes & PSW 1,373,653 Theorem

### Upstream Branch
`upstream/strong-psp-multi-psw-1373653`

### Target Files
- `Mathlib/NumberTheory/StrongPspMulti.lean`

### PR Title
```text
feat(NumberTheory/StrongPsp): formalize PSW theorem for bases 2 and 3 and primality decider
```

### PR Description
```markdown
Formalizes multi-base Miller-Rabin pseudoprimes and the Pomerance-Selfridge-Wagstaff theorem.

### Mathematical Changes
- Define multi-base predicate `Nat.IsStrongPspSet (B : Finset ℕ) (n : ℕ) : Prop`.
- Implement computable multi-base test `Nat.millerRabinPassList (bases : List ℕ) (n : ℕ) : Bool`.
- Formally establish the PSW threshold theorem: 1,373,653 is the strictly smallest strong
  pseudoprime to bases {2, 3} (`strong_psp_two_three_1373653`, `isStrongPspSet_two_three_min`).
- Implement deterministic primality decider `isPrimeFast1373653` with certified equivalence
  `isPrimeFast1373653_iff : isPrimeFast1373653 n = true ↔ Nat.Prime n` for `n < 1373653`.
- Define industrial standard base set `bases64 : List ℕ := [2, 3, 5, 7, 11, 13, 17]` and
  `isPrimeU64`.

### Main Declarations
- `Nat.IsStrongPspSet`
- `Nat.millerRabinPassList`
- `Nat.strong_psp_two_three_1373653`
- `Nat.isStrongPspSet_two_three_min`
- `Nat.isPrimeFast1373653`
- `Nat.isPrimeFast1373653_iff`
- `Nat.bases64`, `Nat.isPrimeU64`

### LLM Disclosure
- [x] This PR was prepared with the assistance of an LLM. All proofs and statements have
  been formally verified by Lean 4 and checked for correctness.
```

---

## Review & Merge Guidelines

1. **Review Order**: Merge Stage 1 first to establish `Nat.Korselt`. Stage 2 and Stage 3 depend
   on the hierarchy structures. Stage 4 completes the multi-base PSW foundations.
2. **Hygiene Standards**:
   - Zero `sorry`, zero warnings under `-KwarningAsError=true`.
   - Line length strictly `<= 100` characters.
   - All standard Mathlib linters (`#lint`) clean.
   - Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`).
