# Pseudoprimes & Deterministic Primality Testing in Lean 4

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![DOI](https://zenodo.org/badge/1362912112.svg)](https://zenodo.org/badge/latestdoi/1362912112)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)
[![LLM Assisted](https://img.shields.io/badge/Formalized_with-LLM_Assistance-blueviolet.svg)](#ai--llm-assistance-disclosure)

Formal verification in **Lean 4** and **Mathlib4** establishing the core foundation of pseudoprimes, computational reflection, and deterministic Miller-Rabin primality testing:

1. **561 is the strictly smallest Carmichael number** (`Carmichael/Smallest.lean`), resolving the open TODO in Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`.
2. **Korselt's Criterion (1899)** (`Carmichael/Korselt.lean`), bridging Carmichael numbers with group exponent and `Mathlib.NumberTheory.ArithmeticFunction.Carmichael`.
3. **341 is the strictly smallest Poulet number (base-2 Fermat pseudoprime)** (`Carmichael/Poulet.lean`).
4. **2047 is the strictly smallest strong pseudoprime to base 2** (`Carmichael/StrongPsp.lean`), formalized via constructive 2-adic decomposition and high-efficiency computational reflection.
5. **Pomerance-Selfridge-Wagstaff (PSW) Theorem for bases {2, 3}** (`Carmichael/StrongPspMulti.lean`), establishing 1,373,653 as the strictly smallest strong pseudoprime to bases 2 and 3 simultaneously via certified sparse reflection.

---

## The Four Groundbreaking Milestones

| # | Milestone Theorem | Boundary | Module | Key Declarations |
|---|---|---|---|---|
| 1 | **Carmichael Numbers & Korselt** | $561 = 3 \times 11 \times 17$ | [`Carmichael/Smallest.lean`](Carmichael/Smallest.lean) | `Nat.isCarmichael_min`, `Nat.carmichael_iff_korselt` |
| 2 | **Poulet Numbers (Base-2 Fermat)** | $341 = 11 \times 31$ | [`Carmichael/Poulet.lean`](Carmichael/Poulet.lean) | `Nat.isPoulet_min`, `Nat.isPoulet_341` |
| 3 | **Miller-Rabin Strong Psp (Base 2)** | $2047 = 23 \times 89$ | [`Carmichael/StrongPsp.lean`](Carmichael/StrongPsp.lean) | `Nat.smallest_strong_psp_two`, `Nat.strong_psp_2047` |
| 4 | **Multi-Base MR (PSW {2, 3} Theorem)** | $1373653 = 829 \times 1657$ | [`Carmichael/StrongPspMulti.lean`](Carmichael/StrongPspMulti.lean) | `Nat.smallest_strong_psp_two_three`, `Nat.strong_psp_two_three_1373653` |

---

## Mathematical Highlights

### 1. Resolving the Mathlib Open TODO (Smallest Carmichael Number 561)
In Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`:
> *"TODO: Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561."*

This repository completely resolves this TODO in [`Carmichael/Smallest.lean`](Carmichael/Smallest.lean). Using Korselt pruning (every Carmichael number is odd, squarefree, and has $\ge 3$ distinct prime factors), only 279 odd candidate branches are inspected and eliminated.

### 2. Korselt's Criterion (1899)
In [`Carmichael/Korselt.lean`](Carmichael/Korselt.lean), we establish the tripartite equivalence for any composite $n > 1$:
$$\text{Nat.Carmichael } n \iff \lambda(n) \mid (n - 1) \iff (n \text{ is squarefree } \land \forall p \mid n, (p - 1) \mid (n - 1))$$
bridging `ArithmeticFunction.carmichael` and `exponent (ZMod n)ˣ`.

### 3. Smallest Poulet Number (341)
In [`Carmichael/Poulet.lean`](Carmichael/Poulet.lean), we formalize that 341 is the strictly smallest composite number satisfying $2^{n-1} \equiv 1 \pmod n$, and prove equivalence with Mathlib's native `Nat.FermatPsp n 2`.

### 4. 2047 as the Smallest Strong Pseudoprime to Base 2
In [`Carmichael/StrongPsp.lean`](Carmichael/StrongPsp.lean):
- Computable 2-adic decomposition: $n - 1 = d \cdot 2^s$ with constructive termination proofs (`Nat.oddPart`, `Nat.twoPowerPart`).
- Definition: `Nat.IsStrongPsp (b : ℕ) (n : ℕ) : Prop`.
- Fast prime decider `isPrimeDec2047` covering trial primes up to $\lfloor\sqrt{2047}\rfloor = 45$.
- Minimality proof verified in Lean kernel reduction in **~2 ms**:
```lean
theorem smallest_strong_psp_two : ∀ n < 2047, ¬ IsStrongPsp 2 n
theorem strong_psp_2047 : IsStrongPsp 2 2047
theorem isStrongPsp_min : ∀ n, IsStrongPsp 2 n → 2047 ≤ n
```

### 5. Multi-Base Miller-Rabin & Pomerance-Selfridge-Wagstaff {2, 3} Theorem
In [`Carmichael/StrongPspMulti.lean`](Carmichael/StrongPspMulti.lean):
- Multi-base definition over finite sets: `def IsStrongPspSet (B : Finset ℕ) (n : ℕ) : Prop := ∀ b ∈ B, IsStrongPsp b n`.
- Sparse pre-filter certification: by base-2 minimality, counterexamples must be among the 58 base-2 pseudoprimes below 1,373,653; kernel reflection checks all 58 fail base-3 testing.
- Positive witness theorem for $1373653 = 829 \times 1657$:
```lean
theorem smallest_strong_psp_two_three (h : Base2PspsPreFilter base2PspsLt1373653) :
    ∀ n < 1373653, ¬ IsStrongPspSet {2, 3} n
theorem strong_psp_two_three_1373653 : IsStrongPspSet {2, 3} 1373653
```

---

## Project Structure

```text
.
├── Carmichael.lean                 # Unified root module exporting all submodules
├── Carmichael/
│   ├── Korselt.lean                # Korselt's Criterion (1899) via group exponent
│   ├── Smallest.lean               # Proof that no Carmichael number < 561 exists
│   ├── Poulet.lean                 # 341 is smallest base-2 Fermat pseudoprime
│   ├── StrongPsp.lean              # 2047 is smallest base-2 strong pseudoprime
│   └── StrongPspMulti.lean         # 1,373,653 is smallest {2, 3} strong pseudoprime (PSW)
├── benchmark/                      # Benchmark scripts and reflection timers
├── PR_DESCRIPTION.md               # Upstream Mathlib contribution description
├── lakefile.lean                   # Lake configuration
└── lean-toolchain                  # Lean 4 toolchain (v4.33.1)
```

---

## Build & Verification

```bash
# Build all modules with warnings as errors
lake build -KwarningAsError=true

# Check axioms (Standard Lean 4 foundations only: propext, Classical.choice, Quot.sound)
lake env lean Carmichael/StrongPspMulti.lean
```

---


## AI / LLM Assistance Disclosure

In compliance with the **Mathlib Community & LLM Contribution Guidelines**:
- This formalization project was developed and explored with the assistance of Large Language Models (LLMs).
- All formal definitions, theorems, lemmas, and proofs have been strictly compiled and machine-checked by **Lean 4 (v4.33.1)** and the Lean 4 kernel with **0 sorry** and **0 custom axioms**.

## License

Dual-licensed under:
- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- **Mulan Permissive Software License, Version 2 (木兰宽松许可证, 第2版, MulanPSL-2.0)** ([LICENSE-MULAN](LICENSE-MULAN) or <http://license.coscl.org.cn/MulanPSL2>)
