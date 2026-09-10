# Formalization of Carmichael Numbers in Lean 4 (Mathlib4 Upstream Ready)

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

A formalization of **Carmichael numbers** (absolute Fermat pseudoprimes) and machine-checked verification of the first positive witness $561$ as well as a negative sanity check $9$ in **Lean 4** with **Mathlib4**, structured for direct upstream integration.

---

## Background & Motivation

By Fermat's Little Theorem, if $p$ is a prime number, then for every integer $b$ coprime to $p$,
$$b^{p-1} \equiv 1 \pmod p$$

Composite numbers that satisfy this congruence for a specific base $b$ are called **Fermat probable primes** or **Fermat pseudoprimes** to base $b$. Composite numbers that satisfy this congruence for **all** bases $b$ coprime to $n$ are known as **Carmichael numbers** (or absolute Fermat pseudoprimes).

In Mathlib4 (`Mathlib.NumberTheory.FermatPsp`), Fermat pseudoprimes are formalized, but Carmichael numbers were left undefined, with the explicit remark in the module documentation:
> *"Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet defined in this file)."*

This repository directly addresses that gap by:
1. Natively importing `Mathlib.NumberTheory.FermatPsp` and utilizing official `Nat.ProbablePrime (n b : ℕ)`.
2. Providing the canonical mathematical definition `Nat.Carmichael` with dot-notation extractors.
3. Formally proving that $561 = 3 \times 11 \times 17$ is a Carmichael number (`carmichael_561`), verified with zero axioms beyond the Lean 4 kernel foundations.
4. Formally proving that $9$ is not a Carmichael number (`not_carmichael_nine`), verifying soundness.

---

## Formalized Results

The main formalizations are located in [`Carmichael.lean`](Carmichael.lean):

### 1. Definition & Dot-Notation Extractors
- **`Nat.Carmichael (n : ℕ) : Prop`**  
  A composite number $n > 1$ such that for all $b$ coprime to $n$, $n$ is a Fermat probable prime to base $b$:
  ```lean
  def Carmichael (n : ℕ) : Prop :=
    ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime n b
  ```
- **Dot-Notation Extractors:**
  - `lemma Carmichael.not_prime {n : ℕ} (h : Carmichael n) : ¬ n.Prime`
  - `lemma Carmichael.one_lt {n : ℕ} (h : Carmichael n) : 1 < n`
  - `lemma Carmichael.probablePrime {n : ℕ} (h : Carmichael n) {b : ℕ} (hb : b.Coprime n) : ProbablePrime n b`

### 2. Supporting Lemmas
- `factor_561 : 561 = 3 * 11 * 17` — Prime factorization of 561.
- `not_prime_561 : ¬ (561 : ℕ).Prime` — 561 is composite.
- `dvd_mod_three {b : ℕ} (h : b.Coprime 561) : 3 ∣ b ^ 560 - 1` — Prime factor divisibility for 3.
- `dvd_mod_eleven {b : ℕ} (h : b.Coprime 561) : 11 ∣ b ^ 560 - 1` — Prime factor divisibility for 11.
- `dvd_mod_seventeen {b : ℕ} (h : b.Coprime 561) : 17 ∣ b ^ 560 - 1` — Prime factor divisibility for 17.
- `dvd_561_of_prime_factors` — Divisibility combination for pairwise coprime factors $3 \times 11 \times 17 = 561$.

### 3. Main Theorems
- **Positive Witness**:
  ```lean
  theorem carmichael_561 : Carmichael 561
  ```
  Formally establishes that 561 is a Carmichael number.
- **Negative Sanity Check**:
  ```lean
  theorem not_carmichael_nine : ¬ Carmichael 9
  ```
  Formally establishes that 9 fails the Fermat test for base $b = 2$ ($\gcd(2, 9) = 1$ but $9 \nmid 2^8 - 1$).

---

## Build & Verify Instructions

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.33.1` (managed via [elan](https://github.com/leanprover/elan))
- Lake build system (bundled with Lean 4)

### 1. Build the Library
```bash
lake build
```

### 2. Strict Typecheck & Lint (Zero Warnings)
```bash
lake env lean -D warningAsError=true Carmichael.lean
```

### 3. Verify Soundness & Axioms (No Sorry / No Cheating Axioms)
To inspect the axioms used by `carmichael_561` and `not_carmichael_nine`:

**Windows (PowerShell):**
```powershell
lake env lean -D warningAsError=true Carmichael.lean
```

**Expected Output:**
```text
'Nat.carmichael_561' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.not_carmichael_nine' depends on axioms: [propext]
-- Found 0 errors in 12 declarations (plus 0 automatically generated ones) in the current file with 14 linters
-- All linting checks passed!
```

---

## Mathlib4 Upstream Pull Request

See [PR_DESCRIPTION.md](PR_DESCRIPTION.md) for the upstream Pull Request draft conforming to Mathlib4 review standards.

---

## License

This project is dual-licensed under either:

- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- **Mulan Permissive Software License, Version 2** ([LICENSE-MULAN](LICENSE-MULAN) or <http://license.coscl.org.cn/MulanPSL2>)

at your option.
