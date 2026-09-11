# Smallest Carmichael Number (561) & Korselt's Criterion in Lean 4

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![DOI](https://zenodo.org/badge/1362912112.svg)](https://zenodo.org/badge/latestdoi/1362912112)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

Formal verification in **Lean 4** and **Mathlib4** establishing:
1. **561 is the strictly smallest Carmichael number** (`Nat.isCarmichael_min`, `Nat.not_isCarmichael_of_lt_561`), resolving the open TODO in Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`.
2. **Korselt's Criterion (1899)** (`Nat.carmichael_iff_korselt`), bridging Carmichael numbers with group exponent and `Mathlib.NumberTheory.ArithmeticFunction.Carmichael`.

---

## Key Mathematical Highlights

### 1. Resolving the Mathlib Upstream Open TODO (Smallest Carmichael Number)
In Mathlib's `Mathlib.NumberTheory.CarmichaelNumber`, the module documentation explicitly states:
> *"TODO: Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561."*

This repository completely resolves this TODO in [`Carmichael/Smallest.lean`](Carmichael/Smallest.lean) with high computational efficiency:
- **Pruning theorems**:
  - `IsCarmichael.odd`: every Carmichael number is odd.
  - `not_isCarmichael_mul_primes`: no product of two distinct primes ($p \times q$) can be a Carmichael number.
  - Square non-divisibility: if $p^2 \mid n$, $n$ violates squarefreeness and cannot be Carmichael.
- **Fast candidate elimination**: Only 279 odd candidate branches $< 561$ need to be checked, verified in **~17 seconds** locally on a single core without running into heartbeat limits.

```lean
/-- No natural number strictly less than 561 is a Carmichael number. -/
theorem not_isCarmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ n.IsCarmichael

/-- 561 is the minimal Carmichael number. -/
theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n

/-- Compatibility corollaries for Nat.Carmichael -/
theorem not_carmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ Nat.Carmichael n
theorem carmichael_min {n : ℕ} (hn : Nat.Carmichael n) : 561 ≤ n
```

---

### 2. Korselt's Criterion (1899) via Group Exponent
In [`Carmichael/Korselt.lean`](Carmichael/Korselt.lean), we establish the tripartite equivalence for any composite $n > 1$:
$$\text{Nat.Carmichael } n \iff \lambda(n) \mid (n - 1) \iff (n \text{ is squarefree } \land \forall p \mid n, (p - 1) \mid (n - 1))$$

leveraging Mathlib's `ArithmeticFunction.carmichael` ($\lambda$ function) and `exponent (ZMod n)ˣ`:

```lean
/-- Step 1: Nat.Carmichael n ↔ carmichael n ∣ n - 1 -/
theorem carmichael_iff_carmichael_dvd (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ ArithmeticFunction.carmichael n ∣ n - 1

/-- Step 2: carmichael n ∣ n - 1 ↔ Korselt's condition -/
theorem carmichael_dvd_iff_korselt (n : ℕ) (hn : 1 < n) :
    ArithmeticFunction.carmichael n ∣ n - 1 ↔
    Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- Step 3 (Main Theorem: Korselt's Criterion) -/
theorem carmichael_iff_korselt (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)
```

---

### 3. Basic Definition & Verification Baseline
Located in [`Carmichael.lean`](Carmichael.lean):
- Standard definition `Nat.Carmichael (n : ℕ) : Prop` based on `Mathlib.NumberTheory.FermatPsp.ProbablePrime`.
- Elementary proof that 561 is Carmichael (`carmichael_561`).
- Elementary sanity counterexample that 9 is not Carmichael (`not_carmichael_nine`).

---

## Project Structure

```text
.
├── Carmichael.lean           # Baseline definition, 561 positive witness, 9 counterexample
├── Carmichael/
│   ├── Korselt.lean          # Korselt's Criterion (1899) via group exponent & ArithmeticFunction.carmichael
│   └── Smallest.lean         # Proof that no Carmichael number < 561 exists (resolving Mathlib TODO)
├── PR_DESCRIPTION.md         # Upstream Mathlib contribution description
├── lakefile.toml             # Lake configuration
└── lean-toolchain            # Lean 4 toolchain (v4.33.1)
```

---

## Build & Verification Instructions

### 1. Build all targets
```bash
lake build
```

### 2. Measure compile time of 561 minimality proof (~17s)
```powershell
Measure-Command { lake env lean Carmichael/Smallest.lean }
```

### 3. Check axioms (0 non-standard axioms)
```bash
lake env lean -D warningAsError=true Carmichael/Smallest.lean
```
All declarations depend strictly on standard Lean 4 foundational axioms: `[propext, Classical.choice, Quot.sound]`, with zero `sorry`.

---

## License

Dual-licensed under:
- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- **Mulan Permissive Software License, Version 2 (木兰宽松许可证, 第2版, MulanPSL-2.0)** ([LICENSE-MULAN](LICENSE-MULAN) or <http://license.coscl.org.cn/MulanPSL2>)

