# Formalization of Carmichael Numbers in Lean 4

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

A formalization of **Carmichael numbers** (absolute Fermat pseudoprimes) and the proof of the smallest counterexample $561$ in the Lean 4 proof assistant with Mathlib4.

*基于 Lean 4 与 Mathlib4 的卡迈克尔数（Carmichael numbers）严格形式化库，形式化证明最小卡迈克尔数反例 561。*

---

## Background & Motivation / 背景与动机

### English
By Fermat's Little Theorem, if $p$ is a prime number, then for every integer $b$ coprime to $p$,
$$b^{p-1} \equiv 1 \pmod p$$
Composite numbers that satisfy this congruence for a specific base $b$ are called **Fermat pseudoprimes** to base $b$. Composite numbers that satisfy this congruence for **all** bases $b$ coprime to $n$ are known as **Carmichael numbers** (or absolute Fermat pseudoprimes).

In Lean's mathematical library Mathlib4 (`Mathlib.NumberTheory.FermatPsp`), Fermat pseudoprimes are formalized, but Carmichael numbers were left undefined, with the explicit remark in the module documentation:
> *"Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet defined in this file)."*

This repository directly fills this open gap by:
1. Providing the formal mathematical definition `Nat.Carmichael`.
2. Formally proving that $561 = 3 \times 11 \times 17$ is a Carmichael number (`carmichael_561`), verified with zero axioms beyond the Lean 4 kernel foundations.

### 中文对照
根据费马小定理，若 $p$ 为素数，则对任意与 $p$ 互质的底数 $b$ 均有 $b^{p-1} \equiv 1 \pmod p$。若合数 $n$ 关于特定底数 $b$ 满足此同余式，则称 $n$ 为关于底数 $b$ 的费马伪素数；若合数 $n$ 对**所有**与其互质的底数 $b$ 均满足该同余式，则称 $n$ 为**卡迈克尔数**（Carmichael number，亦称绝对费马伪素数）。

Mathlib4 的 `Mathlib.NumberTheory.FermatPsp` 形式化了特定底数的费马伪素数，并在模块文档中明确留空说明：
> *“对所有底数均为费马伪素数的数称为卡迈克尔数（本文件中尚未定义）。”*

本项目补全了该定义空白，建立了 `Nat.Carmichael` 规范，并利用欧拉定理与同余整除性质严格机器验证了首个反例 $561 = 3 \times 11 \times 17$ 是卡迈克尔数。

---

## Formalized Results / 形式化成果

The main formalizations are located in [`Carmichael.lean`](Carmichael.lean):

### 1. Definitions / 核心定义
- **`Nat.ProbablePrime (b n : ℕ) : Prop`**  
  A natural number $n$ passes the Fermat primality test to base $b$ if $n \mid b^{n-1} - 1$.
- **`Nat.Carmichael (n : ℕ) : Prop`**  
  A composite number $n > 1$ such that for all $b$ coprime to $n$, $n$ is a probable prime to base $b$:
  ```lean
  def Carmichael (n : ℕ) : Prop :=
    ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime b n
  ```

### 2. Supporting Lemmas / 关键引理
- `factor_561 : 561 = 3 * 11 * 17` — Prime factorization of 561.
- `not_prime_561 : ¬ (561 : ℕ).Prime` — 561 is composite.
- `dvd_mod_three {b : ℕ} (h : b.Coprime 561) : 3 ∣ b ^ 560 - 1` — Prime factor divisibility for 3.
- `dvd_mod_eleven {b : ℕ} (h : b.Coprime 561) : 11 ∣ b ^ 560 - 1` — Prime factor divisibility for 11.
- `dvd_mod_seventeen {b : ℕ} (h : b.Coprime 561) : 17 ∣ b ^ 560 - 1` — Prime factor divisibility for 17.
- `dvd_561_of_prime_factors` — Divisibility combination for pairwise coprime factors $3 \times 11 \times 17 = 561$.

### 3. Main Theorem / 核心主定理
- **`theorem carmichael_561 : Carmichael 561`** (also accessible as `Nat.carmichael_561`):
  Formally establishes that 561 is a Carmichael number.

---

## Build & Verify Instructions / 构建与验证指南

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.33.1` (managed via [elan](https://github.com/leanprover/elan))
- Lake build system (bundled with Lean 4)

### 1. Build the Library / 编译项目
```bash
lake build
```

### 2. Strict Typecheck (Zero Warnings) / 严格零警告检查
```bash
lake env lean -D warningAsError=true Carmichael.lean
```

### 3. Verify Soundness & Axioms / 验证证明公理（无 sorry 检查）
To inspect the axioms used by `carmichael_561` and verify there are no hidden assumptions or `sorryAx`:

**Linux / macOS (Bash):**
```bash
printf "import Carmichael\n#print axioms carmichael_561\n" | lake env lean --stdin
```

**Windows (PowerShell):**
```powershell
@('import Carmichael', '#print axioms carmichael_561') | lake env lean --stdin
```

**Expected Output:**
```text
'Nat.carmichael_561' depends on axioms: [propext, Classical.choice, Quot.sound]
```
This confirms that the theorem is completely proved and relies solely on the standard Lean 4 kernel foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## CI / 持续集成

The repository includes a GitHub Actions continuous integration pipeline in [`.github/workflows/lean_build.yml`](.github/workflows/lean_build.yml) that automatically checks every push and pull request on Ubuntu:
1. Installs the exact toolchain via `elan`.
2. Fetches Mathlib pre-built cache via `lake exe cache get`.
3. Executes `lake build`.
4. Validates `Carmichael.lean` under `-D warningAsError=true`.
5. Inspects kernel axioms to ensure zero `sorryAx`.

---

## License / 开源许可证

This project is dual-licensed under either:

- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- **Mulan Permissive Software License, Version 2** ([LICENSE-MULAN](LICENSE-MULAN) or <http://license.coscl.org.cn/MulanPSL2>)

at your option.

本项目采用 **Apache-2.0** 与 **MulanPSL-2.0** 双许可证授权，用户可自由择一使用。
