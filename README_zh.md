# Lean 4 卡迈克尔数形式化验证库（Mathlib4 官方合入标准）

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

本项目在交互式定理证明器 **Lean 4** 与数学库 **Mathlib4** 中，完成了**卡迈克尔数（Carmichael numbers，绝对费马伪素数）**的原生形式化定义，并严格机器验证了正向首例 **561** 是卡迈克尔数，以及负向健全性反例 **9** 不是卡迈克尔数，完全对齐 Mathlib4 官方 PR 标准。

---

## 背景与动机

根据费马小定理，若 $p$ 为素数，则对任意与 $p$ 互质的底数 $b$ 均满足：
$$b^{p-1} \equiv 1 \pmod p$$

在数论中，某些合数对于特定底数也会满足上述同余关系，这类数被称为关于底数 $b$ 的**费马可能素数（Fermat Probable Prime）**或**费马伪素数（Fermat Pseudoprime）**。而若一个合数 $n$ 对于**所有**与其互质的底数 $b$ 均能通过费马素性测试，则称 $n$ 为**卡迈克尔数（Carmichael number）**。

在 Lean 4 官方数学库 Mathlib4 的 `Mathlib.NumberTheory.FermatPsp` 模块中，已经形式化了针对特定底数的费马伪素数，但在模块文档中明确留空指出：
> *“Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet defined in this file).”*  
> （对所有底数均为费马伪素数的数称为卡迈克尔数，本文件中尚未定义。）

本项目正式填补了 Mathlib4 的这一空白：
1. 直接复用官方原生 `Mathlib.NumberTheory.FermatPsp.ProbablePrime (n b : ℕ)`，不重复造轮子；
2. 给出标准卡迈克尔数定义 `Nat.Carmichael` 及点号表示法 API 提取器；
3. 严格形式化证明了 $561 = 3 \times 11 \times 17$ 是卡迈克尔数（`carmichael_561`，正向非空性验证）；
4. 严格形式化证明了 $9$ 不是卡迈克尔数（`not_carmichael_nine`，负向健全性反例）；
5. 证明完全闭环，零 `sorry`，且通过全部 14 项 Mathlib `#lint` 检查。

---

## 形式化成果

所有核心代码均位于 [`Carmichael.lean`](Carmichael.lean)：

### 1. 核心定义与 API 提取器
- **`Nat.Carmichael (n : ℕ) : Prop`**  
  大于 1 的合数 $n$，且对任意与其互质的底数 $b$，均满足费马可能素数条件：
  ```lean
  def Carmichael (n : ℕ) : Prop :=
    ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime n b
  ```
- **点号表示法提取器：**
  - `lemma Carmichael.not_prime {n : ℕ} (h : Carmichael n) : ¬ n.Prime`
  - `lemma Carmichael.one_lt {n : ℕ} (h : Carmichael n) : 1 < n`
  - `lemma Carmichael.probablePrime {n : ℕ} (h : Carmichael n) {b : ℕ} (hb : b.Coprime n) : ProbablePrime n b`

### 2. 辅助引理
- `factor_561 : 561 = 3 * 11 * 17`：561 的素因数分解。
- `not_prime_561 : ¬ (561 : ℕ).Prime`：561 是合数而非素数。
- `dvd_mod_three`：若 $\gcd(b, 561) = 1$，则 $3 \mid b^{560} - 1$。
- `dvd_mod_eleven`：若 $\gcd(b, 561) = 1$，则 $11 \mid b^{560} - 1$。
- `dvd_mod_seventeen`：若 $\gcd(b, 561) = 1$，则 $17 \mid b^{560} - 1$。
- `dvd_561_of_prime_factors`：由模 3、11、17 同余整除导出 $561 \mid b^{560} - 1$。

### 3. 主定理
- **正向非空性实例**：
  ```lean
  theorem carmichael_561 : Carmichael 561
  ```
  证明 561 是卡迈克尔数。
- **负向健全性反例**：
  ```lean
  theorem not_carmichael_nine : ¬ Carmichael 9
  ```
  证明 9 不是卡迈克尔数（取底数 $b = 2$，$\gcd(2, 9) = 1$ 但 $9 \nmid 2^8 - 1$）。

---

## 本地构建与复现指南

### 环境准备
- Lean 4 编译器版本：`leanprover/lean4:v4.33.1`（建议通过 [elan](https://github.com/leanprover/elan) 安装管理）
- Lake 构建系统（Lean 4 自带）

### 1. 编译项目
```bash
lake build
```

### 2. 严格零警告类型检查与 Linter 检验
```bash
lake env lean -D warningAsError=true Carmichael.lean
```

### 3. 检验内核公理（验证证明无 sorry / 无作弊公理）
```powershell
lake env lean -D warningAsError=true Carmichael.lean
```

**预期输出：**
```text
'Nat.carmichael_561' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.not_carmichael_nine' depends on axioms: [propext]
-- Found 0 errors in 12 declarations (plus 0 automatically generated ones) in the current file with 14 linters
-- All linting checks passed!
```

---

## Mathlib4 官方 PR 描述草稿

详见 [PR_DESCRIPTION.md](PR_DESCRIPTION.md)。

---

## 开源许可证 (License)

本项目采用**双许可证（Dual License）**模式发布，用户可在以下两项许可协议中自由选择：

- **Apache License 2.0**（参见 [LICENSE-APACHE](LICENSE-APACHE)）
- **木兰宽松许可证 第2版（MulanPSL-2.0）**（参见 [LICENSE-MULAN](LICENSE-MULAN)）
