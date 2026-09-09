# Lean 4 卡迈克尔数形式化验证库

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

本项目在交互式定理证明器 **Lean 4** 与数学库 **Mathlib4** 中，完成了**卡迈克尔数（Carmichael numbers，绝对费马伪素数）**的形式化定义，并严格机器验证了首个经典反例 **561** 是卡迈克尔数。

---

## 背景与动机

根据费马小定理，若 $p$ 为素数，则对任意与 $p$ 互质的底数 $b$ 均满足：
$$b^{p-1} \equiv 1 \pmod p$$

在数论中，某些合数对于特定底数也会满足上述同余关系，这类数被称为关于底数 $b$ 的**费马可能素数（Fermat Probable Prime）**或**费马伪素数（Fermat Pseudoprime）**。而若一个合数 $n$ 对于**所有**与其互质的底数 $b$ 均能通过费马素性测试，则称 $n$ 为**卡迈克尔数（Carmichael number）**。

在 Lean 4 官方数学库 Mathlib4 的 `Mathlib.NumberTheory.FermatPsp` 模块中，已经形式化了针对特定底数的费马伪素数，但在模块文档中明确留空指出：
> *“Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet defined in this file).”*  
> （对所有底数均为费马伪素数的数称为卡迈克尔数，本文件中尚未定义。）

本项目正式填补了 Mathlib4 的这一空白：
1. 给出了符合 Mathlib 社区规范的标准卡迈克尔数定义 `Nat.Carmichael`；
2. 构造了完整的引理链条，严格形式化证明了 $561 = 3 \times 11 \times 17$ 是卡迈克尔数（`carmichael_561`）；
3. 证明完全闭环，不依赖任何除 Lean 4 内核三大基础公理之外的公理或 `sorry`。

---

## 形式化成果

所有核心代码均位于 [`Carmichael.lean`](Carmichael.lean)：

### 1. 核心定义
- **`Nat.ProbablePrime (b n : ℕ) : Prop`**  
  自然数 $n$ 关于底数 $b$ 的费马可能素数测试条件，精确定义为 $n \mid b^{n-1} - 1$。
- **`Nat.Carmichael (n : ℕ) : Prop`**  
  大于 1 的合数 $n$，且对任意与其互质的底数 $b$，均满足可能素数条件：
  ```lean
  def Carmichael (n : ℕ) : Prop :=
    ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime b n
  ```

### 2. 辅助引理
- `factor_561 : 561 = 3 * 11 * 17`：561 的素因数分解。
- `not_prime_561 : ¬ (561 : ℕ).Prime`：561 是合数而非素数。
- `dvd_mod_three`：若 $\gcd(b, 561) = 1$，则 $3 \mid b^{560} - 1$。
- `dvd_mod_eleven`：若 $\gcd(b, 561) = 1$，则 $11 \mid b^{560} - 1$。
- `dvd_mod_seventeen`：若 $\gcd(b, 561) = 1$，则 $17 \mid b^{560} - 1$。
- `dvd_561_of_prime_factors`：利用两两互质素因子的整除性合并定理，由模 3、11、17 同余整除导出 $561 \mid b^{560} - 1$。

### 3. 主定理
- **`theorem carmichael_561 : Carmichael 561`**（亦导出为 `Nat.carmichael_561`）：  
  正式确立 561 是卡迈克尔数。

---

## 本地构建与复现指南

### 环境准备
- Lean 4 编译器版本：`leanprover/lean4:v4.33.1`（建议通过 [elan](https://github.com/leanprover/elan) 安装管理）
- Lake 构建系统（Lean 4 自带）

### 1. 编译项目
```bash
lake build
```

### 2. 严格零警告类型检查
```bash
lake env lean -D warningAsError=true Carmichael.lean
```

### 3. 独立检验内核公理（验证证明无 sorry / 无作弊公理）
可在终端中直接查询 Lean 4 内核，确认 `carmichael_561` 依赖的公理列表：

**Linux / macOS (Bash):**
```bash
printf "import Carmichael\n#print axioms carmichael_561\n" | lake env lean --stdin
```

**Windows (PowerShell):**
```powershell
@('import Carmichael', '#print axioms carmichael_561') | lake env lean --stdin
```

**预期输出：**
```text
'Nat.carmichael_561' depends on axioms: [propext, Classical.choice, Quot.sound]
```
输出仅包含 Lean 4 官方内核三大标准逻辑公理（命题外延性、选择公理、商类型健全性），**无 `sorryAx`，无任何自定义公理**，证明绝对严密。

---

## 持续集成 (CI)

仓库已配置标准的 GitHub Actions 流水线 [`.github/workflows/lean_build.yml`](.github/workflows/lean_build.yml)，在 Ubuntu 环境下对每次提交进行自动构建与公理检验：
1. 基于 `elan` 自动配置指定版本工具链；
2. 拉取 Mathlib 预编译缓存；
3. 执行 `lake build`；
4. 开启 `-D warningAsError=true` 进行严格无警告语法检查；
5. 自动断言内核公理依赖，确保构建与证明真实性。

---

## 开源许可证 (License)

本项目采用**双许可证（Dual License）**模式发布，用户可在以下两项许可协议中自由选择：

- **Apache License 2.0**（参见 [LICENSE-APACHE](LICENSE-APACHE)）
- **木兰宽松许可证 第2版（MulanPSL-2.0）**（参见 [LICENSE-MULAN](LICENSE-MULAN)）

双许可架构既完全兼容国际 Mathlib 上游生态，又符合国内开源法律与版权合规要求。
