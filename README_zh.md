# 最小卡迈克尔数（561）极小性定理与科瑟尔特准则的 Lean 4 形式化验证

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![DOI](https://zenodo.org/badge/1362912112.svg)](https://zenodo.org/badge/latestdoi/1362912112)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

本项目基于交互式定理证明器 **Lean 4** 与官方数学库 **Mathlib4**，完成了以下核心形式化成果：
1. **严格形式化证明 561 是最小的卡迈克尔数**（`Nat.isCarmichael_min`、`Nat.not_isCarmichael_of_lt_561`），直接攻克并闭环了 Mathlib 官方 `Mathlib.NumberTheory.CarmichaelNumber` 模块中悬挂的 TODO。
2. **科瑟尔特准则（Korselt's Criterion 1899）机器证明**（`Nat.carmichael_iff_korselt`），将卡迈克尔数与群指数理论及 Mathlib 的 `Mathlib.NumberTheory.ArithmeticFunction.Carmichael` 正式桥接。

---

## 核心数学成果

### 1. 攻克 Mathlib 官方开放 TODO（最小卡迈克尔数）
在 Mathlib 官方模块 `Mathlib.NumberTheory.CarmichaelNumber` 的模块文档中，明确留下了待办说明：
> *"TODO: Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561."*  
> （TODO：以高效计算的方式证明不存在小于 561 的卡迈克尔数。）

本项目在 [`Carmichael/Smallest.lean`](Carmichael/Smallest.lean) 中完全证明了该猜想/定理，并保证极高的计算效率：
- **数论剪枝定理**：
  - `IsCarmichael.odd`：证明卡迈克尔数必为奇数；
  - `not_isCarmichael_mul_primes`：严格证明任意半素数（两不同素数之积 $p \times q$）绝不可能为卡迈克尔数；
  - 平方因子整除判定：若 $p^2 \mid n$，则破坏无平方因子性，不可能为卡迈克尔数。
- **高效候选消除**：对于 $< 561$ 的所有奇数，仅需排查 279 种奇数候选分支。在单核环境下，仅需 **~17 秒** 即可完成全部 Lean 4 内核类型检查，绝不触发 heartbeat 超时或深度递归溢出。

```lean
/-- 严格证明小于 561 的自然数中不存在卡迈克尔数 -/
theorem not_isCarmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ n.IsCarmichael

/-- 严格证明 561 是最小的卡迈克尔数 -/
theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n

/-- 面向 Nat.Carmichael 的等价推论 -/
theorem not_carmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ Nat.Carmichael n
theorem carmichael_min {n : ℕ} (hn : Nat.Carmichael n) : 561 ≤ n
```

---

### 2. 科瑟尔特准则（Korselt's Criterion 1899）
位于 [`Carmichael/Korselt.lean`](Carmichael/Korselt.lean)，对任意大于 1 的合数 $n$，证明了三者等价：
$$\text{Nat.Carmichael } n \iff \lambda(n) \mid (n - 1) \iff (n \text{ 无平方因子 } \land \forall p \mid n, (p - 1) \mid (n - 1))$$

全面桥接了 Mathlib 的卡迈克尔函数 `ArithmeticFunction.carmichael` 与群单位元指数 `exponent (ZMod n)ˣ`：

```lean
/-- 第一步：Nat.Carmichael n ↔ carmichael n ∣ n - 1 -/
theorem carmichael_iff_carmichael_dvd (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ ArithmeticFunction.carmichael n ∣ n - 1

/-- 第二步：carmichael n ∣ n - 1 ↔ 科瑟尔特条件 -/
theorem carmichael_dvd_iff_korselt (n : ℕ) (hn : 1 < n) :
    ArithmeticFunction.carmichael n ∣ n - 1 ↔
    Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- 第三步（主定理：科瑟尔特准则） -/
theorem carmichael_iff_korselt (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)
```

---

### 3. 基础定义与健全性检验基线
位于 [`Carmichael.lean`](Carmichael.lean)：
- 基于 `Mathlib.NumberTheory.FermatPsp.ProbablePrime` 的标准定义 `Nat.Carmichael`；
- 初等证明 561 为卡迈克尔数（`carmichael_561`）；
- 负向健全性反例证明 9 不是卡迈克尔数（`not_carmichael_nine`）。

---

## 项目目录结构

```text
.
├── Carmichael.lean           # 基础定义、561 正向非空实例与 9 负向反例
├── Carmichael/
│   ├── Korselt.lean          # 科瑟尔特准则（基于群指数与 ArithmeticFunction.carmichael）
│   └── Smallest.lean         # 攻克 Mathlib 官方 TODO：证明小于 561 无卡迈克尔数
├── benchmark/                # 严格强制求值性能基准实测（561反射耗时仅 ~226 微秒，筛法支持至 10 万）
├── PR_DESCRIPTION.md         # 针对 Mathlib4 的贡献说明草稿
├── lakefile.toml             # Lake 配置文件
└── lean-toolchain            # Lean 4 工具链版本 (v4.33.1)
```

---

## 本地构建与复现指南

### 1. 编译全部目标
```bash
lake build
```

### 2. 运行严格强制求值性能实测（561 判定仅约 0.22 毫秒）
```bash
lake env lean --run benchmark/StrictBench.lean
```
或直接运行 PowerShell 测试脚本：
```powershell
pwsh ./benchmark/run_benchmark_zh.ps1
```

### 3. 检查内核公理（零非标准公理、零 sorry）
```bash
lake env lean -D warningAsError=true Carmichael/Smallest.lean
```
所有定理均仅依赖 Lean 4 核心标准公理：`[propext, Classical.choice, Quot.sound]`。

---

## 开源许可证 (License)

本项目采用**双许可证（Dual License）**模式发布：
- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE) 或 <https://www.apache.org/licenses/LICENSE-2.0>)
- **木兰宽松许可证 第2版 (Mulan Permissive Software License, Version 2 / MulanPSL-2.0)** ([LICENSE-MULAN](LICENSE-MULAN) 或 <http://license.coscl.org.cn/MulanPSL2>)

