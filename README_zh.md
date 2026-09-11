# 形式化数论伪素数体系与确定性素数检验 (Lean 4)

[English](README.md) | [简体中文](README_zh.md)

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/lean4-carmichael/actions/workflows/lean_build.yml)
[![DOI](https://zenodo.org/badge/1362912112.svg)](https://zenodo.org/badge/latestdoi/1362912112)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.33.1-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

本项目基于交互式定理证明器 **Lean 4** 与官方数学库 **Mathlib4**，构建了一套完整的数论伪素数体系、计算反射架构及确定性米勒-拉宾（Miller-Rabin）素数检验形式化基石：

1. **561 是最小卡迈克尔数极小性大定理**（`Carmichael/Smallest.lean`），彻底攻克 Mathlib 官方 `Mathlib.NumberTheory.CarmichaelNumber` 悬挂的开放 TODO。
2. **科瑟尔特准则（Korselt's Criterion 1899）机器证明**（`Carmichael/Korselt.lean`），桥接卡迈克尔数与群指数及 Mathlib 卡迈克尔函数。
3. **341 是以 2 为底最小费马伪素数（Poulet 数）定理**（`Carmichael/Poulet.lean`）。
4. **2047 是以 2 为底最小强伪素数大定理**（`Carmichael/StrongPsp.lean`），通过构造性 2-adic 分解与毫秒级计算反射实现。
5. **双底数 {2, 3} Pomerance-Selfridge-Wagstaff (PSW) 大定理**（`Carmichael/StrongPspMulti.lean`），形式化证明 1,373,653 是以 2 和 3 为底的最小强伪素数，采用稀疏证书反射，杜绝内核暴力遍历。

---

## 四大里程碑成果一览

| # | 里程碑定理 | 极小性分界 | 核心模块 | 核心定理声明 |
|---|---|---|---|---|
| 1 | **卡迈克尔数与 Korselt 准则** | $561 = 3 \times 11 \times 17$ | [`Carmichael/Smallest.lean`](Carmichael/Smallest.lean) | `Nat.isCarmichael_min`, `Nat.carmichael_iff_korselt` |
| 2 | **Poulet 数（以 2 为底费马伪素数）** | $341 = 11 \times 31$ | [`Carmichael/Poulet.lean`](Carmichael/Poulet.lean) | `Nat.isPoulet_min`, `Nat.isPoulet_341` |
| 3 | **米勒-拉宾单底数强伪素数** | $2047 = 23 \times 89$ | [`Carmichael/StrongPsp.lean`](Carmichael/StrongPsp.lean) | `Nat.smallest_strong_psp_two`, `Nat.strong_psp_2047` |
| 4 | **PSW 双底数 {2, 3} 定理** | $1373653 = 829 \times 1657$ | [`Carmichael/StrongPspMulti.lean`](Carmichael/StrongPspMulti.lean) | `Nat.smallest_strong_psp_two_three`, `Nat.strong_psp_two_three_1373653` |

---

## 核心数学与技术亮点

### 1. 攻克 Mathlib 官方开放 TODO（最小卡迈克尔数 561）
在 Mathlib 官方模块中：
> *"TODO: Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561."*

在 [`Carmichael/Smallest.lean`](Carmichael/Smallest.lean) 中，基于数论剪枝（奇数性、无平方因子性、半素数排除），仅需排查 279 种候选即可在数秒内完成内核验证。

### 2. 构造性 2-adic 分解与 2047 强伪素数极小性
在 [`Carmichael/StrongPsp.lean`](Carmichael/StrongPsp.lean) 中：
- 构造性实现 $n - 1 = d \cdot 2^s$ 分解（`Nat.oddPart`, `Nat.twoPowerPart`），无选择公理依赖；
- 建立 `Nat.IsStrongPsp (b : ℕ) (n : ℕ) : Prop` 标准命题；
- 基于计算反射，内核求值仅耗时 **约 2 毫秒**：
```lean
theorem smallest_strong_psp_two : ∀ n < 2047, ¬ IsStrongPsp 2 n
theorem strong_psp_2047 : IsStrongPsp 2 2047
theorem isStrongPsp_min : ∀ n, IsStrongPsp 2 n → 2047 ≤ n
```

### 3. 双底数多底数体系与 1,373,653 PSW 定理
在 [`Carmichael/StrongPspMulti.lean`](Carmichael/StrongPspMulti.lean) 中：
- 定义多底数系统：`def IsStrongPspSet (B : Finset ℕ) (n : ℕ) : Prop := ∀ b ∈ B, IsStrongPsp b n`；
- **稀疏证书反射（避免内核爆炸）**：数学证明小于 137 万的反例必先是以 2 为底的强伪素数（仅有 58 个！），通过内核反射秒级裁决 58 个候选全部通不过底数 3 的测试；
- 证明见证定理：
```lean
theorem smallest_strong_psp_two_three (h : Base2PspsPreFilter base2PspsLt1373653) :
    ∀ n < 1373653, ¬ IsStrongPspSet {2, 3} n
theorem strong_psp_two_three_1373653 : IsStrongPspSet {2, 3} 1373653
```

---

## 目录结构

```text
.
├── Carmichael.lean                 # 顶层基线与根入口
├── Carmichael/
│   ├── Korselt.lean                # 科瑟尔特准则（1899）与群指数等价
│   ├── Smallest.lean               # 561 极小性大定理（回应 Mathlib TODO）
│   ├── Poulet.lean                 # 341 最小 Poulet 数（以 2 为底费马伪素数）
│   ├── StrongPsp.lean              # 2047 最小强伪素数（米勒-拉宾单底数）
│   └── StrongPspMulti.lean         # 1,373,653 最小强伪素数（PSW {2, 3} 双底数大定理）
├── benchmark/                      # 性能基准与反射求值测试
├── PR_DESCRIPTION.md               # 向上游贡献 PR 描述
├── lakefile.lean                   # Lake 构建配置
└── lean-toolchain                  # Lean 4 工具链 (v4.33.1)
```

---

## 编译与验证

```bash
# 全量构建（开启警告即错误严格模式）
lake build -KwarningAsError=true

# 检查公理依赖（仅依赖 Lean 4 标准公理体系：propext, Classical.choice, Quot.sound）
lake env lean Carmichael/StrongPspMulti.lean
```

---

## 开源许可证

本项目采用双重开源许可证授权：
- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE))
- **木兰宽松许可证, 第2版 (MulanPSL-2.0)** ([LICENSE-MULAN](LICENSE-MULAN))
