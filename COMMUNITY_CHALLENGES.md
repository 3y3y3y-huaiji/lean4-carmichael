# Mathlib 社区前沿挑战与后续研究路线备忘 (COMMUNITY_CHALLENGES.md)

本文件永久记录在个人仓库 `3y3y3y-huaiji/lean4-carmichael`，用于归档针对 Mathlib4 核心维护者与数论学家提出的未决设想与进阶研究攻坚计划。

---

## 📜 历史背景：Mathlib PR #42801 的关键讨论

在 Mathlib4 合并卡迈克尔数基础理论的原始 PR 中：
- **PR 链接**：[leanprover-community/mathlib4#42801](https://github.com/leanprover-community/mathlib4/pull/42801)
- **核心人物**：
  - **Felix Pernegger**（维也纳大学，PR 作者）
  - **Michael Stoll**（德国拜罗伊特大学数论讲席教授，Reviewer / Maintainer）
  - **Johan Commelin**（Liquid Tensor Experiment 领军人，Mathlib 核心领导者之一）

### 当时各方的尝试与瓶颈记录：
1. **Felix Pernegger（AI 协作初级尝试受挫）**：
   - 原文：*“Some of the proofs were originally made by Codex, but heavily golfed etc. A fun challenge would be to prove efficiently that 561 is the smallest Carmichael number. The following code works but is way too slow for mathlib: `interval_cases n ... all_goals norm_num`”*
   - **瓶颈分析**：依靠初级 LLM 的暴力策略在 Lean 4 中展开 560 个独立证明分支，导致语法树和内存爆炸、CI 超时，被迫放弃并留下 TODO。
2. **Michael Stoll 教授的观察**：
   - 原文：*“The problem seems to be that `Nat.primeFactorsList` does not kernel-reduce. The following works (and is fast): `by native_decide` ... but `decide` fails here. So to get this to work, one needs to make `example : Nat.primeFactorsList 60 = [2, 2, 3, 5] := by decide` work. But this is for another PR.”*
   - **瓶颈分析**：Stoll 认为必须先对全量质因数分解开发出内核可规约的基础设施，才能做全量排除。
3. **Johan Commelin 提出的终极挑战**：
   - 原文：*“@felixpernegger How far do you think we are from a verified tabulation of all Carmichael numbers below B, for say B ~ 10^6 or 10^9?”*
   - **Felix 回复**：*“I think 10^6 is still a challenge and would need observations not yet formalised... One curious intermediate thing that would be required, is to implement the Sieve of Eratosthenes for `Nat.primes_below`, which apparently isn't done right now.”*

---

## 🚀 我们的第一阶段突破（已达成）

针对上述困境，我们于 2026 年 9 月完成破局并正式提交官方 PR：
- **PR 链接**：[leanprover-community/mathlib4#43890](https://github.com/leanprover-community/mathlib4/pull/43890)
- **技术突破**：
  1. **放弃全量因数分解**：绕过 Stoll 提到的 `Nat.primeFactorsList` 无法内核规约的死结；
  2. **构造布尔证书阻击器 (`isNotCarmichael`)**：通过奇偶、试除平方数、小素数双向商阻击（$p \le 37$ 与 $n/p$），仅需 76 行纯净代码；
  3. **纯粹内核级反射**：直接走 `by decide`（0 外部不安全公理），仅需 **0.8 秒** 即可完成全部 560 个自然数的全量验证，彻底终结官方悬空 TODO！

---

## 🎯 承接社区愿景：后续三大攻坚战役 (Roadmap)

接下来，我们将在个人仓库与 Mathlib 上游逐步实现 Commelin、Stoll 与 Felix 的未决构想：

### 战役一：卡迈克尔数全量验证与分类定理 ($B \le 10^4$)
- **目标**：正式回答 Johan Commelin 提出的 “verified tabulation” 挑战。
- **数学依据**：在 $10^4$ 范围内，全部卡迈克尔数严格只有 7 个：
  $$561, 1105, 1729, 2465, 2821, 6601, 8911$$
- **技术路径**：
  - 基于我们已证明的 `hc.three_le_card_primeFactors`（至少 3 个不同素因子，最小因子 $p \le \sqrt[3]{10000} \approx 21.5$）；
  - 将 `smallPrimes` 适度扩充，证明健全性引理：
    $$\forall n < 10000, n \text{ 是卡迈克尔数} \iff n \in \{561, 1105, 1729, 2465, 2821, 6601, 8911\}$$
  - 继续坚持纯 `by decide`（不引入 `native_decide` 不可信公理），直接震撼 Commelin！

### 战役二：形式化且内核可规约的“埃氏筛” (`Nat.primes_below`)
- **目标**：实现 Felix Pernegger 提到的关键中间基建。
- **现状**：Mathlib 当前素数判定多依赖简单递归试除，计算大范围素数表时内核开销过大。
- **技术路径**：
  - 实现基于位图或尾递归数组的可计算埃氏筛算法 `eratosthenesSieve (N : ℕ) : List ℕ`；
  - 形式化证明其健全性与完备性：
    $$\forall p \le N, p \in \text{eratosthenesSieve } N \iff p.\text{Prime}$$
  - 为 Mathlib 贡献 `Nat.primesBelow` 高效规约算子，直接解决 Stoll 教授感叹的内核规约慢点。

### 战役三：伪素数全景金字塔（Stages 2–4）
- **Stage 2**：普莱特数（Poulet numbers，以 2 为底的费马伪素数）及 341 极小性定理（`Nat.not_isPoulet_of_lt_341`）；
- **Stage 3**：强伪素数（Strong Pseudoprimes）与米勒-拉宾测试，证明 2047 是最小底 2 强伪素数；
- **Stage 4**：多底强伪素数与 PSW 定理（1,373,653 极小性），实现针对 $n < 1,373,653$ 的极速确定性素性检测器。

---

## 📌 执行原则与规范保障

在后续攻坚中，必须严格贯彻已固化在 `.agents/skills/` 下的 4 大精益数学基建：
1. **`lean-proof-golfing`**：拒绝工程堆砌，追求数学直击本质；
2. **`mathlib-style-and-naming`**：7大命名决策树与严格 100 字符行宽；
3. **`mathlib-pr-conventions`**：小步快跑、Draft PR 优先与显性 LLM 披露。
