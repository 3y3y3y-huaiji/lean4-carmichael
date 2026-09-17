---
name: mathematics-in-lean
description: >-
  Authoritative formalization and proof-golfing guide based directly on the
  Mathematics in Lean (MIL) curriculum and Mathlib community best practices.
  Eliminates AI boilerplate and anti-patterns across calculations, logic,
  sets, number theory, algebra, and computational reflection with idiomatic,
  review-ready Lean 4 patterns.
---

# Mathematics in Lean: Idiomatic Formalization & Proof Golfing Guide
# 《精益数学》通用形式化规范与证明精简（Golfing）指南

This skill codifies the authoritative formalization principles, tactic hierarchies,
and compression paradigms from the official *Mathematics in Lean* (MIL) curriculum
by Jeremy Avigad, Patrick Massot et al., alongside Mathlib maintainer standards.
本技能系统提炼官方《精益数学》（MIL）教程与 Mathlib 社区维护者核心标准，
彻底消除 AI 生成的啰嗦模板代码，指引编写紧凑、地道、可直接合并的高质量证明。

---

## 1. The Core Philosophy: Mathlib-Idiomatic vs. AI Anti-Patterns
## 核心理念：Mathlib 地道规范 vs. AI 意面反面模式

| 维度 | Mathlib 地道规范 | 严禁的 AI 废话模式 |
| :--- | :--- | :--- |
| **自动化** | 决策战术 (`omega`, `ring`, `norm_num`) | 10+ 行手工 `rw` 重写链 |
| **中间变量** | 管道流 / 项模式 / `obtain` 解构 | 级联 `have h1 ... have h2` |
| **减法整除** | `zify; grind` 提升至 ℤ 求解 | 30 行自然数下溢分类讨论 |
| **有限搜索** | `decide` 计算反射 1 行搞定 | 暴力手工枚举分支讨论 |
| **库复用** | 检索复用 (`exact?`, `apply?`) | 闭门造车重复造已有引理 |

---

## 2. Chapter 2: Basics & Algebraic Calculation (基础与代数计算)

### Tactic Hierarchy for Equational Reasoning (代数推理战术层级)
1. **Concrete Numerics (纯具体数值计算)**: Use 
orm_num.
   - Examples: evaluating primes, prime factors, gcd, modular arithmetic on numbers.
2. **Ring / Field Equalities (环/域恒等式)**: Use 
ing (or 
ing1).
   - Handles commutativity, associativity, distribution, expansion without manual steps.
3. **Linear Integer/Natural Inequalities (一元线性算术与不等式)**: Use omega (or linarith).
   - Automatically solves Presburger arithmetic, order transitivity, linear bounds.
4. **Targeted Equational Rewrite (定向重写)**: Use 
w [lemma] or 
th_rw.
   - Keep rewrite lists short: 
w [h1, h2, h3] instead of separate tactic lines.

### Anti-Pattern Elimination (反面模式消除)

`lean
-- ❌ BAD (AI Fluff: manual associative/commutative expansion)
have h1 : (x + y) * (x - y) = x * (x - y) + y * (x - y) := by rw [add_mul]
have h2 : x * (x - y) = x * x - x * y := by rw [mul_sub]
have h3 : y * (x - y) = y * x - y * y := by rw [mul_sub]
-- ... 10 more lines of manual algebra

-- ✅ GOOD (Mathlib Idiomatic: 1 line)
ring
`

`lean
-- ❌ BAD (AI Fluff: chaining inequalities manually)
have h1 : a <= b := by omega
have h2 : b < c := by omega
have h3 : a < c := lt_of_le_of_lt h1 h2
exact h3

-- ✅ GOOD (Mathlib Idiomatic: 1 line)
omega
`

---

## 3. Chapter 3: Logic, Quantifiers & Negation (逻辑、量词与反证法)

### Deconstruction & Construction Rules (构造与解构法则)

| Connective / Quantifier 逻辑结构 | Introduction (证明目标) | Elimination (拆解前置假设 h) |
| :--- | :--- | :--- |
| **Conjunction 逻辑与 (P ∧ Q)** | constructor or ⟨hp, hq⟩ | 
cases h with ⟨hp, hq⟩ |
| **Disjunction 逻辑或 (P ∨ Q)** | left / 
ight or Or.inl / Or.inr | 
cases h with hp | hq |
| **Implication 逻辑蕴涵 (P → Q)** | intro hp or un hp ↦ ... | h hp (function application) |
| **Equivalence 充要条件 (P ↔ Q)** | constructor or ⟨mp, mpr⟩ | h.mp, h.mpr |
| **Existential 存在量词 (∃ x, P x)** | use x or 
efine ⟨x, ?_⟩ | obtain ⟨x, hx⟩ := h |
| **Negation & Contradiction 反证法** | y_contra h (经典反证) | contrapose! h (转为逆否命题) |

### Anti-Pattern: Deep Nested Deconstructions (严禁多层嵌套解构)

`lean
-- ❌ BAD (AI Fluff: 3 levels of rcases)
rcases h with ⟨h1, h2⟩
rcases h2 with ⟨h3, h4⟩
rcases h4 with ⟨x, hx⟩

-- ✅ GOOD (Mathlib Idiomatic: 1-line flat obtain)
obtain ⟨h1, h3, x, hx⟩ := h
`

### Contraposition over Contradiction (优先使用逆否命题)
- When goal is P → ¬ Q, prefer contrapose! h over intro hp; by_contra hq.
  Mathlib maintainers prefer constructive contraposition whenever possible.

---

## 4. Chapter 4: Sets, Functions & Relations (集合、映射与关系)

### Key Methodologies (核心法则)
1. **Extensionality (外延性原理)**: Use ext (or ext x) to prove two sets or functions equal.
2. **Set Membership Simplification**:
   - simp only [Set.mem_setOf_eq]
   - simp only [Set.mem_inter_iff, Set.mem_union]
3. **Function Properties**:
   - **Injectivity (单射)**: intro x y hxy followed by equational deduction.
   - **Surjectivity (满射)**: intro y; obtain ⟨x, rfl⟩ := ...
4. **Relational Reasoning**: Use calc blocks for multi-step transitive chains.

---

## 5. Chapter 5: Number Theory & Divisibility (数论、整除与计算反射)

### The Natural Subtraction Pitfall & The zify Bridge (自然数截断陷阱与 zify 桥梁)
In ℕ, `a - b` is truncated to 0 if `a < b`. Proving algebraic divisibilities
involving `p - 1` or `n - 1` directly in ℕ generates massive boilerplate.
- **The Golden Rule**: Use `zify` to cast equalities/congruences into ℤ,
  solve with `ring` or `grind`, then return.

```lean
-- ❌ BAD (AI Fluff: 25 lines of Nat underflow casing)
have h_pos : 1 <= p := hp.one_le
have h_sub : ...

-- ✅ GOOD (Mathlib Idiomatic: 1 line)
have eq : p - 1 + (q - 1) * p = p * q - 1 := by zify; grind
```

### Computational Reflection (计算反射)
Whenever verifying a bounded universal property `∀ n < N, ¬ P n` on a finite domain:
1. Construct computable decider `P_dec (n : ℕ) : Bool`.
2. Prove single soundness lemma: `P_dec n = false → ¬ P n`.
3. Dispatch the entire bounded verification in **1 line** via `decide`:
   ```lean
   theorem not_P_below_N : ∀ n < N, ¬ P n := by decide
   ```

---

## 6. Chapter 6: Algebraic Structures (抽象代数结构)

### Typeclasses & Morphisms (类型类与态射)
- **Monoids & Groups**: Rely on typeclass synthesis `[Group G]` instead of manual axioms.
- **Homomorphisms**: Use bundled morphisms (`MonoidHom`, `RingHom`);
  apply `map_mul`, `map_pow`, `map_one`.
- **Substructures**: Work with `Subgroup`, `Submonoid`, `Ideal`. Use `.mem` lemmas.

---

## 7. The 10 Mandates & 10 Prohibitions (10 必须与 10 严禁)

### The 10 Mandates (10 必须)
1. **Must** search Mathlib (exact?, pply?, Moogle) before writing any lemma.
2. **Must** prefer modern decision tactics: omega for linear arithmetic, 
ing for polynomials.
3. **Must** use obtain ⟨...⟩ for simultaneous destructuring.
4. **Must** keep line lengths strictly <= 100 characters.
5. **Must** use zify when manipulating subtraction in number-theoretic divisibility.
6. **Must** use decide / computational reflection for finite bounded searches.
7. **Must** use calc blocks for clarity when chaining >= 3 transitivity steps.
8. **Must** provide docstrings (/-- ... -/) on all top-level public definitions and theorems.
9. **Must** use snake_case for theorem names matching Mathlib conventions (even_add_even).
10. **Must** run #lint and maintain zero warnings under -KwarningAsError=true.

### The 10 Prohibitions (10 严禁)
1. **Never** write manual rewrite chains when 
ing, omega, or 
orm_num applies.
2. **Never** write cascading single-variable have chains without branch-closing tactics.
3. **Never** redefine concepts already in Mathlib (e.g. Prime, Squarefree, Coprime).
4. **Never** leave sorry in production code.
5. **Never** use non-standard axioms beyond [propext, Classical.choice, Quot.sound].
6. **Never** write lines exceeding 100 characters.
7. **Never** case-split finite domains manually (e.g. checking 500 cases one-by-one).
8. **Never** use simp non-terminally without simp only or restricted rule sets.
9. **Never** duplicate proofs between left/right symmetric branches (use wlog or symmetry lemmas).
10. **Never** include conversational AI fluff or unsolicited tutorials in PR descriptions.

---

## 8. Pre-Submission Quality Checklist (提交前自查清单)

- [ ] **Line Length**: All lines <= 100 characters (Get-Content <file> | ...).
- [ ] **Axiom Hygiene**: Verified with #print axioms <thm> (standard Lean 4 core axioms only).
- [ ] **Golfing Review**: Can any have block be compressed into omega, 
ing, or 
orm_num?
- [ ] **Linter Cleanliness**: Runs clean under #lint with 0 errors and 0 warnings.
- [ ] **PR Conventions**: Title adheres to <type>(<scope>): <subject> format.
