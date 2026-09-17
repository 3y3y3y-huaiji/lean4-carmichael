# AI Pair Programming & Formal Mathematics Guidelines (AGENTS.md)

This document provides explicit instructions for AI agents working in this repository.
All Lean 4 code and GitHub contributions in this workspace **MUST** adhere to the specialized skills installed under `.agents/skills/`.

---

## 🛠️ Installed Skills Suite (Prompt Reference)

The workspace is equipped with 4 production-grade formalization skills:

| Skill Directory | Primary Scope | When to Activate |
| :--- | :--- | :--- |
| [`.agents/skills/mathlib-style-and-naming`](.agents/skills/mathlib-style-and-naming/SKILL.md) | **Formatting & Naming** | Every time you write, edit, or refactor `.lean` files. Enforces 7 capitalization rules, line length $\le 100$, 2/4-space indent, docstrings, and `#use-of-ai` compliance. |
| [`.agents/skills/lean-proof-golfing`](.agents/skills/lean-proof-golfing/SKILL.md) | **Proof Compression & Tactics** | When proving theorems. Eliminates AI boilerplate, forbids reinventing wheels, uses tactic hierarchy (`omega`, `zify; grind`, `decide`), and achieves mathematical conciseness. |
| [`.agents/skills/mathlib-pr-conventions`](.agents/skills/mathlib-pr-conventions/SKILL.md) | **GitHub PR & Review Standards** | When drafting commits, preparing PRs, or communicating with upstream Mathlib. Enforces conventional commit titles, minimalist descriptions, and mandatory `LLM-generated` disclosure. |
| [`.agents/skills/mathematics-in-lean`](.agents/skills/mathematics-in-lean/SKILL.md) | **Mathematical Foundations** | For deep formalizations across number theory, algebra, and analysis based on the Mathematics in Lean (MIL) curriculum. |

---

## 📐 Mandatory AI Developer Workflow

Before delivering any Lean 4 code to the user or pushing to git, the AI agent **MUST** follow this 3-step quality gate:

### Step 1: Proof Golfing (No AI Spaghetti)
- Never construct 10-line manual arithmetic chains when `omega`, `ring`, or `zify; grind` can close it in 1 line.
- For bounded checks over finite domains ($n < N$), use **computational reflection** (`def dec ... := ...` + `by decide`) instead of branching into 500 cases.
- Reuse Mathlib existing theorems—never redefine concepts already merged in Mathlib.

### Step 2: Static Style & Naming Audit
Run the automated validator:
```bash
python .agents/skills/mathlib-style-and-naming/scripts/check_style_naming.py <path-to-file.lean>
```
Verify:
1. All lines $\le 100$ characters.
2. Theorem/lemma names are `snake_case`.
3. Types/classes/structures are `UpperCamelCase`.
4. Values/computable deciders are `lowerCamelCase`.
5. Spacing around `:`, `:=`, and infix operators is standard.

### Step 3: Local Lean 4 Verification
Run:
```bash
lake build -KwarningAsError=true
```
Ensure **0 errors, 0 warnings, and 0 sorry**.

---

## 🏷️ Upstream PR & Community Compliance

When interacting with `leanprover-community/mathlib4`:
1. **Never submit non-draft PRs without explicit user authorization** (default to `--draft`).
2. **Always include the LLM Disclosure** in the PR body:
   ```markdown
   > [!NOTE]
   > **LLM Disclosure / AI Use**: This PR was prepared with the assistance of an LLM (`LLM-generated`). All proofs and statements have been formally verified by Lean 4 and checked with linters.
   ```
3. **Trigger the official label**: Comment `LLM-generated` on the PR so the GitHub Actions bot applies the official `LLM-generated` label.
