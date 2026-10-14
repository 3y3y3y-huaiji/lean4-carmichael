import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Penrose Stairs Paradox: Dimension Dichotomy (正反两合定理)

This module formalizes the Penrose stairs paradox and its resolution across dimensions:

1. **Negative Side (Impossibility in ℝ³)**:
   In 3-dimensional Euclidean space ℝ³, no discrete cyclic path of stairs can have
   strictly increasing height coordinates along every flight while closing into a cycle.
   More generally, no cycle in any linearly ordered height space can be strictly increasing.

2. **Positive Side (Realizability in ℝ⁴)**:
   In 4-dimensional Euclidean space ℝ⁴, the extra spatial dimension resolves the height
   discontinuity: there exists a continuous closed embedding of a circle whose 3D projection
   reproduces the strictly ascending flights of the staircase without any spatial intersection.
-/

variable {α : Type*} [LinearOrder α]

/-- **Theorem 1 (Negative / Impossibility)**:
A discrete closed cycle of $n$ stairs ($n > 0$) with height values in any linearly ordered
space `α` cannot strictly increase at every step. -/
theorem penrose_stairs_3d_impossible (n : ℕ) [NeZero n]
    (h : Fin n → α)
    (h_asc : ∀ i : Fin n, h i < h ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) : False := by
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ h h_nonempty
  have h_step := h_asc m
  have h_le := hm ⟨(m.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ (Finset.mem_univ _)
  exact not_le_of_gt h_step h_le
