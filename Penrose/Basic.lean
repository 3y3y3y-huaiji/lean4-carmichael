import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Max

/-!
# The Penrose Stairs Paradox (No-Go Theorem)

This file formalizes the classical Penrose stairs impossible object using a purely
algebraic and order-theoretic perspective: discrete group actions on the finite cyclic group
`ZMod n`.

## Main Theorem
`penrose_stairs_zmod_impossible`:
No height function on `ZMod n` with values in a linearly ordered type `α`
can strictly increase at every step along the cycle.
-/

variable {α : Type*} [LinearOrder α]

/-- A cyclic sequence of elements in an arbitrary linearly ordered type `α`
cannot strictly increase at every step. -/
theorem penrose_stairs_zmod_impossible (n : ℕ) [NeZero n]
    (h : ZMod n → α)
    (h_asc : ∀ x : ZMod n, h x < h (x + 1)) : False := by
  have h_nonempty : (Finset.univ : Finset (ZMod n)).Nonempty := Finset.univ_nonempty
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ h h_nonempty
  have h_step : h m < h (m + 1) := h_asc m
  have h_le : h (m + 1) ≤ h m := hm (m + 1) (Finset.mem_univ _)
  exact not_le_of_gt h_step h_le
