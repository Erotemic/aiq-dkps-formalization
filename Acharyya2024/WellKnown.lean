/-
General lemmas used by the Acharyya et al. 2024 formalization.

This file is intentionally paper-agnostic: results that are useful outside DKPS
belong here first, so they can later be moved toward Mathlib if they are not
already present there in a comparable form.
-/

import Mathlib

open scoped BigOperators Topology

/--
Changing both endpoints of a distance changes the distance by at most the sum of
the two endpoint perturbations.

This is the normed-additive-group form of the elementary estimate used in the
paper's Appendix A.2 before applying Markov's inequality.

Formalized by Codex.
-/
theorem abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub
    {E : Type*} [SeminormedAddCommGroup E]
    (x y x₀ y₀ : E) :
    |‖x - y‖ - ‖x₀ - y₀‖| ≤ ‖x - x₀‖ + ‖y - y₀‖ := by
  have h₁ : |‖x - y‖ - ‖x₀ - y₀‖| ≤ ‖(x - y) - (x₀ - y₀)‖ :=
    abs_norm_sub_norm_le (x - y) (x₀ - y₀)
  have h₂ : ‖(x - y) - (x₀ - y₀)‖ ≤ ‖x - x₀‖ + ‖y - y₀‖ := by
    have hrewrite : (x - y) - (x₀ - y₀) = (x - x₀) - (y - y₀) := by
      abel
    simpa [hrewrite] using norm_sub_le (x - x₀) (y - y₀)
  exact h₁.trans h₂

/--
A scaled version of `abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub` for a
nonnegative scalar.

Formalized by Codex.
-/
theorem abs_mul_norm_sub_sub_le_mul_norm_sub_add
    {E : Type*} [SeminormedAddCommGroup E]
    {c : Real} (hc : 0 ≤ c) (x y x₀ y₀ : E) :
    |c * ‖x - y‖ - c * ‖x₀ - y₀‖| ≤ c * (‖x - x₀‖ + ‖y - y₀‖) := by
  have h :
      |c * ‖x - y‖ - c * ‖x₀ - y₀‖|
        = c * |‖x - y‖ - ‖x₀ - y₀‖| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub x y x₀ y₀) hc

/--
The finite `ℓ²` norm of a real-valued function is bounded by its `ℓ¹` norm.

Formalized by Codex.
-/
theorem sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (f : ι → Real) :
    Real.sqrt (∑ i, (f i)^2) ≤ ∑ i, |f i| := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg (f i)
  · simpa [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset ι)) (f := fun i => |f i|)
        (fun i _ => abs_nonneg (f i)))
