/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SinTheta

/-!
# Complex spectral layer for the infinite-dimensional Davis--Kahan theory

The dimension-free residual, projection, coercive-Sylvester, and one-sided
`sin Θ` core is stated for arbitrary `RCLike` scalars.  The genuine *spectral*
hypotheses (a real bound on `spectrum ℝ T`) require the C\*-algebra order theory,
which at the pinned mathlib revision is available for **complex** operator
algebras only (`E →L[ℂ] E` carries the `CStarAlgebra`/`StarOrderedRing`
instances; the real operator-algebra CFC is not yet provided).  This module
therefore restricts to complex Hilbert spaces.

The two bridges below convert a real spectral bound into an operator quadratic
form bound via the spectral order
`spectrum ℝ T ⊆ (-∞, c] ⟹ T ≤ c • 1 ⟹ 0 ≤ c • 1 - T`, using
`le_algebraMap_of_spectrum_le` and `ContinuousLinearMap.nonneg_iff_isPositive`.
This is the infinite-dimensional analogue of the finite-dimensional
eigenbasis bridge in `DavisKahanTheory.Basic`, and it needs no
numerical-range / convex-hull-of-spectrum theorem.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Spectral upper bound ⟹ quadratic-form upper bound.**  If the real spectrum
of a self-adjoint `T` lies in `(-∞, c]`, then `re ⟪T x, x⟫ ≤ c ‖x‖²`.  Via the
C\*-order: `spectrum ℝ T ⊆ Iic c ⟹ T ≤ c • 1 ⟹ c • 1 - T ≥ 0`. -/
theorem re_inner_le_of_spectrum_subset_Iic
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) (x : H) :
    RCLike.re ⟪T x, x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  have hle : T ≤ algebraMap ℝ (H →L[ℂ] H) c :=
    le_algebraMap_of_spectrum_le (fun r hr => hσ hr) hT
  have hpos : (algebraMap ℝ (H →L[ℂ] H) c - T).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]; exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcx : RCLike.re ⟪c • x, x⟫_ℂ = c * ‖x‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith

/-- **Spectral lower bound ⟹ quadratic-form lower bound.**  If the real spectrum
of a self-adjoint `T` lies in `[c, ∞)`, then `c ‖x‖² ≤ re ⟪T x, x⟫`. -/
theorem le_re_inner_of_Ici_subset_spectrum
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) (x : H) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  have hle : algebraMap ℝ (H →L[ℂ] H) c ≤ T :=
    algebraMap_le_of_le_spectrum (fun r hr => hσ hr) hT
  have hpos : (T - algebraMap ℝ (H →L[ℂ] H) c).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]; exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcx : RCLike.re ⟪c • x, x⟫_ℂ = c * ‖x‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith

end DavisKahanExt
end ForMathlib
