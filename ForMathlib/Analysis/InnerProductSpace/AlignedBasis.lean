/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`AlignedBasis.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W3.4 of
`dev/davis-kahan-gap-closure-plan.md`.

Groundwork for the Yu–Wang–Samworth aligned-basis (orthogonal-Procrustes) bound:
the coordinate isometry `EuclideanSpace 𝕜 (Fin d) →ₗᵢ E` attached to an
orthonormal family, used to build the `d × d` overlap operator whose singular
values are the principal-angle cosines.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.LinearAlgebra.Basis.Defs
import ForMathlib.Analysis.InnerProductSpace.SingularSubspace

/-! # The coordinate isometry of an orthonormal family

An orthonormal family `v : Fin d → E` gives a linear isometry
`familyIsometry hv : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E`, `eⱼ ↦ vⱼ`, onto the
span of the family.  Its adjoint recovers the coordinates `y ↦ (⟪vⱼ, y⟫)ⱼ`, so
the composite `(familyIsometry hu)⋆ ∘ (familyIsometry hv)` is the overlap operator
with matrix `⟪uᵢ, vⱼ⟫` — the object whose singular values are the cosines of the
principal angles between `span u` and `span v`.

## Main results

* `ForMathlib.familyMap` and `familyMap_apply`: the linear map `eⱼ ↦ vⱼ`.
* `ForMathlib.familyMap_inner_map_map`: it preserves inner products when `v` is
  orthonormal.
* `ForMathlib.familyIsometry`: the bundled `EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E`.
-/

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {d : ℕ}

/-- The linear map `EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E` sending the `j`-th standard
basis vector to `v j` (extended linearly): `x ↦ ∑ j, x j • v j`. -/
noncomputable def familyMap (v : Fin d → E) : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
  (Fintype.linearCombination 𝕜 v).comp (WithLp.linearEquiv 2 𝕜 (Fin d → 𝕜)).toLinearMap

@[simp] theorem familyMap_apply (v : Fin d → E) (x : EuclideanSpace 𝕜 (Fin d)) :
    familyMap v x = ∑ i, x i • v i := by
  rw [familyMap, LinearMap.comp_apply, Fintype.linearCombination_apply]
  rfl

/-- The coordinate map of an orthonormal family preserves inner products. -/
theorem familyMap_inner_map_map {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (x y : EuclideanSpace 𝕜 (Fin d)) :
    ⟪familyMap v x, familyMap v y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  rw [familyMap_apply, familyMap_apply, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i i, if_pos rfl, mul_one,
      RCLike.inner_apply]
    ring
  · intro j _ hji
    rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i j, if_neg (Ne.symm hji),
      mul_zero, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The bundled coordinate isometry `EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E` of an
orthonormal family `v`, sending `eⱼ ↦ vⱼ`. -/
noncomputable def familyIsometry {v : Fin d → E} (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E :=
  (familyMap v).isometryOfInner (familyMap_inner_map_map hv)

@[simp] theorem familyIsometry_apply {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) : familyIsometry hv x = ∑ i, x i • v i := by
  rw [familyIsometry, LinearMap.coe_isometryOfInner, familyMap_apply]

end ForMathlib
