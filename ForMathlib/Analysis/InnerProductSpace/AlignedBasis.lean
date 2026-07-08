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

@[simp] theorem familyIsometry_single {v : Fin d → E} (hv : Orthonormal 𝕜 v) (k : Fin d) :
    familyIsometry hv (EuclideanSpace.single k 1) = v k := by
  rw [familyIsometry_apply]
  rw [Finset.sum_eq_single k]
  · rw [PiLp.single_apply, if_pos rfl, one_smul]
  · intro i _ hik; rw [PiLp.single_apply, if_neg hik, zero_smul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

variable [FiniteDimensional 𝕜 E]

/-- **The overlap operator** of two orthonormal families `u, v`: the compression
`(familyIsometry hu)⋆ ∘ (familyIsometry hv)` on `EuclideanSpace 𝕜 (Fin d)`, with
matrix `⟪uᵢ, vⱼ⟫`.  Its singular values are the cosines of the principal angles
between `span u` and `span v`. -/
noncomputable def overlapOp {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  (familyIsometry hu).toLinearMap.adjoint ∘ₗ (familyIsometry hv).toLinearMap

theorem overlapOp_apply {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) :
    overlapOp hu hv x = (familyIsometry hu).toLinearMap.adjoint (familyIsometry hv x) := rfl

/-- **The overlap operator is a contraction.** `‖overlapOp hu hv x‖ ≤ ‖x‖`, since
`familyIsometry hv` is an isometry and the adjoint of an isometry is a
contraction. -/
theorem overlapOp_contraction {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) : ‖overlapOp hu hv x‖ ≤ ‖x‖ := by
  rw [overlapOp_apply]
  have hiso : ∀ y : EuclideanSpace 𝕜 (Fin d), ‖(familyIsometry hu).toLinearMap y‖ ≤ 1 * ‖y‖ :=
    fun y => by rw [one_mul, LinearIsometry.coe_toLinearMap]; exact le_of_eq ((familyIsometry hu).norm_map y)
  calc ‖(familyIsometry hu).toLinearMap.adjoint (familyIsometry hv x)‖
      ≤ 1 * ‖familyIsometry hv x‖ := norm_adjoint_apply_le (by norm_num) hiso _
    _ = ‖x‖ := by rw [one_mul, (familyIsometry hv).norm_map]

/-- **The overlap sum equals `∑ σ²`.** The sum of squared singular values of the
overlap operator is the total squared overlap `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.  (By Parseval,
`‖overlapOp eⱼ‖² = ‖(familyIsometry hu)⋆ vⱼ‖² = ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.) -/
theorem sum_sq_singularValues_overlapOp {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) ^ 2
      = ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 := by
  rw [sum_sq_singularValues (overlapOp hu hv) finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin d) 𝕜)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [overlapOp_apply]
  simp only [EuclideanSpace.basisFun_apply, familyIsometry_single]
  rw [← (EuclideanSpace.basisFun (Fin d) 𝕜).sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
    familyIsometry_single]

/-- **The overlap sum is at most the sum of singular values (cosines).**
`∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖² ≤ ∑ⱼ cos θⱼ`, i.e. `d − ‖sinΘ‖²_F ≤ ∑ cos θ`.  This is the
analytic heart of the Yu–Wang–Samworth aligned-basis (orthogonal-Procrustes)
bound: the overlap operator is a contraction, so `∑σ² ≤ ∑σ`, and its squared
singular values sum to the overlap while its singular values sum to `∑ cos θ`. -/
theorem sum_overlap_le_sum_singularValues {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 ≤ ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) := by
  have h : finrank 𝕜 (EuclideanSpace 𝕜 (Fin d)) = d := finrank_euclideanSpace_fin
  -- `∑σ² ≤ ∑σ`, over `Fin (finrank)`, from the contraction core lemma.
  have hcore := sum_sq_norm_le_sum_re_inner_abs_of_contraction (overlapOp_contraction hu hv)
    (stdOrthonormalBasis 𝕜 (EuclideanSpace 𝕜 (Fin d)))
  rw [← sum_sq_singularValues (overlapOp hu hv) rfl (stdOrthonormalBasis 𝕜 _),
    sum_re_inner_abs_self_eq_sum_singularValues (overlapOp hu hv)
      (stdOrthonormalBasis 𝕜 _)] at hcore
  -- Reindex `Fin (finrank) → Fin d`.
  have reindex : ∀ g : ℕ → ℝ,
      ∑ i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin d))), g (i : ℕ) = ∑ i : Fin d, g (i : ℕ) :=
    fun g => Fintype.sum_equiv (finCongr h) _ _ (fun i => by simp)
  rw [reindex (fun m => (overlapOp hu hv).singularValues m ^ 2),
    reindex fun m => (overlapOp hu hv).singularValues m] at hcore
  calc ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2
      = ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) ^ 2 :=
        (sum_sq_singularValues_overlapOp hu hv).symm
    _ ≤ ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) := hcore

/-- **Cross-term identity** (Procrustes/polar).  With `O = polarUnitary
(overlapOp hu hv)`, the aligned rotation `wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)`
satisfies `⟪uⱼ, wⱼ⟫ = ⟪O⁻¹ eⱼ, |M|(O⁻¹ eⱼ)⟫`, where `M = overlapOp hu hv`.
Moves `familyIsometry hu` to its adjoint (giving `M`), then `M = O|M|` with `O`
unitary. -/
theorem inner_u_aligned_eq {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (j : Fin d) :
    ⟪u j, familyIsometry hv ((polarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))⟫_𝕜
      = ⟪(polarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1),
          abs (overlapOp hu hv)
            ((polarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))⟫_𝕜 := by
  set M := overlapOp hu hv with hM
  set O := polarUnitary M with hO
  have hstep : ⟪u j, familyIsometry hv (O.symm (EuclideanSpace.single j 1))⟫_𝕜
      = ⟪EuclideanSpace.single j 1, M (O.symm (EuclideanSpace.single j 1))⟫_𝕜 := by
    rw [← familyIsometry_single hu j, ← LinearIsometry.coe_toLinearMap,
      ← LinearMap.adjoint_inner_right]
    rfl
  rw [hstep]
  -- `M = O ∘ |M|`, then `O` unitary moves across the inner product.
  have hpolar : M (O.symm (EuclideanSpace.single j 1))
      = O (abs M (O.symm (EuclideanSpace.single j 1))) := by
    have h1 := LinearMap.congr_fun (polar_decomposition_unitary M)
      (O.symm (EuclideanSpace.single j 1))
    rw [LinearMap.comp_apply] at h1
    rw [h1, hO]
    rfl
  rw [hpolar, ← O.apply_symm_apply (EuclideanSpace.single j 1)]
  rw [O.inner_map_map, O.symm_apply_apply]

end ForMathlib
