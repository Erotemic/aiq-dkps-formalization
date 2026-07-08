/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`PrincipalAngles.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W0.2 of
`dev/davis-kahan-gap-closure-plan.md`.

The canonical principal-angle API: the cosines of the principal angles between
two subspaces (given by orthonormal families) are the singular values of the
flat overlap operator `overlapOp` (from `AlignedBasis.lean`).  This packages the
`cos Θ`/`sin Θ` vectors, their basic order/range properties, the symmetry in the
two families (which needs `singularValues_adjoint`, W0.1(d)), and the bridge
`‖sin Θ‖²_F = d − overlap` to the flat overlap sum.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.AlignedBasis

/-! # Principal angles between subspaces

For orthonormal families `u : Fin d → E` and `v : Fin d → E` spanning two
`d`-dimensional subspaces `U = span u`, `V = span v`, the **cosines of the
principal angles** are the singular values of the flat overlap operator
`overlapOp hu hv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)`
(matrix `⟪uᵢ, vⱼ⟫`).  The singular values lie in `[0, 1]` (the operator is a
contraction), are sorted decreasingly, and are symmetric in `u, v` (`M⋆` is the
overlap operator of the swapped pair, and `σ(M⋆) = σ(M)`).

The complementary quantity `‖sin Θ‖²_F = ∑ᵢ sin²θᵢ = ∑ᵢ (1 − cos²θᵢ)` measures
the total misalignment of the two subspaces; here it equals `d − overlap` where
`overlap = ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` is the flat overlap sum used throughout the
Davis–Kahan development.

## Main definitions

* `ForMathlib.cosPrincipalAngles`: the sorted cosines `σ(overlapOp hu hv)`.
* `ForMathlib.sinThetaSq`: the squared Frobenius sine `∑ᵢ (1 − cos²θᵢ)`.

## Main results

* `ForMathlib.cosPrincipalAngles_nonneg` / `_le_one` / `_antitone`: range and
  order.
* `ForMathlib.overlapOp_adjoint`: `(overlapOp hu hv)⋆ = overlapOp hv hu`.
* `ForMathlib.cosPrincipalAngles_comm`: symmetry `cos Θ(u, v) = cos Θ(v, u)`.
* `ForMathlib.sinThetaSq_eq_sub_overlap`: `‖sin Θ‖²_F = d − overlap`.
* `ForMathlib.sum_sq_norm_aligned_le_sinThetaSq`: the Yu–Wang–Samworth
  aligned-basis bound restated as `∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`.
-/

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {d : ℕ}

/-- **The cosines of the principal angles** between the subspaces spanned by two
orthonormal families `u, v : Fin d → E`: the (sorted, `ℕ →₀ ℝ`-indexed) singular
values of the overlap operator `overlapOp hu hv`. -/
noncomputable def cosPrincipalAngles {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  (overlapOp hu hv).singularValues

theorem cosPrincipalAngles_nonneg {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : ℕ) : 0 ≤ cosPrincipalAngles hu hv i :=
  (overlapOp hu hv).singularValues_nonneg i

/-- The principal-angle cosines are at most `1`: the overlap operator is a
contraction. -/
theorem cosPrincipalAngles_le_one {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : Fin d) : cosPrincipalAngles hu hv (i : ℕ) ≤ 1 :=
  singularValues_le_one_of_contraction (overlapOp_contraction hu hv)
    finrank_euclideanSpace_fin i

theorem cosPrincipalAngles_antitone {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : Antitone (cosPrincipalAngles hu hv) :=
  (overlapOp hu hv).singularValues_antitone

/-- **The overlap operator of the swapped pair is the adjoint.**
`(overlapOp hu hv)⋆ = overlapOp hv hu`, immediate from `(P⋆ ∘ Q)⋆ = Q⋆ ∘ P`. -/
theorem overlapOp_adjoint {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (overlapOp hu hv).adjoint = overlapOp hv hu := by
  rw [overlapOp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, overlapOp]

/-- **Symmetry of the principal angles.**  `cos Θ(u, v) = cos Θ(v, u)`: the two
overlap operators are adjoint (`overlapOp_adjoint`) and adjoints share singular
values (`singularValues_adjoint`, plan step W0.1(d)). -/
theorem cosPrincipalAngles_comm {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : cosPrincipalAngles hu hv = cosPrincipalAngles hv hu := by
  rw [cosPrincipalAngles, cosPrincipalAngles, ← overlapOp_adjoint hu hv, singularValues_adjoint]

/-- **The squared Frobenius sine** `‖sin Θ‖²_F = ∑ᵢ sin²θᵢ = ∑ᵢ (1 − cos²θᵢ)`
between the subspaces spanned by two orthonormal families of the same size. -/
noncomputable def sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℝ :=
  ∑ k : Fin d, (1 - cosPrincipalAngles hu hv (k : ℕ) ^ 2)

/-- **`‖sin Θ‖²_F = d − overlap`.**  The squared Frobenius sine equals `d` minus
the flat overlap sum `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` (which is `∑ cos²θᵢ`). -/
theorem sinThetaSq_eq_sub_overlap {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = (d : ℝ) - ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 := by
  unfold sinThetaSq
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  congr 1
  unfold cosPrincipalAngles
  exact sum_sq_singularValues_overlapOp hu hv

theorem sinThetaSq_nonneg {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    0 ≤ sinThetaSq hu hv :=
  Finset.sum_nonneg fun k _ => by
    have h1 := cosPrincipalAngles_le_one hu hv k
    have h0 := cosPrincipalAngles_nonneg hu hv (k : ℕ)
    nlinarith

/-- Symmetry of the squared Frobenius sine, `‖sin Θ(u, v)‖²_F = ‖sin Θ(v, u)‖²_F`. -/
theorem sinThetaSq_comm {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = sinThetaSq hv hu := by
  unfold sinThetaSq
  rw [cosPrincipalAngles_comm hu hv]

/-- **Aligned-basis bound in principal-angle form.**  The Yu–Wang–Samworth
Procrustes-rotated basis `wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)` obeys
`∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`. -/
theorem sum_sq_norm_aligned_le_sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ j, ‖familyIsometry hv ((polarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))
        - u j‖ ^ 2
      ≤ 2 * sinThetaSq hu hv := by
  rw [sinThetaSq_eq_sub_overlap]
  exact sum_sq_norm_aligned_le hu hv

end ForMathlib
