/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Statistics
import ForMathlib.Analysis.InnerProductSpace.SingularSubspace

/-!
# Singular-subspace Davis--Kahan and Wedin-style corollaries

Literature map:

* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`, Section
  "The singular-vector extension".
* `ForMathlib/prose/Horn-Johnson-2013-Gram-core-arguments.tex`, Sections on
  Gram factorization and isometric freedom.
* `papers/DavisKahan-formalized-vs-literature.tex`, paragraph
  "The singular-subspace extension".

The right singular subspaces are spectral subspaces of `A⋆A`, the left ones
are spectral subspaces of `AA⋆`, and the Hermitian dilation packages both at
once.  The existing `SingularSubspace.lean` contains much of the scalar and
Frobenius infrastructure; this file records the final canonical subspace API.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Right Gram operator `A⋆A`. -/
noncomputable def rightGram (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  A.adjoint ∘ₗ A

/-- The right Gram operator is symmetric and positive semidefinite. -/
theorem isSymmetric_rightGram (A : E →ₗ[𝕜] F) : (rightGram A).IsSymmetric := by
  simpa [rightGram] using A.isSymmetric_adjoint_comp_self

/-- Left Gram operator `AA⋆`. -/
noncomputable def leftGram (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] F :=
  A ∘ₗ A.adjoint

/-- The left Gram operator is symmetric and positive semidefinite. -/
theorem isSymmetric_leftGram (A : E →ₗ[𝕜] F) : (leftGram A).IsSymmetric := by
  simpa [leftGram] using A.adjoint.isSymmetric_adjoint_comp_self

/-- Right singular subspace selected by squared singular values in `Ω`. -/
noncomputable def rightSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  spectralSubspace (rightGram A) Ω

/-- Left singular subspace selected by squared singular values in `Ω`. -/
noncomputable def leftSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule 𝕜 F :=
  spectralSubspace (leftGram A) Ω

/-- The product-coordinate block map underlying the Hermitian dilation. -/
noncomputable def hermitianDilationProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun x := (A.adjoint x.2, A x.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Hermitian dilation `[[0,A⋆],[A,0]]`. -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    hermitianDilationProd A ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- The product-coordinate block map `diag(A⋆A, AA⋆)`. -/
noncomputable def gramBlockDiagonalProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun x := (rightGram A x.1, leftGram A x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Block diagonal operator `diag(A⋆A, AA⋆)`. -/
noncomputable def gramBlockDiagonal (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    gramBlockDiagonalProd A ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

@[simp] theorem hermitianDilation_apply (A : E →ₗ[𝕜] F)
    (x : WithLp 2 (E × F)) :
    hermitianDilation A x =
      WithLp.toLp 2 (A.adjoint (WithLp.ofLp x).2, A (WithLp.ofLp x).1) := by
  rfl

@[simp] theorem gramBlockDiagonal_apply (A : E →ₗ[𝕜] F)
    (x : WithLp 2 (E × F)) :
    gramBlockDiagonal A x =
      WithLp.toLp 2 (rightGram A (WithLp.ofLp x).1, leftGram A (WithLp.ofLp x).2) := by
  rfl

/-- The dilation is symmetric.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the experimental compact/singular layer.
-/
theorem isSymmetric_hermitianDilation (A : E →ₗ[𝕜] F) :
    (hermitianDilation A).IsSymmetric := fun x y => by
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, add_comm]

/-- Squaring the dilation gives the two Gram operators on the diagonal.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the experimental compact/singular layer.
-/
theorem hermitianDilation_sq (A : E →ₗ[𝕜] F) :
    hermitianDilation A ∘ₗ hermitianDilation A =
      gramBlockDiagonal A := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [rightGram, leftGram]

/-- Gram perturbation identity.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the experimental compact/singular layer.
-/
theorem rightGram_sub_rightGram
    (A Â : E →ₗ[𝕜] F) :
    rightGram Â - rightGram A =
      Â.adjoint ∘ₗ (Â - A) + (Â - A).adjoint ∘ₗ A := by
  ext x
  simp [rightGram, map_sub]

/-- Left-Gram perturbation identity, dual to `rightGram_sub_rightGram`. -/
theorem leftGram_sub_leftGram
    (A Â : E →ₗ[𝕜] F) :
    leftGram Â - leftGram A =
      (Â - A) ∘ₗ Â.adjoint + A ∘ₗ (Â - A).adjoint := by
  ext x
  simp [leftGram, map_sub]

/-- Operator-norm Gram perturbation bound.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the experimental compact/singular layer.
-/
theorem opNorm_rightGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    ‖(rightGram Â - rightGram A).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  refine (rightGram Â - rightGram A).toContinuousLinearMap.opNorm_le_bound
    (by positivity) fun x => ?_
  have h := norm_gram_sub_gram_apply_le
    (a := ‖A.toContinuousLinearMap‖)
    (â := ‖Â.toContinuousLinearMap‖)
    (ε := ‖(Â - A).toContinuousLinearMap‖)
    (norm_nonneg _) (norm_nonneg _)
    (fun y => A.toContinuousLinearMap.le_opNorm y)
    (fun y => Â.toContinuousLinearMap.le_opNorm y)
    (fun y => (Â - A).toContinuousLinearMap.le_opNorm y) x
  simpa [rightGram, add_comm] using h

/-- Operator-norm perturbation bound for the left Gram operator. -/
theorem opNorm_leftGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    ‖(leftGram Â - leftGram A).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  refine (leftGram Â - leftGram A).toContinuousLinearMap.opNorm_le_bound
    (by positivity) fun x => ?_
  have hAadj : ∀ y, ‖A.adjoint y‖ ≤ ‖A.toContinuousLinearMap‖ * ‖y‖ :=
    fun y => norm_adjoint_apply_le (norm_nonneg _)
      (fun z => A.toContinuousLinearMap.le_opNorm z) y
  have hÂadj : ∀ y, ‖Â.adjoint y‖ ≤ ‖Â.toContinuousLinearMap‖ * ‖y‖ :=
    fun y => norm_adjoint_apply_le (norm_nonneg _)
      (fun z => Â.toContinuousLinearMap.le_opNorm z) y
  have hdiffadj : ∀ y,
      ‖(Â.adjoint - A.adjoint) y‖ ≤ ‖(Â - A).toContinuousLinearMap‖ * ‖y‖ :=
    fun y => by
      have h := norm_adjoint_apply_le (norm_nonneg _)
        (fun z => (Â - A).toContinuousLinearMap.le_opNorm z) y
      simpa [map_sub] using h
  have h := norm_gram_sub_gram_apply_le
    (A := A.adjoint) (Â := Â.adjoint)
    (a := ‖A.toContinuousLinearMap‖)
    (â := ‖Â.toContinuousLinearMap‖)
    (ε := ‖(Â - A).toContinuousLinearMap‖)
    (norm_nonneg _) (norm_nonneg _) hAadj hÂadj hdiffadj x
  simpa [leftGram, map_sub, add_comm] using h

/-- Right singular-subspace `sin Θ` theorem obtained from the Gram operators.

Lean proof route for a weaker agent:

1. Apply the finite operator-norm `sin Θ` theorem to the appropriate Gram operators, then use `opNorm_rightGram_sub_le` (or its left analogue).
2. Keep this finite instead of waiting for the experimental compact/singular-subspace module.
-/
theorem rightSingularSubspace_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap (rightGram A) (rightGram Â)
      (rightSingularSubspace A (Set.Icc a b))
      (rightSingularSubspace Â (Set.Icc a b)) a b δ) :
    δ * ‖(sinThetaMap (rightSingularSubspace A (Set.Icc a b))
        (rightSingularSubspace Â (Set.Icc a b))).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  have hdk := sinTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 E)
    (isSymmetric_rightGram A) (isSymmetric_rightGram Â)
    (reduces_spectralSubspace (rightGram A) (Set.Icc a b))
    (reduces_spectralSubspace (rightGram Â) (Set.Icc a b)) hδ hgap
  change δ * ‖(sinThetaMap (rightSingularSubspace A (Set.Icc a b))
      (rightSingularSubspace Â (Set.Icc a b))).toContinuousLinearMap‖ ≤
    ‖(rightGram Â - rightGram A).toContinuousLinearMap‖ at hdk
  exact hdk.trans (opNorm_rightGram_sub_le A Â)

/-- Left singular-subspace counterpart.

Lean proof route for a weaker agent:

1. Apply the finite operator-norm `sin Θ` theorem to the appropriate Gram operators, then use `opNorm_rightGram_sub_le` (or its left analogue).
2. Keep this finite instead of waiting for the experimental compact/singular-subspace module.
-/
theorem leftSingularSubspace_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap (leftGram A) (leftGram Â)
      (leftSingularSubspace A (Set.Icc a b))
      (leftSingularSubspace Â (Set.Icc a b)) a b δ) :
    δ * ‖(sinThetaMap (leftSingularSubspace A (Set.Icc a b))
        (leftSingularSubspace Â (Set.Icc a b))).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  have hdk := sinTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 F)
    (isSymmetric_leftGram A) (isSymmetric_leftGram Â)
    (reduces_spectralSubspace (leftGram A) (Set.Icc a b))
    (reduces_spectralSubspace (leftGram Â) (Set.Icc a b)) hδ hgap
  change δ * ‖(sinThetaMap (leftSingularSubspace A (Set.Icc a b))
      (leftSingularSubspace Â (Set.Icc a b))).toContinuousLinearMap‖ ≤
    ‖(leftGram Â - leftGram A).toContinuousLinearMap‖ at hdk
  exact hdk.trans (opNorm_leftGram_sub_le A Â)

/-- Hermitian-dilation form controlling left and right singular subspaces in a
single Davis--Kahan application.

Lean proof route for a weaker agent:

1. Apply the generic separated-spectrum finite `sin Θ` theorem to the two
   explicit Hermitian dilations.
2. Keep the `pi / 2` factor: `HybridGap` does not encode ordered or
   interval/exterior geometry.
3. A later Wedin wrapper may separately prove
   `‖hermitianDilation (Â-A)‖ = ‖Â-A‖` and replace the dilation difference by the
   rectangular perturbation norm.

Signature audit: the previous constant-one conclusion was too strong for an
arbitrary `HybridGap`; constant one requires a stronger gap predicate.
-/
theorem singularSubspace_dilation_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {Ω : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : HybridGap (hermitianDilation A) (hermitianDilation Â)
      (spectralSubspace (hermitianDilation A) Ω)
      (spectralSubspace (hermitianDilation Â) Ω) δ) :
    δ * ‖(sinThetaMap (spectralSubspace (hermitianDilation A) Ω)
        (spectralSubspace (hermitianDilation Â) Ω)).toContinuousLinearMap‖ ≤
      (Real.pi / 2) *
        ‖(hermitianDilation Â - hermitianDilation A).toContinuousLinearMap‖ := by
  exact sinTheta_perturbation_le_of_spectralDistance
    (UnitarilyInvariantNorm.opNorm 𝕜 (WithLp 2 (E × F)))
    (isSymmetric_hermitianDilation A) (isSymmetric_hermitianDilation Â)
    (reduces_spectralSubspace (hermitianDilation A) Ω)
    (reduces_spectralSubspace (hermitianDilation Â) Ω) hδ hgap

/-- Equal-dimensional right singular subspaces admit an isometric
identification; the aligned-frame theorem in `Statistics.lean` chooses the
identification minimizing basis discrepancy.

Lean proof route for a weaker agent:

1. Use equality of finite dimensions to choose orthonormal bases of the two subspaces and map one basis isometrically to the other.
2. Obtain orthonormal bases indexed by the common finrank.
3. Use `OrthonormalBasis.equiv` or construct the linear isometry by basis extension, then package it in `Nonempty`.
-/
theorem nonempty_rightSingularSubspace_isometry
    {A Â : E →ₗ[𝕜] F} {Ω : Set ℝ}
    (hrank : finrank 𝕜 (rightSingularSubspace A Ω) =
      finrank 𝕜 (rightSingularSubspace Â Ω)) :
    Nonempty (rightSingularSubspace Â Ω ≃ₗᵢ[𝕜]
      rightSingularSubspace A Ω) := by
  sorry

end DavisKahanTheory
end ForMathlib
