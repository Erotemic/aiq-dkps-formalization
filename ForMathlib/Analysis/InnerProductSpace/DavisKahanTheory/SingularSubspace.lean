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

/-- Left Gram operator `AA⋆`. -/
noncomputable def leftGram (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] F :=
  A ∘ₗ A.adjoint

/-- Right singular subspace selected by squared singular values in `Ω`. -/
noncomputable def rightSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  spectralSubspace (rightGram A) Ω

/-- Left singular subspace selected by squared singular values in `Ω`. -/
noncomputable def leftSingularSubspace (A : E →ₗ[𝕜] F) (Ω : Set ℝ) :
    Submodule 𝕜 F :=
  spectralSubspace (leftGram A) Ω

/-- Hermitian dilation `[[0,A⋆],[A,0]]`. -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) := by
  sorry

/-- Block diagonal operator `diag(A⋆A, AA⋆)`. -/
noncomputable def gramBlockDiagonal (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) := by
  sorry

/-- The dilation is symmetric.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the late Ext compact/singular layer.
-/
theorem isSymmetric_hermitianDilation (A : E →ₗ[𝕜] F) :
    (hermitianDilation A).IsSymmetric := by
  sorry

/-- Squaring the dilation gives the two Gram operators on the diagonal.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the late Ext compact/singular layer.
-/
theorem hermitianDilation_sq (A : E →ₗ[𝕜] F) :
    hermitianDilation A ∘ₗ hermitianDilation A =
      gramBlockDiagonal A := by
  sorry

/-- Gram perturbation identity.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the late Ext compact/singular layer.
-/
theorem rightGram_sub_rightGram
    (A Â : E →ₗ[𝕜] F) :
    rightGram Â - rightGram A =
      Â.adjoint ∘ₗ (Â - A) + (Â - A).adjoint ∘ₗ A := by
  sorry

/-- Operator-norm Gram perturbation bound.

Lean proof route for a weaker agent:

1. Prove directly by block-matrix/adjoint algebra and the operator-norm ideal inequality.
2. These finite identities are prerequisites for, rather than consequences of, the late Ext compact/singular layer.
-/
theorem opNorm_rightGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    ‖(rightGram Â - rightGram A).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  sorry

/-- Right singular-subspace `sin Θ` theorem obtained from the Gram operators.

Lean proof route for a weaker agent:

1. Apply the finite operator-norm `sin Θ` theorem to the appropriate Gram operators, then use `opNorm_rightGram_sub_le` (or its left analogue).
2. Keep this finite instead of waiting for `DavisKahanExt.CompactAndSingular`.
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
  sorry

/-- Left singular-subspace counterpart.

Lean proof route for a weaker agent:

1. Apply the finite operator-norm `sin Θ` theorem to the appropriate Gram operators, then use `opNorm_rightGram_sub_le` (or its left analogue).
2. Keep this finite instead of waiting for `DavisKahanExt.CompactAndSingular`.
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
  sorry

/-- Hermitian-dilation form controlling left and right singular subspaces in a
single Davis--Kahan application.

Lean proof route for a weaker agent:

1. Apply the finite `sin Θ` theorem to the Hermitian dilations and simplify the dilation perturbation.
2. This is the finite precursor of the later Ext Wedin theorem.
-/
theorem singularSubspace_dilation_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {Ω : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : HybridGap (hermitianDilation A) (hermitianDilation Â)
      (spectralSubspace (hermitianDilation A) Ω)
      (spectralSubspace (hermitianDilation Â) Ω) δ) :
    δ * ‖(sinThetaMap (spectralSubspace (hermitianDilation A) Ω)
        (spectralSubspace (hermitianDilation Â) Ω)).toContinuousLinearMap‖ ≤
      ‖(hermitianDilation Â - hermitianDilation A).toContinuousLinearMap‖ := by
  sorry

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
