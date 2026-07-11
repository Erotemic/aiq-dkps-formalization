/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.RectangularUINorm

/-!
# Compressions, Ritz maps, and residuals

This file scaffolds the coordinate-free numerical-analysis side of the
Davis--Kahan theory.  An isometric embedding `X : F →ₗᵢ[𝕜] E` represents an
orthonormal approximate basis.  Its compression and residual are

`M = X⋆ A X`, `R = A X - X M`.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 2 and 5.
* Davis--Kahan (1970), Sections 1--2 and the block equations preceding the
  `sin Θ` and `tan Θ` theorems.
* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`,
  Sections "The proof as an upper/lower sandwich" and
  "Minimal supporting lemmas".
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

/-- Compression of `A` to the isometric coordinate space of `X`. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] F :=
  X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap

/-- Residual of an approximate invariant pair `(X,M)`. -/
noncomputable def residual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M

/-- Galerkin/Ritz residual. -/
noncomputable def ritzResidual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] E :=
  residual A X (compression A X)

/-- The represented approximate subspace. -/
def approximateSubspace (X : F →ₗᵢ[𝕜] E) : Submodule 𝕜 E :=
  LinearMap.range X.toLinearMap

/-- Sine map from approximate coordinates into the orthogonal complement of
an exact subspace. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  complementaryProjection U ∘ₗ X.toLinearMap

/-- Cosine map from approximate coordinates into an exact subspace. -/
noncomputable def cosThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  projection U ∘ₗ X.toLinearMap

/-- Tangent map in approximate coordinates. -/
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- Double-angle sine map in approximate coordinates. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- Double-angle tangent map in approximate coordinates. -/
noncomputable def tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- No principal angle between `U` and `range X` is `π/4`. -/
def AvoidsQuarterTurnEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : Prop :=
  AvoidsQuarterTurn U (approximateSubspace X)

/-- Compression of a symmetric operator is symmetric. -/
theorem isSymmetric_compression {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (X : F →ₗᵢ[𝕜] E) : (compression A X).IsSymmetric := by
  sorry

/-- The Ritz residual is orthogonal to the trial subspace. -/
theorem adjoint_comp_ritzResidual_eq_zero (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) :
    X.toLinearMap.adjoint ∘ₗ ritzResidual A X = 0 := by
  sorry

/-- Vanishing Ritz residual is equivalent to invariance of the represented
subspace. -/
theorem ritzResidual_eq_zero_iff_reduces {A : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) :
    ritzResidual A X = 0 ↔ Reduces A (approximateSubspace X) := by
  sorry

/-- Residuals transform naturally under a unitary change of approximate
coordinates. -/
theorem residual_comp_unitary (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) (V : F ≃ₗᵢ[𝕜] F) :
    residual A (X.comp V.toLinearIsometry)
        (V.symm.toLinearMap ∘ₗ M ∘ₗ V.toLinearMap) =
      residual A X M ∘ₗ V.toLinearMap := by
  sorry

/-- If `(X,M)` is invariant for `B`, its residual for `A` is exactly the
perturbation applied to `X`. -/
theorem residual_eq_perturbation_comp {A B : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    residual A X M = (A - B) ∘ₗ X.toLinearMap := by
  sorry

/-- A unitarily invariant norm of the invariant-pair residual is bounded by
that of the ambient perturbation. -/
theorem opNorm_residual_le_perturbation
    {A B : E →ₗ[𝕜] E} (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    RectangularUnitarilyInvariantNorm.opNorm (residual A X M) ≤
      ‖(A - B).toContinuousLinearMap‖ := by
  sorry

/-- The Ritz compression minimizes the Frobenius residual over all coordinate
operators. -/
theorem ritzResidual_frobenius_minimal (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    RectangularUnitarilyInvariantNorm.frobenius (ritzResidual A X) ≤
      RectangularUnitarilyInvariantNorm.frobenius (residual A X M) := by
  sorry

/-- Orthogonal decomposition of a general residual into the Ritz residual and
compression error. -/
theorem residual_frobenius_pythagoras (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    RectangularUnitarilyInvariantNorm.frobenius (residual A X M) ^ 2 =
      RectangularUnitarilyInvariantNorm.frobenius (ritzResidual A X) ^ 2 +
      RectangularUnitarilyInvariantNorm.frobenius (compression A X - M) ^ 2 := by
  sorry

/-- The singular values of `sinThetaEmbedding` are the sines of the principal
angles between `U` and `range X`. -/
theorem singularValues_sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (sinThetaEmbedding U X).singularValues =
      principalSines U (approximateSubspace X) := by
  sorry

/-- The tangent map is finite exactly when the represented subspace is
transverse to `U`. -/
theorem tanThetaEmbedding_defined_iff (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    IsTransverse (approximateSubspace X) U ↔
      LinearMap.ker (cosThetaEmbedding U X) = ⊥ := by
  sorry

end DavisKahanTheory
end ForMathlib
