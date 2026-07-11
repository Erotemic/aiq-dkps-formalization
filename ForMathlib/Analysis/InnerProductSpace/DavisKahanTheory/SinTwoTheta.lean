/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTheta
import ForMathlib.Analysis.InnerProductSpace.SinTwoThetaUINorm

/-!
# The complete finite-dimensional `sin (2 Θ)` theorem family

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 9, "The sin two Theta theorem".
* Davis--Kahan (1970), Section 2 (`sin 2Θ`) and Section 7 (reflection proof).
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, Section
  "The sharp two-subspace estimate" for the one-vector ancestor.

The perturbation and mirror-defect forms are already substantially present in
`SinTwoThetaUINorm.lean`.  This scaffold adds the residual form, canonical
angle-operator wrappers, unequal-rank extension, and the full concrete-norm
surface.
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

/-- Conjugation by the reflection through `V`. -/
noncomputable def reflectionConjugate (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  V.reflection.toLinearMap ∘ₗ A ∘ₗ V.reflection.toLinearMap

/-- Mirror defect `J A J - A`. -/
noncomputable def reflectionDefect (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  reflectionConjugate V A - A

/-- **Davis--Kahan `sin 2Θ`, residual form, every UI norm.**

Proof strategy: Use the reflection to convert the angle expression to a cross-block Sylvester
equation. Prefer the operator-norm proof from `DavisKahanExt.sinTwoTheta_residual`; obtain every
finite UI norm through the existing `SinTwoThetaUINorm` majorization theorem.
-/
theorem sinTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  sorry

/-- **Davis--Kahan `sin 2Θ`, perturbation form, every UI norm.**

Proof strategy: Combine the mirror-defect theorem with
`reflectionDefect_le_two_mul_perturbation`; instantiate spectral subspaces or zero-padded
unequal ranks afterward. The operator-norm core should be a direct Ext specialization.
-/
theorem sinTwoTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  sorry

/-- One-sided cross-block normalization matching the theorem already proved in
`SinTwoThetaUINorm.lean`.

Proof strategy: Apply the already proved theorem in `SinTwoThetaUINorm.lean` and reconcile its
cross-projection notation with the scaffold definitions.
-/
theorem sinTwoTheta_cross_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
      N (B - A) := by
  sorry

/-- Mirror-defect theorem with no second operator.

Proof strategy: Use the reflection to convert the angle expression to a cross-block Sylvester
equation. Prefer the operator-norm proof from `DavisKahanExt.sinTwoTheta_residual`; obtain every
finite UI norm through the existing `SinTwoThetaUINorm` majorization theorem.
-/
theorem sinTwoTheta_reflectionDefect_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {δ : ℝ} (hδ : 0 < δ)
    (hgap : InternalGap A U δ) :
    δ * N (sinTwoAngleOperator U V) ≤ N (reflectionDefect V A) := by
  sorry

/-- The reflection defect is at most twice the perturbation when `V` reduces
`B`.

Proof strategy: After adding symmetry of `B`, show its reflection commutes with `B`, rewrite
`JAJ-A` as two conjugates of `A-B`, and apply UI invariance plus the triangle inequality. This
is the finite specialization of the same lemma needed by `DavisKahanExt.DoubleAngle`.

Signature audit: False with only `Reduces B V`, because finite `Reduces` records invariance of
`V` but not of `Vᗮ`. Add `hB : B.IsSymmetric` (or explicitly assume both blocks reduce) so the
reflection commutes with `B`.
-/
theorem reflectionDefect_le_two_mul_perturbation
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} {V : Submodule 𝕜 E}
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    N (reflectionDefect V A) ≤ 2 * N (B - A) := by
  sorry

/-- Canonical spectral-projector form.

Proof strategy: Combine the mirror-defect theorem with
`reflectionDefect_le_two_mul_perturbation`; instantiate spectral subspaces or zero-padded
unequal ranks afterward. The operator-norm core should be a direct Ext specialization.
-/
theorem sinTwoTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {Ω : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : InternalGap A (spectralSubspace A Ω) δ) :
    δ * N (sinTwoAngleOperator (spectralSubspace A Ω)
        (spectralSubspace B Ω)) ≤ 2 * N (B - A) := by
  sorry

/-- Unequal-dimensional extension: zero padding records the unmatched
principal directions.

Proof strategy: Combine the mirror-defect theorem with
`reflectionDefect_le_two_mul_perturbation`; instantiate spectral subspaces or zero-padded
unequal ranks afterward. The operator-norm core should be a direct Ext specialization.
-/
theorem sinTwoTheta_perturbation_le_unequalFinrank
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  sorry

/-- Operator-norm form.

Proof strategy: Instantiate the corrected every-UI perturbation theorem and simplify. The
op-norm case should eventually be a direct specialization of
`DavisKahanExt.sinTwoTheta_perturbation`.
-/
theorem opNorm_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * ‖(sinTwoAngleOperator U V).toContinuousLinearMap‖ ≤
      2 * ‖(B - A).toContinuousLinearMap‖ := by
  sorry

/-- Frobenius form.

Proof strategy: Instantiate the corrected every-UI perturbation theorem and simplify. The
op-norm case should eventually be a direct specialization of
`DavisKahanExt.sinTwoTheta_perturbation`.
-/
theorem frobenius_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (sinTwoAngleOperator U V) ≤
      2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  sorry

/-- Ky Fan form.

Proof strategy: Instantiate the corrected every-UI perturbation theorem and simplify. The
op-norm case should eventually be a direct specialization of
`DavisKahanExt.sinTwoTheta_perturbation`.
-/
theorem kyFan_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) (k : ℕ) :
    δ * kyFanSum k (sinTwoAngleOperator U V) ≤ 2 * kyFanSum k (B - A) := by
  sorry

end DavisKahanTheory
end ForMathlib
