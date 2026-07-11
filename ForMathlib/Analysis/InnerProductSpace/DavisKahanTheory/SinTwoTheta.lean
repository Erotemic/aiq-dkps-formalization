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

Lean proof route for a weaker agent:

1. Use the reflection to convert the angle expression to a cross-block Sylvester equation.
2. Prefer the operator-norm proof from the supported `DavisKahan.ReflectionDefect` module; obtain every finite UI norm through the existing `SinTwoThetaUINorm` majorization theorem.
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

Lean proof route for a weaker agent:

1. Combine the mirror-defect theorem with `reflectionDefect_le_two_mul_perturbation`; instantiate spectral subspaces or zero-padded unequal ranks afterward.
2. The operator-norm core should be a direct specialization of the supported reflection-defect theory.
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

Lean proof route for a weaker agent:

1. Apply the already proved theorem in `SinTwoThetaUINorm.lean` and reconcile its cross-projection notation with the scaffold definitions.
2. Rewrite `sinTwoAngleOperator` with `sinTwoAngleOperator_eq_two_smul_cross` if the source theorem uses the normalized map.
3. Normalize scalar multiplication with `N.smul_eq` and `norm_ofNat`.
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

Lean proof route for a weaker agent:

1. Use the reflection to convert the angle expression to a cross-block Sylvester equation.
2. Prefer the operator-norm proof from the supported `DavisKahan.ReflectionDefect` module; obtain every finite UI norm through the existing `SinTwoThetaUINorm` majorization theorem.
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

Lean proof route for a weaker agent:

1. After adding symmetry of `B`, show its reflection commutes with `B`, rewrite `JAJ-A` as two conjugates of `A-B`, and apply UI invariance plus the triangle inequality.
2. This is the finite specialization of the same lemma needed by `DavisKahan.ReflectionDefect`.

Signature audit: The added `hB` hypothesis upgrades invariance of `V` to reduction of both
orthogonal blocks, so the reflection commutes with `B`.
-/
theorem reflectionDefect_le_two_mul_perturbation
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hB : B.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces B V) :
    N (reflectionDefect V A) ≤ 2 * N (B - A) := by
  let J : E →ₗ[𝕜] E := V.reflection.toLinearMap
  have hcomm : J ∘ₗ B = B ∘ₗ J := by
    ext x
    change V.reflection (B x) = B (V.reflection x)
    simp only [Submodule.reflection_apply, map_sub, map_nsmul]
    have hproj :
        V.starProjection (B x) = B (V.starProjection x) := by
      change projection V (B x) = B (projection V x)
      exact projection_apply_comm_of_reduces hB hV x
    rw [hproj]
  have hJinvol : J ∘ₗ J = LinearMap.id := by
    ext x
    change V.reflection (V.reflection x) = x
    exact V.reflection_reflection x
  have hconjB : J ∘ₗ B ∘ₗ J = B := by
    ext x
    have hc := LinearMap.congr_fun hcomm (J x)
    change J (B (J x)) = B (J (J x)) at hc
    have hj := LinearMap.congr_fun hJinvol x
    change J (J x) = x at hj
    change J (B (J x)) = B x
    calc
      J (B (J x)) = B (J (J x)) := hc
      _ = B x := congrArg B hj
  have hdef : reflectionDefect V A =
      J ∘ₗ (A - B) ∘ₗ J - (A - B) := by
    ext x
    simp only [reflectionDefect, reflectionConjugate, J, LinearMap.comp_apply,
      LinearMap.sub_apply, map_sub]
    have hb := LinearMap.congr_fun hconjB x
    change J (B (J x)) = B x at hb
    rw [hb]
    abel
  have hconjNorm : N (J ∘ₗ (A - B) ∘ₗ J) = N (A - B) := by
    simpa [J] using N.invariant V.reflection V.reflection (A - B)
  calc
    N (reflectionDefect V A) =
        N (J ∘ₗ (A - B) ∘ₗ J - (A - B)) := by rw [hdef]
    _ ≤ N (J ∘ₗ (A - B) ∘ₗ J) + N (-(A - B)) := by
      rw [sub_eq_add_neg]
      exact N.add_le _ _
    _ = N (A - B) + N (A - B) := by
      rw [hconjNorm, N.apply_neg]
    _ = 2 * N (B - A) := by
      have hsub : A - B = -(B - A) := by abel
      rw [hsub, N.apply_neg]
      ring

/-- Canonical spectral-projector form.

Lean proof route for a weaker agent:

1. Combine the mirror-defect theorem with `reflectionDefect_le_two_mul_perturbation`; instantiate spectral subspaces or zero-padded unequal ranks afterward.
2. The operator-norm core should be a direct specialization of the supported reflection-defect theory.
-/
theorem sinTwoTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {Ω : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : InternalGap A (spectralSubspace A Ω) δ) :
    δ * N (sinTwoAngleOperator (spectralSubspace A Ω)
        (spectralSubspace B Ω)) ≤ 2 * N (B - A) := by
  exact sinTwoTheta_perturbation_le N hA hB
    (reduces_spectralSubspace A Ω) (reduces_spectralSubspace B Ω) hδ hgap

/-- Unequal-dimensional extension: zero padding records the unmatched
principal directions.

Lean proof route for a weaker agent:

1. Combine the mirror-defect theorem with `reflectionDefect_le_two_mul_perturbation`; instantiate spectral subspaces or zero-padded unequal ranks afterward.
2. The operator-norm core should be a direct specialization of the supported reflection-defect theory.
-/
theorem sinTwoTheta_perturbation_le_unequalFinrank
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  exact sinTwoTheta_perturbation_le N hA hB hU hV hδ hgap

/-- Operator-norm form.

Lean proof route for a weaker agent:

1. Instantiate the corrected every-UI perturbation theorem and simplify.
2. The op-norm case should eventually be a direct specialization of the supported `DavisKahan.ReflectionDefect` module.
-/
theorem opNorm_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * ‖(sinTwoAngleOperator U V).toContinuousLinearMap‖ ≤
      2 * ‖(B - A).toContinuousLinearMap‖ := by
  exact sinTwoTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 E)
    hA hB hU hV hδ hgap

/-- Frobenius form.

Lean proof route for a weaker agent:

1. Instantiate the corrected every-UI perturbation theorem and simplify.
2. The op-norm case should eventually be a direct specialization of the supported `DavisKahan.ReflectionDefect` module.
-/
theorem frobenius_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (sinTwoAngleOperator U V) ≤
      2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact sinTwoTheta_perturbation_le (UnitarilyInvariantNorm.frobenius 𝕜 E)
    hA hB hU hV hδ hgap

/-- Ky Fan form.

Lean proof route for a weaker agent:

1. Instantiate the corrected every-UI perturbation theorem and simplify.
2. The op-norm case should eventually be a direct specialization of the supported `DavisKahan.ReflectionDefect` module.
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
