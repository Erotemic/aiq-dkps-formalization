/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Sylvester
import ForMathlib.Analysis.InnerProductSpace.SinThetaUINorm

/-!
# The complete finite-dimensional `sin Θ` theorem family

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 7, "The sin Theta theorem".
* Davis--Kahan (1970), Section 2 (`sin Θ`) and Section 6 (proof and symmetric
  extension).
* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`,
  Sections "The symmetric-matrix variant" and "Lower bound on the residual".

The residual theorem is the numerical analyst's form.  The perturbation
version is the operator theorist's form.  Both are stated for every relevant
unitarily invariant norm, followed by the interval, spectral-projector, and
concrete-norm corollaries expected from the final API.
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

/-! ## Residual form -/

/-- **Davis--Kahan `sin Θ`, residual form, every UI norm.**

The spectrum of the approximate coordinate operator `M` lies in `[a,b]`, the
unwanted spectrum of `A` on `Uᗮ` lies outside `(a-δ,b+δ)`, and `R = AX-XM`.
Then `δ ‖sin Θ‖ ≤ ‖R‖`.

Lean proof route for a weaker agent:

1. Project `AX-XM` into `Uᗮ`; reduction of `U` gives a Sylvester equation between `A|Uᗮ` and `M`.
2. Apply the interval/exterior finite UI Sylvester theorem and the projection ideal bound.
-/
theorem sinTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hMspec : SpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : SpectrumIn A Uᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  sorry

/-- Ordered half-line residual form.

Lean proof route for a weaker agent:

1. Project the residual onto `Uᗮ`, identify the ordered Sylvester equation, and apply `uiNorm_sylvester_le_of_orderedGap`.
2. The operator-norm core should later specialize `DavisKahanExt.sinTheta_residual`.
-/
theorem sinTheta_residual_le_of_orderedGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  sorry

/-- General disjoint-spectrum residual form.  The `π/2` loss is the
Bhatia--Davis--McIntosh extension, not the sharp interval/exterior theorem.

Lean proof route for a weaker agent:

1. Project the residual onto `Uᗮ`, obtain the rectangular Sylvester equation, apply `uiNorm_sylvester_le_of_spectralDistance`, and contract the projected residual.
2. Record the exact Sylvester equation as a named local equality before applying the general estimate.
3. Use the projection contraction and positivity of `δ` to normalize the final scalar inequality.
-/
theorem sinTheta_residual_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated M ⊤ A Uᗮ δ) :
    δ * N (sinThetaEmbedding U X) ≤ (Real.pi / 2) * N (residual A X M) := by
  sorry

/-! ## Perturbation form -/

/-- **Davis--Kahan `sin Θ`, perturbation form, every square UI norm.**

Lean proof route for a weaker agent:

1. Represent the perturbed reducing subspace by an isometric embedding, rewrite its residual as `(A-B)X`, apply the corresponding residual theorem, and contract composition by the embedding.
2. The operator-norm instance should be a thin specialization of `DavisKahanExt.SinTheta`.
-/
theorem sinTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  sorry

/-- **Symmetric `sin Θ` theorem.**  The full-space angle operator contains
both one-sided sine blocks.  Consequently the sharp full-space conclusion
requires the reverse mixed gap as well as the forward one; a single mixed gap
controls only `sinThetaMap U V` (except in the operator norm).  This is
Davis--Kahan Proposition 6.1.

Lean proof route for a weaker agent:

1. Apply the one-sided theorem in both directions, identify the two sine blocks of the full angle operator, and use the finite pinching/symmetric-gauge argument.
2. For operator norm, this should specialize `DavisKahanExt.sinTheta_symmetric`.
-/
theorem sinAngleOperator_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : HybridGap A B U V δ)
    (hgapVU : HybridGap B A V U δ) :
    δ * N (sinAngleOperator U V) ≤ N (B - A) := by
  sorry

/-- Ordered half-line perturbation form.

Lean proof route for a weaker agent:

1. Represent the perturbed reducing subspace by an isometric embedding, rewrite its residual as `(A-B)X`, apply the corresponding residual theorem, and contract composition by the embedding.
2. The operator-norm instance should be a thin specialization of `DavisKahanExt.SinTheta`.
-/
theorem sinTheta_perturbation_le_of_orderedGap
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  sorry

/-- Canonical spectral-projector statement with no eigenbasis in the API.

Lean proof route for a weaker agent:

1. Represent the perturbed reducing subspace by an isometric embedding, rewrite its residual as `(A-B)X`, apply the corresponding residual theorem, and contract composition by the embedding.
2. The operator-norm instance should be a thin specialization of `DavisKahanExt.SinTheta`.
-/
theorem sinTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hAselected : SpectrumIn A (spectralSubspace A (Set.Icc a b)) (Set.Icc a b))
    (hBoutside : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) := by
  sorry

/-- Difference-of-projectors operator-norm form.

Lean proof route for a weaker agent:

1. Combine the operator-norm one-sided `sin Θ` theorem with the equal-rank projection/cross-gap identity.
2. The analytic bound should specialize Ext; only the finite rank bridge remains local.
-/
theorem opNorm_projection_sub_projection_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hrank : finrank 𝕜 U = finrank 𝕜 V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * ‖(projection U - projection V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  sorry

/-- Frobenius form.

Lean proof route for a weaker agent:

1. Instantiate the every-UI perturbation theorem with the existing Frobenius or Ky Fan norm and simplify the evaluation theorem.
2. Instantiate `sinTheta_perturbation_le` with `UnitarilyInvariantNorm.frobenius`.
3. Rewrite the norm application with the Frobenius evaluation lemma and close by `simpa`.
-/
theorem frobenius_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (sinThetaMap U V) ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  sorry

/-- Ky Fan form, simultaneously controlling every singular-value prefix.

Lean proof route for a weaker agent:

1. Instantiate the every-UI perturbation theorem with the existing Frobenius or Ky Fan norm and simplify the evaluation theorem.
2. Instantiate `sinTheta_perturbation_le` with the finite Ky Fan UI norm.
3. Rewrite both applications using the Ky Fan evaluation theorem.
-/
theorem kyFan_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) (k : ℕ) :
    δ * kyFanSum k (sinThetaMap U V) ≤ kyFanSum k (B - A) := by
  sorry

/-- General two-sided spectral separation with the `π/2` constant.

Lean proof route for a weaker agent:

1. Use the residual equation and the general `π/2` Sylvester estimate.
2. Prefer the Ext general-separation theorem for operator norm and retain finite Fan dominance for arbitrary UI norms.
-/
theorem sinTheta_perturbation_le_of_spectralDistance
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ (Real.pi / 2) * N (B - A) := by
  sorry

end DavisKahanTheory
end ForMathlib
