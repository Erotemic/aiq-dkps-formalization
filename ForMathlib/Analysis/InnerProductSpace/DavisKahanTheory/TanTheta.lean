/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTheta
import ForMathlib.Analysis.InnerProductSpace.TanTheta

/-!
# The complete finite-dimensional `tan Θ` theorem family

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 8, "The tan Theta theorem".
* Davis--Kahan (1970), Section 2 (`tan Θ`) and Section 6 (proof, including
  Lemma 6.3 and the singular-value argument).
* `papers/DavisKahan-formalized-vs-literature.tex`, paragraph
  "The subspace tan Theta theorem" for the already formalized pole-free
  operator-norm route.

Unlike the present `TanTheta.lean` endpoint, the 1970 theorem is stated for
**every unitarily invariant norm**.  This scaffold therefore records the
singular-value/Ky Fan strengthening as the final target.
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

/-- The graph operator from an approximate subspace to the orthogonal
complement of an exact subspace. -/
noncomputable def graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- The graph operator realizes the tangent map.

Lean proof route for a weaker agent:

1. Preferred geometric route: specialize the unique angular-operator construction from `DavisKahanExt.GraphSubspace`, then identify its finite coordinate representation with `P_{Uᗮ}X(P_UX)⁻¹`.
2. Unfold both finite definitions after obtaining the inverse of the cosine block from `htrans`.
3. Prove equality by extensionality on the coordinate space and simplify the projection identities.
-/
theorem graphOperator_eq_tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    graphOperator U X = tanThetaEmbedding U X := by
  sorry

/-- The singular values of the graph operator are the principal tangents.

Lean proof route for a weaker agent:

1. Choose principal-vector bases for `U` and `approximateSubspace X`, and use `htrans` to show every cosine is nonzero.
2. In each principal two-plane, compute the graph block as the scalar quotient `sin θ / cos θ` and identify its singular value with `tan θ`.
3. Transport the block calculation back by unitary invariance, sort the finite list, and verify the zero-padding convention in `principalTangents`.
-/
theorem singularValues_graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    (graphOperator U X).singularValues =
      principalTangents U (approximateSubspace X) := by
  sorry

/-- **Davis--Kahan `tan Θ`, residual form, every UI norm.**

The Ritz/Galerkin condition eliminates the selected diagonal block.  Ordered
separation keeps the cosine block invertible and yields the sharp constant
one.

Lean proof route for a weaker agent:

1. Use Galerkin orthogonality to derive the graph Sylvester equation, apply the ordered UI Sylvester theorem, and identify the solution with the tangent map.
2. The graph existence/invertibility step should specialize `DavisKahanExt.GraphSubspace`.
-/
theorem tanTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) := by
  sorry

/-- The residual hypotheses force transversality; the tangent has no pole.

Lean proof route for a weaker agent:

1. Suppose `x` lies in `range X` and `projection U x = 0`.
2. Write `x = X y`; the projected residual equation and `hGalerkin` give a homogeneous ordered
   Sylvester equation for this vector.
3. Use `hgap` and `hδ` to force `y = 0`, hence `x = 0`.
4. Unfold `IsTransverse`; it is intentionally the one-sided injectivity predicate, so no
   equal-dimension hypothesis is needed.

Signature audit: Valid with the current one-sided definition of `IsTransverse`.
-/
theorem isTransverse_of_tanTheta_residual_gap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    IsTransverse (approximateSubspace X) U := by
  sorry

/-- **Davis--Kahan `tan Θ`, perturbation form, every UI norm.**

Lean proof route for a weaker agent:

1. Convert the reducing subspace of `B` into a graph over `U`, use the zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual theorem.
2. Reuse Ext graph/Riccati geometry for the operator-norm skeleton; keep UI singular values finite.

Signature audit: `hacute` now supplies the domain on which the full finite tangent operator
represents the principal tangents without a `π/2` pole.
-/
theorem tanTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanAngleOperator U V) ≤ N (B - A) := by
  sorry

/-- Cross/graph form of the perturbation theorem.

Lean proof route for a weaker agent:

1. Convert the reducing subspace of `B` into a graph over `U`, use the zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual theorem.
2. Reuse Ext graph/Riccati geometry for the operator-norm skeleton; keep UI singular values finite.
-/
theorem tanThetaMap_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (htrans : IsTransverse U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanThetaMap U V) ≤ N (B - A) := by
  sorry

/-- Canonical spectral-subspace version.

Lean proof route for a weaker agent:

1. Convert the reducing subspace of `B` into a graph over `U`, use the zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual theorem.
2. Reuse Ext graph/Riccati geometry for the operator-norm skeleton; keep UI singular values finite.

Signature audit: `hacute` explicitly selects the transverse spectral branch.  A later
continuation theorem may derive this premise in common applications.
-/
theorem tanTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hzero : HasZeroCompression (spectralSubspace A (Set.Icc a b)) (B - A))
    (hacute : IsAcute (spectralSubspace A (Set.Icc a b))
      (spectralSubspace B (Set.Icc a b)))
    (hgap : OrderedGap A (spectralSubspace A (Set.Icc a b))
      B (spectralSubspace B (Set.Icc a b))ᗮ δ) :
    δ * N (tanAngleOperator (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) := by
  sorry

/-- Pole-free vector form.  This is the theorem shape already approached in
`ForMathlib/Analysis/InnerProductSpace/TanTheta.lean`.

Lean proof route for a weaker agent:

1. Rewrite `M` using `hGalerkin`, then project `A X y - X M y` onto `U` and `Uᗮ`.
2. Apply the pole-free vector estimate from the older `TanTheta.lean` to `X y`; use `hgap` to supply its ordered spectral separation premise.
3. Bound the residual by `hres`, simplify `‖X y‖ = ‖y‖`, and keep the cosine factor on the right instead of dividing by it.

Signature audit: The added `hGalerkin` premise supplies the projected-residual cancellation
needed for the pole-free vector inequality.
-/
theorem tanTheta_vector_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ ρ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap M ⊤ A Uᗮ δ)
    (hres : ∀ y, ‖residual A X M y‖ ≤ ρ * ‖y‖) :
    ∀ y, δ * ‖sinThetaEmbedding U X y‖ ≤
      ρ * ‖cosThetaEmbedding U X y‖ := by
  sorry

/-- Operator-norm largest-angle form.

Lean proof route for a weaker agent:

1. Apply `tanTheta_perturbation_le` with the concrete operator-norm `UnitarilyInvariantNorm` instance.
2. Rewrite the abstract norm of `tanAngleOperator U V` and `B-A` using the instance's application theorem.
3. Preserve `hacute` through the specialization; do not divide by a cosine or re-prove graph existence in this wrapper.

Signature audit: The explicit `hacute` premise makes the full-space tangent operator a valid
finite principal-angle object.
-/
theorem opNorm_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * ‖(tanAngleOperator U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  sorry

/-- Frobenius `tan Θ` form.

Lean proof route for a weaker agent:

1. Apply `tanTheta_perturbation_le` with the concrete operator-norm `UnitarilyInvariantNorm` instance.
2. Rewrite the abstract norm of `tanAngleOperator U V` and `B-A` using the instance's application theorem.
3. Preserve `hacute` through the specialization; do not divide by a cosine or re-prove graph existence in this wrapper.

Signature audit: The explicit `hacute` premise rules out tangent poles; the proof should still
pass through the one-sided graph singular values.
-/
theorem frobenius_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanAngleOperator U V) ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  sorry

/-- Ky Fan `tan Θ` form.

Lean proof route for a weaker agent:

1. Apply `tanTheta_perturbation_le` with the concrete operator-norm `UnitarilyInvariantNorm` instance.
2. Rewrite the abstract norm of `tanAngleOperator U V` and `B-A` using the instance's application theorem.
3. Preserve `hacute` through the specialization; do not divide by a cosine or re-prove graph existence in this wrapper.

Signature audit: The explicit `hacute` premise rules out tangent poles; the proof should still
pass through the one-sided graph singular values.
-/
theorem kyFan_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) (k : ℕ) :
    δ * kyFanSum k (tanAngleOperator U V) ≤ kyFanSum k (B - A) := by
  sorry

end DavisKahanTheory
end ForMathlib
