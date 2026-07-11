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

Proof strategy: Preferred geometric route: specialize the unique angular-operator construction
from `DavisKahanExt.GraphSubspace`, then identify its finite coordinate representation with
`P_{Uᗮ}X(P_UX)⁻¹`.
-/
theorem graphOperator_eq_tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    graphOperator U X = tanThetaEmbedding U X := by
  sorry

/-- The singular values of the graph operator are the principal tangents.

Proof strategy: Use the finite principal-plane decomposition of the graph: each cosine/sine pair
gives a singular value `tan θ`; then sort and pad the list.
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

Proof strategy: Use Galerkin orthogonality to derive the graph Sylvester equation, apply the
ordered UI Sylvester theorem, and identify the solution with the tangent map. The graph
existence/invertibility step should specialize `DavisKahanExt.GraphSubspace`.
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

Proof strategy: After correcting the conclusion or adding equal dimension, use the homogeneous
ordered Sylvester equation to rule out a kernel of the cosine block; finite dimension then
upgrades one-sided injectivity to transversality.

Signature audit: False for the symmetric two-sided `IsTransverse` predicate without equal
dimension. The ordered residual equation gives injectivity of the cosine map on the trial space;
add `finrank F = finrank U` or conclude only one-sided transversality.
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

Proof strategy: Convert the reducing subspace of `B` into a graph over `U`, use the
zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual
theorem. Reuse Ext graph/Riccati geometry for the operator-norm skeleton; keep UI singular
values finite.

Signature audit: The full ambient `tanAngleOperator` needs transversality/equal-defect data and
is not a bounded operator for arbitrary pairs. Prefer the one-sided graph/tangent map, or add
equal-rank plus a proved acute/transverse conclusion.
-/
theorem tanTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanAngleOperator U V) ≤ N (B - A) := by
  sorry

/-- Cross/graph form of the perturbation theorem.

Proof strategy: Convert the reducing subspace of `B` into a graph over `U`, use the
zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual
theorem. Reuse Ext graph/Riccati geometry for the operator-norm skeleton; keep UI singular
values finite.
-/
theorem tanThetaMap_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanThetaMap U V) ≤ N (B - A) := by
  sorry

/-- Canonical spectral-subspace version.

Proof strategy: Convert the reducing subspace of `B` into a graph over `U`, use the
zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual
theorem. Reuse Ext graph/Riccati geometry for the operator-norm skeleton; keep UI singular
values finite.

Signature audit: The full ambient tangent requires a proved transverse/equal-rank branch. The
current gap and zero-compression hypotheses do not state that the selected spectral subspaces
have matching dimension.
-/
theorem tanTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hzero : HasZeroCompression (spectralSubspace A (Set.Icc a b)) (B - A))
    (hgap : OrderedGap A (spectralSubspace A (Set.Icc a b))
      B (spectralSubspace B (Set.Icc a b))ᗮ δ) :
    δ * N (tanAngleOperator (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) := by
  sorry

/-- Pole-free vector form.  This is the theorem shape already approached in
`ForMathlib/Analysis/InnerProductSpace/TanTheta.lean`.

Proof strategy: After adding the missing Galerkin cancellation, project the residual equation
onto `U` and `Uᗮ`, pair with the relevant vector, and apply the ordered quadratic-form gap. This
follows the already proved pole-free vector theorem in the older `TanTheta.lean`.

Signature audit: False without the Galerkin/zero-compression hypothesis. For example, a trial
vector entirely in `Uᗮ` can satisfy the ordered gap while the right-hand cosine factor vanishes.
Add `M = compression A X` or the corresponding projected-residual cancellation.
-/
theorem tanTheta_vector_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ρ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap M ⊤ A Uᗮ δ)
    (hres : ∀ y, ‖residual A X M y‖ ≤ ρ * ‖y‖) :
    ∀ y, δ * ‖sinThetaEmbedding U X y‖ ≤
      ρ * ‖cosThetaEmbedding U X y‖ := by
  sorry

/-- Operator-norm largest-angle form.

Proof strategy: Derive this from the corrected every-UI graph/tangent theorem by instantiating
the corresponding norm; the operator-norm geometric portion should specialize the Ext
graph-subspace result.

Signature audit: Inherits the boundedness/domain issue of `tanAngleOperator`; prove a one-sided
graph-operator theorem first, then add equal-rank/transversality before exposing the full-space
operator.
-/
theorem opNorm_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * ‖(tanAngleOperator U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  sorry

/-- Frobenius `tan Θ` form.

Proof strategy: Derive this from the corrected every-UI graph/tangent theorem by instantiating
the corresponding norm; the operator-norm geometric portion should specialize the Ext
graph-subspace result.

Signature audit: Inherits the boundedness/domain issue of `tanAngleOperator`; the final UI
statement should be phrased through the finite graph/tangent singular values after proving
transversality.
-/
theorem frobenius_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanAngleOperator U V) ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  sorry

/-- Ky Fan `tan Θ` form.

Proof strategy: Derive this from the corrected every-UI graph/tangent theorem by instantiating
the corresponding norm; the operator-norm geometric portion should specialize the Ext
graph-subspace result.

Signature audit: Inherits the boundedness/domain issue of `tanAngleOperator`; the final UI
statement should be phrased through the finite graph/tangent singular values after proving
transversality.
-/
theorem kyFan_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) (k : ℕ) :
    δ * kyFanSum k (tanAngleOperator U V) ≤ kyFanSum k (B - A) := by
  sorry

end DavisKahanTheory
end ForMathlib
