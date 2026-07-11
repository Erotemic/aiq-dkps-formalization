/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTwoTheta
import ForMathlib.Analysis.InnerProductSpace.TanTwoTheta

/-!
# The complete finite-dimensional `tan (2 Θ)` theorem family

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 10--11.
* Davis--Kahan (1970), Section 2 (`tan 2Θ`), Section 7 (proof), and
  Theorem 8.1 (selection of the correct perturbed spectral subspace and
  spectral repulsion).
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, Section
  "The sharp two-subspace estimate" for the one-vector ancestor.

The current `TanTwoTheta.lean` proves the largest-angle/operator-norm endpoint.
The final classic theorem is stronger: it is stated for every unitarily
invariant norm and has both residual and perturbation conclusions.
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

/-- **Davis--Kahan `tan 2Θ`, residual form, every UI norm.**

Here `X` spans a reducing subspace of the perturbed operator `B`, while the
perturbation `B-A` is fully off diagonal relative to the unperturbed splitting
`U ⊕ Uᗮ`.  The theorem itself excludes quarter-turn angles; acuteness is not a
hypothesis for the raw double-angle theorem.

Proof strategy: Use the off-diagonal block equation and the graph/Riccati representation to
identify `tan (2Θ)`; apply the ordered internal-gap Sylvester estimate. Prefer the operator-norm
skeleton from `DavisKahanExt.Riccati` and `OffDiagonal`, then prove finite UI domination
separately.
-/
theorem tanTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurnEmbedding U X ∧
      δ * N (tanTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  sorry

/-- **Davis--Kahan `tan 2Θ`, perturbation form, every UI norm.**

For an arbitrary reducing subspace `V`, angles may lie on either side of
`π/4`.  The theorem proves that no angle equals `π/4` and bounds the norm of
`tan (2Θ)`; the later spectral-selection theorem chooses the acute branch.

Proof strategy: Use the off-diagonal block equation and the graph/Riccati representation to
identify `tan (2Θ)`; apply the ordered internal-gap Sylvester estimate. Prefer the operator-norm
skeleton from `DavisKahanExt.Riccati` and `OffDiagonal`, then prove finite UI domination
separately.
-/
theorem tanTwoTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * N (tanTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  sorry

/-- The off-diagonal hypotheses and the canonical same-cut spectral choice
imply the acute-angle condition.  This is the branch selection in
Davis--Kahan Theorem 8.1.

Proof strategy: Specialize the continuation and off-diagonal branch-selection results from
`DavisKahanExt.Continuation` and `OffDiagonal`; identify the finite spectral projector with the
eigenvector-span projector, then apply the graph-angle theorem.
-/
theorem isAcute_canonical_tanTwoTheta
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    IsAcute U (spectralSubspace (A + H) (Set.Iic a)) := by
  sorry

/-- Canonical spectral-subspace `tan 2Θ` theorem, with the acute conclusion
built in and the same spectral cut used for `A` and `A+H`.

Proof strategy: Specialize the continuation and off-diagonal branch-selection results from
`DavisKahanExt.Continuation` and `OffDiagonal`; identify the finite spectral projector with the
eigenvector-span projector, then apply the graph-angle theorem.
-/
theorem tanTwoTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    let V := spectralSubspace (A + H) (Set.Iic a)
    IsAcute U V ∧
      (b - a) * N (tanTwoAngleOperator U V) ≤ 2 * N H := by
  sorry

/-! ## Davis--Kahan Theorem 8.1: spectral selection and repulsion -/

/-- Existence and uniqueness of the reducing projector on the correct side of
an off-diagonal gap.

Proof strategy: Specialize the continuation and off-diagonal branch-selection results from
`DavisKahanExt.Continuation` and `OffDiagonal`; identify the finite spectral projector with the
eigenvector-span projector, then apply the graph-angle theorem.
-/
theorem existsUnique_reducingSubspace_preserving_gap
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    ∃! V : Submodule 𝕜 E,
      Reduces (A + H) V ∧
      SpectrumIn (A + H) V (Set.Iic a) ∧
      SpectrumIn (A + H) Vᗮ (Set.Ici b) ∧
      IsAcute U V := by
  sorry

/-- Theorem 8.1(i): compression comparison through the cosine block.

Proof strategy: First add the missing ordered orientation. Then use the cosine-block
intertwining/compression formula from the selected graph subspace; derive eigenvalue
monotonicity by min--max and the UI statement by singular-value majorization.

Signature audit: False without an orientation hypothesis identifying `U` as the lower or upper
block. Reversing the ordered blocks reverses the claimed eigenvalue inequality. Add
half-line/ordered spectral bounds such as `SpectrumIn A U (Iic a)` and `SpectrumIn A Uᗮ (Ici
b)`.
-/
theorem spectral_repulsion_compression
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V) :
    SpectrumIn (A + H) Vᗮ
      {lam | ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam} := by
  sorry

/-- Theorem 8.1(ii): ordered eigenvalues move away from the gap.

Proof strategy: First add the missing ordered orientation. Then use the cosine-block
intertwining/compression formula from the selected graph subspace; derive eigenvalue
monotonicity by min--max and the UI statement by singular-value majorization.

Signature audit: False without the same ordered-block orientation required by the compression
form. Add the lower/upper spectral enclosure hypotheses.
-/
theorem spectral_repulsion_eigenvalues
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V) :
    ∀ lam ∈ restrictedSpectrum (A + H) Vᗮ,
      ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam := by
  sorry

/-- Theorem 8.1(iii): symmetric-gauge/UI-norm spectral repulsion.

Proof strategy: First add the missing ordered orientation. Then use the cosine-block
intertwining/compression formula from the selected graph subspace; derive eigenvalue
monotonicity by min--max and the UI statement by singular-value majorization.

Signature audit: Underdetermined without an ordered-block orientation and a precise compression
identification. The direction of the UI-norm comparison changes when the two diagonal blocks are
exchanged.
-/
theorem spectral_repulsion_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V) {c : ℝ} :
    N (projection Vᗮ ∘ₗ ((A + H) - (c : 𝕜) • LinearMap.id) ∘ₗ projection Vᗮ) ≥
      N (cosThetaMap Uᗮ Vᗮ ∘ₗ
        (projection Uᗮ ∘ₗ (A - (c : 𝕜) • LinearMap.id) ∘ₗ projection Uᗮ)) := by
  sorry

/-- Largest-angle consequence: the selected subspaces differ by less than
`π/4`.

Proof strategy: Specialize the continuation and off-diagonal branch-selection results from
`DavisKahanExt.Continuation` and `OffDiagonal`; identify the finite spectral projector with the
eigenvector-span projector, then apply the graph-angle theorem.
-/
theorem largestPrincipalAngle_lt_pi_div_four
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    principalAngles U (spectralSubspace (A + H) (Set.Iic a)) 0 <
      Real.pi / 4 := by
  sorry

/-- Operator-norm endpoint already represented by `TanTwoTheta.lean`.

Proof strategy: Instantiate the corrected every-UI `tan 2Θ` theorem. The op-norm branch/graph
part should specialize Ext; Frobenius and Ky Fan remain finite singular-value corollaries.
-/
theorem opNorm_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * ‖(tanTwoAngleOperator U V).toContinuousLinearMap‖ ≤
        2 * ‖(B - A).toContinuousLinearMap‖ := by
  sorry

/-- Frobenius endpoint.

Proof strategy: Instantiate the corrected every-UI `tan 2Θ` theorem. The op-norm branch/graph
part should specialize Ext; Frobenius and Ky Fan remain finite singular-value corollaries.
-/
theorem frobenius_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanTwoAngleOperator U V) ≤
        2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  sorry

/-- Ky Fan endpoint.

Proof strategy: Instantiate the corrected every-UI `tan 2Θ` theorem. The op-norm branch/graph
part should specialize Ext; Frobenius and Ky Fan remain finite singular-value corollaries.
-/
theorem kyFan_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ)
    (k : ℕ) :
    AvoidsQuarterTurn U V ∧
      δ * kyFanSum k (tanTwoAngleOperator U V) ≤ 2 * kyFanSum k (B - A) := by
  sorry

end DavisKahanTheory
end ForMathlib
