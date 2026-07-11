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

Lean proof route for a weaker agent:

1. Use `hoff` and the reducing decompositions of `A` and `B` to derive the finite Riccati equation for the angular operator from `U` to `V`.
2. Prove the cosine-difference denominator is nonzero from `InternalGap A U δ`; this yields `AvoidsQuarterTurn U V` and legitimizes `tanTwoAngleOperator`.
3. Apply the ordered Sylvester/Ky Fan estimate to the Riccati identity and use finite Fan dominance to obtain the arbitrary UI-norm inequality.
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

Lean proof route for a weaker agent:

1. Use `hoff` and the reducing decompositions of `A` and `B` to derive the finite Riccati equation for the angular operator from `U` to `V`.
2. Prove the cosine-difference denominator is nonzero from `InternalGap A U δ`; this yields `AvoidsQuarterTurn U V` and legitimizes `tanTwoAngleOperator`.
3. Apply the ordered Sylvester/Ky Fan estimate to the Riccati identity and use finite Fan dominance to obtain the arbitrary UI-norm inequality.
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

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
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

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
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

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
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

Lean proof route for a weaker agent:

1. Use `horder` to orient `U` as the lower spectral block and `Uᗮ` as the upper block.
2. Write `Vᗮ` as the graph of the adjoint angular operator over `Uᗮ`; use `hoff` to compute the compression of `A+H` to that graph.
3. Compare the graph compression with the compression of `A` on `Uᗮ` by a positive congruence, then apply the finite min--max principle to obtain the spectral inclusion.

Signature audit: `horder` now identifies `U` as the lower block and fixes the direction of the
repulsion inequality.
-/
theorem spectral_repulsion_compression
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ) :
    SpectrumIn (A + H) Vᗮ
      {lam | ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam} := by
  sorry

/-- Theorem 8.1(ii): ordered eigenvalues move away from the gap.

Lean proof route for a weaker agent:

1. Apply `spectral_repulsion_compression` to obtain the spectral inclusion for the perturbed complementary block.
2. Unpack membership in `restrictedSpectrum (A+H) Vᗮ` and specialize that inclusion to the chosen eigenvalue `lam`.
3. Extract the witnessing unperturbed eigenvalue `μ`; no additional min--max argument should be repeated in this corollary.

Signature audit: The inherited ordered-gap premise fixes the eigenvalue comparison direction.
-/
theorem spectral_repulsion_eigenvalues
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ) :
    ∀ lam ∈ restrictedSpectrum (A + H) Vᗮ,
      ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam := by
  exact spectral_repulsion_compression hA hH hU hV hoff hacute hδ horder

/-- Theorem 8.1(iii): symmetric-gauge/UI-norm spectral repulsion.

Lean proof route for a weaker agent:

1. Express both compressed operators in eigenbases ordered compatibly with the lower/upper block orientation from `horder`.
2. Use `spectral_repulsion_eigenvalues` to obtain coordinatewise domination of the shifted nonnegative eigenvalues; prove the required singular-value prefix inequalities.
3. Apply finite Fan dominance to `N`, then rewrite the cosine compression and projection compositions into the displayed operators.

Signature audit: The ordered-gap premise fixes the block orientation; the proof must identify
the exact compressed operators before applying Fan dominance.
-/
theorem spectral_repulsion_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ)
    {c : ℝ} :
    N (projection Vᗮ ∘ₗ ((A + H) - (c : 𝕜) • LinearMap.id) ∘ₗ projection Vᗮ) ≥
      N (cosThetaMap Uᗮ Vᗮ ∘ₗ
        (projection Uᗮ ∘ₗ (A - (c : 𝕜) • LinearMap.id) ∘ₗ projection Uᗮ)) := by
  sorry

/-- Largest-angle consequence: the selected subspaces differ by less than
`π/4`.

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
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

Lean proof route for a weaker agent:

1. Apply `tanTwoTheta_perturbation_le` with the operator-norm UI instance.
2. Project the conjunction to obtain both `AvoidsQuarterTurn U V` and the norm estimate.
3. Rewrite the abstract norm applications with the operator-norm instance theorem and simplify scalar multiplication.
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
  exact tanTwoTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 E)
    hA hB hU hV hoff hδ hgap

/-- Frobenius endpoint.

Lean proof route for a weaker agent:

1. Apply `tanTwoTheta_perturbation_le` with the Frobenius UI instance.
2. Retain the pole-avoidance conjunct and rewrite the UI norm applications as Frobenius norms.
3. Normalize the factor `2` and use the established Frobenius instance simp lemmas; no new Riccati argument is needed.
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
  exact tanTwoTheta_perturbation_le (UnitarilyInvariantNorm.frobenius 𝕜 E)
    hA hB hU hV hoff hδ hgap

/-- Ky Fan endpoint.

Lean proof route for a weaker agent:

1. Apply the Ky Fan prefix inequality proved inside the all-UI `tanTwoTheta_perturbation_le` argument, or instantiate its Ky Fan norm object when available.
2. Preserve the `AvoidsQuarterTurn U V` conclusion from the parent theorem.
3. Rewrite the norm application as `kyFanSum k` and simplify the scalar factor termwise.
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
