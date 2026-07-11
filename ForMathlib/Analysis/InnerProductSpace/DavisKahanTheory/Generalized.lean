/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTwoTheta

/-!
# Generalized finite-dimensional Davis--Kahan theorems

This file records the finite-dimensional forms of the generalizations stated
after the four headline theorems in Davis--Kahan (1970).

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 5--11.
* Davis--Kahan (1970), Theorems 6.1--6.3 and 8.2.

The important extra features are non-orthonormal trial vectors, comparison of
subspaces of unequal dimension, the square-norm fallback under arbitrary
spectral separation, and the continuation argument selecting the acute branch
of a double-angle estimate.  These are kept separate from the sharp clean API
so their conditioning losses are visible in theorem statements.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators Topology
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- A quantitative lower frame bound for a not-necessarily-isometric trial
map.  Davis--Kahan's parameter `e` is this lower singular-value bound. -/
def LowerFrameBound (X : F →ₗ[𝕜] E) (ε : ℝ) : Prop :=
  ∀ y, ε * ‖y‖ ≤ ‖X y‖

/-- Residual for a general trial map. -/
noncomputable def generalResidual (A : E →ₗ[𝕜] E) (X : F →ₗ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X - X ∘ₗ M

/-- Isometric factor in the polar decomposition of an injective trial map. -/
noncomputable def orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : F →ₗᵢ[𝕜] E := by
  sorry

/-- Generalized Rayleigh--Ritz compression for a full-column-rank trial map,
`(X⋆X)⁻¹ X⋆ A X`. -/
noncomputable def generalizedCompression (A : E →ₗ[𝕜] E)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) : F →ₗ[𝕜] F := by
  sorry

/-- The range is unchanged by orthonormalization.

Proof strategy: Expand the polar/whitening factor of `X`; its positive Gram factor is invertible
under injectivity, so postcomposition by that automorphism does not change the range.
-/
theorem range_orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) :
    LinearMap.range (orthonormalizedEmbedding X hX).toLinearMap =
      LinearMap.range X := by
  sorry

/-- The generalized compression is symmetric for a symmetric ambient
operator.

Proof strategy: Do not prove the current statement. Replace it by Gram-self-adjointness or by
symmetry of the whitened compression, then prove it by moving adjoints through the Gram square
root.

Signature audit: False for `(X⋆X)⁻¹ X⋆ A X` in the ordinary inner product unless the Gram matrix
commutes with `X⋆AX`. The correct target is Gram-self-adjointness, or ordinary symmetry of the
whitened compression `(X⋆X)⁻¹/² X⋆ A X (X⋆X)⁻¹/²`.
-/
theorem isSymmetric_generalizedCompression {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (generalizedCompression A X hX).IsSymmetric := by
  sorry

/-- Davis--Kahan Theorem 6.1: generalized `sin Θ` for non-orthonormal trial
vectors and unequal dimensions.

Proof strategy: Whiten `X = Q G^{1/2}`, convert the residual to the isometric embedding `Q`,
apply the finite `sinTheta_residual_le`, and use the lower frame bound to control multiplication
by `G^{1/2}`.
-/
theorem generalizedSinTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hMspec : SpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : SpectrumIn A Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (generalResidual A X M) := by
  sorry

/-- Davis--Kahan Theorem 6.2: under arbitrary spectral separation the sharp
all-UI conclusion is replaced by the Hilbert--Schmidt/square-norm estimate.

Proof strategy: Whiten the trial map, apply the entrywise/Frobenius Sylvester estimate under
absolute separation, and use the lower frame bound. This is finite and should not wait for
infinite symmetric ideals.
-/
theorem generalizedSinTheta_frobenius_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectraSeparated M ⊤ A Vᗮ δ) :
    δ * ε * RectangularUnitarilyInvariantNorm.frobenius
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      RectangularUnitarilyInvariantNorm.frobenius
        (generalResidual A X M) := by
  sorry

/-- Trace/nuclear fallback obtained from the square-norm estimate and rank.

Proof strategy: Combine the preceding Frobenius theorem with `‖T‖₁ ≤ sqrt(rank T) ‖T‖₂`; bound
the rank by `finrank F`.
-/
theorem generalizedSinTheta_nuclear_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectraSeparated M ⊤ A Vᗮ δ) :
    δ * ε * RectangularUnitarilyInvariantNorm.nuclear
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      Real.sqrt (finrank 𝕜 F) *
        RectangularUnitarilyInvariantNorm.frobenius
          (generalResidual A X M) := by
  sorry

/-- Davis--Kahan Theorem 6.3: generalized `tan Θ`, allowing the exact target
subspace to have larger dimension than the trial space.

Proof strategy: After correcting the compression, whiten the trial map and specialize the
bounded graph/Riccati geometry from `DavisKahanExt.GraphSubspace`; finish the arbitrary-UI
estimate with the finite Sylvester/Ky Fan theorem.

Signature audit: Depends on the preceding false ordinary-symmetry model. Restate using the
whitened compression and whitened residual, or formulate the Sylvester equation in the Gram
inner product.
-/
theorem generalizedTanTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    (hdim : finrank 𝕜 F ≤ finrank 𝕜 V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap (generalizedCompression A X hX) ⊤ A Vᗮ δ) :
    δ * N (tanThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (generalResidual A X (generalizedCompression A X hX)) := by
  sorry

/-- The unequal-dimensional `sin 2Θ` extension mentioned after Theorem 8.2.

Proof strategy: Apply the residual reflection theorem to the isometric embedding `X`; the
operator-norm core can specialize `DavisKahanExt.sinTwoTheta_residual`, while zero padding and
arbitrary UI norms remain finite.
-/
theorem generalizedSinTwoTheta_unequalFinrank
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  sorry

/-- Spectral projectors along the homotopy `A+tH` stay on one isolated branch.

Proof strategy: After strengthening the hypothesis to a uniform contour/gap, specialize
`DavisKahanExt.continuous_rieszProjection_path` and `rieszProjection_eq_spectralProjection`
through the finite bridge.

Signature audit: False/underdetermined: the current `hisolated` hypothesis is essentially
tautological and gives no uniform gap. Require a fixed separating contour or a positive uniform
distance from `Ω` to the complementary spectrum, and usually constant rank.
-/
theorem spectralSubspace_path_continuous
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (Ω : Set ℝ)
    (hisolated : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H) (spectralSubspace (A + (t : 𝕜) • H) Ω) Ω) :
    ContinuousOn (fun t : ℝ =>
      (spectralProjection (A + (t : 𝕜) • H) Ω).toContinuousLinearMap)
      (Set.Icc 0 1) := by
  sorry

/-- Davis--Kahan Theorem 8.2: a quantitative half-gap bound selects the acute
branch of the `sin 2Θ` conclusion.

Proof strategy: Use the strengthened continuation theorem to keep the selected projector in the
component of `U`, combine the half-gap perturbation bound with `‖P-Q‖ < 1`, and conclude
`IsAcute`. This should directly specialize the bounded Ext continuation layer.
-/
theorem sinTwoTheta_acute_of_small_perturbation
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hUcentral : SpectrumIn A U (Set.Icc (a - δ / 2) (b + δ / 2)))
    (hUoutside : SpectrumIn A Uᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)})
    (hsmall : ‖H.toContinuousLinearMap‖ < δ / 2) :
    IsAcute U (spectralSubspace (A + H) (Set.Icc (a - δ / 2) (b + δ / 2))) := by
  sorry

end DavisKahanTheory
end ForMathlib
