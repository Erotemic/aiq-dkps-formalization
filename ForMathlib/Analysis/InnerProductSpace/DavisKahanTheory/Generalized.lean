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


/-! ## Remaining construction plan

For injective `X`, let `G = X.adjoint * X`.  Prove `G` is positive definite,
construct its positive inverse square root, and define
`orthonormalizedEmbedding X = X * G^{-1/2}`.  Verify the isometry identity
entrywise, prove the whitening factor is invertible, and obtain range equality
by postcomposition with that equivalence.  All generalized residual estimates
should then reduce to the isometric theory with explicit condition-number
bounds from the lower frame hypothesis.
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

/-- Symmetric compression after whitening a full-column-rank trial map.

If `X = Q G^{1/2}` is the polar/whitening factorization, this is `Q⋆ A Q`.
The coordinate Rayleigh quotient `(X⋆X)⁻¹ X⋆ A X` is similar to this operator
but is generally only self-adjoint for the Gram inner product. -/
noncomputable def generalizedCompression (A : E →ₗ[𝕜] E)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) : F →ₗ[𝕜] F :=
  compression A (orthonormalizedEmbedding X hX)

/-- The range is unchanged by orthonormalization.

Lean proof route for a weaker agent:

1. Unfold `orthonormalizedEmbedding` and name the positive Gram square root and its inverse.
2. Prove the whitening factor is a linear equivalence using `hX` and positivity of `X⋆X`.
3. Rewrite the isometry as `X` postcomposed with this equivalence and apply `LinearMap.range_comp_of_surjective`.
-/
theorem range_orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) :
    LinearMap.range (orthonormalizedEmbedding X hX).toLinearMap =
      LinearMap.range X := by
  sorry

/-- The whitened generalized compression is symmetric for a symmetric
ambient operator.

Lean proof route for a weaker agent:

1. Unfold `generalizedCompression`.
2. Apply `isSymmetric_compression hA` to the isometric factor
   `orthonormalizedEmbedding X hX`.
3. Keep any future theorem about `(X⋆X)⁻¹ X⋆ A X` separate and formulate it as
   Gram-self-adjointness or similarity to this compression.

Signature audit: Valid because the public compression is now the whitened
ordinary-self-adjoint operator.
-/
theorem isSymmetric_generalizedCompression {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (generalizedCompression A X hX).IsSymmetric := by
  exact isSymmetric_compression hA (orthonormalizedEmbedding X hX)

/-- Davis--Kahan Theorem 6.1: generalized `sin Θ` for non-orthonormal trial
vectors and unequal dimensions.

Lean proof route for a weaker agent:

1. Whiten `X = Q G^{1/2}`, convert the residual to the isometric embedding `Q`, apply the finite `sinTheta_residual_le`, and use the lower frame bound to control multiplication by `G^{1/2}`.
2. Establish the residual factorization `R_Q = R_X G⁻¹/²` as a separate lemma.
3. Apply the right ideal inequality and use `hframe` to bound `‖G⁻¹/²‖ ≤ ε⁻¹`; clear the positive denominators last.
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

Lean proof route for a weaker agent:

1. Set `Q := orthonormalizedEmbedding X hX` and rewrite its range using `range_orthonormalizedEmbedding`.
2. Derive the rectangular Sylvester equation for `sinThetaEmbedding U Q` and apply the Frobenius separated-spectrum estimate entrywise.
3. Factor the whitened residual through the Gram inverse square root, use `hframe` to control that factor, and clear `ε` with `hε`.
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

Lean proof route for a weaker agent:

1. Apply `generalizedSinTheta_frobenius_le_of_spectralDistance` to obtain the Hilbert--Schmidt bound.
2. Use the finite singular-value inequality `nuclear ≤ sqrt(rank) * frobenius` for the rectangular sine map.
3. Bound its rank by `finrank 𝕜 F`, preserve all nonnegativity side conditions, and simplify the scalar factors.
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

Lean proof route for a weaker agent:

1. Set `Q := orthonormalizedEmbedding X hX` and rewrite the range with
   `range_orthonormalizedEmbedding`.
2. Use `htrans` to construct the graph operator from `range Q` to `V`.
3. Derive the ordered tangent Sylvester equation for the Ritz pair
   `(Q, compression A Q)` and apply `tanTheta_residual_le`.
4. Simplify `generalizedCompression` and the residual definitions.

Signature audit: The theorem now uses the symmetric whitened compression and its matching
whitened residual.  The previous statement mixed whitened coordinates with the unwhitened
trial map.
-/
theorem generalizedTanTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    (hdim : finrank 𝕜 F ≤ finrank 𝕜 V)
    (htrans : IsTransverse
      (approximateSubspace (orthonormalizedEmbedding X hX)) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap (generalizedCompression A X hX) ⊤ A Vᗮ δ) :
    δ * N (tanThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (residual A (orthonormalizedEmbedding X hX)
        (generalizedCompression A X hX)) := by
  sorry

/-- The unequal-dimensional `sin 2Θ` extension mentioned after Theorem 8.2.

Lean proof route for a weaker agent:

1. Form the reflection across `U` and rewrite the double-angle embedding as the corresponding off-diagonal reflection block.
2. Apply the finite rectangular reflection-defect/Sylvester estimate under `InternalGap A U δ`.
3. Use the residual equation for `(X,M)` and UI ideal inequalities to bound the reflection defect by twice `N (residual A X M)`; unequal dimensions require only zero-padding in the final singular-value identification.
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

Lean proof route for a weaker agent:

1. Use `hselected` and `houtside` to obtain one fixed interval/exterior contour with clearance
   `δ` for every `t ∈ [0,1]`.
2. Specialize the experimental continuation/Riesz-projection module to the path
   `t ↦ A + t • H` and this fixed contour.
3. Identify the finite Riesz projection with `spectralProjection` by diagonalizing each
   symmetric operator.
4. Transfer continuity through the linear-map/continuous-linear-map coercion.

Signature audit: The fixed interval and uniform exterior buffer prevent eigenvalues from
crossing the selection boundary; the former hypothesis was tautological.
-/
theorem spectralSubspace_path_continuous
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hselected : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) (Set.Icc a b))
        (Set.Icc a b))
    (houtside : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) (Set.Icc a b))ᗮ
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    ContinuousOn (fun t : ℝ =>
      (spectralProjection (A + (t : 𝕜) • H) (Set.Icc a b)).toContinuousLinearMap)
      (Set.Icc 0 1) := by
  sorry

/-- Davis--Kahan Theorem 8.2: a quantitative half-gap bound selects the acute
branch of the `sin 2Θ` conclusion.

Lean proof route for a weaker agent:

1. Use the strengthened continuation theorem to keep the selected projector in the component of `U`, combine the half-gap perturbation bound with `‖P-Q‖ < 1`, and conclude `IsAcute`.
2. This should directly specialize the experimental bounded continuation layer.
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
