/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Forms

/-!
# Compact operators, Schatten consequences, and singular subspaces

Literature writeup: local TeX, Sections 32--34.  This module connects the
Hilbert-space theory to compact covariance operators and Wedin-type singular
subspace perturbation through Hermitian dilation.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Compact self-adjoint spectral block. -/
noncomputable def compactSpectralSubspace (A : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E := by
  sorry

/-- Compact perturbations produce compact differences of isolated spectral
projections. 

Lean proof route for a weaker agent:

1. Apply the two mixed-gap `sinTheta_symmetric` argument at the operator level.
2. Express the projector difference as the image of `B-A` under the inverse Sylvester map on the off-diagonal blocks.
3. Use the compact ideal property and closure under sums/adjoints to prove compactness of both blocks and hence of the full difference.
-/
theorem compact_projection_difference
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) {d : ℝ} (hd : 0 < d)
    (hsepAB : SpectraSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ d)
    (hsepBA : SpectraSeparated B (spectralSubspace B t)
      A (spectralSubspace A s)ᗮ d)
    (hcompact : (SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)).mem (B - A)) :
    (SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)).mem
      (spectralProjection A s - spectralProjection B t) := by
  sorry

/-- Schatten-class perturbation implies Schatten-class angle operator. 

Lean proof route for a weaker agent:

1. Instantiate `ideal_sinTheta` with the Schatten ideal at `p` and `hp`.
2. Supply `hmem` and the two mixed interval/exterior gaps.
3. Extract the membership and numerical components; normalize the factor `d` to the displayed form.
-/
theorem schatten_sinTheta
    (p : ℝ) (hp : 1 ≤ p) {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).mem (B - A)) :
    (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).mem
        (sinAngleOperator U V) ∧
      d * (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).gauge
        (sinAngleOperator U V) ≤
      (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).gauge (B - A) := by
  sorry

/-- Hermitian dilation of a rectangular bounded operator. -/
noncomputable def hermitianDilation (T : E →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := by
  sorry

/-- The Hermitian dilation is self-adjoint. 

Lean proof route for a weaker agent:

1. Expand the `2×2` block definition of `hermitianDilation`.
2. Compute the inner product of `D(T)(x,y)` with `(x',y')`.
3. Move `T` across the inner product using its continuous adjoint and rearrange terms.
4. Finish by extensionality of the product inner product.
-/
theorem hermitianDilation_selfAdjoint (T : E →L[𝕜] F) :
    IsSelfAdjointOperator (hermitianDilation T) := by
  sorry

/-- Infinite-dimensional Wedin theorem for isolated singular spectral sets.

Proof strategy: construct the Hermitian dilation
`D(T) = [[0,T*],[T,0]]`, prove it is self-adjoint, and identify its positive and
negative spectral subspaces with the left/right singular subspaces of `T`.
Observe `D(T)-D(S)=D(T-S)` and prove `‖D(T-S)‖=‖T-S‖`.  Apply the self-adjoint
`sin Theta` theorem to the isolated spectral sets and project the resulting
block estimate back to the desired left or right singular subspace. 

Lean proof route for a weaker agent:

1. Prove the Hermitian dilations are self-adjoint and their difference is the dilation of `T-S`.
2. Apply the symmetric spectral-projection `sinTheta` theorem using both mixed gaps.
3. Prove `‖hermitianDilation (T-S)‖=‖T-S‖` if a rectangular statement is desired.
4. Project the dilation subspace estimate to left/right singular subspaces in later corollaries.
-/
theorem wedin_singularSubspace
    {S T : E →L[𝕜] F} (s t : Set ℝ)
    {d : ℝ} (hd : 0 < d)
    (hsepST : SpectraSeparated (hermitianDilation S)
      (spectralSubspace (hermitianDilation S) s)
      (hermitianDilation T)
      (spectralSubspace (hermitianDilation T) t)ᗮ d)
    (hsepTS : SpectraSeparated (hermitianDilation T)
      (spectralSubspace (hermitianDilation T) t)
      (hermitianDilation S)
      (spectralSubspace (hermitianDilation S) s)ᗮ d) :
    d * ‖spectralProjection (hermitianDilation S) s -
      spectralProjection (hermitianDilation T) t‖ ≤
      ‖hermitianDilation (T - S)‖ := by
  sorry

/-- Covariance-operator principal-subspace perturbation. 

Lean proof route for a weaker agent:

1. Instantiate `spectralProjection_sinTheta` with the two supplied interval/exterior gaps.
2. Rewrite the abstract spectral subspaces and projections to the covariance-operator notation.
3. Finish by ring normalization of the factor `d`.
-/
theorem covariance_subspace_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hsepAB : IntervalExteriorSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ left right d)
    (hsepBA : IntervalExteriorSeparated B (spectralSubspace B t)
      A (spectralSubspace A s)ᗮ left' right' d) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤ ‖B - A‖ := by
  sorry

end DavisKahanExt
end ForMathlib
