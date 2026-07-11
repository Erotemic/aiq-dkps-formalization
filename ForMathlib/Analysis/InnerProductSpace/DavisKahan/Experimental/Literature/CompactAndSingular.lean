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


Ext-agent signature audit (GPT 5.6 High): Correct with two mixed separations and
measurable sets. General separated spectra suffice for ideal membership even when the
sharp constant-one norm estimate is unavailable.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem compact_projection_difference
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {d : ℝ} (hd : 0 < d)
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


Ext-agent signature audit (GPT 5.6 High): Correct only if `ideal_sinTheta` establishes
the full ambient sine operator with matched adjoint-block multiplicity. Keep `1≤p`;
values below one are quasi-norms.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
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


Ext-agent signature audit (GPT 5.6 High): Correct. The definition must use the Hilbert
`L²` direct sum and place `T*` and `T` in the proper blocks.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem hermitianDilation_selfAdjoint (T : E →L[𝕜] F) :
    IsSelfAdjointOperator (hermitianDilation T) := by
  sorry

/-- Hermitian-dilation spectral-projection bound underlying Wedin's theorem.

This is intentionally named as an intermediate result: separate left and right
singular-subspace definitions and their projection correspondences are still needed
before exposing a theorem called `wedin_singularSubspace`.

Proof strategy: construct the Hermitian dilation
`D(T) = [[0,T*],[T,0]]`, prove it is self-adjoint, and identify its positive and
negative spectral subspaces with the left/right singular subspaces of `T`.
Observe `D(T)-D(S)=D(T-S)` and prove `‖D(T-S)‖=‖T-S‖`.  Apply the self-adjoint
`sin Theta` theorem to the isolated spectral sets and project the resulting
block estimate back to the desired left or right singular subspace. 

Lean proof route for a weaker agent:

1. Prove the Hermitian dilations are self-adjoint and their difference is the dilation of `T-S`.
2. Apply the general separated spectral-projection `sinTheta` theorem in both directions, retaining the `π/2` constant.
3. Prove `‖hermitianDilation (T-S)‖=‖T-S‖` if a rectangular statement is desired.
4. Project the dilation subspace estimate to left/right singular subspaces in later corollaries.


Ext-agent signature audit (GPT 5.6 High): This is presently a Hermitian-dilation
spectral-projection theorem, not yet a left/right singular-subspace theorem. Its arbitrary
separated-set hypotheses require the generic `π/2` constant; ordered singular clusters can
support a later constant-one Wedin specialization.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem hermitianDilation_spectralProjection_sinTheta
    {S T : E →L[𝕜] F} (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
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
      (Real.pi / 2) * ‖hermitianDilation (T - S)‖ := by
  sorry

/-- Covariance-operator principal-subspace perturbation. 

Lean proof route for a weaker agent:

1. Instantiate `spectralProjection_sinTheta` with the two supplied interval/exterior gaps.
2. Rewrite the abstract spectral subspaces and projections to the covariance-operator notation.
3. Finish by ring normalization of the factor `d`.


Ext-agent signature audit (GPT 5.6 High): Correct as a thin specialization of the
canonical spectral-projection theorem; covariance positivity is not needed for the
abstract estimate.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem covariance_subspace_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hsepAB : IntervalExteriorSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ left right d)
    (hsepBA : IntervalExteriorSeparated B (spectralSubspace B t)
      A (spectralSubspace A s)ᗮ left' right' d) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤ ‖B - A‖ := by
  sorry

end DavisKahanExt
end ForMathlib
