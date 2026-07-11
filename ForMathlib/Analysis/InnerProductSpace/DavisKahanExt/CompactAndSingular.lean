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
projections. -/
theorem compact_projection_difference
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ d)
    (hcompact : (SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)).mem (B - A)) :
    (SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)).mem
      (spectralProjection A s - spectralProjection B t) := by
  sorry

/-- Schatten-class perturbation implies Schatten-class angle operator. -/
theorem schatten_sinTheta
    (p : ℝ) {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d) :
    (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p).gauge
      (sinAngleOperator U V) ≤
    (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p).gauge (B - A) / d := by
  sorry

/-- Hermitian dilation of a rectangular bounded operator. -/
noncomputable def hermitianDilation (T : E →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := by
  sorry

/-- The Hermitian dilation is self-adjoint. -/
theorem hermitianDilation_selfAdjoint (T : E →L[𝕜] F) :
    IsSelfAdjointOperator (hermitianDilation T) := by
  sorry

/-- Infinite-dimensional Wedin theorem for isolated singular spectral sets. -/
theorem wedin_singularSubspace
    {S T : E →L[𝕜] F} (s t : Set ℝ)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated (hermitianDilation S)
      (spectralSubspace (hermitianDilation S) s)
      (hermitianDilation T)
      (spectralSubspace (hermitianDilation T) t)ᗮ d) :
    d * ‖spectralProjection (hermitianDilation S) s -
      spectralProjection (hermitianDilation T) t‖ ≤
      ‖hermitianDilation (T - S)‖ := by
  sorry

/-- Covariance-operator principal-subspace perturbation. -/
theorem covariance_subspace_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) {left right d : ℝ} (hd : 0 < d)
    (hsep : IntervalExteriorSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ left right d) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤ ‖B - A‖ := by
  sorry

end DavisKahanExt
end ForMathlib
