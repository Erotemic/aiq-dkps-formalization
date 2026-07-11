/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Projector
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Real spectral bridge roadmap

The supported bounded theorem is already scalar-generic.  This module records
the missing real-Hilbert-space bridge from actual spectra to quadratic-form
bounds.  A direct Rayleigh-shift proof is preferred; complexification is a
secondary route.  The declarations here are excluded from the supported
umbrella until the bridge is discharged.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Foundation
namespace RealSpectralBridge

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real spectral upper bound implies a global quadratic-form upper bound. -/
theorem upperFormBoundOn_top_of_spectrum_subset_Iic
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) {c : ℝ}
    (hσ : spectrum ℝ A ⊆ Set.Iic c) :
    UpperFormBoundOn A ⊤ c := by
  sorry

/-- Real spectral lower bound implies a global quadratic-form lower bound. -/
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) {c : ℝ}
    (hσ : spectrum ℝ A ⊆ Set.Ici c) :
    LowerFormBoundOn A ⊤ c := by
  sorry

/-- Real restriction-spectrum upper bridge on an orthogonally complemented
subspace. -/
theorem upperFormBoundOn_of_restriction_spectrum_subset_Iic
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c) :
    UpperFormBoundOn A U c := by
  sorry

/-- Real restriction-spectrum lower bridge on an orthogonally complemented
subspace. -/
theorem lowerFormBoundOn_of_restriction_spectrum_subset_Ici
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c) :
    LowerFormBoundOn A U c := by
  sorry

/-- Target sharp real Davis--Kahan theorem from spectra of actual
restrictions. -/
theorem opNorm_starProjection_sub_le_of_restriction_spectra
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule ℝ E} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : E →L[ℝ] E)‖ ≤ ‖B - A‖ / g := by
  apply DavisKahan.opNorm_starProjection_sub_le_of_formBounds hA hB hU hW hg
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hA hU.1 hUhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hA hU.2 hUlo
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hB hW.1 hWhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hB hW.2 hWlo

end RealSpectralBridge
end Foundation
end Experimental
end DavisKahan
end ForMathlib
