/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Spectral.Complex

/-! Compatibility aliases for the former complex spectral module. -/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

alias re_inner_le_of_spectrum_subset_Iic :=
  SpectralOrder.Complex.re_inner_le_of_spectrum_subset_Iic
alias le_re_inner_of_spectrum_subset_Ici :=
  SpectralOrder.Complex.le_re_inner_of_spectrum_subset_Ici
@[deprecated le_re_inner_of_spectrum_subset_Ici (since := "2026-07-11")]
alias le_re_inner_of_Ici_subset_spectrum := le_re_inner_of_spectrum_subset_Ici
alias re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic :=
  SpectralOrder.Complex.re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic
alias le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici :=
  SpectralOrder.Complex.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
alias upperFormBoundOn_top_of_spectrum_subset_Iic :=
  SpectralOrder.Complex.upperFormBoundOn_top_of_spectrum_subset_Iic
alias lowerFormBoundOn_top_of_spectrum_subset_Ici :=
  SpectralOrder.Complex.lowerFormBoundOn_top_of_spectrum_subset_Ici
alias upperFormBoundOn_of_restriction_spectrum_subset_Iic :=
  SpectralOrder.Complex.upperFormBoundOn_of_restriction_spectrum_subset_Iic
alias lowerFormBoundOn_of_restriction_spectrum_subset_Ici :=
  SpectralOrder.Complex.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
alias norm_add_eq_max_of_block := ContinuousLinearMap.norm_add_eq_max_of_block
alias norm_starProjection_sub_eq_max := Submodule.norm_starProjection_sub_eq_max
alias opNorm_starProjection_sub_le_of_coercive :=
  DavisKahan.opNorm_starProjection_sub_le_of_coercive
alias opNorm_starProjection_sub_le_of_formBounds :=
  DavisKahan.opNorm_starProjection_sub_le_of_formBounds
alias opNorm_starProjection_sub_le_of_restriction_spectra :=
  DavisKahan.Spectral.Complex.opNorm_starProjection_sub_le_of_restriction_spectra

theorem isComplete_coe_of_hasOrthogonalProjection
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] : IsComplete (U : Set H) :=
  U.isComplete_coe_of_hasOrthogonalProjection

end DavisKahanExt
end ForMathlib
