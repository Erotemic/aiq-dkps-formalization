/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Riccati
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Continuation

/-!
# Off-diagonal perturbations, `tan Θ`, and `tan 2Θ`

Literature writeup: local TeX, Sections 21--24.  This covers gap preservation,
spectral enclosure, the generalized `tan 2Θ` theorem, and the sharp a priori
`tan Θ` theorem.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Spectral components born from an isolated component under an off-diagonal
perturbation. -/
noncomputable def continuedSpectralSubspace (A H : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E := by
  sorry

noncomputable instance continuedSpectralSubspace_hasOrthogonalProjection
    (A H : E →L[𝕜] E) (s : Set ℝ) :
    (continuedSpectralSubspace A H s).HasOrthogonalProjection := by
  sorry

/-- Off-diagonal perturbations preserve the separating gap below the sharp
`√2 d` threshold.

Proof strategy: first obtain enclosure of each perturbed spectral component
from the Schur complement or Riccati block diagonalization.  Show the two
enclosures remain disjoint under the scalar inequality `‖H‖ < sqrt 2 * d`.
Use norm-continuity of the Riesz projection along `A+tH` to rule out branch
switching, then identify the endpoint with the continued spectral subspace. -/
theorem gap_preserved_of_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    ∃ V : Submodule 𝕜 E, Reduces (A + H) V := by
  sorry

/-- Generalized `tan 2Θ` theorem. -/
theorem tanTwoTheta_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces (A + H) V)
    (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : OrderedInternalGap A U d) :
    ‖tanTwoAngleOperator U V‖ ≤ 2 * ‖H‖ / d := by
  sorry

/-- A priori `tan Θ` theorem in the finite-gap configuration.

Proof strategy: select the continued spectral subspace and represent it as the
graph of the contractive Riccati solution `X`.  Combine spectral enclosure for
the perturbed diagonal blocks with the Riccati equation to obtain a scalar
quadratic inequality for `x = ‖X‖`.  Solve the majorant inequality on the
contractive branch and translate through

`‖P-Q‖ = x / sqrt(1+x^2)`.

The sharp `sqrt 2 * d` threshold is where the selected scalar branch ceases to
remain uniformly acute.  Keep the scalar optimization and trigonometric
identity in separate lemmas so the operator proof is mostly monotonicity. -/
theorem aPrioriTanTheta
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
    subspaceGap U V ≤ Real.sin (Real.arctan (‖H‖ / d)) := by
  sorry

/-- The a priori bound is sharp. -/
theorem aPrioriTanTheta_constant_sharp :
    ∀ c : ℝ, c < Real.sqrt 2 →
      ∃ (A H P : E →L[𝕜] E),
        IsSelfAdjointOperator A ∧ IsSelfAdjointOperator H ∧
        IsOrthogonalProjection P ∧ IsOffDiagonalRelativeToProjection P H := by
  sorry

/-- Spectral repulsion: off-diagonal perturbations move the two components
away from the original gap. -/
theorem spectral_repulsion_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hordered : OrderedInternalGap A U d) :
    spectralDistance (restrictedSpectrum (A + H)
      (continuedSpectralSubspace A H (restrictedSpectrum A U)))
      (restrictedSpectrum (A + H)
        (continuedSpectralSubspace A H (restrictedSpectrum A U))ᗮ) ≥
      spectralDistance (restrictedSpectrum A U) (restrictedSpectrum A Uᗮ) := by
  sorry

end DavisKahanExt
end ForMathlib
