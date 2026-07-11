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
switching, then identify the endpoint with the continued spectral subspace. 

Lean proof route for a weaker agent:

1. Use off-diagonal spectral enclosure to bound the two perturbed components on opposite sides of the original gap.
2. Check the scalar `sqrt 2` inequality leaves a positive distance between the enclosures.
3. Continue the Riesz projection along `A+tH` to select the correct component.
4. Prove reduction, acuteness, and positive endpoint spectral distance in that order.


Ext-agent signature audit (GPT 5.6 High): The nonempty block hypotheses are necessary
for the positive spectral-distance conclusion. The `√2 d` threshold belongs to
continuation/branch preservation, not to the local Riccati contraction theorem.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
theorem gap_preserved_of_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hU_spec : (restrictedSpectrum A U).Nonempty)
    (hUc_spec : (restrictedSpectrum A Uᗮ).Nonempty)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
    Reduces (A + H) V ∧ IsAcute U V ∧
      0 < spectralDistance (restrictedSpectrum (A + H) V)
        (restrictedSpectrum (A + H) Vᗮ) := by
  sorry

/-- Generalized `tan 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Represent `V` as a graph over `U`; `hquarter` ensures the double-angle tangent is bounded.
2. Derive the Riccati equation from reduction of `A+H` and the off-diagonal form of `H`.
3. Apply the ordered gap to the linear Sylvester term and estimate the quadratic terms.
4. Translate the resulting bound on the angular operator to `tanTwoAngleOperator`.


Ext-agent signature audit (GPT 5.6 High): Correct only below the quarter-angle pole; the
proof argument is now passed to `tanTwoAngleOperator`, so the operator is not silently
totalized.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
theorem tanTwoTheta_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces (A + H) V)
    (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : OrderedInternalGap A U d)
    (hquarter : IsQuarterAcute U V) :
    ‖tanTwoAngleOperator U V hquarter‖ ≤ 2 * ‖H‖ / d := by
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
identity in separate lemmas so the operator proof is mostly monotonicity. 

Lean proof route for a weaker agent:

1. Use `gap_preserved_of_offDiagonal` to obtain the continued reducing subspace and acuteness.
2. Apply `existsUnique_angularOperator` to represent that subspace as `graphSubspace U X`.
3. Derive the Riccati equation from graph invariance and use the finite-gap enclosure to obtain the scalar majorant for `‖X‖`.
4. Solve the scalar inequality on the contractive branch, then rewrite the projector gap with `tan_maximalAngle_eq_norm_angularOperator`.


Ext-agent signature audit (GPT 5.6 High): The added nonempty-spectrum hypotheses align
this theorem with `gap_preserved_of_offDiagonal`. The endpoint is the continued branch,
not an arbitrary reducing subspace of `A+H`.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
theorem aPrioriTanTheta
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hU_spec : (restrictedSpectrum A U).Nonempty)
    (hUc_spec : (restrictedSpectrum A Uᗮ).Nonempty)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
    subspaceGap U V ≤ Real.sin (Real.arctan (‖H‖ / d)) := by
  sorry

/-- Spectral repulsion: off-diagonal perturbations move the two components
away from the original gap. 

Lean proof route for a weaker agent:

1. Use the Riccati block diagonalization of the continued spectral subspace.
2. Express the effective diagonal blocks as the original blocks plus positive/negative Schur-complement corrections.
3. Apply spectral monotonicity to show the selected components move away from the original gap.
4. Convert the two enclosure inequalities into the stated spectral-distance comparison.


Ext-agent signature audit (GPT 5.6 High): Plausible only in the ordered configuration;
the explicit `OrderedInternalGap` and nonempty hypotheses are therefore essential. Prove
oriented enclosure inequalities before converting to set distance.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
theorem spectral_repulsion_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hordered : OrderedInternalGap A U d)
    (hU_spec : (restrictedSpectrum A U).Nonempty)
    (hUc_spec : (restrictedSpectrum A Uᗮ).Nonempty)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    spectralDistance (restrictedSpectrum (A + H)
      (continuedSpectralSubspace A H (restrictedSpectrum A U)))
      (restrictedSpectrum (A + H)
        (continuedSpectralSubspace A H (restrictedSpectrum A U))ᗮ) ≥
      spectralDistance (restrictedSpectrum A U) (restrictedSpectrum A Uᗮ) := by
  sorry

end DavisKahanExt
end ForMathlib
