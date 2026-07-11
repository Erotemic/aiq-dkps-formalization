/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Sylvester

/-!
# Infinite-dimensional `sin Θ` theorems

Literature writeup: local TeX, Sections 12--13.  Both residual and perturbation
forms are represented, including general separated spectra and ideal-norm
versions.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Residual `sin Θ` theorem for an isometric trial map. 

Lean proof route for a weaker agent:

1. Set `Y=(I-P_U)X` and derive `A|_{Uᗮ} Y - Y M = (I-P_U) residual A X M`.
2. Apply the ordered constant-one Sylvester theorem using `hsep`.
3. Bound the projected residual by the full residual norm.
4. Identify `Y` with `sinThetaEmbedding U X`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed residual theorem. The
isometric embedding is needed for the subspace interpretation, although the raw
Sylvester norm estimate itself uses only boundedness.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U)
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated M ⊤ A Uᗮ d) :
    d * ‖sinThetaEmbedding U X‖ ≤ ‖residual A X M‖ := by
  sorry

/-- One-sided perturbation theorem for spectral subspaces. 

Lean proof route for a weaker agent:

1. Derive the off-diagonal Sylvester equation for `X=(I-P_V)P_U`.
2. Use the interval/exterior decomposition to apply the constant-one ordered Sylvester estimate to the lower and upper pieces.
3. Bound the right-hand residual by `‖B-A‖`.
4. Rewrite `‖X‖` as the directed gap.


Ext-agent signature audit (GPT 5.6 High): Correct as a one-sided directed-angle theorem.
One mixed interval/exterior gap is intentionally insufficient for a full
projector-difference conclusion.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    d * directedGap U V ≤ ‖B - A‖ := by
  sorry

/-- Symmetric projector-difference form requiring both mixed gaps. 

Lean proof route for a weaker agent:

1. Apply `sinTheta_perturbation` to `(U,V)` and again to `(V,U)` using the reverse gap.
2. Use the two-projection norm identity that the full gap is the maximum of the two directed gaps.
3. Combine the two inequalities with `max_le` and simplify the perturbation sign.


Ext-agent signature audit (GPT 5.6 High): Correct with both mixed gaps. The full
projection gap is the maximum of the two directed gaps in operator norm.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_symmetric
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d) :
    d * subspaceGap U V ≤ ‖B - A‖ := by
  sorry

/-- General separated-spectrum form with the optimal universal `π / 2`
Sylvester constant. 

Lean proof route for a weaker agent:

1. Derive the Sylvester equation for `(I-P_V)P_U` from the two reducing relations.
2. Apply `norm_sylvester_le_of_generalSeparation` with the hybrid spectral gap.
3. Bound the residual block by `‖B-A‖` using projection contractions.
4. Rewrite the block norm as `directedGap U V`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed theorem with the `π/2`
constant. The hybrid gap matches the cross block `P_{Vᗮ}P_U`.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : HybridGap A B U V d) :
    d * directedGap U V ≤ (Real.pi / 2) * ‖B - A‖ := by
  sorry

/-- Canonical spectral-projection form. 

Lean proof route for a weaker agent:

1. Convert the four spectral-containment hypotheses into the two `IntervalExteriorSeparated` predicates.
2. Apply `sinTheta_symmetric` to the canonical spectral subspaces, using `reduces_spectralSubspace`.
3. Rewrite the subspace gap as the norm of the two spectral projections.


Ext-agent signature audit (GPT 5.6 High): Correct after the measurable-set hypotheses
were added. The four containments encode exactly the two mixed interval/exterior gaps.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem spectralProjection_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hAs : SpectrumIn A (spectralSubspace A s) (Set.Icc left right))
    (hBt : SpectrumIn B (spectralSubspace B t)ᗮ
      {x | x ≤ left - d ∨ right + d ≤ x})
    (hBs : SpectrumIn B (spectralSubspace B t) (Set.Icc left' right'))
    (hAt : SpectrumIn A (spectralSubspace A s)ᗮ
      {x | x ≤ left' - d ∨ right' + d ≤ x}) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤
      ‖B - A‖ := by
  sorry

/-- Symmetric-ideal form. 

Lean proof route for a weaker agent:

1. Decompose the full sine operator into the two directed off-diagonal blocks.
2. Apply the interval/exterior ideal-valued Sylvester estimate to each block, using `hmem` for the perturbation.
3. Recombine the blocks through the two-projection decomposition or the symmetric-angle identity.
4. Return both ideal membership and the gauge inequality.


Ext-agent signature audit (GPT 5.6 High): Plausible with the full ambient sine
convention because the self-adjoint off-diagonal blocks occur as adjoint pairs. The
proof must establish the corresponding ideal block identity; do not combine two directed
estimates by a triangle inequality, which would lose the sharp constant.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem ideal_sinTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : I.mem (B - A)) :
    I.mem (sinAngleOperator U V) ∧
      d * I.gauge (sinAngleOperator U V) ≤ I.gauge (B - A) := by
  sorry

end DavisKahanExt
end ForMathlib
