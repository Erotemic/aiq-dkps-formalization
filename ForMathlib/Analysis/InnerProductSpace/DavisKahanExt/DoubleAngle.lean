/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SinTheta

/-!
# Infinite-dimensional `sin 2Θ` and generic double-angle bounds

Literature writeup: local TeX, Sections 14--15, including Seelmann's general
spectral-separation form.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Reflection through a closed subspace. -/
noncomputable def reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  2 • projection U - ContinuousLinearMap.id 𝕜 E

/-- Mirror defect used in the reflection proof of `sin 2Θ`. -/
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  reflectionOperator U ∘L A ∘L reflectionOperator U - A

/-- Residual `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Let `J` be the reflection through `V` and compare `A` with `JAJ`.
2. The spectral subspace `JU` reduces `JAJ` and has the same internal gap.
3. Apply the symmetric `sinTheta` theorem to `A` and `JAJ`.
4. Use the two-projection identity relating the angle between `U` and `JU` to `sin(2Θ(U,V))`.
-/
theorem sinTwoTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {d : ℝ} (hd : 0 < d)
    (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤
      ‖reflectionDefect V A‖ := by
  sorry

/-- Perturbation form of the `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Apply `sinTwoTheta_residual` with the perturbed reducing subspace `V`.
2. Insert and subtract the reflection conjugate of `B`.
3. Use reduction of `B` by `V` to cancel its reflection defect.
4. Bound the two remaining perturbation terms by `2‖B-A‖`.
-/
theorem sinTwoTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ 2 * ‖B - A‖ := by
  sorry

/-- General spectral-separation `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Apply the general separated-spectrum Sylvester estimate to the reflection defect.
2. Identify the resulting cross block with `sin(2Θ)` through the two-projection calculus.
3. Bound the defect by `2‖B-A‖`; combine constants to obtain `π‖B-A‖/d`.
4. Convert the operator norm of `sinTwoAngleOperator` to the scalar maximal-angle expression.
-/
theorem sinTwoTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    Real.sin (2 * maximalAngle U V) ≤
      Real.pi * ‖B - A‖ / d := by
  sorry

/-- Ideal-norm `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Use the reflection-defect form of `sinTwoTheta_residual` in the ideal gauge.
2. Show the reflection defect equals the off-diagonal extraction of `B-A` up to the factor two because `V` reduces `B`.
3. Apply `gauge_offDiagonalPart_le` and `hmem`.
4. Package ideal membership before the numerical inequality.
-/
theorem ideal_sinTwoTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d)
    (hmem : I.mem (B - A)) :
    I.mem (sinTwoAngleOperator U V) ∧
      d * I.gauge (sinTwoAngleOperator U V) ≤
        2 * I.gauge (B - A) := by
  sorry

end DavisKahanExt
end ForMathlib
