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

/-- Residual `sin 2Θ` theorem. -/
theorem sinTwoTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {d : ℝ} (hd : 0 < d)
    (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤
      ‖reflectionDefect V A‖ := by
  sorry

/-- Perturbation form of the `sin 2Θ` theorem. -/
theorem sinTwoTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ 2 * ‖B - A‖ := by
  sorry

/-- General spectral-separation `sin 2Θ` theorem. -/
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

/-- Ideal-norm `sin 2Θ` theorem. -/
theorem ideal_sinTwoTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * I.gauge (sinTwoAngleOperator U V) ≤
      2 * I.gauge (B - A) := by
  sorry

end DavisKahanExt
end ForMathlib
