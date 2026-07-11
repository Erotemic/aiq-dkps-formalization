/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Basic
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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Mirror defect used in the reflection proof of `sin 2Θ`. -/
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  reflectionOperator U ∘L A ∘L reflectionOperator U - A

/-- The mirror defect vanishes when the subspace reduces the operator.

Lean proof route for a weaker agent:

1. Evaluate reflection-operator commutation at the reflected vector.
2. Evaluate reflection involutivity at the original vector.
3. Unfold `reflectionDefect` and substitute both equalities.
-/
theorem reflectionDefect_eq_zero_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    reflectionDefect U A = 0 := by
  ext x
  have hcomm := congrArg (fun T : E →L[𝕜] E => T (reflectionOperator U x))
    (reflectionOperator_comm_of_reduces A U hU)
  have hinvol := congrArg (fun T : E →L[𝕜] E => T x)
    (reflectionOperator_involutive U)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcomm hinvol
  simp only [reflectionDefect, ContinuousLinearMap.comp_apply, sub_apply,
    zero_apply]
  rw [hcomm, hinvol, sub_self]

/-- Conjugating and subtracting a reducing comparison operator leaves only
its perturbation.

Lean proof route for a weaker agent:

1. Use `reflectionDefect_eq_zero_of_reduces` for `B`.
2. Subtract that zero defect from the defect of `A`.
3. Extensionalize and distribute reflection through `A-B`.
-/
theorem reflectionDefect_eq_perturbationDefect
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    reflectionDefect V A =
      reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B) := by
  have hB : reflectionDefect V B = 0 :=
    reflectionDefect_eq_zero_of_reduces B V hV
  unfold reflectionDefect at hB ⊢
  calc
    reflectionOperator V ∘L A ∘L reflectionOperator V - A =
        (reflectionOperator V ∘L A ∘L reflectionOperator V - A) -
          (reflectionOperator V ∘L B ∘L reflectionOperator V - B) := by
      rw [hB, sub_zero]
    _ = reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      abel

/-- The reflection defect is bounded by twice the perturbation norm.

Lean proof route for a weaker agent:

1. Rewrite the defect using `reflectionDefect_eq_perturbationDefect`.
2. Bound the conjugated perturbation with operator-norm submultiplicativity
   and `norm_reflectionOperator_le_one` twice.
3. Apply the norm triangle inequality to the final subtraction.
-/
theorem norm_reflectionDefect_le_two_mul
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    ‖reflectionDefect V A‖ ≤ 2 * ‖A - B‖ := by
  rw [reflectionDefect_eq_perturbationDefect A B V hV]
  have hconj :
      ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V‖ ≤
        ‖A - B‖ := by
    calc
      ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V‖ ≤
          ‖reflectionOperator V‖ * ‖(A - B) ∘L reflectionOperator V‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖reflectionOperator V‖ * (‖A - B‖ * ‖reflectionOperator V‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg (reflectionOperator V))
      _ ≤ 1 * (‖A - B‖ * ‖reflectionOperator V‖) :=
        mul_le_mul_of_nonneg_right (norm_reflectionOperator_le_one V) (by positivity)
      _ ≤ 1 * (‖A - B‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_reflectionOperator_le_one V)
            (norm_nonneg (A - B)))
          zero_le_one
      _ = ‖A - B‖ := by ring
  calc
    ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B)‖ ≤
        ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V‖ +
          ‖A - B‖ := norm_sub_le _ _
    _ ≤ ‖A - B‖ + ‖A - B‖ := add_le_add hconj le_rfl
    _ = 2 * ‖A - B‖ := by ring

/-- Reflection-defect `sin 2Θ` theorem.

This is the theorem previously named `sinTwoTheta_residual`. The old name was
misleading: its right-hand side is a mirror defect, not the residual of an
approximate invariant pair.

Lean proof route for a weaker agent:

1. Let `J` be the reflection through `V` and compare `A` with `JAJ`.
2. The spectral subspace `JU` reduces `JAJ` and has the same internal gap.
3. Apply the symmetric `sinTheta` theorem to `A` and `JAJ`.
4. Use the two-projection identity relating the angle between `U` and `JU` to `sin(2Θ(U,V))`.


Ext-agent signature audit (GPT 5.6 High): `FiniteGapConfiguration` already supplies the
structured internal separation at positive `d`; the former separate `InternalGap`
hypothesis was redundant. The reflection-defect target is the correct sharp residual
form.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_reflectionDefect
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤
      ‖reflectionDefect V A‖ := by
  sorry

/-- Approximate-invariant-pair residual form of `sin 2Θ`.

This is the genuine residual theorem missing from the earlier scaffold.  The
proof should reflect through the closed range of `X`, identify its mirror
defect with twice the off-diagonal residual, and apply
`sinTwoTheta_reflectionDefect`.

Lean proof route for a weaker agent:

1. Prove that an isometric embedding has closed range and construct the
   orthogonal projection onto that range.
2. Show that self-adjointness of `M` makes `X ∘ M ∘ X⁻¹` reduce the trial
   range.
3. Express the reflection defect of `A` through the trial range in terms of
   `residual A X M` and its adjoint block.
4. Bound that defect by twice the residual norm and invoke the
   reflection-defect theorem.
-/
theorem sinTwoTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d) (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoThetaEmbedding U X‖ ≤ 2 * ‖residual A X M‖ := by
  sorry

/-- Perturbation form of the `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Apply `sinTwoTheta_reflectionDefect` with the perturbed reducing subspace `V`.
2. Insert and subtract the reflection conjugate of `B`.
3. Use reduction of `B` by `V` to cancel its reflection defect.
4. Bound the two remaining perturbation terms by `2‖B-A‖`.


Ext-agent signature audit (GPT 5.6 High): Correct under finite-gap geometry. Reduction
of `B` by `V` is essential for cancellation of its reflection defect. Self-adjointness
of `B` is not needed for this reflection argument and was removed from the signature.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ 2 * ‖B - A‖ := by
  calc
    d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖A - B‖ := norm_reflectionDefect_le_two_mul A B V hV
    _ = 2 * ‖B - A‖ := by rw [norm_sub_rev]

/-- General spectral-separation `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Apply the general separated-spectrum Sylvester estimate to the reflection defect.
2. Identify the resulting cross block with `sin(2Θ)` through the two-projection calculus.
3. Bound the defect by `2‖B-A‖`; combine constants to obtain the factor `π`.
4. Keep the result at the operator level: `sin (2·maximalAngle)` is not the
   norm of `sinTwoAngleOperator` when the angle spectrum crosses `π/4`.


Ext-agent signature audit (GPT 5.6 High): The corrected operator-norm conclusion is the
meaningful generic theorem. `sin (2·maximalAngle)` alone can miss intermediate angle
spectrum when angles cross `π/4`.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ Real.pi * ‖B - A‖ := by
  sorry

/-- Ideal-norm `sin 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Use the reflection-defect form of `sinTwoTheta_reflectionDefect` in the ideal gauge.
2. Show the reflection defect equals the off-diagonal extraction of `B-A` up to the factor two because `V` reduces `B`.
3. Apply `gauge_offDiagonalPart_le` and `hmem`.
4. Package ideal membership before the numerical inequality.


Ext-agent signature audit (GPT 5.6 High): Correct roadmap target under finite-gap
geometry and ideal membership of the perturbation. The proof must work with ambient
reflection blocks so multiplicities match.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem ideal_sinTwoTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hmem : I.mem (B - A)) :
    I.mem (sinTwoAngleOperator U V) ∧
      d * I.gauge (sinTwoAngleOperator U V) ≤
        2 * I.gauge (B - A) := by
  sorry

end DavisKahanExt
end ForMathlib
