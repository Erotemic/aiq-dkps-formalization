/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Basic

/-! # Reflection defects for bounded operators -/

namespace ForMathlib
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

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


end DavisKahan
end ForMathlib
