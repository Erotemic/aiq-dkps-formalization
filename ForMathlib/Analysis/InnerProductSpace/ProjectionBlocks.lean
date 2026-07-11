/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.ReducingSubspace

/-!
# Projection blocks and reflections

General `RCLike` block decomposition relative to an orthogonally complemented
subspace.  This module is independent of the Davis--Kahan theory.
-/


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-- Reflection through an orthogonally complemented subspace. -/
noncomputable def reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.reflection.toLinearIsometry.toContinuousLinearMap

/-- Diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def diagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  U.starProjection ∘L A ∘L U.starProjection +
    Uᗮ.starProjection ∘L A ∘L Uᗮ.starProjection

/-- Off-diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def offDiagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  A - U.diagonalPart A

/-- The operator has vanishing diagonal blocks relative to `U`. -/
def IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) : Prop := U.diagonalPart A = 0

/-- Pointwise formula for reflection. -/
theorem reflectionOperator_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    U.reflectionOperator x = (2 : 𝕜) • U.starProjection x - x := by
  change U.reflection x = (2 : 𝕜) • U.starProjection x - x
  rw [Submodule.reflection_apply, ← Nat.cast_smul_eq_nsmul 𝕜]
  norm_num

/-- Reflection is involutive. -/
theorem reflectionOperator_involutive (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    U.reflectionOperator ∘L U.reflectionOperator =
      ContinuousLinearMap.id 𝕜 E := by
  ext x
  change U.reflection (U.reflection x) = x
  exact U.reflection_reflection x

/-- Reflection preserves norms. -/
theorem reflectionOperator_norm_map (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    ‖U.reflectionOperator x‖ = ‖x‖ := by
  change ‖U.reflection x‖ = ‖x‖
  exact U.reflection.norm_map x

/-- Reflection is onto. -/
theorem reflectionOperator_surjective (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : Function.Surjective U.reflectionOperator := by
  change Function.Surjective U.reflection
  exact U.reflection.surjective

/-- Reflection has operator norm at most one. -/
theorem norm_reflectionOperator_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : ‖U.reflectionOperator‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖U.reflection x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using le_of_eq (U.reflection.norm_map x)

/-- A reducing operator commutes with the corresponding reflection. -/
theorem reflectionOperator_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    U.reflectionOperator ∘L A = A ∘L U.reflectionOperator := by
  ext x
  change U.reflectionOperator (A x) = A (U.reflectionOperator x)
  rw [reflectionOperator_apply, reflectionOperator_apply,
    ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU,
    map_sub, map_smul]

/-- Complementary projection as `I-P`, pointwise. -/
theorem starProjection_orthogonal_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    Uᗮ.starProjection x = x - U.starProjection x := by
  rw [Submodule.starProjection_orthogonal]
  simp

/-- Twice the diagonal pinch is `A + JAJ`. -/
theorem two_smul_diagonalPart_eq_add_reflectionConjugate
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (2 : 𝕜) • U.diagonalPart A =
      A + U.reflectionOperator ∘L A ∘L U.reflectionOperator := by
  ext x
  simp only [diagonalPart, ContinuousLinearMap.comp_apply, add_apply, smul_apply]
  simp_rw [starProjection_orthogonal_apply, reflectionOperator_apply]
  simp only [map_sub, map_smul]
  module

/-- Twice the off-diagonal extraction is `A-JAJ`. -/
theorem two_smul_offDiagonalPart_eq_sub_reflectionConjugate
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (2 : 𝕜) • U.offDiagonalPart A =
      A - U.reflectionOperator ∘L A ∘L U.reflectionOperator := by
  unfold offDiagonalPart
  rw [smul_sub, two_smul_diagonalPart_eq_add_reflectionConjugate]
  module

end Submodule

