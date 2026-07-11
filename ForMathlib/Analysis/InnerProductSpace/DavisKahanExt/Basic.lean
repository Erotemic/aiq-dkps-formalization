/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Mathlib

/-!
# Infinite-dimensional Davis--Kahan foundations

This module also owns the shared reflection API used by `DoubleAngle`.

This file introduces the bounded-operator and closed-subspace vocabulary used
throughout `DavisKahanExt`.

Literature writeup:
`ForMathlib/Analysis/InnerProductSpace/DavisKahanExt/prose/InfiniteDimensionalDavisKahan.tex`,
Sections 2--4.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

abbrev BoundedOperator (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] := E →L[𝕜] E

/-- Inner-product formulation of bounded self-adjointness. -/
def IsSelfAdjointOperator (A : E →L[𝕜] E) : Prop :=
  ∀ x y, ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜

/-- A closed subspace reduces a bounded operator. -/
def Reduces (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  (∀ x ∈ U, A x ∈ U) ∧ (∀ x ∈ Uᗮ, A x ∈ Uᗮ)

/-- Orthogonal projection onto a closed subspace. -/
noncomputable def projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.starProjection

/-- Orthogonal projection onto the complementary subspace. -/
noncomputable def complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  Uᗮ.starProjection

/-- Diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def diagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  projection U ∘L A ∘L projection U +
    complementaryProjection U ∘L A ∘L complementaryProjection U

/-- Off-diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def offDiagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  A - diagonalPart U A

/-- The perturbation has vanishing diagonal blocks. -/
def IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) : Prop :=
  diagonalPart U A = 0

/-- A bounded operator is an orthogonal projection. -/
def IsOrthogonalProjection (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ IsSelfAdjointOperator P

/-- A bounded unitary operator, expressed without committing to a particular
bundled equivalence API. -/
def IsUnitaryOperator (W : E →L[𝕜] E) : Prop :=
  (∀ x, ‖W x‖ = ‖x‖) ∧ Function.Surjective W

/-- Off-diagonal relative to an explicitly supplied orthogonal projection. -/
def IsOffDiagonalRelativeToProjection (P H : E →L[𝕜] E) : Prop :=
  P ∘L H ∘L P = 0 ∧
    (ContinuousLinearMap.id 𝕜 E - P) ∘L H ∘L
      (ContinuousLinearMap.id 𝕜 E - P) = 0

/-- Abstract real spectrum of a bounded self-adjoint operator.

The eventual implementation should be tied to the Banach-algebra spectrum and
its reality theorem. -/
noncomputable def realSpectrum (A : E →L[𝕜] E) : Set ℝ := by
  sorry

/-- Spectrum of the restriction of `A` to a reducing subspace. -/
noncomputable def restrictedSpectrum (A : E →L[𝕜] E)
    (U : Submodule 𝕜 E) : Set ℝ := by
  sorry

/-- The spectrum carried by `U` is contained in `s`. -/
def SpectrumIn (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (s : Set ℝ) : Prop :=
  restrictedSpectrum A U ⊆ s

/-- A scalar function is uniformly bounded on the real spectrum of `A`. -/
def BoundedOnSpectrum (A : E →L[𝕜] E) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ realSpectrum A, |f x| ≤ C

/-- Distance between two real spectral sets. -/
noncomputable def spectralDistance (s t : Set ℝ) : ℝ :=
  sInf {r | ∃ x ∈ s, ∃ y ∈ t, r = |x - y|}

/-- Two restricted spectra are separated by at least `d`. -/
def SpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
    d ≤ |a - b|

/-- The selected block of `A` is separated from the complementary block of
`B`. -/
def HybridGap (A B : E →L[𝕜] E) (U V : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  SpectraSeparated A U B Vᗮ d

/-- Internal spectral gap of a reducing subspace. -/
def InternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  SpectraSeparated A U A Uᗮ d

/-- Ordered separation, giving the sharp constant-one Sylvester estimate. -/
def OrderedSpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
    a + d ≤ b

/-- Interval/exterior separation from the classic `sin Θ` theorem. -/
def IntervalExteriorSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F)
    (left right d : ℝ) : Prop :=
  SpectrumIn A U (Set.Icc left right) ∧
    SpectrumIn B V {x | x ≤ left - d ∨ right + d ≤ x}

/-- One spectral component lies in a finite gap of the other. -/
def FiniteGapConfiguration (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  ∃ left right, left ≤ right ∧
    SpectrumIn A U (Set.Icc left right) ∧
    SpectrumIn A Uᗮ {x | x ≤ left - d ∨ right + d ≤ x}

/-- Ordered internal gap, in either orientation. -/
def OrderedInternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  OrderedSpectraSeparated A U A Uᗮ d ∨
    OrderedSpectraSeparated A Uᗮ A U d

/-- Gap metric on closed subspaces. -/
noncomputable def subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  ‖projection U - projection V‖

/-- Directed gap from `U` to `V`. -/
noncomputable def directedGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  ‖complementaryProjection V ∘L projection U‖

/-- The two subspaces are in the acute case. -/
def IsAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  subspaceGap U V < 1

/-- The projection gap lies below the quarter-angle threshold.  This is the
operator-level hypothesis under which `tan (2 Θ)` is bounded. -/
def IsQuarterAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  subspaceGap U V < Real.sqrt 2 / 2

/-- Isometric embedding used in residual formulations. -/
def IsometricEmbedding (X : F →L[𝕜] E) : Prop :=
  ∀ x, ‖X x‖ = ‖x‖

/-- Residual of an approximate invariant pair. -/
def residual (A : E →L[𝕜] E) (X : F →L[𝕜] E)
    (M : F →L[𝕜] F) : F →L[𝕜] E :=
  A ∘L X - X ∘L M

/-- Sine residual block relative to an exact subspace. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E :=
  complementaryProjection U ∘L X

/-- A reducing subspace for a self-adjoint operator has a reducing orthogonal
complement. 

Lean proof route for a weaker agent:

1. Retain the supplied invariance of `U` as the first conjunct.
2. For `x∈Uᗮ` and `u∈U`, use self-adjointness to rewrite `⟪Ax,u⟫=⟪x,Au⟫`.
3. Apply `hU` and orthogonality to show the inner product vanishes for every `u`.
4. Conclude `Ax∈Uᗮ` and package both conjuncts.


Ext-agent signature audit (GPT 5.6 High): Correct as stated: for a bounded self-adjoint
operator, invariance of a closed subspace implies invariance of its orthogonal
complement. Completeness is used only for projection infrastructure, not the
inner-product argument itself.

Preferred dependency route: Prove this in the bounded projection-geometry core, using
only `Basic` definitions and mathlib Hilbert-space projection lemmas; all finite
versions should later specialize this result.
-/
theorem reduces_orthogonalComplement {A : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : Reduces A U := by
  refine ⟨hU, ?_⟩
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

/-- A reducing subspace projection commutes with the operator.

This is the bounded Hilbert-space version of the projection-commutation lemma
already used by the finite-dimensional `sin Θ` development.  Unlike
`reduces_orthogonalComplement`, self-adjointness is not needed here because
`Reduces A U` explicitly includes invariance of both `U` and `Uᗮ`.

Lean proof route for a weaker agent:

1. Split `x` into `P_U x + (x - P_U x)`.
2. Use the two conjuncts of `hU` to put the images of those summands in `U`
   and `Uᗮ` respectively.
3. Project the split image; the first summand is fixed and the second vanishes.
4. Upgrade the pointwise equality to equality of continuous linear maps.
-/
theorem projection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    projection U ∘L A = A ∘L projection U := by
  ext x
  change U.starProjection (A x) = A (U.starProjection x)
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal x
  have hApx : A (U.starProjection x) ∈ U := hU.1 _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hU.2 _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    rw [← map_add]
    congr 1
    abel
  rw [hsplit, map_add,
    Submodule.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest,
    add_zero]

/-- Pointwise form of `projection_comp_comm_of_reduces`.

Lean proof route for a weaker agent:

1. Evaluate the map equality at `x` with `congrArg`.
2. Simplify both compositions with `ContinuousLinearMap.comp_apply`.
-/
theorem projection_apply_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) (x : E) :
    projection U (A x) = A (projection U x) := by
  have h := congrArg (fun T : E →L[𝕜] E => T x)
    (projection_comp_comm_of_reduces A U hU)
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- Reflection through a closed subspace, using mathlib's bundled
linear isometry. -/
noncomputable def reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.reflection.toLinearIsometry.toContinuousLinearMap

/-- Pointwise formula for the reflection.

Lean proof route for a weaker agent:

1. Unfold `reflectionOperator` and `projection`.
2. Apply mathlib's `Submodule.reflection_apply` theorem.
-/
theorem reflectionOperator_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    reflectionOperator U x = (2 : 𝕜) • projection U x - x := by
  change U.reflection x = (2 : 𝕜) • U.starProjection x - x
  rw [Submodule.reflection_apply, ← Nat.cast_smul_eq_nsmul 𝕜]
  norm_num

/-- Reflection is an involution.

Lean proof route for a weaker agent:

1. Extensionalize at an arbitrary vector.
2. Reduce to `Submodule.reflection_reflection`.
-/
theorem reflectionOperator_involutive (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    reflectionOperator U ∘L reflectionOperator U =
      ContinuousLinearMap.id 𝕜 E := by
  ext x
  change U.reflection (U.reflection x) = x
  exact U.reflection_reflection x

/-- Reflection preserves norms and is onto.

Lean proof route for a weaker agent:

1. Use `LinearIsometryEquiv.norm_map` for norm preservation.
2. Use surjectivity of the bundled equivalence.
-/
theorem reflectionOperator_isUnitary (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsUnitaryOperator (reflectionOperator U) := by
  refine ⟨?_, ?_⟩
  · intro x
    change ‖U.reflection x‖ = ‖x‖
    exact U.reflection.norm_map x
  · change Function.Surjective U.reflection
    exact U.reflection.surjective

/-- The reflection has operator norm at most one, including on the zero space.

Lean proof route for a weaker agent:

1. Apply `ContinuousLinearMap.opNorm_le_bound` with bound one.
2. Discharge the pointwise estimate using reflection's exact norm preservation.
-/
theorem norm_reflectionOperator_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : ‖reflectionOperator U‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖U.reflection x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using le_of_eq (U.reflection.norm_map x)

/-- A reducing operator commutes with the corresponding reflection.

Lean proof route for a weaker agent:

1. Expand both reflections as `2P-I` pointwise.
2. Rewrite `P(Ax)` with `projection_apply_comm_of_reduces`.
3. Use linearity of `A` to normalize both sides.
-/
theorem reflectionOperator_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    reflectionOperator U ∘L A = A ∘L reflectionOperator U := by
  ext x
  change reflectionOperator U (A x) = A (reflectionOperator U x)
  rw [reflectionOperator_apply, reflectionOperator_apply,
    projection_apply_comm_of_reduces A U hU, map_sub, map_smul]

/-- Complementary projection as `I-P`, pointwise.

Lean proof route for a weaker agent:

1. Unfold both projection abbreviations.
2. Rewrite with `Submodule.starProjection_orthogonal` and simplify.
-/
theorem complementaryProjection_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    complementaryProjection U x = x - projection U x := by
  simp only [complementaryProjection, projection]
  rw [Submodule.starProjection_orthogonal]
  simp

/-- Twice the diagonal pinch is the average numerator `A + JAJ`.

Lean proof route for a weaker agent:

1. Extensionalize and replace every complementary projection by `I-P`.
2. Replace both reflections by `2P-I`.
3. Push `A` and `P` through sums and scalar multiples.
4. Close the resulting module identity with `module`.
-/
theorem two_smul_diagonalPart_eq_add_reflectionConjugate
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (2 : 𝕜) • diagonalPart U A =
      A + reflectionOperator U ∘L A ∘L reflectionOperator U := by
  ext x
  simp only [diagonalPart, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply]
  simp_rw [complementaryProjection_apply, reflectionOperator_apply]
  simp only [map_sub, map_smul]
  module

/-- Twice the off-diagonal extraction is `A-JAJ`.

Lean proof route for a weaker agent:

1. Unfold `offDiagonalPart`.
2. Distribute the scalar over subtraction.
3. Rewrite the diagonal term with
   `two_smul_diagonalPart_eq_add_reflectionConjugate`.
4. Normalize the additive identity with `module`.
-/
theorem two_smul_offDiagonalPart_eq_sub_reflectionConjugate
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (2 : 𝕜) • offDiagonalPart U A =
      A - reflectionOperator U ∘L A ∘L reflectionOperator U := by
  unfold offDiagonalPart
  rw [smul_sub, two_smul_diagonalPart_eq_add_reflectionConjugate]
  module

/-- Double-angle residual map for an isometric approximate invariant pair.

The eventual implementation should construct the orthogonal projection onto
`LinearMap.range X` from `hX : IsometricEmbedding X` and return the ambient
cross block representing `sin (2 Θ(U, range X))`.  It is kept abstract here
until the closed-range/isometry bridge is available.
-/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E := by
  sorry

/-- The gap metric is symmetric. 

Lean proof route for a weaker agent:

1. Rewrite `projection V - projection U = -(projection U - projection V)`.
2. Use norm invariance under negation.
3. Unfold `subspaceGap`.


Ext-agent signature audit (GPT 5.6 High): Correct and definitionally independent of
acuteness. The proof should use only norm invariance under negation.

Preferred dependency route: Prove this in the bounded projection-geometry core, using
only `Basic` definitions and mathlib Hilbert-space projection lemmas; all finite
versions should later specialize this result.
-/
theorem subspaceGap_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    subspaceGap U V = subspaceGap V U := by
  unfold subspaceGap
  rw [show projection V - projection U = -(projection U - projection V) by abel,
    norm_neg]

/-- The directed gap is bounded by the symmetric gap. 

Lean proof route for a weaker agent:

1. Expand `(I-Q)P = (P-Q)P` using projection idempotence.
2. Apply submultiplicativity and `‖P‖≤1` for an orthogonal projection.
3. Rewrite the two norms as `directedGap` and `subspaceGap`.


Ext-agent signature audit (GPT 5.6 High): Correct for orthogonal projections. The key
identity is `(I-Q)P = (P-Q)P`, so no equal-dimension or acute hypothesis is needed.

Preferred dependency route: Prove this in the bounded projection-geometry core, using
only `Basic` definitions and mathlib Hilbert-space projection lemmas; all finite
versions should later specialize this result.
-/
theorem directedGap_le_subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedGap U V ≤ subspaceGap U V := by
  have hcomp : complementaryProjection V ∘L projection U =
      (projection U - projection V) ∘L projection U := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply]
    rw [complementaryProjection_apply V (projection U x)]
    rw [show projection U (projection U x) = projection U x by
      exact Submodule.starProjection_eq_self_iff.mpr
        (U.starProjection_apply_mem x)]
  have hP : ‖projection U‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa [projection] using U.norm_starProjection_apply_le x
  unfold directedGap subspaceGap
  rw [hcomp]
  calc
    ‖(projection U - projection V) ∘L projection U‖
        ≤ ‖projection U - projection V‖ * ‖projection U‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖projection U - projection V‖ * 1 :=
      mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ = ‖projection U - projection V‖ := mul_one _

end DavisKahanExt
end ForMathlib
