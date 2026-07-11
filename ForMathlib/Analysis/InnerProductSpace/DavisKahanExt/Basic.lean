/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Mathlib

/-!
# Infinite-dimensional Davis--Kahan foundations

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
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

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
complement. -/
theorem reduces_orthogonalComplement {A : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : Reduces A U := by
  sorry

/-- The gap metric is symmetric. -/
theorem subspaceGap_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    subspaceGap U V = subspaceGap V U := by
  sorry

/-- The directed gap is bounded by the symmetric gap. -/
theorem directedGap_le_subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedGap U V ≤ subspaceGap U V := by
  sorry

end DavisKahanExt
end ForMathlib
