/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.OperatorAngle

/-!
# Symmetric norm ideals

Infinite-dimensional unitarily invariant norm statements live on compact
operator ideals, not on all bounded operators.  This file records the ideal
API needed to lift operator-norm Davis--Kahan estimates to Schatten, trace,
Hilbert--Schmidt, and general symmetric ideals.

Literature writeup: local TeX, Section 9.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A symmetric norm ideal of bounded operators on a Hilbert space. -/
structure SymmetricNormIdeal where
  mem : (E →L[𝕜] E) → Prop
  gauge : (E →L[𝕜] E) → ℝ
  zero_mem : mem 0
  add_mem : ∀ {A B}, mem A → mem B → mem (A + B)
  smul_mem : ∀ (c : 𝕜) {A}, mem A → mem (c • A)
  ideal_mem : ∀ (L R : E →L[𝕜] E) {A}, mem A → mem (L ∘L A ∘L R)
  nonneg : ∀ A, 0 ≤ gauge A
  triangle : ∀ A B, gauge (A + B) ≤ gauge A + gauge B
  ideal_bound : ∀ (L R : E →L[𝕜] E) A,
    gauge (L ∘L A ∘L R) ≤ ‖L‖ * gauge A * ‖R‖

namespace SymmetricNormIdeal

/-- The operator norm ideal. -/
noncomputable def operatorNorm : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Compact-operator ideal equipped with the operator norm. -/
noncomputable def compactOperator :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Schatten `p` ideal. -/
noncomputable def schatten (p : ℝ) : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Trace-class ideal. -/
noncomputable def traceClass : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Hilbert--Schmidt ideal. -/
noncomputable def hilbertSchmidt : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Ky Fan ideal seminorm. -/
noncomputable def kyFan (k : ℕ) : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Unitary invariance of a symmetric ideal norm. -/
theorem gauge_unitary_conjugation
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U Uinv A : E →L[𝕜] E)
    (hleft : Uinv ∘L U = ContinuousLinearMap.id 𝕜 E)
    (hright : U ∘L Uinv = ContinuousLinearMap.id 𝕜 E) :
    I.gauge (U ∘L A ∘L Uinv) = I.gauge A := by
  sorry

/-- Pinching is contractive for every symmetric norm ideal. -/
theorem gauge_diagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) :
    I.gauge (diagonalPart U A) ≤ I.gauge A := by
  sorry

/-- Off-diagonal extraction has norm at most one in the sharp symmetric-ideal
form used by the double-angle theorems. -/
theorem gauge_offDiagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) :
    I.gauge (offDiagonalPart U A) ≤ I.gauge A := by
  sorry

end SymmetricNormIdeal
end DavisKahanExt
end ForMathlib
