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
  gauge_smul : ∀ (c : 𝕜) A, gauge (c • A) = ‖c‖ * gauge A
  unitary_invariant : ∀ (U Uinv A : E →L[𝕜] E),
    IsUnitaryOperator U → IsUnitaryOperator Uinv →
    Uinv ∘L U = ContinuousLinearMap.id 𝕜 E →
    U ∘L Uinv = ContinuousLinearMap.id 𝕜 E →
    gauge (U ∘L A ∘L Uinv) = gauge A
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
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
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

/-- Unitary invariance of a symmetric ideal norm. 

Lean proof route for a weaker agent:

1. Apply the structure field `unitary_invariant` with the supplied unitary and inverse hypotheses.
2. If the final structure is refactored to one unitary plus adjoint, first prove the supplied inverse equals the adjoint.
3. Keep `hA` available for downstream membership lemmas even though equality of the total gauge is immediate.
-/
theorem gauge_unitary_conjugation
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U Uinv A : E →L[𝕜] E) (hA : I.mem A)
    (hU : IsUnitaryOperator U) (hUinv : IsUnitaryOperator Uinv)
    (hleft : Uinv ∘L U = ContinuousLinearMap.id 𝕜 E)
    (hright : U ∘L Uinv = ContinuousLinearMap.id 𝕜 E) :
    I.gauge (U ∘L A ∘L Uinv) = I.gauge A := by
  sorry

/-- Pinching is contractive for every symmetric norm ideal. 

Lean proof route for a weaker agent:

1. Let `J=2P-I`; show `J` is unitary and `diagonalPart U A = (A+J A J)/2`.
2. Use ideal membership under left/right multiplication to obtain membership of `J A J` and the sum.
3. Apply unitary invariance, homogeneity, and the triangle inequality to get the sharp contraction bound.
-/
theorem gauge_diagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : I.mem A) :
    I.mem (diagonalPart U A) ∧
      I.gauge (diagonalPart U A) ≤ I.gauge A := by
  sorry

/-- Off-diagonal extraction has norm at most one in the sharp symmetric-ideal
form used by the double-angle theorems. 

Lean proof route for a weaker agent:

1. Use `offDiagonalPart U A = (A-J A J)/2` for the reflection `J=2P-I`.
2. Prove membership using the ideal axioms and scalar closure.
3. Apply unitary invariance and the triangle inequality exactly as in the pinching lemma.
-/
theorem gauge_offDiagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : I.mem A) :
    I.mem (offDiagonalPart U A) ∧
      I.gauge (offDiagonalPart U A) ≤ I.gauge A := by
  sorry

end SymmetricNormIdeal
end DavisKahanExt
end ForMathlib
