/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Residual
import ForMathlib.Analysis.InnerProductSpace.SylvesterBound

/-!
# Sylvester equations under spectral separation

This file scaffolds the rectangular, every-unitarily-invariant-norm Sylvester
machinery implicit in the Davis--Kahan proofs.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 6.
* Davis--Kahan (1970), Section 5, "On the equation `AX-XB=C`".
* The ordered/coercive special case already proved in
  `ForMathlib/Analysis/InnerProductSpace/SylvesterBound.lean`.

The interval/exterior theorem has sharp constant one.  The final theorem in
this file records the separate `π/2`-constant extension for arbitrary disjoint
spectral sets; it must not be used silently in the classic constant-one API.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Sylvester operator `X ↦ A X - X B`. -/
noncomputable def sylvesterOperator (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) := by
  sorry

/-- Ordered spectral separation for the Sylvester equation. -/
def OrderedSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (δ : ℝ) : Prop :=
  OrderedGap B ⊤ A ⊤ δ ∨ OrderedGap A ⊤ B ⊤ δ

/-- Interval/exterior separation with the spectrum of `B` in `[a,b]` and the
spectrum of `A` outside `(a-δ,b+δ)`. -/
def IntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  SpectrumIn B ⊤ (Set.Icc a b) ∧
    SpectrumIn A ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- The Sylvester operator is injective under positive spectral separation.

Lean proof route for a weaker agent:

1. Preferred route: specialize uniqueness from `DavisKahanExt.sylvester_unique` through the finite continuous-linear-map bridge.
2. A direct eigenbasis proof is also immediate from nonzero scalar denominators.
-/
theorem sylvesterOperator_injective {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ) :
    Function.Injective (sylvesterOperator A B) := by
  sorry

/-- Unique solution of the finite-dimensional Sylvester equation. -/
noncomputable def solveSylvester (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (C : E →ₗ[𝕜] F) : E →ₗ[𝕜] F := by
  sorry

/-- The chosen solution satisfies the Sylvester equation under separation.

Lean proof route for a weaker agent:

1. Preferred route: specialize `DavisKahanExt.sylvester_solve`.
2. If the finite `solveSylvester` remains an eigenbasis definition, prove this entrywise and use separation to divide by every eigenvalue difference.
-/
theorem sylvesterOperator_solveSylvester {A : F →ₗ[𝕜] F}
    {B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (C : E →ₗ[𝕜] F) :
    A ∘ₗ solveSylvester A B C - solveSylvester A B C ∘ₗ B = C := by
  sorry

/-- Sharp constant-one ordered Sylvester estimate in every rectangular UI
norm.

Lean proof route for a weaker agent:

1. Use the existing finite `SylvesterBound` coercive theorem or specialize the Ext ordered operator-norm theorem for the op-norm case.
2. For arbitrary UI norms, prove Ky Fan domination and invoke finite Fan dominance.
-/
theorem uiNorm_sylvester_le_of_orderedGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedSylvesterGap A B δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  sorry

/-- Sharp constant-one interval/exterior Sylvester estimate in every
rectangular UI norm.

Lean proof route for a weaker agent:

1. Split the exterior spectrum into the lower and upper ordered pieces, solve on the corresponding spectral blocks, establish Ky Fan domination with constant one, and combine by pinching.
2. The operator-norm skeleton may reuse `DavisKahanExt.SinTheta`/`Sylvester`.
-/
theorem uiNorm_sylvester_le_of_intervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  sorry

/-- Singular-value/Ky Fan form from which Fan dominance yields the preceding
UI-norm theorem.

Lean proof route for a weaker agent:

1. Diagonalize `A` and `B`, express the solution as a Schur multiplier with denominators at least `δ`, and apply the finite singular-value/majorization lemma used in Davis--Kahan Section 5.
2. Prove prefix-sum domination for the singular values of the Schur multiplier solution.
3. Rewrite the prefixes as `rectangularKyFanSum` and preserve the factor `δ` by nonnegative scalar arithmetic.
-/
theorem kyFan_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  sorry

/-- Ordered positivity/coercivity form used by the existing integral-free
proof.

Lean proof route for a weaker agent:

1. Dispatch through the already proved `ForMathlib.SylvesterBound` theorem after converting its norm abstraction to the rectangular UI API.
2. This is the fastest direct finite route.
-/
theorem uiNorm_sylvester_le_of_form_bounds
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  sorry

/-- General disjoint-spectrum extension with the Bhatia--Davis--McIntosh
constant `π/2`.  This is beyond the sharp interval/exterior classic theorem
but belongs in the complete finite-dimensional roadmap.

Lean proof route for a weaker agent:

1. Prefer specialization of `DavisKahanExt.ideal_sylvester_le` once the Ext ideal signature is corrected
2. alternatively formalize the finite Bhatia--Davis--McIntosh multiplier and finish by Fan dominance.
-/
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  sorry

end DavisKahanTheory
end ForMathlib
