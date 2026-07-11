/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Basic
import ForMathlib.Analysis.InnerProductSpace.KyFan
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Rectangular unitarily invariant norms

The residual forms of the Davis--Kahan theorems compare maps between different
finite-dimensional Hilbert spaces.  The existing
`ForMathlib.UnitarilyInvariantNorm` is square.  This file scaffolds the
rectangular abstraction needed for the final literature-faithful API.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 3, 6, and 7.
* Davis--Kahan (1970), Sections 1--2 and Lemmas 6.1--6.3.
* Mirsky's symmetric-gauge correspondence, as invoked in Davis--Kahan (1970).

The intended proof path is singular-value majorization plus the ideal
property.  Square norms should be recovered without duplicating the existing
`UnitarilyInvariantNorm` development.
-/


/-! ## Remaining construction plan

Complete this module in the following order: adjoint transport, zero extension,
singular values of zero extension, square/rectangular conversion, then concrete
norm objects.  Define rectangular operator, Frobenius, Ky Fan, nuclear, and
Schatten norms from rectangular singular values (or zero extension) and prove
unitary invariance and ideal inequalities before using them in residual
results.  The evaluation lemmas should be definitional or short consequences
of `singularValues_zeroExtension`, so later concrete wrappers carry no new
analytic content.
-/


/-! ## Weak-agent execution plan: rectangular singular values and UI norms

Treat this file as an API-building project, not as a list of independent
`sorry`s.  The following order avoids circularity and uses machinery already
present in this repository.

### A. Establish the rectangular SVD/gauge seam first

The hard root of `apply_le_of_kyFanSum_le` is not zero extension.  It is the
fact that a rectangular UI seminorm depends only on the singular values.
Introduce private helpers before attempting Fan dominance:

* `rectangularDiagonal` on fixed orthonormal bases, sending the first
  `min (finrank 𝕜 E) (finrank 𝕜 F)` basis vectors to the corresponding
  nonnegative diagonal entries and the rest to zero;
* `exists_rectangular_svd`, returning `U : F ≃ₗᵢ[𝕜] F`,
  `V : E ≃ₗᵢ[𝕜] E`, and a diagonal map `D` with
  `A = U.toLinearMap ∘ₗ D ∘ₗ V.toLinearMap`;
* `singularValues_rectangularDiagonal`, including the zero-padding statement;
* a finite symmetric gauge obtained by evaluating `N` on
  `rectangularDiagonal`.

Build `exists_rectangular_svd` from eigenbases of `A.adjoint ∘ₗ A` and the
polar vectors `A vᵢ / σᵢ`.  Split indices with `σᵢ = 0`; complete the resulting
orthonormal family in `F`.  Do not divide before introducing the nonzero
singular-value hypothesis.  Equality of maps should be proved by
`LinearMap.ext` followed by expansion in the domain eigenbasis.

Once this seam exists, copy the gauge-level weak-majorization descent from
`UnitarilyInvariantNorm.apply_le_of_kyFanSum_le`; do not duplicate operator
algebra from that file.  This yields rectangular Fan dominance directly and
makes `apply_le_of_singularValues_le` a finite-sum corollary.

### B. Prove the ideal inequalities only after Fan dominance

The repository already contains the rectangular singular-value estimate
`singularValues_comp_le` in `KyFan.lean`.  For the left ideal property, set
`c := ‖C.toContinuousLinearMap‖`, prove

`(C ∘ₗ A).singularValues i ≤ c * A.singularValues i`,

identify the right side with the singular values of `((c : 𝕜) • A)` using
`singularValues_real_smul`, apply `apply_le_of_singularValues_le`, and finish
with `N.smul_eq`.  The right ideal property should be obtained by applying the
left result to adjoints after `adjointTransport` is available; this avoids
reproving the Gram-order argument for a genuinely rectangular right factor.

### C. Implement `adjointTransport` directly

Use `toFun A := N A.adjoint`.  The additive and scalar fields follow from the
adjoint laws; remember that the adjoint of `c • A` uses `star c`, whose norm is
`‖c‖`.  For invariance, adjoint reverses composition, so the two unitary
arguments swap and become their adjoints/symmetries.  Prove
`adjointTransport_apply` by `rfl` if possible.  Add private simp lemmas for the
adjoint of the relevant threefold composition rather than asking `simp` to
normalize every coercion at once.

### D. Keep zero extension secondary and define it pointwise

The existing `LinearMap.singularValues` is already rectangular, so zero
extension is only a compatibility tool.  Define

`zeroExtension A (x,y) = (0, A x)`

on `WithLp 2 (E × F)`.  A robust implementation constructs the map with
`toFun z := WithLp.toLp 2 (0, A (WithLp.ofLp z).1)` and proves linearity by
extensionality on the two product coordinates.  Immediately add simp lemmas
for its application and adjoint.  For `singularValues_zeroExtension`, prove the
Gram operator is block diagonal with blocks `A.adjoint ∘ₗ A` and `0`; then use
an orthonormal basis formed by concatenating eigenvectors of the first block
with any orthonormal basis of `F`.  Handle `i < finrank 𝕜 E` and the zero tail
as separate cases; do not attempt a single `simp` proof of the sorted sequence.

### E. Concrete norms

Construct concrete norms in this order:

1. `kyFan k` from `rectangularKyFanSum`; prove its triangle inequality by the
   rectangular Ky Fan variational principle already used in `KyFan.lean`.
2. `nuclear` as `kyFan (finrank 𝕜 E)`; zero padding makes this valid even when
   the codomain is smaller.
3. `opNorm` either from the ordinary continuous-linear-map norm or from
   `kyFan 1`; the ordinary norm gives the shortest structure proof.
4. `frobenius` from the basis sum of squares, using the existing square proof
   as a template and a rectangular Parseval calculation.
5. `schatten p` only after a finite `ℓp` symmetric-gauge lemma is available.

Do not define all five through `ofSquareFamily`; that constructor is useful for
compatibility tests, but it hides the evaluation lemmas needed downstream.
`toRectangular` in the square case should be the direct structure copy, making
`toRectangular_apply` definitional.  `ofSquareFamily` may use zero extension,
but its documentation must not claim dimension-independent uniqueness unless
compatibility between the supplied square norms is added as a hypothesis.

### F. Elaboration traps

* Distinguish `A.adjoint` as a `LinearMap` from continuous-map adjoints.
* Normalize `LinearMap.comp_apply` explicitly before rewriting pointwise.
* Use real scalar coercions `((c : ℝ) : 𝕜)` when invoking
  `singularValues_real_smul`.
* Split zero-dimensional spaces before using a norm-one or basis witness.
* Prove sequence equalities with `funext i` and explicit rank cases; sorted
  singular-value functions rarely close by `simp` globally.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

/-- A unitarily invariant seminorm on rectangular linear maps.

As in the existing square `UnitarilyInvariantNorm`, definiteness is deliberately
not bundled: the Davis--Kahan inequalities and Fan dominance use only
subadditivity, absolute homogeneity, and two-sided unitary invariance. -/
structure RectangularUnitarilyInvariantNorm (𝕜 E F : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] where
  toFun : (E →ₗ[𝕜] F) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) A, toFun (a • A) = ‖a‖ * toFun A
  invariant' : ∀ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) A,
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

namespace RectangularUnitarilyInvariantNorm

/-- Prefix sum of singular values for a rectangular map. -/
noncomputable def rectangularKyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)

instance : CoeFun (RectangularUnitarilyInvariantNorm 𝕜 E F)
    fun _ => (E →ₗ[𝕜] F) → ℝ :=
  ⟨RectangularUnitarilyInvariantNorm.toFun⟩

variable (N : RectangularUnitarilyInvariantNorm 𝕜 E F)

/--
Lean proof route for a weaker agent:

1. Derive `N 0 ≤ N 0 + N 0` from `add_le'` and use homogeneity at scalar zero to rewrite the left side.
2. Use nonnegativity of the codomain real norm value, or the same triangle/homogeneity argument used by the square UI-norm implementation.
3. Finish with antisymmetry; keep this as a structure-level lemma with no singular-value dependency.
-/
@[simp] theorem apply_zero : N (0 : E →ₗ[𝕜] F) = 0 := by
  have h := N.smul' 0 (0 : E →ₗ[𝕜] F)
  simpa using h

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem nonneg (A : E →ₗ[𝕜] F) : 0 ≤ N A := by
  have h := N.add_le' A (-A)
  rw [add_neg_cancel] at h
  have hneg : N.toFun (-A) = N.toFun A := by
    have h1 := N.smul' (-1) A
    simpa using h1
  have hz : N.toFun (0 : E →ₗ[𝕜] F) = 0 := apply_zero N
  rw [hz, hneg] at h
  linarith

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem add_le (A B : E →ₗ[𝕜] F) : N (A + B) ≤ N A + N B :=
  N.add_le' A B

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem smul_eq (a : 𝕜) (A : E →ₗ[𝕜] F) : N (a • A) = ‖a‖ * N A :=
  N.smul' a A

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem invariant (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) :
    N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = N A :=
  N.invariant' U V A

/-- Left ideal property.

Lean proof route for a weaker agent:

1. Prove the Ky Fan prefix inequalities for the singular values of the composition using the finite ideal inequality `s_j(CA) ≤ ‖C‖ s_j(A)` (or its right-handed form).
2. Sum the prefix inequalities and invoke finite Fan dominance for the symmetric gauge defining `N`.
3. Rewrite scalar multiplication through `smul_eq` and normalize the operator norm coercions.
-/
theorem comp_le_opNorm_mul (C : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N (C ∘ₗ A) ≤ ‖C.toContinuousLinearMap‖ * N A := by
  sorry

/-- Right ideal property.

Lean proof route for a weaker agent:

1. Prove the Ky Fan prefix inequalities for the singular values of the composition using the finite ideal inequality `s_j(CA) ≤ ‖C‖ s_j(A)` (or its right-handed form).
2. Sum the prefix inequalities and invoke finite Fan dominance for the symmetric gauge defining `N`.
3. Rewrite scalar multiplication through `smul_eq` and normalize the operator norm coercions.
-/
theorem comp_le_mul_opNorm (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E) :
    N (A ∘ₗ C) ≤ N A * ‖C.toContinuousLinearMap‖ := by
  sorry

/-- Fan dominance in rectangular form.

Lean proof route for a weaker agent:

1. Transfer `N` to its finite symmetric gauge on singular values and apply the Ky Fan dominance theorem already developed in `KyFan.lean`.
2. Translate `rectangularKyFanSum` to the square zero-extension convention.
3. Apply the existing square Fan-dominance theorem and simplify `ofSquareFamily`.
-/
theorem apply_le_of_kyFanSum_le {A B : E →ₗ[𝕜] F}
    (h : ∀ k, rectangularKyFanSum k A ≤ rectangularKyFanSum k B) : N A ≤ N B := by
  sorry

/-- Pointwise singular-value dominance implies norm dominance.

Lean proof route for a weaker agent:

1. Sum the pointwise inequalities to obtain all Ky Fan prefix inequalities, then apply `apply_le_of_kyFanSum_le`.
2. Sum the pointwise inequalities over each finite prefix using `Finset.sum_le_sum`.
3. Invoke `apply_le_of_kyFanSum_le` with the resulting prefix inequalities.
-/
theorem apply_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) : N A ≤ N B := by
  sorry

/-- Adjoint transport to the transposed rectangular norm. -/
noncomputable def adjointTransport
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F) :
    RectangularUnitarilyInvariantNorm 𝕜 F E := by
  sorry

/--
Lean proof route for a weaker agent:

1. Unfold `adjointTransport`; the theorem is the defining equation of the transported rectangular UI norm.
2. Prove it by `rfl` after the constructor is implemented, or by the constructor simp lemma.
-/
@[simp] theorem adjointTransport_apply (A : E →ₗ[𝕜] F) :
    (adjointTransport N).toFun A.adjoint = N.toFun A := by
  sorry

/-- Zero extension of a rectangular map to a square endomorphism. -/
noncomputable def zeroExtension (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) := by
  sorry

/-- Singular values are unchanged by zero extension, apart from zero padding.

Lean proof route for a weaker agent:

1. Choose orthonormal bases of `E` and `F`; the zero extension is the block matrix with `A` in one off-diagonal block, so its Gram operator is `A⋆A` plus a zero block.
2. Compare sorted eigenvalues with zero padding.
-/
theorem singularValues_zeroExtension (A : E →ₗ[𝕜] F) :
    (zeroExtension A).singularValues = A.singularValues := by
  sorry

/-- Every square unitarily invariant norm has a compatible rectangular
extension, unique after fixing its symmetric gauge family across dimensions. -/
noncomputable def ofSquareFamily
    (Ns : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [FiniteDimensional 𝕜 H], UnitarilyInvariantNorm 𝕜 H) :
    RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- Operator norm as a rectangular UI norm. -/
noncomputable def opNorm : RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- Frobenius/Hilbert--Schmidt norm as a rectangular UI norm. -/
noncomputable def frobenius : RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- Ky Fan `k`-norm. -/
noncomputable def kyFan (k : ℕ) : RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- Nuclear/trace norm. -/
noncomputable def nuclear : RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- Schatten `p`-norm for `1 ≤ p`. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- The rectangular Frobenius norm is the square root of the sum of squared
column norms in any orthonormal basis of the domain.

Lean proof route for a weaker agent:

1. Unfold the rectangular Frobenius norm through zero extension or its singular values and reuse Parseval/the existing square Frobenius basis formula.
2. Rewrite the zero extension on the canonical L² direct-sum basis and eliminate the codomain-only basis vectors.
3. Use `Real.sqrt_eq_iff_sq_eq` only after proving nonnegativity of the finite sum.
-/
theorem frobenius_apply (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    frobenius A = Real.sqrt (∑ i, ‖A (b i)‖ ^ 2) := by
  sorry

/-- The Ky Fan norm evaluates to the prefix sum of singular values.

Lean proof route for a weaker agent:

1. This should be definitional once `kyFan` is constructed from `rectangularKyFanSum`
2. otherwise reduce through the zero-extension square norm.
-/
theorem kyFan_apply (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFan k A = rectangularKyFanSum k A := by
  sorry

end RectangularUnitarilyInvariantNorm

/-- Restrict a rectangular UI norm to square maps. -/
noncomputable def RectangularUnitarilyInvariantNorm.toSquare
    (N : RectangularUnitarilyInvariantNorm 𝕜 E E) :
    UnitarilyInvariantNorm 𝕜 E := by
  sorry

end DavisKahanTheory

namespace UnitarilyInvariantNorm

open DavisKahanTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Embed the existing square abstraction into the rectangular API. -/
noncomputable def toRectangular
    (N : UnitarilyInvariantNorm 𝕜 E) :
    RectangularUnitarilyInvariantNorm 𝕜 E E := by
  sorry

/--
Lean proof route for a weaker agent:

1. Unfold `UnitarilyInvariantNorm.toRectangular` and the zero-extension bridge.
2. The proof should be definitional once the square-to-rectangular constructor is implemented.
-/
@[simp] theorem toRectangular_apply
    (N : UnitarilyInvariantNorm 𝕜 E) (A : E →ₗ[𝕜] E) :
    N.toRectangular A = N A := by
  sorry

end UnitarilyInvariantNorm
end ForMathlib
