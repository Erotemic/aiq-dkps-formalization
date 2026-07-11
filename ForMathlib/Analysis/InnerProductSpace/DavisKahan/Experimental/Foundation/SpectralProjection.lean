/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Basic

/-!
# Spectral projections and bounded Borel calculus

This module records the spectral-theorem infrastructure needed for genuinely
infinite-dimensional Davis--Kahan statements.  Mathlib currently has useful
self-adjoint and compact spectral theory, but the roadmap needs a projection-
valued Borel calculus for arbitrary bounded self-adjoint operators.

Literature writeup: local TeX, Sections 5--6.
-/


/-! ## Construction plan

This module needs one coherent projection-valued-measure or Borel-functional-
calculus foundation.

1. Construct `spectralProjection A s` as the indicator functional calculus for
   a self-adjoint operator and a measurable set.
2. Define `spectralSubspace` as its range; derive closedness and the orthogonal
   projection instance from idempotence and self-adjointness.
3. Define `boundedBorelFunctionalCalculus` by integration against the same
   projection-valued measure, not independently.
4. Prove complement, intersection, disjointness, strong countable additivity,
   commutation, and reduction from the measure laws.
5. Keep the complex implementation separate from a future real transfer, while
   stating projection algebra over `RCLike` whenever it no longer depends on
   the calculus.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Spectral projection of a bounded self-adjoint operator associated with a
Borel set.

Construction route: define the indicator function of `s` in a bounded Borel
functional calculus for the self-adjoint operator `A`; prove idempotence and
self-adjointness directly from multiplication and conjugation of indicators. -/
noncomputable def spectralProjection (A : E →L[𝕜] E)
    (s : Set ℝ) : E →L[𝕜] E := by
  sorry

/-- Spectral subspace associated with a Borel set. -/
noncomputable def spectralSubspace (A : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E :=
  LinearMap.range (spectralProjection A s).toLinearMap

/-- Spectral subspaces are closed and admit orthogonal projection.

Proof strategy: prove `spectralProjection A s` is a star projection, identify
its range with `spectralSubspace A s`, and use the generic theorem that the
range of a star projection is closed and has that orthogonal projector. -/
noncomputable instance spectralSubspace_hasOrthogonalProjection
    (A : E →L[𝕜] E) (s : Set ℝ) :
    (spectralSubspace A s).HasOrthogonalProjection := by
  sorry

/-- Bounded Borel functional calculus.

Construction route: integrate bounded Borel functions against one
projection-valued measure associated with `A`; do not construct this
independently from `spectralProjection`, since indicator compatibility is the
main API invariant. -/
noncomputable def boundedBorelFunctionalCalculus (A : E →L[𝕜] E)
    (f : ℝ → ℝ) : E →L[𝕜] E := by
  sorry

/-- Strong countable additivity of a projection-valued measure. -/
def StronglyCountablyAdditive
    (P : Set ℝ → E →L[𝕜] E) : Prop :=
  ∀ (s : ℕ → Set ℝ), (∀ i, MeasurableSet (s i)) →
    (Pairwise fun i j => Disjoint (s i) (s j)) →
    ∀ x, Tendsto
      (fun n => ∑ i ∈ Finset.range n, P (s i) x)
      atTop (nhds (P (⋃ i, s i) x))

/-- `spectralProjection_empty`.


Lean proof route for a weaker agent:

1. Rewrite the empty-set indicator as the zero function.
2. Apply the zero law of the Borel functional calculus.
3. The self-adjointness hypothesis selects the valid spectral calculus instance.


Ext-agent signature audit (GPT 5.6 High): Correct on the self-adjoint domain of the
roadmap spectral calculus. The total definition outside that domain must not be used to
weaken the hypothesis.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
@[simp] theorem spectralProjection_empty (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) :
    spectralProjection A ∅ = 0 := by
  sorry

/-- `spectralProjection_univ`.


Lean proof route for a weaker agent:

1. Rewrite the universal-set indicator as the constant-one function.
2. Apply the unital law of the Borel functional calculus.
3. Simplify the image of `1` to the identity operator.


Ext-agent signature audit (GPT 5.6 High): Correct for a unital spectral calculus. Keep
self-adjointness explicit until the definition itself is bundled with a self-adjoint
operator.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
@[simp] theorem spectralProjection_univ (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) :
    spectralProjection A Set.univ = ContinuousLinearMap.id 𝕜 E := by
  sorry

/-- Multiplicativity of spectral projections. 

Lean proof route for a weaker agent:

1. Rewrite both projections as indicator functions in the Borel calculus.
2. Apply multiplicativity.
3. Simplify the pointwise product of indicators to the indicator of `s∩t` using `hs,ht`.


Ext-agent signature audit (GPT 5.6 High): Correct only for measurable sets; the added
measurability hypotheses are essential for the Borel PVM interface.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem spectralProjection_comp (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    spectralProjection A s ∘L spectralProjection A t =
      spectralProjection A (s ∩ t) := by
  sorry

/-- Every spectral projection is orthogonal. 

Lean proof route for a weaker agent:

1. Use `spectralProjection_comp` with `s=t` for idempotence.
2. Prove self-adjointness because the indicator is real-valued in the self-adjoint functional calculus.
3. Package the two facts as `IsOrthogonalProjection`.


Ext-agent signature audit (GPT 5.6 High): Correct for measurable sets and self-adjoint
`A`. This should become a direct field theorem of the eventual projection-valued measure
package.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem spectralProjection_isOrthogonalProjection
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IsOrthogonalProjection (spectralProjection A s) := by
  sorry

/-- Spectral projections commute with their operator. 

Lean proof route for a weaker agent:

1. Express `A` and `spectralProjection A s` as Borel functions of the same self-adjoint operator.
2. Apply multiplicativity/commutativity of the functional calculus.
3. Use measurability of `s` for the indicator function.


Ext-agent signature audit (GPT 5.6 High): Correct: the identity function is bounded on
the spectrum of a bounded operator, even though it is not globally bounded. The
implementation must use spectrum-restricted boundedness.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem spectralProjection_comm (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) (s : Set ℝ) (hs : MeasurableSet s) :
    A ∘L spectralProjection A s = spectralProjection A s ∘L A := by
  sorry

/-- Spectral subspaces reduce the operator. 

Lean proof route for a weaker agent:

1. Use `spectralProjection_comm` to show the range of the projection is invariant.
2. Use orthogonality of the projection and the same commutation identity to show its kernel is invariant.
3. Identify the kernel with the orthogonal complement of the range and package `Reduces`, avoiding dependence on the later complement theorem.


Ext-agent signature audit (GPT 5.6 High): Correct. Prove both range and kernel
invariance directly from projection commutation; do not depend on the later complement
theorem and create a declaration-order cycle.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem reduces_spectralSubspace (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) (s : Set ℝ) (hs : MeasurableSet s) :
    Reduces A (spectralSubspace A s) := by
  sorry

/-- The spectral projection has the expected range. 

Lean proof route for a weaker agent:

1. Unfold `spectralSubspace`.
2. Close the goal by reflexivity; keep this named theorem as the public rewrite lemma.


Ext-agent signature audit (GPT 5.6 High): Definitionally true with the current
`spectralSubspace`; retain it as a public simp/rewrite theorem rather than spending
spectral-theorem effort here.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem range_spectralProjection (A : E →L[𝕜] E) (s : Set ℝ) :
    LinearMap.range (spectralProjection A s).toLinearMap =
      spectralSubspace A s := by
  sorry

/-- Complementary Borel sets produce complementary projections. 

Lean proof route for a weaker agent:

1. Use the pointwise identity `1_{sᶜ}=1-1_s` for a measurable set.
2. Apply linearity of the Borel functional calculus.
3. Rewrite the constant-one calculus as the identity operator.


Ext-agent signature audit (GPT 5.6 High): Correct only for measurable `s`; complement
measurability and the identity `1_{sᶜ}=1-1_s` are the complete analytic content.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem spectralProjection_compl (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) (s : Set ℝ) (hs : MeasurableSet s) :
    spectralProjection A sᶜ =
      ContinuousLinearMap.id 𝕜 E - spectralProjection A s := by
  sorry

/-- Strong countable additivity of the spectral resolution.

Long-term proof strategy: construct the scalar spectral measures
`mu_x_y(s) = inner (E_A(s) x) y` by the Riesz representation theorem applied
to the continuous functional calculus, then assemble the projection-valued
measure by polarization.  For pairwise disjoint sets, scalar countable
additivity and orthogonality give convergence of partial projection sums on
each vector; identify the limit with the projection of the union by testing
inner products against a dense set.

This theorem is deliberately not on the critical path for the first bounded
Davis--Kahan results.  Gap-selected projections should first be built from
continuous functional calculus on clopen spectral components or from Riesz
contours. 

Lean proof route for a weaker agent:

1. Prove finite additivity first from projection multiplication and disjointness.
2. For a fixed vector, use orthogonality to show partial sums are Cauchy via the Pythagorean identity.
3. Identify the limit by testing inner products and scalar measure countable additivity.
4. Verify the measurable-set premise in `StronglyCountablyAdditive`.


Ext-agent signature audit (GPT 5.6 High): Mathematically correct, but intentionally not
on the first Davis--Kahan critical path. It requires a genuine PVM construction, not
merely a continuous functional calculus on gap-selected clopen sets.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem spectralProjection_stronglyCountablyAdditive (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) :
    StronglyCountablyAdditive (spectralProjection A) := by
  sorry

/-- The support of the spectral resolution is the real spectrum. 

Lean proof route for a weaker agent:

1. The indicator of `s` vanishes on `realSpectrum A` by `h`.
2. Apply functional-calculus extensionality on the spectrum against the zero function.
3. Rewrite the indicator calculus as `spectralProjection A s`.


Ext-agent signature audit (GPT 5.6 High): Correct with measurability. The support
argument should use equality of Borel functions on the spectrum, not global equality.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem spectralProjection_eq_zero_of_disjoint_spectrum
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s)
    (h : Disjoint s (realSpectrum A)) :
    spectralProjection A s = 0 := by
  sorry

/-- Indicator functions recover spectral projections. 

Lean proof route for a weaker agent:

1. Unfold the Borel functional calculus as integration against the spectral measure.
2. Use the integral of an indicator to identify the result with the spectral projection of the measurable set.
3. Discharge the real-to-scalar coercion and normalization at `1` by `simp`.


Ext-agent signature audit (GPT 5.6 High): Correct and should eventually be definitional
if spectral projections are defined as indicator calculus.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem boundedBorelFunctionalCalculus_indicator
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedBorelFunctionalCalculus A (s.indicator fun _ => 1) =
      spectralProjection A s := by
  sorry

/-- Functional calculus is multiplicative. 

Lean proof route for a weaker agent:

1. Approximate the bounded measurable functions by bounded simple functions on the spectrum.
2. Prove multiplicativity for indicators using `spectralProjection_comp`, then for simple functions by finite algebra.
3. Pass to bounded pointwise limits using the norm bound and the monotone-class/dominated-convergence extension used to construct the calculus.


Ext-agent signature audit (GPT 5.6 High): Correct for measurable functions bounded on
the spectrum. The product is automatically bounded on the spectrum, so no separate
product hypothesis is needed.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem boundedBorelFunctionalCalculus_mul
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : BoundedOnSpectrum A f) (hgb : BoundedOnSpectrum A g) :
    boundedBorelFunctionalCalculus A (fun x => f x * g x) =
      boundedBorelFunctionalCalculus A f ∘L
        boundedBorelFunctionalCalculus A g := by
  sorry

/-- Norm control by the essential supremum on the spectrum. 

Lean proof route for a weaker agent:

1. Use the spectral integral representation of the Borel calculus.
2. For each vector, bound the squared norm integral by `C²‖x‖²` using `hC` and support on the spectrum.
3. Take square roots and then the operator norm supremum.
4. Use `hf` only to justify the spectral integral construction.


Ext-agent signature audit (GPT 5.6 High): Correct. This is a uniform-supremum bound, not
an essential-supremum statement unless scalar spectral measures are explicitly
introduced.

Preferred dependency route: Implement the bounded self-adjoint spectral measure/Borel
calculus first, then discharge this as a calculus law. Do not route through finite
diagonalization.
-/
theorem norm_boundedBorelFunctionalCalculus_le
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ realSpectrum A, |f x| ≤ C) :
    ‖boundedBorelFunctionalCalculus A f‖ ≤ C := by
  sorry

end DavisKahanExt
end ForMathlib
