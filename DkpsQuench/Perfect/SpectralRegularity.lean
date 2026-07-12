/-
Random spectral regularity for Perfect Quench.

The production growing theorem currently assumes a population eigenvalue floor
and ceiling for every reference-sampling outcome.  That is stronger than the
probabilistic setting warrants.  This module replaces those global assumptions
by a high-probability spectral event derived from:

* compact bounded perspectives;
* iid reference sampling;
* one population covariance nondegeneracy condition.

The lemmas are intentionally split into probability, covariance-to-Gram, target
augmentation, and eigenvalue comparison steps so no single proof must solve the
whole argument.
-/

import DkpsQuench.Perfect.PopulationGeometry

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open scoped RealInnerProductSpace InnerProductSpace Matrix
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench.Perfect

open Acharyya2024
open Acharyya2025.Bridge
open Acharyya2025.Deterministic
open Acharyya2025.MatrixPerturbation
open DkpsQuench.GrowingAcharyyaBridge

universe u v wr

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]

/-- Population covariance matrix around the center supplied by the
nondegeneracy certificate. -/
noncomputable def perspectiveCovarianceMatrix
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d) (center : Vec d) : DisMat d :=
  fun i j => ∫ f, (ψ f - center) i * (ψ f - center) j ∂Pf

/-- Stage-`n` reference perspective configuration. -/
def referencePerspectiveConfig
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) : Config n d :=
  fun i => ψ (f_ref n ωref i)

/-- Sample-centered empirical covariance of the reference perspectives.

Using the sample centroid here is essential: this matrix is exactly the
feature-space scatter associated with the centered Gram matrix used by CMDS.
The probability proof must therefore control both empirical second moments and
the empirical mean; a covariance about a fixed population center would have the
wrong inequality direction for the later spectral floor. -/
noncomputable def referenceEmpiricalCovariance
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) : DisMat d :=
  fun a b => (n : Real)⁻¹ *
    ∑ i : Fin n,
      centerConfig (referencePerspectiveConfig ψ f_ref n ωref) i a *
      centerConfig (referencePerspectiveConfig ψ f_ref n ωref) i b

/-- Empirical mean of one perspective coordinate over the stage references. -/
noncomputable def referenceCoordinateMean
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (a : Fin d) : Real :=
  (n : Real)⁻¹ * ∑ i : Fin n, ψ (f_ref n ωref i) a

/-- Empirical mean of one coordinate product over the stage references. -/
noncomputable def referenceCoordinateProductMean
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (a b : Fin d) : Real :=
  (n : Real)⁻¹ * ∑ i : Fin n,
    ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b

/-- Algebraic expansion of one sample-centered covariance entry.

Unfold the centroid, distribute both finite sums, and use
`Finset.sum_mul`/`Finset.mul_sum`.  This theorem is deliberately probability
free; the scalar covariance weak law should only have to combine convergence
of the three quantities displayed here.

Implementation recipe (execute in this order):
1. Unfold `referenceEmpiricalCovariance`, `referenceCoordinateMean`,
   `referenceCoordinateProductMean`, `centerConfig`, and `configCentroid` at the
   fixed coordinates `a,b`.
2. Rewrite the centroid coordinates as the corresponding empirical means.
3. Expand `(x_i - x̄_a) * (y_i - x̄_b)` inside the finite sum.
4. Use `Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
   `Finset.sum_mul`, and `Finset.mul_sum` to collect terms.
5. Simplify the two sums of constants with `Fintype.card_fin`; cancel
   `(n : Real)⁻¹ * n` in the nonzero case.
6. Handle `n = 0` separately by `cases n`; both sides simplify to zero.  For
   `n+1`, prove the cast is nonzero and finish with `ring`.
7. Keep this theorem purely algebraic and use it as the only covariance
   expansion downstream.
-/
theorem referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (a b : Fin d) :
    referenceEmpiricalCovariance ψ f_ref n ωref a b =
      referenceCoordinateProductMean ψ f_ref n ωref a b -
        referenceCoordinateMean ψ f_ref n ωref a *
          referenceCoordinateMean ψ f_ref n ωref b := by
  sorry

/-- Scalar weak law for one perspective coordinate mean.

This should be proved from the iid joint-law interface by a bounded second-
moment Chebyshev estimate.  Compactness supplies a uniform coordinate bound.
Keeping it separate lets a weaker agent debug the sample-mean probability
argument before handling products or covariance algebra.

Implementation recipe (execute in this order):
1. Derive a uniform bound `B` on `‖ψ f‖` from
   `exists_perspective_norm_bound_of_isCompact_range`; hence
   `|ψ f a| ≤ B` and the scalar variance is bounded by `4*B^2` (a loose bound is
   fine).
2. Use `hiid` to identify the stage coordinates
   `fun ω => ψ (f_ref n ω i) a` as iid with law induced by `Pf` and to obtain
   measurability.
3. Apply the existing finite-sample/second-moment mean theorem in
   `Acharyya2024` or `Acharyya2025.GrowingResponse` to the scalar variables.
4. Obtain a probability bound of order `C/(n*ε^2)` by Chebyshev; treat `n=0`
   separately and use the theorem only eventually.
5. Unfold `HighProbAtTop`; choose `N` so `C/(n*ε^2) < δ`, convert the complement
   estimate to the event lower bound, and simplify the population mean.
6. Search anchors: `integral_norm_sq_replicateMean_sub_mean_le_of_bound`,
   `Probability.meas_gt_le_ofReal_secondMoment_div_sq`, and the iid fields used
   in `Coverage.lean`.  Do not invoke a matrix concentration theorem.
-/
theorem highProb_referenceCoordinateMean_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (a : Fin d) {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref (fun n => {ωref |
      |referenceCoordinateMean ψ f_ref n ωref a -
        ∫ f, ψ f a ∂Pf| ≤ ε}) := by
  sorry

/-- Scalar weak law for one perspective-coordinate product mean.

Apply the same bounded Chebyshev argument as the coordinate-mean theorem to the
measurable bounded scalar map `f ↦ ψ f a * ψ f b`.  No covariance expansion
belongs in this proof.

Implementation recipe (execute in this order):
1. Reuse the perspective norm bound `B`; prove
   `|ψ f a * ψ f b| ≤ B^2` and hence a uniform second-moment bound for the scalar
   product map.
2. Prove the product map is measurable from `hψ` and coordinate evaluation.
3. Transport the iid law through the measurable product map using the same
   `IIDReferenceSampler` fields as in the coordinate-mean theorem.
4. Apply the same scalar sample-mean Chebyshev theorem with mean
   `∫ f, ψ f a * ψ f b ∂Pf`.
5. Convert the `O(1/n)` complement bound to `HighProbAtTop` exactly as in
   `highProb_referenceCoordinateMean_of_compact_iid`.
6. Factor any repeated scalar weak-law code into a local helper taking a bounded
   measurable scalar observable; do not mix covariance algebra into this proof.
-/
theorem highProb_referenceCoordinateProductMean_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (a b : Fin d) {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref (fun n => {ωref |
      |referenceCoordinateProductMean ψ f_ref n ωref a b -
        ∫ f, ψ f a * ψ f b ∂Pf| ≤ ε}) := by
  sorry

/-- A safe entrywise covariance tolerance.  The `d+1` denominator avoids a
special zero-dimensional branch while remaining small enough for the finite
entrywise-to-quadratic-form estimate. -/
noncomputable def covarianceEntryTolerance (d : Nat) (κ : Real) : Real :=
  κ / (4 * (d + 1))

/-- Measurable finite-dimensional event that empirical reference covariance is
entrywise close to population covariance. -/
def referenceCovarianceEvent
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (center : Vec d) (ε : Real) (n : Nat) : Set Ωref :=
  {ωref | EntrywiseClose
    (referenceEmpiricalCovariance ψ f_ref n ωref)
    (perspectiveCovarianceMatrix Pf ψ center) ε}

/-- Compactness of the perspective range gives a uniform norm envelope.

Suggested proof route: the norm is continuous, hence its image on the compact
range is compact and bounded.  Extract a real upper bound and enlarge it to a
nonnegative number.  Return a bound on every model rather than only on points in
the range so later theorem applications remain simple.

Implementation recipe (execute in this order):
1. Apply compactness of `Set.range ψ` to the continuous norm map; obtain that
   `norm '' Set.range ψ` is compact.
2. Use compactness to obtain boundedness, or use
   `hcompact.isBounded.subset_closedBall` to get a radius `R` and center.
3. Convert a ball bound around an arbitrary center into a bound from zero by the
   triangle inequality, and choose `B := max 0 (...)`.
4. For each `f`, use `ψ f ∈ Set.range ψ` to specialize the boundedness result.
5. Search anchors: `IsCompact.bddAbove`, `IsCompact.isBounded`,
   `Metric.isBounded_iff_subset_closedBall`, and `ContinuousOn.norm`.
6. Do not assume the model type itself is compact; only the perspective range is.
-/
theorem exists_perspective_norm_bound_of_isCompact_range
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖ψ f‖ ≤ B := by
  sorry

/-- One scalar empirical-covariance entry event is measurable.

This is the atomic measurability result required by
`HighProbAtTop.finset_all`.  Expand the sample-centered covariance entry into
finite sums and products of measurable coordinates.  Keep this separate from
the finite conjunction theorem: measurability of the conjunction alone does
not provide measurability of each event needed by the high-probability
intersection API.

Implementation recipe (execute in this order):
1. Prove each map `ωref ↦ ψ (f_ref n ωref i) a` measurable by
   `(hψ.comp (href n i)).eval a` or the corresponding coordinate-evaluation
   lemma.
2. From these maps, prove measurability of `referenceCoordinateMean` and
   `referenceCoordinateProductMean` using finite sums and scalar multiplication.
3. Rewrite the empirical covariance entry with
   `referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean`; deduce its
   measurability by subtraction and multiplication.
4. The population covariance entry is constant in `ωref`.
5. Apply measurability of subtraction, absolute value, and `measurableSet_le` to
   the constant `ε`.
6. Avoid unfolding the double finite sum directly after step 3; the algebraic
   lemma exists to keep this proof small.
-/
theorem measurableSet_referenceCovarianceEntryEvent
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (center : Vec d) (ε : Real) (n : Nat) (a b : Fin d) :
    MeasurableSet {ωref |
      |referenceEmpiricalCovariance ψ f_ref n ωref a b -
        perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε} := by
  sorry

/-- The empirical covariance event is measurable.

Suggested proof route: unfold `EntrywiseClose` and apply
`measurableSet_finset_all` twice over `Finset.univ`, using
`measurableSet_referenceCovarianceEntryEvent` for each scalar event.  Avoid
introducing operator norms here, because the finite entrywise event is exactly
what the later union-bound proof controls.

Implementation recipe (execute in this order):
1. Unfold `referenceCovarianceEvent` and `EntrywiseClose`.
2. Express the event as
   `{ω | ∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ, ω ∈ E a b}` where `E a b` is the
   scalar absolute-error event.
3. Apply `measurableSet_finset_all` first over `b`, then over `a`.
4. Discharge each scalar measurability goal with
   `measurableSet_referenceCovarianceEntryEvent`.
5. Finish the set equality by `ext ω; simp [EntrywiseClose]`.
-/
theorem measurableSet_referenceCovarianceEvent
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (center : Vec d) (ε : Real) (n : Nat) :
    MeasurableSet (referenceCovarianceEvent Pf ψ f_ref center ε n) := by
  sorry

/-- Scalar weak law for one empirical covariance entry.

For fixed coordinates `a,b`, combine
`highProb_referenceCoordinateMean_of_compact_iid` for both coordinates with
`highProb_referenceCoordinateProductMean_of_compact_iid`, then rewrite using
`referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean`.  Use
`hcenter` to identify the resulting population expression with
`perspectiveCovarianceMatrix`; without this mean-zero condition the statement
would be false for an arbitrary center.  The result remains pointwise in
`a,b`; the next theorem performs the fixed finite intersection.

Implementation recipe (execute in this order):
1. Choose a small scalar tolerance `δ > 0` so that errors of size `δ` in the
   product mean and the two coordinate means force covariance-entry error at
   most `ε`.  Use the compact perspective bound to bound the limiting means.
2. Obtain three high-probability events from
   `highProb_referenceCoordinateProductMean_of_compact_iid` and two applications
   of `highProb_referenceCoordinateMean_of_compact_iid`.
3. Intersect the three events using `HighProbAtTop.inter` twice; prove their
   measurability using the scalar measurable-map arguments from the preceding
   theorem.
4. On the intersection, rewrite the sample covariance using
   `referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean`.
5. Use `Hnondeg.center_is_mean`-style algebra supplied here as `hcenter` to show
   `∫ ψ_a ψ_b - (∫ψ_a)(∫ψ_b)` equals
   `perspectiveCovarianceMatrix Pf ψ center a b`.
6. Bound the difference of products with
   `|xy-x'y'| ≤ |x|*|y-y'| + |y'|*|x-x'|`, then close by the chosen `δ`.
7. Finally use event monotonicity to obtain the stated event.  Keep this theorem
   pointwise in `a,b`.
-/
theorem highProb_referenceCovarianceEntry_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (center : Vec d)
    (hcenter : ∀ j, ∫ f, (ψ f - center) j ∂Pf = 0)
    (a b : Fin d) {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref (fun n => {ωref |
      |referenceEmpiricalCovariance ψ f_ref n ωref a b -
        perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε}) := by
  sorry

/-- Finite intersection of the scalar covariance-entry events.

Use `HighProbAtTop.finset_all` twice or induction over
`Finset.univ ×ˢ Finset.univ`.  The theorem deliberately accepts scalar-event
measurability because that is what the finite-intersection API requires.  Keep
the event equality explicit: after unfolding `referenceCovarianceEvent` and
`EntrywiseClose`, it is exactly the conjunction of the scalar entry events.

Implementation recipe (execute in this order):
1. Apply `HighProbAtTop.finset_all` to `Finset.univ : Finset (Fin d)` for the
   outer coordinate `a`.
2. For each `a`, apply it again to `Finset.univ : Finset (Fin d)` for `b`, using
   `hentry a b` and `hentryMeas a b`.
3. The resulting event is a nested finite conjunction.  Prove it equals
   `referenceCovarianceEvent ... ε` by extensionality and
   `simp [referenceCovarianceEvent, EntrywiseClose]`.
4. Rewrite by that function/event equality and return the finite-intersection
   result.  Do not reprove any probability estimate.
-/
theorem highProb_referenceCovarianceEvent_of_entries
    {d : Nat}
    (Pf : Measure (Model Q X))
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (center : Vec d) {ε : Real}
    (hentry : ∀ a b : Fin d,
      HighProbAtTop μref hμref (fun n => {ωref |
        |referenceEmpiricalCovariance ψ f_ref n ωref a b -
          perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε}))
    (hentryMeas : ∀ a b : Fin d, ∀ n,
      MeasurableSet {ωref |
        |referenceEmpiricalCovariance ψ f_ref n ωref a b -
          perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε}) :
    HighProbAtTop μref hμref
      (referenceCovarianceEvent Pf ψ f_ref center ε) := by
  sorry

/-- Fixed-dimensional weak law for all covariance entries simultaneously.

This is the probability-heavy obligation in the spectral track.  A direct
proof is sufficient:

1. prove the empirical coordinate means converge to the population center;
2. prove the empirical coordinate products converge to their expectations;
3. expand the sample-centered covariance as second moment minus mean product;
4. combine the scalar limits and intersect over `Fin d × Fin d`.

Use `hcenter` when identifying the covariance limit.  There is no need for a
sharp matrix Bernstein inequality.  The purpose is to remove an unrealistic
global spectral hypothesis, not optimize constants.

Implementation recipe (execute in this order):
1. For each `a,b`, call
   `highProb_referenceCovarianceEntry_of_compact_iid` with the common tolerance
   `ε` and `hε`.
2. Prove each scalar event measurable with
   `measurableSet_referenceCovarianceEntryEvent`, using `hiid.measurable` for the
   reference maps.
3. Pass these two families to
   `highProb_referenceCovarianceEvent_of_entries`.
4. This theorem should be a short composition.  If it grows beyond a few dozen
   lines, missing details belong in the scalar-entry theorem.
-/
theorem highProb_referenceCovarianceEvent_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (center : Vec d)
    (hcenter : ∀ j, ∫ f, (ψ f - center) j ∂Pf = 0)
    {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref
      (referenceCovarianceEvent Pf ψ f_ref center ε) := by
  sorry

/-- Entrywise covariance closeness preserves a uniform quadratic-form floor.

Suggested proof route:

* expand `xᵀ(A-B)x` as a double finite sum;
* bound it by `d * ε * ‖x‖₁²`, then use the finite-dimensional
  `ℓ¹ ≤ √d ℓ²` estimate, or use the repository's entrywise-to-operator bridge;
* the definition `covarianceEntryTolerance` leaves enough slack to retain at
  least half of the population floor.

Keep this lemma independent of random sampling.

Implementation recipe (execute in this order):
1. Split the target quadratic form as population quadratic form plus the error
   `xᵀ(A-C)x`, with `C := perspectiveCovarianceMatrix ...`.
2. Apply `Hnondeg.quadratic_floor` to the population part; first prove the
   integral quadratic form equals `∑ a,∑ b, x a * C a b * x b` by expanding the
   finite inner-product square and interchanging finite sums with the integral.
3. Bound the absolute error by
   `ε * (∑ a, |x a|)^2` using `hclose a b` and finite sum triangle inequalities.
4. Use Cauchy--Schwarz to show
   `(∑ a, |x a|)^2 ≤ d * ‖x‖^2`; it is acceptable to use the looser
   `(d+1) * ‖x‖^2` matching `covarianceEntryTolerance`.
5. Substitute `ε = κ/(4*(d+1))` and prove the error is at most
   `(κ/2) * ‖x‖^2`; handle `d=0` by simp.
6. Combine lower bounds with `linarith`/`nlinarith`.
7. Search for an existing entrywise-to-operator or Frobenius bound first; if it
   yields the same half-floor, use it instead of rebuilding step 3.
-/
theorem empiricalCovariance_quadratic_floor_of_entrywise
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (A : DisMat d)
    (hclose : EntrywiseClose A
      (perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ))
      (covarianceEntryTolerance d κ))
    (x : Vec d) :
    (κ / 2) * ‖x‖ ^ 2 ≤
      ∑ a, ∑ b, x a * A a b * x b := by
  sorry

/-- Convert the entrywise covariance event into the quadratic-form
floor needed by the reference-scatter theorem.

Unfold `referenceEmpiricalCovariance`, expand the quadratic form, and exchange
the finite sums.  The resulting expression is the average of squared inner
products with the sample-centered reference configuration.  Apply
`empiricalCovariance_quadratic_floor_of_entrywise` to the event membership.

Implementation recipe (execute in this order):
1. Unfold membership in `referenceCovarianceEvent` to obtain the `EntrywiseClose`
   premise needed by `empiricalCovariance_quadratic_floor_of_entrywise`.
2. Apply that theorem with
   `A := referenceEmpiricalCovariance ψ f_ref n ωref` and the given `x`.
3. Unfold `referenceEmpiricalCovariance` in the resulting quadratic form.
4. Exchange the finite sums over `a,b,i`; for each `i`, recognize
   `∑ a, x a * centerConfig ... i a` as the real inner product
   `⟪x, centerConfig ... i⟫_ℝ`.
5. Rewrite the product of the two identical sums as the square and normalize the
   outer `(n : Real)⁻¹`.
6. Use `ring` after the finite-sum rearrangement.  No probability argument is
   needed once `hω` is supplied.
-/
theorem reference_centered_quadratic_floor_of_event
    {d n : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (ωref : Ωref)
    (hω : ωref ∈ referenceCovarianceEvent Pf ψ f_ref (perspectiveMean Pf ψ)
      (covarianceEntryTolerance d κ) n)
    (x : Vec d) :
    (κ / 2) * ‖x‖ ^ 2 ≤
      (n : Real)⁻¹ * ∑ i : Fin n,
        ((∑ a : Fin d, x a * centerConfig
          (referencePerspectiveConfig ψ f_ref n ωref) i a)) ^ 2 := by
  sorry

/-- Usable reference-scatter spectral floor.

The preceding conceptual step is stated directly on a configuration here to
avoid forcing later agents through the dummy covariance expression above.  The
proof should identify the reference scatter as `n` times an empirical
covariance and then use the shared nonzero-spectrum result.

Implementation recipe (execute in this order):
1. Define the linear map `T : Vec d → EuclideanSpace Real (Fin n)` by
   `T x i = ⟪x, zref i⟫_ℝ`; the hypothesis says
   `n*(κ/2)*‖x‖² ≤ ‖T x‖²` after multiplying by `n`.
2. Identify `T†T` with the feature-space scatter matrix and its nonzero spectrum
   with the centered configuration Gram matrix `configGram zref` using the
   repository's rectangular Gram/singular-value bridge.
3. Convert the quadratic floor into a lower bound on all `d` eigenvalues of
   `T†T` via the min--max/Courant--Fischer theorem.
4. Transfer that lower bound to the first `d` sorted eigenvalues of `TT†`, which
   is `configGram zref`; use `hi : i < d` and `hn` to justify index ranges.
5. If the exact bridge already exists, search for
   `rectangular`, `nonzero_spectrum`, `gram`, `sortedEigenvalues`, and
   `quadratic_floor` in `ForMathlib` and `Acharyya2025` before defining `T`.
6. Do not prove the claim by choosing an eigenbasis manually; isolate any missing
   rectangular-spectrum lemma as a reusable helper.
-/
theorem sortedEigenvalues_reference_centeredGram_lower
    {d n : Nat} (hn : 0 < n)
    (zref : Config n d) {κ : Real}
    (hquad : ∀ x : Vec d,
      (κ / 2) * ‖x‖ ^ 2 ≤
        (n : Real)⁻¹ * ∑ i, ((∑ a : Fin d, x a * zref i a)) ^ 2)
    (i : Fin n) (hi : (i : Nat) < d) :
    κ / 2 ≤ sortedEigenvalues
      (configGramPosSemidef zref).isHermitian i := by
  sorry

/-- Adding the target and recentering the enlarged cloud cannot decrease the
reference scatter in any perspective direction.

A clean proof uses the online variance identity: total centered scatter after
adding one point equals the old scatter plus a nonnegative rank-one term.  Prove
the quadratic-form inequality first, then transfer it to sorted eigenvalues by
Courant--Fischer.  The premise `d ≤ n` is essential: without it the augmented
cloud can introduce a new index below `d` for which the reference cloud supplied
no lower bound.

Implementation recipe (execute in this order):
1. Prove the online-scatter identity for every `x : Vec d`:
   the squared projection sum of the centered augmented cloud equals the old
   centered reference sum plus
   `(n/(n+1)) * ⟪x, target - referenceCentroid⟫²`.
2. Deduce the feature-space scatter quadratic form of the augmented cloud
   dominates that of the reference cloud.
3. Convert `href` into a rank-`d` lower bound on the reference scatter (or use
   the same rectangular nonzero-spectrum bridge as the preceding theorem).
4. Apply eigenvalue monotonicity/Courant--Fischer to transfer the lower bound to
   the augmented scatter.
5. Transfer from feature scatter to the augmented centered Gram matrix's first
   `d` nonzero eigenvalues.
6. Use `hdn : d ≤ n` and `hi : i < d` to keep every index within both spectra.
7. Keep the rank-one update term explicit and nonnegative; do not use a false
   claim that arbitrary matrix principal extension preserves sorted indices.
-/
theorem augmented_centeredGram_floor_of_reference_floor
    {d n : Nat} (hn : 0 < n) (hdn : d ≤ n)
    (ψref : Fin n → Vec d) (target : Vec d) {α : Real}
    (href : ∀ i : Fin n, (i : Nat) < d →
      α ≤ sortedEigenvalues
        (configGramPosSemidef (centerConfig ψref)).isHermitian i)
    (i : Fin (n + 1)) (hi : (i : Nat) < d) :
    α ≤ sortedEigenvalues
      (configGramPosSemidef (centerConfig (Fin.lastCases target ψref))).isHermitian i := by
  sorry

/-- A uniform perspective norm bound gives a deterministic linear-in-`n`
ceiling for every eigenvalue of the augmented centered Gram matrix.

Suggested proof route: top eigenvalue is at most the trace for a PSD matrix;
the trace is the sum of squared centered norms; each centered point has norm at
most `2B`.  Loose constants are preferred over adding hypotheses.

Implementation recipe (execute in this order):
1. Use PSD to bound every sorted eigenvalue by the largest eigenvalue, and bound
   the largest eigenvalue by the trace.  Search for
   `sortedEigenvalues_le_trace` or combine `eigenvalue_le_trace` with PSD.
2. Rewrite the trace of `configGram (centerConfig points)` as
   `∑ i, ‖centerConfig points i‖²` by expanding diagonal entries.
3. Prove the centroid has norm at most `B` because it is an average of points
   bounded by `B` (the batch is nonempty).
4. Hence each centered point has norm at most `2*B`; square to obtain
   `≤ 4*B²`.
5. Sum over `n+1` points and simplify the constant sum to the stated ceiling.
6. If a direct trace theorem is unavailable, use the Rayleigh quotient bound
   `λmax ≤ frobNorm` and prove the same loose ceiling.  Do not add a separate
   centroid bound hypothesis.
-/
theorem sortedEigenvalues_augmented_centeredGram_upper
    {d n : Nat}
    (points : Config (n + 1) d) {B : Real}
    (hBnonneg : 0 ≤ B)
    (hB : ∀ i, ‖points i‖ ≤ B)
    (i : Fin (n + 1)) :
    sortedEigenvalues
      (configGramPosSemidef (centerConfig points)).isHermitian i ≤
      4 * ((n + 1 : Nat) : Real) * B ^ 2 := by
  sorry

/-- Assemble the covariance weak law and deterministic Gram lemmas into the
high-probability spectral certificate consumed by the new Quench capstone.

Once complete, this theorem dispatches the old global `hfloor`, `hceiling`, and
caller-chosen `ceiling` inputs.  Define the certificate event with an explicit
deterministic gate `d ≤ n`; that gate is eventually true and is needed by
`augmented_centeredGram_floor_of_reference_floor`.  The only lower-spectrum
assumption remaining in the final theorem is `PerspectiveNondegeneracy`.

Implementation recipe (execute in this order):
1. Obtain `B ≥ 0` and `hB : ∀ f, ‖ψ f‖ ≤ B` from
   `exists_perspective_norm_bound_of_isCompact_range`.
2. Define
   `event n := referenceCovarianceEvent Pf ψ f_ref (perspectiveMean Pf ψ)
   (covarianceEntryTolerance d κ) n ∩ {ω | d ≤ n}`.
3. Prove measurability using
   `measurableSet_referenceCovarianceEvent`, `hiid.measurable`, and the fact that
   the dimension gate is either `univ` or `∅`.
4. Prove high probability by intersecting
   `highProb_referenceCovarianceEvent_of_compact_iid` (with
   `Hnondeg.center_is_mean`) and the deterministic eventual event `d ≤ n`.
5. For the `floor` field, use
   `reference_centered_quadratic_floor_of_event`, then
   `sortedEigenvalues_reference_centeredGram_lower`, and finally
   `augmented_centeredGram_floor_of_reference_floor` for the target-augmented
   configuration.  Rewrite its Gram matrix to the population CMDS matrix with
   `centeredAugmentedPerspectiveConfig_gram_eq` and `hrealize`.
6. For `ceiling_bound`, apply
   `sortedEigenvalues_augmented_centeredGram_upper` to
   `augmentedPerspectiveConfig ψ f_ref n ωref f`; obtain point bounds from `hB`.
7. Package the structure with `α := κ/2` and
   `ceiling n := 4*(n+1)*B²`.
8. Use named fields throughout.  This constructor should not contain new
   covariance or eigenvalue algebra; repair the preceding lemmas if a field is
   hard to fill.
-/
theorem exists_growingSpectralSubevents_of_compact_iid_nondegenerate
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    {κ : Real} (Hnondeg : PerspectiveNondegeneracy Pf ψ κ) :
    ∃ B : Real, 0 ≤ B ∧ (∀ f, ‖ψ f‖ ≤ B) ∧
      Nonempty (GrowingSpectralSubevents μref hμref
        (fun n ωref f => responseDist (μbar n ωref f))
        (centeredAugmentedPerspectiveConfig ψ f_ref)
        (centeredAugmentedPerspectiveConfig_gram_eq
          ψ f_ref μbar hrealize)
        (κ / 2)
        (fun n => 4 * ((n + 1 : Nat) : Real) * B ^ 2)) := by
  sorry

end DkpsQuench.Perfect
