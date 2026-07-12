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
of the three quantities displayed here. -/
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
argument before handling products or covariance algebra. -/
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
belongs in this proof. -/
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
the range so later theorem applications remain simple. -/
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
intersection API. -/
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
what the later union-bound proof controls. -/
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
`a,b`; the next theorem performs the fixed finite intersection. -/
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
`EntrywiseClose`, it is exactly the conjunction of the scalar entry events. -/
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
global spectral hypothesis, not optimize constants. -/
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

Keep this lemma independent of random sampling. -/
theorem empiricalCovariance_quadratic_floor_of_entrywise
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (A : DisMat d)
    (hclose : EntrywiseClose A
      (perspectiveCovarianceMatrix Pf ψ Hnondeg.center)
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
`empiricalCovariance_quadratic_floor_of_entrywise` to the event membership. -/
theorem reference_centered_quadratic_floor_of_event
    {d n : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (ωref : Ωref)
    (hω : ωref ∈ referenceCovarianceEvent Pf ψ f_ref Hnondeg.center
      (covarianceEntryTolerance d κ) n)
    (x : Vec d) :
    (κ / 2) * ‖x‖ ^ 2 ≤
      (n : Real)⁻¹ * ∑ i : Fin n,
        (⟪x, centerConfig
          (referencePerspectiveConfig ψ f_ref n ωref) i⟫_ℝ) ^ 2 := by
  sorry

/-- Usable reference-scatter spectral floor.

The preceding conceptual step is stated directly on a configuration here to
avoid forcing later agents through the dummy covariance expression above.  The
proof should identify the reference scatter as `n` times an empirical
covariance and then use the shared nonzero-spectrum result. -/
theorem sortedEigenvalues_reference_centeredGram_lower
    {d n : Nat} (hn : 0 < n)
    (zref : Config n d) {κ : Real}
    (hquad : ∀ x : Vec d,
      (κ / 2) * ‖x‖ ^ 2 ≤
        (n : Real)⁻¹ * ∑ i, (⟪x, zref i⟫_ℝ) ^ 2)
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
no lower bound. -/
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
most `2B`.  Loose constants are preferred over adding hypotheses. -/
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
assumption remaining in the final theorem is `PerspectiveNondegeneracy`. -/
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
      GrowingSpectralSubevents μref hμref
        (fun n ωref f => responseDist (μbar n ωref f))
        (centeredAugmentedPerspectiveConfig ψ f_ref)
        (centeredAugmentedPerspectiveConfig_gram_eq
          ψ f_ref μbar hrealize)
        (κ / 2)
        (fun n => 4 * ((n + 1 : Nat) : Real) * B ^ 2) := by
  sorry

end DkpsQuench.Perfect
