/-
Final Perfect Quench theorem scaffold.

There are two complete routes:

* finite model classes: raw iid replicates plus a direct target union bound;
* compact infinite model classes: raw iid replicates plus shrinking finite nets
  and response regularity.

Both routes derive population geometry, random spectral regularity, conservative
rate conditions, reference coverage, and the literal target-augmented CMDS
nearest-neighbor estimator.  The final section lifts fixed-subset results to all
proper query subsets.
-/

import DkpsQuench.Perfect.SpectralCapstone

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
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
open DkpsQuench.GrowingAcharyyaBridge

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- Raw data needed to run the conservative finite-model Perfect Quench
pipeline for one query subset. -/
structure FinitePerfectSubsetData (d m p : Nat) where
  perspective : Model Q X → Vec d
  rawResponse : ∀ n, Model Q X → Fin (safeFiniteReplicates n) →
    Ωresp → Acharyya2024.Mat m p
  populationMean : Model Q X → Acharyya2024.Mat m p
  varianceBound : Real
  covarianceFloor : Real
  lipschitzConstant : Real

/-- Honest paper-facing assumptions for one finite-model query subset.

Fields deliberately omitted because the scaffold derives them:

* no sample response means or second-moment events;
* no population configuration, Gram identity, PSD, or rank proof;
* no global eigenvalue floor or ceiling over every sample outcome;
* no explicit CMDS entry-rate or `GrowingConfigControl` certificate;
* no compactness proof for the finite model class;
* no population response-norm envelope, which follows from finiteness.
-/
structure FinitePerfectSubsetAssumptions
    [Fintype (Model Q X)]
    {d m p : Nat}
    (Pf : Measure (Model Q X))
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : FinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p) : Prop where
  perspective_measurable : Measurable D.perspective
  full_support : PerspectiveFullSupport Pf D.perspective
  raw : RawIIDResponseModel μresp safeFiniteReplicates D.rawResponse
    D.populationMean (fun _ => D.varianceBound)
  response_realization : ModelResponseRealization D.perspective D.populationMean
  nondegenerate : PerspectiveNondegeneracy Pf D.perspective D.covarianceFloor
  lipschitz_pos : 0 < D.lipschitzConstant
  score_lipschitz : ∀ f g,
    |score f Qstar - score g Qstar| ≤
      D.lipschitzConstant * ‖D.perspective f - D.perspective g‖
  baseline_pos : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)

/-- Literal finite-model Perfect Quench estimator for one query subset. -/
noncomputable def finitePerfectQuenchEstimator
    {d m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : FinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) : Real :=
  yNNTieAverage_augmentedCMDS (d := d)
    (augmentedSampleResponseDist
      (augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse))
    (fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse n ω f))
    (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
    score Qstar n ω f

/-- Fixed-subset finite-model Perfect Quench theorem.

Proof assembly guide:

1. derive compactness and a population response-norm envelope from
   `Fintype`;
2. lift the iid reference sampler to the product space;
3. construct the finite raw-response subevent certificate using
   `safeFinite_concentration_ratio_zero`;
4. derive target-augmented population realization from
   `response_realization`;
5. construct centered population geometry;
6. obtain the high-probability spectral certificate from iid covariance
   concentration and `nondegenerate`;
7. build `GrowingConfigControl` using `safe_growingConfigControl`;
8. invoke
   `highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents`.

After those scaffold lemmas are completed, this theorem's visible assumptions
are the intended finite-model Perfect Quench interface. -/
theorem perfectQuench_finite_fixedSubset
    [Fintype (Model Q X)]
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : FinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (H : FinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (finitePerfectQuenchEstimator f_ref score Qstar D)
      (fun _ _ f => yQ score Qsub f) := by
  sorry

/-- Raw data needed for one compact infinite-model Perfect Quench theorem. -/
structure InfinitePerfectSubsetData (d m p : Nat) where
  perspective : Model Q X → Vec d
  rawResponse : ∀ n, Model Q X →
    Fin (safeEntropyReplicates (5 * d) n) →
    Ωresp → Acharyya2024.Mat m p
  populationMean : Model Q X → Acharyya2024.Mat m p
  varianceBound : Real
  covarianceFloor : Real
  lipschitzConstant : Real
  rawResponseLipschitzConstant : Real

/-- Paper-facing assumptions for one compact infinite-model query subset.

The additional assumption relative to the finite theorem is pathwise
Lipschitz regularity of the raw response embedding over a compact perspective
range.  The scaffold derives the replicate-mean and population-mean regularity,
finite nets, polynomial covering bound, entropy exponent, shrinking radius,
and population response envelope internally. -/
structure InfinitePerfectSubsetAssumptions
    {d m p : Nat}
    (Pf : Measure (Model Q X))
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : InfinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p) : Prop where
  perspective_measurable : Measurable D.perspective
  compact_range : IsCompact (Set.range D.perspective)
  full_support : PerspectiveFullSupport Pf D.perspective
  raw : RawIIDResponseModel μresp
    (safeEntropyReplicates (5 * d)) D.rawResponse
    D.populationMean (fun _ => D.varianceBound)
  raw_lipschitz : RawResponseLipschitz D.perspective
    (safeEntropyReplicates (5 * d)) D.rawResponse
    D.rawResponseLipschitzConstant
  response_realization : ModelResponseRealization D.perspective D.populationMean
  nondegenerate : PerspectiveNondegeneracy Pf D.perspective D.covarianceFloor
  lipschitz_pos : 0 < D.lipschitzConstant
  score_lipschitz : ∀ f g,
    |score f Qstar - score g Qstar| ≤
      D.lipschitzConstant * ‖D.perspective f - D.perspective g‖
  baseline_pos : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)

/-- Literal compact infinite-model Perfect Quench estimator. -/
noncomputable def infinitePerfectQuenchEstimator
    {d m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : InfinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) : Real :=
  yNNTieAverage_augmentedCMDS (d := d)
    (augmentedSampleResponseDist
      (augmentedRawSampleMean f_ref
        (safeEntropyReplicates (5 * d)) D.rawResponse))
    (fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (augmentedRawSampleMean f_ref
          (safeEntropyReplicates (5 * d)) D.rawResponse n ω f))
    (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
    score Qstar n ω f

/-- Fixed-subset compact infinite-model Perfect Quench theorem.

This theorem has the same proof skeleton as the finite result.  Before the
response subevent step:

1. derive sample and population Lipschitz regularity from `raw_lipschitz`;
2. construct the canonical polynomial finite net with
   `exists_safeGrowingPerspectiveNet`;
3. derive a population response-norm envelope from compactness and population
   Lipschitzness;
4. invoke `augmentedRawResponseMeanSubevents_infinite`, discharging its ratio
   with `safeEntropy_concentration_ratio_zero` and its extension budget with
   `safe_net_extension_budget`.

Completing it removes the last abstract uniform response-concentration premise
and every explicit net/envelope certificate from the arbitrary-model growing
Quench path. -/
theorem perfectQuench_infinite_fixedSubset
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : InfinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (H : InfinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (infinitePerfectQuenchEstimator f_ref score Qstar D)
      (fun _ _ f => yQ score Qsub f) := by
  sorry

/-- All-proper-subsets finite-model Perfect Quench.

Each valid subset receives its own dimensions, data, and assumptions, while the
reference law, response-noise law, and full score are shared.  Once
`perfectQuench_finite_fixedSubset` is complete, this proof is only the
quantifier lift encoded by `HighProbQueryEfficient`. -/
theorem perfectQuench_finite_allQueries
    [Fintype (Model Q X)]
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : ∀ Qsub, FinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card,
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card,
      FinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => finitePerfectQuenchEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  sorry

/-- All-proper-subsets compact infinite-model Perfect Quench.

As in the finite theorem, each subset may use its own embedding and response
dimensions, perspective, raw response embedding, and raw-response Lipschitz
constant.  The finite net, entropy exponent, regularity certificates, and norm
envelope are derived within the fixed-subset theorem.  The proof should apply
`perfectQuench_infinite_fixedSubset` subset-by-subset and unfold the all-budget
predicate. -/
theorem perfectQuench_infinite_allQueries
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : ∀ Qsub, InfinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card,
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card,
      InfinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => infinitePerfectQuenchEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  sorry

end DkpsQuench.Perfect
