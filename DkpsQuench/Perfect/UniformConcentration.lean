/-
Uniform response concentration over infinite model classes.

The finite-model theorem uses a union bound over every target.  For an infinite
class, Perfect Quench needs a shrinking finite net plus pathwise/population
regularity.  This module keeps the empirical-process argument elementary:
finite-net concentration followed by deterministic Lipschitz extension.
-/

import DkpsQuench.Perfect.Compactness

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
open Acharyya2025.GrowingResponse
open DkpsQuench.GrowingResponseBridge

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- Uniform model-level response-mean event before references and targets are
assembled into an augmented batch. -/
def modelUniformResponseEvent
    {m p : Nat}
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (η : Nat → Real) (n : Nat) : Set Ωresp :=
  {ω | ∀ f, ‖Xbar n ω f - μmodel f‖ ≤ η n}

/-- Response-mean event checked only on one stage's finite perspective net. -/
def modelNetResponseEventFor
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (τ : Nat → Real) (n : Nat) : Set Ωresp :=
  {ω | ∀ f ∈ net.centers n, ‖Xbar n ω f - μmodel f‖ ≤ τ n}

/-- Finite-net control extends to the full model class under sample and
population Lipschitz regularity.

Suggested proof route: choose a net center `g` for `f`, insert and subtract
`Xbar g` and `μmodel g`, apply the triangle inequality, then the two Lipschitz
bounds and the net-center error.  The stated scalar side condition is exactly
the resulting bound.

Implementation recipe (execute in this order):
1. Introduce `ω hω f`.  Obtain a center `g ∈ net.centers n` with
   `‖ψ f - ψ g‖ ≤ net.radius n` from `net.covers n f`.
2. Insert and subtract `Xbar n ω g` and `μmodel g`; use the three-term triangle
   inequality to bound the target error by sample transport, net-center error,
   and population transport.
3. Apply `Hreg.sample_lipschitz`, `hω g hg`, and
   `Hreg.population_lipschitz` respectively.
4. Use nonnegativity of the Lipschitz constants and the cover-radius inequality
   to replace both perspective distances by `net.radius n`.
5. Normalize the scalar expression to
   `τ n + (Lsample n + Lpopulation n) * net.radius n` and finish with
   `hbudget n`.
6. If norm symmetry is needed for the population term, rewrite
   `‖ψ g - ψ f‖ = ‖ψ f - ψ g‖` using `norm_neg`/`dist_comm`.
-/
theorem modelNetResponseEventFor_subset_uniform
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ Xbar μmodel
      Lsample Lpopulation)
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n)
    (n : Nat) :
    modelNetResponseEventFor ψ Xbar μmodel net τ n ⊆
      modelUniformResponseEvent Xbar μmodel η n := by
  sorry

/-- Measurability of the finite-net response event.

Only finite intersections are involved.  Prove measurability model-by-model
from `hXbar`; the population response is constant on the response sample space.

Implementation recipe (execute in this order):
1. Unfold `modelNetResponseEventFor` and express membership as
   `∀ f ∈ net.centers n, ...`.
2. For fixed `f`, prove measurability of
   `ω ↦ ‖Xbar n ω f - μmodel f‖` from `hXbar n f`, constant measurability,
   subtraction, and norm continuity.
3. Apply `measurableSet_le` to obtain the scalar event.
4. Apply `measurableSet_finset_all (net.centers n)` with the membership proof.
5. Do not quantify over the full model type in the measurable event; only the
   finite center set belongs here.
-/
theorem measurableSet_modelNetResponseEventFor
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (τ : Nat → Real)
    (hXbar : ∀ n f, Measurable fun ω => Xbar n ω f)
    (n : Nat) :
    MeasurableSet (modelNetResponseEventFor ψ Xbar μmodel net τ n) := by
  sorry

/-- Finite-net response concentration from uniform modelwise second moments.

The proof is a Chebyshev bound for each center followed by a finite union bound.
The only growth quantity is the actual cardinality of the chosen stage net.
This theorem intentionally does not hide that entropy term behind a vague
uniform-concentration premise.

Implementation recipe (execute in this order):
1. For each stage, show the complement of the net event is contained in the
   finite union of bad-center events
   `{ω | τ n < ‖Xbar n ω f - μmodel f‖}`.
2. Use the repository Chebyshev lemma with `hint n f`, `hσ2 n f`, and `hτ n` to
   bound each bad-center probability by `ENNReal.ofReal (σ2 n / τ n^2)`.
3. Sum over `net.centers n` with `measure_iUnion_finset_le`; simplify the sum of
   a constant to the center cardinality times that bound.
4. Convert the real ratio `hratio` to ENNReal convergence or use the same
   complement-probability criterion as `GrowingResponse`.
5. Prove event measurability with `measurableSet_modelNetResponseEventFor`; derive
   `hXbar` from `Integrable.measurable` applied to `hint` if no separate
   measurability premise is available.
6. Keep the actual cardinality in the estimate; polynomial replacement belongs
   in `RateSchedule`, not here.
-/
theorem highProb_modelNetResponseEventFor_of_secondMoment
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (σ2 τ : Nat → Real)
    (hint : ∀ n f,
      Integrable (fun ω => ‖Xbar n ω f - μmodel f‖ ^ 2) (μresp n))
    (hσ2 : ∀ n f,
      ∫ ω, ‖Xbar n ω f - μmodel f‖ ^ 2 ∂(μresp n) ≤ σ2 n)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * σ2 n / (τ n) ^ 2) atTop (𝓝 0)) :
    HighProbAtTop μresp hμresp
      (modelNetResponseEventFor ψ Xbar μmodel net τ) := by
  sorry

/-- Infinite-class uniform response concentration by finite nets and
regularity.

Once this is complete, the arbitrary-model growing response bridge no longer
needs uniform concentration as an external input.  Applications supply a
shrinking net, pointwise second moments, and pathwise/population regularity.

Implementation recipe (execute in this order):
1. Obtain high probability of the finite-net event from
   `highProb_modelNetResponseEventFor_of_secondMoment`.
2. Use `modelNetResponseEventFor_subset_uniform ... hbudget` stagewise.
3. Apply the monotonicity lemma for `HighProbAtTop` under event inclusion; if no
   named lemma exists, unfold `HighProbAtTop` and compose the measure inequality
   `measure_mono` with the subset.
4. The uniform event need not be measurable for this implication; only the net
   event used to witness high probability must be measurable.
5. Do not repeat Chebyshev or triangle-inequality calculations in this theorem.
-/
theorem highProb_modelUniformResponseEvent_of_net_regular
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation σ2 τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ Xbar μmodel
      Lsample Lpopulation)
    (hint : ∀ n f,
      Integrable (fun ω => ‖Xbar n ω f - μmodel f‖ ^ 2) (μresp n))
    (hσ2 : ∀ n f,
      ∫ ω, ‖Xbar n ω f - μmodel f‖ ^ 2 ∂(μresp n) ≤ σ2 n)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * σ2 n / (τ n) ^ 2) atTop (𝓝 0))
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n) :
    HighProbAtTop μresp hμresp
      (modelUniformResponseEvent Xbar μmodel η) := by
  sorry

/-- A model-uniform response event implies every target-augmented response
event, including randomly selected references.

Implementation recipe (execute in this order):
1. Introduce `ω hω f i` and unfold the two event definitions.
2. Specialize `hω` to the single model
   `augmentedModelAt f_ref n ω.1 f i`.
3. Simplify the sample term to the lambda-defined augmented sample mean and the
   population term to `augmentedRawPopulationMean`.
4. Close with `simpa [augmentedRawPopulationMean]`; no `Fin.lastCases` split is
   needed because the uniform model event already covers every model.
-/
theorem modelUniformResponseEvent_subset_augmented
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (η : Nat → Real) (n : Nat) :
    {ω : Ωref × Ωresp | ω.2 ∈ modelUniformResponseEvent Xbar μmodel η n} ⊆
      augmentedUniformResponseMeanEvent
        (fun n ω f i => Xbar n ω.2
          (augmentedModelAt f_ref n ω.1 f i))
        (augmentedRawPopulationMean f_ref μmodel) η n := by
  sorry

/-- Lift a high-probability response-only event to the independent joint sample
space.

Implementation recipe (execute in this order):
1. Unfold `HighProbAtTop`; fix `δ` and obtain `N` from `hE δ hδ`.
2. For `n > N`, identify the lifted event with the rectangle
   `Set.univ ×ˢ E n` by extensionality.
3. Install `hμref n` and `hμresp n`; apply the product-measure rectangle formula
   using `measurableSet_univ` and `hEmeas n`.
4. Simplify `(μref n) univ = 1`, so the joint probability equals
   `(μresp n) (E n)`.
5. Finish with the lower bound supplied by `hE`.
6. If the rectangle formula requires sigma-finiteness, obtain it from the local
   probability instances rather than adding assumptions.
-/
theorem highProb_prod_mk_right
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (E : Nat → Set Ωresp)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hE : HighProbAtTop μresp hμresp E) :
    HighProbAtTop (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      (fun n => {ω : Ωref × Ωresp | ω.2 ∈ E n}) := by
  sorry

/-- Infinite-model augmented response concentration from raw iid replicates,
shrinking perspective nets, and response regularity.

This is the final response-statistics seam needed by the infinite-model Perfect
Quench capstone.  It should compose:

1. the raw replicate second-moment theorem;
2. finite-net uniform concentration;
3. deterministic net extension;
4. product-event lifting;
5. the augmented-event inclusion.

No finite model-class assumption remains.

Implementation recipe (execute in this order):
1. Apply `integral_norm_sq_modelReplicateMean_sub_mean_le` for each model to get
   second-moment bound `variance n / replicates n`; obtain integrability from the
   corresponding raw-response theorem or `Hraw.memLp_two` and finite sums.
2. Invoke `highProb_modelUniformResponseEvent_of_net_regular` with
   `Xbar := modelReplicateMean replicates Y`, `σ2 := fun n => variance n /
   replicates n`, and the supplied net/regularity/rate data.
3. Prove measurability of each finite-net event from
   `measurableSet_modelNetResponseEventFor`, using finite sums of
   `Hraw.measurable` for `hXbar`.
4. Lift the resulting response-only high-probability event to the joint space via
   `highProb_prod_mk_right`.
5. Use `modelUniformResponseEvent_subset_augmented` and `HighProbAtTop`
   monotonicity to reach the target augmented event.
6. Keep reference measurability out of this proof; the event depends on the
   reference sample only after the deterministic inclusion.
-/
theorem highProb_augmentedRawResponseMean_infinite
    {d m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ
      (modelReplicateMean replicates Y) μmodel Lsample Lpopulation)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * (variance n / replicates n) /
        (τ n) ^ 2) atTop (𝓝 0))
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n) :
    HighProbAtTop (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedUniformResponseMeanEvent
        (augmentedRawSampleMean f_ref replicates Y)
        (augmentedRawPopulationMean f_ref μmodel) η) := by
  sorry

/-- Measurable finite-net subevents for infinite-model augmented response
concentration.

The event stored in this certificate is the product lift of the finite-net
response event, not the universal target event.  Its subset field performs the
regularity extension and augmented-batch reduction.  This design is essential:
it avoids asking Lean to prove measurability of an uncountable intersection.

Implementation recipe (execute in this order):
1. Define `event n` to be the product lift of
   `modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ n`.
2. Prove `measurable` by `MeasurableSet.preimage measurable_snd` together with
   `measurableSet_modelNetResponseEventFor`; construct the sample-mean
   measurability from finite sums of `Hraw.measurable`.
3. Prove `highProb` by first applying
   `highProb_modelNetResponseEventFor_of_secondMoment` with
   `σ2 n = variance n / replicates n`, then `highProb_prod_mk_right`.
4. For `subset`, first apply
   `modelNetResponseEventFor_subset_uniform ... hbudget`, then
   `modelUniformResponseEvent_subset_augmented`.
5. Do not use the universal model event as `event`; its measurability is exactly
   what this certificate is designed to avoid.
-/
noncomputable def augmentedRawResponseMeanSubevents_infinite
    {d m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ
      (modelReplicateMean replicates Y) μmodel Lsample Lpopulation)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * (variance n / replicates n) /
        (τ n) ^ 2) atTop (𝓝 0))
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n) :
    AugmentedResponseMeanSubevents
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η := by
  sorry

end DkpsQuench.Perfect
