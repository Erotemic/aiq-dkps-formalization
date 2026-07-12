/-
Raw iid response observations for Perfect Quench.

Reference sampling and response sampling are placed on separate probability
spaces and then combined with a product measure.  This is not cosmetic: if a
random reference index and its cached response array lived on the same opaque
sample space, selecting the response array by the random model could introduce
selection bias.  The product construction makes the required independence
structural.
-/

import DkpsQuench.Perfect.SpectralRegularity

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

/-- Stagewise product measure carrying independent reference and response
randomness. -/
noncomputable def jointStageMeasure
    (μref : Nat → Measure Ωref) (μresp : Nat → Measure Ωresp) :
    Nat → Measure (Ωref × Ωresp) :=
  fun n => (μref n).prod (μresp n)

/-- Lift a reference sampler to the joint space by ignoring response
randomness. -/
def liftedReferenceSampler
    (f_ref : ∀ n, Ωref → Fin n → Model Q X) :
    ∀ n, Ωref × Ωresp → Fin n → Model Q X :=
  fun n ω i => f_ref n ω.1 i

/-- Per-model average of the raw cached response replicates. -/
noncomputable def modelReplicateMean
    {m p : Nat}
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (n : Nat) (ωresp : Ωresp) (f : Model Q X) : Acharyya2024.Mat m p :=
  replicateMean (Y n f) ωresp

/-- Target-augmented sample response means on the product sample space. -/
noncomputable def augmentedRawSampleMean
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) :
    Fin (n + 1) → Acharyya2024.Mat m p :=
  fun i => modelReplicateMean replicates Y n ω.2
    (augmentedModelAt f_ref n ω.1 f i)

/-- Target-augmented population response means.  These depend on the reference
sample through the selected reference models, but not on response noise. -/
def augmentedRawPopulationMean
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) :
    Fin (n + 1) → Acharyya2024.Mat m p :=
  fun i => μmodel (augmentedModelAt f_ref n ω.1 f i)

/-- Product of probability measures is a probability measure.

This should be a thin wrapper around Mathlib's product-measure instance.  Keep
it separate so all later files can install the stagewise instance with one
line. -/
theorem jointStageMeasure_probability
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n)) :
    ∀ n, IsProbabilityMeasure (jointStageMeasure μref μresp n) := by
  sorry

/-- The lifted reference sampler preserves its iid law under independent
product extension.

Suggested proof route: measurable coordinate maps are compositions with
`Prod.fst`; every joint event is a cylinder set `A ×ˢ univ`; install the two
stagewise probability instances, apply the product-measure formula, and simplify
the response-space mass to one. -/
theorem iidReferenceSampler_lifted_prod
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref) :
    IIDReferenceSampler Pf (jointStageMeasure μref μresp)
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref) := by
  sorry

/-- Model-level response-distance realization automatically realizes every
random target-augmented population batch. -/
theorem augmentedRawPopulationMean_realization
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (hrealize : ModelResponseRealization ψ μmodel) :
    PerspectiveResponseRealization ψ
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
      (augmentedRawPopulationMean f_ref μmodel) := by
  sorry

/-- A model-level population norm envelope lifts to every augmented batch. -/
theorem augmentedRawPopulationMean_norm_le
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    {B : Real} (hB : ∀ f, ‖μmodel f‖ ≤ B) :
    ∀ n (ω : Ωref × Ωresp) f i,
      ‖augmentedRawPopulationMean f_ref μmodel n ω f i‖ ≤ B := by
  intro n ω f i
  exact hB _

/-- Second-moment bound for one model's concrete replicate average.

Suggested proof route: install `Hraw.probability n` locally and apply
`integral_norm_sq_replicateMean_sub_mean_le_of_bound` from
`Acharyya2025.GrowingResponse` with the corresponding structure fields. -/
theorem integral_norm_sq_modelReplicateMean_sub_mean_le
    {m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (f : Model Q X) :
    ∫ ωresp,
      ‖modelReplicateMean replicates Y n ωresp f - μmodel f‖ ^ 2
        ∂(μresp n) ≤ variance n / replicates n := by
  sorry

/-- Uniform modelwise second moments transfer through random reference
selection on the independent product space.

This is the Fubini/selection lemma.  For each fixed reference outcome, every
augmented coordinate selects some model, and the response-space integral is
bounded uniformly by the preceding theorem.  Integrate that bound over the
reference space.  Do not assume the model class is finite. -/
theorem integral_norm_sq_augmentedRawSampleMean_sub_population_le
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (f : Model Q X) (i : Fin (n + 1)) :
    ∫ ω,
      ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
        augmentedRawPopulationMean f_ref μmodel n ω f i‖ ^ 2
        ∂(jointStageMeasure μref μresp n) ≤
      variance n / replicates n := by
  sorry

/-- Measurability and integrability package for augmented raw sample errors.

The proof should use product measurability, finite replicate sums, and the
measurability fields in `RawIIDResponseModel`.  The population term depends only
on the reference coordinate; its measurability follows from the reference
sampler and any model-level measurability needed by the application.  If the
current `IIDReferenceSampler` interface is insufficient, add the smallest
model-level measurability field to `RawIIDResponseModel` rather than assuming
measurability separately at every augmented index. -/
theorem integrable_sq_augmentedRawSampleMean_sub_population
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (f : Model Q X) (i : Fin (n + 1)) :
    Integrable (fun ω =>
      ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
        augmentedRawPopulationMean f_ref μmodel n ω f i‖ ^ 2)
      (jointStageMeasure μref μresp n) := by
  sorry

/-- Measurability of the target-augmented raw response event.

Use joint measurability of the raw response array, measurability of the model
mean, and measurability of the lifted reference sampler.  The universal target
quantifier is finite in the theorem below; the infinite-model path avoids this
event and uses measurable finite-net subevents instead. -/
theorem measurableSet_augmentedRawResponseMeanEvent_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ω => f_ref n ω i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance η : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) :
    MeasurableSet (augmentedUniformResponseMeanEvent
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η n) := by
  sorry

/-- Finite-model uniform response concentration derived directly from raw iid
replicates.

Completing this theorem removes the abstract `Xbar`, per-index integrability,
per-index second-moment, and response-event hypotheses from the finite-model
Perfect Quench capstone.  The remaining rate condition is explicit in the
replicate count and tolerance.  The reference measurability argument is passed
separately here and is discharged by `IIDReferenceSampler.measurable` in the
final capstone. -/
theorem highProb_augmentedRawResponseMean_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance η : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (hη : ∀ n, 0 < η n)
    (hratio : Tendsto (fun n =>
      (Fintype.card (Model Q X) : Real) * ((n + 1 : Nat) : Real) *
        (variance n / replicates n) / (η n) ^ 2) atTop (𝓝 0)) :
    HighProbAtTop (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedUniformResponseMeanEvent
        (augmentedRawSampleMean f_ref replicates Y)
        (augmentedRawPopulationMean f_ref μmodel) η) := by
  sorry

/-- Finite-model measurable subevent certificate for raw response means.

This packages the preceding probability and measurability theorems in the exact
form consumed by the Perfect Quench spectral capstone. -/
noncomputable def augmentedRawResponseMeanSubevents_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ω => f_ref n ω i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance η : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (hη : ∀ n, 0 < η n)
    (hratio : Tendsto (fun n =>
      (Fintype.card (Model Q X) : Real) * ((n + 1 : Nat) : Real) *
        (variance n / replicates n) / (η n) ^ 2) atTop (𝓝 0)) :
    AugmentedResponseMeanSubevents
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η := by
  sorry

end DkpsQuench.Perfect
