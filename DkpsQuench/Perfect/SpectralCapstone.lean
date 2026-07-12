/-
Quench capstones with probabilistic spectral regularity.

These theorems are the structural bridge between the existing proved growing
CMDS argument and the new covariance/spectral scaffold.  They differ from the
production theorem only in one essential way: eigenvalue floor and ceiling
conditions are allowed to hold on a measurable high-probability subevent rather
than for every random reference sample.
-/

import DkpsQuench.Perfect.RateSchedule

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

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
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open DkpsQuench.GrowingAcharyyaBridge
open DkpsQuench.GrowingResponseBridge

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Growing target-augmented Quench with a high-probability spectral
certificate.

Proof plan for a weaker agent:

1. copy the proof skeleton of
   `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds`;
2. replace its event `E ∩ {good n}` by the triple intersection of the CMDS
   entry event, `Hspectral.event`, and the deterministic rate event;
3. obtain the local floor and ceiling from `Hspectral.floor` and
   `Hspectral.ceiling_bound` at the current outcome;
4. use the existing bespoke pairwise-distance theorem unchanged;
5. finish with the same radial tie-average and iid coverage theorem.

Completing this theorem removes global `hfloor` and `hceiling` premises from all
later capstones.  Do not add them back as hidden fields. -/
theorem highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_spectralSubevents
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (Dhat D : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (hsym : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))).IsHermitian)
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (D n ω f) i j)
    (hzRadial : ∀ n ω f (i : Fin n),
      ‖z n ω f i.castSucc - z n ω f (Fin.last n)‖ =
        ‖ψ (f_ref n ω i) - ψ f‖)
    {α : Real} (hα : 0 < α)
    (ceiling entryRate : Nat → Real)
    (Hspectral : GrowingSpectralSubevents μ hμ D z hzGram α ceiling)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling entryRate)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f,
      EntrywiseClose
        (classicalMDSMatrix (Dhat n ω f))
        (classicalMDSMatrix (D n ω f)) (entryRate n)})
    (hE : HighProbAtTop μ hμ E)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        Dhat hsym f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  sorry

/-- Response-mean capstone with population geometry reduced to one distance
realization and spectral assumptions reduced to a high-probability certificate.

After the population-geometry and spectral-regularity modules are complete,
callers no longer provide `z`, a Gram proof, a radial proof, positive
semidefiniteness, rank, or global eigenvalue bounds.  This theorem is the direct
entry point for both raw finite-model and raw infinite-model response theorems. -/
theorem highProbQQueryEfficient_tieAverage_of_response_mean_realization_spectralSubevents
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η B : Nat → Real)
    (hηNonneg : ∀ n, 0 ≤ η n)
    (hmeanMeas : ∀ n,
      MeasurableSet (augmentedUniformResponseMeanEvent Xbar μbar η n))
    (hmean : HighProbAtTop μ hμ
      (augmentedUniformResponseMeanEvent Xbar μbar η))
    (hpopulationNorm : ∀ n ω f i, ‖μbar n ω f i‖ ≤ B n)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    {α : Real} (hα : 0 < α)
    (ceiling : Nat → Real)
    (Hspectral : GrowingSpectralSubevents μ hμ
      (fun n ω f => responseDist (μbar n ω f))
      (centeredAugmentedPerspectiveConfig ψ f_ref)
      (centeredAugmentedPerspectiveConfig_gram_eq
        ψ f_ref μbar hrealize)
      α ceiling)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling
      (fun n => cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (B n + η n)) (η n)))
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        (augmentedSampleResponseDist Xbar)
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  sorry

/-- Infinite-class-compatible response capstone using measurable response
subevents rather than measurability of the universal response event.

The proof should intersect `Hmean.event` with `Hspectral.event` and use
`Hmean.subset` only after entering the event.  Once complete, this is the sole
spectral/response theorem needed by both final Perfect Quench capstones. -/
theorem highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η B : Nat → Real)
    (hηNonneg : ∀ n, 0 ≤ η n)
    (Hmean : AugmentedResponseMeanSubevents μ hμ Xbar μbar η)
    (hpopulationNorm : ∀ n ω f i, ‖μbar n ω f i‖ ≤ B n)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    {α : Real} (hα : 0 < α)
    (ceiling : Nat → Real)
    (Hspectral : GrowingSpectralSubevents μ hμ
      (fun n ω f => responseDist (μbar n ω f))
      (centeredAugmentedPerspectiveConfig ψ f_ref)
      (centeredAugmentedPerspectiveConfig_gram_eq
        ψ f_ref μbar hrealize)
      α ceiling)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling
      (fun n => cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (B n + η n)) (η n)))
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        (augmentedSampleResponseDist Xbar)
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  sorry

end DkpsQuench.Perfect
