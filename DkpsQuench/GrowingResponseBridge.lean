/-
Concrete response-mean input for the growing target-augmented Quench theorem.

GrowingAcharyyaBridge starts from a measurable high-probability family of
entrywise CMDS events.  This file constructs those events from random response
mean matrices.  Thus applications now expose response-level second moments or
replicate averages rather than assuming the matrix concentration conclusion.
-/

import Acharyya2025.GrowingResponse
import DkpsQuench.GrowingAcharyyaBridge

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

namespace DkpsQuench.GrowingResponseBridge

open Acharyya2024
open Acharyya2025.Bridge
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.MatrixPerturbation
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open DkpsQuench.GrowingAcharyyaBridge

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type w} [MeasurableSpace Ω]
variable {d : Nat}

/-- Sample dissimilarity matrix of the response-mean augmented batch. -/
noncomputable def augmentedSampleResponseDist
    {m p : Nat}
    (Xbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (n : Nat) (ω : Ω) (f : Model Q X) : DisMat (n + 1) :=
  responseDist (Xbar n ω f)

/-- Population dissimilarity matrix of the response-mean augmented batch. -/
noncomputable def augmentedPopulationResponseDist
    {m p : Nat}
    (μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (n : Nat) (ω : Ω) (f : Model Q X) : DisMat (n + 1) :=
  responseDist (μbar n ω f)

/-- Uniform target-wise response-mean event for the augmented batch. -/
def augmentedUniformResponseMeanEvent
    {m p : Nat}
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η : Nat → Real) (n : Nat) : Set Ω :=
  {ω | ∀ f, UniformResponseMeanClose
    (Xbar n ω f) (μbar n ω f) (η n)}

/-- Response-mean form of the growing target-augmented Quench capstone.

The CMDS entrywise event is derived deterministically from uniform augmented
response-mean closeness and bounded sample/population dissimilarities.  The
remaining probability input is therefore stated at the response level. -/
theorem highProbQQueryEfficient_tieAverage_of_growing_augmented_response_mean
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μΩ : Nat → Measure Ω) (hμΩ : ∀ n, IsProbabilityMeasure (μΩ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μΩ f_ref)
    {m p : Nat}
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η R : Nat → Real)
    (hmeanMeas : ∀ n,
      MeasurableSet (augmentedUniformResponseMeanEvent Xbar μbar η n))
    (hmean : HighProbAtTop μΩ hμΩ
      (augmentedUniformResponseMeanEvent Xbar μbar η))
    (hsampleBound : ∀ n ω f i j,
      |responseDist (Xbar n ω f) i j| ≤ R n)
    (hpopulationBound : ∀ n ω f i j,
      |responseDist (μbar n ω f) i j| ≤ R n)
    (hB : ∀ n ω f,
      (disMatToMatrix
        (classicalMDSMatrix (responseDist (μbar n ω f)))).PosSemidef)
    (hrank : ∀ n ω f,
      (disMatToMatrix
        (classicalMDSMatrix (responseDist (μbar n ω f)))).rank ≤ d)
    {α : Real} (hα : 0 < α)
    (ceiling : Nat → Real)
    (hfloor : ∀ n ω f (i : Fin (n + 1)), (i : Nat) < d →
      α ≤ sortedEigenvalues (hB n ω f).isHermitian i)
    (hceiling : ∀ n ω f (i : Fin (n + 1)),
      sortedEigenvalues (hB n ω f).isHermitian i ≤ ceiling n)
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (responseDist (μbar n ω f)) i j)
    (hzRadial : ∀ n ω f (i : Fin n),
      ‖z n ω f i.castSucc - z n ω f (Fin.last n)‖ =
        ‖ψ (f_ref n ω i) - ψ f‖)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling
      (fun n => cmdsEntrywiseRate (n + 1) m (R n) (η n)))
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μΩ hμΩ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        (augmentedSampleResponseDist Xbar)
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  let Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1) :=
    augmentedSampleResponseDist Xbar
  let D : ∀ n, Ω → Model Q X → DisMat (n + 1) :=
    augmentedPopulationResponseDist μbar
  let E : Nat → Set Ω := augmentedUniformResponseMeanEvent Xbar μbar η
  have hEsub : ∀ n, E n ⊆ {ω | ∀ f,
      EntrywiseClose
        (classicalMDSMatrix (Dhat n ω f))
        (classicalMDSMatrix (D n ω f))
        (cmdsEntrywiseRate (n + 1) m (R n) (η n))} := by
    intro n ω hω f
    simpa [Dhat, D, augmentedSampleResponseDist,
      augmentedPopulationResponseDist] using
      cmdsEntrywise_of_responseMeanClose (by omega)
        (Xbar n ω f) (μbar n ω f) (hω f)
        (hsampleBound n ω f) (hpopulationBound n ω f)
  exact highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds
    Pf μΩ hμΩ ψ hψmeas hcompact hfull f_ref hiid
    Dhat D
    (fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (Xbar n ω f))
    hB hrank hα ceiling
    (fun n => cmdsEntrywiseRate (n + 1) m (R n) (η n))
    hfloor hceiling z hzGram hzRadial Hrate
    E hmeanMeas hEsub hmean score Qstar Qsub γ hlip hγ hbase

/-- Finite-model second-moment capstone.  When the target model class is finite,
a double union bound over targets and augmented-batch indices derives the
uniform response event consumed by the general response-mean theorem. -/
theorem highProbQQueryEfficient_tieAverage_of_growing_augmented_secondMoment
    [Fintype (Model Q X)]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μΩ : Nat → Measure Ω) (hμΩ : ∀ n, IsProbabilityMeasure (μΩ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μΩ f_ref)
    {m p : Nat}
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (σ2 η R : Nat → Real)
    (hint : ∀ n f (i : Fin (n + 1)),
      Integrable (fun ω =>
        ‖Xbar n ω f i - μbar n ω f i‖ ^ 2) (μΩ n))
    (hσ2 : ∀ n f (i : Fin (n + 1)),
      ∫ ω, ‖Xbar n ω f i - μbar n ω f i‖ ^ 2 ∂(μΩ n) ≤ σ2 n)
    (hηPos : ∀ n, 0 < η n)
    (hratio : Tendsto
      (fun n =>
        (Fintype.card (Model Q X) : Real) * ((n + 1 : Nat) : Real) *
          σ2 n / (η n) ^ 2)
      atTop (𝓝 0))
    (hXmeas : ∀ n f i, Measurable fun ω => Xbar n ω f i)
    (hμmeas : ∀ n f i, Measurable fun ω => μbar n ω f i)
    (hsampleBound : ∀ n ω f i j,
      |responseDist (Xbar n ω f) i j| ≤ R n)
    (hpopulationBound : ∀ n ω f i j,
      |responseDist (μbar n ω f) i j| ≤ R n)
    (hB : ∀ n ω f,
      (disMatToMatrix
        (classicalMDSMatrix (responseDist (μbar n ω f)))).PosSemidef)
    (hrank : ∀ n ω f,
      (disMatToMatrix
        (classicalMDSMatrix (responseDist (μbar n ω f)))).rank ≤ d)
    {α : Real} (hα : 0 < α)
    (ceiling : Nat → Real)
    (hfloor : ∀ n ω f (i : Fin (n + 1)), (i : Nat) < d →
      α ≤ sortedEigenvalues (hB n ω f).isHermitian i)
    (hceiling : ∀ n ω f (i : Fin (n + 1)),
      sortedEigenvalues (hB n ω f).isHermitian i ≤ ceiling n)
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (responseDist (μbar n ω f)) i j)
    (hzRadial : ∀ n ω f (i : Fin n),
      ‖z n ω f i.castSucc - z n ω f (Fin.last n)‖ =
        ‖ψ (f_ref n ω i) - ψ f‖)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling
      (fun n => cmdsEntrywiseRate (n + 1) m (R n) (η n)))
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μΩ hμΩ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        (augmentedSampleResponseDist Xbar)
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  have hmeanA : Acharyya2024.HighProbAtTop μΩ
      (fun n => {ω | ∀ f i,
        ‖Xbar n ω f i - μbar n ω f i‖ ≤ η n}) :=
    highProb_uniformTargetResponseMeanClose_of_secondMoment
      μΩ (fun n => n + 1) Xbar μbar σ2 η
      hint hσ2 hηPos hratio
  have hmeanQ : HighProbAtTop μΩ hμΩ
      (augmentedUniformResponseMeanEvent Xbar μbar η) := by
    intro δ hδ
    exact hmeanA δ hδ
  have hmeanMeas : ∀ n,
      MeasurableSet (augmentedUniformResponseMeanEvent Xbar μbar η n) := by
    intro n
    exact measurableSet_uniformTargetResponseMeanClose
      (Xbar n) (μbar n) (η n) (hXmeas n) (hμmeas n)
  exact highProbQQueryEfficient_tieAverage_of_growing_augmented_response_mean
    Pf μΩ hμΩ ψ hψmeas hcompact hfull f_ref hiid
    Xbar μbar η R hmeanMeas hmeanQ
    hsampleBound hpopulationBound hB hrank hα ceiling
    hfloor hceiling z hzGram hzRadial Hrate
    score Qstar Qsub γ hlip hγ hbase

end DkpsQuench.GrowingResponseBridge
