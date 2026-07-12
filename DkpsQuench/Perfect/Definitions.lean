/-
Shared definitions for the remaining Perfect Quench proof program.

This namespace deliberately separates paper-facing assumptions from the
intermediate objects consumed by the existing growing CMDS theorem.  Each later
module removes one group of caller-visible hypotheses and records the exact
bridge theorem that is still open.
-/

import DkpsQuench.GrowingResponseBridge

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open scoped RealInnerProductSpace
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
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.MatrixPerturbation
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open DkpsQuench.GrowingAcharyyaBridge
open DkpsQuench.GrowingResponseBridge

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- The model occupying one coordinate of the target-augmented stage.  The
first `n` coordinates are sampled references and the final coordinate is the
current target. -/
def augmentedModelAt
    {Ωref : Type wr}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (f : Model Q X) :
    Fin (n + 1) → Model Q X :=
  Fin.lastCases f (f_ref n ωref)

/-- The uncentered perspective configuration of the references and target. -/
def augmentedPerspectiveConfig
    {Ωref : Type wr} {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (f : Model Q X) : Config (n + 1) d :=
  fun i => ψ (augmentedModelAt f_ref n ωref f i)

/-- Arithmetic centroid of a finite Euclidean configuration. -/
noncomputable def configCentroid {n d : Nat} (z : Config n d) : Vec d :=
  (n : Real)⁻¹ • ∑ i, z i

/-- Translation of a configuration to zero centroid. -/
noncomputable def centerConfig {n d : Nat} (z : Config n d) : Config n d :=
  fun i => z i - configCentroid z

/-- Centered reference-plus-target perspective configuration. -/
noncomputable def centeredAugmentedPerspectiveConfig
    {Ωref : Type wr} {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (f : Model Q X) : Config (n + 1) d :=
  centerConfig (augmentedPerspectiveConfig ψ f_ref n ωref f)


/-- Gram matrix of a finite Euclidean configuration, represented in the
curried matrix format used by the Acharyya libraries. -/
noncomputable def configGram {n d : Nat} (z : Config n d) : DisMat n :=
  fun i j => ∑ k, z i k * z j k

/-- Positive semidefiniteness of a configuration Gram matrix. -/
noncomputable def configGramPosSemidef {n d : Nat} (z : Config n d) :
    (disMatToMatrix (configGram z)).PosSemidef :=
  (Acharyya2025.GramRealization.posSemidef_and_rank_le_of_config_gram_eq
    (disMatToMatrix (configGram z)) z (by intro i j; rfl)).1

/-- Paper-facing population geometry assumption: population response
Dissimilarities exactly equal Euclidean distances in the true perspective
space for every target-augmented batch.

Completing the population-geometry module turns this single hypothesis into the
configuration, Gram identity, positive-semidefinite/rank facts, and radial
identity currently requested separately by the growing Quench bridge. -/
def PerspectiveResponseRealization
    {Ωref : Type wr} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p) : Prop :=
  ∀ n ωref f i j,
    responseDist (μbar n ωref f) i j =
      ‖ψ (augmentedModelAt f_ref n ωref f i) -
        ψ (augmentedModelAt f_ref n ωref f j)‖

/-- Model-level version of the population geometry assumption.  Raw-response
capstones use one population response matrix per model; target-augmented
realization is then a definitional consequence. -/
def ModelResponseRealization
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (μmodel : Model Q X → Acharyya2024.Mat m p) : Prop :=
  ∀ f g,
    ((m : Real)⁻¹) * ‖μmodel f - μmodel g‖ = ‖ψ f - ψ g‖

/-- The exact geometric data consumed by the current growing CMDS theorem.
This structure is an internal target, not intended as a final paper-facing
assumption.  `populationGeometry_of_responseRealization` will construct it. -/
structure AugmentedPopulationGeometry
    {Ωref : Type wr} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p) where
  config : ∀ n, Ωref → Model Q X → Config (n + 1) d
  gram_eq : ∀ n ωref f i j,
    (∑ k, config n ωref f i k * config n ωref f j k) =
      classicalMDSMatrix (responseDist (μbar n ωref f)) i j
  radial_eq : ∀ n ωref f (i : Fin n),
    ‖config n ωref f i.castSucc - config n ωref f (Fin.last n)‖ =
      ‖ψ (f_ref n ωref i) - ψ f‖

/-- A nondegenerate population perspective distribution.  The chosen center is
required to be the population mean, and every direction has second moment at
least `κ`.  This is the genuine identifiability assumption that replaces the
current stage-by-stage eigenvalue-floor hypothesis.

The compactness/measurability assumptions in the spectral module will supply
integrability.  The proof agent should not add a second spectral-floor premise
to downstream capstones; this structure is meant to be the sole lower-spectrum
input. -/
structure PerspectiveNondegeneracy
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    (κ : Real) : Prop where
  kappa_pos : 0 < κ
  center : Vec d
  center_is_mean : ∀ j,
    ∫ f, (ψ f - center) j ∂Pf = 0
  quadratic_floor : ∀ x : Vec d,
    κ * ‖x‖ ^ 2 ≤ ∫ f, ((∑ j : Fin d, x j * (ψ f - center) j)) ^ 2 ∂Pf

/-- Measurable high-probability subevents certifying a uniform augmented
response-mean bound.  This avoids requiring measurability of a universal event
over an infinite model class. -/
structure AugmentedResponseMeanSubevents
    {Ω : Type*} [MeasurableSpace Ω]
    {m p : Nat}
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η : Nat → Real) where
  event : Nat → Set Ω
  measurable : ∀ n, MeasurableSet (event n)
  highProb : HighProbAtTop μ hμ event
  subset : ∀ n, event n ⊆ augmentedUniformResponseMeanEvent Xbar μbar η n

/-- High-probability spectral regularity for the random target-augmented
population CMDS matrices.  This replaces global floor and ceiling assumptions
that currently quantify over every sampling outcome, including arbitrarily bad
reference samples.

Once `spectralSubevents_of_iid_nondegenerate` is completed, public Quench
capstones should accept `PerspectiveNondegeneracy` instead of this internal
certificate. -/
structure GrowingSpectralSubevents
    {Ωref : Type wr} [MeasurableSpace Ωref]
    {d : Nat}
    (μref : Nat → Measure Ωref)
    (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (D : ∀ n, Ωref → Model Q X → DisMat (n + 1))
    (z : ∀ n, Ωref → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ωref f i j,
      (∑ k, z n ωref f i k * z n ωref f j k) =
        classicalMDSMatrix (D n ωref f) i j)
    (α : Real) (ceiling : Nat → Real) where
  event : Nat → Set Ωref
  measurable : ∀ n, MeasurableSet (event n)
  highProb : HighProbAtTop μref hμref event
  floor : ∀ n ωref, ωref ∈ event n → ∀ f (i : Fin (n + 1)),
    (i : Nat) < d →
      α ≤ sortedEigenvalues
        (populationPosSemidefOfGram D z hzGram n ωref f).isHermitian i
  ceiling_bound : ∀ n ωref, ωref ∈ event n → ∀ f (i : Fin (n + 1)),
    sortedEigenvalues
        (populationPosSemidefOfGram D z hzGram n ωref f).isHermitian i ≤
      ceiling n

/-- A stage-dependent finite perspective net used to upgrade pointwise response
concentration to uniform concentration over an infinite model class. -/
structure GrowingPerspectiveNet {d : Nat} (ψ : Model Q X → Vec d) where
  radius : Nat → Real
  radius_pos : ∀ n, 0 < radius n
  radius_zero : Tendsto radius atTop (𝓝 0)
  centers : Nat → Finset (Model Q X)
  covers : ∀ n, PerspectiveFiniteCover ψ (radius n) (centers n)

/-- Uniform regularity needed to extend response-mean control from a finite net
to the full model class.  The sample Lipschitz condition is intentionally
separate from the population condition: future applications may prove the
former from a pathwise Lipschitz response embedding and the latter by
integration. -/
structure UniformModelResponseRegularity
    {Ωresp : Type wy} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (Lsample Lpopulation : Nat → Real) : Prop where
  sample_nonneg : ∀ n, 0 ≤ Lsample n
  population_nonneg : ∀ n, 0 ≤ Lpopulation n
  sample_lipschitz : ∀ n ω f g,
    ‖Xbar n ω f - Xbar n ω g‖ ≤
      Lsample n * ‖ψ f - ψ g‖
  population_lipschitz : ∀ n f g,
    ‖μmodel f - μmodel g‖ ≤
      Lpopulation n * ‖ψ f - ψ g‖


/-- Uniform pathwise Lipschitz regularity of the raw response observations.

This is the paper-facing regularity assumption used by the compact infinite-
model route.  `Compactness.lean` derives both Lipschitz regularity of the
replicate mean and Lipschitz regularity of the population mean from this one
condition.  Final capstones should not ask callers to supply those two derived
certificates separately. -/
structure RawResponseLipschitz
    {Ωresp : Type wy}
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (L : Real) : Prop where
  constant_nonneg : 0 ≤ L
  bound : ∀ n f g k ω,
    ‖Y n f k ω - Y n g k ω‖ ≤ L * ‖ψ f - ψ g‖

/-- Raw iid response observations for every model at every asymptotic stage.
The response randomness is kept separate from the reference-sampling
randomness in `RawResponses.lean`; this avoids selection bias when a random
reference model is used to index a cached response array. -/
structure RawIIDResponseModel
    {Ωresp : Type wy} [MeasurableSpace Ωresp]
    {m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real) : Prop where
  probability : ∀ n, IsProbabilityMeasure (μresp n)
  replicates_pos : ∀ n, 0 < replicates n
  measurable : ∀ n f k, Measurable (Y n f k)
  jointly_measurable : ∀ n k,
    Measurable fun z : Model Q X × Ωresp => Y n z.1 k z.2
  mean_measurable : Measurable μmodel
  memLp_two : ∀ n f k, MemLp (Y n f k) 2 (μresp n)
  mean_entry : ∀ n f k c,
    ∫ ω, Y n f k ω c ∂(μresp n) = μmodel f c
  pairwise_independent : ∀ n f,
    Set.Pairwise (Set.univ : Set (Fin (replicates n)))
      fun k l => IndepFun (Y n f k) (Y n f l) (μresp n)
  second_moment : ∀ n f k,
    ∫ ω, ‖Y n f k ω - μmodel f‖ ^ 2 ∂(μresp n) ≤ variance n

end DkpsQuench.Perfect
