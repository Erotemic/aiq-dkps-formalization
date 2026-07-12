/-
Growing target-augmented Acharyya2025 bridge for Quench.

The earlier bridge represented the entire model class by one fixed finite
configuration and an `indexOf : Model → Fin n`.  This module removes that
factorization.  At stage `n`, each target is adjoined to the `n` sampled
reference models, producing an `(n+1)`-point CMDS problem.  Quench uses only the
sample target-to-reference distances.  The choice-free pairwise-distance theorem
in `Acharyya2025.GrowingPipeline` controls those distances directly.
-/

import Acharyya2025.GrowingPipeline
import Acharyya2025.GramRealization
import DkpsQuench.Radial
import Acharyya2025.SpectralMeasurability

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

namespace DkpsQuench.GrowingAcharyyaBridge

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.MatrixPerturbation
open Acharyya2025.GrowingPipeline

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type w} [MeasurableSpace Ω]
variable {d : Nat}

/-- Raw sample CMDS configuration for the target-augmented stage.  Before the
stage contains at least `d` points, use the zero configuration; the asymptotic
proof restricts to the eventual branch `d ≤ n+1`. -/
noncomputable def rawAugmentedSpectralConfig
    (Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (hsym : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))).IsHermitian)
    (n : Nat) (ω : Ω) (f : Model Q X) : Config (n + 1) d := by
  by_cases hd : d ≤ n + 1
  · exact spectralConfig
      (Matrix.toEuclideanLin
        (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))))
      (opSym (hsym n ω f)) hd
  · exact fun _ => 0

@[simp] theorem rawAugmentedSpectralConfig_of_dimension
    (Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (hsym : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))).IsHermitian)
    (n : Nat) (ω : Ω) (f : Model Q X) (hd : d ≤ n + 1) :
    rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f =
      spectralConfig
        (Matrix.toEuclideanLin
          (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))))
        (opSym (hsym n ω f)) hd := by
  simp [rawAugmentedSpectralConfig, hd]

/-- Estimated distance from reference `i` to the adjoined target, measured in
the raw sample CMDS configuration. -/
noncomputable def augmentedSpectralRadialDistance
    (Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (hsym : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))).IsHermitian)
    (n : Nat) (ω : Ω) (f : Model Q X) (i : Fin n) : Real :=
  let zhat := rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f
  ‖zhat i.castSucc - zhat (Fin.last n)‖

/-- Literal tie-averaged Quench estimator using the raw target-augmented CMDS
distances.  No global estimated perspective map and no model-to-finite-index
factorization are present. -/
noncomputable def yNNTieAverage_augmentedCMDS
    (Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (hsym : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))).IsHermitian)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (n : Nat) (ω : Ω) (f : Model Q X) : Real :=
  radialTieAverageNN
    (augmentedSpectralRadialDistance (d := d) Dhat hsym)
    f_ref (yFull score Qstar) n ω f


/-- A population Gram realization already implies positive semidefiniteness of
its classical-MDS matrix.  This is exposed separately so higher-level Quench
capstones do not ask callers to restate a consequence of their Gram witness. -/
noncomputable def populationPosSemidefOfGram
    (D : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (D n ω f) i j)
    (n : Nat) (ω : Ω) (f : Model Q X) :
    (disMatToMatrix (classicalMDSMatrix (D n ω f))).PosSemidef :=
  (Acharyya2025.GramRealization.posSemidef_and_rank_le_of_config_gram_eq
    (disMatToMatrix (classicalMDSMatrix (D n ω f)))
    (z n ω f) (hzGram n ω f)).1

/-- A population Gram realization in dimension `d` automatically bounds the
rank of its classical-MDS matrix by `d`. -/
theorem populationRankLeOfGram
    (D : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (D n ω f) i j)
    (n : Nat) (ω : Ω) (f : Model Q X) :
    (disMatToMatrix (classicalMDSMatrix (D n ω f))).rank ≤ d :=
  (Acharyya2025.GramRealization.posSemidef_and_rank_le_of_config_gram_eq
    (disMatToMatrix (classicalMDSMatrix (D n ω f)))
    (z n ω f) (hzGram n ω f)).2

/--
**Growing target-augmented Quench capstone.**

At stage `n`, the sample and population CMDS problems contain the `n` sampled
references plus the current target.  A measurable high-probability subevent
supplies uniform entrywise CMDS closeness over all targets.  Uniform spectral
hypotheses and a `GrowingConfigControl` convert that event to a vanishing radial
distance error.  Compact perspective range, full support, and iid reference
sampling supply coverage.  The literal tie-averaged estimator is therefore
eventually query-efficient.

This theorem removes the old global `indexOf : Model → Fin N` assumption.  The
remaining statistical seam is the high-probability uniform entrywise event for
the random target-augmented matrices; it is now isolated in exactly the form a
future joint response-array theorem must prove.

The completion scaffold in `DkpsQuench.Perfect` records how every heavier input
of this compatibility theorem is dispatched.  `PopulationGeometry` constructs
`z`, `hzGram`, and `hzRadial` from one response-distance realization;
`SpectralRegularity` replaces global `hfloor` and `hceiling` by a measurable
high-probability covariance event; `RawResponses`, `Compactness`, and
`UniformConcentration` construct `E` without exposing finite nets or response
envelopes; and `RateSchedule` constructs `entryRate` and `Hrate`.  The
proved bespoke pairwise-distance argument below remains the production engine
until a newer Davis--Kahan result removes a visible premise rather than merely
shortening the proof.
-/
theorem highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds
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
    (hB : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (D n ω f))).PosSemidef)
    (hrank : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (D n ω f))).rank ≤ d)
    {α : Real} (hα : 0 < α)
    (ceiling entryRate : Nat → Real)
    (hfloor : ∀ n ω f (i : Fin (n + 1)), (i : Nat) < d →
      α ≤ sortedEigenvalues (hB n ω f).isHermitian i)
    (hceiling : ∀ n ω f (i : Fin (n + 1)),
      sortedEigenvalues (hB n ω f).isHermitian i ≤ ceiling n)
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (D n ω f) i j)
    (hzRadial : ∀ n ω f (i : Fin n),
      ‖z n ω f i.castSucc - z n ω f (Fin.last n)‖ =
        ‖ψ (f_ref n ω i) - ψ f‖)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling entryRate)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f,
      Acharyya2025.Bridge.EntrywiseClose
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
  let good : Nat → Prop := fun n =>
    d ≤ n + 1 ∧
    ((n + 1 : Nat) : Real) * entryRate n ≤ α / 2 ∧
    (d : Real) *
      (4 * ((n + 1 : Nat) : Real) *
        ((((n + 1 : Nat) : Real) * entryRate n)^2) / α^2) ≤ 1 / 2 ∧
    configBound (n + 1) d α (ceiling n)
      (((n + 1 : Nat) : Real) * entryRate n) ≤ Hrate.bound n
  let Eg : Nat → Set Ω := fun n => E n ∩ {ω | good n}
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [eventually_dimension_le_succ d, Hrate.eventually_all]
      with n hdim hsides
    exact ⟨hdim, hsides.1, hsides.2.1, hsides.2.2⟩
  have hEgMeas : ∀ n, MeasurableSet (Eg n) := by
    intro n
    by_cases hn : good n
    · simpa [Eg, hn] using hEmeas n
    · simpa [Eg, hn] using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hEg : HighProbAtTop μ hμ Eg := by
    apply hE.mono_eventually
    filter_upwards [hgood] with n hn
    intro ω hω
    exact ⟨hω, hn⟩
  let radialRate : Nat → Real := fun n => 2 * Hrate.bound n
  have hradialRateZero : Tendsto radialRate atTop (nhds 0) := by
    dsimp [radialRate]
    simpa using tendsto_const_nhds.mul Hrate.bound_zero
  have hradialRateNonneg : ∀ n, 0 ≤ radialRate n := by
    intro n
    dsimp [radialRate]
    exact mul_nonneg (by norm_num) (Hrate.bound_nonneg n)
  have hEgSub : ∀ n, Eg n ⊆ {ω | ∀ f i,
      |augmentedSpectralRadialDistance (d := d) Dhat hsym n ω f i -
          ‖ψ (f_ref n ω i) - ψ f‖| ≤ radialRate n} := by
    intro n ω hω f i
    rcases hω with ⟨hentryEvent, hdim, hsmall, hpolar, hbound⟩
    have hentry := hEsub n hentryEvent f
    -- This low-level step deliberately retains the proved bespoke
    -- cross-energy/polar argument.  The newer sharp projector theory should
    -- replace it only when that replacement removes a caller-side condition
    -- such as polar smallness; a cleanup-only refactor is deferred.
    have hpair :=
      abs_pairwiseDistance_spectralConfig_sub_le_two_configBound
        hdim
        (disMatToMatrix (classicalMDSMatrix (D n ω f)))
        (disMatToMatrix (classicalMDSMatrix (Dhat n ω f)))
        (hB n ω f) (hsym n ω f) (hrank n ω f)
        hα (Hrate.entry_nonneg n) (hfloor n ω f) (hceiling n ω f)
        hentry hsmall hpolar (z n ω f) (hzGram n ω f)
        i.castSucc (Fin.last n)
    have hraw : rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f =
        spectralConfig
          (Matrix.toEuclideanLin
            (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))))
          (opSym (hsym n ω f)) hdim :=
      rawAugmentedSpectralConfig_of_dimension Dhat hsym n ω f hdim
    change
      |‖rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f i.castSucc -
            rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f (Fin.last n)‖ -
          ‖ψ (f_ref n ω i) - ψ f‖| ≤ 2 * Hrate.bound n
    rw [hraw, ← hzRadial n ω f i]
    exact hpair.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))
  exact highProbQQueryEfficient_radialTieAverage_of_compact_iid_fullSupport
    Pf μ hμ ψ hψmeas hcompact hfull
    (augmentedSpectralRadialDistance (d := d) Dhat hsym)
    f_ref hiid score Qstar Qsub γ hlip hγ
    radialRate hradialRateZero hradialRateNonneg
    Eg hEgMeas hEgSub hEg hbase


/-- Hypothesis-reduced growing CMDS capstone.

The population configuration witness and its Gram identity imply both positive
semidefiniteness and the rank bound.  This theorem therefore removes the
redundant explicit `hB` and `hrank` arguments from the public interface while
reusing the established spectral proof unchanged. -/
theorem highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_of_gram
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
    (hfloor : ∀ n ω f (i : Fin (n + 1)), (i : Nat) < d →
      α ≤ sortedEigenvalues
        (populationPosSemidefOfGram D z hzGram n ω f).isHermitian i)
    (hceiling : ∀ n ω f (i : Fin (n + 1)),
      sortedEigenvalues
        (populationPosSemidefOfGram D z hzGram n ω f).isHermitian i ≤ ceiling n)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling entryRate)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f,
      Acharyya2025.Bridge.EntrywiseClose
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
  exact highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds
    Pf μ hμ ψ hψmeas hcompact hfull f_ref hiid Dhat D hsym
    (populationPosSemidefOfGram D z hzGram)
    (populationRankLeOfGram D z hzGram)
    hα ceiling entryRate hfloor hceiling z hzGram hzRadial Hrate
    E hEmeas hEsub hE score Qstar Qsub γ hlip hγ hbase

end DkpsQuench.GrowingAcharyyaBridge
