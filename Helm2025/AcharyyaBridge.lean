/-
Deterministic bridges from the Acharyya DKPS concentration scaffolds to the
Helm et al. 2025 alignment-consistency interface.

The probability/convergence bridge still needs measurability and fixed-measure
bookkeeping.  This file isolates the theorem that does not need those analytic
assumptions: Acharyya-style finite configuration error controls Helm's finite
sample `iSup` alignment error.
-/

import Acharyya2025.Bridge
import Acharyya2025.AlignedPipeline
import Helm2025.Basic

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Helm2025.DKPS.AcharyyaBridge

open Acharyya2024

variable {Ω : Type} [MeasurableSpace Ω]

/--
Acharyya finite-configuration error controls Helm's samplewise alignment error
for the identity alignment.

This is the deterministic core needed before upgrading an Acharyya-style
high-probability configuration bound into Helm's `DKPSAlignmentConsistency`.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_iSup_le_configError
    {n d d' : Nat}
    (ψhat : (Sample n d d') → Fin (n + 1) → E d)
    (ω : Sample n d d') :
    (⨆ i : Fin (n + 1), dist (ψhat ω i) ((ω i).1))
      ≤ ConfigError (ψhat ω) (fun i : Fin (n + 1) => (ω i).1) := by
  exact ciSup_le fun i => by
    simpa [dist_eq_norm] using
      norm_config_le_ConfigError (ψhat ω) (fun i : Fin (n + 1) => (ω i).1) i

/--
The finite-sample Helm alignment error is nonnegative.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_iSup_nonneg
    {n d d' : Nat}
    (ψhat : (Sample n d d') → Fin (n + 1) → E d)
    (ω : Sample n d d') :
    0 ≤ (⨆ i : Fin (n + 1), dist (ψhat ω i) ((ω i).1)) := by
  have hle :
      dist (ψhat ω (Fin.last n)) ((ω (Fin.last n)).1)
        ≤ (⨆ i : Fin (n + 1), dist (ψhat ω i) ((ω i).1)) :=
    le_ciSup
      (Finite.bddAbove_range
        (fun i : Fin (n + 1) => dist (ψhat ω i) ((ω i).1)))
      (Fin.last n)
  exact dist_nonneg.trans hle

/--
Event-level bridge from an Acharyya-style configuration-error event to Helm's
sample-alignment-error event.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_event_of_configError_event
    {n d d' : Nat}
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (u : Nat) :
    {ω : Sample n d d' |
      ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u}
      ⊆
    {ω : Sample n d d' |
      (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1)) ≤ rate u} := by
  intro ω hω
  exact (sample_alignment_iSup_le_configError (ψhat u) ω).trans hω

/--
Event-level bridge from an Acharyya-style configuration-error event to the
absolute-value event used by Helm's convergence-in-probability definition.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_abs_event_of_configError_event
    {n d d' : Nat}
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (u : Nat) :
    {ω : Sample n d d' |
      ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u}
      ⊆
    {ω : Sample n d d' |
      |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u} := by
  intro ω hω
  change |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u
  rw [abs_of_nonneg (sample_alignment_iSup_nonneg (ψhat u) ω)]
  exact (sample_alignment_iSup_le_configError (ψhat u) ω).trans hω

/--
High-probability event bridge from Acharyya-style finite configuration
concentration to Helm-style finite sample alignment-error concentration.

This deliberately stays at the high-probability event layer.  The next formal
bridge to `DKPSAlignmentConsistency` should add the fixed product measure,
measurability, and `rate → 0` assumptions needed to turn these events into
convergence in probability.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem highProb_sample_alignment_of_configError
    {n d d' : Nat}
    (P : Nat → Measure (Sample n d d'))
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (hconfig :
      HighProbAtTop P
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    HighProbAtTop P
      (fun u =>
        {ω : Sample n d d' |
          (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1)) ≤ rate u}) := by
  exact HighProbAtTop.mono hconfig
    (fun u => sample_alignment_event_of_configError_event ψhat rate u)

/--
High-probability event bridge for the absolute-value version of the Helm sample
alignment error.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem highProb_abs_sample_alignment_of_configError
    {n d d' : Nat}
    (P : Nat → Measure (Sample n d d'))
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (hconfig :
      HighProbAtTop P
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    HighProbAtTop P
      (fun u =>
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u}) := by
  exact HighProbAtTop.mono hconfig
    (fun u => sample_alignment_abs_event_of_configError_event ψhat rate u)

/--
High-probability Acharyya-style finite configuration concentration with a
deterministic rate tending to zero gives Helm's finite-sample alignment error
convergence in probability.

The measurability hypothesis is the genuine remaining analytic bridge needed to
turn event-level high-probability control into convergence in probability.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_convergesInProbabilityToZero_of_highProb_configError
    {n d d' : Nat}
    (P : Measure (Sample n d d')) [IsProbabilityMeasure P]
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u})
    (hrate : Tendsto rate atTop (𝓝 0))
    (hconfig :
      HighProbAtTop (fun _u : Nat => P)
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    ConvergesInProbabilityToZero P
      (fun u ω => (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))) := by
  exact tendsto_measure_abs_gt_zero_of_highProb_abs_le_rate P
    (fun u ω => (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1)))
    rate hgood_meas hrate
    (highProb_abs_sample_alignment_of_configError
      (fun _u : Nat => P) ψhat rate hconfig)

/--
Acharyya-style finite configuration concentration supplies Helm's alignment
consistency with the identity affine-isometry alignment.

This theorem is the currently cleanest formal seam between Acharyya2025 and
Helm2025: the remaining hypotheses are rate convergence, rate nonnegativity, and
measurability of the finite sample alignment events.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem alignmentConsistency_of_highProb_configError
    {n d d' : Nat}
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u})
    (hrate : Tendsto rate atTop (𝓝 0))
    (hconfig :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    DKPSAlignmentConsistency n d d' P ψhat := by
  refine ⟨fun _u => AffineIsometryEquiv.refl Real (E d), ?_⟩
  simpa using
    sample_alignment_convergesInProbabilityToZero_of_highProb_configError
      (Measure.pi (fun _ : Fin (n + 1) => P))
      ψhat rate hgood_meas hrate hconfig

/--
**Helm alignment consistency from the aligned CMDS spectral estimator.**

Helm's population configuration is the *per-`ω`* tuple of latents
`fun i => (ω i).1`, so the matrix-world capstone (which fixes a single population
Gram matrix) cannot be instantiated against a single fixed `ψ`.  Instead the
aligned estimator is evaluated with the ω-dependent population fed in as its `ψ`
argument:
`ψhat u ω := alignedSpectralConfig hd Dhat hsym (fun i => (ω i).1) cBound u ω`.

By `configError_alignedSpectralConfig_le`, whenever the alignment isometry exists
at sample `(u, ω)` against this per-`ω` population (the hypothesis `halign`), the
estimator achieves `ConfigError ≤ cBound u`.  We transport the high-probability
alignment-existence event to the high-probability `ConfigError` event and feed it
to the existing `alignmentConsistency_of_highProb_configError`, discharging Helm's
`DKPSAlignmentConsistency`.

What is composed: the per-`ω` alignment-existence event is turned into the
`ConfigError` event by the aligned estimator's defining property.  What is
hypothesized: the high-probability alignment-existence event `halign`, the
measurability of the sample alignment events, and the rate convergence.

HONEST SEAM.  `halign` is *not derived anywhere in this development* — it is an
assumed primitive that subsumes the paper's core high-probability alignment
guarantee.  The matrix-world capstone
`Acharyya2025.AlignedPipeline.highProb_alignedSpectralConfigError` produces this
event, but only against a *single fixed* population configuration realizing a
fixed Gram matrix; the Helm setting feeds the *per-`ω`* population
`fun i => (ω i).1`, which cannot satisfy a single fixed-Gram realization, so the
capstone cannot be instantiated and `halign` must be assumed.  Consequently this
bridge is a faithful *reduction* of Helm's alignment consistency to a
per-`ω`-population alignment event, NOT an end-to-end derivation of it.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem alignmentConsistency_of_aligned_spectral
    {n d d' : Nat} (hd : d ≤ n + 1)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (Dhat : Nat → (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (rate : Nat → Real)
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1),
              dist
                (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                  (fun i : Fin (n + 1) => (ω i).1) rate u ω i)
                ((ω i).1))| ≤ rate u})
    (hrate : Tendsto rate atTop (𝓝 0))
    (halign :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym
              (fun i : Fin (n + 1) => (ω i).1) rate u ω})) :
    DKPSAlignmentConsistency n d d' P
      (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
        (fun i : Fin (n + 1) => (ω i).1) rate u ω) := by
  -- Transport the alignment-existence HP event to the `ConfigError` HP event.
  have hconfig :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            ConfigError
              (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                (fun i : Fin (n + 1) => (ω i).1) rate u ω)
              (fun i : Fin (n + 1) => (ω i).1) ≤ rate u}) := by
    refine HighProbAtTop.mono halign (fun u ω hω => ?_)
    exact Acharyya2025.AlignedPipeline.configError_alignedSpectralConfig_le
      hd Dhat hsym (fun i : Fin (n + 1) => (ω i).1) rate u ω hω
  exact alignmentConsistency_of_highProb_configError P
    (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
      (fun i : Fin (n + 1) => (ω i).1) rate u ω)
    rate hgood_meas hrate hconfig

end Helm2025.DKPS.AcharyyaBridge
