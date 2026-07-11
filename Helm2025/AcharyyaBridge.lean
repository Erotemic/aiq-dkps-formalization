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
import Acharyya2025.RateChain
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

The event-measurability hypothesis is the remaining analytic bridge needed to
turn event-level high-probability control into convergence in probability.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_convergesInProbabilityToZero_of_highProb_configError
    {n d d' : Nat}
    (P : Measure (Sample n d d')) [IsProbabilityMeasure P]
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    -- extra (implicit) assumption beyond the paper: measurability of the sample
    -- alignment-error events (needed to pass from events to convergence in probability)
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
    -- Conclusion: the finite-sample alignment error → 0 in probability.
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
    -- extra (implicit) assumption beyond the paper: measurability of the sample
    -- alignment-error events (needed to pass from events to convergence in probability)
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
    -- Conclusion: the estimator ψhat satisfies Helm's alignment consistency (paper Eq. (3)).
    DKPSAlignmentConsistency n d d' P ψhat := by
  refine ⟨fun _u => AffineIsometryEquiv.refl Real (E d), ?_⟩
  simpa using
    sample_alignment_convergesInProbabilityToZero_of_highProb_configError
      (Measure.pi (fun _ : Fin (n + 1) => P))
      ψhat rate hgood_meas hrate hconfig

/--
**Helm alignment consistency from the aligned CMDS spectral estimator — assumptions made explicit.**

Derives Helm's `DKPSAlignmentConsistency` (paper Eq. (3)) for the aligned
classical-MDS spectral estimator from two *decomposed* inputs, in place of the
former opaque `halign` primitive:

* `hgood` — a high-probability event bundling
  (i) the paper's **estimation closeness** (the sample CMDS matrix is entrywise
      `rate u`-close to the per-`ω` population CMDS matrix — the content of the
      Acharyya consistency Helm cites for Eq. (3)), and
  (ii) the **latent eigenvalue stability** `α ≤ λ_i` on the top-`d` block of the
      population CMDS matrix.
* `hpsd`/`hrank`/`hcap`/`hgram` — structural facts about the population CMDS
  matrix (PSD, rank `≤ d`, eigenvalue cap `Λ`, and the Gram realization by the
  true latents `(ω ·).1`).  These are automatic for the distance matrix of a
  centred `d`-dimensional configuration; `hgram` additionally encodes that the
  latents are centred (`classicalMDSMatrix` of a distance matrix is the *centred*
  Gram), and `hpsd` itself follows from `hgram` (Gram matrices are PSD).

**ASSUMPTION SURFACED BY THE FORMALIZATION (not stated in Helm).**  Conjunct (ii)
— the latent eigenvalue stability `α ≤ λ_d` — is **Acharyya 2025's Assumption 2**;
it is *not* among Helm's stated assumptions (A1–A4 constrain only the learning
rule and loss).  It is required because this bridge realizes the DKPS estimator
as the **classical / spectral** MDS embedding (`alignedSpectralConfig`,
Davis–Kahan), whose finite-sample stability genuinely needs an eigengap.  Helm's
own argument avoids it by citing the *asymptotic raw-stress* consistency
(Acharyya 2024), which is eigengap-free; a raw-stress variant of this bridge
would instead surface the milder identifiability condition `UniquePairProfile`.
The theory/practice MDS-variant discrepancy this exposes is exactly the kind of
hidden assumption a formalization is meant to surface.

So `halign` is no longer assumed — it is *derived* from `hgood` via the
deterministic `alignExists_of_entrywiseClose`, with the eigenvalue-stability
assumption now explicit and named.

Formalized by Claude Fable 5 (claude-fable-5[1m]); `halign` discharged to the
explicit eigenvalue-stability assumption by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem alignmentConsistency_of_aligned_spectral
    {n d d' : Nat} (hd : d ≤ n + 1)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (Dhat : Nat → (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    -- The per-ω population dissimilarity matrix (of the true latents `(ω ·).1`):
    (Dpop : (Sample n d d') → Acharyya2024.DisMat (n + 1))
    {α Λ : Real} (hα_pos : 0 < α)
    -- Structural facts about the population CMDS matrix (automatic for the distance
    -- matrix of a centred `d`-dim config; `hpsd` also follows from `hgram`):
    (hpsd : ∀ ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω))).PosSemidef)
    (hrank : ∀ ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω))).rank ≤ d)
    (hcap : ∀ ω l,
        Acharyya2025.MatrixPerturbation.sortedEigenvalues (hpsd ω).isHermitian l ≤ Λ)
    -- Gram realization (also encodes centring of the latents):
    (hgram : ∀ ω i j, (∑ k, (ω i).1 k * (ω j).1 k)
        = Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j)
    -- Vanishing perturbation rate.  The local spectral smallness conditions are
    -- derived automatically on a sufficiently large tail.
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Tendsto (fun u => ((n + 1 : ℕ) : ℝ) * rate u) atTop (𝓝 0))
    -- measurability of the alignment-error events (implicit, beyond the paper):
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1),
              dist
                (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                  (fun i : Fin (n + 1) => (ω i).1)
                  (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                    (((n + 1 : ℕ) : ℝ) * rate u)) u ω i)
                ((ω i).1))|
            ≤ Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                (((n + 1 : ℕ) : ℝ) * rate u)})
    -- ★ Estimation closeness (paper's Acharyya consistency) AND the surfaced latent
    -- eigenvalue-stability (Acharyya 2025 Assumption 2, NOT among Helm's assumptions):
    (hgood :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.Bridge.EntrywiseClose
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω)) (rate u)
            ∧ (∀ i : Fin (n + 1), (i : ℕ) < d →
                α ≤ Acharyya2025.MatrixPerturbation.sortedEigenvalues (hpsd ω).isHermitian i)})) :
    -- Conclusion: Helm's alignment consistency (Eq. (3)) — now *derived*, with the
    -- eigenvalue-stability assumption explicit (see docstring).
    DKPSAlignmentConsistency n d d' P
      (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
        (fun i : Fin (n + 1) => (ω i).1)
        (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
          (((n + 1 : ℕ) : ℝ) * rate u)) u ω) := by
  -- Derive the alignment-existence HP event from `hgood` via the deterministic capstone.
  have hside := Acharyya2025.AlignedPipeline.eventually_spectral_side_conditions
    (n := n + 1) (d := d) hα_pos hrate_zero
  have halign :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym
              (fun i : Fin (n + 1) => (ω i).1)
              (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                (((n + 1 : ℕ) : ℝ) * rate u)) u ω}) := by
    refine HighProbAtTop.mono_eventually hgood ?_
    filter_upwards [hside] with u hu
    intro ω hω
    obtain ⟨hclose, hfloor⟩ := hω
    exact Acharyya2025.AlignedPipeline.alignExists_of_entrywiseClose
      hd Dhat (Dpop ω) hsym (hpsd ω) (hrank ω) hα_pos hfloor (fun l => hcap ω l)
      (fun i : Fin (n + 1) => (ω i).1) (hgram ω) rate u (hrate_nonneg u)
      hu.1 hu.2 ω hclose
  -- Transport to the ConfigError HP event, then apply the identity-alignment bridge.
  have hconfig :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            ConfigError
              (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                (fun i : Fin (n + 1) => (ω i).1)
                (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                  (((n + 1 : ℕ) : ℝ) * rate u)) u ω)
              (fun i : Fin (n + 1) => (ω i).1)
              ≤ Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                  (((n + 1 : ℕ) : ℝ) * rate u)}) := by
    refine HighProbAtTop.mono halign (fun u ω hω => ?_)
    exact Acharyya2025.AlignedPipeline.configError_alignedSpectralConfig_le
      hd Dhat hsym (fun i : Fin (n + 1) => (ω i).1)
      (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
        (((n + 1 : ℕ) : ℝ) * rate u)) u ω hω
  have hrate_c :
      Tendsto (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
        (((n + 1 : ℕ) : ℝ) * rate u)) atTop (𝓝 0) :=
    Acharyya2025.RateChain.tendsto_configBound_comp_zero (n + 1) d α Λ hrate_zero
  exact alignmentConsistency_of_highProb_configError P
    (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
      (fun i : Fin (n + 1) => (ω i).1)
      (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
        (((n + 1 : ℕ) : ℝ) * rate u)) u ω)
    (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
      (((n + 1 : ℕ) : ℝ) * rate u))
    hgood_meas hrate_c hconfig

end Helm2025.DKPS.AcharyyaBridge
