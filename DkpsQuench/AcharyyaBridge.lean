/-
Deterministic bridges from finite Acharyya DKPS concentration statements to the
Quench query-efficiency concentration hypothesis.

Quench's theorem is stated over an abstract model space and assumes a uniform
embedding-error event over all models.  Acharyya's DKPS concentration theorems
are finite-configuration statements.  The bridge therefore explicitly assumes a
factorization of the Quench embedding maps through a finite Acharyya
configuration.
-/

import Acharyya2025.AlignedPipeline
import Acharyya2025.RateChain
import DkpsQuench.Basic

open scoped BigOperators Topology
open Filter MeasureTheory

namespace DkpsQuench.AcharyyaBridge

open Acharyya2024

universe u v

variable {Q : Type u}
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type} [MeasurableSpace Ω]

/--
Finite Acharyya configuration concentration gives Quench's uniform model-space
embedding concentration when the true and estimated Quench embeddings factor
through the finite configuration by an index map.

The factorization hypothesis is essential: without it, a bound over `Fin n`
cannot imply a bound over an arbitrary model type.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem quench_uniform_embedding_error_of_finite_configError
    (μ : Nat → Measure Ω)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {n d : Nat}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Config n d)
    (ψhatFinite : Nat → Ω → Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (c : Nat → Real)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f = ψhatFinite u ω (indexOf f))
    (hfinite :
      Acharyya2024.HighProbAtTop μ
        (fun u => {ω | ConfigError (ψhatFinite u ω) ψFinite ≤ c u})) :
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤ c u}) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hfinite δ hδ
  refine ⟨N, fun u hu => ?_⟩
  exact (hN u hu).trans (MeasureTheory.measure_mono fun ω hω f => by
    calc
      ‖ψHat u ω f - ψ f‖
          = ‖ψhatFinite u ω (indexOf f) - ψFinite (indexOf f)‖ := by
            simp [hψ f, hψHat u ω f]
      _ ≤ ConfigError (ψhatFinite u ω) ψFinite :=
            norm_config_le_ConfigError (ψhatFinite u ω) ψFinite (indexOf f)
      _ ≤ c u := hω)

/--
**Quench uniform embedding error from the aligned CMDS spectral estimator.**

A thin, honest composition: the matrix-world spectral capstone (via
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`)
produces a high-probability bound on `ConfigError (alignedSpectralConfig …) ψ`,
and the existing generic
`quench_uniform_embedding_error_of_finite_configError` lifts it to Quench's
uniform model-space embedding-error event, provided the Quench embedding maps
factor through the finite Acharyya configuration by an index map.

What is composed end-to-end: the entrywise CMDS-closeness HP event `hcenter` is
fed through the proved capstone to produce the aligned-`ConfigError` HP event,
which is then transported by the index-map factorization.  What is hypothesized:
the factorization data (`indexOf`, `hψ`, `hψHat`), the spectral hypotheses of the
capstone (PSD/rank/floor/cap/smallness/polar), the Gram realization of `ψ`, and
the entrywise-closeness HP event `hcenter`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem quench_uniform_embedding_error_of_aligned_spectral
    (μ : Nat → Measure Ω)
    (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n) (D : Acharyya2024.DisMat n)
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ Acharyya2025.MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l, Acharyya2025.MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hsmall : ∀ u, (n : Real) * rate u ≤ α / 2)
    (hpolar : ∀ u, (d : Real) *
      (4 * (n : Real) * ((n : Real) * rate u)^2 / α^2) ≤ 1/2)
    (hcenter : Acharyya2024.HighProbAtTop μ (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate u)}))
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) u ω (indexOf f)) :
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤
        Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)}) := by
  -- Capstone composition: produce the aligned-`ConfigError` HP event.
  have haligned :=
    Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close
      μ hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite
      rate hrate_nonneg hsmall hpolar hcenter
  -- Lift through the index-map factorization with the existing generic theorem.
  exact quench_uniform_embedding_error_of_finite_configError
    μ hμ indexOf ψFinite
    (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)))
    ψ ψHat
    (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * rate u))
    hψ hψHat haligned

/--
**Query efficiency from the spectral concentration chain (Theorem 2 Part 2,
`h_conc` discharged).**

This is `DkpsQuench.Theorem2_part2_paper` with the abstract uniform
embedding-error event `h_conc` (and the rate side-conditions `h_c_tendsto`,
`h_c_nonneg`) no longer *assumed* but *derived* from the actual statistical /
spectral inputs, via `quench_uniform_embedding_error_of_aligned_spectral` and
the `RateChain` vanishing-rate lemmas.  In other words: the concentration
hypothesis is replaced by the prose assumptions that produce it (population PSD
/ rank / spectral-floor / cap structure, the entrywise CMDS-closeness
high-probability event `hcenter`, the Gram realization of `ψ`, the index-map
factorization, and the vanishing rate `(n)·rate u → 0`).

**Measurability seam discharged (no measurable selection).**  The former
`h_conc_meas` hypothesis (measurability of the embedding-error event of the
`Classical.choose`-based aligned estimator) is gone.  The route: the aligned
estimator's error event *equals* the choice-free alignment existential
(`configError_alignedSpectralConfig_le_iff_alignExists` — a raw embedding
satisfying the bound witnesses the existential with `W = id`), and the
existential over the **compact** set of inner-product-preserving maps is
measurable by `ForMathlib.measurableSet_exists_mem_le` (countable dense
approximation; no selection of the optimal alignment).  This measurable
high-probability event is contained in the embedding-error event, which is
exactly what the sub-event form `Theorem2_part2_paper_subevent` consumes.

The one remaining measurability primitive is `hmeas_spec`: the **raw**
(unaligned) spectral embedding `ω ↦ spectralConfig …(Dhat k ω)…` is measurable.
This is a genuine Borel-measurability question about the fixed eigendecomposition
map (no `ω`-dependent choice), recorded in `planning/for-fable.md` F5.  The
model-coverage assumptions `h_cover`/`h_cover_meas` (paper Assumption 2) and the
score Lipschitz / MSE-positivity assumptions remain, as they should.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); measurability seam
discharged by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem Theorem2_part2_of_aligned_spectral
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n) (D : Acharyya2024.DisMat n)
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ Acharyya2025.MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l, Acharyya2025.MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hsmall : ∀ u, (n : Real) * rate u ≤ α / 2)
    (hpolar : ∀ u, (d : Real) *
      (4 * (n : Real) * ((n : Real) * rate u)^2 / α^2) ≤ 1/2)
    (hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (hcenter : Acharyya2024.HighProbAtTop μ (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate u)}))
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) u ω (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (hm : Qsub.card < Qstar.card)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    -- Honest measurability primitive: the RAW spectral embedding is measurable
    -- in the sample; no measurability of the chosen alignment is needed.
    (hmeas_spec : ∀ (k : Nat) (i : Fin n), Measurable (fun ω =>
      Acharyya2025.ConfigPerturbation.spectralConfig
        (Matrix.toEuclideanLin (Acharyya2025.MathlibBridge.disMatToMatrix
          (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))))
        (Acharyya2025.MatrixPerturbation.opSym (hsym k ω)) hd i))
    -- Genuine model-coverage assumption (paper Assumption 2):
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- The measurable high-probability sub-event: the choice-free alignment
  -- existential at the `configBound` level.
  have hE_meas : ∀ k, MeasurableSet {ω |
      Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) k ω} := fun k =>
    Acharyya2025.AlignedPipeline.measurableSet_setOf_alignExists hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)) k (hmeas_spec k)
  -- The sub-event is contained in the uniform embedding-error event.
  have hE_sub : ∀ k, {ω |
      Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) k ω}
      ⊆ {ω | ∀ f, ‖ψHat k ω f - ψ f‖
          ≤ Acharyya2025.ConfigPerturbation.configBound n d α Λ
              ((n : Real) * rate k)} := by
    intro k ω hA f
    have hcfg := Acharyya2025.AlignedPipeline.configError_alignedSpectralConfig_le
      hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)) k ω hA
    calc ‖ψHat k ω f - ψ f‖
        = ‖Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
            (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
              ((n : Real) * rate u)) k ω (indexOf f) - ψFinite (indexOf f)‖ := by
          rw [hψHat, hψ]
      _ ≤ ConfigError
            (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
              (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
                ((n : Real) * rate u)) k ω) ψFinite :=
          norm_config_le_ConfigError _ _ _
      _ ≤ _ := hcfg
  -- The sub-event is high-probability: it *equals* the aligned-estimator error
  -- event (the choice-elimination iff), which the spectral chain controls.
  have hE : _root_.HighProbAtTop μ hμ (fun k => {ω |
      Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) k ω}) := by
    have haligned :=
      Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close
        μ hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite
        rate hrate_nonneg hsmall hpolar hcenter
    intro δ hδ
    obtain ⟨N, hN⟩ := haligned δ hδ
    refine ⟨N, fun k hk => ?_⟩
    have hset : {ω | ConfigError
          (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
            (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
              ((n : Real) * rate u)) k ω) ψFinite
          ≤ Acharyya2025.ConfigPerturbation.configBound n d α Λ ((n : Real) * rate k)}
        = {ω | Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite
            (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
              ((n : Real) * rate u)) k ω} := by
      ext ω
      exact Acharyya2025.AlignedPipeline.configError_alignedSpectralConfig_le_iff_alignExists
        hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) k ω
    show (μ k) {ω | Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)) k ω} ≥ 1 - δ
    rw [← hset]
    exact hN k hk
  -- Discharge the rate side-conditions from `RateChain`.
  have h_c_tendsto :
      Filter.Tendsto
        (fun k => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate k)) Filter.atTop (nhds 0) :=
    Acharyya2025.RateChain.tendsto_configBound_comp_zero n d α Λ hrate_zero
  have h_c_nonneg : ∀ k, 0 ≤ Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * rate k) := by
    intro k
    unfold Acharyya2025.ConfigPerturbation.configBound
    positivity
  -- Feed into the sub-event paper theorem (everything else genuine).
  exact Theorem2_part2_paper_subevent (Q := Q) (X := X) (d := d) Pf μ hμ
    (fun _ f => ψ f) (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub
    hm γ h_lipQ h_gamma_pos _ h_c_tendsto h_c_nonneg
    (fun k => {ω | Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)) k ω})
    hE_meas hE_sub hE
    h_cover h_cover_meas hMSE_Q_pos

end DkpsQuench.AcharyyaBridge
