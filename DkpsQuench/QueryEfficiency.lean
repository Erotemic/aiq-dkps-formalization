/-
Paper-shaped Quench query-efficiency capstones.

This module exposes the eventual high-probability conclusion already present in
the abstract MSE engine, uses the paper's tie-averaged nearest-neighbor
estimator, derives reference coverage from compactness/full support/iid
sampling, and packages the fixed-subset result into the paper's `m`-query and
all-strict-budgets predicates.
-/
import DkpsQuench.Theorem2
import DkpsQuench.Coverage

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

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Tie-averaged nearest-neighbor regression for a generic estimated
perspective map.  The zero-reference stage is assigned value zero; all eventual
results operate after positive sample sizes. -/
noncomputable def tieAverageNN
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → ℝ)
    (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ := by
  by_cases hn : n > 0
  · exact hNNTieAverage hn
      (fun i => ψHat n ω (f_ref n ω i))
      (ψHat n ω f)
      (fun i => y (f_ref n ω i))
  · exact 0

@[simp] lemma tieAverageNN_of_pos
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → ℝ)
    (n : ℕ) (ω : Ω) (f : Model Q X) (hn : n > 0) :
    tieAverageNN ψHat f_ref y n ω f =
      hNNTieAverage hn
        (fun i => ψHat n ω (f_ref n ω i))
        (ψHat n ω f)
        (fun i => y (f_ref n ω i)) := by
  simp [tieAverageNN, hn]

/-- Literal paper estimator: average the full benchmark scores of every
reference model tied for nearest neighbor in the estimated `Qsub` perspective. -/
noncomputable def yNNTieAverage_paper
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ :=
  tieAverageNN (fun u ω' g => ψHat u ω' Qsub g)
    f_ref (fun g => score g Qstar) n ω f

/-- Any estimator whose MSE tends to zero with high probability is eventually
no worse than a fixed baseline with positive MSE. -/
theorem highProbQQueryEfficient_of_mse_atTop
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (y baseline : Model Q X → ℝ)
    (h : ℕ → Ω → Model Q X → ℝ)
    (hmse : ∀ ε : ℝ, 0 < ε →
      HighProbAtTop μ hμ (fun n => {ω | MSE Pf y (h n ω) ≤ ε}))
    (hbase : 0 < MSE Pf y baseline) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss y
      h (fun _ _ => baseline) := by
  unfold HighProbQQueryEfficient
  change HighProbAtTop μ hμ (fun n => {ω |
    MSE Pf y (h n ω) ≤ MSE Pf y baseline})
  exact hmse (MSE Pf y baseline) hbase

/-- Tie-averaged nearest-neighbor MSE converges to zero from a measurable
high-probability embedding-error subevent and a measurable high-probability
coverage subevent certificate. -/
theorem highProb_mse_tieAverage_of_subevents
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → ℝ)
    (γ : ℝ)
    (h_lip : ∀ f f', |y f - y f'| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (c : ℕ → ℝ) (hc_zero : Tendsto c atTop (nhds 0))
    (hc_nonneg : ∀ n, 0 ≤ c n)
    (E : ℕ → Set Ω)
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE_sub : ∀ n, E n ⊆ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
    (hE : HighProbAtTop μ hμ E)
    (C : CoverageSubevents μ hμ ψ f_ref) :
    ∀ ε : ℝ, 0 < ε →
      HighProbAtTop μ hμ (fun n => {ω |
        MSE Pf y (fun f => tieAverageNN ψHat f_ref y n ω f) ≤ ε}) := by
  intro ε hε
  let ρ : ℝ := Real.sqrt ε / (2 * γ)
  let cmax : ℝ := Real.sqrt ε / (8 * γ)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hcmax : 0 < cmax := by
    dsimp [cmax]
    positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc_zero cmax hcmax
  have hinter : HighProbAtTop μ hμ
      (fun n => E n ∩ C.event ρ n) :=
    HighProbAtTop.inter hE (C.highProb ρ hρ)
      hE_meas (C.measurable ρ hρ)
  refine hinter.mono_eventually ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨N + 1, fun n hn => hn⟩] with n hn
  intro ω hω
  have hnpos : n > 0 := by omega
  have hc_lt : |c n| < cmax := by
    exact hN n (by omega)
  have hc_le : c n ≤ cmax :=
    (le_abs_self (c n)).trans (le_of_lt hc_lt)
  apply mse_le_of_pointwise_sq_error_le Pf y
    (fun f => tieAverageNN ψHat f_ref y n ω f) ε hε.le
  intro f
  have hconc := hE_sub n hω.1
  have hcover := C.subset ρ hρ n hω.2
  have herr :
      |tieAverageNN ψHat f_ref y n ω f - y f| ≤
        γ * (ρ + 4 * c n) := by
    rw [tieAverageNN_of_pos ψHat f_ref y n ω f hnpos]
    exact step5_tieAverage_pointwise_error hnpos
      (fun i => ψ (f_ref n ω i))
      (fun i => ψHat n ω (f_ref n ω i))
      (ψ f) (ψHat n ω f) (c n) ρ γ
      (fun i => hconc (f_ref n ω i)) (hconc f)
      (hcover f)
      (fun i => y (f_ref n ω i)) (y f)
      (fun i => h_lip (f_ref n ω i) f)
      hγ.le hρ.le (hc_nonneg n)
  have herr_sq :
      (tieAverageNN ψHat f_ref y n ω f - y f) ^ 2 ≤
        (γ * (ρ + 4 * c n)) ^ 2 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _ ) herr 2
  have hparam : (γ * (ρ + 4 * c n)) ^ 2 ≤ ε := by
    simpa [ρ, cmax] using
      (step6_parameter_choice ε γ hε hγ (c n) (hc_nonneg n) hc_le)
  exact herr_sq.trans hparam

/-- Fixed-subset, eventual high-probability query efficiency for the literal
tie-averaged estimator, from explicit concentration and coverage subevents. -/
theorem highProbQQueryEfficient_tieAverage_of_subevents
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (c : ℕ → ℝ) (hc_zero : Tendsto c atTop (nhds 0))
    (hc_nonneg : ∀ n, 0 ≤ c n)
    (E : ℕ → Set Ω)
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE_sub : ∀ n, E n ⊆ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
    (hE : HighProbAtTop μ hμ E)
    (C : CoverageSubevents μ hμ ψ f_ref)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => tieAverageNN ψHat f_ref (yFull score Qstar) n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  apply highProbQQueryEfficient_of_mse_atTop Pf μ hμ
    (yFull score Qstar) (yQ score Qsub)
    (fun n ω f => tieAverageNN ψHat f_ref (yFull score Qstar) n ω f)
  · exact highProb_mse_tieAverage_of_subevents Pf μ hμ ψ ψHat f_ref
      (yFull score Qstar) γ h_lip hγ c hc_zero hc_nonneg
      E hE_meas hE_sub hE C
  · exact hbase

/-- Compact perspective image, positive mass in every perspective ball, and an
explicit iid reference sampler discharge the paper's abstract coverage
assumption in the fixed-subset query-efficiency theorem. -/
theorem highProbQQueryEfficient_tieAverage_of_compact_iid_fullSupport
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (c : ℕ → ℝ) (hc_zero : Tendsto c atTop (nhds 0))
    (hc_nonneg : ∀ n, 0 ≤ c n)
    (E : ℕ → Set Ω)
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE_sub : ∀ n, E n ⊆ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
    (hE : HighProbAtTop μ hμ E)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => tieAverageNN ψHat f_ref (yFull score Qstar) n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  let C := coverageSubevents_of_compact_iid_fullSupport
    Pf μ hμ ψ hψ hcompact hfull f_ref hiid
  exact highProbQQueryEfficient_tieAverage_of_subevents Pf μ hμ ψ ψHat
    f_ref score Qstar Qsub γ h_lip hγ c hc_zero hc_nonneg
    E hE_meas hE_sub hE C hbase

/-- All assumptions that vary with a query subset, packaged for finite-subset
quantification.  The common model law, reference sampler, score, and full
benchmark are supplied outside this structure. -/
structure QuerySubsetCertificate
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q) where
  gamma : ℝ
  gamma_pos : 0 < gamma
  lipschitz : ∀ f f',
    |score f Qstar - score f' Qstar| ≤
      gamma * ‖ψ Qsub f - ψ Qsub f'‖
  rate : ℕ → ℝ
  rate_zero : Tendsto rate atTop (nhds 0)
  rate_nonneg : ∀ n, 0 ≤ rate n
  event : ℕ → Set Ω
  event_measurable : ∀ n, MeasurableSet (event n)
  event_subset : ∀ n, event n ⊆ {ω | ∀ f,
    ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ rate n}
  event_highProb : HighProbAtTop μ hμ event
  perspective_measurable : Measurable (ψ Qsub)
  compact_perspective_range : IsCompact (Set.range (ψ Qsub))
  full_support : PerspectiveFullSupport Pf (ψ Qsub)
  baseline_pos : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)

/-- A subset certificate produces the paper-shaped eventual theorem for that
subset. -/
theorem QuerySubsetCertificate.highProbQQueryEfficient
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (H : QuerySubsetCertificate Pf μ hμ ψ ψHat f_ref score Qstar Qsub) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_paper ψHat f_ref score Qstar Qsub n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  change HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
    (yFull score Qstar)
    (fun n ω f => tieAverageNN (fun u ω' g => ψHat u ω' Qsub g)
      f_ref (yFull score Qstar) n ω f)
    (fun _ _ f => yQ score Qsub f)
  exact highProbQQueryEfficient_tieAverage_of_compact_iid_fullSupport
    Pf μ hμ (ψ Qsub) H.perspective_measurable
    H.compact_perspective_range H.full_support
    (fun n ω f => ψHat n ω Qsub f) f_ref hiid score Qstar Qsub
    H.gamma H.lipschitz H.gamma_pos H.rate H.rate_zero H.rate_nonneg
    H.event H.event_measurable H.event_subset H.event_highProb H.baseline_pos

/-- If every size-`m` subset has a certificate, the literal tie-averaged
estimator is high-probability `m`-query-efficient. -/
theorem highProbMQueryEfficient_tieAverage_of_certificates
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar : Finset Q) (m : ℕ)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card = m →
      QuerySubsetCertificate Pf μ hμ ψ ψHat f_ref score Qstar Qsub) :
    HighProbMQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss Qstar m
      (yFull score Qstar)
      (fun Qsub n ω f =>
        yNNTieAverage_paper ψHat f_ref score Qstar Qsub n ω f)
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro Qsub hsubset hcard
  exact QuerySubsetCertificate.highProbQQueryEfficient
    Pf μ hμ ψ ψHat f_ref hiid score Qstar Qsub
      (H Qsub hsubset hcard)

/-- Certificates for every strict subset budget yield the paper's complete
all-`m < M` high-probability query-efficiency conclusion. -/
theorem highProbQueryEfficientBelow_tieAverage_of_certificates
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar : Finset Q) (M : ℕ)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < M →
      QuerySubsetCertificate Pf μ hμ ψ ψHat f_ref score Qstar Qsub) :
    HighProbQueryEfficientBelow (Q := Q) (X := X) μ hμ Pf sqLoss Qstar M
      (yFull score Qstar)
      (fun Qsub n ω f =>
        yNNTieAverage_paper ψHat f_ref score Qstar Qsub n ω f)
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro m hm Qsub hsubset hcard
  apply QuerySubsetCertificate.highProbQQueryEfficient Pf μ hμ ψ ψHat
    f_ref hiid score Qstar Qsub
  exact H Qsub hsubset (by simpa [hcard] using hm)

/-- Certificates for every proper subset of `Qstar` yield the complete
paper-facing high-probability query-efficiency predicate. -/
theorem highProbQueryEfficient_tieAverage_of_certificates
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar : Finset Q)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      QuerySubsetCertificate Pf μ hμ ψ ψHat f_ref score Qstar Qsub) :
    HighProbQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss Qstar
      (yFull score Qstar)
      (fun Qsub n ω f =>
        yNNTieAverage_paper ψHat f_ref score Qstar Qsub n ω f)
      (fun Qsub _ _ f => yQ score Qsub f) := by
  exact highProbQueryEfficientBelow_tieAverage_of_certificates
    Pf μ hμ ψ ψHat f_ref hiid score Qstar Qstar.card H
