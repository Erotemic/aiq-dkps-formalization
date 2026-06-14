/-
DKPS / Quench, Theorem 2 (query efficiency) — paper-facing statements.

This file follows the prose of Helm–Johnson–Priebe, "Query-efficient model
evaluation using cached responses" (arXiv:2605.07096), Theorem 2.  It states the
paper's nearest-neighbor estimator `ŷ_NN` (`yNN_paper`) and its query-efficiency
relative to the subset baseline `ŷ_Q` (`yQ`), wrapping the abstract engine in
`DkpsQuench.Internal`.

* `highProb_mse_nn_le` — `MSE(ŷ_NN) ≤ ε` with high probability (Part 1);
* `highProb_queryEfficient_nn` — query efficiency relative to `ŷ_Q` (Part 2);
* `highProb_mse_nn_le_of_subevent` / `highProb_queryEfficient_nn_of_subevent` — the same
  from a measurable high-probability sub-event of the embedding-error event.

The concentration event is *assumed* here; it is discharged from the Acharyya2025
spectral chain in `DkpsQuench.AcharyyaBridge`.
-/
import DkpsQuench.Internal
import Mathlib
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

universe u v

section Paper_Theorem2_Literal

open Filter MeasureTheory

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type} [MeasurableSpace Ω]

/-- Full-score target `y(f) := y(f, Q⋆)` from the paper. -/
def yFull (score : Model Q X → Finset Q → ℝ) (Qstar : Finset Q) : Model Q X → ℝ :=
  fun f => score f Qstar

/-- Subset-score baseline `ŷ_Q(f) := y(f, Q)` from the paper. -/
def yQ (score : Model Q X → Finset Q → ℝ) (Qsub : Finset Q) : Model Q X → ℝ :=
  fun f => score f Qsub

/--
Paper NN estimator `ŷ_NN` for a fixed query subset `Qsub ⊆ Q⋆`.

- NN is computed in *estimated perspective space* induced by `Qsub` (via `ψHat`).
- Prediction is the *full score* on `Q⋆` of the nearest reference model, as in the proof text.
-/
noncomputable def yNN_paper
  (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (score : Model Q X → Finset Q → ℝ)
  (Qstar Qsub : Finset Q)
  (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ :=
by
  by_cases hn : n > 0
  · -- NN index in estimated perspective space for this `Qsub`
    let ψHat_ref : Fin n → Vec d := fun i => ψHat n ω Qsub (f_ref n ω i)
    let ψHat_tgt : Vec d := ψHat n ω Qsub f
    let iStar : Fin n := nnIndex (d := d) hn ψHat_ref ψHat_tgt
    exact score (f_ref n ω iStar) Qstar
  · exact 0

/--
**Theorem 2 (Part 1), literal paper form.**

Paper text: “For any ε > 0 there exists (n,m,r) such that MSE(ŷ_NN) ≤ ε with high probability.”
We encode “with high probability” as: ∀ δ>0, ∃ n, P( MSE ≤ ε ) ≥ 1-δ.

Here `m := Qsub.card`. The `r` dependence lives inside the concentration hypothesis (`h_conc` / `c n`).

ASSUMPTION DISCLOSURE.  The embedding-concentration event `h_conc` (the paper's
Theorem 1 content) and its rate `c n` are *assumed here, not derived* — together
with the coverage event `h_cover` (Assumption 2) and their measurability.  For
the version that DISCHARGES `h_conc`/`h_conc_meas` from the actual spectral
concentration chain, see
`DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_aligned_spectral`; for the variant
that only needs a measurable high-probability sub-event of the error event, see
`highProb_mse_nn_le_of_subevent`.
-/
theorem highProb_mse_nn_le
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (ψ : Finset Q → Model Q X → Vec d)
  (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (score : Model Q X → Finset Q → ℝ)
  (Qstar Qsub : Finset Q)
  -- Lipschitz only needs to hold for this fixed `Qsub` (paper Assumption 1, after “Fix Q ⊆ Q⋆”)
  (γ : ℝ)
  (h_lipQ : ∀ (f f' : Model Q X),
    |score f Qstar - score f' Qstar| ≤ γ * ‖ψ Qsub f - ψ Qsub f'‖)
  (h_gamma_pos : 0 < γ)
  (c : ℕ → ℝ) (h_c_tendsto : Tendsto c atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  -- concentration & cover specialized to this `Qsub` (paper Theorem 1 + Assumption 2)
  (h_conc :
    HighProbAtTop μ hμ (fun n => {ω | ∀ f, ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ c n}))
  (h_conc_meas :
    ∀ n, MeasurableSet {ω | ∀ f, ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ c n})
  (h_cover :
    ∀ ρ > 0,
      HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ}))
  (h_cover_meas :
    ∀ ρ > 0, ∀ n,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ}) :
  -- Conclusion: for every target ε > 0 and confidence δ > 0, some sample size `n` makes
  -- P( MSE(ŷ_NN) ≤ ε ) ≥ 1 - δ.  (Proof — everything after `:= by` — follows.)
  ∀ ε : ℝ, 0 < ε → ∀ δ : ENNReal, 0 < δ →
    ∃ n : ℕ,
      (μ n) {ω |
        MSE (Q := Q) (X := X) Pf
          (yFull score Qstar)
          (fun f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f)
        ≤ ε} ≥ 1 - δ := by
  intro ε hε δ hδ

  -- Package the fixed-Qsub Lipschitz hypothesis into `LipschitzScore` expected by `highProb_mse_le_of_concentration`.
  have h_lip_const :
      LipschitzScore (Q := Q) (X := X) (d := d) γ
        (fun (_ : Finset Q) (f : Model Q X) => ψ Qsub f)
        (fun f => score f Qstar) := by
    intro _ f f'
    simpa using h_lipQ f f'

  -- Define `hNN` to match the general theorem interface.
  let hNN : ℕ → Ω → Model Q X → ℝ :=
    fun n ω f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f

  have h_hNN_def :
      ∀ n ω f, (hn : n > 0) →
        hNN n ω f =
          hNN_estimator (d := d) hn
            (fun i => ψHat n ω Qsub (f_ref n ω i))
            (ψHat n ω Qsub f)
            (fun i => score (f_ref n ω i) Qstar) := by
    intro n ω f hn
    -- expand the definition and simplify the `by_cases hn : n>0`.
    simp [hNN, yNN_paper, hn, hNN_estimator, nnIndex]

  -- Apply your already-proved asymptotic theorem (stronger than paper), then pick one large `n`.
  have hp_atTop :=
    highProb_mse_le_of_concentration (Q := Q) (X := X) (d := d) (Ω := Ω)
      (Pf := Pf) (μ := μ) (hμ := hμ)
      (ψ := fun f => ψ Qsub f)
      (ψHat := fun n ω f => ψHat n ω Qsub f)
      (f_ref := f_ref)
      (score := score) (Qstar := Qstar)
      (γ := γ) (h_lip := h_lip_const) (h_gamma_pos := h_gamma_pos)
      (c := c) (h_c_tendsto := h_c_tendsto) (h_c_nonneg := h_c_nonneg)
      (h_conc := h_conc) (h_conc_meas := h_conc_meas)
      (h_cover := h_cover) (h_cover_meas := h_cover_meas)
      (hNN := hNN) (h_hNN_def := h_hNN_def)
      ε hε

  obtain ⟨N, hN⟩ := hp_atTop δ hδ
  refine ⟨N+1, ?_⟩
  exact hN (N+1) (Nat.lt_succ_self N)

/--
**Theorem 2 (Part 2), literal paper form.**

Paper text: “for m < M such that MSE(ŷ_Q) > 0, ŷ_NN is query-efficient relative to ŷ_Q with high probability.”

We formalize the “query-efficient relative to ŷ_Q” conclusion as:
∀ δ>0, ∃ n, P( MSE(ŷ_NN) ≤ MSE(ŷ_Q) ) ≥ 1-δ.

Here ŷ_Q(f) := score f Qsub is the baseline.

ASSUMPTION DISCLOSURE.  As in Part 1, the concentration event `h_conc` and rate
`c n` are *assumed*, not derived.  Only `hMSE_Q_pos` (the `MSE(ŷ_Q) > 0`
condition) drives the proof; the paper's `m < M` condition `hm` is recorded for
fidelity but is not used by the formal argument.  This theorem is SUPERSEDED by
`highProb_queryEfficient_nn_of_subevent` (measurable HP sub-event instead of
`h_conc`/`h_conc_meas`) and by
`DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_aligned_spectral` (which discharges
`h_conc` from the spectral chain entirely); prefer those for new work.
-/
theorem highProb_queryEfficient_nn
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (ψ : Finset Q → Model Q X → Vec d)
  (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (score : Model Q X → Finset Q → ℝ)
  (Qstar Qsub : Finset Q)
  (hm : Qsub.card < Qstar.card)   -- paper condition m < M
  (γ : ℝ)
  (h_lipQ : ∀ (f f' : Model Q X),
    |score f Qstar - score f' Qstar| ≤ γ * ‖ψ Qsub f - ψ Qsub f'‖)
  (h_gamma_pos : 0 < γ)
  (c : ℕ → ℝ) (h_c_tendsto : Tendsto c atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  (h_conc :
    HighProbAtTop μ hμ (fun n => {ω | ∀ f, ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ c n}))
  (h_conc_meas :
    ∀ n, MeasurableSet {ω | ∀ f, ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ c n})
  (h_cover :
    ∀ ρ > 0,
      HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ}))
  (h_cover_meas :
    ∀ ρ > 0, ∀ n,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ})
  (hMSE_Q_pos :
    0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar) (yQ score Qsub)) :
  -- Conclusion: with high probability (some sample size `n`), MSE(ŷ_NN) ≤ MSE(ŷ_Q); i.e. the
  -- NN estimator is query-efficient relative to the subset baseline.  (Proof follows `:= by`.)
  ∀ δ : ENNReal, 0 < δ →
    ∃ n : ℕ,
      (μ n) {ω |
        MSE (Q := Q) (X := X) Pf
          (yFull score Qstar)
          (fun f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f)
        ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar) (yQ score Qsub)} ≥ 1 - δ := by
  intro δ hδ

  -- choose ε = (MSE baseline)/2
  let base : ℝ := MSE (Q := Q) (X := X) Pf (yFull score Qstar) (yQ score Qsub)
  have hbase_pos : 0 < base := hMSE_Q_pos
  have hbase_nonneg : 0 ≤ base := le_of_lt hbase_pos
  let ε : ℝ := base / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]; linarith

  -- Apply Part 1 with ε = base/2 to get MSE(NN) ≤ base/2 with high probability.
  obtain ⟨n, hn⟩ :=
    highProb_mse_nn_le (Q := Q) (X := X) (d := d) (Ω := Ω)
      (Pf := Pf) (μ := μ) (hμ := hμ)
      (ψ := ψ) (ψHat := ψHat) (f_ref := f_ref)
      (score := score) (Qstar := Qstar) (Qsub := Qsub)
      (γ := γ) (h_lipQ := h_lipQ) (h_gamma_pos := h_gamma_pos)
      (c := c) (h_c_tendsto := h_c_tendsto) (h_c_nonneg := h_c_nonneg)
      (h_conc := h_conc) (h_conc_meas := h_conc_meas)
      (h_cover := h_cover) (h_cover_meas := h_cover_meas)
      ε hε_pos δ hδ

  refine ⟨n, ?_⟩
  -- Monotone event: {MSE ≤ base/2} ⊆ {MSE ≤ base}
  refine le_trans hn ?_
  apply MeasureTheory.measure_mono
  intro ω hω
  have : MSE (Q := Q) (X := X) Pf
        (yFull score Qstar)
        (fun f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f)
      ≤ base := by
    -- since base/2 ≤ base
    have hε_le : ε ≤ base := by
      dsimp [ε]; linarith [hbase_nonneg]
    exact le_trans hω hε_le
  simpa [base] using this

end Paper_Theorem2_Literal

/-!
## Sub-event variants of Theorem 2

The `h_conc`/`h_conc_meas` pair in the theorems above demands measurability of
the *exact* uniform embedding-error event.  When the estimator `ψHat` involves a
nonconstructive alignment (`Classical.choose`), that event need not be known to
be measurable — but the concentration chain typically produces a *smaller*
measurable high-probability event (e.g. the choice-free alignment existential).
The variants below take such a sub-event `E` instead: `E` measurable,
high-probability, and contained in the embedding-error event.  The originals
are recovered by taking `E` to be the event itself.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

section Theorem2_Subevent

open Filter MeasureTheory

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type} [MeasurableSpace Ω]

/-- `highProb_mse_le_of_concentration` with the concentration event replaced by a measurable
high-probability **sub-event** `E`.  Identical proof; the intersection step uses
`E`, and one extra monotonicity step upgrades membership in `E` to membership in
the embedding-error event via `hE_sub`. -/
theorem highProb_mse_le_of_subevent
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (ψ : Model Q X → Vec d)
  (ψHat : ℕ → Ω → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (score : Model Q X → Finset Q → ℝ)
  (Qstar : Finset Q)
  -- paper Assumption 1 (Lipschitz score): |y(f) - y(f')| ≤ γ·‖ψf - ψf'‖, with γ > 0
  (γ : ℝ)
  (h_lip : LipschitzScore γ (fun _ f => ψ f) (fun f => score f Qstar))
  (h_gamma_pos : 0 < γ)
  -- embedding-error rate `c n → 0` (this is the paper's Theorem 1 content, *assumed* here)
  (c : ℕ → ℝ) (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  -- Measurable high-probability sub-event `E` of the uniform embedding-error event.
  -- `hE_meas` is a Lean-only measurability device (so the argument also works when `ψHat`
  -- is built by a nonconstructive alignment): it is NOT an assumption stated in the paper.
  -- `hE_sub` says `E` lies inside the error event; `hE` says `E` holds with high probability.
  (E : ℕ → Set Ω)
  (hE_meas : ∀ n, MeasurableSet (E n))
  (hE_sub : ∀ n, E n ⊆ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
  (hE : HighProbAtTop μ hμ E)
  -- paper Assumption 2 (reference-model coverage): every model is within ρ of some reference
  -- model, with high probability.  `h_cover_meas` (measurability of that event) is implicit /
  -- beyond the paper.
  (h_cover : ∀ ρ > 0, HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}))
  (h_cover_meas : ∀ ρ > 0, ∀ n, MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ})
  -- the estimator under test (`hNN`), pinned by `h_hNN_def` to the NN rule in estimated space
  (hNN : ℕ → Ω → Model Q X → ℝ)
  (h_hNN_def : ∀ n ω f, (hn : n > 0) → hNN n ω f = hNN_estimator hn (fun i => ψHat n ω (f_ref n ω i)) (ψHat n ω f) (fun i => score (f_ref n ω i) Qstar)) :
  -- Conclusion: for every target ε > 0, with high probability (eventually in n) MSE(ŷ_NN) ≤ ε.
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ (fun n => {ω | MSE Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ ε}) := by
      have h_mse_bound : ∀ ε > 0, ∃ N : ℕ, ∀ n > N, ∀ ω ∈ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n} ∩ {ω | ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ Real.sqrt ε / (2 * γ)}, MSE Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ ε := by
        intro ε hε_pos
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n > N, ∀ ω ∈ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n} ∩ {ω | ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ Real.sqrt ε / (2 * γ)}, ∀ f, |hNN n ω f - score f Qstar| ≤ Real.sqrt ε := by
          obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n > N, ∀ ω ∈ {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n} ∩ {ω | ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ Real.sqrt ε / (2 * γ)}, ∀ f, |hNN n ω f - score f Qstar| ≤ γ * (Real.sqrt ε / (2 * γ) + 4 * c n) := by
            use 1;
            intro n hn ω hω f;
            rw [ h_hNN_def n ω f hn.le ];
            exact step5_pointwise_error n ( fun i => ψ ( f_ref n ω i ) ) ( fun i => ψHat n ω ( f_ref n ω i ) ) ( ψ f ) ( ψHat n ω f ) ( nnIndex ( by linarith ) ( fun i => ψHat n ω ( f_ref n ω i ) ) ( ψHat n ω f ) ) ( nnIndex_isArgmin ( by linarith ) ( fun i => ψHat n ω ( f_ref n ω i ) ) ( ψHat n ω f ) ) ( c n ) ( Real.sqrt ε / ( 2 * γ ) ) γ ( fun i => hω.1 ( f_ref n ω i ) ) ( hω.1 f ) ( by obtain ⟨ i, hi ⟩ := hω.2 f; exact ⟨ i, hi ⟩ ) ( fun i => score ( f_ref n ω i ) Qstar ) ( score f Qstar ) ( fun i => h_lip Qstar ( f_ref n ω i ) f ) h_gamma_pos.le ( by positivity ) ( h_c_nonneg n );
          obtain ⟨ N', hN' ⟩ := Metric.tendsto_atTop.mp h_c_tendsto ( Real.sqrt ε / ( 8 * γ ) ) ( by positivity );
          exact ⟨ Max.max N N', fun n hn ω hω f => le_trans ( hN n ( lt_of_le_of_lt ( le_max_left _ _ ) hn ) ω hω f ) ( by nlinarith [ abs_lt.mp ( hN' n ( le_of_lt ( lt_of_le_of_lt ( le_max_right _ _ ) hn ) ) ), Real.sqrt_nonneg ε, Real.sq_sqrt hε_pos.le, mul_div_cancel₀ ( Real.sqrt ε ) ( by positivity : ( 2 * γ ) ≠ 0 ), mul_div_cancel₀ ( Real.sqrt ε ) ( by positivity : ( 8 * γ ) ≠ 0 ), h_c_nonneg n ] ) ⟩;
        use N;
        intro n hn ω hω
        have h_mse_le : ∫ f, (hNN n ω f - score f Qstar) ^ 2 ∂Pf ≤ ∫ f, (Real.sqrt ε) ^ 2 ∂Pf := by
          refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
          · exact Filter.Eventually.of_forall fun f => sq_nonneg _;
          · norm_num;
          · filter_upwards [ ] with f using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) ( hN n hn ω hω f ) 2;
        have h_eq : MSE Pf (fun f => score f Qstar) (fun f => hNN n ω f)
            = ∫ f, (hNN n ω f - score f Qstar) ^ 2 ∂Pf := by
          simp only [MSE, sqLoss]
        rw [h_eq]
        refine h_mse_le.trans ?_
        simp [Real.sq_sqrt hε_pos.le]
      intro ε hε_pos
      obtain ⟨N, hN⟩ := h_mse_bound ε hε_pos
      have h_inter : HighProbAtTop μ hμ (fun n => E n ∩ {ω | ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ Real.sqrt ε / (2 * γ)}) := by
        apply HighProbAtTop.inter hE (h_cover (Real.sqrt ε / (2 * γ)) (by
        positivity)) (fun n => hE_meas n) (fun n => h_cover_meas (Real.sqrt ε / (2 * γ)) (by
        positivity) n);
      exact h_inter.mono_eventually ( Filter.eventually_atTop.mpr ⟨ N + 1, fun n hn => by intro ω hω; exact hN n ( by linarith ) ω ⟨hE_sub n hω.1, hω.2⟩ ⟩ )

/-- `highProb_mse_nn_le` with a measurable high-probability sub-event in place
of `h_conc`/`h_conc_meas`. -/
theorem highProb_mse_nn_le_of_subevent
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (ψ : Finset Q → Model Q X → Vec d)
  (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (score : Model Q X → Finset Q → ℝ)
  (Qstar Qsub : Finset Q)
  -- paper Assumption 1 (Lipschitz score), specialized to the fixed query subset `Qsub`
  (γ : ℝ)
  (h_lipQ : ∀ (f f' : Model Q X),
    |score f Qstar - score f' Qstar| ≤ γ * ‖ψ Qsub f - ψ Qsub f'‖)
  (h_gamma_pos : 0 < γ)
  -- embedding-error rate `c n → 0` (paper's Theorem 1 content, assumed here)
  (c : ℕ → ℝ) (h_c_tendsto : Tendsto c atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  -- measurable high-probability sub-event `E` of the embedding-error event
  -- (`hE_meas` is a Lean-only measurability device, not an assumption in the paper)
  (E : ℕ → Set Ω)
  (hE_meas : ∀ n, MeasurableSet (E n))
  (hE_sub : ∀ n, E n ⊆ {ω | ∀ f, ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ c n})
  (hE : HighProbAtTop μ hμ E)
  -- paper Assumption 2 (coverage) for this `Qsub`; `h_cover_meas` is implicit / beyond the paper
  (h_cover :
    ∀ ρ > 0,
      HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ}))
  (h_cover_meas :
    ∀ ρ > 0, ∀ n,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ}) :
  -- Conclusion: for every ε > 0 and confidence δ > 0, some sample size `n` gives P(MSE(ŷ_NN) ≤ ε) ≥ 1-δ.
  ∀ ε : ℝ, 0 < ε → ∀ δ : ENNReal, 0 < δ →
    ∃ n : ℕ,
      (μ n) {ω |
        MSE (Q := Q) (X := X) Pf
          (yFull score Qstar)
          (fun f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f)
        ≤ ε} ≥ 1 - δ := by
  intro ε hε δ hδ
  have h_lip_const :
      LipschitzScore (Q := Q) (X := X) (d := d) γ
        (fun (_ : Finset Q) (f : Model Q X) => ψ Qsub f)
        (fun f => score f Qstar) := by
    intro _ f f'
    simpa using h_lipQ f f'
  let hNN : ℕ → Ω → Model Q X → ℝ :=
    fun n ω f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f
  have h_hNN_def :
      ∀ n ω f, (hn : n > 0) →
        hNN n ω f =
          hNN_estimator (d := d) hn
            (fun i => ψHat n ω Qsub (f_ref n ω i))
            (ψHat n ω Qsub f)
            (fun i => score (f_ref n ω i) Qstar) := by
    intro n ω f hn
    simp [hNN, yNN_paper, hn, hNN_estimator, nnIndex]
  have hp_atTop :=
    highProb_mse_le_of_subevent (Q := Q) (X := X) (d := d) (Ω := Ω)
      (Pf := Pf) (μ := μ) (hμ := hμ)
      (ψ := fun f => ψ Qsub f)
      (ψHat := fun n ω f => ψHat n ω Qsub f)
      (f_ref := f_ref)
      (score := score) (Qstar := Qstar)
      (γ := γ) (h_lip := h_lip_const) (h_gamma_pos := h_gamma_pos)
      (c := c) (h_c_tendsto := h_c_tendsto) (h_c_nonneg := h_c_nonneg)
      (E := E) (hE_meas := hE_meas) (hE_sub := hE_sub) (hE := hE)
      (h_cover := h_cover) (h_cover_meas := h_cover_meas)
      (hNN := hNN) (h_hNN_def := h_hNN_def)
      ε hε
  obtain ⟨N, hN⟩ := hp_atTop δ hδ
  refine ⟨N+1, ?_⟩
  exact hN (N+1) (Nat.lt_succ_self N)

/-- `highProb_queryEfficient_nn` (query efficiency) with a measurable
high-probability sub-event in place of `h_conc`/`h_conc_meas`. -/
theorem highProb_queryEfficient_nn_of_subevent
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (ψ : Finset Q → Model Q X → Vec d)
  (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (score : Model Q X → Finset Q → ℝ)
  (Qstar Qsub : Finset Q)
  -- paper condition m < M (recorded for fidelity; not used by the formal argument)
  (hm : Qsub.card < Qstar.card)
  -- paper Assumption 1 (Lipschitz score) for this `Qsub`
  (γ : ℝ)
  (h_lipQ : ∀ (f f' : Model Q X),
    |score f Qstar - score f' Qstar| ≤ γ * ‖ψ Qsub f - ψ Qsub f'‖)
  (h_gamma_pos : 0 < γ)
  -- embedding-error rate `c n → 0` (paper's Theorem 1 content, assumed here)
  (c : ℕ → ℝ) (h_c_tendsto : Tendsto c atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  -- measurable high-probability sub-event `E` of the embedding-error event
  -- (`hE_meas` is a Lean-only measurability device, not an assumption in the paper)
  (E : ℕ → Set Ω)
  (hE_meas : ∀ n, MeasurableSet (E n))
  (hE_sub : ∀ n, E n ⊆ {ω | ∀ f, ‖ψHat n ω Qsub f - ψ Qsub f‖ ≤ c n})
  (hE : HighProbAtTop μ hμ E)
  -- paper Assumption 2 (coverage); `h_cover_meas` is implicit / beyond the paper
  (h_cover :
    ∀ ρ > 0,
      HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ}))
  (h_cover_meas :
    ∀ ρ > 0, ∀ n,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ Qsub (f_ref n ω i) - ψ Qsub f‖ ≤ ρ})
  -- the sole driver of the conclusion: the baseline ŷ_Q has strictly positive MSE
  (hMSE_Q_pos :
    0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar) (yQ score Qsub)) :
  -- Conclusion: with high probability (some sample size `n`), MSE(ŷ_NN) ≤ MSE(ŷ_Q) — i.e. ŷ_NN
  -- is query-efficient relative to the subset baseline ŷ_Q.
  ∀ δ : ENNReal, 0 < δ →
    ∃ n : ℕ,
      (μ n) {ω |
        MSE (Q := Q) (X := X) Pf
          (yFull score Qstar)
          (fun f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f)
        ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar) (yQ score Qsub)} ≥ 1 - δ := by
  intro δ hδ
  let base : ℝ := MSE (Q := Q) (X := X) Pf (yFull score Qstar) (yQ score Qsub)
  have hbase_pos : 0 < base := hMSE_Q_pos
  have hbase_nonneg : 0 ≤ base := le_of_lt hbase_pos
  let ε : ℝ := base / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]; linarith
  obtain ⟨n, hn⟩ :=
    highProb_mse_nn_le_of_subevent (Q := Q) (X := X) (d := d) (Ω := Ω)
      (Pf := Pf) (μ := μ) (hμ := hμ)
      (ψ := ψ) (ψHat := ψHat) (f_ref := f_ref)
      (score := score) (Qstar := Qstar) (Qsub := Qsub)
      (γ := γ) (h_lipQ := h_lipQ) (h_gamma_pos := h_gamma_pos)
      (c := c) (h_c_tendsto := h_c_tendsto) (h_c_nonneg := h_c_nonneg)
      (E := E) (hE_meas := hE_meas) (hE_sub := hE_sub) (hE := hE)
      (h_cover := h_cover) (h_cover_meas := h_cover_meas)
      ε hε_pos δ hδ
  refine ⟨n, ?_⟩
  refine le_trans hn ?_
  apply MeasureTheory.measure_mono
  intro ω hω
  have : MSE (Q := Q) (X := X) Pf
        (yFull score Qstar)
        (fun f => yNN_paper (d := d) ψHat f_ref score Qstar Qsub n ω f)
      ≤ base := by
    have hε_le : ε ≤ base := by
      dsimp [ε]; linarith [hbase_nonneg]
    exact le_trans hω hε_le
  simpa [base] using this

end Theorem2_Subevent

