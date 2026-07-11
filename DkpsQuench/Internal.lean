/-
DKPS / Quench query-efficiency formalization — internal machinery.

The high-probability-event helper lemmas (`HighProbAtTop.{mono,inter,
mono_eventually}`), the per-model error-analysis steps (`step1`–`step6`,
`nnIndex_isArgmin`), and the abstract concentration→MSE engine theorems
(`highProb_mse_le_of_concentration`, `highProb_queryEfficient_of_concentration`) over an arbitrary embedding estimator.
The paper-facing theorems live in `DkpsQuench.Theorem2`.
-/
import DkpsQuench.Basic
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

section Theorem2_Proof_Steps

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}

/-- Step 1: the Lipschitz score assumption reduces the score-prediction error to
the *true* embedding (perspective-space) distance between the two models.
Internal helper corresponding to the first step of the paper's proof of the
query-efficiency theorem (its Theorem 2): the application of Assumption 1. -/
lemma step1_lipschitz_bound
    (γ : ℝ)
    (Psi : Finset Q → Model Q X → Vec d)
    (y : Model Q X → ℝ)
    (hLip : LipschitzScore γ Psi y)   -- the Lipschitz-score assumption (Assumption 1)
    (Qstar : Finset Q)
    (f_target : Model Q X)
    (f_ref : Model Q X) :
    -- Conclusion: the score error is at most γ times the true perspective distance.
    |y f_ref - y f_target| ≤ γ * ‖Psi Qstar f_ref - Psi Qstar f_target‖ := by
  specialize hLip Qstar f_ref f_target
  exact hLip

end Theorem2_Proof_Steps

section Theorem2_Proof_Steps

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}

/-- Step 2: a triangle-inequality split of the true perspective distance
`‖ψ i_star - ψ_target‖` into (i) the estimation errors at the reference and
target (`ψ` vs `ψHat`), and (ii) the *estimated* nearest-neighbor distance
`‖ψHat i_star - ψHat_target‖`. Internal helper for the paper's Theorem 2 proof. -/
lemma step2_triangle_inequality
    (n : ℕ)
    (ψ : Fin n → Vec d)          -- true reference perspectives
    (ψHat : Fin n → Vec d)       -- estimated reference perspectives
    (ψ_target : Vec d)           -- true target perspective
    (ψHat_target : Vec d)        -- estimated target perspective
    (i_star : Fin n) :
    -- Conclusion: triangle bound on the true distance via the estimated quantities.
    ‖ψ i_star - ψ_target‖ ≤
      ‖ψ i_star - ψHat i_star‖ + ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ := by
        -- Apply the triangle inequality to the vectors ψ i_star - ψHat i_star, ψHat i_star - ψHat_target, and ψHat_target - ψ_target.
        have h_triangle : ‖(ψ i_star - ψHat i_star) + (ψHat i_star - ψHat_target) + (ψHat_target - ψ_target)‖ ≤ ‖ψ i_star - ψHat i_star‖ + ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ := by
          -- Apply the triangle inequality to the sum of the three vectors.
          apply norm_add₃_le;
        -- Since the sum of the three vectors simplifies to ψ i_star - ψ_target, we can directly apply h_triangle to get the desired inequality.
        convert h_triangle using 1
        simp

end Theorem2_Proof_Steps

section HighProb_Lemmas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Monotonicity of `HighProbAtTop`: if a smaller event sequence `E` holds with
high probability and `E n ⊆ F n` for every `n`, then `F` also holds with high
probability. Internal helper lemma about the "high probability" encoding; not a
statement from the paper. -/
lemma HighProbAtTop.mono
    {μ : ℕ → Measure Ω} {hμ : ∀ n, IsProbabilityMeasure (μ n)}
    {E F : ℕ → Set Ω}
    (hE : HighProbAtTop μ hμ E)        -- E holds with high probability
    (h_subset : ∀ n, E n ⊆ F n) :      -- F always contains E
    -- Conclusion: F also holds with high probability.
    HighProbAtTop μ hμ F := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hE δ hδ
  use N
  intro n hn
  refine le_trans (hN n hn) ?_
  apply MeasureTheory.measure_mono
  exact h_subset n


end HighProb_Lemmas

/-- Arithmetic helper in `ENNReal`: if two probabilities each exceed `1 - δ/2`,
then `p + q - 1 ≥ 1 - δ` (the Bonferroni/union-bound arithmetic used to combine
two high-probability events). Internal helper; no paper counterpart. -/
lemma ennreal_inter_bound {δ p q : ENNReal}
    (hp : 1 - δ / 2 ≤ p)
    (hq : 1 - δ / 2 ≤ q) :
    -- Conclusion: the combined lower bound 1 - δ on p + q - 1.
    1 - δ ≤ p + q - 1 := by
      rcases le_or_gt 1 δ with hδ | hδ
      · -- If δ ≥ 1, then 1 - δ = 0 and the inequality is trivial.
        simp [tsub_eq_zero_of_le hδ]
      · -- Otherwise δ < 1, so δ and δ/2 are finite and δ/2 ≤ 1.
        have hδ_top : δ ≠ ⊤ := hδ.ne_top
        have hhalf_le : δ / 2 ≤ 1 := ENNReal.half_le_self.trans hδ.le
        apply ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top
        -- Goal: 1 - δ + 1 ≤ p + q.  Both sides reduce to 2 - δ ≤ p + q.
        have h1 : (1 : ENNReal) - δ + 1 = 2 - δ := by
          rw [ENNReal.sub_add_eq_add_sub hδ.le hδ_top, one_add_one_eq_two]
        have hhalf_top : δ / 2 ≠ ⊤ := (hhalf_le.trans_lt ENNReal.one_lt_top).ne
        have hsum : (1 - δ / 2) + (1 - δ / 2) = 2 - δ := by
          rw [ENNReal.sub_add_eq_add_sub hhalf_le hhalf_top,
            add_comm (1 : ENNReal) (1 - δ / 2),
            ENNReal.sub_add_eq_add_sub hhalf_le hhalf_top, tsub_tsub,
            ENNReal.add_halves, one_add_one_eq_two]
        rw [h1, ← hsum]
        exact add_le_add hp hq

section HighProb_Lemmas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Intersection of high-probability events: if `E` and `F` each hold with high
probability, so does their intersection `E ∩ F` (a union-bound argument).
Internal helper lemma about the "high probability" encoding; not from the paper. -/
lemma HighProbAtTop.inter
    {μ : ℕ → Measure Ω} {hμ : ∀ n, IsProbabilityMeasure (μ n)}
    {E F : ℕ → Set Ω}
    (hE : HighProbAtTop μ hμ E)             -- E holds with high probability
    (hF : HighProbAtTop μ hμ F)             -- F holds with high probability
    -- extra (implicit) assumptions beyond the paper: measurability of the events,
    -- needed so the measure of the intersection is controlled by a union bound.
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hF_meas : ∀ n, MeasurableSet (F n)) :
    -- Conclusion: the intersection E ∩ F also holds with high probability.
    HighProbAtTop μ hμ (fun n => E n ∩ F n) := by
      -- By definition of HighProbAtTop, we know that for any δ > 0, there exist N1 and N2 such that for all n > N1, μ n (E n) ≥ 1 - δ/2, and for all n > N2, μ n (F n) ≥ 1 - δ/2.
      have hN1N2 : ∀ δ > 0, ∃ N1 N2 : ℕ, ∀ n > N1, (μ n) (E n) ≥ 1 - δ / 2 ∧ ∀ n > N2, (μ n) (F n) ≥ 1 - δ / 2 := by
        -- By definition of HighProbAtTop, for any δ > 0, there exist N1 and N2 such that for all n > N1, μ n (E n) ≥ 1 - δ/2, and for all n > N2, μ n (F n) ≥ 1 - δ/2.
        intros δ hδ_pos
        obtain ⟨N1, hN1⟩ := hE (δ / 2) (by
        -- Since δ is positive, dividing it by 2 will still give a positive result. We can use the fact that division by a positive number preserves positivity.
        apply ENNReal.half_pos; exact hδ_pos.ne')
        obtain ⟨N2, hN2⟩ := hF (δ / 2) (by
        exact ENNReal.half_pos hδ_pos.ne')
        use N1, N2
        intro n hn
        exact ⟨hN1 n hn, fun n' hn' => hN2 n' hn'⟩
      intro δ hδ_pos
      obtain ⟨N1, N2, hN1N2⟩ := hN1N2 δ hδ_pos
      use max N1 N2
      intro n hn
      have h1 : (μ n) (E n) ≥ 1 - δ / 2 := by
        exact hN1N2 n ( lt_of_le_of_lt ( le_max_left _ _ ) hn ) |>.1
      have h2 : (μ n) (F n) ≥ 1 - δ / 2 := by
        grind
      have h3 : (μ n) (E n ∩ F n) ≥ 1 - δ := by
        have h3 : (μ n) (E n ∩ F n) ≥ (μ n) (E n) + (μ n) (F n) - 1 := by
          have h3 : (μ n) (E n ∪ F n) ≤ 1 := by
            exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide )
          have h4 : (μ n) (E n ∩ F n) = (μ n) (E n) + (μ n) (F n) - (μ n) (E n ∪ F n) := by
            rw [ ← MeasureTheory.measure_union_add_inter, ENNReal.add_sub_cancel_left ] ; aesop;
            exact hF_meas n
          rw [h4]
          have h5 : (μ n) (E n ∪ F n) ≤ 1 := h3
          exact (by
          exact tsub_le_tsub_left h3 ((μ n) (E n) + (μ n) (F n)))
        refine le_trans ?_ h3;
        exact ennreal_inter_bound h1 h2
      exact h3

/-- A finite conjunction of measurable events is measurable.  This avoids
introducing countability requirements on the ambient index type: only the
explicit finite set of indices is intersected. -/
lemma measurableSet_finset_all
    {ι : Type*} (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    MeasurableSet {ω | ∀ i ∈ s, ω ∈ E i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha_meas : MeasurableSet (E a) :=
        hE a (Finset.mem_insert_self a s)
      have hs_meas : MeasurableSet {ω | ∀ i ∈ s, ω ∈ E i} := by
        apply ih
        intro i hi
        exact hE i (Finset.mem_insert_of_mem hi)
      have heq : {ω | ∀ i ∈ insert a s, ω ∈ E i} =
          E a ∩ {ω | ∀ i ∈ s, ω ∈ E i} := by
        ext ω
        simp
      rw [heq]
      exact ha_meas.inter hs_meas

/-- A finite conjunction of measurable high-probability event sequences is
again high probability. -/
lemma HighProbAtTop.finset_all
    {ι : Type*} {μ : ℕ → Measure Ω} {hμ : ∀ n, IsProbabilityMeasure (μ n)}
    (s : Finset ι) (E : ι → ℕ → Set Ω)
    (hE : ∀ i ∈ s, HighProbAtTop μ hμ (E i))
    (hE_meas : ∀ i ∈ s, ∀ n, MeasurableSet (E i n)) :
    HighProbAtTop μ hμ (fun n => {ω | ∀ i ∈ s, ω ∈ E i n}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro δ hδ
      refine ⟨0, ?_⟩
      intro n hn
      simp
  | @insert a s ha ih =>
      have ha_hp : HighProbAtTop μ hμ (E a) :=
        hE a (Finset.mem_insert_self a s)
      have hs_hp : HighProbAtTop μ hμ
          (fun n => {ω | ∀ i ∈ s, ω ∈ E i n}) := by
        apply ih
        · intro i hi
          exact hE i (Finset.mem_insert_of_mem hi)
        · intro i hi n
          exact hE_meas i (Finset.mem_insert_of_mem hi) n
      have hs_meas : ∀ n,
          MeasurableSet {ω | ∀ i ∈ s, ω ∈ E i n} := by
        intro n
        exact measurableSet_finset_all s (fun i => E i n)
          (fun i hi => hE_meas i (Finset.mem_insert_of_mem hi) n)
      have hinter := HighProbAtTop.inter ha_hp hs_hp
        (fun n => hE_meas a (Finset.mem_insert_self a s) n) hs_meas
      have heq : (fun n => {ω | ∀ i ∈ insert a s, ω ∈ E i n}) =
          (fun n => E a n ∩ {ω | ∀ i ∈ s, ω ∈ E i n}) := by
        funext n
        ext ω
        simp
      rw [heq]
      exact hinter

end HighProb_Lemmas

section Theorem2_Proof_Steps

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}

/-- Step 3: on the *concentration event* (estimated perspectives within `c` of
the truth), the true distance is bounded by `2c + δ*`, where `δ*` is the
estimated nearest-neighbor distance `‖ψHat i_star - ψHat_target‖`. Internal
helper corresponding to the concentration step of the paper's Theorem 2 proof. -/
lemma step3_concentration_bound
    (n : ℕ)
    (ψ : Fin n → Vec d)
    (ψHat : Fin n → Vec d)
    (ψ_target : Vec d)
    (ψHat_target : Vec d)
    (i_star : Fin n)
    (c : ℝ)
    -- concentration of the estimated embeddings: each estimate within c of the truth
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c) :
    -- Conclusion: true distance ≤ 2c plus the estimated nearest-neighbor distance δ*.
    ‖ψ i_star - ψ_target‖ ≤ 2 * c + ‖ψHat i_star - ψHat_target‖ := by
  calc ‖ψ i_star - ψ_target‖
    _ ≤ ‖ψ i_star - ψHat i_star‖ + ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ :=
      step2_triangle_inequality n ψ ψHat ψ_target ψHat_target i_star
    _ = ‖ψHat i_star - ψ i_star‖ + ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ := by
      rw [norm_sub_rev]
    _ ≤ c + ‖ψHat i_star - ψHat_target‖ + c := by
      gcongr
      exact h_conc_ref i_star
    _ = 2 * c + ‖ψHat i_star - ψHat_target‖ := by
      ring

end Theorem2_Proof_Steps

section Theorem2_Proof_Steps

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}

/-- Step 4: combining nearest-neighbor optimality with the *support/coverage*
assumption (some reference model is within `ρ` of the target in true perspective
space), the true distance from the selected neighbor `i_star` to the target is
bounded by `ρ + 4c`. Internal helper corresponding to the model-support step of
the paper's Theorem 2 proof (its Assumption 2). -/
lemma step4_support_bound
    (n : ℕ)
    (ψ : Fin n → Vec d)
    (ψHat : Fin n → Vec d)
    (ψ_target : Vec d)
    (ψHat_target : Vec d)
    (i_star : Fin n)
    -- i_star is the estimated nearest neighbor (argmin of estimated distance)
    (h_i_star : IsArgmin (fun i => ‖ψHat i - ψHat_target‖) i_star)
    (c ρ : ℝ)
    -- concentration of the estimated embeddings (each estimate within c of truth)
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c)
    -- coverage/support: some reference model lands within ρ of the target (Assumption 2)
    (h_supp : ∃ j : Fin n, ‖ψ j - ψ_target‖ ≤ ρ) :
    -- Conclusion: the selected neighbor's true distance to the target is ≤ ρ + 4c.
    ‖ψ i_star - ψ_target‖ ≤ ρ + 4 * c := by
      -- By the triangle inequality, we have ‖ψ i_star - ψ_target‖ ≤ ‖ψ i_star - ψ_hat i_star‖ + ‖ψ_hat i_star - ψ_hat_target‖ + ‖ψ_hat_target - ψ_target‖.
      have h_triangle : ‖ψ i_star - ψ_target‖ ≤ ‖ψ i_star - ψHat i_star‖ + ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle4 (ψ i_star) (ψHat i_star) ψHat_target ψ_target;
      -- By the triangle inequality, we have ‖ψ_hat i_star - ψ_hat_target‖ ≤ 2c + ‖ψ j_star - ψ_target‖.
      obtain ⟨j_star, hj_star⟩ : ∃ j_star, ‖ψ j_star - ψ_target‖ ≤ ρ := h_supp
      have h_triangle_j_star : ‖ψHat i_star - ψHat_target‖ ≤ 2 * c + ‖ψ j_star - ψ_target‖ := by
        -- By the triangle inequality, we have ‖ψHat i_star - ψHat_target‖ ≤ ‖ψHat j_star - ψHat_target‖.
        have h_triangle_j_star : ‖ψHat i_star - ψHat_target‖ ≤ ‖ψHat j_star - ψHat_target‖ := by
          exact h_i_star j_star;
        -- By the triangle inequality, we have ‖ψHat j_star - ψHat_target‖ ≤ ‖ψHat j_star - ψ j_star‖ + ‖ψ j_star - ψ_target‖ + ‖ψHat_target - ψ_target‖.
        have h_triangle_j_star : ‖ψHat j_star - ψHat_target‖ ≤ ‖ψHat j_star - ψ j_star‖ + ‖ψ j_star - ψ_target‖ + ‖ψHat_target - ψ_target‖ := by
          have h_triangle_j_star : ‖ψHat j_star - ψHat_target‖ ≤ ‖ψHat j_star - ψ j_star‖ + ‖ψ j_star - ψHat_target‖ := by
            simpa using norm_add_le ( ψHat j_star - ψ j_star ) ( ψ j_star - ψHat_target );
          have h_triangle_j_star : ‖ψ j_star - ψHat_target‖ ≤ ‖ψ j_star - ψ_target‖ + ‖ψHat_target - ψ_target‖ := by
            convert norm_sub_le ( ψ j_star - ψ_target ) ( ψHat_target - ψ_target ) using 1 ; abel_nf;
          linarith;
        linarith [ h_conc_ref j_star ];
      linarith [ norm_sub_rev ( ψ i_star ) ( ψHat i_star ), h_conc_ref i_star ]

end Theorem2_Proof_Steps

section Theorem2_Proof_Steps

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}

/-- Step 5: the final *pointwise* (per-model) score-prediction error bound:
combining the Lipschitz bound (Step 1) with the distance bound (Step 4), the
nearest-neighbor prediction error is at most `γ·(ρ + 4c)`. Internal helper
assembling the per-model error bound in the paper's Theorem 2 proof. -/
lemma step5_pointwise_error
    (n : ℕ)
    (ψ : Fin n → Vec d)
    (ψHat : Fin n → Vec d)
    (ψ_target : Vec d)
    (ψHat_target : Vec d)
    (i_star : Fin n)
    -- i_star is the estimated nearest neighbor (argmin of estimated distance)
    (h_i_star : IsArgmin (fun i => ‖ψHat i - ψHat_target‖) i_star)
    (c ρ γ : ℝ)
    -- concentration of the estimated embeddings (each estimate within c of truth)
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c)
    -- coverage/support: some reference model is within ρ of the target (Assumption 2)
    (h_supp : ∃ j : Fin n, ‖ψ j - ψ_target‖ ≤ ρ)
    (y_ref : Fin n → ℝ)
    (y_target : ℝ)
    -- Lipschitz score bound applied pointwise (Assumption 1)
    (h_lip : ∀ i, |y_ref i - y_target| ≤ γ * ‖ψ i - ψ_target‖)
    -- nonnegativity side-conditions on the constants (not separate paper assumptions)
    (h_gamma_nonneg : 0 ≤ γ)
    (h_rho_nonneg : 0 ≤ ρ)
    (h_c_nonneg : 0 ≤ c) :
    -- Conclusion: the nearest-neighbor prediction error is at most γ·(ρ + 4c).
    |y_ref i_star - y_target| ≤ γ * (ρ + 4 * c) := by
  calc |y_ref i_star - y_target|
    _ ≤ γ * ‖ψ i_star - ψ_target‖ := h_lip i_star
    _ ≤ γ * (ρ + 4 * c) := by
      gcongr
      exact step4_support_bound n ψ ψHat ψ_target ψHat_target i_star h_i_star c ρ h_conc_ref h_conc_target h_supp

end Theorem2_Proof_Steps

section Theorem2_Proof_Steps

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}

/-- Step 6: the explicit *parameter choice*. Taking the coverage radius
`ρ = √ε/(2γ)` and requiring the concentration constant `c ≤ √ε/(8γ)` makes the
squared pointwise error `(γ·(ρ + 4c))²` at most `ε`. Internal helper realizing
the parameter-tuning step of the paper's Theorem 2 proof that drives the squared
error below the target `ε`. -/
lemma step6_parameter_choice
    (ε γ : ℝ)
    (h_eps_pos : 0 < ε)
    (h_gamma_pos : 0 < γ) :
    -- ρ (coverage radius) and c_bound (concentration budget) chosen in terms of ε, γ
    let ρ := Real.sqrt ε / (2 * γ)
    let c_bound := Real.sqrt ε / (8 * γ)
    -- Conclusion: for any concentration constant c within budget, the squared error ≤ ε.
    ∀ c, 0 ≤ c → c ≤ c_bound →
      (γ * (ρ + 4 * c)) ^ 2 ≤ ε := by
        -- Substitute the values of ρ and c_bound into the inequality.
        intro ρ c_bound c hc_nonneg hc_le_bound
        field_simp [hc_nonneg, hc_le_bound];
        -- Substitute the values of ρ and c_bound into the inequality and simplify.
        have h_subst : (Real.sqrt ε / (2 * γ) + 4 * (Real.sqrt ε / (8 * γ))) ^ 2 = ε / γ ^ 2 := by
          grind;
        -- Since $c \leq \frac{\sqrt{\epsilon}}{8\gamma}$, we have $4c \leq \frac{\sqrt{\epsilon}}{2\gamma}$. Therefore, $\rho + 4c \leq \rho + \frac{\sqrt{\epsilon}}{2\gamma}$.
        have h_bound : ρ + 4 * c ≤ ρ + 4 * c_bound := by
          nlinarith [hc_le_bound]
        exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) h_bound 2 ) ( by positivity ) ) ( by rw [ h_subst, mul_div_cancel₀ _ ( by positivity ) ] )

end Theorem2_Proof_Steps

section HighProb_Lemmas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- "Eventual" monotonicity of `HighProbAtTop`: it suffices that `E n ⊆ F n`
holds *eventually* (for all large `n`), rather than for every `n`, to transfer
the high-probability property from `E` to `F`. Internal helper lemma about the
"high probability" encoding; not from the paper. -/
lemma HighProbAtTop.mono_eventually
    {μ : ℕ → Measure Ω} {hμ : ∀ n, IsProbabilityMeasure (μ n)}
    {E F : ℕ → Set Ω}
    (hE : HighProbAtTop μ hμ E)                  -- E holds with high probability
    (h_subset : ∀ᶠ n in atTop, E n ⊆ F n) :      -- F eventually contains E
    -- Conclusion: F also holds with high probability.
    HighProbAtTop μ hμ F := by
      -- Since $E_n \subseteq F_n$ for sufficiently large $n$, we have $\mu_n(F_n) \geq \mu_n(E_n)$.
      have h_measure_ge : ∀ᶠ n in Filter.atTop, (μ n) (F n) ≥ (μ n) (E n) := by
        exact h_subset.mono fun n hn => MeasureTheory.measure_mono hn |> le_trans <| le_rfl;
      -- By combining the results from hE and h_measure_ge, we can conclude that for any δ > 0, there exists an N such that for all n > N, the measure of F n is at least 1 - δ.
      intros δ hδ_pos
      obtain ⟨N, hN⟩ := hE δ hδ_pos
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_measure_ge
      use max N M
      intro n hn
      have h_measure_F : (μ n) (F n) ≥ (μ n) (E n) := by
        -- Since $n > \max N M$, we have $n \geq M$, so we can apply $hM$.
        apply hM n (le_of_lt (lt_of_le_of_lt (le_max_right N M) hn))
      have h_measure_E : (μ n) (E n) ≥ 1 - δ := by
        exact hN n ( lt_of_le_of_lt ( le_max_left _ _ ) hn )
      exact le_trans h_measure_E h_measure_F

end HighProb_Lemmas

section NN_Definitions_Properties

variable {d : ℕ}

/-- The index returned by `nnIndex` really is a nearest neighbor: it minimizes
the estimated distance `‖ψHat_ref i - ψHat_target‖`. Internal correctness lemma
for the nearest-neighbor selection. -/
lemma nnIndex_isArgmin {n : ℕ} (hn : n > 0)
    (ψHat_ref : Fin n → Vec d)
    (ψHat_target : Vec d) :
    -- Conclusion: nnIndex selects a minimizer of the estimated distance.
    IsArgmin (fun i => ‖ψHat_ref i - ψHat_target‖) (nnIndex hn ψHat_ref ψHat_target) := by
  unfold nnIndex
  apply Classical.choose_spec


@[simp] lemma mem_nnMinimizers_iff {n : ℕ} (hn : n > 0)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) (i : Fin n) :
    i ∈ nnMinimizers hn ψHat_ref ψHat_target ↔
      IsArgmin (fun j => ‖ψHat_ref j - ψHat_target‖) i := by
  simp [nnMinimizers]

lemma nnIndex_mem_nnMinimizers {n : ℕ} (hn : n > 0)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) :
    nnIndex hn ψHat_ref ψHat_target ∈ nnMinimizers hn ψHat_ref ψHat_target := by
  rw [mem_nnMinimizers_iff]
  exact nnIndex_isArgmin hn ψHat_ref ψHat_target

lemma nnMinimizers_nonempty {n : ℕ} (hn : n > 0)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) :
    (nnMinimizers hn ψHat_ref ψHat_target).Nonempty :=
  ⟨nnIndex hn ψHat_ref ψHat_target,
    nnIndex_mem_nnMinimizers hn ψHat_ref ψHat_target⟩

/-- An average of tied-nearest-neighbor scores inherits any common absolute
error bound satisfied by every tied minimizer. -/
lemma abs_hNNTieAverage_sub_le {n : ℕ} (hn : n > 0)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d)
    (y_ref : Fin n → ℝ) (y_target B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ i ∈ nnMinimizers hn ψHat_ref ψHat_target,
      |y_ref i - y_target| ≤ B) :
    |hNNTieAverage hn ψHat_ref ψHat_target y_ref - y_target| ≤ B := by
  let S := nnMinimizers hn ψHat_ref ψHat_target
  have hS : S.Nonempty := by
    simpa [S] using nnMinimizers_nonempty hn ψHat_ref ψHat_target
  have hcard_nat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hcard_nat
  have hsum :
      |∑ i ∈ S, (y_ref i - y_target)| ≤ (S.card : ℝ) * B := by
    calc
      |∑ i ∈ S, (y_ref i - y_target)|
          ≤ ∑ i ∈ S, |y_ref i - y_target| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ S, B :=
        Finset.sum_le_sum fun i hi => hbound i (by simpa [S] using hi)
      _ = (S.card : ℝ) * B := by simp [mul_comm]
  have havg_rewrite :
      (∑ i ∈ S, y_ref i) / (S.card : ℝ) - y_target =
        (∑ i ∈ S, (y_ref i - y_target)) / (S.card : ℝ) := by
    field_simp [ne_of_gt hcard]
    simp [Finset.sum_sub_distrib]
  rw [hNNTieAverage]
  change |(∑ i ∈ S, y_ref i) / (S.card : ℝ) - y_target| ≤ B
  rw [havg_rewrite, abs_div, abs_of_pos hcard]
  exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hsum)

/-- Every tied estimated nearest neighbor satisfies the same deterministic
score-error bound, so their average satisfies it as well. -/
lemma step5_tieAverage_pointwise_error
    {n : ℕ} (hn : n > 0)
    (ψ ψHat : Fin n → Vec d)
    (ψ_target ψHat_target : Vec d)
    (c ρ γ : ℝ)
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c)
    (h_supp : ∃ j : Fin n, ‖ψ j - ψ_target‖ ≤ ρ)
    (y_ref : Fin n → ℝ) (y_target : ℝ)
    (h_lip : ∀ i, |y_ref i - y_target| ≤ γ * ‖ψ i - ψ_target‖)
    (h_gamma_nonneg : 0 ≤ γ) (h_rho_nonneg : 0 ≤ ρ)
    (h_c_nonneg : 0 ≤ c) :
    |hNNTieAverage hn ψHat ψHat_target y_ref - y_target| ≤
      γ * (ρ + 4 * c) := by
  apply abs_hNNTieAverage_sub_le hn ψHat ψHat_target y_ref y_target
    (γ * (ρ + 4 * c))
  · positivity
  · intro i hi
    apply step5_pointwise_error n ψ ψHat ψ_target ψHat_target i
      ((mem_nnMinimizers_iff hn ψHat ψHat_target i).1 hi)
      c ρ γ h_conc_ref h_conc_target h_supp y_ref y_target
      h_lip h_gamma_nonneg h_rho_nonneg h_c_nonneg

end NN_Definitions_Properties

section MSE_Properties

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- A uniform pointwise squared-error bound integrates to the same MSE bound
under a probability measure. -/
lemma mse_le_of_pointwise_sq_error_le
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (y yHat : Model Q X → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hbound : ∀ f, (yHat f - y f) ^ 2 ≤ ε) :
    MSE Pf y yHat ≤ ε := by
  have hint : ∫ f, (yHat f - y f) ^ 2 ∂Pf ≤ ∫ _f, ε ∂Pf := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun f => sq_nonneg _
    · norm_num
    · exact Filter.Eventually.of_forall hbound
  change (∫ f, (yHat f - y f) ^ 2 ∂Pf) ≤ ε
  exact hint.trans_eq (by simp)

end MSE_Properties

section Theorem2_Part1_Proof

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Abstract engine theorem — Theorem 2, Part 1 (MSE ≤ ε with high
probability).** This is the abstract (arbitrary-embedding) form of the paper's
query-efficiency Theorem 2, Part 1: under a Lipschitz score, a vanishing
concentration rate, and a coverage assumption, the nearest-neighbor estimator's
MSE is at most any target `ε > 0` with high probability (eventually in `n`).
It is stated over an *arbitrary* embedding estimator `ψHat` and reference-sampler
`f_ref` (not the specific DKPS perspective estimator of the paper), which is the
abstractness flagged below. -/
theorem highProb_mse_le_of_concentration
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  -- ψ : the true perspective embedding; ψHat : an ARBITRARY estimator of it.
  -- extra abstractness beyond the paper: ψHat / f_ref are generic, not the DKPS estimator.
  (ψ : Model Q X → Vec d)
  (ψHat : ℕ → Ω → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)        -- the n sampled reference models
  (score : Model Q X → Finset Q → ℝ)
  (Qstar : Finset Q)
  (γ : ℝ)
  -- Lipschitz score assumption (Assumption 1), here for the true embedding ψ
  (h_lip : LipschitzScore γ (fun _ f => ψ f) (fun f => score f Qstar))
  (h_gamma_pos : 0 < γ)
  -- concentration rate c n → 0 (the abstract analogue of the paper's concentration
  -- constant c(n,m,r,d)); tendsto/nonneg are extra side-conditions on the rate.
  (c : ℕ → ℝ) (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  -- concentration event holds with high probability: all estimates within c n of truth
  (h_conc : HighProbAtTop μ hμ (fun n => {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n}))
  -- extra (implicit) assumption beyond the paper: measurability of the concentration event
  (h_conc_meas : ∀ n, MeasurableSet {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
  -- coverage/support assumption (Assumption 2): for every radius ρ, with high
  -- probability every target is within ρ of some sampled reference model
  (h_cover : ∀ ρ > 0, HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}))
  -- extra (implicit) assumption beyond the paper: measurability of the coverage event
  (h_cover_meas : ∀ ρ > 0, ∀ n, MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ})
  (hNN : ℕ → Ω → Model Q X → ℝ)
  -- hNN is the nearest-neighbor estimator built from the estimated embeddings
  (h_hNN_def : ∀ n ω f, (hn : n > 0) → hNN n ω f = hNN_estimator hn (fun i => ψHat n ω (f_ref n ω i)) (ψHat n ω f) (fun i => score (f_ref n ω i) Qstar)) :
  -- Conclusion: for every ε > 0, MSE(ŷ_NN) ≤ ε with high probability (eventually in n).
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ (fun n => {ω | MSE Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ ε}) := by
      -- Apply the Lipschitz condition to bound the mean squared error.
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
      have h_inter : HighProbAtTop μ hμ (fun n => {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n} ∩ {ω | ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ Real.sqrt ε / (2 * γ)}) := by
        apply HighProbAtTop.inter h_conc (h_cover (Real.sqrt ε / (2 * γ)) (by
        positivity)) (fun n => h_conc_meas n) (fun n => h_cover_meas (Real.sqrt ε / (2 * γ)) (by
        positivity) n);
      exact h_inter.mono_eventually ( Filter.eventually_atTop.mpr ⟨ N + 1, fun n hn => by intro ω hω; exact hN n ( by linarith ) ω hω ⟩ )

end Theorem2_Part1_Proof

section Theorem2_Part2_Proof

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Abstract engine theorem — Theorem 2, Part 2 (query-efficiency).** This is
the abstract (arbitrary-embedding) form of the paper's query-efficiency
Theorem 2, Part 2: since the nearest-neighbor MSE can be driven below any `ε`
(Part 1, `highProb_mse_le_of_concentration`), and the subset baseline `hQ` has
MSE bounded below by a positive constant, the nearest-neighbor estimator
eventually has MSE no larger than the baseline — i.e. it is query-efficient — with
high probability. Like Part 1 it is stated over an arbitrary embedding estimator
`ψHat` rather than the specific DKPS estimator. -/
theorem highProb_queryEfficient_of_concentration
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  -- ψ : true embedding; ψHat : ARBITRARY estimator (abstractness beyond the paper)
  (ψ : Model Q X → Vec d)
  (ψHat : ℕ → Ω → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)        -- the n sampled reference models
  (score : Model Q X → Finset Q → ℝ)
  (Qstar : Finset Q)
  (γ : ℝ)
  -- Lipschitz score assumption (Assumption 1)
  (h_lip : LipschitzScore γ (fun _ f => ψ f) (fun f => score f Qstar))
  (h_gamma_pos : 0 < γ)
  -- vanishing concentration rate c n → 0 (extra tendsto/nonneg side-conditions on the rate)
  (c : ℕ → ℝ) (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds 0))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  -- concentration event holds with high probability
  (h_conc : HighProbAtTop μ hμ (fun n => {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n}))
  -- extra (implicit) assumption beyond the paper: measurability of the concentration event
  (h_conc_meas : ∀ n, MeasurableSet {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
  -- coverage/support assumption (Assumption 2) holding with high probability
  (h_cover : ∀ ρ > 0, HighProbAtTop μ hμ (fun n => {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}))
  -- extra (implicit) assumption beyond the paper: measurability of the coverage event
  (h_cover_meas : ∀ ρ > 0, ∀ n, MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ})
  (hNN hQ : ℕ → Ω → Model Q X → ℝ)
  -- hNN is the nearest-neighbor estimator; hQ is the subset-score baseline ŷ_Q
  (h_hNN_def : ∀ n ω f, (hn : n > 0) → hNN n ω f = hNN_estimator hn (fun i => ψHat n ω (f_ref n ω i)) (ψHat n ω f) (fun i => score (f_ref n ω i) Qstar))
  -- baseline has strictly positive MSE bounded below by c_base (paper's MSE(ŷ_Q) > 0)
  (hQ_pos : ∃ c_base : ℝ, 0 < c_base ∧ ∃ N : ℕ, ∀ n > N, ∀ ω : Ω,
      c_base ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)) :
  -- Conclusion: with high probability the NN estimator's MSE ≤ the baseline's MSE
  -- (i.e. ŷ_NN is query-efficient relative to ŷ_Q).
  HighProbAtTop (μ := μ) (hμ := hμ)
    (E := fun n => {ω : Ω |
      MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f)
        ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)
    }) := by
      obtain ⟨ c_base, hc_base_pos, N, hN ⟩ := hQ_pos;
      intro δ hδ_pos;
      -- By choosing ε = c_base, we can apply highProb_mse_le_of_concentration to get the desired result.
      obtain ⟨N', hN'⟩ : ∃ N', ∀ n > N', (μ n) {ω | MSE Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ c_base} ≥ 1 - δ := by
        apply highProb_mse_le_of_concentration Pf μ hμ ψ ψHat f_ref score Qstar γ h_lip h_gamma_pos c h_c_tendsto h_c_nonneg h_conc h_conc_meas h_cover h_cover_meas hNN h_hNN_def c_base hc_base_pos |> fun h => h δ hδ_pos |> fun ⟨ N', hN' ⟩ => ⟨ N', fun n hn => hN' n hn ⟩;
      exact ⟨ Max.max N N', fun n hn => le_trans ( hN' n ( lt_of_le_of_lt ( le_max_right _ _ ) hn ) ) ( MeasureTheory.measure_mono fun ω hω => le_trans hω.out ( hN n ( lt_of_le_of_lt ( le_max_left _ _ ) hn ) ω ) ) ⟩

end Theorem2_Part2_Proof
