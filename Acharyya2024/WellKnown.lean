/-
General lemmas used by the Acharyya et al. 2024 formalization.

This file is intentionally paper-agnostic: results that are useful outside DKPS
belong here first, so they can later be moved toward Mathlib if they are not
already present there in a comparable form.
-/

import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory

/--
Changing both endpoints of a distance changes the distance by at most the sum of
the two endpoint perturbations.

This is the normed-additive-group form of the elementary estimate used in the
paper's Appendix A.2 before applying Markov's inequality.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub
    {E : Type*} [SeminormedAddCommGroup E]
    (x y x₀ y₀ : E) :
    |‖x - y‖ - ‖x₀ - y₀‖| ≤ ‖x - x₀‖ + ‖y - y₀‖ := by
  have h₁ : |‖x - y‖ - ‖x₀ - y₀‖| ≤ ‖(x - y) - (x₀ - y₀)‖ :=
    abs_norm_sub_norm_le (x - y) (x₀ - y₀)
  have h₂ : ‖(x - y) - (x₀ - y₀)‖ ≤ ‖x - x₀‖ + ‖y - y₀‖ := by
    have hrewrite : (x - y) - (x₀ - y₀) = (x - x₀) - (y - y₀) := by
      abel
    simpa [hrewrite] using norm_sub_le (x - x₀) (y - y₀)
  exact h₁.trans h₂

/--
A scaled version of `abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub` for a
nonnegative scalar.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_mul_norm_sub_sub_le_mul_norm_sub_add
    {E : Type*} [SeminormedAddCommGroup E]
    {c : Real} (hc : 0 ≤ c) (x y x₀ y₀ : E) :
    |c * ‖x - y‖ - c * ‖x₀ - y₀‖| ≤ c * (‖x - x₀‖ + ‖y - y₀‖) := by
  have h :
      |c * ‖x - y‖ - c * ‖x₀ - y₀‖|
        = c * |‖x - y‖ - ‖x₀ - y₀‖| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub x y x₀ y₀) hc

/--
The finite `ℓ²` norm of a real-valued function is bounded by its `ℓ¹` norm.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (f : ι → Real) :
    Real.sqrt (∑ i, (f i)^2) ≤ ∑ i, |f i| := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg (f i)
  · simpa [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset ι)) (f := fun i => |f i|)
        (fun i _ => abs_nonneg (f i)))

/--
If measurable events have probability eventually at least `1 - δ` for every
positive `δ`, then their complements have measure tending to zero.

This is a paper-independent probability bookkeeping lemma and is a plausible
Mathlib contribution candidate if an equivalent result is not already present.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem tendsto_measure_compl_zero_of_forall_eventually_ge_one_sub
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Nat → Set Ω)
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE_prob :
      ∀ δ : ENNReal, 0 < δ → ∃ N : Nat, ∀ n > N, P (E n) ≥ 1 - δ) :
    Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨N, hN⟩ := hE_prob δ hδ
  refine eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
  have hn_gt : n > N := by omega
  have hgood : 1 - δ ≤ P (E n) := hN n hn_gt
  have hcompl_le : 1 - P (E n) ≤ δ := by
    have hmono : 1 - P (E n) ≤ 1 - (1 - δ) :=
      tsub_le_tsub_left hgood 1
    exact hmono.trans (by
      rw [tsub_le_iff_right]
      simpa [add_comm] using (le_tsub_add : (1 : ENNReal) ≤ 1 - δ + δ))
  calc
    P (E n)ᶜ = 1 - P (E n) := by
      rw [measure_compl (hE_meas n) (measure_ne_top P (E n)), measure_univ]
    _ ≤ δ := hcompl_le

/--
A high-probability deterministic error bound with rate tending to zero implies
the usual convergence-in-probability bad-event probabilities tend to zero.

This is stated for real-valued errors and does not depend on DKPS.  It is a
second plausible Mathlib contribution candidate, likely near the existing
convergence-in-measure API.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem tendsto_measure_abs_gt_zero_of_highProb_abs_le_rate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Nat → Ω → Real)
    (rate : Nat → Real)
    (hgood_meas : ∀ n, MeasurableSet {ω | |X n ω| ≤ rate n})
    (hrate : Tendsto rate atTop (𝓝 0))
    (hgood_prob :
      ∀ δ : ENNReal, 0 < δ → ∃ N : Nat, ∀ n > N,
        P {ω | |X n ω| ≤ rate n} ≥ 1 - δ) :
    ∀ ε : Real, 0 < ε →
      Tendsto (fun n => P {ω | |X n ω| > ε}) atTop (𝓝 0) := by
  intro ε hε
  let E : Nat → Set Ω := fun n => {ω | |X n ω| ≤ rate n}
  have hcompl :
      Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0) :=
    tendsto_measure_compl_zero_of_forall_eventually_ge_one_sub P E hgood_meas hgood_prob
  rw [ENNReal.tendsto_nhds_zero] at hcompl ⊢
  intro δ hδ
  have hrate_eventually : ∀ᶠ n in atTop, rate n < ε := by
    have hball : ∀ᶠ n in atTop, rate n ∈ Metric.ball (0 : Real) ε :=
      hrate.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [hball] with n hn
    have habs : |rate n| < ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hn
    exact (abs_lt.mp habs).2
  filter_upwards [hcompl δ hδ, hrate_eventually] with n hcompl_le hrate_lt
  calc
    P {ω | |X n ω| > ε} ≤ P (E n)ᶜ := by
      refine measure_mono ?_
      intro ω hbad hgood
      have hlt : |X n ω| < ε := lt_of_le_of_lt hgood hrate_lt
      exact (not_lt_of_ge hlt.le) hbad
    _ ≤ δ := hcompl_le
