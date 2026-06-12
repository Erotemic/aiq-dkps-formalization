/-
General lemmas used by the Acharyya et al. 2024 formalization.

This file is intentionally paper-agnostic: results that are useful outside DKPS
belong here first, so they can later be moved toward Mathlib if they are not
already present there in a comparable form.
-/

import Mathlib
import ForMathlib.MeasureTheory.Function.ConvergenceInMeasure

open scoped BigOperators Topology
open Filter MeasureTheory

/--
Standard fact (elementary normed-space inequality). Changing both endpoints of a
distance changes the distance by at most the sum of the two endpoint
perturbations: `| ‖x-y‖ - ‖x₀-y₀‖ | ≤ ‖x-x₀‖ + ‖y-y₀‖`.

This is the normed-additive-group form of the elementary estimate used in the
paper's Appendix A.2 before applying Markov's inequality.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub
    {E : Type*} [SeminormedAddCommGroup E]
    (x y x₀ y₀ : E) :
    -- Conclusion: a perturbation of both endpoints perturbs the distance by at
    -- most the sum of the two endpoint perturbations.
    |‖x - y‖ - ‖x₀ - y₀‖| ≤ ‖x - x₀‖ + ‖y - y₀‖ := by
  have h₁ : |‖x - y‖ - ‖x₀ - y₀‖| ≤ ‖(x - y) - (x₀ - y₀)‖ :=
    abs_norm_sub_norm_le (x - y) (x₀ - y₀)
  have h₂ : ‖(x - y) - (x₀ - y₀)‖ ≤ ‖x - x₀‖ + ‖y - y₀‖ := by
    have hrewrite : (x - y) - (x₀ - y₀) = (x - x₀) - (y - y₀) := by
      abel
    simpa [hrewrite] using norm_sub_le (x - x₀) (y - y₀)
  exact h₁.trans h₂

/--
Standard fact. A scaled version of
`abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub` for a nonnegative scalar `c`
(here used with the `1/m` factor of the paper's dissimilarity entry).

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_mul_norm_sub_sub_le_mul_norm_sub_add
    {E : Type*} [SeminormedAddCommGroup E]
    {c : Real} (hc : 0 ≤ c) (x y x₀ y₀ : E) :  -- `hc`: the scalar is nonnegative
    -- Conclusion: the scaled distance perturbation is at most `c` times the sum
    -- of the endpoint perturbations.
    |c * ‖x - y‖ - c * ‖x₀ - y₀‖| ≤ c * (‖x - x₀‖ + ‖y - y₀‖) := by
  have h :
      |c * ‖x - y‖ - c * ‖x₀ - y₀‖|
        = c * |‖x - y‖ - ‖x₀ - y₀‖| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (abs_norm_sub_norm_sub_le_norm_sub_add_norm_sub x y x₀ y₀) hc

/--
Standard fact. The finite `ℓ²` norm of a real-valued function is bounded by its
`ℓ¹` norm. Used to pass from a Frobenius (`ℓ²`) bound to an entrywise-sum
(`ℓ¹`) bound on the dissimilarity matrices.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (f : ι → Real) :
    -- Conclusion: the `ℓ²` norm of `f` is at most its `ℓ¹` norm.
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
    (hE_meas : ∀ n, MeasurableSet (E n))   -- measurability of the good events
    -- (extra technical hypothesis, not stated in the paper)
    (hE_prob :                             -- good events eventually have prob ≥ 1-δ
      ∀ δ : ENNReal, 0 < δ → ∃ N : Nat, ∀ n > N, P (E n) ≥ 1 - δ) :
    -- Conclusion: the bad events (complements) have probability tending to zero.
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
    -- measurability of the good events (extra technical hypothesis, not in the paper)
    (hgood_meas : ∀ n, MeasurableSet {ω | |X n ω| ≤ rate n})
    (hrate : Tendsto rate atTop (𝓝 0))   -- the deterministic rate vanishes
    (hgood_prob :                         -- and holds with high probability
      ∀ δ : ENNReal, 0 < δ → ∃ N : Nat, ∀ n > N,
        P {ω | |X n ω| ≤ rate n} ≥ 1 - δ) :
    -- Conclusion: `Xₙ → 0` in probability (bad-event probabilities vanish for every ε).
    ∀ ε : Real, 0 < ε →
      Tendsto (fun n => P {ω | |X n ω| > ε}) atTop (𝓝 0) := by
  -- The complements of the good events have vanishing probability.
  have hcompl : Tendsto (fun n => P {ω | |X n ω| ≤ rate n}ᶜ) atTop (𝓝 0) :=
    tendsto_measure_compl_zero_of_forall_eventually_ge_one_sub P _ hgood_meas hgood_prob
  -- Rewrite them as the exceptional sets of the staged general lemma.
  have hbad : Tendsto (fun n => P {ω | rate n < dist (X n ω) 0}) atTop (𝓝 0) := by
    refine hcompl.congr fun n => ?_
    congr 1
    ext ω
    simp [not_le]
  -- Apply the staged Mathlib candidate: convergence in measure to `0`.
  have htim : TendstoInMeasure P X atTop (fun _ => (0 : Real)) :=
    ForMathlib.tendstoInMeasure_of_tendsto_measure_rate_lt_dist hrate hbad
  -- Extract the bad-event probabilities at a fixed threshold `ε`.
  intro ε hε
  have hclosed := (MeasureTheory.tendstoInMeasure_iff_dist.mp htim) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hclosed
    (fun n => zero_le) fun n => measure_mono fun ω hω => ?_
  simpa [Real.dist_0_eq_abs] using hω.le
