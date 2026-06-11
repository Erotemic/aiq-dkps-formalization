/-
Probability step for the fixed-model / growing-query regime of

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel
perspective space"
arXiv:2409.17308, Theorem 2 and Appendix A.2.

This file proves the TRUE, paper-faithful probabilistic step that
`Acharyya2024.Consistency.growing_queries_dissimilarity_converges` only sketches
(that theorem is stated without hypotheses and is false as written). Here we make
the second-moment hypothesis explicit: if the per-model mean-squared response
errors `E‖Xbar(r) i − μ i‖²` are bounded by `v r → 0`, then the Frobenius
distance between the empirical and population response-dissimilarity matrices
converges to zero in probability.

The proof chains:
  * a Chebyshev/Markov inequality (`meas_gt_le_ofReal_secondMoment_div_sq`),
  * a finite union bound over the `Fin n` models, and
  * the deterministic Appendix A.2 reduction
    `frobSub_responseDist_le_of_uniform_errors` from `Acharyya2024.Common`.

No `axiom`, no `sorry`.
-/

import Acharyya2024.Common

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2024.Probability

open Acharyya2024

variable {Ω : Type} [MeasurableSpace Ω]

/--
Chebyshev/Markov inequality in second-moment form, packaged for `ENNReal`.

For a nonnegative measurable function `Y` with `∫ Y² ≤ v` and `0 < η`,
the probability of `{ω | η < Y ω}` is at most `ENNReal.ofReal (v / η²)`.

The proof applies `mul_meas_ge_le_integral_of_nonneg` to `Y²` at level `η²`,
uses `{η < Y} ⊆ {η² ≤ Y²}`, and converts the resulting real-valued measure
bound to `ENNReal` using that `P` is a probability measure.

Formalized by Claude Opus 4.8.
-/
theorem meas_gt_le_ofReal_secondMoment_div_sq
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → Real}
    (hY_int : Integrable (fun ω => (Y ω) ^ 2) P)
    {v η : Real} (hη : 0 < η) (hmoment : ∫ ω, (Y ω) ^ 2 ∂P ≤ v) :
    P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  -- Markov on Y² at level η².
  have hsq_nonneg : 0 ≤ᵐ[P] fun ω => (Y ω) ^ 2 :=
    Eventually.of_forall fun ω => sq_nonneg (Y ω)
  have hmarkov :
      η ^ 2 * P.real {ω | η ^ 2 ≤ (Y ω) ^ 2} ≤ ∫ ω, (Y ω) ^ 2 ∂P :=
    mul_meas_ge_le_integral_of_nonneg hsq_nonneg hY_int (η ^ 2)
  -- The bad set is contained in the squared-threshold set.
  have hsubset : {ω | η < Y ω} ⊆ {ω | η ^ 2 ≤ (Y ω) ^ 2} := by
    intro ω hω
    have : η < Y ω := hω
    exact pow_le_pow_left₀ hη.le this.le 2
  have hηsq_pos : 0 < η ^ 2 := by positivity
  -- Real-valued bound on P.real of the bad set.
  have hbad_real :
      P.real {ω | η < Y ω} ≤ v / η ^ 2 := by
    have hmono : P.real {ω | η < Y ω} ≤ P.real {ω | η ^ 2 ≤ (Y ω) ^ 2} :=
      measureReal_mono hsubset
    have h1 : η ^ 2 * P.real {ω | η < Y ω} ≤ ∫ ω, (Y ω) ^ 2 ∂P := by
      refine le_trans ?_ hmarkov
      exact mul_le_mul_of_nonneg_left hmono hηsq_pos.le
    have h2 : η ^ 2 * P.real {ω | η < Y ω} ≤ v := h1.trans hmoment
    rw [le_div_iff₀ hηsq_pos]
    calc P.real {ω | η < Y ω} * η ^ 2
          = η ^ 2 * P.real {ω | η < Y ω} := by ring
      _ ≤ v := h2
  -- Convert to ENNReal.
  have hne_top : P {ω | η < Y ω} ≠ ⊤ := measure_ne_top P _
  calc P {ω | η < Y ω}
        = ENNReal.ofReal (P.real {ω | η < Y ω}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal hne_top]
    _ ≤ ENNReal.ofReal (v / η ^ 2) :=
          ENNReal.ofReal_le_ofReal hbad_real

/--
Main probabilistic theorem (paper Theorem 2 / Appendix A.2).

Let `Xbar r ω : Fin n → Mat m p` be sample-average response matrices and
`μ : Fin n → Mat m p` the population means. If each per-model mean-squared error
`∫ ‖Xbar r ω i − μ i‖² ∂P` is bounded by `v r` with `v r → 0`, then the Frobenius
distance between the empirical and population response-dissimilarity matrices
converges to `0` in probability.

The second-moment bound `hmoment` is the only probabilistic hypothesis; in the
paper it is established by the iid variance/trace computation `v r = (1/r)·Σγ`.
We take it as a hypothesis to separate the concentration step from the variance
algebra.

Formalized by Claude Opus 4.8.
-/
theorem dissimilarity_convergesInProbability_of_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n m p : Nat}
    (Xbar : Nat → Ω → Fin n → Mat m p)
    (μ : Fin n → Mat m p)
    (hmeas : ∀ r i, Measurable (fun ω => Xbar r ω i))
    (v : Nat → Real)
    (hint : ∀ r i, Integrable (fun ω => ‖Xbar r ω i - μ i‖ ^ 2) P)
    (hmoment : ∀ r i, ∫ ω, ‖Xbar r ω i - μ i‖ ^ 2 ∂P ≤ v r)
    (hv : Tendsto v atTop (𝓝 0)) :
    ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) (responseDist μ)) := by
  classical
  intro ε hε
  -- Reduce the metric goal to a measure-of-bad-set statement.
  -- dist (frobSub ...) 0 = |frobSub ... - 0| = frobSub ... (it is a sqrt, ≥ 0).
  have hfrob_nonneg : ∀ r ω,
      0 ≤ frobSub (responseDist (Xbar r ω)) (responseDist μ) := by
    intro r ω; exact Real.sqrt_nonneg _
  -- Rewrite the bad set into the clean `{ε < frobSub}` form.
  have hset_eq : ∀ r,
      {ω | dist (frobSub (responseDist (Xbar r ω)) (responseDist μ)) (0 : Real) > ε}
        = {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)} := by
    intro r
    ext ω
    simp only [Set.mem_setOf_eq, dist_zero_right, Real.norm_eq_abs, gt_iff_lt,
      abs_of_nonneg (hfrob_nonneg r ω)]
  -- Degenerate case n = 0: frobSub is sqrt of an empty sum = 0 < ε, bad set empty.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hzero : ∀ r ω, frobSub (responseDist (Xbar r ω)) (responseDist μ) = 0 := by
      intro r ω
      simp [frobSub, frob, frobSq]
    have : ∀ r,
        {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)} = (∅ : Set Ω) := by
      intro r; ext ω
      simp only [hzero r ω, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    simp only [hset_eq, this]
    simp only [measure_empty]
    exact tendsto_const_nhds
  -- Degenerate case m = 0: (m:ℝ)⁻¹ = 0, so both dissimilarity matrices are 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hzero : ∀ r ω, frobSub (responseDist (Xbar r ω)) (responseDist μ) = 0 := by
      intro r ω
      simp [frobSub, frob, frobSq, responseDist, responseDistEntry]
    have : ∀ r,
        {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)} = (∅ : Set Ω) := by
      intro r; ext ω
      simp only [hzero r ω, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    simp only [hset_eq, this]
    simp only [measure_empty]
    exact tendsto_const_nhds
  -- Main (nondegenerate) case.
  -- Per-model threshold: if ‖Xbar r ω i − μ i‖ ≤ η for all i then frobSub ≤ ε.
  set η : Real := ε * (m : Real) / (2 * (n : Real) * (n : Real)) with hη_def
  have hn_pos : (0 : Real) < (n : Real) := by exact_mod_cast hnpos
  have hm_pos : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hη_pos : 0 < η := by
    rw [hη_def]; positivity
  -- The deterministic reduction: uniform error η gives frobSub ≤ ε.
  have hdet : ∀ r ω,
      (∀ i : Fin n, ‖Xbar r ω i - μ i‖ ≤ η) →
        frobSub (responseDist (Xbar r ω)) (responseDist μ) ≤ ε := by
    intro r ω hbound
    have hle := frobSub_responseDist_le_of_uniform_errors (Xbar r ω) μ hbound
    refine hle.trans ?_
    have hval : ((n : Real) * (n : Real)) * (((m : Real))⁻¹ * (2 * η)) = ε := by
      rw [hη_def]
      field_simp
    exact hval.le
  -- Chebyshev for each per-model error.
  have hcheb : ∀ (r : Nat) (i : Fin n),
      P {ω | η < ‖Xbar r ω i - μ i‖} ≤ ENNReal.ofReal (v r / η ^ 2) := by
    intro r i
    exact meas_gt_le_ofReal_secondMoment_div_sq P
      (hint r i) hη_pos (hmoment r i)
  -- The bad event is contained in the union of per-model bad events.
  have hincl : ∀ r : Nat,
      {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)}
        ⊆ ⋃ i : Fin n, {ω | η < ‖Xbar r ω i - μ i‖} := by
    intro r ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
    exact absurd (hdet r ω hnot) (not_le.mpr hω)
  -- Union bound.
  have hbad : ∀ r : Nat,
      P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)}
        ≤ (n : ENNReal) * ENNReal.ofReal (v r / η ^ 2) := by
    intro r
    calc
      P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)}
          ≤ P (⋃ i : Fin n, {ω | η < ‖Xbar r ω i - μ i‖}) :=
            measure_mono (hincl r)
      _ ≤ ∑ i : Fin n, P {ω | η < ‖Xbar r ω i - μ i‖} :=
            measure_iUnion_fintype_le (μ := P)
              (fun i => {ω | η < ‖Xbar r ω i - μ i‖})
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (v r / η ^ 2) :=
            Finset.sum_le_sum fun i _ => hcheb r i
      _ = (n : ENNReal) * ENNReal.ofReal (v r / η ^ 2) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- The upper bound tends to zero.
  have hub : Tendsto (fun r => (n : ENNReal) * ENNReal.ofReal (v r / η ^ 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => v r / η ^ 2) atTop (𝓝 0) := by
      simpa using hv.div_const (η ^ 2)
    have h2 : Tendsto (fun r => ENNReal.ofReal (v r / η ^ 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ENNReal.Tendsto.const_mul h2
      (Or.inr (ENNReal.natCast_ne_top n))
    simpa using h3
  -- Squeeze.
  have hsqueeze :
      Tendsto (fun r =>
        P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)})
        atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun r => zero_le _) hbad
  simpa only [hset_eq] using hsqueeze

end Acharyya2024.Probability
