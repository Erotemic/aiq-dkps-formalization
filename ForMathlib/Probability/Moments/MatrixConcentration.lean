/-
Staged for Mathlib: eigenvalue concentration for a random Hermitian matrix from
per-entry second-moment control (the elementary, no-matrix-Bernstein route:
entrywise Chebyshev + union bound, then entrywise → operator-norm → Weyl).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.Matrix.EntrywiseEigenvalue
import ForMathlib.Probability.Moments.Variance

/-! # Eigenvalue concentration of a random Hermitian matrix

For a random real-symmetric `n × n` matrix `Ŝ(ω)` that is entrywise close in
mean-square to a fixed symmetric `A` (`∫ (Ŝ_{kl} − A_{kl})² ≤ v` for every
entry), Chebyshev + a union bound over the `n²` entries give that, with
probability `≥ 1 − n² v / η²`, every entry is within `η`; whence (entrywise
eigenvalue perturbation) every sorted eigenvalue of `Ŝ(ω)` is within `n · η` of
the corresponding eigenvalue of `A`.

This is the elementary route to sample-covariance / empirical-Gram eigenvalue
concentration — no matrix Bernstein/Hoeffding needed (at the cost of the loose
`n`/`n²` constants).

## Main results

* `ForMathlib.measure_exists_entry_gt_le` — entrywise concentration (union bound).
* `ForMathlib.measure_forall_abs_sortedEig_sub_le_ge` — eigenvalue concentration.
-/

open scoped Matrix ENNReal
open MeasureTheory

namespace ForMathlib

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- **Entrywise concentration (union bound).**  If each entry of `Ŝ(ω) − A` has
mean-square `≤ v`, then the probability that *some* entry exceeds `η` in absolute
value is at most `n² v / η²`. -/
theorem measure_exists_entry_gt_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∃ k l, η < |Shat ω k l - A k l|}
      ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  classical
  -- per-entry Chebyshev: P{η < |Ŝ_{kl} − A_{kl}|} ≤ v / η²
  have hcheb : ∀ k l : Fin n,
      P {ω | η < |Shat ω k l - A k l|} ≤ ENNReal.ofReal (v / η ^ 2) := by
    intro k l
    have hint' : Integrable (fun ω => |Shat ω k l - A k l| ^ 2) P := by
      simpa [sq_abs] using hint k l
    have hmoment' : ∫ ω, |Shat ω k l - A k l| ^ 2 ∂P ≤ v := by
      simpa [sq_abs] using hmoment k l
    exact meas_gt_le_ofReal_integral_sq_div_sq P hint' hη hmoment'
  -- the bad event is the finite union over entries
  have hsub : {ω | ∃ k l, η < |Shat ω k l - A k l|}
      = ⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hsub]
  calc P (⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|})
      ≤ ∑ k : Fin n, P (⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ k : Fin n, ∑ l : Fin n, P {ω | η < |Shat ω k l - A k l|} :=
        Finset.sum_le_sum fun k _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, ENNReal.ofReal (v / η ^ 2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hcheb k l
    _ = ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg n), ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        congr 1; ring

/-- **Eigenvalue concentration of a random Hermitian matrix.**  With probability
`≥ 1 − n² v / η²`, every sorted eigenvalue of `Ŝ(ω)` is within `n · η` of the
corresponding eigenvalue of `A`. -/
theorem measure_forall_abs_sortedEig_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l))
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin n,
        |Matrix.sortedEig (hSherm ω) k - Matrix.sortedEig hAherm k| ≤ (n : ℝ) * η}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  -- the good (all-entries-close) event is contained in the eigenvalue event
  have hcontain :
      {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η}
        ⊆ {ω | ∀ k : Fin n,
            |Matrix.sortedEig (hSherm ω) k - Matrix.sortedEig hAherm k| ≤ (n : ℝ) * η} := by
    intro ω hω k
    exact Matrix.abs_sortedEig_sub_le_of_entry_le hAherm (hSherm ω)
      (fun i j => hω i j) k
  -- the bad (some-entry-far) event, bounded above
  have hbad : P {ω | ∃ k l, η < |Shat ω k l - A k l|}
      ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) :=
    measure_exists_entry_gt_le P Shat A hint hη hmoment
  -- the good event is the complement of the bad event, and is measurable
  have hbad_meas : MeasurableSet {ω | ∃ k l, η < |Shat ω k l - A k l|} := by
    have : {ω | ∃ k l, η < |Shat ω k l - A k l|}
        = ⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [this]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => ?_
    exact measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hmeas k l).sub measurable_const))
  have hcompl : {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η}
      = {ω | ∃ k l, η < |Shat ω k l - A k l|}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hgood : 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)
      ≤ P {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η} := by
    rw [hcompl, prob_compl_eq_one_sub hbad_meas]
    exact tsub_le_tsub_left hbad 1
  exact le_trans hgood (measure_mono hcontain)

/-- **Eigenvalue lower bound for a random Hermitian matrix.**  With probability
`≥ 1 − n² v / η²`, every sorted eigenvalue of `Ŝ(ω)` is at least the corresponding
eigenvalue of `A` minus `n · η`.  (Take `η := c / (2n)` to keep a top-block
eigenvalue floored at `c` above `c / 2`.) -/
theorem measure_forall_sortedEig_ge_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l))
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin n,
        Matrix.sortedEig hAherm k - (n : ℝ) * η ≤ Matrix.sortedEig (hSherm ω) k}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  refine le_trans (measure_forall_abs_sortedEig_sub_le_ge P Shat A hSherm hAherm hmeas hint hη
    hmoment) (measure_mono ?_)
  intro ω hω k
  have hk := abs_le.mp (hω k)
  linarith [hk.1]

end ForMathlib
