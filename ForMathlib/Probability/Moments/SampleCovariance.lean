/-
Staged for Mathlib: sample-covariance eigenvalue concentration.

Specializes the generic random-Hermitian eigenvalue-concentration engine
(`MatrixConcentration.lean`) to the empirical covariance
`Cov̂_{kl}(ω) = n⁻¹ Σᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ` of iid random vectors, via the scalar
sample-mean second-moment identity applied to the coordinate products.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Probability.Moments.MatrixConcentration
import ForMathlib.Probability.Moments.SampleMean

open scoped Matrix ENNReal
open MeasureTheory ProbabilityTheory

namespace ForMathlib

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The empirical covariance matrix of the vectors `V₀, …, V_{n-1}` at outcome
`ω`: `Cov̂_{kl}(ω) = n⁻¹ Σᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ`. -/
noncomputable def sampleCovariance {n d : ℕ}
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => (n : ℝ)⁻¹ * ∑ i, V i ω k * V i ω l

/-- **Per-entry second-moment bound for the sample covariance.**  Applying the
scalar sample-mean second-moment identity to the coordinate products
`Yᵢ = Vᵢ(·)ₖ Vᵢ(·)ₗ`, the `(k,l)` entry of `Cov̂ − Cov` has mean-square `≤ v / n`. -/
theorem integral_sq_sampleCovariance_entry_le {n d : ℕ} (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (Cov : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d)
    (hL2 : ∀ i, MemLp (fun ω => V i ω k * V i ω l) 2 P)
    (hmean : ∀ i, ∫ ω, V i ω k * V i ω l ∂P = Cov k l)
    (hindep : Set.Pairwise (Set.univ : Set (Fin n))
      fun i j => IndepFun (fun ω => V i ω k * V i ω l) (fun ω => V j ω k * V j ω l) P)
    (hident : ∀ i, ∫ ω, ‖V i ω k * V i ω l - Cov k l‖ ^ 2 ∂P
        = ∫ ω, ‖V ⟨0, hn⟩ ω k * V ⟨0, hn⟩ ω l - Cov k l‖ ^ 2 ∂P)
    {v : ℝ} (hv : ∫ ω, ‖V ⟨0, hn⟩ ω k * V ⟨0, hn⟩ ω l - Cov k l‖ ^ 2 ∂P ≤ v) :
    ∫ ω, (sampleCovariance V ω k l - Cov k l) ^ 2 ∂P ≤ (n : ℝ)⁻¹ * v := by
  have key := integral_norm_sq_average_sub_of_iid P hn
    (fun i ω => V i ω k * V i ω l) (Cov k l) hL2 hmean hindep hident
  have hrw : ∫ ω, (sampleCovariance V ω k l - Cov k l) ^ 2 ∂P
      = ∫ ω, ‖(n : ℝ)⁻¹ • (∑ i, V i ω k * V i ω l) - Cov k l‖ ^ 2 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [sampleCovariance, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  rw [hrw, key]
  have hv_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hv hv_nonneg

omit [MeasurableSpace Ω] in
/-- The empirical covariance matrix is symmetric (Hermitian over `ℝ`). -/
theorem isHermitian_sampleCovariance {n d : ℕ}
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    (sampleCovariance V ω).IsHermitian := by
  ext k l
  show star (sampleCovariance V ω l k) = sampleCovariance V ω k l
  simp only [sampleCovariance, star_trivial]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- **Sample-covariance eigenvalue lower bound (high probability).**  Given a
per-entry mean-square bound `v` for `Σ̂ − Σ` (e.g. `v = σ²/n` from
`integral_sq_sampleCovariance_entry_le` under iid coordinates), with probability
`≥ 1 − d² v / η²` every sorted eigenvalue of the empirical covariance `Σ̂(ω)`
exceeds the corresponding eigenvalue of the population covariance `Σ` minus
`d · η`.  Taking `η = c / (2d)` keeps a population eigenvalue floored at `c`
above `c / 2` with high probability — the eigengap the DKPS `halign` route needs. -/
theorem measure_forall_sampleCovariance_sortedEig_ge_ge {n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (Cov : Matrix (Fin d) (Fin d) ℝ) (hCovHerm : Cov.IsHermitian)
    (hVmeas : ∀ i (k : Fin d), Measurable fun ω => V i ω k)
    (hint : ∀ k l, Integrable (fun ω => (sampleCovariance V ω k l - Cov k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η)
    (hmoment : ∀ k l, ∫ ω, (sampleCovariance V ω k l - Cov k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin d,
        Matrix.sortedEig hCovHerm k - (d : ℝ) * η ≤ Matrix.sortedEig (isHermitian_sampleCovariance V ω) k}
      ≥ 1 - ENNReal.ofReal ((d : ℝ) ^ 2 * v / η ^ 2) := by
  have hmeas : ∀ k l : Fin d, Measurable fun ω => sampleCovariance V ω k l := by
    intro k l
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ fun i _ => (hVmeas i k).mul (hVmeas i l)
  exact measure_forall_sortedEig_ge_ge P (sampleCovariance V) Cov
    (isHermitian_sampleCovariance V) hCovHerm hmeas hint hη hmoment

end ForMathlib
