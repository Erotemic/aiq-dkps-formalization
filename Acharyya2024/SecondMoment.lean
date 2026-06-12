/-
Second-moment (variance/trace) algebra for the iid sample mean, supplying the
hypothesis that the probabilistic step of

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel
perspective space"
arXiv:2409.17308, Appendix A.2 (and the finite-sample companion
arXiv:2511.08307, Theorem 1) consume.

The downstream concentration theorem
`Acharyya2024.Probability.dissimilarity_convergesInProbability_of_secondMoment`
needs a bound `∫ ‖X̄(r)ᵢ − μᵢ‖² ∂P ≤ v r` with `v r → 0`.  For an iid (or merely
pairwise-independent, identically-centered, square-integrable) sample
`X₀, …, X_{r-1}` of `EuclideanSpace ℝ ι`-valued responses with mean `μ`, the
paper establishes this via the elementary variance identity

  E ‖(1/r) Σₖ Xₖ − μ‖² = (1/r) · E ‖X − μ‖²    ("trace(Σ)/r" in paper notation),

where `E ‖X − μ‖² = trace(cov X)`.  This file proves that identity (and the
additive generalization that does not assume identical distribution) and the
`≤ γ/r` bound the Acharyya chain actually consumes.

This file is paper-agnostic variance algebra: a plausible Mathlib contribution
candidate near `Mathlib/Probability/Moments/Variance.lean`.  The scalar engine is
Mathlib's `ProbabilityTheory.IndepFun.variance_sum`; the work here is the
coordinatewise reduction on `EuclideanSpace`.

No `axiom`, no `sorry`.
-/

import Mathlib
import ForMathlib.Probability.Moments.SampleMean

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Acharyya2024.SecondMoment

variable {Ω : Type} [MeasurableSpace Ω]

/--
Scalar variance-of-the-mean identity.

For pairwise-independent, square-integrable real random variables `Z 0, …, Z (r-1)`
with a *common* mean `μc` (each `∫ Z k = μc`), the second moment of the scaled
sum about `μc` is `r⁻²` times the sum of the per-variable second moments about
`μc`:

  ∫ (r⁻¹ Σₖ Zₖ − μc)² = r⁻² Σₖ ∫ (Zₖ − μc)².

The common-mean hypothesis is genuinely needed: without centring each `Z k` at
`μc` an extra bias term `(E[mean] − μc)²` appears.  The proof routes through
Mathlib's `variance` (which absorbs the centring) and
`ProbabilityTheory.IndepFun.variance_sum`.

This is now a thin wrapper around the Mathlib-staged
`ForMathlib.integral_sq_scaledSum_sub_of_pairwise_indep`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_sq_scaled_sum_sub_of_pairwise_indep
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : Nat} (hr : 0 < r)
    (Z : Fin r → Ω → Real)
    (μc : Real)
    (hL2 : ∀ k, MemLp (Z k) 2 P)
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = μc)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (Z i) (Z j) P) :
    ∫ ω, ((r : Real)⁻¹ * (∑ k, Z k ω) - μc) ^ 2 ∂P
      = (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, (Z k ω - μc) ^ 2 ∂P :=
  ForMathlib.integral_sq_scaledSum_sub_of_pairwise_indep P hr Z μc hL2 hmean hindep

/--
Per-coordinate independence of `EuclideanSpace`-valued samples follows from joint
independence by composing with the coordinate projection.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem pairwise_indep_coord
    (P : Measure Ω)
    {ι : Type} [Fintype ι]
    {r : Nat} (X : Fin r → Ω → EuclideanSpace Real ι)
    (hindep : iIndepFun X P) (c : ι) :
    Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (fun ω => X i ω c) (fun ω => X j ω c) P := by
  intro i _ j _ hij
  have hmeas : Measurable (fun x : EuclideanSpace Real ι => x c) :=
    (EuclideanSpace.proj c : EuclideanSpace Real ι →L[Real] Real).continuous.measurable
  exact (hindep.indepFun hij).comp hmeas hmeas

/-- Coordinate-wise common mean upgrades to a Bochner common mean for an
integrable `EuclideanSpace`-valued sample.  Used to feed the coordinate-mean
paper statements into the Mathlib-staged Bochner-mean theorems. -/
private theorem bochner_mean_of_coord
    (P : Measure Ω) {ι : Type} [Fintype ι]
    (Y : Ω → EuclideanSpace Real ι) (μ : EuclideanSpace Real ι)
    (hint : Integrable Y P) (hmean : ∀ c, ∫ ω, Y ω c ∂P = μ c) :
    ∫ ω, Y ω ∂P = μ := by
  ext c
  have h : (EuclideanSpace.proj c : EuclideanSpace Real ι →L[Real] Real) (∫ ω, Y ω ∂P)
      = ∫ ω, Y ω c ∂P :=
    (ContinuousLinearMap.integral_comp_comm _ hint).symm
  rw [hmean c] at h
  exact h

/--
**Main second-moment identity (additive form).**

Let `X : Fin r → Ω → EuclideanSpace ℝ ι` be pairwise-independent,
square-integrable response vectors with common mean `μ : EuclideanSpace ℝ ι`
(each coordinate `∫ X k ω c = μ c`).  Then the mean-squared error of the sample
mean equals `r⁻²` times the sum of the individual mean-squared errors:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P = r⁻² Σₖ ∫ ‖Xₖ − μ‖² ∂P.

Only pairwise independence and identical centring are needed (not identical
distribution); the cross terms vanish by independence.  The proof upgrades the
coordinate means to a Bochner mean (`bochner_mean_of_coord`) and applies the
Mathlib-staged `ForMathlib.integral_norm_sq_average_sub_eq_sum`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι]
    {r : Nat} (hr : 0 < r)
    (X : Fin r → Ω → EuclideanSpace Real ι)
    (μ : EuclideanSpace Real ι)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P) :
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
  -- Bridge the paper's coordinate-mean hypotheses to the Mathlib-staged abstract
  -- theorem (only pairwise independence and a Bochner mean are needed).
  have hbm : ∀ k, ∫ ω, X k ω ∂P = μ :=
    fun k => bochner_mean_of_coord P (X k) μ ((hL2 k).integrable one_le_two)
      (fun c => hmean k c)
  exact ForMathlib.integral_norm_sq_average_sub_eq_sum P hr X μ hL2 hbm hindep

/--
**iid corollary (equality form).**

If in addition the per-sample mean-squared errors are identical
(`∫ ‖X k − μ‖² = ∫ ‖X 0 − μ‖²` for all `k`, automatic for an iid sample), the
additive identity collapses to the paper's `trace(Σ)/r` rate:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P = r⁻¹ · ∫ ‖X 0 − μ‖² ∂P.

Requires `0 < r` (the scaling collapses the `r⁻²·r` to `r⁻¹`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι]
    {r : Nat} (hr : 0 < r)
    (X : Fin r → Ω → EuclideanSpace Real ι)
    (μ : EuclideanSpace Real ι)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P
      = ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P) :
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : Real)⁻¹ * ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P := by
  rw [integral_norm_sq_sampleMean_sub_mean_eq_sum P hr X μ hL2 hmean hindep]
  simp_rw [hident]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/--
**Bound consumed by the Acharyya concentration chain.**

If each per-sample mean-squared error is bounded by `γ` (in the paper,
`γ = trace(Σ)`), then the sample-mean mean-squared error decays at rate `γ/r`:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P ≤ γ / r.

This is exactly the `v r = γ/r → 0` hypothesis of
`Acharyya2024.Probability.dissimilarity_convergesInProbability_of_secondMoment`.
Requires `0 < r`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean_le_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι]
    {r : Nat} (hr : 0 < r)
    (X : Fin r → Ω → EuclideanSpace Real ι)
    (μ : EuclideanSpace Real ι)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    {γ : Real}
    (hbound : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P ≤ γ) :
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P ≤ γ / r := by
  rw [integral_norm_sq_sampleMean_sub_mean_eq_sum P hr X μ hL2 hmean hindep]
  have hr0 : (0 : Real) < (r : Real) := by exact_mod_cast hr
  -- Sum of per-sample second moments is ≤ r·γ.
  have hsum_le : (∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P) ≤ (r : Real) * γ := by
    calc (∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P)
          ≤ ∑ _k : Fin r, γ := Finset.sum_le_sum fun k _ => hbound k
      _ = (r : Real) * γ := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Multiply by `r⁻² ≥ 0` and simplify `r⁻² · r · γ = γ / r`.
  have hinv_nonneg : (0 : Real) ≤ (r : Real)⁻¹ ^ 2 := by positivity
  calc (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P
        ≤ (r : Real)⁻¹ ^ 2 * ((r : Real) * γ) :=
          mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
    _ = γ / r := by
          rw [sq, mul_assoc, inv_mul_cancel_left₀ hr0.ne', div_eq_inv_mul]

end Acharyya2024.SecondMoment
