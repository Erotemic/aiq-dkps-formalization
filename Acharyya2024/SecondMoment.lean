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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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
      = (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, (Z k ω - μc) ^ 2 ∂P := by
  classical
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast hr.ne'
  -- The scaled sum has mean `μc`.
  have hmean_sum : P[fun ω => (r : Real)⁻¹ * (∑ k, Z k ω)] = μc := by
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [hmean]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · exact fun k _ => (hL2 k).integrable one_le_two
  -- Measurability of the scaled sum.
  have hmeasS : AEMeasurable (fun ω => (r : Real)⁻¹ * (∑ k, Z k ω)) P := by
    refine AEMeasurable.const_mul ?_ _
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin r))
      (fun k _ => (hL2 k).aemeasurable)
    have heq : (fun ω => ∑ k, Z k ω) = (∑ i : Fin r, Z i) := by
      ext ω; simp [Finset.sum_apply]
    rw [heq]; exact h
  -- LHS is the variance of the scaled sum (since its mean is `μc`).
  have hLHS : ∫ ω, ((r : Real)⁻¹ * (∑ k, Z k ω) - μc) ^ 2 ∂P
      = variance (fun ω => (r : Real)⁻¹ * (∑ k, Z k ω)) P := by
    rw [variance_eq_integral hmeasS, hmean_sum]
  rw [hLHS]
  -- Pull out the scalar.
  rw [variance_const_mul]
  -- Variance of a sum of pairwise-independent variables is the sum of variances.
  have hvarsum : variance (fun ω => ∑ k, Z k ω) P = ∑ k, variance (Z k) P := by
    have hsum := IndepFun.variance_sum (X := Z) (s := Finset.univ)
      (fun i _ => hL2 i)
      (fun i _ j _ hij => hindep (Set.mem_univ i) (Set.mem_univ j) hij)
    rw [← hsum]
    congr 1
    ext ω
    simp [Finset.sum_apply]
  rw [hvarsum]
  -- Each variance is the second moment about `μc`.
  have hvark : ∀ k, variance (Z k) P = ∫ ω, (Z k ω - μc) ^ 2 ∂P := by
    intro k
    rw [variance_eq_integral (hL2 k).aemeasurable, hmean k]
  simp_rw [hvark]

/--
Per-coordinate independence of `EuclideanSpace`-valued samples follows from joint
independence by composing with the coordinate projection.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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

/--
**Main second-moment identity (additive form).**

Let `X : Fin r → Ω → EuclideanSpace ℝ ι` be jointly independent, square-integrable
response vectors with common mean `μ : EuclideanSpace ℝ ι` (each coordinate
`∫ X k ω c = μ c`).  Then the mean-squared error of the sample mean equals `r⁻²`
times the sum of the individual mean-squared errors:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P = r⁻² Σₖ ∫ ‖Xₖ − μ‖² ∂P.

This needs only pairwise independence and identical centring (not identical
distribution); the cross terms vanish by independence.  The proof reduces
coordinatewise to `integral_sq_scaled_sum_sub_of_pairwise_indep`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι]
    {r : Nat} (hr : 0 < r)
    (X : Fin r → Ω → EuclideanSpace Real ι)
    (μ : EuclideanSpace Real ι)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)
    (hindep : iIndepFun X P) :
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
  classical
  -- Per-coordinate square-integrability of `X k`.
  have hL2c : ∀ (k : Fin r) (c : ι), MemLp (fun ω => X k ω c) 2 P := by
    intro k c
    have := (hL2 k).continuousLinearMap_comp
      (EuclideanSpace.proj c : EuclideanSpace Real ι →L[Real] Real)
    simpa using this
  -- Per-coordinate integrability of the deviation square (for the `∫ Σ_c = Σ_c ∫` swap).
  have hintc : ∀ c : ι, Integrable
      (fun ω => ((r : Real)⁻¹ * (∑ k, X k ω c) - μ c) ^ 2) P := by
    intro c
    have hsum : MemLp (fun ω => (r : Real)⁻¹ * (∑ k, X k ω c) - μ c) 2 P := by
      have h1 : MemLp (fun ω => ∑ k, X k ω c) 2 P :=
        memLp_finsetSum (Finset.univ : Finset (Fin r)) (fun k _ => hL2c k c)
      exact (h1.const_mul _).sub (memLp_const (μ c))
    exact hsum.integrable_sq
  -- Reduce the LHS norm-square integral to a sum over coordinates.
  have hpt : ∀ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2
      = ∑ c : ι, ((r : Real)⁻¹ * (∑ k, X k ω c) - μ c) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro c _
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    rw [PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  -- Reduce the RHS per-sample norm-square integral to a sum over coordinates.
  have hptk : ∀ (k : Fin r) (ω : Ω), ‖X k ω - μ‖ ^ 2
      = ∑ c : ι, (X k ω c - μ c) ^ 2 := by
    intro k ω
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro c _
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  -- Per-sample integrability of `(X k c - μ c)²` (for the `∫ Σ_c = Σ_c ∫` swap).
  have hintkc : ∀ (k : Fin r) (c : ι),
      Integrable (fun ω => (X k ω c - μ c) ^ 2) P := by
    intro k c
    exact ((hL2c k c).sub (memLp_const (μ c))).integrable_sq
  calc
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
        = ∫ ω, ∑ c : ι, ((r : Real)⁻¹ * (∑ k, X k ω c) - μ c) ^ 2 ∂P := by
          simp_rw [hpt]
    _ = ∑ c : ι, ∫ ω, ((r : Real)⁻¹ * (∑ k, X k ω c) - μ c) ^ 2 ∂P := by
          rw [integral_finsetSum]; exact fun c _ => hintc c
    _ = ∑ c : ι, (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, (X k ω c - μ c) ^ 2 ∂P := by
          apply Finset.sum_congr rfl
          intro c _
          exact integral_sq_scaled_sum_sub_of_pairwise_indep P hr
            (fun k ω => X k ω c) (μ c) (fun k => hL2c k c)
            (fun k => hmean k c) (pairwise_indep_coord P X hindep c)
    _ = (r : Real)⁻¹ ^ 2 * ∑ c : ι, ∑ k, ∫ ω, (X k ω c - μ c) ^ 2 ∂P := by
          rw [Finset.mul_sum]
    _ = (r : Real)⁻¹ ^ 2 * ∑ k, ∑ c : ι, ∫ ω, (X k ω c - μ c) ^ 2 ∂P := by
          rw [Finset.sum_comm]
    _ = (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [← integral_finsetSum]
          · apply integral_congr_ae
            exact Eventually.of_forall fun ω => (hptk k ω).symm
          · exact fun c _ => hintkc k c

/--
**iid corollary (equality form).**

If in addition the per-sample mean-squared errors are identical
(`∫ ‖X k − μ‖² = ∫ ‖X 0 − μ‖²` for all `k`, automatic for an iid sample), the
additive identity collapses to the paper's `trace(Σ)/r` rate:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P = r⁻¹ · ∫ ‖X 0 − μ‖² ∂P.

Requires `0 < r` (the scaling collapses the `r⁻²·r` to `r⁻¹`).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι]
    {r : Nat} (hr : 0 < r)
    (X : Fin r → Ω → EuclideanSpace Real ι)
    (μ : EuclideanSpace Real ι)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)
    (hindep : iIndepFun X P)
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean_le_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι]
    {r : Nat} (hr : 0 < r)
    (X : Fin r → Ω → EuclideanSpace Real ι)
    (μ : EuclideanSpace Real ι)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)
    (hindep : iIndepFun X P)
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
