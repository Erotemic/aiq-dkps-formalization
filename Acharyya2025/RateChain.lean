/-
End-to-end RATE bookkeeping for the Acharyya et al. 2025 DKPS concentration
chain (arXiv:2511.08307).

Every qualitative link of the chain is already proved
(`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean`);
this file makes the rate explicit and proves it vanishes:

* Chebyshev + union bound turn per-model second-moment bounds `σ2 u` into the
  high-probability uniform response-mean event at level `t u`, provided
  `n · σ2 u / (t u)² → 0` (`highProb_uniformResponseMeanClose_of_secondMoment`);
* the capstone spectral bound `configBound n d α Λ ε` is continuous in `ε` and
  vanishes at `ε = 0` (`tendsto_configBound_zero`), so it vanishes along any
  vanishing rate sequence (`tendsto_configBound_comp_zero`);
* composing the two through the aligned pipeline gives the explicit end-to-end
  rate `endToEndRate n m d α Λ R t u
    = configBound n d α Λ (n · cmdsEntrywiseRate n m R (t u))`
  (`highProb_aligned_configError_endToEndRate`), which tends to `0` whenever
  `t u → 0` (`tendsto_endToEndRate_zero`).

**Comparison with the paper's rate.**  The paper states the embedding error as
`Poly₃((n³/r)^{1/2−δ})` for a degree-3 polynomial `Poly₃` in the problem
constants, where `r = r(u)` is the per-model response count.  In the formal
chain, taking `σ2 u = γ / r(u)` (the iid trace bound proved in
`Acharyya2024.SecondMoment.integral_norm_sq_sampleMean_sub_mean_le_of_bound`)
and a closeness level `t u ~ √(n · σ2 u) / δ' = √(n γ / r(u)) / δ'`, the
Chebyshev hypothesis `n · σ2 u / (t u)² = δ'² → 0` holds along any `δ' → 0`
slow enough, and the resulting bound is
`configBound n d α Λ (n · cmdsEntrywiseRate n m R (t u))` with
`cmdsEntrywiseRate n m R η = 8 R n² m⁻¹ · η` linear in `η = t u`.  Since
`configBound n d α Λ ε` is, for small `ε`, dominated by its linear-in-`ε`
Davis–Kahan term `√n · d · ε / √(α/2)` (the polar term is `O(ε²)` and the
commutator term `O(ε)`), the formal rate is
`poly(n, d, m⁻¹, R, Λ, 1/α) · √(γ / r(u))` — matching the paper's `r^{−1/2+δ}`
dependence (the `δ`-loss is exactly the Chebyshev slack `1/δ'` above) and a
polynomial constant in the structural parameters.  What differs is bookkeeping:
the formal constant is the deliberately loose product of the proved chain
constants (`n²` from the ℓ²→ℓ¹ Frobenius step, `8R/m` from the
squaring/centering step, `√n` from `ConfigError ≤ √n‖·‖_F`), not the paper's
optimized `Poly₃(n³)` aggregation, and the formal statement quantifies the
spectral hypotheses (floor `α`, cap `Λ`, rank ≤ `d`, smallness, polar) as
explicit per-`u` side conditions rather than absorbing them asymptotically.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import ForMathlib.MeasureTheory.Measure.Typeclasses.Probability
import Acharyya2024.Probability
import Acharyya2025.AlignedPipeline

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2025.RateChain

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.AlignedPipeline
open Acharyya2025.Bridge

/-! ### (0) HighProbAtTop from vanishing complement measure -/

/--
If the measures `P u` are probability measures and the complement measures
`P u ((E u)ᶜ)` tend to `0`, then `E` is a high-probability event family.

No measurability of `E u` is needed: subadditivity gives
`1 = P u (E u ∪ (E u)ᶜ) ≤ P u (E u) + P u ((E u)ᶜ)`, hence
`P u (E u) ≥ 1 − P u ((E u)ᶜ)` by `ENNReal` truncated-subtraction arithmetic.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProbAtTop_of_tendsto_compl_zero
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    (E : Nat → Set Ω)
    (h : Tendsto (fun u => P u ((E u)ᶜ)) atTop (𝓝 0)) :
    HighProbAtTop P E := by
  intro δ hδ
  have hev : ∀ᶠ u in atTop, P u ((E u)ᶜ) < δ := h.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun u hu => ?_⟩
  have hcompl : P u ((E u)ᶜ) ≤ δ := (hN u (le_of_lt hu)).le
  -- Measurability-free complement bound, staged for Mathlib.
  have h1 : (1 : ENNReal) - δ ≤ 1 - P u ((E u)ᶜ) := tsub_le_tsub_left hcompl 1
  exact h1.trans (ForMathlib.one_sub_measure_compl_le (P u) (E u))

/-! ### (1) Chebyshev → uniform high-probability response-mean event -/

/--
**Chebyshev → uniform HP event.**  Per-model second-moment bounds
`∫ ‖X̄ᵤ ᵢ − μᵢ‖² ≤ σ2 u` (uniform over the `n` models) turn into the
high-probability uniform response-mean event at closeness level `t u`, provided
the Chebyshev ratio `n · σ2 u / (t u)²` tends to `0`.

The proof is the union bound `P(∃ i, ‖X̄ᵢ − μᵢ‖ > t) ≤ Σᵢ P(‖X̄ᵢ − μᵢ‖ > t)
≤ n · σ2 u / (t u)²` with the per-coordinate Chebyshev/Markov inequality
`Acharyya2024.Probability.meas_gt_le_ofReal_secondMoment_div_sq`, then
`highProbAtTop_of_tendsto_compl_zero`.  The only measurability-flavored
hypothesis is the integrability `hint` of the squared errors (which carries
`AEStronglyMeasurable` and is what Chebyshev consumes); no `Measurable Xbar` or
`MeasurableSet` hypothesis is needed because the `HighProbAtTop` conversion is
measurability-free.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProb_uniformResponseMeanClose_of_secondMoment
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {n m p : Nat}
    (Xbar : Nat → Ω → Fin n → Mat m p)
    (μ : Fin n → Mat m p)
    (σ2 : Nat → Real)
    (t : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0)) :
    HighProbAtTop P
      (fun u => {ω | UniformResponseMeanClose (Xbar u ω) μ (t u)}) := by
  apply highProbAtTop_of_tendsto_compl_zero
  -- Union bound: the complement measure is at most `n · σ2 u / (t u)²`.
  have hbound : ∀ u,
      P u ({ω | UniformResponseMeanClose (Xbar u ω) μ (t u)})ᶜ
        ≤ ENNReal.ofReal ((n : Real) * σ2 u / (t u) ^ 2) := by
    intro u
    have hincl :
        ({ω | UniformResponseMeanClose (Xbar u ω) μ (t u)})ᶜ
          ⊆ ⋃ i : Fin n, {ω | t u < ‖Xbar u ω i - μ i‖} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
      exact hω (fun i => hnot i)
    have hcheb : ∀ i : Fin n,
        P u {ω | t u < ‖Xbar u ω i - μ i‖}
          ≤ ENNReal.ofReal (σ2 u / (t u) ^ 2) := fun i =>
      Acharyya2024.Probability.meas_gt_le_ofReal_secondMoment_div_sq (P u)
        (hint u i) (ht_pos u) (hσ2 u i)
    calc P u ({ω | UniformResponseMeanClose (Xbar u ω) μ (t u)})ᶜ
        ≤ P u (⋃ i : Fin n, {ω | t u < ‖Xbar u ω i - μ i‖}) :=
          measure_mono hincl
      _ ≤ ∑ i : Fin n, P u {ω | t u < ‖Xbar u ω i - μ i‖} :=
          measure_iUnion_fintype_le (μ := P u)
            (fun i => {ω | t u < ‖Xbar u ω i - μ i‖})
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (σ2 u / (t u) ^ 2) :=
          Finset.sum_le_sum fun i _ => hcheb i
      _ = (n : ENNReal) * ENNReal.ofReal (σ2 u / (t u) ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : Real) * (σ2 u / (t u) ^ 2)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ((n : Real) * σ2 u / (t u) ^ 2) := by
          rw [mul_div_assoc]
  -- The explicit upper bound tends to zero, so squeeze.
  have hub : Tendsto (fun u => ENNReal.ofReal ((n : Real) * σ2 u / (t u) ^ 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hratio
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun u => zero_le) hbound

/-! ### (2) Vanishing of the spectral bound -/

/--
The capstone spectral bound `configBound n d α Λ ε` is continuous in `ε`
(for any fixed `n, d, α, Λ`): it is built from `√`, `+`, `*`, `^2` and division
by the constants `α²` and `√(α/2)`, all continuous.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem continuous_configBound (n d : Nat) (α Λ : Real) :
    Continuous (fun ε : Real => configBound n d α Λ ε) := by
  unfold configBound
  fun_prop

/--
The capstone spectral bound vanishes at `ε = 0`: every summand of
`configBound n d α Λ ε` carries a factor of `ε` or `ε²`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem configBound_zero (n d : Nat) (α Λ : Real) :
    configBound n d α Λ 0 = 0 := by
  simp [configBound]

/--
**Vanishing of the spectral bound.**  `configBound n d α Λ ε → 0` as `ε → 0`
(plain two-sided neighborhood; no sign or positivity hypotheses are needed
because Lean's division-by-zero and `Real.sqrt`-of-negative conventions keep
the formula continuous and zero at `ε = 0` unconditionally).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem tendsto_configBound_zero (n d : Nat) (α Λ : Real) :
    Tendsto (fun ε => configBound n d α Λ ε) (𝓝 0) (𝓝 0) := by
  simpa [configBound_zero n d α Λ] using
    (continuous_configBound n d α Λ).tendsto 0

/--
Sequence corollary: along any vanishing rate sequence `e u → 0`, the capstone
spectral bound vanishes: `configBound n d α Λ (e u) → 0`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem tendsto_configBound_comp_zero (n d : Nat) (α Λ : Real)
    {e : Nat → Real} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun u => configBound n d α Λ (e u)) atTop (𝓝 0) :=
  (tendsto_configBound_zero n d α Λ).comp he

/-! ### (3) The end-to-end rate -/

/--
**The explicit end-to-end rate** of the aligned DKPS spectral estimator: the
capstone spectral bound evaluated at the operator-norm proxy
`n · cmdsEntrywiseRate n m R (t u)`, where `t u` is the uniform response-mean
closeness level, `R` the uniform dissimilarity bound, and
`cmdsEntrywiseRate n m R η = 4 · (2R) · n² · m⁻¹ · 2η` the proved entrywise
CMDS-matrix rate.  This is literally the bound produced by
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean`
specialized to a constant dissimilarity bound `R`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
noncomputable def endToEndRate (n m d : Nat) (α Λ R : Real) (t : Nat → Real) :
    Nat → Real :=
  fun u => configBound n d α Λ ((n : Real) * cmdsEntrywiseRate n m R (t u))

/--
**End-to-end rate theorem.**  Under per-model second-moment bounds `σ2 u`
(uniform over models) with vanishing Chebyshev ratio `n · σ2 u / (t u)² → 0`,
and under the capstone spectral hypotheses on the population CMDS matrix
(PSD, rank ≤ `d`, eigenvalue floor `α` on the top-`d` block, cap `Λ`, Gram
realization `ψ`, per-`u` smallness and polar conditions, uniform dissimilarity
bound `R`), the aligned spectral estimator's `ConfigError` against the
population configuration `ψ` is high-probability bounded by the EXPLICIT rate
`endToEndRate n m d α Λ R t u`.

This composes the Chebyshev union bound
(`highProb_uniformResponseMeanClose_of_secondMoment`) with the proved aligned
pipeline (`highProb_aligned_configError_of_response_mean`); the spectral
hypotheses are threaded through verbatim with the dissimilarity bound
specialized to the constant `R`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProb_aligned_configError_endToEndRate
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)
    (hB : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l, MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k)
      = classicalMDSMatrix (responseDist μ) i j)
    (t : Nat → Real) (R : Real) (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0))
    (hrate_nonneg : ∀ u, 0 ≤ cmdsEntrywiseRate n m R (t u))
    (hsmall : ∀ u, (n : Real) * cmdsEntrywiseRate n m R (t u) ≤ α / 2)
    (hpolar : ∀ u, (d : Real) *
      (4 * (n : Real) * ((n : Real) * cmdsEntrywiseRate n m R (t u))^2 / α^2)
        ≤ 1/2)
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R)
    (hpopulation_bound : ∀ i j, |responseDist μ i j| ≤ R) :
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfig hd (fun u ω => responseDist (Xbar u ω))
          (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar u ω))
          ψ (endToEndRate n m d α Λ R t) u ω) ψ
        ≤ endToEndRate n m d α Λ R t u}) := by
  -- (1): Chebyshev → uniform HP response-mean event at level `t u`.
  have hmean : HighProbAtTop P
      (fun u => {ω | UniformResponseMeanClose (Xbar u ω) μ (t u)}) :=
    highProb_uniformResponseMeanClose_of_secondMoment P Xbar μ σ2 t
      hint hσ2 ht_pos hratio
  -- Aligned pipeline with the constant dissimilarity bound `fun _ => R`;
  -- `endToEndRate` is definitionally the bound it produces.
  exact Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean
    P hn hd Xbar μ hB hrank hα_pos hfloor hΛ ψ hψ t (fun _ => R)
    hrate_nonneg hsmall hpolar hmean hsample_bound
    (fun _u i j => hpopulation_bound i j)

/-! ### (4) Consistency corollary -/

/--
**Consistency of the end-to-end rate.**  If the response-mean closeness level
vanishes (`t u → 0`), then the explicit end-to-end rate vanishes:
`endToEndRate n m d α Λ R t u → 0`.

The inner rate `n · cmdsEntrywiseRate n m R (t u)` is linear in `t u` (constant
`16 R n³ / m`), so it vanishes with `t`; composing with
`tendsto_configBound_comp_zero` finishes.  No sign conditions on `R, Λ, α` are
needed (the bound is continuous and zero-at-zero unconditionally).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem tendsto_endToEndRate_zero (n m d : Nat) (α Λ R : Real)
    {t : Nat → Real} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (endToEndRate n m d α Λ R t) atTop (𝓝 0) := by
  -- The inner rate is a constant multiple of `t u`.
  have hkey : ∀ u, (n : Real) * cmdsEntrywiseRate n m R (t u)
      = ((n : Real) * (4 * ((2 * R) * (((n : Real) * (n : Real))
          * ((m : Real)⁻¹ * 2))))) * t u := by
    intro u
    simp only [cmdsEntrywiseRate, responseFrobRate]
    ring
  have hlin : Tendsto (fun u => (n : Real) * cmdsEntrywiseRate n m R (t u))
      atTop (𝓝 0) := by
    simp_rw [hkey]
    simpa using ht.const_mul
      ((n : Real) * (4 * ((2 * R) * (((n : Real) * (n : Real))
        * ((m : Real)⁻¹ * 2)))))
  exact tendsto_configBound_comp_zero n d α Λ hlin

end Acharyya2025.RateChain
