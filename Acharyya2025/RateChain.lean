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
`cmdsEntrywiseRate n m R η = 16 R n² m⁻¹ · η` linear in `η = t u`.  Since
`configBound n d α Λ ε` is, for small `ε`, dominated by its linear-in-`ε`
Davis–Kahan term `√n · d · ε / √(α/2)` (the polar term is `O(ε²)` and the
commutator term `O(ε)`), the formal rate is
`poly(n, d, m⁻¹, R, Λ, 1/α) · √(γ / r(u))` — matching the paper's `r^{−1/2+δ}`
dependence (the `δ`-loss is exactly the Chebyshev slack `1/δ'` above) and a
polynomial constant in the structural parameters.  What differs is bookkeeping:
the formal constant is the deliberately loose product of the proved chain
constants (`2n²/m` from the ℓ²→ℓ¹ Frobenius step, `8R` from the
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

Internal helper (probability bookkeeping toward Corollary 2's "with high
probability" statements).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProbAtTop_of_tendsto_compl_zero
    {Ω : Type} [MeasurableSpace Ω]                       -- EXTRA: measurable-space structure
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]  -- EXTRA: each `P u` is a probability measure
    (E : Nat → Set Ω)
    (h : Tendsto (fun u => P u ((E u)ᶜ)) atTop (𝓝 0))   -- complement probabilities vanish
    -- Conclusion: `E` is a high-probability event family.
    :
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

Internal helper (the probabilistic input to the rate chain): produces the
high-probability uniform response-mean event that feeds the aligned pipeline.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProb_uniformResponseMeanClose_of_secondMoment
    {Ω : Type} [MeasurableSpace Ω]                       -- EXTRA: measurable-space structure
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]  -- EXTRA: each `P u` is a probability measure
    {n m p : Nat}
    (Xbar : Nat → Ω → Fin n → Mat m p)                  -- sample mean responses
    (μ : Fin n → Mat m p)                               -- population means
    (σ2 : Nat → Real)                                   -- per-model second-moment bound (cf. γ/r)
    (t : Nat → Real)                                    -- closeness level
    -- EXTRA (measurability-flavored): integrability of the squared errors, consumed by Chebyshev.
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)  -- second-moment bound holds
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0))  -- vanishing Chebyshev ratio
    -- Conclusion: the uniform response-mean closeness event holds with high probability.
    :
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

Internal helper (analytic ingredient for the vanishing-rate lemma).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Conclusion: the spectral bound is continuous in its perturbation argument `ε`.
theorem continuous_configBound (n d : Nat) (α Λ : Real) :
    Continuous (fun ε : Real => configBound n d α Λ ε) := by
  unfold configBound
  fun_prop

/--
The capstone spectral bound vanishes at `ε = 0`: every summand of
`configBound n d α Λ ε` carries a factor of `ε` or `ε²`.

Internal helper (analytic ingredient for the vanishing-rate lemma).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Conclusion: the spectral bound is `0` at zero perturbation.
theorem configBound_zero (n d : Nat) (α Λ : Real) :
    configBound n d α Λ 0 = 0 := by
  simp [configBound]

/--
**Vanishing of the spectral bound.**  `configBound n d α Λ ε → 0` as `ε → 0`
(plain two-sided neighborhood; no sign or positivity hypotheses are needed
because Lean's division-by-zero and `Real.sqrt`-of-negative conventions keep
the formula continuous and zero at `ε = 0` unconditionally).

Vanishing-rate lemma (toward Corollary 2): the deterministic spectral bound
shrinks to `0` as the perturbation shrinks.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Conclusion: `configBound … ε → 0` as `ε → 0`.
theorem tendsto_configBound_zero (n d : Nat) (α Λ : Real) :
    Tendsto (fun ε => configBound n d α Λ ε) (𝓝 0) (𝓝 0) := by
  simpa [configBound_zero n d α Λ] using
    (continuous_configBound n d α Λ).tendsto 0

/--
Sequence corollary: along any vanishing rate sequence `e u → 0`, the capstone
spectral bound vanishes: `configBound n d α Λ (e u) → 0`.

Vanishing-rate lemma (toward Corollary 2): sequence form of the above.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem tendsto_configBound_comp_zero (n d : Nat) (α Λ : Real)
    {e : Nat → Real} (he : Tendsto e atTop (𝓝 0))  -- the perturbation sequence vanishes
    -- Conclusion: the spectral bound along that sequence vanishes.
    :
    Tendsto (fun u => configBound n d α Λ (e u)) atTop (𝓝 0) :=
  (tendsto_configBound_zero n d α Λ).comp he

/-! ### (3) The end-to-end rate -/

/--
**An explicit (loose-constant) end-to-end rate** of the aligned DKPS spectral
estimator: the deterministic spectral bound `configBound` evaluated at the
operator-norm proxy
`n · cmdsEntrywiseRate n m R (t u)`, where `t u` is the uniform response-mean
closeness level, `R` the uniform dissimilarity bound, and
`cmdsEntrywiseRate n m R η = 4 · (2R) · n² · m⁻¹ · 2η` the proved entrywise
CMDS-matrix rate.  This is literally the bound produced by
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean`
specialized to a constant dissimilarity bound `R`.

This is the named rate sequence that plays the role of the paper's
`Poly₃((n³/r)^{1/2−δ})` bound (see the file header for the constant-by-constant
comparison); Corollary 2 is the statement that it vanishes as the budget grows.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
noncomputable def endToEndRate (n m d : Nat) (α Λ R : Real) (t : Nat → Real) :
    Nat → Real :=
  fun u => configBound n d α Λ ((n : Real) * cmdsEntrywiseRate n m R (t u))

/--
**End-to-end rate theorem.**  Under per-model second-moment bounds `σ2 u`
(uniform over models) with vanishing Chebyshev ratio `n · σ2 u / (t u)² → 0`,
and under the spectral hypotheses on the population CMDS matrix
(PSD, rank ≤ `d`, eigenvalue floor `α` on the top-`d` block, cap `Λ`, Gram
realization `ψ`, a vanishing CMDS perturbation rate, and a uniform dissimilarity
bound `R`), the aligned spectral estimator's `ConfigError` against the
population configuration `ψ` is high-probability bounded by the EXPLICIT rate
`endToEndRate n m d α Λ R t u`.

This composes the Chebyshev union bound
(`highProb_uniformResponseMeanClose_of_secondMoment`) with the proved aligned
pipeline (`highProb_aligned_configError_of_response_mean`); the spectral
hypotheses are threaded through verbatim with the dissimilarity bound
specialized to the constant `R`.

This is a loose-constant, explicit-rate high-probability bound *corresponding to*
Theorem 2, with the rate named (`endToEndRate`); paired with
`tendsto_endToEndRate_zero` below it yields a vanishing-rate (Corollary-2-style)
"for any κ > 0, with high probability eventually" statement.  Note the constants
are deliberately non-sharp and the spectral hypotheses appear as explicit
side-conditions, so this is an analogue of Theorem 2 / Corollary 2, not a
verbatim formalization of them.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProb_aligned_configError_endToEndRate
    {Ω : Type} [MeasurableSpace Ω]                       -- EXTRA: measurable-space structure
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]  -- EXTRA: each `P u` is a probability measure
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)           -- EXTRA: finite embedding dim `d ≤ n`, nonempty index set
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)  -- sample mean responses vs population means
    -- Spectral structure of the population CMDS Gram matrix (Assumptions 1/2):
    (hB : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).PosSemidef)      -- PSD
    (hrank : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).rank ≤ d)     -- rank ≤ d
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)  -- eigenvalue floor α on top-d block
    (hΛ : ∀ l, MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)  -- eigenvalue cap Λ
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k)
      = classicalMDSMatrix (responseDist μ) i j)  -- ψ is a Gram factor of the population CMDS matrix
    (t : Nat → Real) (R : Real) (σ2 : Nat → Real)  -- closeness level, constant dissimilarity bound, second-moment bound
    -- EXTRA (measurability-flavored): integrability of the squared errors.
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)  -- second-moment bound
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0))  -- vanishing Chebyshev ratio (cf. r = ω(n³))
    -- Rate side-conditions.  The local spectral smallness inequalities are
    -- automatic eventually from the vanishing scaled perturbation rate.
    (hrate_nonneg : ∀ u, 0 ≤ cmdsEntrywiseRate n m R (t u))
    (hrate_zero : Tendsto
      (fun u => (n : Real) * cmdsEntrywiseRate n m R (t u)) atTop (𝓝 0))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R)  -- uniform dissimilarity bound (sample)
    (hpopulation_bound : ∀ i j, |responseDist μ i j| ≤ R) :         -- uniform dissimilarity bound (population)
    -- Conclusion (explicit-rate Theorem 2): with high probability the aligned
    -- estimator's `ConfigError` against `ψ` is `≤ endToEndRate …`.
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
    hrate_nonneg hrate_zero hmean hsample_bound
    (fun _u i j => hpopulation_bound i j)

/-- Canonical population-realization form of the explicit end-to-end rate
theorem.

The population CMDS configuration and its Gram proof are synthesized from the
PSD/rank hypotheses, so the public assumptions now match the structural matrix
conditions actually used by the spectral pipeline. -/
theorem highProb_aligned_configError_endToEndRate_canonical
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
    (t : Nat → Real) (R : Real) (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0))
    (hrate_nonneg : ∀ u, 0 ≤ cmdsEntrywiseRate n m R (t u))
    (hrate_zero : Tendsto
      (fun u => (n : Real) * cmdsEntrywiseRate n m R (t u)) atTop (𝓝 0))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R)
    (hpopulation_bound : ∀ i j, |responseDist μ i j| ≤ R) :
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfigCanonical hd
          (fun u ω => responseDist (Xbar u ω))
          (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar u ω))
          (responseDist μ) hB hrank (endToEndRate n m d α Λ R t) u ω)
        (canonicalCMDSConfig (responseDist μ) hB hrank)
        ≤ endToEndRate n m d α Λ R t u}) := by
  exact highProb_aligned_configError_endToEndRate P hn hd Xbar μ hB hrank
    hα_pos hfloor hΛ (canonicalCMDSConfig (responseDist μ) hB hrank)
    (canonicalCMDSConfig_gram_eq (responseDist μ) hB hrank)
    t R σ2 hint hσ2 ht_pos hratio hrate_nonneg hrate_zero
    hsample_bound hpopulation_bound

/-! ### (4) Consistency corollary -/

/--
**Consistency of the end-to-end rate.**  If the response-mean closeness level
vanishes (`t u → 0`), then the explicit end-to-end rate vanishes:
`endToEndRate n m d α Λ R t u → 0`.

The inner rate `n · cmdsEntrywiseRate n m R (t u)` is linear in `t u` (constant
`16 R n³ / m`), so it vanishes with `t`; composing with
`tendsto_configBound_comp_zero` finishes.  No sign conditions on `R, Λ, α` are
needed (the bound is continuous and zero-at-zero unconditionally).

This is the vanishing-rate side of **Corollary 2**: as the response-mean
closeness level shrinks (which the paper achieves by growing the per-model
response count `r = ω(n³)`), the explicit end-to-end bound tends to `0`, so any
target accuracy `κ > 0` is eventually met with high probability.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem tendsto_endToEndRate_zero (n m d : Nat) (α Λ R : Real)
    {t : Nat → Real} (ht : Tendsto t atTop (𝓝 0))  -- the closeness level vanishes (cf. growing budget)
    -- Conclusion (Corollary 2, rate side): the explicit end-to-end bound vanishes.
    :
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


/-! ### End-to-end rate with a canonical spectral ceiling -/

/-- The end-to-end rate specialized to the canonical largest-eigenvalue ceiling
of the population CMDS matrix. -/
noncomputable def endToEndRateTopEigenvalue
    {n : Nat} (hn : 0 < n)
    (m d : Nat) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    (α R : Real) (t : Nat → Real) : Nat → Real :=
  endToEndRate n m d α (MatrixPerturbation.topEigenvalue hn hB) R t

/-- The explicit end-to-end theorem with the upper spectral ceiling discharged
by the leading population eigenvalue. -/
theorem highProb_aligned_configError_endToEndRate_topEigenvalue
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)
    (hB : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).rank ≤ d)
    {α : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k)
      = classicalMDSMatrix (responseDist μ) i j)
    (t : Nat → Real) (R : Real) (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0))
    (hrate_nonneg : ∀ u, 0 ≤ cmdsEntrywiseRate n m R (t u))
    (hrate_zero : Tendsto
      (fun u => (n : Real) * cmdsEntrywiseRate n m R (t u)) atTop (𝓝 0))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R)
    (hpopulation_bound : ∀ i j, |responseDist μ i j| ≤ R) :
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfig hd (fun u ω => responseDist (Xbar u ω))
          (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar u ω))
          ψ (endToEndRateTopEigenvalue hn m d hB α R t) u ω) ψ
        ≤ endToEndRateTopEigenvalue hn m d hB α R t u}) := by
  exact highProb_aligned_configError_endToEndRate P hn hd Xbar μ hB hrank
    hα_pos hfloor (MatrixPerturbation.sortedEigenvalues_le_topEigenvalue hn hB)
    ψ hψ t R σ2 hint hσ2 ht_pos hratio hrate_nonneg hrate_zero
    hsample_bound hpopulation_bound

/-- Canonical population realization and canonical upper spectral ceiling for
the explicit end-to-end rate theorem. -/
theorem highProb_aligned_configError_endToEndRate_canonical_topEigenvalue
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)
    (hB : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).rank ≤ d)
    {α : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (t : Nat → Real) (R : Real) (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μ i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μ i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (ht_pos : ∀ u, 0 < t u)
    (hratio : Tendsto (fun u => (n : Real) * σ2 u / (t u) ^ 2) atTop (𝓝 0))
    (hrate_nonneg : ∀ u, 0 ≤ cmdsEntrywiseRate n m R (t u))
    (hrate_zero : Tendsto
      (fun u => (n : Real) * cmdsEntrywiseRate n m R (t u)) atTop (𝓝 0))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R)
    (hpopulation_bound : ∀ i j, |responseDist μ i j| ≤ R) :
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfigCanonical hd
          (fun u ω => responseDist (Xbar u ω))
          (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar u ω))
          (responseDist μ) hB hrank
          (endToEndRateTopEigenvalue hn m d hB α R t) u ω)
        (canonicalCMDSConfig (responseDist μ) hB hrank)
        ≤ endToEndRateTopEigenvalue hn m d hB α R t u}) := by
  exact highProb_aligned_configError_endToEndRate_canonical P hn hd Xbar μ hB hrank
    hα_pos hfloor (MatrixPerturbation.sortedEigenvalues_le_topEigenvalue hn hB)
    t R σ2 hint hσ2 ht_pos hratio hrate_nonneg hrate_zero
    hsample_bound hpopulation_bound

/-- The canonically capped end-to-end rate still vanishes whenever the
response-mean tolerance vanishes. -/
theorem tendsto_endToEndRateTopEigenvalue_zero
    {n : Nat} (hn : 0 < n) (m d : Nat)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    (α R : Real) {t : Nat → Real} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (endToEndRateTopEigenvalue hn m d hB α R t) atTop (𝓝 0) := by
  exact tendsto_endToEndRate_zero n m d α
    (MatrixPerturbation.topEigenvalue hn hB) R ht

end Acharyya2025.RateChain
