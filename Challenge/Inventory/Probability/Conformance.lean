/-
# AIQ DKPS ForMathlib inventory challenge: Probability, moments, and concentration

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`
-/
/-
Staged for Mathlib: additions to
`Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Measurability-free complement bound for probability measures

For a probability measure, `1 - μ sᶜ ≤ μ s` for an **arbitrary** set `s`.

Mathlib's `prob_compl_eq_one_sub₀` requires `NullMeasurableSet s` and
`prob_compl_le_one_sub_of_le_prob` requires `MeasurableSet s`; this lemma needs
nothing, because subadditivity `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ` holds for outer
measures.  This is the form in which high-probability events are consumed when
converting vanishing failure probabilities into convergence statements, where
the event sets are often not (easily) measurable.
-/

namespace ForMathlib

open MeasureTheory
open scoped ENNReal

/--
For a probability measure, `1 - μ sᶜ ≤ μ s`, with no measurability assumption
on `s`: subadditivity gives `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ`.
-/
theorem one_sub_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) : 1 - μ sᶜ ≤ μ s := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Probability/Moments/Variance.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Probability/Moments/Variance.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Uncentered second-moment Chebyshev inequality

`P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2)` from `∫ Y² ≤ v`, for a real
random variable `Y` that need not be centered, nonnegative, or measurable
(integrability of `Y ^ 2` suffices).

Mathlib's `meas_ge_le_variance_div_sq` is the centered version and requires
`MemLp Y 2`; concentration arguments routinely need the raw second-moment form
below, applied to error norms `Y = ‖Xᵢ - μᵢ‖`.
-/

namespace ForMathlib

open MeasureTheory

/--
**Uncentered second-moment Chebyshev.**  If `∫ Y² ≤ v` and `0 < η`, then
`P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2)`.  No measurability of `Y` is
required beyond integrability of `Y ^ 2`.
-/
theorem meas_gt_le_ofReal_integral_sq_div_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY_int : Integrable (fun ω => Y ω ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∫ ω, Y ω ^ 2 ∂P ≤ v) :
    P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Probability/Moments/SampleMean.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Probability/Moments/` (new file
`SampleMean.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Mean-squared error of the sample mean

For a sample `X 0, …, X (r-1)` of square-integrable random vectors valued in a
finite-dimensional real inner product space, with common mean `μ`, the
mean-squared error of the sample mean `r⁻¹ ∑ₖ Xₖ` about `μ` is `r⁻²` times the
sum of the individual mean-squared errors:

`∫ ‖r⁻¹ ∑ₖ Xₖ − μ‖² = r⁻² ∑ₖ ∫ ‖Xₖ − μ‖²`.

Only **pairwise** independence and a **common mean** are needed; the cross terms
vanish by independence (no identical-distribution hypothesis). Specialized to an
identically-distributed sample this is the classical `trace(Σ) / r` rate, and an
upper bound on each individual error gives the `γ / r` decay used throughout
concentration arguments.

Mathlib's `ProbabilityTheory.variance` is `ℝ`-valued; the covariance API in
`Mathlib/Probability/Moments/CovarianceBilin.lean` has no trace identity and no
sample-mean lemmas. The scalar engine here is `IndepFun.variance_sum`; the work
is the coordinatewise reduction over an orthonormal basis.

## Main results

* `ForMathlib.integral_sq_scaledSum_sub_of_pairwise_indep`: scalar identity
  `∫ (r⁻¹ ∑ₖ Zₖ − c)² = r⁻² ∑ₖ ∫ (Zₖ − c)²` for pairwise-independent,
  common-mean real random variables.
* `ForMathlib.integral_norm_sq_average_sub_eq_sum`: the vector identity above on
  a finite-dimensional real inner product space.
* `ForMathlib.integral_norm_sq_average_sub_of_iid`: identically-distributed
  collapse to `r⁻¹ ∫ ‖X 0 − μ‖²`.
* `ForMathlib.integral_norm_sq_average_sub_le_of_bound`: the `γ / r` bound.
-/

namespace ForMathlib

open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/--
**Scalar variance-of-the-mean identity.** For pairwise-independent,
square-integrable real random variables `Z 0, …, Z (r-1)` sharing a common mean
`c` (each `∫ Z k = c`), the second moment of the scaled sum about `c` is `r⁻²`
times the sum of the per-variable second moments about `c`:

`∫ (r⁻¹ ∑ₖ Zₖ − c)² = r⁻² ∑ₖ ∫ (Zₖ − c)²`.

The common-mean hypothesis is genuinely needed: without centring each `Z k` at
`c` an extra bias term `(E[mean] − c)²` appears. The proof routes through
`ProbabilityTheory.variance` (which absorbs the centring) and
`ProbabilityTheory.IndepFun.variance_sum`.
-/
theorem integral_sq_scaledSum_sub_of_pairwise_indep
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (Z : Fin r → Ω → ℝ) (c : ℝ)
    (hL2 : ∀ k, MemLp (Z k) 2 P)
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = c)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (Z i) (Z j) P) :
    ∫ ω, ((r : ℝ)⁻¹ * (∑ k, Z k ω) - c) ^ 2 ∂P
      = (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, (Z k ω - c) ^ 2 ∂P := by
  sorry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/--
**Mean-squared error of the sample mean (additive form).**

Let `X : Fin r → Ω → E` be pairwise-independent, square-integrable random
vectors in a finite-dimensional real inner product space, with common mean
`μ` (each Bochner integral `∫ X k = μ`). Then the mean-squared error of the
sample mean equals `r⁻²` times the sum of the individual mean-squared errors:

`∫ ‖r⁻¹ ∑ₖ Xₖ − μ‖² = r⁻² ∑ₖ ∫ ‖Xₖ − μ‖²`.

Only pairwise independence and identical centring are required (not identical
distribution); the cross terms vanish by independence. The proof reduces
coordinatewise via `stdOrthonormalBasis` to the scalar identity
`integral_sq_scaledSum_sub_of_pairwise_indep`.
-/
theorem integral_norm_sq_average_sub_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
  sorry
theorem integral_norm_sq_average_sub_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P = ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : ℝ)⁻¹ * ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P := by
  sorry
theorem integral_norm_sq_average_sub_le_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    {γ : ℝ} (hbound : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P ≤ γ) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P ≤ γ / r := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
-/
/-
Staged for Mathlib: additions to
`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Convergence in measure from a vanishing high-probability rate

A standard way to consume concentration inequalities: if for each index `i` the
deviation `edist (f i x) (g x)` exceeds some deterministic `rate i` only on a
set of small measure, and `rate` tends to `0`, then `f` tends to `g` in
measure.  This is how "with high probability, the error is at most `rate i`"
statements are converted into `MeasureTheory.TendstoInMeasure`.

No measurability is required of the exceptional sets, since the squeeze only
uses monotonicity of the (outer) measure; the index runs along an arbitrary
filter, matching the generality of `MeasureTheory.TendstoInMeasure`.

## Main results

* `ForMathlib.tendstoInMeasure_of_tendsto_measure_rate_lt_edist`: the `edist`
  form, for an `ℝ≥0∞`-valued rate and a target with an extended distance.
* `ForMathlib.tendstoInMeasure_of_tendsto_measure_rate_lt_dist`: the `dist`
  form, for a real-valued rate and a pseudometric target.
* `ForMathlib.tendstoInMeasure_of_tendsto_measure_dist_le_rate`: the
  high-probability phrasing for a probability measure, with hypothesis
  `μ {x | dist (f i x) (g x) ≤ rate i} → 1`; here null-measurability of the
  good events is genuinely needed, since an outer measure can assign full
  measure to both a set and its complement.
-/

namespace ForMathlib

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}

/--
If `f i` is within `rate i` of `g` outside a set whose measure tends to `0`,
and `rate` tends to `0`, then `f` tends to `g` in measure.

This is the form in which concentration inequalities ("with high probability,
`edist (f i x) (g x) ≤ rate i`") are consumed.  No measurability of the
exceptional sets is needed: the proof only uses monotonicity of the measure.
-/
theorem tendstoInMeasure_of_tendsto_measure_rate_lt_edist [EDist E]
    {f : ι → α → E} {g : α → E} {rate : ι → ℝ≥0∞} (hrate : Tendsto rate l (𝓝 0))
    (h : Tendsto (fun i => μ {x | rate i < edist (f i x) (g x)}) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  sorry
theorem tendstoInMeasure_of_tendsto_measure_rate_lt_dist [PseudoMetricSpace E]
    {f : ι → α → E} {g : α → E} {rate : ι → ℝ} (hrate : Tendsto rate l (𝓝 0))
    (h : Tendsto (fun i => μ {x | rate i < dist (f i x) (g x)}) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  sorry
theorem tendstoInMeasure_of_tendsto_measure_dist_le_rate [PseudoMetricSpace E]
    [IsProbabilityMeasure μ] {f : ι → α → E} {g : α → E} {rate : ι → ℝ}
    (hrate : Tendsto rate l (𝓝 0))
    (hmeas : ∀ i, NullMeasurableSet {x | dist (f i x) (g x) ≤ rate i} μ)
    (hprob : Tendsto (fun i => μ {x | dist (f i x) (g x) ≤ rate i}) l (𝓝 1)) :
    TendstoInMeasure μ f l g := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Probability/Moments/MatrixConcentration.lean`
-/
/-
Staged for Mathlib: eigenvalue concentration for a random Hermitian matrix from
per-entry second-moment control (the elementary, no-matrix-Bernstein route:
entrywise Chebyshev + union bound, then entrywise → operator-norm → Weyl).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


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
  sorry
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
  sorry
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
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Probability/Moments/SampleCovariance.lean`
-/
/-
Staged for Mathlib: sample-covariance eigenvalue concentration.

Specializes the generic random-Hermitian eigenvalue-concentration engine
(`MatrixConcentration.lean`) to the empirical covariance
`Cov̂_{kl}(ω) = n⁻¹ Σᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ` of iid random vectors, via the scalar
sample-mean second-moment identity applied to the coordinate products.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


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
  sorry
/-!
`ForMathlib.isHermitian_sampleCovariance` and
`ForMathlib.measure_forall_sampleCovariance_sortedEig_ge_ge` are intentionally
excluded from this inventory for now. They come from the newest sample-covariance
concentration staging work, and the current conformance wrapper is not yet
comparator-exact for the Hermitian witness used by the sorted-eigenvalue theorem.
They should be reintroduced after statement/API review.
-/
end ForMathlib
