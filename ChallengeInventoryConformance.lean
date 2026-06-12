/-
# AIQ DKPS ForMathlib full inventory challenge conformance file

This file imports only Mathlib and mirrors the public theorem surface of the
project's current `ForMathlib` staging library. The theorem bodies are left as
`sorry` so that comparator can check that the project implementation proves the
same declarations.

This is an inventory and calibration challenge, not a proposed single Mathlib PR.
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
## Source: `ForMathlib/Analysis/Matrix/EntrywiseOpNorm.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/PiL2.lean`
(the `ℓ¹ ≤ √card · ℓ²` bound) and `Mathlib/Analysis/Matrix/Normed.lean` (the
entrywise → `ℓ²`-operator-norm bound).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # `ℓ¹`–`ℓ²` and entrywise–operator norm comparisons

Two elementary norm comparisons that are absent from Mathlib (which has the
`ℓ²`-operator-norm API in `Mathlib/Analysis/CStarAlgebra/Matrix.lean` but no
bound of it by the entrywise norm):

* on `EuclideanSpace 𝕜 ι`, `∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖` (Cauchy–Schwarz /
  Chebyshev);
* for a real `n × n` matrix with entries bounded by `ε`, the induced Euclidean
  operator `Matrix.toEuclideanLin A` has `‖A x‖ ≤ n ε ‖x‖`.

## Main results

* `ForMathlib.sum_norm_le_sqrt_card_mul_norm`
* `ForMathlib.norm_toEuclideanLin_le_of_entry_le`

The matrix bound's constant `n` is loose (the Frobenius bound gives `√(card)`);
it is the form produced by an entrywise sup bound and consumed by operator-norm
spectral-perturbation arguments. TODO(RCLike): the matrix bound is stated over
`ℝ`; the `RCLike` generalization is routine (`‖A i j‖`, `RCLike.norm_ofReal`).
-/

namespace ForMathlib

open scoped BigOperators
open Matrix

/--
**`ℓ¹ ≤ √card · ℓ²` on Euclidean space.** For `x : EuclideanSpace 𝕜 ι`,
`∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖`.
-/
theorem sum_norm_le_sqrt_card_mul_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  sorry
theorem norm_toEuclideanLin_le_of_entry_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {ε : ℝ} (hentry : ∀ i j, |A i j| ≤ ε) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  sorry
end ForMathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/Spectrum.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Eigenvector cross-term identity for a perturbation

For symmetric operators `T`, `S` on a finite-dimensional inner product space,
with `u i` the `i`-th eigenvector of `T` (eigenvalue `λ i`) and `v j` the
`j`-th eigenvector of `S` (eigenvalue `μ j`),

`⟪u i, (S - T) (v j)⟫ = (μ j - λ i) * ⟪u i, v j⟫`.

This three-line identity is the seed of every Davis–Kahan-style subspace
perturbation bound: cross terms between well-separated parts of the spectra
are controlled by the perturbation `S - T` divided by the eigenvalue gap.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/--
**Cross-term identity.** The matrix entry of the perturbation `S - T` between
the `i`-th eigenvector of `T` and the `j`-th eigenvector of `S` is the
eigenvalue difference times the overlap of the two eigenvectors.
-/
theorem inner_eigenvectorBasis_map_sub_eigenvectorBasis
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i j : Fin n) :
    ⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hS.eigenvalues hn j - hT.eigenvalues hn i : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
  sorry
end ForMathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/CourantFischer.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Courant–Fischer min-max and Weyl's eigenvalue perturbation inequality

For a symmetric operator `T` on a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ`, Mathlib provides the decreasingly sorted eigenvalues
`LinearMap.IsSymmetric.eigenvalues` together with an orthonormal eigenbasis
`LinearMap.IsSymmetric.eigenvectorBasis`.  This file proves the discrete
Courant–Fischer characterization of these sorted eigenvalues and derives from
it Weyl's eigenvalue perturbation inequality
`|λₖ(T) − λₖ(S)| ≤ ε` whenever `∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`.

## Main results

* `ForMathlib.re_inner_map_self_eq_sum_eigenvalues_mul_sq`: diagonalization of
  the quadratic form, `re ⟪T x, x⟫ = ∑ i, λᵢ * ‖(b.repr x) i‖ ^ 2` in the
  eigenbasis `b` of `T`.
* `ForMathlib.exists_unit_vector_re_inner_le_eigenvalue`: Courant–Fischer,
  upper direction — every subspace of dimension `k + 1` contains a unit vector
  `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`.
* `ForMathlib.forall_unit_vector_eigenvalue_le_re_inner`: Courant–Fischer,
  lower direction — some subspace of dimension `k + 1` satisfies
  `λₖ(T) ≤ re ⟪T x, x⟫` for all unit vectors `x` in it.
* `ForMathlib.abs_eigenvalues_sub_le`: **Weyl's inequality** — the `k`-th
  sorted eigenvalues of two symmetric operators differ by at most an operator
  norm bound on their difference.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Theorem 4.2.6
  (Courant–Fischer) and Theorem 4.3.1 (Weyl).
* R. Bhatia, *Matrix Analysis*, Corollary III.2.6 (Weyl).
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-! ### Spectral subspaces

Given an orthonormal basis `b` and a predicate `p` on the index set, the
subspace spanned by the basis vectors selected by `p`.  We record its dimension
(the number of selected indices) and the key orthogonality fact: a vector in
this subspace has vanishing `b`-coordinates outside `p`. -/

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices `i`
satisfying `p i`. -/
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

/-- A spectral subspace has dimension equal to the number of selected indices. -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  sorry
theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  sorry
variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- The quadratic form `re ⟪T x, x⟫` of a symmetric operator `T` expressed in
its eigenbasis: it is the eigenvalue-weighted sum of the squared norms of the
coordinates of `x`.  This is the diagonalization of the quadratic form.  (For
symmetric `T` the inner product `⟪T x, x⟫` is real, so no information is lost
by taking the real part.) -/
theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  sorry
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  sorry
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  sorry
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  sorry
end ForMathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`DavisKahan.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Davis–Kahan cross-block bound (elementary finite-dimensional form)

For two self-adjoint operators `T`, `S` on a finite-dimensional inner product
space that are close in operator norm, the eigenvectors associated to a
well-separated block of the spectrum are nearly orthogonal across the gap.  This
is the (squared) sin-Θ theorem of Davis and Kahan, in the most elementary
finite-dimensional packaging: a direct consequence of the spectral cross-term
identity `⟪uᵢ, (S − T) v̂ⱼ⟫ = (λ̂ⱼ − λᵢ) ⟪uᵢ, v̂ⱼ⟫` and Parseval, with no
resolvents or contour integrals.

Mathlib has no Davis–Kahan / sin-Θ result; `Analysis/InnerProductSpace/Rayleigh`
covers only the extreme eigenvalues.  The constant here (`n ε² / gap²`) is crude
— the sharp sin-Θ constant is `ε² / gap²` summed over the block — but the result
is self-contained and correct.

## Main results

* `ForMathlib.sum_norm_inner_eigenvectorBasis_map_sub_sq_le`: the total
  cross-energy bound `∑_{i,j} ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖² ≤ n ε²`.
* `ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le`: the Davis–Kahan
  cross-block bound `∑_{i < d, j ≥ d} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ n ε² / gap²`.
* `ForMathlib.sum_norm_sub_spectralProjection_sq_eq` (real): the canonical
  projector form — the squared Frobenius distance between the two rank-`d`
  spectral projectors is `2 ·` the cross-block sum.
* `ForMathlib.sum_norm_sub_spectralProjection_sq_le` (real): the resulting
  `‖P̂ − P‖_F² ≤ 2 n ε² / gap²` sin-Θ bound.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), 315–323.
-/

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/--
**Total cross-energy bound.** With `T`, `S` self-adjoint and close in operator
norm (`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), the sum over all eigenvector pairs of the
squared off-diagonal entries of `S − T` is at most `n ε²`.

For each fixed `j` the inner sum over `i` is `‖(S − T) v̂ⱼ‖²` by Parseval in the
orthonormal eigenbasis of `T`, which is `≤ ε²` since `v̂ⱼ` is a unit vector.
-/
theorem sum_norm_inner_eigenvectorBasis_map_sub_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i : Fin n, ∑ j : Fin n,
      ‖⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜‖ ^ 2
      ≤ (n : ℝ) * ε ^ 2 := by
  sorry
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ (n : ℝ) * ε ^ 2 / gap ^ 2 := by
  sorry
theorem gap_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ}
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      α / 2 ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := by
  sorry
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * (n : ℝ) * ε ^ 2 / α ^ 2 := by
  sorry
section RealProjector

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ}

open scoped RealInnerProductSpace

/-- The orthogonal projection onto the span of the first `d` vectors of an
orthonormal basis `b`, as a linear map `x ↦ ∑_{i < d} ⟪bᵢ, x⟫ • bᵢ`. -/
noncomputable def spectralProjection (b : OrthonormalBasis (Fin m) ℝ F) (d : ℕ) :
    F →ₗ[ℝ] F :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d),
    LinearMap.smulRight ((innerSL ℝ (b i)).toLinearMap) (b i)

omit [FiniteDimensional ℝ F] in
theorem spectralProjection_apply (b : OrthonormalBasis (Fin m) ℝ F) (d : ℕ) (x : F) :
    spectralProjection b d x
      = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d), ⟪b i, x⟫ • b i := by
  sorry
omit [FiniteDimensional ℝ F] in
/-- On a vector of its own basis, the projector keeps it iff its index is `< d`. -/
theorem spectralProjection_apply_self (b : OrthonormalBasis (Fin m) ℝ F) (d : ℕ)
    (k : Fin m) :
    spectralProjection b d (b k) = if (k : ℕ) < d then b k else 0 := by
  sorry
omit [FiniteDimensional ℝ F] in
/--
**Projector form of the Davis–Kahan identity (real).** For two orthonormal bases
`u`, `v` of a finite-dimensional real inner product space and a cutoff `d`, the
squared Frobenius distance between the two rank-`d` spectral projectors (computed
in the `u` basis) is twice the cross-block overlap sum:
`∑ₖ ‖(P_v − P_u) uₖ‖² = 2 · ∑_{i < d} ∑_{j ≥ d} ⟪uᵢ, vⱼ⟫²`.

(The left side `∑ₖ ‖A uₖ‖²` is the Frobenius / Hilbert–Schmidt norm² of
`A = P_v − P_u`, evaluated in the orthonormal basis `u`.)
-/
theorem sum_norm_sub_spectralProjection_sq_eq
    (u v : OrthonormalBasis (Fin m) ℝ F) (d : ℕ) :
    ∑ k, ‖(spectralProjection v d - spectralProjection u d) (u k)‖ ^ 2
      = 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => d ≤ (j : ℕ)), ⟪u i, v j⟫ ^ 2 := by
  sorry
theorem sum_norm_sub_spectralProjection_sq_le {T S : F →ₗ[ℝ] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ F = m)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin m, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : F, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ k, ‖(spectralProjection (hS.eigenvectorBasis hn) d
        - spectralProjection (hT.eigenvectorBasis hn) d) (hT.eigenvectorBasis hn k)‖ ^ 2
      ≤ 2 * ((m : ℝ) * ε ^ 2 / gap ^ 2) := by
  sorry
end RealProjector

end ForMathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Gram matrix rigidity (exact Procrustes)

Two families of vectors in a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ` have equal Gram matrices if and only if they are related by a single
linear isometry equivalence of the ambient space.

This is the rigidity statement underlying *Procrustes alignment* in classical
multidimensional scaling: a configuration recovered from a Gram matrix is
determined exactly up to an orthogonal (unitary) transformation.

## Main results

* `ForMathlib.exists_linearIsometryEquiv_of_inner_eq`: equal pairwise inner
  products yield a linear isometry equivalence mapping one family to the other.
* `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv`: the same
  statement packaged as a characterization of `Matrix.gram` equality.

## References

* R. Sibson, *Studies in the robustness of multidimensional scaling:
  Perturbational analysis of classical scaling*, J. Roy. Statist. Soc. Ser. B
  **41** (1979), 217–229.
* I. Borg and P. J. F. Groenen, *Modern Multidimensional Scaling*, 2nd ed.,
  Springer, 2005, Ch. 12.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/--
**Gram rigidity.** If two families `φ ψ : ι → E` of vectors in a
finite-dimensional inner product space have equal pairwise inner products,
i.e. `⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫` for all `i, j`, then there is a linear isometry
equivalence `W` of `E` with `W (φ i) = ψ i` for every `i`.

The index type `ι` is arbitrary (no finiteness needed).  The proof builds the
map `φ i ↦ ψ i` on the span of the `φ i` (the range of the linear-combination
map of `φ`), shows it is an isometry there using the equal inner products,
extends it to all of `E` by `LinearIsometry.extend`, and upgrades the result to
an equivalence by finite dimensionality.
-/
theorem exists_linearIsometryEquiv_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry
namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the
other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry
end Matrix

end ForMathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`
-/
/-
Staged for Mathlib: a proposed new file `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Quantitative polar factor for a near-isometry

A linear map `M` on a finite-dimensional real inner product space whose quadratic form
`x ↦ ⟪M x, M x⟫` is uniformly `δ`-close to `x ↦ ⟪x, x⟫` (with `δ ≤ 1 / 2`) lies within
`2 * δ` of a genuine linear isometry equivalence: there is `W : E ≃ₗᵢ[ℝ] E` with
`‖M x - W x‖ ≤ 2 * δ * ‖x‖` for all `x`.

The isometry is the *polar factor* `W = M ∘ (Mᵀ ∘ M)^(-1/2)`: the inverse square root of the
Gram operator `G = Mᵀ ∘ M` is built directly from its orthonormal eigenbasis
(`LinearMap.IsSymmetric.eigenvectorBasis`), so the proof uses neither the continuous functional
calculus nor a singular value decomposition.  Mathlib currently has no polar decomposition in
any form, and a future CFC-based polar decomposition would not directly give the quantitative
bound proved here.

The constant `2 * δ` is not sharp: the construction actually yields `√(1 + δ) * δ`, which is
the known sharp constant, but the statement rounds it up to `2 * δ` for usability (as in the
source development).

## Main results

* `ForMathlib.Real.abs_one_sub_inv_sqrt_le`: the scalar inequality `|1 - (√μ)⁻¹| ≤ δ` for
  `|μ - 1| ≤ δ ≤ 1 / 2`, used to control the eigenvalue rescaling.  It belongs with the
  `Real.sqrt` API (`Mathlib/Analysis/Real/Sqrt.lean`) and is staged here next to its consumer.
* `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le`: the quantitative polar
  factor, with the pointwise quadratic-form hypothesis
  `|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`.
* `ForMathlib.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`: the corollary for
  the operator-norm hypothesis `‖adjoint M * M - 1‖ ≤ δ`.

## TODO

* `TODO(RCLike)`: generalize the two operator results from `ℝ` to `RCLike 𝕜`.  The eigenbasis
  machinery (`LinearMap.IsSymmetric.eigenvectorBasis`) already works over `RCLike`; only the
  real-inner-product bookkeeping below would need to be redone.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Ch. 8
  (the unitary polar factor as the nearest isometry).
-/

namespace ForMathlib

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

namespace Real

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The point: `1 - (√μ)⁻¹ = (μ - 1) / (μ + √μ)` and the denominator `μ + √μ ≥ 1` when
`μ ≥ 1 / 2`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  sorry
end Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Quantitative polar factor for a near-isometry.**  If the quadratic form of a linear map
`M` on a finite-dimensional real inner product space is uniformly `δ`-close to the identity
quadratic form (`|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`, with `δ ≤ 1 / 2`), then `M` differs
from a linear isometry equivalence `W` by at most `2 * δ` pointwise:
`‖M x - W x‖ ≤ 2 * δ * ‖x‖`.

`W` is the polar factor `M ∘ G^(-1/2)` where `G = Mᵀ ∘ M` is the Gram operator; its inverse
square root is built from the orthonormal eigenbasis of `G`, with the eigenvalue rescaling
controlled by `ForMathlib.Real.abs_one_sub_inv_sqrt_le`.  The constant `2 * δ` is not sharp:
the construction gives `√(1 + δ) * δ` (the known sharp constant), and the statement rounds it
up to `2 * δ`. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  sorry
end LinearMap

namespace ContinuousLinearMap

/-- **Quantitative polar factor, operator-norm form.**  If a continuous linear map `M` on a
finite-dimensional real inner product space satisfies `‖adjoint M * M - 1‖ ≤ δ` with
`δ ≤ 1 / 2`, then `M` differs from a linear isometry equivalence `W` by at most `2 * δ`
pointwise: `‖M x - W x‖ ≤ 2 * δ * ‖x‖`.

This is a corollary of `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le` via
Cauchy–Schwarz: `|⟪M x, M x⟫ - ⟪x, x⟫| = |⟪(adjoint M * M - 1) x, x⟫| ≤ δ * ⟪x, x⟫`. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  sorry
end ContinuousLinearMap

end ForMathlib

/-!
## Source: `ForMathlib/Analysis/Matrix/Spectrum.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Vanishing tail of the sorted eigenvalues of a low-rank PSD matrix

For a positive semidefinite matrix of rank at most `d`, the sorted eigenvalues
`Matrix.IsHermitian.eigenvalues₀` (decreasing) vanish from index `d` on.

Mathlib's `eigenvalues₀` currently exposes little beyond `eigenvalues₀_antitone`.
The proof here is the elementary counting argument: by antitonicity and
nonnegativity (PSD), a nonzero sorted eigenvalue at an index `≥ d` would force
`> d` nonzero sorted eigenvalues, but their number equals `rank ≤ d` (the
sorted and unsorted eigenvalues differ by the index equivalence used to *define*
`eigenvalues`, so `rank_eq_card_non_zero_eigs` transports).

## Main result

* `ForMathlib.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le`
-/

namespace ForMathlib.Matrix

open scoped BigOperators ComplexOrder
open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/--
**Vanishing tail of the sorted eigenvalues.** If `B` is positive semidefinite
with `B.rank ≤ d`, then its sorted (decreasing) eigenvalues
`hB.isHermitian.eigenvalues₀` are zero at every index `≥ d`.
-/
theorem PosSemidef.eigenvalues₀_eq_zero_of_le {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) {d : ℕ} (hrank : B.rank ≤ d)
    (i : Fin (Fintype.card n)) (hi : d ≤ (i : ℕ)) :
    hB.isHermitian.eigenvalues₀ i = 0 := by
  sorry
end ForMathlib.Matrix

/-!
## Source: `ForMathlib/LinearAlgebra/Matrix/PosDef.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Rank-constrained positive-semidefinite factorization

A real positive-semidefinite matrix `B` factors as `B = Aᴴ * A` with `A` having
at most `d` rows **iff** its rank is at most `d`. The square-factor version
(`B = Aᴴ * A` with `A` square, e.g. the PSD square root) is already available;
this is the dimension-controlled refinement, equivalently the statement that a
PSD matrix of rank `≤ d` is the Gram matrix of `n` points in `ℝ^d` — the
classical multidimensional-scaling embedding step.

The forward (hard) direction is the spectral construction: `B = Σ_k λ_k uₖ uₖᵀ`
with `λ_k ≥ 0` and exactly `rank B` nonzero eigenvalues; scaling each nonzero
eigenvector by `√λ_k` and packing the `rank B ≤ d` resulting coordinates into
`d` rows yields `A`. The reverse direction is `posSemidef_conjTranspose_mul_self`
together with `rank_conjTranspose_mul_self` and `rank_le_height`.

## Main results

* `ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`:
  the rank-`≤ d` PSD factorization characterization, over `RCLike 𝕜`.

## References

* Cox & Cox, *Multidimensional Scaling*, 2nd ed., §2.2–2.3 (classical scaling).
* Horn & Johnson, *Matrix Analysis*, 2nd ed. (spectral theorem and PSD Gram
  factorizations).
-/

namespace ForMathlib.Matrix

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/--
Entrywise spectral expansion of a Hermitian matrix over `𝕜 = ℝ, ℂ`:
`B i j = Σ_k (eigenvalues k) * U i k * conj (U j k)`, where `U` is the
eigenvector unitary.  This is the entrywise form of
`Matrix.IsHermitian.spectral_theorem`.
-/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  sorry
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry
end ForMathlib.Matrix

/-!
## Source: `ForMathlib/MeasureTheory/CfcMeasurable.lean`
-/
/-
Staged for Mathlib: addition to
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/` (measurability of
`ω ↦ cfc f (a ω)`) and `Mathlib/MeasureTheory/MeasurableSpace/` (a countable
restrict-cover measurability criterion).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Measurability of the continuous functional calculus in the element

For a *fixed* continuous `f : ℝ → ℝ`, the map `ω ↦ cfc f (a ω)` is measurable
whenever `a` is measurable and self-adjoint-valued in a C⋆-algebra `A`.

The point is that no measurable selection of an eigenbasis is needed — even
though `cfc f a = ∑ₖ f(λₖ) uₖ uₖ*` is built from eigenvectors `uₖ` that depend
*discontinuously* on `a` at eigenvalue crossings.  The functional-calculus map
`a ↦ cfc f a` is itself continuous on each set of uniformly bounded spectrum
(`continuousOn_cfc`), and `A` is covered by countably many such sets
`{a | ‖a‖ ≤ k}`; measurability glues over the cover.

This is exactly the tool that lets a "spectral embedding" `ψ̂(ω)` enter a
probability statement: while `ψ̂(ω)` (an eigenvector configuration) need not be
measurable, its Gram matrix — a rank-`d` *spectral truncation* `cfc f` of the
sample matrix — is, and the events one cares about depend only on that Gram.

## Main results

* `ForMathlib.measurable_of_iUnion_restrict` — measurability from a countable
  measurable cover on which the restrictions are measurable.
* `ForMathlib.measurable_cfc_comp` — `ω ↦ cfc f (a ω)` is measurable.
-/

namespace ForMathlib

open MeasureTheory Set

/--
**Measurability from a countable restrict-cover.**

If `Ω = ⋃ₖ sₖ` with each `sₖ` measurable and the restriction of `g` to each
`sₖ` measurable, then `g` is measurable.  (The two-set case is
`measurable_of_restrict_of_restrict_compl`; this is the countable version.)
-/
theorem measurable_of_iUnion_restrict {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {g : Ω → A} {s : ℕ → Set Ω}
    (hs : ∀ k, MeasurableSet (s k)) (hcov : (⋃ k, s k) = univ)
    (hg : ∀ k, Measurable ((s k).restrict g)) : Measurable g := by
  sorry
variable {Ω A : Type*} [MeasurableSpace Ω]
  [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [ContinuousStar A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NormOneClass A]
  [MeasurableSpace A] [BorelSpace A]

/--
**Measurability of the continuous functional calculus in the element.**

For a fixed continuous `f : ℝ → ℝ`, if `B : Ω → A` is measurable and
self-adjoint-valued, then `ω ↦ cfc f (B ω)` is measurable — with no measurable
selection of an eigenbasis.
-/
theorem measurable_cfc_comp
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : Ω → A) (hB : Measurable B) (hsa : ∀ ω, IsSelfAdjoint (B ω)) :
    Measurable (fun ω => cfc f (B ω)) := by
  sorry
end ForMathlib

/-!
## Source: `ForMathlib/MeasureTheory/CompactExists.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/MeasureTheory/Constructions/BorelSpace/`
(measurability of events defined by a compactly-quantified constraint).

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Measurability of compactly-quantified existential events

For a Carathéodory-type function `F : Y → Ω → ℝ` — continuous in the parameter
`y` on a compact set `S`, measurable in the sample `ω` for each fixed `y` — the
event `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable.

The point is that the existential quantifies over an *uncountable* compact set,
yet no measurable-selection theorem is needed: by separability of the compact
set the event is a countable intersection of countable unions
`⋂ k, ⋃ (y ∈ D), {ω | F y ω < c + 1/(k+1)}` (`D ⊆ S` countable dense), the
nontrivial inclusion being sequential compactness plus continuity in `y` to pass
the approximate witnesses to a limit witness.

This is the standard device for showing measurability of events of the form
"some alignment/transformation in a compact group achieves error ≤ c" without
selecting the optimal transformation measurably.

## Main result

* `ForMathlib.measurableSet_exists_mem_le`
-/

namespace ForMathlib

open Filter Topology TopologicalSpace

/--
**Measurability of a compactly-quantified existential constraint.**

Let `S` be a compact set in a pseudometric space, and `F : Y → Ω → ℝ` be
continuous in `y` on `S` (for each `ω`) and measurable in `ω` (for each
`y ∈ S`).  Then `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable.
-/
theorem measurableSet_exists_mem_le
    {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Y} (hS : IsCompact S)
    {F : Y → Ω → ℝ}
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hFm : ∀ y ∈ S, Measurable (F y)) (c : ℝ) :
    MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ c} := by
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
## Source: `ForMathlib/Analysis/Matrix/SpectralFunctionMeasurable.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(measurability of a continuous spectral function of a measurable Hermitian-matrix
family).

Formalized by Claude Fable 5 (claude-fable-5[1m]); relocated/staged and
self-contained-ized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Measurability of a continuous spectral function of a Hermitian matrix family

For a fixed continuous `h : ℝ → ℝ`, the *spectral `h`-transform*
`specTransform h B = Σₖ h(λₖ) uₖ uₖᵀ` of a measurable Hermitian-matrix family is
measurable.  Equivalently (for `h` continuous) this is the matrix continuous
functional calculus `h(B)`; the point is that it is measurable in the *entrywise*
σ-algebra with **no measurable selection of an eigenbasis** — `B ↦ uₖ(B)` is
discontinuous at eigenvalue crossings, yet `specTransform h B` is the entrywise
pointwise limit of matrix *polynomials* `p(B)` (Stone–Weierstrass on a spectral
interval), each of which is an entrywise polynomial in the entries of `B`.

## Main results

* `ForMathlib.Matrix.specTransform`
* `ForMathlib.Matrix.measurable_specTransform`
-/

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open MeasureTheory Filter Polynomial Set

namespace ForMathlib.Matrix

variable {n : ℕ}

/-- `Matrix` is a type-level def, so the pi `MeasurableSpace` instance does not
fire on it automatically; register the entrywise σ-algebra (matching the pi
topology used by `continuous_aeval`).  (To be reconciled with Mathlib's matrix
measurable structure at PR time.) -/
instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

instance : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

/-- The symmetric-operator structure of `toEuclideanLin B` for a Hermitian `B`. -/
noncomputable def opSym {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    (Matrix.toEuclideanLin B).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hB

/-- The sorted (decreasing) eigenvalues of `toEuclideanLin B` for Hermitian `B`. -/
noncomputable def sortedEig {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    Fin n → ℝ :=
  (opSym hB).eigenvalues finrank_euclideanSpace_fin

/-- For continuous `h` and any radius/tolerance, there is a polynomial
uniformly close to `h` on `[-R, R]`. -/
theorem exists_polynomial_uniform_close (h : ℝ → ℝ) (hh : Continuous h)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc (-R) R, |h x - p.eval x| ≤ ε := by
  sorry
theorem abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  sorry
theorem abs_sortedEig_le_of_entry_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {β : ℝ} (hβ : ∀ i j, |B i j| ≤ β) (k : Fin n) :
    |sortedEig hB k| ≤ (n : ℝ) * β := by
  sorry
theorem pow_mulVec_eigenvector {B : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : B *ᵥ v = μ • v) (t : ℕ) :
    (B ^ t) *ᵥ v = (μ ^ t) • v := by
  sorry
theorem aeval_mulVec_eigenvector {B : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : B *ᵥ v = μ • v) (p : Polynomial ℝ) :
    (aeval B p) *ᵥ v = (p.eval μ) • v := by
  sorry
theorem mulVec_eigenvectorBasis {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (k : Fin n) :
    B *ᵥ WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k)
      = sortedEig hB k
          • WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k) := by
  sorry
theorem aeval_entry_eq_sum {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (p : Polynomial ℝ) (i j : Fin n) :
    (aeval B p) i j
      = ∑ k : Fin n, p.eval (sortedEig hB k)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j) := by
  sorry
noncomputable def specTransform (h : ℝ → ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin n, h (sortedEig hB k)
      * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
      * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j)

/-- Uniform approximation of the spectral transform by matrix polynomials, on
an entrywise-bounded set of matrices. -/
theorem abs_specTransform_sub_aeval_le (h : ℝ → ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {β ε : ℝ} (hβ : ∀ a b, |B a b| ≤ β)
    {p : Polynomial ℝ}
    (hp : ∀ x ∈ Set.Icc (-((n : ℝ) * β)) ((n : ℝ) * β), |h x - p.eval x| ≤ ε)
    (i j : Fin n) :
    |specTransform h hB i j - (aeval B p) i j| ≤ (n : ℝ) * ε := by
  sorry
theorem measurable_specTransform {Ω : Type*} [MeasurableSpace Ω]
    (h : ℝ → ℝ) (hh : Continuous h)
    {Bm : Ω → Matrix (Fin n) (Fin n) ℝ} (hBmeas : Measurable Bm)
    (hsym : ∀ ω, (Bm ω).IsHermitian) :
    Measurable fun ω => specTransform h (hsym ω) := by
  sorry
end ForMathlib.Matrix

/-!
## Source: `ForMathlib/Analysis/Matrix/EntrywiseEigenvalue.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(eigenvalue perturbation from entrywise closeness).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Eigenvalue perturbation from entrywise closeness

Weyl's inequality bounds the eigenvalue perturbation by the *operator* norm of the
difference.  Combined with the entrywise→operator-norm comparison
`‖toEuclideanLin A‖ ≤ n · (entrywise sup of A)`, this gives a directly usable
**entrywise** eigenvalue-perturbation bound: if two real symmetric `n × n`
matrices are entrywise `ε`-close, their sorted eigenvalues differ by at most
`n · ε`.

## Main result

* `ForMathlib.Matrix.abs_sortedEig_sub_le_of_entry_le`
-/

open scoped Matrix
open Module

namespace ForMathlib.Matrix

variable {n : ℕ}

/-- **Entrywise eigenvalue perturbation.**  If two real symmetric matrices `A`,
`Ahat` are entrywise `ε`-close, their `k`-th sorted eigenvalues differ by at most
`n · ε` (Weyl's inequality through the entrywise → operator-norm comparison). -/
theorem abs_sortedEig_sub_le_of_entry_le {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, |Ahat i j - A i j| ≤ ε) (k : Fin n) :
    |sortedEig hAhat k - sortedEig hA k| ≤ (n : ℝ) * ε := by
  sorry
end ForMathlib.Matrix

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
omit [MeasurableSpace Ω] in
/-- The empirical covariance matrix is symmetric (Hermitian over `ℝ`). -/
theorem isHermitian_sampleCovariance {n d : ℕ}
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    (sampleCovariance V ω).IsHermitian := by
  sorry
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
  sorry
end ForMathlib

/-!
## Source: `ForMathlib/Topology/ApproxMinimizer.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Topology/Order/Compact.lean` (companion
to `IsCompact.exists_isMinOn`), or a dedicated file alongside
`Mathlib/Topology/Sequences.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Stability of minimizers under approximate minimization

If a sequence `z k` lives in a compact set and each `z k` *approximately*
minimizes a continuous real function `F` — for every point `x`, `F (z k) ≤
F x + ε x k` with `ε x k → 0` — then a subsequence of `z k` converges to a
genuine global minimizer of `F`.

This is the elementary "recovery" half of the fundamental theorem of
Γ-convergence: a perturbed family of variational problems whose minimizers stay
in a fixed compact set has a limit point that solves the unperturbed problem.
The typical source of the approximate-minimizer hypothesis is a second family
`F k` with `z k ∈ argmin (F k)` and `F k → F` in a suitable uniform sense.

## Main results

* `ForMathlib.exists_subseq_tendsto_forall_le_of_approxMin`
* `ForMathlib.exists_subseq_tendsto_isMinOn_of_approxMinOn` — the variant where the
  approximate-minimization comparison ranges only over the compact set `K`, so the
  limit is a minimizer *on `K`* (`IsMinOn F K`) rather than a global one. This is
  the form the Berge maximum theorem consumes (the feasible set is constrained).
-/

namespace ForMathlib

open Filter Topology

/--
**Stability of minimizers under approximate minimization.**

Let `K` be a compact subset of a first-countable topological space, `F : X → ℝ`
continuous, and `z : ℕ → X` a sequence in `K` such that each `z k` approximately
minimizes `F`: for every `x`, `F (z k) ≤ F x + ε x k`, where `ε x k → 0` as
`k → ∞` (the error may depend on the comparison point `x`). Then there is a
strictly monotone `φ` and a point `ψ ∈ K` with `z ∘ φ → ψ` and `ψ` a global
minimizer of `F` (`∀ x, F ψ ≤ F x`).
-/
theorem exists_subseq_tendsto_forall_le_of_approxMin
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, (∀ x, F ψ ≤ F x) ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  sorry
theorem exists_subseq_tendsto_isMinOn_of_approxMinOn
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x ∈ K, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x ∈ K, ∀ k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, IsMinOn F K ψ ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  sorry
end ForMathlib

/-!
## Source: `ForMathlib/Topology/Berge.lean`
-/
/-
Staged for Mathlib: the Berge maximum theorem (upper hemicontinuity of the
parametric argmin correspondence over a fixed compact feasible set).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Berge's maximum theorem (fixed compact constraint)

Let `g : P → X → ℝ` be jointly continuous and let `K ⊆ X` be a fixed nonempty
compact set.  Consider the parametric minimization of `g p` over `K`, with
argmin correspondence
`M p = {x ∈ K | IsMinOn (g p) K x}`.
Berge's maximum theorem says the value function `p ↦ ⨅ x ∈ K, g p x` is continuous
and the correspondence `M` is upper hemicontinuous (and compact-valued and
nonempty).

Mathlib has the hemicontinuity *definitions* (`Mathlib/Topology/Semicontinuity/
Hemicontinuity.lean`) and the extreme-value theorem (`IsCompact.exists_isMinOn`),
but no Berge theorem.  This file supplies the upper-hemicontinuity half in two
usable forms, building on the approximate-minimizer stability engine
`ForMathlib.exists_subseq_tendsto_isMinOn_of_approxMinOn`:

* `tendsto_eval_sub_of_isCompact` — along a convergent parameter sequence
  `p k → p₀`, the evaluation difference `g (p k) (x k) − g p₀ (x k)` vanishes
  uniformly over points `x k` staying in the compact `K` (a uniform-convergence-
  on-compacts fact, here in the sequential form actually needed).
* `tendsto_subseq_isMinOn_of_isMinOn` — **sequential upper hemicontinuity**: any
  sequence of constrained minimizers `x k ∈ argmin (g (p k))` for `p k → p₀` has
  a subsequence converging to a constrained minimizer of `g p₀`.  This is the
  closed-graph form of Berge's theorem.
* `upperHemicontinuousAt_isMinOn` — the same conclusion phrased through Mathlib's
  own `UpperHemicontinuousAt` predicate for the argmin correspondence
  `p ↦ {x ∈ K | IsMinOn (g p) K x}` (requires `X` Hausdorff so the compact `K` is
  closed and limits of feasible points stay feasible).
* `exists_modulus_isMinOn_family` / `exists_modulus_isMinOn` — the **uniform
  `ε`–`δ` modulus** form (metric `P`): for every `ε > 0` there is a `δ > 0` such
  that whenever `dist p p₀ ≤ δ`, *every* minimizer of `g p` over `K` is `ε`-close
  (in the ambient metric, or in any finite family of continuous invariants) to
  *some* minimizer of `g p₀` over `K`.  The family form captures the
  affine-invariant `pairDistErr` closeness of MDS; it is the general core of the
  raw-stress modulus `Acharyya2024.exists_modulus_pairDist`, which additionally
  needs the MDS-specific coercive compactness (centering into a parameter-
  dependent box) that the fixed-`K` theorem here does not subsume.

## Main results

* `ForMathlib.tendsto_subseq_isMinOn_of_isMinOn`
* `ForMathlib.upperHemicontinuousAt_isMinOn`
* `ForMathlib.continuous_iInf_of_isCompact` — value-function continuity.
* `ForMathlib.exists_modulus_isMinOn_family` / `ForMathlib.exists_modulus_isMinOn`
-/

namespace ForMathlib

open Filter Topology Set

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [FirstCountableTopology X]

/-- **Sequential uniform convergence on a compact set from joint continuity.**
If `g : P → X → ℝ` is jointly continuous, `p k → p₀`, and the points `x k` stay in
a compact set `K`, then the evaluation difference `g (p k) (x k) − g p₀ (x k)`
tends to `0`.  (This is the only consequence of "`g (p k) → g p₀` uniformly on
`K`" needed for Berge; it is proved directly via the subsequence criterion and
sequential compactness, avoiding the compact-open topology.) -/
theorem tendsto_eval_sub_of_isCompact
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hx : ∀ k, x k ∈ K) :
    Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) := by
  sorry
theorem tendsto_subseq_isMinOn_of_isMinOn
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K)
    (hxmin : ∀ k, IsMinOn (g (p k)) K (x k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  sorry
theorem upperHemicontinuousAt_isMinOn {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [T2Space X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := by
  sorry
theorem continuous_iInf_of_isCompact [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := by
  sorry
theorem exists_modulus_isMinOn_family {P X : Type*} [PseudoMetricSpace P]
    [TopologicalSpace X] [FirstCountableTopology X]
    {ι : Type*} [Finite ι]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {ρ : ι → X → X → ℝ} (hρ : ∀ i, Continuous (Function.uncurry (ρ i)))
    (hρ0 : ∀ i x, ρ i x x = 0)
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ ∀ i, ρ i x x₀ < ε := by
  sorry
theorem exists_modulus_isMinOn {P X : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε := by
  sorry
end ForMathlib
