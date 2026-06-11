# Mathlib-contribution candidates from the DKPS formalization

Compiled 2026-06-11 from two systematic surveys (spectral/linear-algebra and
probability/analysis) of the proved, zero-sorry content in `Acharyya2024/`,
`Acharyya2025/`, and `DrsbBridge/WellKnown.lean`. Every "Mathlib has/lacks"
claim below was verified by grep against the local checkout
`proofs/.lake/packages/mathlib` at commit `0e4799ceff90` (2026-02-13), not
from memory.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).

Effort grades: **S** = statement+proof port nearly verbatim; **M** = moderate
generalization (typically ℝ → `RCLike 𝕜`, restating in Mathlib idiom);
**L** = substantial redesign.

---

## Unified priority ranking (value per effort)

| # | Candidate | Source | Effort | Proposed home |
|---|-----------|--------|--------|---------------|
| 1 | Donsker–Varadhan variational principle (inequality + Gibbs attainment + `IsGreatest`/`sSup`) | `DrsbBridge/WellKnown.lean:225,250,271,298` | S–M | new `InformationTheory/KullbackLeibler/DonskerVaradhan.lean` |
| 2 | Procrustes rigidity (equal Grams ⇒ linear isometry equiv) | `Acharyya2025/Procrustes.lean:49` | S/M | `Analysis/InnerProductSpace/GramMatrix.lean` |
| 3 | QoL small-lemma bundle: measurability-free `1 − μ sᶜ ≤ μ s`; Bochner Markov in division form; uncentered second-moment Chebyshev | `Acharyya2025/RateChain.lean:75`, `DrsbBridge/WellKnown.lean:174`, `Acharyya2024/Probability.lean:49` | S | next to the existing siblings (see §3) |
| 4 | Courant–Fischer (k-th eigenvalue, both directions) + Weyl's eigenvalue perturbation inequality | `Acharyya2025/Weyl.lean:142,196,260` | M | new `Analysis/InnerProductSpace/CourantFischer.lean` |
| 5 | Vector-valued sample-mean MSE: `E‖X̄−μ‖² = r⁻²Σₖ E‖Xₖ−μ‖²` + iid trace(Σ)/r + `≤ γ/r` | `Acharyya2024/SecondMoment.lean:143,232,265` | M | `Probability/Moments/Variance.lean` or new `SampleMean.lean` |
| 6 | Rank-constrained PSD Gram realization (`PosSemidef ∧ rank ≤ d ↔ ∃ A : Matrix (Fin d) n 𝕜, B = Aᴴ*A`) + `eigenvalues₀` tail-vanishing | `Acharyya2025/GramRealization.lean:96`, `MatrixPerturbation.lean:130` | M | `GramMatrix.lean` / `Analysis/Matrix/Spectrum.lean` |
| 7 | Quantitative polar factor (near-isometry ⇒ isometry within 2δ, no CFC/SVD) | `Acharyya2025/PolarFactor.lean:93` | M | new `Analysis/InnerProductSpace/NearIsometry.lean` |
| 8 | `TendstoInMeasure` constructor from a vanishing high-probability rate | `Acharyya2024/WellKnown.lean:112` | S–M | `MeasureTheory/Function/ConvergenceInMeasure.lean` |
| 9 | Hoeffding for bounded iid empirical means (MGF + two-sided tail packaging) | `DrsbBridge/WellKnown.lean:83,368` | M | `Probability/Moments/SubGaussian.lean` |
| 10 | PAC-Bayes master bound + supervised corollary | `DrsbBridge/WellKnown.lean:392,444` | M–L | would open new area (`Probability/PACBayes.lean`); sequence after #1 |

**Deliberately deferred** (real gaps, but redesign expected): the Davis–Kahan
cross-block theorem itself (`n·ε²/gap²` constant is crude — contribute the
S-grade cross-term identity now, see §4b, the theorem later in projector
form); ℓ²-opNorm vs Frobenius vs entrywise norm comparisons (verified absent
upstream, but mostly scoped-instance plumbing — best as a dedicated
norm-comparison PR: `Matrix.l2_opNorm_le_frobenius` + entrywise corollary);
argmin-set stability behind `exists_modulus_pairDist` (Mathlib just gained
`Topology/Semicontinuity/Hemicontinuity.lean` with no Berge maximum theorem —
raise as a feature request to its author rather than port our MDS-specific
proof).

**Not candidates** (verified duplicates / one-line wrappers):
`DrsbBridge/WellKnown.lean:43 integral_eval_pi` = existing
`MeasureTheory.integral_comp_eval` (`Integral/Pi.lean:139`, weaker hypotheses
than ours); `Acharyya2024/WellKnown.lean:23` = `dist_dist_dist_le`;
`sqrt_sum_sq_le_sum_abs` (wrapper over `Finset.sum_sq_le_sq_sum_of_nonneg`);
`abs_sqrt_rawStress_sub_le` (reverse triangle in ℓ² in disguise);
`mds_nonempty` (pattern = `Continuous.exists_forall_le'`); `RankGap.lean` and
`Overlap.lean` packaging (paper-specific composition glue);
`MatrixPerturbation.sortedEigenvalues` (duplicate of Mathlib's
`Matrix.IsHermitian.eigenvalues₀`).

**Local cleanup opportunities** (not blocking, nice-to-have): migrate
`sortedEigenvalues` to `eigenvalues₀`; delete `integral_eval_pi` in favor of
`integral_comp_eval`.

---

## Detailed dossiers

### 1. Donsker–Varadhan variational principle — top priority

- `integral_le_klDiv_add_log_integral_exp` (`DrsbBridge/WellKnown.lean:225`):
  for probability measures `μ ≪ ν`, `exp∘f ∈ L¹(ν)`, `llr μ ν ∈ L¹(μ)`:
  `∫ f dμ ≤ (klDiv μ ν).toReal + log ∫ exp f dν`.
- `integral_tilted_sub_klDiv_tilted` (`:250`): equality at the Gibbs measure
  `ν.tilted f`.
- `isGreatest_donskerVaradhan` (`:271`) / `log_integral_exp_eq_sSup` (`:298`):
  the full Gibbs variational principle.

Mathlib state: zero hits for "donsker|varadhan";
`InformationTheory/KullbackLeibler/Basic.lean` has only Gibbs' inequality and
`klDiv_eq_top_iff`/`klDiv_ne_top_iff`. ALL the proof infrastructure already
exists upstream (`Measure.tilted`, `isProbabilityMeasure_tilted`,
`log_rnDeriv_tilted_left_self` in `Measure/Tilted.lean:368`,
`integral_llr_tilted_right` in `Measure/LogLikelihoodRatio.lean:197`), and the
statements are already phrased in pure Mathlib vocabulary.

Upstream polish: bundle the hypothesis pair `μ ≪ ν ∧ Integrable (llr μ ν) μ`
into `klDiv μ ν ≠ ∞` (this is exactly `klDiv_ne_top_iff`); consider indexing
the `sSup` over `{μ | klDiv μ ν ≠ ∞}`; decide whether
`Integrable f (ν.tilted f)` is derivable for `f` bounded above.

### 2. Procrustes rigidity — best spectral value/effort

`exists_linearIsometryEquiv_of_inner_eq` (`Acharyya2025/Procrustes.lean:49`):
families `φ ψ : ι → E` (arbitrary index, `E` finite-dim real IPS) with
`⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫` are related by `W : E ≃ₗᵢ[ℝ] E` with `W (φ i) = ψ i`.
Proof: `Finsupp.linearCombination` kernel comparison + `LinearIsometry.extend`.

Mathlib state: zero hits for "procrustes"; nothing produces an isometry from
equal inner products. Mathlib *recently gained* `Matrix.gram`
(`Analysis/InnerProductSpace/GramMatrix.lean`, 2025, P. Pfaffelhuber) with
only three lemmas (`posSemidef_gram`, `isHermitian_gram`,
`posDef_gram_iff_linearIndependent`) — our theorem is the natural next one,
statable as `gram 𝕜 φ = gram 𝕜 ψ → ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i`.
RCLike generalization is mild (`inner_smul_left/right` with conjugation in the
expansion step). Submit first among spectral items.

### 3. QoL small-lemma bundle (one PR)

- `highProbAtTop_of_tendsto_compl_zero` kernel
  (`Acharyya2025/RateChain.lean:75`): measurability-free `1 − μ sᶜ ≤ μ s` for
  probability measures via subadditivity `1 = μ(s ∪ sᶜ) ≤ μ s + μ sᶜ`.
  Mathlib's `prob_compl_eq_one_sub₀` needs `NullMeasurableSet`,
  `prob_compl_le_one_sub_of_le_prob` needs `MeasurableSet`; nothing
  measurability-free exists. Home:
  `MeasureTheory/Measure/Typeclasses/Probability.lean`.
- `markov_exp` (`DrsbBridge/WellKnown.lean:174`): Bochner-integral Markov in
  division/`ofReal` form. Mathlib has the multiplication form
  (`mul_meas_ge_le_integral_of_nonneg`, `Bochner/Basic.lean:1176`) and the
  lintegral division form (`meas_ge_le_lintegral_div`,
  `Integral/Lebesgue/Markov.lean:104`) but no Bochner division form — a
  naming-symmetry gap. Relax to `IsFiniteMeasure`.
- `meas_gt_le_ofReal_secondMoment_div_sq` (`Acharyya2024/Probability.lean:49`):
  uncentered second-moment Chebyshev `P{η < Y} ≤ ofReal(v/η²)` from
  `∫ Y² ≤ v`, no measurability of `Y`. Mathlib's
  `meas_ge_le_variance_div_sq` (`Probability/Moments/Variance.lean:380`) is
  centered and needs `MemLp 2`. Home: next to it.

### 4. Courant–Fischer + Weyl — the largest genuine spectral gap

(a) `exists_unit_vector_inner_le_eigenvalue` (`Weyl.lean:142`),
`forall_unit_vector_eigenvalue_le_inner` (`:196`): the two directions of
Courant–Fischer for the k-th sorted eigenvalue of a symmetric operator on a
finite-dim real IPS. `abs_eigenvalues_sub_le` (`:260`): Weyl's inequality
`|λₖ(T) − λₖ(S)| ≤ ε` from `∀ x, ‖(T−S)x‖ ≤ ε‖x‖`. Helpers worth bringing:
`specSubspace` machinery, `inner_map_self_eq_sum_eigenvalues_sq` (quadratic
form diagonalization — also absent upstream).

Mathlib state: no analogue. "Weyl" hits only root systems;
`Analysis/InnerProductSpace/Rayleigh.lean` characterizes only the extreme
eigenvalues. Builds directly on Mathlib's own `IsSymmetric.eigenvalues` /
`eigenvalues_antitone` / `eigenvectorBasis` (`Spectrum.lean:258,292,280`),
which use the same decreasing convention as our code — a major portability
win. Main work: ℝ → `RCLike` (quadratic form becomes `RCLike.re ⟪Tx, x⟫`).
Foundational: unblocks any future eigenvalue-perturbation work upstream and is
a prerequisite for Davis–Kahan.

(b) Independently submittable NOW at grade S: the cross-term identity
`inner_eigenvector_map_sub_eq` (`DavisKahan.lean:59`):
`⟪uᵢ, (S−T)ûⱼ⟫ = (λ̂ⱼ − λᵢ)⟪uᵢ, ûⱼ⟫` — a three-line natural addition to
`Analysis/InnerProductSpace/Spectrum.lean`.

### 5. Vector-valued sample-mean MSE

`integral_norm_sq_sampleMean_sub_mean_eq_sum`
(`Acharyya2024/SecondMoment.lean:143`) + iid (`:232`) + `≤ γ/r` (`:265`).
Mathlib's `variance`/`evariance` are ℝ-valued only; `covarianceBilin`/
`covarianceOperator` exist but have NO trace identity and NO sample-mean API
(the strong law does its Chebyshev step inline). Upstream: generalize
`EuclideanSpace ℝ ι` to finite-dim real IPS via orthonormal basis; weaken
`iIndepFun` to per-coordinate pairwise independence (all the proof uses);
optionally connect to `covarianceBilin` trace. Scalar companion
(`integral_sq_scaled_sum_sub_of_pairwise_indep`, `:58`) is an S-grade
restatement via `variance` of the sample mean on top of existing
`IndepFun.variance_sum` (which already accepts pairwise independence).

### 6. Rank-constrained PSD Gram realization + eigenvalue tail

`exists_config_gram_eq_of_posSemidef_rank_le` (`GramRealization.lean:96`):
real PSD `B` with `rank ≤ d` is the Gram matrix of n points in ℝ^d. Mathlib
has `posSemidef_iff_eq_conjTranspose_mul_self` (square factor, no rank
control) and `posSemidef_iff_eq_sum_vecMulVec` (unconstrained count); the
dimension-controlled version is missing and completes `Matrix.gram` as a
characterization. State as an iff
`B.PosSemidef ∧ B.rank ≤ d ↔ ∃ A : Matrix (Fin d) n 𝕜, B = Aᴴ * A`.
Ride-along: restate `sortedEigenvalues_tail_eq_zero`
(`MatrixPerturbation.lean:130`) against Mathlib's `eigenvalues₀` as
`Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le` — a pure counting proof via
`rank_eq_card_non_zero_eigs` + `eigenvalues₀_antitone` is shorter than our
operator-range detour. (`eigenvalues₀` currently has almost no API beyond
antitonicity.)

### 7. Quantitative polar factor

`exists_isometry_close_of_self_adjoint_comp_close` (`PolarFactor.lean:93`):
`|⟪Mx,Mx⟫ − ⟪x,x⟫| ≤ δ⟪x,x⟫` with `δ ≤ 1/2` ⇒ ∃ isometry `W` with
`‖(M−W)x‖ ≤ 2δ‖x‖`; constructed as `M ∘ (MᵀM)^{−1/2}` from the eigenbasis —
no CFC, no SVD. Mathlib has NO polar decomposition in any form (verified;
"polar" hits only convex-duality polars and polar coordinates). Idiom work:
return a bundled `F →ₗᵢ[𝕜] F`/`≃ₗᵢ`; hypothesis as `‖M†M − 1‖ ≤ δ`. Selling
point: quantitative, which a future CFC-based polar decomposition would not
directly give. Sharp constant is `√(1+δ)·δ`; we ship `2δ` (documented).
Scalar helper `abs_one_sub_inv_sqrt_le` (`:43`) is a free S-grade lemma.

### 8. `TendstoInMeasure` from a vanishing HP rate

`tendsto_measure_abs_gt_zero_of_highProb_abs_le_rate`
(`Acharyya2024/WellKnown.lean:112`): HP events `|Xₙ| ≤ rate n` with
`rate → 0` ⇒ convergence in measure. `ConvergenceInMeasure.lean` has only the
a.e. (`tendstoInMeasure_of_tendsto_ae`) and Lp
(`tendstoInMeasure_of_tendsto_eLpNorm`) constructors — yet the HP-rate form is
how concentration results are actually consumed. Generalize ℝ → pseudometric,
general filter; drop the `MeasurableSet` hypothesis via the bundle-3
complement lemma.

### 9. Hoeffding for bounded iid empirical means

`hoeffding_iid_mgf_le` (`DrsbBridge/WellKnown.lean:83`) + orientation
companion (`:368`). Mathlib has all the pieces
(`hasSubgaussianMGF_of_mem_Icc` = Hoeffding's lemma,
`HasSubgaussianMGF.sum_of_iIndepFun`, `measure_sum_ge_le_of_iIndepFun`,
`iIndepFun_pi`) but not the classical packaged corollary for the empirical
mean (two-sided, `2exp(−2nε²/(b−a)²)`), nor any `Measure.pi`-sample
packaging. Agree orientation (abstract `iIndepFun` vs `Measure.pi`) with
maintainers first.

### 10. PAC-Bayes

`pacBayes_of_expMoment` (`:392`), `pacBayes_supervised` (`:444`): master
bound `∫ F ω dρ ≤ KL(ρ‖π) + log(1/δ)` w.p. ≥ 1−δ, plus a bounded-loss
supervised-learning corollary. Nothing in Mathlib (no statistical-learning
content at all); statements are already generic (`Measure`, `klDiv`, `llr`,
`Measure.pi`). Opens a new area — needs maintainer buy-in and trimming of the
hypothesis lists; sequence after Donsker–Varadhan lands.
