# Mathlib-contribution candidates from the DKPS formalization

Compiled 2026-06-11 from two systematic surveys (spectral/linear-algebra and
probability/analysis) of the proved, zero-sorry content in `Acharyya2024/` and
`Acharyya2025/`. Every "Mathlib has/lacks" claim below was verified by grep
against the local checkout `proofs/.lake/packages/mathlib` at commit
`0e4799ceff90` (2026-02-13), not from memory.

**Update 2026-06-11 (same day, later session):** the workspace was bumped to
Mathlib master `476fb97b621c` (2026-06-11, toolchain v4.31.0-rc2).  Gap claims
for candidates #1, #2 (both halves), and #3b were RE-VERIFIED against the new
pin and still hold; `mul_meas_ge_le_integral_of_nonneg` and the
`IsSymmetric.eigenvalues`/`eigenvectorBasis` sorted spectral API also survive
(eigenvalues are now an `irreducible_def` over `RCLike 𝕜`, same decreasing
convention).  Candidates #3a, #4, #5, #6, #7 have NOT yet been re-verified
against the new pin — re-grep before porting them.  Note Mathlib now uses the
module system (`module` / `public import` headers); staged files must be
converted at PR time.

**Staging status (updated 2026-06-12):** candidates #1, #2 (both lemmas),
#3a (Courant–Fischer + Weyl, RCLike), #3b, #4 (sample-mean MSE on a
finite-dim real IPS), #5 (rank-constrained PSD factorization, ℝ), #6
(quantitative polar factor, bundled isometry + CLM corollary), and #7
(TendstoInMeasure constructors, general filter/EDist) are ALL staged in the
`ForMathlib/` library (see `ForMathlib/README.md`), generalized to `RCLike 𝕜`
where applicable, with the paper libraries rewired to consume them
(`Acharyya2025/Procrustes.lean`, `Acharyya2025/RateChain.lean`,
`Acharyya2024/Probability.lean`, `Acharyya2025/DavisKahan.lean`,
`Acharyya2024/SecondMoment.lean`, `Acharyya2025/GramRealization.lean`,
`Acharyya2025/Weyl.lean`, `Acharyya2025/PolarFactor.lean`,
`Acharyya2024/WellKnown.lean` are now thin wrappers/consumers).  All seven
candidates' gap claims were re-verified against pin `476fb97b621c` before
porting.

Both #5 follow-ups are now resolved (Opus, 2026-06-12):
* **#5 RCLike generalization** — DONE.
  `posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self` and the entry helper
  `isHermitian_entry_eq_sum_eigenvalues` are now over `RCLike 𝕜` (construction
  `A k i = (√λ_k : 𝕜)·conj (U i k)`).  ℝ consumer unchanged.
* **#5 eigenvalue-tail ride-along** — DONE, and the "blocker" dissolved:
  current Mathlib *defines* `eigenvalues = eigenvalues₀ ∘ equiv`, so the
  sorted/unsorted bijection is definitional.  Staged
  `ForMathlib/Analysis/Matrix/Spectrum.lean`
  `PosSemidef.eigenvalues₀_eq_zero_of_le` (`RCLike`).  The local operator-world
  `Acharyya2025/MatrixPerturbation.lean` `sortedEigenvalues` is deliberately
  left (retiring it is a large, zero-benefit refactor).

Formalized by Claude Fable 5 (claude-fable-5[1m]).

Effort grades: **S** = statement+proof port nearly verbatim; **M** = moderate
generalization (typically ℝ → `RCLike 𝕜`, restating in Mathlib idiom);
**L** = substantial redesign.

---

## Unified priority ranking (value per effort)

| # | Candidate | Source | Effort | Proposed home |
|---|-----------|--------|--------|---------------|
| 1 | Procrustes rigidity (equal Grams ⇒ linear isometry equiv) | `Acharyya2025/Procrustes.lean:49` | S/M | `Analysis/InnerProductSpace/GramMatrix.lean` |
| 2 | QoL small-lemma bundle: measurability-free `1 − μ sᶜ ≤ μ s`; uncentered second-moment Chebyshev | `Acharyya2025/RateChain.lean:75`, `Acharyya2024/Probability.lean:49` | S | next to the existing siblings (see §2) |
| 3 | Courant–Fischer (k-th eigenvalue, both directions) + Weyl's eigenvalue perturbation inequality | `Acharyya2025/Weyl.lean:142,196,260` | M | new `Analysis/InnerProductSpace/CourantFischer.lean` |
| 4 | Vector-valued sample-mean MSE: `E‖X̄−μ‖² = r⁻²Σₖ E‖Xₖ−μ‖²` + iid trace(Σ)/r + `≤ γ/r` | `Acharyya2024/SecondMoment.lean:143,232,265` | M | `Probability/Moments/Variance.lean` or new `SampleMean.lean` |
| 5 | Rank-constrained PSD Gram realization (`PosSemidef ∧ rank ≤ d ↔ ∃ A : Matrix (Fin d) n 𝕜, B = Aᴴ*A`) + `eigenvalues₀` tail-vanishing | `Acharyya2025/GramRealization.lean:96`, `MatrixPerturbation.lean:130` | M | `GramMatrix.lean` / `Analysis/Matrix/Spectrum.lean` |
| 6 | Quantitative polar factor (near-isometry ⇒ isometry within 2δ, no CFC/SVD) | `Acharyya2025/PolarFactor.lean:93` | M | new `Analysis/InnerProductSpace/NearIsometry.lean` |
| 7 | `TendstoInMeasure` constructor from a vanishing high-probability rate | `Acharyya2024/WellKnown.lean:112` | S–M | `MeasureTheory/Function/ConvergenceInMeasure.lean` |
| 8 | Davis–Kahan cross-block (squared sin-Θ) bound + rank-`d`/floor corollary | `Acharyya2025/DavisKahan.lean:135`, `RankGap.lean:42,78` | M | new `Analysis/InnerProductSpace/DavisKahan.lean` |

**Update 2026-06-12 (Opus session):** candidate #8 (Davis–Kahan cross-block
bound) is now STAGED, RCLike-general, in
`ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean` —
`sum_norm_inner_eigenvectorBasis_map_sub_sq_le` (total cross-energy `≤ nε²`),
`sum_cross_norm_inner_eigenvectorBasis_sq_le` (the sin-Θ bound `≤ nε²/gap²`),
and `…_of_rank_floor` (the `≤ 4nε²/α²` corollary under PSD rank-`d` + spectral
floor).  The earlier "deferred / needs redesign" note is superseded: the crude
`n·ε²/gap²` constant is documented in-file, the result is correct and
self-contained, and the cleaner projector-form sin-Θ remains a possible future
strengthening.  `Acharyya2025/DavisKahan.lean` and `RankGap.lean` are now thin
ℝ-instantiation wrappers.

**Update 2026-06-12 (Opus session, cont.):** the norm-comparison item is now
STAGED in `ForMathlib/Analysis/Matrix/EntrywiseOpNorm.lean`:
`sum_norm_le_sqrt_card_mul_norm` (the `ℓ¹ ≤ √card · ℓ²` bound on
`EuclideanSpace 𝕜 ι`, `RCLike`, absent upstream — only the
`sq_sum_le_card_mul_sum_sq` Chebyshev kernel exists) and
`norm_toEuclideanLin_le_of_entry_le` (entrywise sup `≤ ε` gives Euclidean
operator bound `‖toEuclideanLin A x‖ ≤ nε‖x‖`, ℝ — Mathlib has the full
`l2_opNorm` API but no entrywise/Frobenius comparison).
`Acharyya2025/OperatorBridge.lean` rewired to consume both.  Two follow-ups:
the `n` constant is loose (Frobenius gives `√card`), and the matrix bound is
ℝ-only (`TODO(RCLike)` in-file).

**Update 2026-06-12 (Opus session, cont.):** the genuinely-general core of the
`Acharyya2024/RawStress.lean` deterministic MDS stability is now STAGED as a
topology lemma: `ForMathlib/Topology/ApproxMinimizer.lean`
`exists_subseq_tendsto_forall_le_of_approxMin` (compact-set + per-point
approximate minimization of a continuous function ⇒ a subsequence converges to a
global minimizer; the elementary "recovery" half of Γ-convergence).
`Acharyya2024/RawStress.lean`'s `exists_subseq_tendsto_mds` is rewired to it
(the MDS-specific coercivity / compact-box construction stays local).  The rest
of RawStress is wrappers (`abs_sqrt_rawStress_sub_le` = reverse triangle;
`mds_nonempty` = coercivity + `IsCompact.exists_isMinOn`) or the Berge-maximum
argmin modulus `exists_modulus_pairDist` — see `planning/for-fable.md` F3.

Remaining non-trivial items are catalogued in `planning/for-fable.md` (RCLike
Gram factorization, eigenvalues₀ tail, Berge/argmin modulus, sharp Davis–Kahan,
the `h_conc_meas` measurable-selection seam) — all either blocked on upstream
API or requiring substantial new proofs.

**Deliberately deferred** (real gaps, but redesign expected):
argmin-set stability behind `exists_modulus_pairDist` (Mathlib just gained
`Topology/Semicontinuity/Hemicontinuity.lean` with no Berge maximum theorem —
raise as a feature request to its author rather than port our MDS-specific
proof).

**Not candidates** (verified duplicates / one-line wrappers):
`Acharyya2024/WellKnown.lean:23` = `dist_dist_dist_le`;
`sqrt_sum_sq_le_sum_abs` (wrapper over `Finset.sum_sq_le_sq_sum_of_nonneg`);
`abs_sqrt_rawStress_sub_le` (reverse triangle in ℓ² in disguise);
`mds_nonempty` (pattern = `Continuous.exists_forall_le'`); `RankGap.lean` and
`Overlap.lean` packaging (paper-specific composition glue);
`MatrixPerturbation.sortedEigenvalues` (duplicate of Mathlib's
`Matrix.IsHermitian.eigenvalues₀`).

**Local cleanup opportunities** (not blocking, nice-to-have): migrate
`sortedEigenvalues` to `eigenvalues₀`.

---

## Detailed dossiers

### 1. Procrustes rigidity — best spectral value/effort

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

### 2. QoL small-lemma bundle (one PR)

- `highProbAtTop_of_tendsto_compl_zero` kernel
  (`Acharyya2025/RateChain.lean:75`): measurability-free `1 − μ sᶜ ≤ μ s` for
  probability measures via subadditivity `1 = μ(s ∪ sᶜ) ≤ μ s + μ sᶜ`.
  Mathlib's `prob_compl_eq_one_sub₀` needs `NullMeasurableSet`,
  `prob_compl_le_one_sub_of_le_prob` needs `MeasurableSet`; nothing
  measurability-free exists. Home:
  `MeasureTheory/Measure/Typeclasses/Probability.lean`.
- `meas_gt_le_ofReal_secondMoment_div_sq` (`Acharyya2024/Probability.lean:49`):
  uncentered second-moment Chebyshev `P{η < Y} ≤ ofReal(v/η²)` from
  `∫ Y² ≤ v`, no measurability of `Y`. Mathlib's
  `meas_ge_le_variance_div_sq` (`Probability/Moments/Variance.lean:380`) is
  centered and needs `MemLp 2`. Home: next to it.

### 3. Courant–Fischer + Weyl — the largest genuine spectral gap

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

### 4. Vector-valued sample-mean MSE

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

### 5. Rank-constrained PSD Gram realization + eigenvalue tail

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

### 6. Quantitative polar factor

`exists_isometry_close_of_self_adjoint_comp_close` (`PolarFactor.lean:93`):
`|⟪Mx,Mx⟫ − ⟪x,x⟫| ≤ δ⟪x,x⟫` with `δ ≤ 1/2` ⇒ ∃ isometry `W` with
`‖(M−W)x‖ ≤ 2δ‖x‖`; constructed as `M ∘ (MᵀM)^{−1/2}` from the eigenbasis —
no CFC, no SVD. Mathlib has NO polar decomposition in any form (verified;
"polar" hits only convex-duality polars and polar coordinates). Idiom work:
return a bundled `F →ₗᵢ[𝕜] F`/`≃ₗᵢ`; hypothesis as `‖M†M − 1‖ ≤ δ`. Selling
point: quantitative, which a future CFC-based polar decomposition would not
directly give. Sharp constant is `√(1+δ)·δ`; we ship `2δ` (documented).
Scalar helper `abs_one_sub_inv_sqrt_le` (`:43`) is a free S-grade lemma.

### 7. `TendstoInMeasure` from a vanishing HP rate

`tendsto_measure_abs_gt_zero_of_highProb_abs_le_rate`
(`Acharyya2024/WellKnown.lean:112`): HP events `|Xₙ| ≤ rate n` with
`rate → 0` ⇒ convergence in measure. `ConvergenceInMeasure.lean` has only the
a.e. (`tendstoInMeasure_of_tendsto_ae`) and Lp
(`tendstoInMeasure_of_tendsto_eLpNorm`) constructors — yet the HP-rate form is
how concentration results are actually consumed. Generalize ℝ → pseudometric,
general filter; drop the `MeasurableSet` hypothesis via the bundle-2
complement lemma.
