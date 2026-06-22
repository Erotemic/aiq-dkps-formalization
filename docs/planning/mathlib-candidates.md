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
(`Acharyya2025/GramRigidity.lean`, `Acharyya2025/RateChain.lean`,
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
* **#5 proof shape — SUPERSEDED (Fable, 2026-06-12).** The R2b recon found the
  blocker was Mathlib's missing rank-factorization API; **candidate #14 below now
  supplies it**, and the PSD forward direction is reproved through the API: square
  factorization `PosSemidef.exists_eq_conjTranspose_mul_self` (spectral, no index
  packing) → rank-factor the square factor through `Fin d` → absorb `Lᴴ·L` by a
  second square factorization. The `Classical.choose`/embedding construction is
  **gone** (audit §2.3 discharged).

**Candidate #14 — rank factorization (`Matrix.exists_eq_mul_rank` /
`exists_eq_mul_of_rank_le` / `rank_le_iff_exists_eq_mul`): STAGED (Fable,
2026-06-12),** `ForMathlib/LinearAlgebra/Matrix/RankFactorization.lean`. Every
matrix over a field factors `M = L·R` with inner dimension `M.rank` (basis of the
column space + coordinates), zero-padded to any `r ≥ rank`, and conversely any
factorization through `Fin r` bounds the rank — `M.rank ≤ r ↔ ∃ L R, M = L * R`.
Textbook-foundational, entirely absent upstream (verified in the R2b recon);
proposed home `Mathlib/LinearAlgebra/Matrix/Rank.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).

Effort grades: **S** = statement+proof port nearly verbatim; **M** = moderate
generalization (typically ℝ → `RCLike 𝕜`, restating in Mathlib idiom);
**L** = substantial redesign.

---

## Unified priority ranking (value per effort)

| # | Candidate | Source | Effort | Proposed home |
|---|-----------|--------|--------|---------------|
| 1 | Gram rigidity (equal Grams ⇒ linear isometry equiv) | `Acharyya2025/GramRigidity.lean:49` | S/M | `Analysis/InnerProductSpace/GramMatrix.lean` |
| 2 | QoL small-lemma bundle: measurability-free `1 − μ sᶜ ≤ μ s`; uncentered second-moment Chebyshev | `Acharyya2025/RateChain.lean:75`, `Acharyya2024/Probability.lean:49` | S | next to the existing siblings (see §2) |
| 3 | Courant–Fischer (k-th eigenvalue, both directions) + Weyl's eigenvalue perturbation inequality | `Acharyya2025/Weyl.lean:142,196,260` | M | new `Analysis/InnerProductSpace/CourantFischer.lean` |
| 4 | Vector-valued sample-mean MSE: `E‖X̄−μ‖² = r⁻²Σₖ E‖Xₖ−μ‖²` + iid trace(Σ)/r + `≤ γ/r` | `Acharyya2024/SecondMoment.lean:143,232,265` | M | `Probability/Moments/Variance.lean` or new `SampleMean.lean` |
| 5 | Rank-constrained PSD Gram realization (`PosSemidef ∧ rank ≤ d ↔ ∃ A : Matrix (Fin d) n 𝕜, B = Aᴴ*A`) + `eigenvalues₀` tail-vanishing | `Acharyya2025/GramRealization.lean:96`, `MatrixPerturbation.lean:130` | M | `GramMatrix.lean` / `Analysis/Matrix/Spectrum.lean` |
| 6 | Quantitative polar factor (near-isometry ⇒ isometry within 2δ, no CFC/SVD) | `Acharyya2025/PolarFactor.lean:93` | M | new `Analysis/InnerProductSpace/NearIsometry.lean` |
| 7 | `TendstoInMeasure` constructor from a vanishing high-probability rate | `Acharyya2024/WellKnown.lean:112` | S–M | `MeasureTheory/Function/ConvergenceInMeasure.lean` |
| 8 | Davis–Kahan cross-block (squared sin-Θ) bound + rank-`d`/floor corollary | `Acharyya2025/DavisKahan.lean:135`, `RankGap.lean:42,78` | M | new `Analysis/InnerProductSpace/DavisKahan.lean` |
| 9 | Measurability of the continuous functional calculus in the element: `ω ↦ cfc f (a ω)` measurable for fixed continuous `f`, measurable self-adjoint-valued `a` in a C⋆-algebra (continuity of `cfc` on bounded-spectrum sets + countable norm cover) | `ForMathlib/MeasureTheory/CfcMeasurable.lean` (STAGED) | S/M | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean` |
| 10 | Measurability of the spectral `h`-transform `Σₖ h(λₖ) uₖuₖᵀ` of a measurable Hermitian-matrix family, for fixed continuous `h` — via entrywise pointwise limit of matrix *polynomials* (Stone–Weierstrass on a spectral interval); **no cfc, no eigenbasis selection** | `ForMathlib/Analysis/Matrix/SpectralFunctionMeasurable.lean` (STAGED, `measurable_specTransform`) | M | `Analysis/Matrix/Spectrum.lean` |
| 11 | Countable restrict-cover measurability: `⋃ₖ sₖ = univ`, each `sₖ` measurable, each `sₖ.restrict g` measurable ⇒ `g` measurable (countable analogue of `measurable_of_restrict_of_restrict_compl`) | `ForMathlib/MeasureTheory/CfcMeasurable.lean` (STAGED, `measurable_of_iUnion_restrict`) | S | `MeasureTheory/MeasurableSpace/Constructions.lean` |

**Update 2026-06-12 (Opus session, `hmeas_spec` discharge):** three new
measurability candidates (#9–#11) surfaced while discharging the DkpsQuench
`hmeas_spec` seam.  #9 (`measurable_cfc_comp`) and #11
(`measurable_of_iUnion_restrict`) are STAGED in
`ForMathlib/MeasureTheory/CfcMeasurable.lean` (built green, RCLike-where-applicable
C⋆-algebra generality).  **#10 (`measurable_specTransform`) is now STAGED** in
`ForMathlib/Analysis/Matrix/SpectralFunctionMeasurable.lean` — the most novel of
the three: measurability of a *spectral function* of a measurable Hermitian-matrix
family with no continuous functional calculus and no (non-measurable) eigenbasis,
obtained purely from polynomial (Stone–Weierstrass) approximation glued over a
countable entrywise-norm cover.  On extracting it, the dev file
`Acharyya2025/SpectralMeasurability.lean` was trimmed (740 → 110 lines) to just the
two facts the bridge uses (`measurable_cmds_matrix`,
`measurableSet_entrywiseClose_event`); the former general spectral-split assembly
(`measurableSet_alignExists_inter` etc.) was unused by the discharge — its general
core is now the staged #10.  Note: the final `hmeas_spec` discharge uses neither #9
nor #10 (it goes through the deterministic CMDS-entrywise route); these are kept as
general staged results.  See `docs/planning/historical/hmeas-spec-discharge.md`.

**Candidate #12 — sample-covariance / empirical-Gram eigenvalue concentration
(`halign` route): NOW STAGED.**  Mathlib has no sample-covariance eigenvalue
concentration; this is the elementary, no-matrix-Bernstein route (entrywise
Chebyshev + union bound, then entrywise → operator-norm → Weyl), staged in two
layers:
- `ForMathlib/Analysis/Matrix/EntrywiseEigenvalue.lean` —
  `abs_sortedEig_sub_le_of_entry_le` (entrywise `ε`-close ⇒ eigenvalues within
  `n·ε`, Weyl through the entrywise→operator comparison).
- `ForMathlib/Probability/Moments/MatrixConcentration.lean` — the random-matrix
  engine: `measure_exists_entry_gt_le` (entrywise union bound),
  `measure_forall_abs_sortedEig_sub_le_ge` (eigenvalue concentration),
  `measure_forall_sortedEig_ge_ge` (eigenvalue **lower bound**, take
  `η = c/(2n)`).  Takes per-entry second-moment bounds as hypotheses.
- `ForMathlib/Probability/Moments/SampleCovariance.lean` — the iid → per-entry
  specialization to the actual empirical covariance
  `Σ̂_{kl} = n⁻¹ Σᵢ Vᵢ(k)Vᵢ(l)`: `sampleCovariance`,
  `integral_sq_sampleCovariance_entry_le` (coordinate products fed through the
  scalar `integral_norm_sq_average_sub_of_iid`), `isHermitian_sampleCovariance`,
  and the capstone `measure_forall_sampleCovariance_sortedEig_ge_ge`.

This furnishes the eigengap Helm's `halign` needs (a population eigenvalue
floored at `c` stays above `c/2` w.h.p.).  Loose `n`/`n²` constants (the price
of the elementary route); a matrix-Bernstein sharpening is possible future work.

**Candidate #13 — Berge's maximum theorem (fixed compact constraint): NOW
STAGED.**  Mathlib has the hemicontinuity *definitions*
(`Topology/Semicontinuity/Hemicontinuity.lean`) and the extreme-value theorem
(`IsCompact.exists_isMinOn`) but NO Berge maximum theorem.  Staged in
`ForMathlib/Topology/Berge.lean` (the upper-hemicontinuity half), building on the
approximate-minimizer engine:
- `tendsto_eval_sub_of_isCompact` — sequential uniform convergence on a compact
  `K` from joint continuity: `g (pₖ)(xₖ) − g p₀(xₖ) → 0` for `pₖ → p₀`, `xₖ ∈ K`
  (proved via the subsequence criterion + sequential compactness, no compact-open
  topology).
- `tendsto_subseq_isMinOn_of_isMinOn` — sequential upper hemicontinuity (closed
  graph): constrained minimizers for `pₖ → p₀` subconverge to a constrained
  minimizer of `g p₀`.
- `upperHemicontinuousAt_isMinOn` — the closed-graph statement on Mathlib's own
  `UpperHemicontinuousAt` predicate for `p ↦ {x ∈ K | IsMinOn (g p) K x}`, via
  `UpperHemicontinuousAt.of_sequences` (needs `X` Hausdorff so `K` is closed).
- `continuous_iInf_of_isCompact` — the **value-function-continuity** half of
  Berge (`p ↦ ⨅ x ∈ K, g p x` continuous), via a squeeze using
  `tendsto_eval_sub_of_isCompact`.
- `exists_modulus_isMinOn_family` — the uniform `ε`–`δ` modulus measured by a
  **finite family of jointly-continuous closeness invariants** `ρ i` with
  `ρ i x x = 0` (captures the affine-invariant `pairDistErr` of MDS, where the
  ambient metric is the wrong notion); `exists_modulus_isMinOn` is its `ι = Unit`,
  `ρ = dist` corollary.

Engine generalization (in `ForMathlib/Topology/ApproxMinimizer.lean`):
`exists_subseq_tendsto_isMinOn_of_approxMinOn`, the `K`-constrained sibling of
`exists_subseq_tendsto_forall_le_of_approxMin` (concludes `IsMinOn F K` rather
than a global minimizer).  Both halves of Berge (upper hemicontinuity + value
continuity) are now staged.  Resolves for-fable F3 without Fable.

Note on the MDS modulus `exists_modulus_pairDist`: the family-modulus form closes
the *metric* gap (the `pairDistErr` family is exactly a family of continuous
invariants), but a literal re-derivation is NOT possible from the fixed-`K`
theorem — MDS minimizes over the non-compact config space and recovers
compactness only via coercive centering into a `Δ`-dependent box, an MDS-specific
ingredient.  Documented at `exists_modulus_pairDist`; bespoke proof kept.

**Candidate #8 projector form — REDESIGNED (Fable, 2026-06-12), audit §4
discharged.** The bespoke ℝ-only `spectralProjection` finite-sum def is gone; the
projector section of `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean` is
now phrased with **Mathlib's `Submodule.starProjection`** of orthonormal-subfamily
spans, over **`RCLike 𝕜`**, with the index cutoff generalized to an **arbitrary
`s : Finset (Fin m)`** (`sᶜ` the complementary block). New bridge lemmas (each
independently Mathlib-worthy, proposed home near
`OrthonormalBasis.starProjection_eq_sum_rankOne`):
`Orthonormal.starProjection_span_image_apply` (projection onto the span of an
orthonormal subfamily = sum of rank-ones), `…_apply_self`, and the Parseval
`Orthonormal.norm_sq_starProjection_span_image` — **all three hold in any inner
product space** (no `FiniteDimensional` on the ambient space; they take
`[(span 𝕜 (w '' ↑s)).HasOrthogonalProjection]`, which fires automatically in the
finite-dimensional spectral-subspace application), Opus follow-on 2026-06-12.
Main results renamed:
`sum_norm_sub_starProjection_span_sq_eq` (identity, arbitrary `s`) and
`sum_norm_sub_starProjection_span_sq_le` (the `2nε²/gap²` sin-Θ bound).

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
argmin modulus `exists_modulus_pairDist` — see `planning/historical/for-fable.md` F3.

Remaining non-trivial items are catalogued in `planning/historical/for-fable.md` (RCLike
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

### 1. Gram rigidity — best spectral value/effort

`exists_linearIsometryEquiv_map_eq_of_inner_eq` (`Acharyya2025/GramRigidity.lean:49`):
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
