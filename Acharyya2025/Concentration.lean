/-
Historical record of the retired scaffold layer for:

Acharyya, Agterberg, Park, Priebe.
"Concentration bounds on response-based vector embeddings of black-box generative models"
arXiv:2511.08307.

Status (2026-06-11):
- Every declaration that previously lived here was an unproved scaffold whose
  statement was FALSE as written (vacuous `Prop`-field hypothesis structures,
  arbitrary estimators, placeholder `1/(u+1)` rates, unaligned `ConfigError`).
- All of that content is now PROVED, in true form, elsewhere.  The live
  probability layer is:
  * `Acharyya2025.Bridge` — deterministic + high-probability event propagation
    (`response_mean_close_hp_to_frob_hp`, `frob_close_hp_to_entrywise_close_hp`,
    `entrywise_close_to_cmds_entrywise_close_of_bounded`, explicit rates
    `responseFrobRate` / `cmdsEntrywiseRate`);
  * `Acharyya2025.AlignedPipeline` — the aligned spectral estimator and the
    high-probability aligned perturbation theorems
    (`highProb_aligned_configError_of_entrywise_close`,
    `highProb_aligned_configError_of_response_mean`);
  * `Acharyya2024.Probability` + `Acharyya2024.SecondMoment` — the
    Markov/variance concentration step feeding the response-mean event.
- This file and its namespace are retained so `import Acharyya2025.Concentration`
  (in `Acharyya2025.Basic` and `DkpsQuench.AcharyyaBridge`) keeps working; the
  namespace body is now comment-only.  The original statements are in git
  history (see commits noted in planning/acharyya-plan.md).
-/

import Acharyya2025.Deterministic

namespace Acharyya2025.Concentration

/-! ### Retired seam (2026-06-11): `ResponseRegularity`

Original purpose: abstract placeholder for the paper's response-variance /
covariance-trace control (bounded covariance trace, replicate growth, eigengap
stability, fixed embedding dimension), intended as the hypothesis package for
response-level concentration.  Citation worth keeping: Acharyya, Agterberg,
Park, Priebe, arXiv:2511.08307, Theorem 1 and Corollary 1.  Why it was FALSE
as written: every field was a bare `Prop` (e.g. `bounded_covariance_trace :
Prop`), so the structure constrained nothing — any instantiation with `True`
(or `False`) type-checked, making the theorems quantifying over it vacuously
demand conclusions from no actual assumptions.  Proved TRUE replacement: the
real hypotheses now appear explicitly in
`Acharyya2025.Bridge.response_mean_close_hp_to_frob_hp` (uniform response-mean
closeness events) fed by `Acharyya2024.Probability` and
`Acharyya2024.SecondMoment` (genuine Markov/variance bounds).

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

/-! ### Retired seam (2026-06-11): `DissimilarityProcess`

Original purpose: bundle a sample dissimilarity process `sample : Nat → Ω →
DisMat n` with a population dissimilarity matrix `population : DisMat n`.  Why
it was FALSE-enabling as written: the `sample` field was completely arbitrary —
nothing tied it to responses, to `population`, or to any measure — so theorems
taking a `DissimilarityProcess` claimed concentration for ALL functions
`Nat → Ω → DisMat n`, which is false.  Proved TRUE replacement: the live chain
works directly with `responseDist (Xbar u ω)` versus `responseDist μ` in
`Acharyya2025.Bridge` (see `response_mean_close_hp_to_frob_hp` and
`dkps`-facing consumers in `Acharyya2025.AlignedPipeline`), where the estimator
is the concrete one induced by response means.

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

/-! ### Retired seam (2026-06-11): `MDSStabilityAssumptions`

Original purpose: spectral/MDS stability precondition (population rank `d`,
eigengap, nondegenerate configuration) for the classical-MDS perturbation step.
Citations worth keeping: Acharyya, Agterberg, Park, Priebe, arXiv:2511.08307,
Theorem 2 and Appendix A; Yu, Wang, Samworth (2015), "A useful variant of the
Davis-Kahan theorem for statisticians", Biometrika 102(2):315-323.  Why it was
FALSE-enabling as written: all three fields were bare `Prop`s
(`population_rank_d : Prop`, `eigengap : Prop`,
`nondegenerate_configuration : Prop`), constraining nothing.  Proved TRUE
replacement: `Acharyya2025.SpectralPipeline.CMDSpectralAssumptions` (hardened:
genuine `PosSemidef` and `rank ≤ d` fields) plus explicit quantitative
eigengap/floor hypotheses (`α`, `Λ`) taken directly by
`Acharyya2025.ConfigPerturbation` and
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`.

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

/-! ### Retired seam (2026-06-11): `dissimilarity_matrix_concentrates`

Original purpose: the matrix-concentration layer — from response-level sampling
to high-probability control of the sample dissimilarity matrix around the
population dissimilarity matrix.  Citation worth keeping: Acharyya, Agterberg,
Park, Priebe, "Concentration bounds on response-based vector embeddings of
black-box generative models", Theorem 1 and Corollary 1.  Why it was FALSE as
written: it quantified over a vacuous `ResponseRegularity` (bare `Prop` fields)
and an arbitrary `proc.sample` (no link to any sampling mechanism or to
`proc.population`), and asserted the placeholder rate `1/(u+1)` — so the
statement claimed a universal concentration bound that fails for almost any
instantiation.  Proved TRUE replacement:
`Acharyya2025.Bridge.response_mean_close_hp_to_frob_hp` (high-probability
propagation with the explicit `responseFrobRate`) fed by
`Acharyya2024.Probability` + `Acharyya2024.SecondMoment` (the Markov/variance
concentration step).

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

/-! ### Retired seam (2026-06-11): `classical_mds_embedding_perturbation`

Original purpose: the Weyl/Davis-Kahan/classical-MDS stability step — if the
centered/noisy matrix is close to the population matrix and the eigenstructure
is stable, sample DKPS coordinates are close to population DKPS coordinates up
to an orthogonal alignment.  Citations worth keeping: Acharyya, Agterberg,
Park, Priebe, Theorem 2 and Appendix A; Yu, Wang, Samworth (2015), "A useful
variant of the Davis-Kahan theorem for statisticians", Biometrika
102(2):315-323; Chen, Chi, Fan, Ma et al. (2021), "Spectral Methods for Data
Science: A Statistical Perspective", Foundations and Trends in Machine Learning
14(5):566-806; Agterberg, Lubberts, Arroyo (2022), the decomposition strategy
used by Acharyya et al. for CMDS perturbation.  Why it was FALSE as written:
`MDSStabilityAssumptions` was vacuous (`Prop` fields), `ψhat` was an arbitrary
function with no link to the dissimilarity process, the rate `1/(u+1)` was a
placeholder, and the conclusion used unaligned `ConfigError` although CMDS
output is only defined up to an orthogonal transformation in O(d).  Proved TRUE
replacement:
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`
(built on
`Acharyya2025.MatrixPerturbation.exists_isometry_configError_le_of_entrywise_close`
and `Acharyya2025.ConfigPerturbation.exists_isometry_configError_spectralConfig_le`),
with explicit `∃ W` isometry alignment baked into `alignedSpectralConfig`,
genuine eigengap/floor hypotheses, and the explicit `configBound` rate.

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

/-! ### Retired seam (2026-06-11): `dkps_embedding_concentration_scaffold`

Original purpose: the downstream-facing high-probability DKPS embedding
concentration shape needed by `DkpsQuench.Basic` (concentration hypothesis) and
`Helm2025.Basic` (alignment-consistency hypothesis); the docstring noted the
paper-faithful `Poly_3((n^3/r)^(1/2-delta))` rate as future work.  Citation
worth keeping: Acharyya, Agterberg, Park, Priebe, arXiv:2511.08307.  Why it was
FALSE as written: it merely re-exported `classical_mds_embedding_perturbation`
(inheriting its unproved, false statement) and therefore carried all the same
defects — vacuous hypothesis structures, arbitrary `ψhat`, placeholder rate,
unaligned `ConfigError`.  Proved TRUE replacement:
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean`,
the end-to-end response-mean-to-aligned-configuration concentration theorem.

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

/-! ### Retired seam (2026-06-11): `quench_style_uniform_embedding_error`

Original purpose: the downstream compatibility target for the Quench
concentration hypothesis — a uniform (over models `i : Fin n`) high-probability
embedding-error event derived componentwise from the configuration-level event.
Why it was FALSE as written: it was a direct corollary of
`dkps_embedding_concentration_scaffold` and inherited that statement's
unproved, false content (vacuous `ResponseRegularity` /
`MDSStabilityAssumptions`, arbitrary estimator, placeholder rate, unaligned
error).  Proved TRUE replacement:
`DkpsQuench.AcharyyaBridge.quench_uniform_embedding_error_of_aligned_spectral`,
which composes the proved aligned spectral capstone with the index-map
factorization lift `quench_uniform_embedding_error_of_finite_configError`.

Retired by Claude Fable 5 (claude-fable-5[1m]);
retained as prose for the formalization case-study record. The original
statement is in git history (see commits noted in planning/acharyya-plan.md).
-/

end Acharyya2025.Concentration
