# DKPS formalization — challenge manifest

This repository fully formalizes four DKPS-family papers (the **end states**) and,
in the course of proving them, produced a number of reusable, Mathlib-quality
results (the **hard upstream proofs**). The challenges are organized into three
families that separate *role* and *upstream readiness*:

```
Challenge/
  MathlibCandidate/  — drop-ready upstream PRs, one folder per PR (leaf theorems only)
  MathlibPending/     — proven, but not yet PR-shaped (needs generality / destination / sharpening)
```

The four DKPS papers — the repo's actual **end states** — are documented in §"DKPS
papers" below and in each library's author-facing `README.md`, but they are
deliberately **not** comparator challenges: their statements are inherently in each
paper's own vocabulary (`bayesRisk`, `ConfigError`, `MDS`, …), and the comparator
can only certify a proof is axiom-clean — it cannot certify those definitions
faithfully model the paper. That faithfulness is a human reading task, so a
comparator artifact there would add no trust. The comparators stay purely
Mathlib-candidate-focused.

Principles:

- **Leaf theorems only.** Each challenge lists only the *leaf* (top-level) theorems
  — those not used to prove any other listed theorem. `#print axioms` on a leaf
  transitively certifies its entire proof tree, so the supporting lemmas need not
  be listed. This is the same "expose only the entry point" rule a comparator
  reviewer asked for.
- **Axiom gate.** Every listed theorem is verified to depend only on
  `propext, Classical.choice, Quot.sound` — no `sorryAx`, no custom axioms.
- **No false dependency arrows.** The Mathlib contributions are *independent*,
  reusable results. They were *motivated* by the DKPS work but are not owned by any
  paper, so this manifest does not link candidates to papers as dependencies.

Gap claims below were checked against a local Mathlib checkout (date 2026-06-14).

---

## Family 1 — `MathlibCandidate/` (the focused upstream push)

**Strategy: a small, strong opening hand.** Three canonical results, each a verified
gap in Mathlib, are enough to establish credibility and earn maintainer engagement
for the rest. Keeping this set minimal is deliberate — fewer, higher-value PRs for
reviewers to look at first.

| # | Challenge | Leaf theorem(s) | Destination | Why it clears the bar |
|---|---|---|---|---|
| 01 | GramRigidity | `Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq` | `Analysis/InnerProductSpace/GramMatrix.lean` | **in review**; canonical (Gram rigidity) |
| 02 | CourantFischerWeyl | `abs_eigenvalues_sub_le_opNorm` (k-th eigenvalue min–max + Weyl perturbation) | new `Analysis/InnerProductSpace/CourantFischer.lean` | Mathlib has only Rayleigh + the extremal eigenvalue; **Weyl & k-th min–max absent**. Canonical |
| 03 | DavisKahan | `sum_norm_sub_starProjection_span_sq_le`, `sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor` | new `Analysis/InnerProductSpace/DavisKahan.lean` | sin-Θ theorem **absent**. Canonical |

---

## Family 2 — `MathlibPending/` (proven, but held back)

All sorry-free and axiom-clean, but **not** part of the opening push — each either
needs work to clear the maintainer bar, or is being deliberately held until the
headline three land and reviewers can help triage. Each may graduate to a Candidate
later.

| Challenge | Leaf theorem(s) | Why pending |
|---|---|---|
| Berge | `continuous_iInf_of_isCompact`, `upperHemicontinuousAt_isMinOn`, `exists_modulus_isMinOn` | likely proven in **too narrow a form** for a canonical Mathlib `Topology` contribution; needs generalization to holistic, reusable shape before it's maintainer-quality |
| RankFactorization | `Matrix.rank_le_iff_exists_eq_mul` | matrix form absent but must be related to abstract `rank_le_iff_exists_linearMap`; confirm framing/value |
| RankPsdRealization | `Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`, `Matrix.eigenvalues₀_eq_zero_of_le` | plain `posSemidef_conjTranspose_mul_self` already exists — only the rank-**control** is novel; confirm it's worth a PR |
| RestrictCoverMeasurable | `measurable_of_iUnion_restrict` | clean countable analogue, but minor; confirm worth standing alone |
| SampleMeanMSE | `integral_norm_sq_average_sub_of_iid`, `integral_norm_sq_average_sub_le_of_bound` | vector-valued (scalar variance exists); confirm not trivially derivable |
| NearIsometry | `LinearMap.exists_linearIsometryEquiv_norm_sub_le`, `ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le` | quantitative polar factor; niche |
| CfcMeasurable | `measurable_cfc_comp`, `measurableSet_exists_mem_le` | involved proof; destination unsettled |
| MatrixConcentration | `measure_forall_sortedEig_ge_ge` (+ entrywise→operator helpers) | elementary route gives **loose `n`/`n²` constants**; Mathlib would want a matrix-Bernstein sharpening |
| SpectralFunctionMeasurable | `Matrix.measurable_specTransform` | novel, but **deliberately unused** by the final discharge; no settled home. Its (matrix-valued measurability) statement is not cleanly Mathlib-only expressible, so it carries an **axiom-audit `Leaderboard` only** — no Mathlib-only `Conformance`/comparator config |
| ProbabilityQoL | `one_sub_measure_compl_le`, `meas_gt_le_ofReal_integral_sq_div_sq` | **too small** to stand alone |
| TendstoInMeasure | `tendstoInMeasure_of_tendsto_measure_dist_le_rate` | verify it is substantive vs. a thin wrapper |

---

## DKPS papers — the repo's end states (documented, not comparator challenges)

These are the four fully-formalized papers all the upstream work was in service of.
They are **not** comparator challenges (see the rationale in the intro). Each was
verified clean — `#print axioms = {propext, Classical.choice, Quot.sound}`, no
`sorryAx`, no custom axioms (checked 2026-06-14). Headline statements and any
"beyond the paper" assumptions are documented in each library's `README.md`.

| Paper | Main theorem(s) | Axiom status |
|---|---|---|
| Acharyya2024 | `Consistency.fixed_models_fixed_queries_consistency`, `…fixed_models_growing_queries_consistency`, `…growing_models_growing_queries_consistency`(`_of_sample_limit`) | clean ✓ |
| Acharyya2025 | `RateChain.tendsto_endToEndRate_zero` (+ `tendsto_configBound_comp_zero`) | clean ✓ |
| DkpsQuench | `AcharyyaBridge.quench_uniform_embedding_error_of_finite_configError`, `queryEfficient_nn_of_second_moment` | clean ✓ |
| Helm2025 | `DKPS.Theorem1`, `DKPS.Theorem2_bayes` (+ `alignmentConsistency_of_highProb_configError`) | clean ✓ |

---

## Replaces

This manifest supersedes the old `Challenge/Gram`, `Challenge/PsdGram`,
`Challenge/Spectral`, and `Challenge/Inventory/*` challenges (including the
69-theorem aggregate), which mixed headline results with their supporting lemmas.
