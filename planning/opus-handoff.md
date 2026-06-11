# Handoff plan: finish the ForMathlib staging effort

Written 2026-06-11 by Claude Fable 5 for a follow-up (Opus) agent.
Context: `planning/mathlib-candidates.md` (ranked dossiers, gap claims),
`ForMathlib/README.md` (staging conventions + PR workflow).

## State at handoff (everything below is COMMITTED and builds green)

Workspace: mathlib master `476fb97b621c` (2026-06-11), toolchain v4.31.0-rc2.
`lake build` = 0 errors, 0 warnings, 0 sorry/axiom across all 5 libraries.

Staged in `ForMathlib/` (one file per target Mathlib path, all RCLike where
noted, paper libs rewired as thin consumers):

| Candidate | Staged file | Rewired consumer |
|---|---|---|
| #1 Procrustes rigidity (RCLike + `Matrix.gram` iff) | `Analysis/InnerProductSpace/GramMatrix.lean` | `Acharyya2025/Procrustes.lean` |
| #2a measurability-free `1 − μ sᶜ ≤ μ s` | `MeasureTheory/Measure/Typeclasses/Probability.lean` | `Acharyya2025/RateChain.lean` |
| #2b uncentered second-moment Chebyshev | `Probability/Moments/Variance.lean` | `Acharyya2024/Probability.lean` |
| #3a Courant–Fischer (both directions) + Weyl (RCLike) | `Analysis/InnerProductSpace/CourantFischer.lean` | `Acharyya2025/Weyl.lean` |
| #3b DK cross-term identity (RCLike) | `Analysis/InnerProductSpace/Spectrum.lean` | `Acharyya2025/DavisKahan.lean` |
| #6 quantitative polar factor (bundled `≃ₗᵢ`, + CLM opNorm corollary, + scalar `abs_one_sub_inv_sqrt_le`) | `Analysis/InnerProductSpace/NearIsometry.lean` | `Acharyya2025/PolarFactor.lean` |
| #7 `TendstoInMeasure` HP-rate constructors (general filter, EDist/pseudometric, measurability-free) | `MeasureTheory/Function/ConvergenceInMeasure.lean` | `Acharyya2024/WellKnown.lean` |

Notable finding recorded in #7's docstrings: the `μ(good) → 1` corollary
NEEDS `NullMeasurableSet` (a set and its complement can both have outer
measure 1), so it cannot be made measurability-free.

## Task A — stage candidate #4 (vector-valued sample-mean MSE)  [unstarted]

Source: `Acharyya2024/SecondMoment.lean` (293 lines). Theorems at ~:58
(scalar pairwise-indep variance algebra), :143 (E‖X̄−μ‖² = r⁻²Σₖ E‖Xₖ−μ‖²),
:232 (iid trace form), :265 (≤ γ/r corollary).
Target: new `ForMathlib/Probability/Moments/SampleMean.lean`.
Gap re-verified 2026-06-11 against the current pin: Mathlib `variance` is
ℝ-valued only; `covarianceBilin`/`covarianceOperator`
(`Mathlib/Probability/Moments/CovarianceBilin.lean`) have NO trace identity
and NO sample-mean API.
Generalize: value space `EuclideanSpace ℝ ι` → finite-dim real IPS via
`stdOrthonormalBasis`; weaken `iIndepFun` to per-coordinate pairwise
independence (all the proof uses; `IndepFun.variance_sum` already accepts
pairwise). Then rewire `Acharyya2024/SecondMoment.lean` (keep every public
name/statement; thin wrappers; matrix-entangled statements may keep local
proofs — say so in the commit).

## Task B — stage candidate #5 (rank-constrained PSD Gram realization)  [unstarted]

Sources: `Acharyya2025/GramRealization.lean:96`
(`exists_config_gram_eq_of_posSemidef_rank_le`) and
`Acharyya2025/MatrixPerturbation.lean:130` (`sortedEigenvalues_tail_eq_zero`).
Targets: `ForMathlib/LinearAlgebra/Matrix/PosDef.lean` with the RCLike iff
`B.PosSemidef ∧ B.rank ≤ d ↔ ∃ A : Matrix (Fin d) n 𝕜, B = Aᴴ * A`
(← direction: `posSemidef_conjTranspose_mul_self` EXISTS upstream at
`Mathlib/LinearAlgebra/Matrix/PosDef.lean:355` + `rank_mul_le`; → direction:
source proof via spectral theorem + injection of nonzero-eig indices into
`Fin d`); and `ForMathlib/Analysis/Matrix/Spectrum.lean` with
`Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le` (counting proof via
`rank_eq_card_non_zero_eigs` + `eigenvalues₀` antitonicity — shorter than the
source's operator-range detour). Rewire GramRealization.lean; rewire
MatrixPerturbation.lean ONLY if the sortedEigenvalues/eigenvalues₀
permutation bridge is painless, else leave and note it.

## Task C — integration chores after A/B

1. Add the new imports to `ForMathlib.lean` (keep alphabetical).
2. Update the inventory tables in `ForMathlib/README.md` and the staging
   status block in `planning/mathlib-candidates.md` (it currently lists
   #1/#2/#3b staged — also outdated: #3a/#6/#7 are now staged; fix in the
   same pass and add #4/#5).
3. Full `lake build` (must be 0 errors / 0 warnings),
   `grep -RIn 'axiom\|sorry'` census = 0.
4. Commit per candidate (style: see `git log` — upgrade/staging/rewire
   commits of 2026-06-11; footer `Co-Authored-By: Claude ...`; note: this
   environment lacks the user's GPG key, use `git -c commit.gpgsign=false`).

## Task D — deferred/optional (from mathlib-candidates.md "deferred" list)

- ℓ²-opNorm vs Frobenius vs entrywise norm-comparison PR
  (`Matrix.l2_opNorm_le_frobenius` + entrywise corollary).
- Davis–Kahan theorem itself in projector form (needs design; the crude
  `n·ε²/gap²` constant should be improved before upstreaming).
- Local cleanup: migrate `MatrixPerturbation.sortedEigenvalues` to Mathlib's
  `eigenvalues₀`.

## Task E — PR pipeline (when the user says go; do NOT push/PR without them)

Sequencing (small trust-builders first): (1) #2a+#2b QoL bundle, (2) #3b
cross-term, (3) #7 constructors, (4) #1 Procrustes into GramMatrix.lean,
(5) #6 polar factor, (6) #3a Courant–Fischer+Weyl (split: helpers/quadratic
form, then CF+Weyl), (7) #4, #5.
Per PR: copy staged decls into a mathlib fork dropping the `ForMathlib`
namespace; convert header to the module system (`module`,
`public import`, `@[expose] public section` — see any current mathlib file);
mathlib copyright header; disclose AI assistance per mathlib policy (a human
author must understand and vouch for every line). After a PR lands: delete
the staged file, bump the pin, re-run the consumers.

## Verification protocol (use everywhere)

- Iterate single files with `~/.elan/bin/lake env lean <file>` (no build lock).
- Build one staged module: `lake build ForMathlib.<Dotted.Module.Name>`.
- Known traps hit this session (details in planning/acharyya-plan.md ledger):
  generic `le_tsub_of_add_le_right`/`tsub_add_tsub_comm` don't apply to
  ENNReal (use the `ENNReal.*` variants); `⟪x, y⟫_𝕜`/`⟪x, y⟫_ℝ` need
  `open scoped InnerProductSpace` (Real scope alone gives only plain `⟪,⟫`
  and `|⟪…⟫_ℝ|` then fails to parse); `convert … using 1` often no longer
  closes defeq goals — prefer `exact`; deprecations: `push_neg`→`push Not`,
  `*_finset_sum`→`*_finsetSum`, `ContinuousLinearMap.mul_apply`→
  `mul_apply_eq_comp`, `…one_apply`→`one_apply_eq_self`.
