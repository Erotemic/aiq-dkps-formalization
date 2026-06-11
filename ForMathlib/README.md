# ForMathlib — staging library for Mathlib contributions

Paper-agnostic results from `Acharyya2024`/`Acharyya2025`, restated in Mathlib
idiom and generality, staged for upstream PRs.  The ranked candidate list and
per-candidate dossiers live in `planning/mathlib-candidates.md`.

## Pattern

- **One file per proposed Mathlib destination path.**  For example,
  `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean` stages additions to
  `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.
- **Mathlib-only, minimal imports.**  No file here may import the paper
  libraries; the paper libraries import from here (and keep only their
  paper-facing specializations).  This guarantees each staged file is
  self-contained and that the generalized statement actually serves the
  application.
- **Everything lives under the `ForMathlib` namespace** so that a future
  Mathlib bump that upstreams these results cannot create name clashes.
  Within it, declarations use their intended final namespaces (e.g.
  `ForMathlib.Matrix.…`).
- **Maximal generality.**  Statements are over `RCLike 𝕜` (not just `ℝ`)
  where the proofs allow it.

## At PR time

1. Copy the staged declarations into the destination Mathlib file (or a new
   file), dropping the `ForMathlib` namespace wrapper.
2. Convert the header to Mathlib's module system (`module`,
   `public import`, `@[expose] public section`) and minimal-import style.
3. Add the Mathlib copyright header.  Per Mathlib's contribution policy,
   substantial AI assistance must be disclosed in the PR description and a
   human author must understand and vouch for every line.
4. After the PR lands, delete the staged file here and bump the Mathlib pin.

## Inventory

| Staged file | Destination | Candidate (mathlib-candidates.md) |
| --- | --- | --- |
| `Analysis/InnerProductSpace/CourantFischer.lean` | new `Mathlib/Analysis/InnerProductSpace/CourantFischer.lean` | #3a Courant–Fischer (both directions) + Weyl's eigenvalue perturbation inequality, `RCLike` |
| `Analysis/InnerProductSpace/GramMatrix.lean` | `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean` | #1 Procrustes rigidity (equal Grams ⇒ linear isometry equiv), generalized to `RCLike` and stated via `Matrix.gram` |
| `Analysis/InnerProductSpace/NearIsometry.lean` | new `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean` | #6 quantitative polar factor (near-isometry ⇒ isometry within `2δ`), bundled `≃ₗᵢ` + CLM op-norm corollary |
| `Analysis/InnerProductSpace/Spectrum.lean` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` | #3b Davis–Kahan cross-term identity, generalized to `RCLike` |
| `MeasureTheory/Function/ConvergenceInMeasure.lean` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` | #7 `TendstoInMeasure` from a vanishing rate (general filter, `EDist`, measurability-free) |
| `MeasureTheory/Measure/Typeclasses/Probability.lean` | `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` | #2a measurability-free `1 − μ sᶜ ≤ μ s` |
| `Probability/Moments/Variance.lean` | `Mathlib/Probability/Moments/Variance.lean` | #2b uncentered second-moment Chebyshev |
