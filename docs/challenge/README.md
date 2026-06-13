# AIQ challenge package

This directory contains comparator challenge files for Mathlib-facing results
extracted from the AIQ DKPS formalization.

The challenge files follow the pattern requested by the Mathlib community:

* `Challenge/*/Conformance.lean` imports only `Mathlib` and states claims with
  `sorry`.
* `Challenge/*/Leaderboard.lean` imports the AIQ project code and supplies the
  corresponding declarations/proofs.
* `comparator/*.json` tells `comparator` which challenge module, solution
  module, theorem names, and permitted axioms to check.

## Challenge families

* `Challenge/Gram` — Procrustes / Gram-matrix rigidity.
* `Challenge/PsdGram` — rank-controlled PSD Gram realization.
* `Challenge/Spectral` — a compact spectral-perturbation stack: cross-term
  identity, Courant--Fischer/Weyl, and Davis--Kahan cross-block estimates.
* `Challenge/Inventory/*` — broader experimental inventory split into
  PR-oriented theorem families. These inventory groups are calibration/audit
  artifacts, not a proposal to upstream each group exactly as-is.

The PR-oriented inventory groups are:

* `Challenge/Inventory/Probability` — probability-measure, moment, sample-mean,
  convergence-in-measure, and concentration helper lemmas.
* `Challenge/Inventory/OperatorSpectral` — inner-product-space spectral
  identities, Courant--Fischer/Weyl, and Davis--Kahan/projector infrastructure.
* `Challenge/Inventory/GramGeometry` — Gram rigidity plus quantitative
  near-isometry / polar-factor style lemmas.
* `Challenge/Inventory/RankPsd` — matrix rank factorization and PSD Gram
  realization infrastructure.
* `Challenge/Inventory/MatrixSpectral` — entrywise operator/eigenvalue bounds
  and spectral-function polynomial approximation infrastructure.
* `Challenge/Inventory/Measurability` — CFC measurability and compact
  existential measurability helpers.
* `Challenge/Inventory/Berge` — approximate minimizer compactness and
  Berge-style continuity fragments.

The legacy monolithic `Challenge/Inventory` files and
`comparator/aiq-inventory.json` are kept as an aggregate audit target, but the
runner's default path uses the split inventory configs so failures localize to a
PR-sized theorem family.

The inventory intentionally excludes a few newest/provisional declarations for
now:

* `ForMathlib.Matrix.measurable_specTransform` comes from the newest
  spectral-transform / CFC measurability work and still needs statement/API
  review before it should be claimed as ready.
* `ForMathlib.isHermitian_sampleCovariance` and
  `ForMathlib.measure_forall_sampleCovariance_sortedEig_ge_ge` come from the
  newest sample-covariance concentration work. The current conformance wrapper
  is not yet comparator-exact for the Hermitian witness used by the sorted
  eigenvalue theorem, so these are excluded until they are reviewed and
  regenerated.

## Running checks

Install comparator tools once:

```bash
bash scripts/install_comparator_tools.sh
```

Run all challenge families. The script continues through all requested configs
and prints a pass/fail summary table at the end:

```bash
bash scripts/run_challenge_comparator.sh
```

Run one family:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/aiq-gram-rigidity.json
bash scripts/run_challenge_comparator.sh --config comparator/aiq-psd-gram-realization.json
bash scripts/run_challenge_comparator.sh --config comparator/aiq-spectral-perturbation.json
bash scripts/run_challenge_comparator.sh --config comparator/aiq-inventory-rank-psd.json
bash scripts/run_challenge_comparator.sh --config comparator/aiq-inventory.json  # legacy full inventory
```

If real `landrun` is unavailable while debugging, use:

```bash
bash scripts/run_challenge_comparator.sh --fake-landrun
```

A real result should use real `landrun`, not fake-landrun.
