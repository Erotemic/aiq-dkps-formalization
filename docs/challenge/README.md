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
* `Challenge/Inventory` — broader experimental inventory of the current
  `ForMathlib` theorem surface. This inventory is not a proposed single PR;
  it is a mechanical audit of what the project can currently certify.

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
bash scripts/run_challenge_comparator.sh --config comparator/aiq-inventory.json
```

If real `landrun` is unavailable while debugging, use:

```bash
bash scripts/run_challenge_comparator.sh --fake-landrun
```

A real result should use real `landrun`, not fake-landrun.
