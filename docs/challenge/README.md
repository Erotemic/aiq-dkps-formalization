# AIQ challenge package

Comparator challenge files for the Mathlib-facing results extracted from the AIQ
DKPS formalization. See [`Challenge/README.md`](../../Challenge/README.md) for the
full manifest (the authoritative map).

The challenge files follow the pattern requested by the Mathlib community:

* `Challenge/*/*/Conformance.lean` imports only `Mathlib` and states the leaf
  (top-level) theorem(s) with `sorry`.
* `Challenge/*/*/Leaderboard.lean` imports the AIQ project code and supplies the
  corresponding proofs (and runs `#print axioms`).
* `comparator/*.json` tells `comparator` which challenge module, solution module,
  theorem names, and permitted axioms to check.

Only **leaf** theorems are listed: `#print axioms` on a leaf transitively
certifies its whole proof tree, so supporting lemmas need not be listed.

## Two families

* `Challenge/MathlibCandidate/` — the focused upstream push: drop-ready PRs.
  * `GramRigidity` — Procrustes / Gram-matrix rigidity (`comparator/candidate-01-gram-rigidity.json`)
  * `CourantFischerWeyl` — k-th eigenvalue min–max + Weyl perturbation (`candidate-02`)
  * `DavisKahan` — cross-block / sin-Θ bound (`candidate-03`)
* `Challenge/MathlibPending/` — proven (sorry-free, axiom-clean) but held back
  pending further work before upstreaming: Berge, RankFactorization,
  RankPsdRealization, RestrictCoverMeasurable, SampleMeanMSE, NearIsometry,
  CfcMeasurable, MatrixConcentration, ProbabilityQoL, TendstoInMeasure
  (`comparator/pending-*.json`), plus SpectralFunctionMeasurable as an
  **axiom-audit leaderboard only** (its matrix-valued measurability statement is
  not cleanly Mathlib-only expressible, so it has no comparator conformance).

The four DKPS-family papers (`Acharyya2024`, `Acharyya2025`, `DkpsQuench`,
`Helm2025`) are the repo's end states. They are documented in `Challenge/README.md`
and each library's `README.md`, and were verified axiom-clean, but they are **not**
comparator challenges: their statements are inherently in each paper's own
vocabulary, and the comparator cannot certify those definitions faithfully model
the paper (that is a human reading task).

## Running checks

Install comparator tools once:

```bash
bash scripts/install_comparator_tools.sh
```

Run all challenge families (continues through all configs, prints a summary):

```bash
bash scripts/run_challenge_comparator.sh
```

Run one family:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/candidate-01-gram-rigidity.json
bash scripts/run_challenge_comparator.sh --config comparator/pending-rank-factorization.json
```

If real `landrun` is unavailable while debugging, use `--fake-landrun` (not the
hardened sandboxed check). A real result should use real `landrun`.
