# AIQ DKPS ForMathlib challenge package

This directory documents the root-level challenge files added for community
review of reusable Mathlib-facing claims from the AIQ DKPS formalization.

Validated against source archive:

- archive: `aiq-dkps-formalization-source-2026-06-12T140903-5-b3b2569cd4ff.tar.gz`
- git commit: `b3b2569cd4ffaab896d7ee183c673170a09773d8`
- short commit: `b3b2569`
- commit date: `2026-06-12 19:04:40 +0000`
- commit subject: `B2b: Berge value-function continuity + finite-family closeness modulus`

## Challenge files

There are two challenge layers.

### Headline sampler

- `ChallengeConformance.lean` imports only `Mathlib` and states four selected
  high-value claims with `sorry`.
- `ChallengeLeaderboard.lean` imports the staged `ForMathlib` declarations and
  fills those claims.
- `comparator/aiq-mathlib-candidates.json` checks the four selected claims.

The headline sampler is meant for quick calibration. It covers:

1. Procrustes rigidity from equality of pairwise inner products.
2. Procrustes rigidity in `Matrix.gram` form.
3. Rank-controlled PSD Gram realization.
4. Weyl eigenvalue perturbation for symmetric operators.

### Full inventory

- `ChallengeInventoryConformance.lean` imports only `Mathlib` and mirrors the
  public theorem surface of the current `ForMathlib` staging library, with each
  theorem body replaced by `sorry`.
- `ChallengeInventoryLeaderboard.lean` imports the project `ForMathlib` modules.
- `comparator/aiq-mathlib-inventory.json` checks the full inventory of staged
  declarations.

The inventory challenge is not a proposed single Mathlib PR. It is a mechanical
claim inventory: it records which reusable staged declarations the current
project can certify under comparator.

## Suggested local commands

From the repository root:

```bash
lake env lean ChallengeConformance.lean
lake env lean ChallengeLeaderboard.lean
lake env lean ChallengeInventoryConformance.lean
lake env lean ChallengeInventoryLeaderboard.lean
```

If comparator and its sandbox/export dependencies are available, run all checks:

```bash
bash scripts/run_challenge_comparator.sh
```

Run only the headline sampler:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/aiq-mathlib-candidates.json
```

Run only the full inventory:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/aiq-mathlib-inventory.json
```
