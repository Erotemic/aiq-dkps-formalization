# AIQ DKPS ForMathlib challenge package

This directory documents the root-level challenge files added for community
review of a first small subset of reusable Mathlib-facing claims from the AIQ
DKPS formalization.

Validated against source archive:

- archive: `aiq-dkps-formalization-source-2026-06-12T140903-5-b3b2569cd4ff.tar.gz`
- git commit: `b3b2569cd4ffaab896d7ee183c673170a09773d8`
- short commit: `b3b2569`
- commit date: `2026-06-12 19:04:40 +0000`
- commit subject: `B2b: Berge value-function continuity + finite-family closeness modulus`

## Files

- `ChallengeConformance.lean` imports only `Mathlib` and states the challenge
  claims with `sorry`.
- `ChallengeLeaderboard.lean` imports the staged `ForMathlib` declarations and
  fills those claims.
- `comparator/aiq-mathlib-candidates.json` is a comparator configuration for
  the four initial challenge theorems.
- `formalization.yaml` records project metadata and AI-use provenance.

## Initial challenge claims

The first challenge intentionally covers only four theorem wrappers from three
high-value Mathlib candidate areas:

1. Procrustes rigidity from equality of pairwise inner products.
2. Procrustes rigidity in `Matrix.gram` form.
3. Rank-controlled PSD Gram realization.
4. Weyl eigenvalue perturbation for symmetric operators.

This is not intended to exhaust the `ForMathlib` staging library. It is a
small starting point for calibrating significance, statement shape, and the
appropriate review path for AI-authored Lean code.

## Suggested local commands

From the repository root:

```bash
lake env lean ChallengeConformance.lean
lake env lean ChallengeLeaderboard.lean
```

If comparator and its sandbox/export dependencies are available, run it with:

```bash
lake env comparator comparator/aiq-mathlib-candidates.json
```

Depending on local installation, the comparator binary may need to be invoked by
absolute path or through the `systemd-run` wrapper recommended by comparator's
README.
