# Acharyya2024 — DKPS consistency (formalized)

Paper:

- Acharyya, Trosset, Priebe, Helm. *Consistent estimation of generative model representations in the data kernel perspective space*. arXiv:2409.17308.

This library formalizes the asymptotic DKPS/raw-stress MDS consistency
results. It is intentionally separate from `Acharyya2025`, which tracks the
later finite-sample concentration paper.

## Status

COMPLETE (2026-06-11): **zero sorries, zero axioms** — every statement in the
library is proved, and statements that were false as written in the original
scaffold have been repaired with the honest hypotheses (`hsample`/`hlimit`/
`huniq`) before being proved. Key results:

- Theorem 2 probability step: `Probability.lean` (Chebyshev + union bound)
  fed by `SecondMoment.lean` (iid variance algebra E‖X̄−μ‖² = trace(Σ)/r).
- Trosset–Priebe raw-stress stability: deterministic core + a
  modulus-of-continuity upgrade in `RawStress.lean`. The probabilistic
  statement is proved **without measurable selection** — a modulus of
  continuity at the limit matrix plus outer-measure event inclusion replaces
  the selection argument the paper leaves implicit. The unconditional truth
  is the set version (`mds_stability_inProbability_set`); the paper's fixed-ψ
  Theorem-1 shape holds under the explicit `UniquePairProfile` hypothesis and
  then along the FULL sequence (no subsequence needed).
- Triangular-array regimes (Theorems 4/5): proved per stage in
  `Consistency.lean`; the paper's diagonal argument is unnecessary since the
  repaired layer-1 stability converges along the full sequence.

See `../planning/acharyya-plan.md` for the work-package history and
`../planning/acharyya-graveyard.md` for dead ends.

Model/provenance note: the original scaffold session's model label is recorded
as `Codex 5.5 High`; the proofs (`Probability.lean`, `SecondMoment.lean`,
`RawStress.lean`, the repaired `Consistency.lean`) were formalized by Claude
Fable 5 (claude-fable-5[1m]), per user-observed model labels.

## Files

- `Probability.lean` — PROVED: the Theorem 2 probability step (Chebyshev,
  union bound, squeeze) from second-moment hypotheses.
- `SecondMoment.lean` — PROVED: iid sample-mean second-moment algebra
  (pairwise independence suffices; ≤ γ/r corollary).
- `RawStress.lean` — PROVED: raw-stress MDS toolkit — √-stress Lipschitz
  continuity, translation invariance, minimizer existence, deterministic
  subsequence stability, modulus of continuity, and the in-probability
  stability theorems (set version + fixed-ψ version under
  `UniquePairProfile`).
- `Common.lean` — shared finite-dimensional DKPS/MDS definitions.
- `WellKnown.lean` — paper-independent finite-dimensional norm inequalities
  and high-probability/complement convergence bookkeeping.
- `Consistency.lean` — PROVED: paper-facing consistency theorems
  (Theorems 1–5 shapes, repaired hypotheses).
- `Basic.lean` — library entry point.
- `prose/consistent-estimation-dkps-2409.17308_transcription.md` — markdown transcription.

## Suggested checks

```bash
lake build Acharyya2024
grep -RIn '\baxiom\b' Acharyya2024
grep -RIn '\bsorry\b' Acharyya2024
```
