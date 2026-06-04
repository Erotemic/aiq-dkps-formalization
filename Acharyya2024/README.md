# Acharyya2024 — DKPS consistency scaffold

Paper:

- Acharyya, Trosset, Priebe, Helm. *Consistent estimation of generative model representations in the data kernel perspective space*. arXiv:2409.17308.

This library is the paper-specific scaffold for the asymptotic DKPS/raw-stress
MDS consistency results. It is intentionally separate from `Acharyya2025`, which
tracks the later finite-sample concentration paper.

## Status

This is a scaffold, not a completed formalization.

Model/provenance note: this session's model label is recorded as
`Codex 5.5 High`, per the user-observed UI label.

- There are no declaration-level assumptions in the new scaffold files.
- Load-bearing unfinished proofs are marked with `sorry`.
- The main open obligations are the raw-stress MDS stability theorem and the
  probability step showing dissimilarity matrices converge in probability.
- Deterministic response-distance plumbing is proved in `Common.lean`, while
  paper-agnostic finite norm/probability lemmas live in `WellKnown.lean`.
- `Common.lean` now includes a generic wrapper from high-probability metric
  error bounds with deterministic rate tending to zero to
  `ConvergesInProbability`.

## Files

- `Common.lean` — shared finite-dimensional DKPS/MDS definitions.
- `WellKnown.lean` — paper-independent finite-dimensional norm inequalities
  and high-probability/complement convergence bookkeeping.
- `Consistency.lean` — paper-facing consistency theorem statements.
- `Basic.lean` — library entry point.
- `prose/consistent-estimation-dkps-2409.17308_transcription.md` — markdown transcription.

## Suggested checks

```bash
lake build Acharyya2024
grep -RIn '\baxiom\b' Acharyya2024
grep -RIn '\bsorry\b' Acharyya2024
```
