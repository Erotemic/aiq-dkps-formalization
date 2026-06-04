# Acharyya2024 — DKPS consistency scaffold

Paper:

- Acharyya, Trosset, Priebe, Helm. *Consistent estimation of generative model representations in the data kernel perspective space*. arXiv:2409.17308.

This library is the paper-specific scaffold for the asymptotic DKPS/raw-stress
MDS consistency results. It is intentionally separate from `Acharyya2025`, which
tracks the later finite-sample concentration paper.

## Status

This is a scaffold, not a completed formalization.

- There are no declaration-level assumptions in the new scaffold files.
- Load-bearing unfinished proofs are marked with `sorry`.
- The main open obligations are the raw-stress MDS stability theorem and the
  probability step showing dissimilarity matrices converge in probability.

## Files

- `Common.lean` — shared finite-dimensional DKPS/MDS definitions.
- `Consistency.lean` — paper-facing consistency theorem statements.
- `Basic.lean` — library entry point.
- `prose/consistent-estimation-dkps-2409.17308_transcription.md` — markdown transcription.

## Suggested checks

```bash
lake build Acharyya2024
grep -RIn '\baxiom\b' Acharyya2024
grep -RIn '\bsorry\b' Acharyya2024
```
