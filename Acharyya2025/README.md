# Acharyya2025 — DKPS concentration scaffold

Paper:

- Acharyya, Agterberg, Park, Priebe. *Concentration bounds on response-based vector embeddings of black-box generative models*. arXiv:2511.08307.

This library is the paper-specific scaffold for the finite-sample/high-probability
DKPS concentration result used as a load-bearing hypothesis by the downstream
DkpsQuench and Helm2025 formalizations.

## Status

This is a scaffold, not a completed formalization.

- There are no declaration-level assumptions in the new scaffold files.
- Load-bearing unfinished proofs are marked with `sorry`.
- The main open obligations are response/dissimilarity matrix concentration,
  MDS perturbation stability, and the downstream-compatible uniform embedding
  error shape.

## Files

- `Concentration.lean` — paper-facing concentration theorem statements.
- `Basic.lean` — library entry point.
- `prose/concentration-bounds-response-embeddings-2511.08307_transcription.md` — markdown transcription.

## Suggested checks

```bash
lake build Acharyya2025
grep -RIn '\baxiom\b' Acharyya2025
grep -RIn '\bsorry\b' Acharyya2025
```
