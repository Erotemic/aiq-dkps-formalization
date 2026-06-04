# Acharyya2025 — DKPS concentration scaffold

Paper:

- Acharyya, Agterberg, Park, Priebe. *Concentration bounds on response-based vector embeddings of black-box generative models*. arXiv:2511.08307.

This library is the paper-specific scaffold for the finite-sample/high-probability
DKPS concentration result used as a load-bearing hypothesis by the downstream
DkpsQuench and Helm2025 formalizations.

## Status

This is a scaffold, not a completed formalization.

Model/provenance note: this session's model label is recorded as
`Codex 5.5 High`, per the user-observed UI label.

- There are no declaration-level assumptions in the new scaffold files.
- Load-bearing unfinished proofs are marked with `sorry`.
- The main open obligations are response/dissimilarity matrix concentration and
  the cited CMDS spectral perturbation theorem.
- Deterministic plumbing now includes response-mean-to-distance propagation,
  componentwise error extraction, and double-centering stability.
- The downstream-compatible uniform embedding error shape is proved from the
  scaffold concentration theorem plus componentwise error extraction.
- Downstream adapters now expose the deterministic reductions into
  `DkpsQuench` and `Helm2025` without hiding the remaining analytic bridges.
- The MDS/spectral proof is now laid out as a pipeline:
  DKPS curried matrices → Mathlib matrices → operator-norm perturbation →
  spectral theorem / Davis-Kahan → Procrustes-aligned configurations.

## Files

- `Deterministic.lean` — proved finite-dimensional centering definitions and
  double-centering stability.
- `MathlibBridge.lean` — paper-independent conversions from curried `DisMat`
  objects to Mathlib `Matrix`, plus symmetry/Frobenius/operator-bound predicates.
- `SpectralPipeline.lean` — the staged CMDS proof pipeline with separate cited
  seams for norm comparison, population Gram realization, and
  Davis-Kahan/Weyl/Procrustes perturbation.
- `Bridge.lean` — proved deterministic/high-probability event propagation and
  the cited CMDS perturbation seam.
- `Concentration.lean` — paper-facing concentration theorem statements.
- `../DkpsQuench/AcharyyaBridge.lean` — finite-configuration concentration to
  Quench's model-space uniform concentration, under an explicit finite
  factorization hypothesis.
- `../Helm2025/AcharyyaBridge.lean` — finite-configuration concentration to
  Helm's finite sample alignment-error event and, with explicit measurability
  and rate-convergence hypotheses, `DKPSAlignmentConsistency`.
- `Basic.lean` — library entry point.
- `prose/concentration-bounds-response-embeddings-2511.08307_transcription.md` — markdown transcription.

## Suggested checks

```bash
lake build Acharyya2025
grep -RIn '\baxiom\b' Acharyya2025
grep -RIn '\bsorry\b' Acharyya2025
```
