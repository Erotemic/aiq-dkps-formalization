# Acharyya2025 — DKPS concentration scaffold

Paper:

- Acharyya, Agterberg, Park, Priebe. *Concentration bounds on response-based vector embeddings of black-box generative models*. arXiv:2511.08307.

This library is the paper-specific scaffold for the finite-sample/high-probability
DKPS concentration result used as a load-bearing hypothesis by the downstream
DkpsQuench and Helm2025 formalizations.

## Status

The hard spectral bridge is COMPLETE (2026-06-11): every analytic step of the
paper's Theorem 2 chain — Weyl, Davis–Kahan, Procrustes alignment, and the
final configuration perturbation — is formally proved with explicit constants
and zero sorries in the new files listed below. The remaining `sorry`s live
only in the LEGACY scaffold statements (Concentration.lean, Bridge.lean,
SpectralPipeline.lean), several of which are marked `TODO(false-statement)`;
they are pending the WP6 repair pass that re-derives them from the proved
bridge. See `../planning/acharyya-plan.md`.

Model/provenance note: the original scaffold session's model label is recorded
as `Codex 5.5 High`; the spectral bridge (Weyl, DavisKahan, RankGap, Overlap,
PolarFactor, ConfigPerturbation, GramRealization, Procrustes, OperatorBridge)
was formalized by Claude Fable 5 (claude-fable-5[1m]), per user-observed model
labels.

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

New proved bridge (zero sorries, 2026-06-11):

- `Weyl.lean` — discrete Courant–Fischer + Weyl's eigenvalue perturbation
  inequality (Mathlib-contribution candidate).
- `DavisKahan.lean` — cross-term identity + Davis–Kahan cross-block sin-Θ
  bound (Mathlib-contribution candidate).
- `RankGap.lean` — gap derivation from rank-d/floor structure via Weyl;
  composed cross-overlap bound 4nε²/α².
- `Overlap.lean` — eigenvector overlap matrix, QᵀQ−I deviation, Sylvester
  commutator identity.
- `PolarFactor.lean` — quantitative polar factor: near-isometry ⇒ exact
  isometry within 2δ (no SVD/CFC).
- `ConfigPerturbation.lean` — THE BRIDGE THEOREM:
  `exists_isometry_configError_spectralConfig_le` — spectral embeddings of
  ε-close operators agree up to isometry within explicit `configBound`.
- `GramRealization.lean` — PSD rank-≤d matrices are Gram matrices of
  d-dimensional configurations (spectral construction).
- `Procrustes.lean` — exact Gram rigidity: equal Grams ⇒ isometry-related.
- `OperatorBridge.lean` — honest ℓ²→ℓ² operator-norm transport
  matrix ↔ operator world.

Legacy scaffold (contains the remaining sorries; WP6 repair pending):

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
