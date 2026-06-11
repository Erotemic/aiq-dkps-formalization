# Acharyya2025 — DKPS concentration (formalized)

Paper:

- Acharyya, Agterberg, Park, Priebe. *Concentration bounds on response-based vector embeddings of black-box generative models*. arXiv:2511.08307.

This library formalizes the finite-sample/high-probability DKPS concentration
result used as a load-bearing hypothesis by the downstream DkpsQuench and
Helm2025 formalizations.

## Status

COMPLETE (2026-06-11): **zero sorries, zero axioms** — every statement in the
library is proved and true as written. The full chain is formally connected:

> iid responses → second moments (trace(Σ)/r) → Chebyshev + union bound →
> dissimilarity entrywise events → CMDS double-centering → Weyl /
> Davis–Kahan / polar-factor perturbation → aligned embedding error
> (`alignedSpectralConfig`, explicit `configBound`) → Quench's uniform
> embedding-error hypothesis and Helm's alignment consistency,

with the explicit end-to-end rate composed in `RateChain.lean`
(`endToEndRate`, vanishing as replicates grow; module docstring compares with
the paper's Poly₃((n³/r)^{1/2−δ}) bookkeeping).

The four legacy scaffold statements that were false as written (vacuous
Prop-field structures, unaligned `ConfigError`, placeholder rates) have been
RETIRED: each is now a prose "Retired seam" record pointing at its proved
replacement; the original statements live in git history. See
`../planning/acharyya-plan.md` for the work-package history.

Model/provenance note: the original scaffold session's model label is recorded
as `Codex 5.5 High`; the spectral bridge, aligned pipeline, rate chain, and
the retirement pass were formalized by Claude Fable 5 (claude-fable-5[1m]),
per user-observed model labels.

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
- `MatrixPerturbation.lean` — matrix-world capstone:
  `exists_isometry_configError_le_of_entrywise_close` (entrywise η ⇒ aligned
  ConfigError ≤ configBound, rank-transport for trailing eigenvalues).
- `AlignedPipeline.lean` — `alignedSpectralConfig` (choice-based aligned
  estimator) + the HP aligned-ConfigError theorems, including the end-to-end
  response-mean version.
- `RateChain.lean` — explicit end-to-end rate: Chebyshev/union-bound HP
  lemma, `configBound` continuity at 0, `endToEndRate`, and its vanishing.

Supporting layers (all proved; retired seams kept as prose records):

- `Deterministic.lean` — finite-dimensional centering definitions and
  double-centering stability.
- `MathlibBridge.lean` — paper-independent conversions from curried `DisMat`
  objects to Mathlib `Matrix`, plus symmetry/Frobenius/operator-bound predicates.
- `SpectralPipeline.lean` — world-map between DKPS/CMDS, matrix, spectral, and
  configuration layers; hardened `CMDSpectralAssumptions`; population CMDS
  Gram realization (proved).
- `Bridge.lean` — deterministic/high-probability event propagation chain
  (response mean → Frobenius → entrywise → CMDS entrywise).
- `Concentration.lean` — historical record of the retired scaffold layer.
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
