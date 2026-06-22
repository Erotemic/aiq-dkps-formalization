# Claim-to-file map for formalization_draft1

This file is a working index for editing the paper.  It records where the main
claims in `paper.tex` are supported by repository files.  It is not a substitute
for line-accurate citations in a final submission.

## Validation anchor

- Validated repository commit: `c8cf511fc4c7b7911294279b99fd76b514cbf64c`.
- Short commit: `c8cf511`.
- Commit date: `2026-06-12 10:49:10 -0400`.
- Source archive inspected: `aiq-dkps-formalization-source-2026-06-12T095220-5-c8cf511fc4c7.tar.gz`.
- Lean toolchain: `leanprover/lean4:v4.31.0-rc2` from `lean-toolchain`.
- Lake workspace: `lakefile.toml`, `lake-manifest.json`.
- User-observed build at this state: `lake build` completed successfully with
  8626 jobs.
- Lean file count / LOC in inspected archive: 51 Lean files, 12888 Lean LOC.

## Main framing claims

- DKPS is treated as the motivating application and integration test:
  `README.md`, `Acharyya2024/README.md`, `Acharyya2025/README.md`,
  `DkpsQuench/README.md`, `Helm2025/README.md`.
- The formalization contribution is concentrated in reusable bridges and
  infrastructure: `Acharyya2025/ConfigPerturbation.lean`,
  `Acharyya2024/RawStress.lean`, `Acharyya2025/AlignedPipeline.lean`,
  `Acharyya2025/RateChain.lean`, and `ForMathlib/README.md`.

## Artifact structure

- `Acharyya2024/README.md`: asymptotic/raw-stress MDS consistency, theorem
  crosswalk, explicit assumptions beyond the prose statements.
- `Acharyya2025/README.md`: finite-sample concentration, deterministic spectral
  perturbation bridge, theorem crosswalk, downstream consumers.
- `DkpsQuench/README.md`: query-efficiency theorem layer and Acharyya bridge.
- `Helm2025/README.md`: statistical-inference transfer and honest bridge seam.
- `ForMathlib/README.md`: staged reusable lemmas and intended Mathlib targets.

## Statement repair / hidden assumptions

- `Acharyya2024/RawStress.lean`: `UniquePairProfile`, MDS stability,
  minimizer-set and in-probability stability statements.
- `Acharyya2024/Consistency.lean`: repaired paper-facing consistency theorems.
- `Acharyya2025/SpectralPipeline.lean`: `CMDSpectralAssumptions` and population
  realization bridge.
- `DkpsQuench/Theorem2.lean`: sub-event variants for measurable concentration
  events.
- `Helm2025/AcharyyaBridge.lean`: documented `HONEST SEAM` for the per-sample
  population alignment bridge.
- `planning/acharyya-graveyard.md`: records false-as-written or retired theorem
  shapes and replacements.

## Deterministic CMDS perturbation bridge

- `Acharyya2025/ConfigPerturbation.lean`: `exists_isometry_configError_spectralConfig_le`.
- `Acharyya2025/MatrixPerturbation.lean`: matrix-world capstone and Gram facts.
- `Acharyya2025/Weyl.lean`: Weyl perturbation results.
- `Acharyya2025/DavisKahan.lean`: Davis-Kahan-style cross-block bounds.
- `Acharyya2025/RankGap.lean`: rank/floor eigengap derivation.
- `Acharyya2025/Overlap.lean`: eigenvector overlap and commutator control.
- `Acharyya2025/PolarFactor.lean`: quantitative polar-factor argument.
- `Acharyya2025/GramRigidity.lean`: Gram rigidity and isometric alignment.
- `Acharyya2025/GramRealization.lean`: PSD rank-constrained Gram realization.
- `Acharyya2025/OperatorBridge.lean`: entrywise-to-operator transport.

## Raw-stress MDS and minimizers

- `Acharyya2024/RawStress.lean`: raw stress, minimizer existence, translation
  invariance, compactness/coercivity, minimizer-set stability, modulus of
  continuity, in-probability stability.
- `ForMathlib/Topology/ApproxMinimizer.lean`: staged approximate-minimizer
  stability theorem used by the raw-stress layer.

## Probability and rate pipeline

- `Acharyya2024/SecondMoment.lean`: sample-mean second-moment identities.
- `Acharyya2024/Probability.lean`: Chebyshev/union-bound concentration.
- `Acharyya2025/Bridge.lean`: response means to centered CMDS closeness.
- `Acharyya2025/AlignedPipeline.lean`: high-probability aligned configuration
  error from entrywise closeness and response means.
- `Acharyya2025/RateChain.lean`: end-to-end rates and vanishing-rate results.

## Measurability and selection

- `Acharyya2025/AlignedPipeline.lean`: choice-free `AlignExists`, equivalence
  with aligned estimator error, compact-existential measurability.
- `ForMathlib/MeasureTheory/CompactExists.lean`: `measurableSet_exists_mem_le`.
- `planning/historical/for-fable.md`: notes on the discharged measurable-selection seam
  and the remaining `hmeas_spec` primitive.

## Downstream integration

- `DkpsQuench/AcharyyaBridge.lean`: bridges aligned spectral concentration to
  query-efficiency theorems, including response-mean and second-moment variants.
- `DkpsQuench/Theorem2.lean`: paper-facing query-efficiency theorem statements.
- `Helm2025/AcharyyaBridge.lean`: bridges aligned spectral concentration to the
  Helm alignment-consistency interface subject to `halign`.
- `Helm2025/Inference.lean`: paper-facing inference-transfer statements.

## Reusable Mathlib-style infrastructure

- `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean`.
- `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean`.
- `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean`.
- `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`.
- `ForMathlib/Analysis/Matrix/EntrywiseOpNorm.lean`.
- `ForMathlib/Analysis/Matrix/Spectrum.lean`.
- `ForMathlib/LinearAlgebra/Matrix/PosDef.lean`.
- `ForMathlib/MeasureTheory/CompactExists.lean`.
- `ForMathlib/Probability/Moments/SampleMean.lean`.
- `ForMathlib/Topology/ApproxMinimizer.lean`.

## Model-assisted provenance evidence

Use `model_provenance.md` for a longer record.  Summary:

- Aristotle evidence: `Helm2025/Basic.lean`, `Helm2025/Internal.lean`, and
  `DkpsQuench/Basic.lean` include explicit scaffold comments naming Harmonic's
  Aristotle.
- GPT/Codex evidence: many comments in `Acharyya2024/Common.lean`,
  `Acharyya2024/WellKnown.lean`, `Acharyya2025/Bridge.lean`,
  `Acharyya2025/Deterministic.lean`, `Acharyya2025/MathlibBridge.lean`,
  and `Helm2025/AcharyyaBridge.lean` record `Codex 5.5 High, per
  user-observed model label`.
- Fable evidence: comments in most hard Acharyya bridge files record
  `Claude Fable 5`; `Acharyya2024/README.md` and `Acharyya2025/README.md`
  attribute the proof and bridge completion to Fable; git commits by the
  `agent <erotemic@gmail.com>` author on 2026-06-11 record completion of the
  spectral bridge, raw-stress stability core, rate chain, and retirement of
  false-as-written seams.
- Opus evidence: `ForMathlib/*` staged files such as
  `ForMathlib/Topology/ApproxMinimizer.lean`,
  `ForMathlib/Analysis/Matrix/EntrywiseOpNorm.lean`,
  `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean`,
  `ForMathlib/Probability/Moments/SampleMean.lean`, and
  `ForMathlib/Analysis/Matrix/Spectrum.lean` record `Claude Opus 4.8`; git
  commits on 2026-06-11/12 record staging, rewiring, RCLike generalization, and
  deeper Quench bridges.
- GPT 5.2 evidence: not recovered from commit metadata in this archive.  The
  author has supplied this provenance, and notes that GPT commits were typically
  not marked as GPT-authored.  Before final submission, verify the GPT 5.2
  attribution against inline comments and external session logs.
