# AIQ DKPS Formalization

This repository contains Lean 4 formalizations for four DKPS-related theorem
developments:

- `Acharyya2024` — asymptotic DKPS / raw-stress MDS consistency.
- `Acharyya2025` — finite-sample DKPS concentration and aligned spectral
  perturbation bounds.
- `DkpsQuench` — a conditional query-efficiency theorem for DKPS-based model
  selection, with an Acharyya2025 bridge.
- `Helm2025` — a conditional statistical-inference transfer theorem, with an
  Acharyya2025 bridge.

The repository is a filtered standalone extraction from a larger research
workspace. The active Lean libraries are at the repository root; historical
commit history for the retained files has been preserved where possible.

## Quick start

Install or verify Lean/Lake:

```bash
./setup_lean.sh
```

Fetch Mathlib cache and build the active libraries:

```bash
lake exe cache get
lake build Acharyya2024 Acharyya2025 DkpsQuench Helm2025
```

The project is pinned by `lean-toolchain` and `lake-manifest.json`. At the time
of this extraction, the toolchain is:

```text
leanprover/lean4:v4.28.0-rc1
```

## Repository layout

```text
.
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── setup_lean.sh
├── Acharyya2024.lean
├── Acharyya2024/
├── Acharyya2025.lean
├── Acharyya2025/
├── DkpsQuench.lean
├── DkpsQuench/
├── Helm2025.lean
├── Helm2025/
├── AcharyyaMDS/
└── planning/
```

`AcharyyaMDS/` is retained as an older compatibility layer for prior Acharyya
DKPS/MDS imports and notes. It is useful context, but the publication-facing
build targets are the four libraries listed above.

Some directories may contain archived drafts under `old-attempt/`. Those files
are retained for provenance only and are not imported by the active library
entry points.

## Project status

### `Acharyya2024`

Formalizes the DKPS consistency layer associated with:

> Acharyya, Trosset, Priebe, Helm. *Consistent estimation of generative model
> representations in the data kernel perspective space*. arXiv:2409.17308.

The active library proves the repaired asymptotic/raw-stress MDS consistency
statements with explicit hypotheses. The current paper-facing entry point is
`Acharyya2024.lean`, which imports `Acharyya2024.Basic`.

Important modules include:

- `Acharyya2024/Common.lean` — finite-dimensional DKPS/MDS definitions.
- `Acharyya2024/Probability.lean` — Chebyshev and union-bound probability step.
- `Acharyya2024/SecondMoment.lean` — iid sample-mean second-moment algebra.
- `Acharyya2024/RawStress.lean` — raw-stress stability toolkit.
- `Acharyya2024/Consistency.lean` — paper-facing consistency theorem shapes.

### `Acharyya2025`

Formalizes the finite-sample DKPS concentration and aligned spectral pipeline
associated with:

> Acharyya, Agterberg, Park, Priebe. *Concentration bounds on response-based
> vector embeddings of black-box generative models*. arXiv:2511.08307.

This is the main linear-algebra and spectral-perturbation layer used by the
bridges into `DkpsQuench` and `Helm2025`. The current entry point is
`Acharyya2025.lean`, which imports `Acharyya2025.Basic`.

Important modules include:

- `Acharyya2025/Bridge.lean` — deterministic and high-probability event
  propagation from response means to CMDS inputs.
- `Acharyya2025/Weyl.lean` and `Acharyya2025/DavisKahan.lean` — spectral
  perturbation lemmas.
- `Acharyya2025/ConfigPerturbation.lean` — aligned configuration perturbation.
- `Acharyya2025/AlignedPipeline.lean` — choice-based aligned spectral estimator
  and high-probability aligned error theorem.
- `Acharyya2025/RateChain.lean` — explicit end-to-end rate composition.

### `DkpsQuench`

Contains the DKPS query-efficiency formalization and its bridge to the
Acharyya2025 concentration layer. The current entry point is `DkpsQuench.lean`,
which imports:

- `DkpsQuench.Basic`
- `DkpsQuench.AcharyyaBridge`

The theorem layer is intentionally conditional: assumptions such as Lipschitz
score behavior, support/cover conditions, finite factorization, and uniform
embedding concentration are made explicit rather than hidden.

### `Helm2025`

Contains the statistical-inference transfer formalization and its bridge to the
Acharyya2025 concentration layer. The current entry point is `Helm2025.lean`,
which imports:

- `Helm2025.Basic`
- `Helm2025.AcharyyaBridge`

The theorem layer states sufficient analytic conditions explicitly, including
boundedness, continuity, measurability, and alignment-consistency hypotheses.

## Suggested verification checks

Build the active libraries:

```bash
lake build Acharyya2024 Acharyya2025 DkpsQuench Helm2025
```

Check for active proof placeholders in the four publication-facing libraries:

```bash
grep -RInE '\b(sorry|admit|axiom)\b|sorryAx' \
  Acharyya2024 Acharyya2025 DkpsQuench Helm2025 \
  --include='*.lean' \
  --exclude-dir='old-attempt'
```

After history-surgery passes, rerun your local filename/content audits for any excluded topics and confirm that the only remaining files are the four active libraries, retained Acharyya compatibility material, build metadata, setup scripts, and documentation you intentionally kept.

## Notes for maintainers

- Prefer building named targets rather than relying on historical default-target
  configuration during transition periods.
- Keep archival drafts out of the active import graph.
- When changing history, make a backup copy first and audit both filenames and
  blob contents across reachable commits.
