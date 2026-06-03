# Proofs

Lean4 (+ prose) formalizations, organized one Lean project per major thrust.
Most of these come from TA1 theory-team results (TA2 evaluation work). This is
an exploration scratchpad — files are working drafts (multiple `vN` variants are
kept deliberately for provenance).

## Projects

| Folder            | Thrust                              | Lean lib       | Toolchain    | Prose |
|-------------------|-------------------------------------|----------------|--------------|-------|
| `dkps-quench/`    | ICML Quench companion proof (DKPS)  | `DkpsQuench`   | v4.28.0-rc1  | missing — check main machine |
| `drsb-bridge/`    | DRSB (Schrödinger bridge)           | `DrsbBridge`   | v4.28.0-rc1  | `drsb-bridge/prose/` (PAC-Bayes bound for DRSB) |
| `helm-2025/`      | HELM-2025 statistical inference     | `Helm2025`     | v4.28.0-rc1  | missing — check main machine |
| `oneoff-proofs/`  | Small standalone proofs             | `Oneoff`       | v4.28.0-rc1  | — |
| `tensor-programs/`| Tensor Programs / Master Theorem    | `TensorPrograms` | v4.27.0    | — |

The DKPS/DRSB/HELM/oneoff projects pin the same toolchain
(`leanprover/lean4:v4.28.0-rc1`) and mathlib revision. `tensor-programs/` is an
older, separate project pinned to `v4.27.0`. Each builds independently:

```bash
cd proofs/<project>
lake exe cache get   # fetch prebuilt mathlib
lake build
```

> Note: many source filenames contain `-`/`.` (e.g. `drsb-v3.1.lean`), which are
> not valid Lean module names, so `lake build` will not pick them up as library
> modules. To check an individual draft, open it in the Lean LSP or run
> `lake env lean DkpsQuench/<file>.lean`.
>
> `dkps-quench/.lake/` holds a prebuilt v4.28 mathlib (relocated from the old
> `dkps-proof/` project); the other v4.28 projects can `lake exe cache get`.

## File inventory

### dkps-quench/DkpsQuench/  (ICML Quench / DKPS)
- `quench-query-efficiency.lean` — main theorem from the Quench paper
- `dkps-statement-v4.lean`, `dkps-statement-v5.lean` — statement-level formalizations
- `dkps-v2.lean`, `dkps-v4.lean` — proof drafts (`Basic.lean` is identical to `dkps-v4.lean`)
- `Basic.lean` — copy of `dkps-v4.lean` (former default lib entry point)
- `dkps-aristotle-v2-121013.lean`, `dkps-aristotle-v2-121013-gpt-revision.lean` — Aristotle-generated + GPT revision
- `dkps-gpt-pro-v1.lean`, `dkps-gpt-pro-v2.lean` — GPT-Pro drafts
- `acharyya-2025-skeleton.lean` — `namespace DKPS` core types skeleton
- `negated-2026-02-14-011207.lean` — `namespace QuenchICML`, negated statement experiment
- `checks.lean` — scratch `#check`s for mathlib lemma names

### drsb-bridge/DrsbBridge/  (DRSB / Schrödinger bridge)
- `drsb-v1.lean` … `drsb-v4.lean`, `drsb-v3.1.lean` — proof drafts
- prose: `prose/main.tex` (annotated transcription), `prose/orig-transcription.tex`, `prose/suggested-fixes.tex`

### helm-2025/Helm2025/  (HELM-2025)
- `helm-2025-stat-inference-dkps.lean` — main
- `-version1`, `-version2`, `-bounded-envelope`, `-bounded-labels`, `-option-B` — variants

### oneoff-proofs/Oneoff/  (small standalone proofs)
- `wikifact_consistency_claim.lean` — `namespace WikiFactNoise` consistency claim

### tensor-programs/  (Tensor Programs, Greg-Yang-style Master Theorem)
- Full project with the `TensorPrograms` library (`TP/` modules) pinned to Lean v4.27.0.
- `tensorprogram.lean` — Master Theorem scaffold scratch (`import TP.Empirical`),
  relocated here from the old `dkps-proof/` project where it could not build.
