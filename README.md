# Proofs

Lean4 (+ prose) formalizations, organized as **one Lake workspace with a
separate library per thrust**. Most of these come from TA1 theory-team results
(TA2 evaluation work). This is an exploration scratchpad — files are working
drafts (multiple `vN` variants are kept deliberately for provenance).

## Layout

```
proofs/
├── lakefile.toml      # umbrella workspace: one lean_lib per thrust, shared Mathlib
├── lean-toolchain     # v4.28.0-rc1 (shared by all libs below)
├── lake-manifest.json
├── .lake/             # single shared Mathlib build — no per-project duplication
├── DkpsQuench/        # lean_lib: ICML Quench companion proof (DKPS)
├── DrsbBridge/        # lean_lib: DRSB (Schrödinger bridge)  + prose/
├── Helm2025/          # lean_lib: HELM-2025 statistical inference
├── Oneoff/            # lean_lib: small standalone proofs
└── tensor-programs/   # SEPARATE project (pins Lean v4.27.0) — not in the workspace
```

The four v4.28 thrusts live in a single Lake workspace so they share one Mathlib
checkout/build instead of compiling it four times. Each library is self-contained
in its own root directory, so any one can be **lifted into a standalone project
later** by moving its directory out and giving it its own `lakefile.toml` +
`lean-toolchain` + `lake-manifest.json` (copy them from here).

`tensor-programs/` is intentionally kept separate: it pins a different toolchain
(v4.27.0) and so cannot share this build.

## Building

```bash
cd proofs
lake exe cache get      # fetch prebuilt Mathlib once for the whole workspace
lake build              # build all libs, or e.g. `lake build DkpsQuench`
```

> Note: many source filenames contain `-`/`.` (e.g. `drsb-v3.1.lean`), which are
> not valid Lean module names, so `lake build` will not pick them up as library
> modules. To check an individual draft, open it in the Lean LSP or run
> `lake env lean DkpsQuench/<file>.lean`.

## File inventory

### DkpsQuench/  (ICML Quench / DKPS)
- `quench-query-efficiency.lean` — main theorem from the Quench paper
- `dkps-statement-v4.lean`, `dkps-statement-v5.lean` — statement-level formalizations
- `dkps-v2.lean`, `dkps-v4.lean` — proof drafts (`Basic.lean` is identical to `dkps-v4.lean`)
- `Basic.lean` — copy of `dkps-v4.lean` (former default lib entry point)
- `dkps-aristotle-v2-121013.lean`, `dkps-aristotle-v2-121013-gpt-revision.lean` — Aristotle-generated + GPT revision
- `dkps-gpt-pro-v1.lean`, `dkps-gpt-pro-v2.lean` — GPT-Pro drafts
- `acharyya-2025-skeleton.lean` — `namespace DKPS` core types skeleton
- `negated-2026-02-14-011207.lean` — `namespace QuenchICML`, negated statement experiment
- `checks.lean` — scratch `#check`s for mathlib lemma names

### DrsbBridge/  (DRSB / Schrödinger bridge)
- `drsb-v1.lean` … `drsb-v4.lean`, `drsb-v3.1.lean` — proof drafts
- `prose/` — `main.tex` (annotated transcription), `orig-transcription.tex`, `suggested-fixes.tex` (PAC-Bayes bound for DRSB)

### Helm2025/  (HELM-2025)
- `helm-2025-stat-inference-dkps.lean` — main
- `-version1`, `-version2`, `-bounded-envelope`, `-bounded-labels`, `-option-B` — variants

### Oneoff/  (small standalone proofs)
- `wikifact_consistency_claim.lean` — `namespace WikiFactNoise` consistency claim

### tensor-programs/  (separate project — Tensor Programs / Master Theorem, Lean v4.27.0)
- Full project with the `TensorPrograms` library (`TP/` modules).
- `tensorprogram.lean` — Master Theorem scaffold scratch (`import TP.Empirical`).

## Missing prose
- DKPS/Quench and HELM-2025 prose proofs are not here yet — check the main machine.
