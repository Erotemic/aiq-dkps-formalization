# Proofs

Lean4 (+ prose) formalizations, organized as **one Lake workspace with a
separate library per thrust**. Most of these come from TA1 theory-team results
(TA2 evaluation work). This is an exploration scratchpad.

Within each library, the **active** working file(s) live at the library root
(named `Basic.lean` where there's a single current version), and superseded
drafts are sequestered under an `old-attempt/` subfolder so they don't get
confused with the current work.

## Layout

```
proofs/
├── lakefile.toml      # umbrella workspace: one lean_lib per thrust, shared Mathlib
├── lean-toolchain     # v4.28.0-rc1 (shared by all libs below)
├── lake-manifest.json
├── .lake/             # single shared Mathlib build — no per-project duplication
├── DkpsQuench/        # lean_lib: ICML Quench companion proof (DKPS)  + prose/
├── DrsbBridge/        # lean_lib: DRSB (Schrödinger bridge)           + prose/
├── Helm2025/          # lean_lib: HELM-2025 statistical inference      + prose/
├── AcharyyaMDS/       # lean_lib: Acharyya DKPS/MDS embedding-consistency (shared foundation)
├── Oneoff/            # lean_lib: small standalone proofs
└── tensor-programs/   # SEPARATE project (pins Lean v4.27.0) — not in the workspace
```

The v4.28 thrusts live in a single Lake workspace so they share one Mathlib
checkout/build instead of compiling it once per project. Each library is
self-contained in its own root directory, so any one can be **lifted into a
standalone project later** by moving its directory out and giving it its own
`lakefile.toml` + `lean-toolchain` + `lake-manifest.json` (copy them from here).

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
> `lake env lean DkpsQuench/Basic.lean`.

## File inventory

### DkpsQuench/  (ICML Quench / DKPS)
- `Basic.lean` — **active** working proof (was `dkps-v4.lean`)
- `prose/` — ICML Quench paper source (`quench-tex-src/`, transcription `.md`)
- `old-attempt/` — superseded drafts: `quench-query-efficiency`, `dkps-statement-v4/v5`,
  `dkps-v2`, `dkps-v4` (= `Basic.lean`), `dkps-aristotle-v2-121013(+gpt-revision)`,
  `dkps-gpt-pro-v1/v2`, `negated-2026-02-14-011207`, `checks`

### DrsbBridge/  (DRSB / Schrödinger bridge)
- `drsb-v1.lean` — **active**: compiles, but may not match the prose claim
- `drsb-v4.lean` — **active**: pushing for the full proof (not complete yet)
- `prose/` — `main.tex` (annotated transcription), `orig-transcription.tex`, `suggested-fixes.tex` (PAC-Bayes bound for DRSB)
- `old-attempt/` — superseded drafts: `drsb-v2`, `drsb-v3`, `drsb-v3.1`

### Helm2025/  (HELM-2025)
- `Basic.lean` — **active** working proof (was `helm-2025-stat-inference-dkps.lean`)
- `prose/` — ACL paper source (`statistical-black-box-dkps-tex-src/`, transcription `.md`)
- `old-attempt/` — superseded drafts: `-version1`, `-version2`, `-bounded-envelope`,
  `-bounded-labels`, `-option-B`

### AcharyyaMDS/  (Acharyya DKPS/MDS embedding-consistency — shared foundation)
- `acharyya-2025-skeleton.lean` — raw-stress MDS / Trosset stability; ψ̂ → ψ consistency
  (Acharyya et al., "Consistent estimation of generative model representations in the
  data kernel perspective space"). Underpins both the Quench and HELM-2025 lines; not
  used directly by either proof yet.

### Oneoff/  (small standalone proofs)
- `wikifact_consistency_claim.lean` — `namespace WikiFactNoise` consistency claim

### tensor-programs/  (separate project — Tensor Programs / Master Theorem, Lean v4.27.0)
- Full project with the `TensorPrograms` library (`TP/` modules).
- `tensorprogram.lean` — Master Theorem scaffold scratch (`import TP.Empirical`).
