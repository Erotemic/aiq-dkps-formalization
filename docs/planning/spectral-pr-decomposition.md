# Spectral perturbation stack — PR decomposition plan (R3)

Readiness-track artifact (see `remaining-work.md` §R). The staged spectral stack
is currently three files; this plan breaks it into PR-sized, dependency-ordered
pieces a Mathlib reviewer can take one at a time. **No files are split yet** —
physical splitting and the destination-file choices are deferred to Task E / a
Zulip discussion (R6). Independent search confirmed none of these results exist
upstream (Weyl and Davis–Kahan are entirely absent; Courant–Fischer has only the
extremal Rayleigh case).

## Current files and declaration inventory

| File | Declarations (public unless noted) |
|---|---|
| `ForMathlib/Analysis/InnerProductSpace/Spectrum.lean` (53 L) | `inner_eigenvectorBasis_map_sub_eigenvectorBasis` (cross-term identity) |
| `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean` (≈315 L) | `specSubspace` (def), `finrank_specSubspace`, `repr_eq_zero_of_mem_specSubspace`, `sum_sq_norm_repr_eq_sq_norm` (private), `re_inner_map_self_eq_sum_eigenvalues_mul_sq`, `card_filter_le`/`card_filter_ge` (private), `exists_unit_vector_re_inner_le_eigenvalue`, `forall_unit_vector_eigenvalue_le_re_inner`, `eigenvalues_sub_le` (private), `abs_eigenvalues_sub_le`, `abs_eigenvalues_sub_le_opNorm` |
| `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean` (≈430 L) | `sum_norm_inner_eigenvectorBasis_map_sub_sq_le`, `sum_cross_norm_inner_eigenvectorBasis_sq_le`, `gap_of_rank_floor`, `sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor`, `spectralProjection` (def), `spectralProjection_apply`, `spectralProjection_apply_self`, `sum_norm_sub_spectralProjection_sq_eq`, `sum_norm_sub_spectralProjection_sq_le` |

## Dependency graph (as currently imported)

```
Spectrum (cross-term identity)        CourantFischer (diag → CF → Weyl)
        \                                   /
         \                                 /
          ----------> DavisKahan <--------
```

`CourantFischer` imports only Mathlib. `Spectrum` imports only Mathlib.
`DavisKahan` imports both `ForMathlib.Spectrum` and `ForMathlib.CourantFischer`.
So the upstreaming order is forced: the two leaves first, Davis–Kahan last.

## PR-sized pieces (in dependency order)

### PR-1 — Cross-term identity (tiny, lead with this)
- **Content:** `inner_eigenvectorBasis_map_sub_eigenvectorBasis` (already its own
  file, `Spectrum.lean`).
- **Deps:** Mathlib only. **Effort:** S. **Fable?** No.
- **Suggested home:** near `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.
- **Notes:** smallest, most self-contained; good first spectral PR to calibrate
  reviewer expectations. Audit §3 "isolate as a tiny PR."

### PR-2 — Quadratic-form diagonalization
- **Content:** `re_inner_map_self_eq_sum_eigenvalues_mul_sq`, plus the
  `specSubspace` scaffolding it and the CF bounds rest on (`specSubspace`,
  `finrank_specSubspace`, `repr_eq_zero_of_mem_specSubspace`,
  `sum_sq_norm_repr_eq_sq_norm`).
- **Deps:** Mathlib only. **Effort:** M. **Fable?** No.
- **Open decision (R6):** is `specSubspace` public API or a private/local
  scaffold? Audit §3.4 suggests private unless reviewers want a public
  spectral-subspace API. Recommend keeping it private until asked.

### PR-3 — Courant–Fischer directional bounds
- **Content:** `exists_unit_vector_re_inner_le_eigenvalue`,
  `forall_unit_vector_eigenvalue_le_re_inner` (+ private `card_filter_le`,
  `card_filter_ge`).
- **Deps:** PR-2. **Effort:** M. **Fable?** No.
- **Notes:** these are the discrete min-max directional inequalities, not the
  full variational `λₖ = min_S max ...` statement. The canonical min-max form is
  a separate, larger target (see R5) and is **not** required for Weyl.

### PR-4 — Weyl perturbation
- **Content:** `abs_eigenvalues_sub_le` (hypothesis form
  `∀ x, ‖(T − S) x‖ ≤ ε‖x‖`) and `abs_eigenvalues_sub_le_opNorm` (the
  operator-norm form via `ContinuousLinearMap.le_opNorm`), + private
  `eigenvalues_sub_le`.
- **Deps:** PR-3. **Effort:** S–M. **Fable?** No.
- **Notes:** Weyl is canonical and entirely absent upstream — likely the
  highest-value early spectral PR after PR-1. R3b already added the opNorm form
  so reviewers get both the convenient and the idiomatic statement.

### PR-5 — Davis–Kahan cross-block energy
- **Content:** `sum_norm_inner_eigenvectorBasis_map_sub_sq_le`,
  `sum_cross_norm_inner_eigenvectorBasis_sq_le`.
- **Deps:** PR-1 (cross-term) + PR-4 (Weyl) / PR-3. **Effort:** M. **Fable?** No.
- **Notes:** the `≤ nε²` / `≤ nε²/gap²` cross-energy bounds. Constants are
  deliberately conservative (documented in-file); separate canonical statement
  from application-sufficient constant per audit §3.5.

### PR-6 — Rank-floor gap corollaries
- **Content:** `gap_of_rank_floor`,
  `sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor`.
- **Deps:** PR-5. **Effort:** S–M. **Fable?** No.
- **Open decision (R6):** the gap hypothesis is written as a pairwise bound split
  by a cutoff `d` — exactly the DKPS shape, but audit §4.2 flags it as
  "application-shaped." Reviewers may want a separated-spectral-sets formulation.

### PR-7 — Projector form (NEEDS REDESIGN — Fable / R4)
- **Content:** `spectralProjection` (def), `spectralProjection_apply`,
  `spectralProjection_apply_self`, `sum_norm_sub_spectralProjection_sq_eq`,
  `sum_norm_sub_spectralProjection_sq_le`.
- **Deps:** PR-6. **Effort:** L. **Fable?** **Yes** (this is R4).
- **Notes:** the bespoke finite-sum `spectralProjection` (ℝ-only) is the part
  audit §4.1/§4.3 wants re-expressed via Mathlib's `orthogonalProjection` /
  submodule / CLM projection APIs, and the real-vs-`RCLike` target decided. Do
  **not** lead with this; it depends on the whole stack and on an API decision.

## Recommended upstreaming order

`PR-1` → `PR-4` (cross-term, then Weyl — both small, canonical, absent upstream)
→ `PR-2`/`PR-3` (the CF machinery underneath, if reviewers want it standalone)
→ `PR-5`/`PR-6` (Davis–Kahan energy + gap) → `PR-7` (projector, after the R4
redesign and an API decision).

## Items requiring human/Zulip input before finalizing (R6)
- `specSubspace`: public API vs private scaffold (PR-2).
- Davis–Kahan gap hypothesis shape: DKPS cutoff vs separated spectral sets (PR-6).
- `spectralProjection`: bespoke def vs `orthogonalProjection`; ℝ vs `RCLike` (PR-7/R4).
- Destination files for each PR (these are proposals, not decisions).
- Whether to pursue the full canonical Courant–Fischer min-max (R5).
