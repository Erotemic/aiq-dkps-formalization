# Remaining work tracker

Fresh as of 2026-06-12 (Opus). The active phase is the **Mathlib-readiness pass**:
getting the strong staged candidates into *mechanically-droppable-into-a-PR*
shape. Cross-refs: `mathlib-candidates.md` (candidate dossiers),
`prep_mathlib_review_and_readiness.md` (the readiness audit),
`pr-decisions.md` (R6 decisions awaiting sign-off, with recommendations),
`spectral-pr-decomposition.md` (spectral PR plan), `acharyya-plan.md`
(formalization-phase map — that phase is complete), `historical/` (archived
completed-phase docs).

## Guiding priority (user-directed 2026-06-12)

> Do **not** spend Fable effort on net-new content Mathlib reviewers may not
> converge on. Spend effort getting **what we already have** into great,
> ready-to-mechanically-drop-into-a-PR shape. → The highest-value remaining work
> is mechanical PR-shaping of the strong candidates (Opus + a few human
> decisions), **not** Fable. The Fable-leaning items are deferred.

---

## Done ledger (compressed)

- **Formalization phase** — complete (see `acharyya-plan.md`; residual sorries are
  documented superseded scaffolds).
- **Candidates #1–#13 staged** in `ForMathlib/` (see `mathlib-candidates.md`).
- **B1** ✅ sample-covariance / empirical-Gram eigenvalue concentration
  (`MatrixConcentration.lean`, `EntrywiseEigenvalue.lean`, `SampleCovariance.lean`;
  candidate #12).
- **B2** ✅ Berge maximum theorem — both halves + finite-family modulus + engine
  sibling (`Topology/Berge.lean`, `ApproxMinimizer.lean`; candidate #13).
- **R1/R1b** ✅ Gram rigidity refactor: reusable identity, two-ambient span-level
  core, thin equiv corollary.
- **Gram span-to-span core** ✅ (2026-06-13, user-directed): the fundamental
  theorem is now `exists_linearIsometry_span_map_eq_of_inner_eq`
  (`span φ →ₗᵢ span ψ`, audit §1.2); span-to-ambient
  `exists_linearIsometry_map_eq_of_inner_eq` is a one-line corollary
  (`(span ψ).subtypeₗᵢ.comp L`), name/signature preserved so downstream and the
  equiv/`gram`-iff corollaries are untouched. Added to `Challenge/Gram`.
- **R2** ✅ rank-PSD forward direction extracted; iff is now a combinator.
- **R3** ✅ spectral-stack PR decomposition plan (`spectral-pr-decomposition.md`).
- **R3b** ✅ Weyl operator-norm corollary `abs_eigenvalues_sub_le_opNorm`.
- **Trust artifacts synced** — headline Gram challenge kept simple; new public
  lemmas tracked in the `Challenge/Inventory/` conformance + leaderboard.
- **R2b** ✅ recon verdict: keep the spectral PSD proof (no cleaner route exists;
  no Fable). **Minimal imports**: one safe trim (`Star.Real` from `PosDef.lean`);
  shake is unreliable out-of-tree, rest deferred to in-tree PR time.
- **R6 decisions prepared** with recommendations in `pr-decisions.md` (awaiting
  sign-off).
- **F1–F6** ✅ (the old Fable task list — all done; archived to
  `historical/for-fable.md`).

Full repo builds green (8633 jobs); headline ForMathlib files are sorry-free.

---

## OPEN WORK, value-ranked for the current priority

### Track 1 — PR-shaping of the strong candidates (DO; high reviewer value; Opus + decisions)

These are the candidates worth driving to drop-ready. "Drop-ready" = statement
shape final, naming final, minimal imports, destination chosen, decomposed into
PR-sized files. The *final* submit (namespace unwrap, copyright header, provenance
moved to PR description) is Task E (gated — see D1); everything up to it is in
scope now.

| Candidate | Reviewer value | State | Left to drop-ready | Fable? |
|---|---|---|---|---|
| **Gram/Procrustes rigidity** | **High** — clean, novel, fundamental (audit A−/B+) | refactored (R1/R1b); modular, general | R6 naming decision; choose destination; minimal-import pass | no |
| **Weyl perturbation** | **High** — entirely absent upstream, canonical | done + opNorm form (R3b); decomposition planned (R3) | physically split per plan (PR-1 cross-term, PR-4 Weyl); naming; destination | no |
| **Rank-controlled PSD factorization** | **Good** — novel rank-controlled refinement | modularized (R2) | **R2b recon** (below); naming; destination | recon only |

### Track 2 — cheap recon that could close an item (DONE)

| Item | What | Effort | Fable? | Status |
|---|---|---|---|---|
| R2b | ✅ **DONE — verdict: keep the spectral proof.** Recon confirmed **no cleaner proof exists**: Mathlib has the PSD square root (`CFC.sqrt`, square `n×n` factor) but **no rank-factorization API** (`M = L·R`, `L : m×r`, `R : r×n`), so the rank-`≤d` compression into `Fin d` must be hand-built — the current spectral + `Classical.choose` construction is near-optimal. **No Fable needed.** Discovered upstream gap (deferred, net-new): a general `Matrix.exists_mul_eq_of_rank_le` would be broadly useful — flagged in `pr-decisions.md` D-7, not pursued. | S | no | **✅** |

### Track 3 — net-new Fable content (R4 + rank factorization DONE 2026-06-12, user-directed)

**Rank factorization (fable-options #1) ✅ DONE** — candidate #14,
`ForMathlib/LinearAlgebra/Matrix/RankFactorization.lean`
(`exists_eq_mul_rank` / `exists_eq_mul_of_rank_le` / `rank_le_iff_exists_eq_mul`).
Used to reprove the PSD forward direction through-API (audit §2.3 discharged: the
`Classical.choose`/embedding construction is gone; R2b verdict superseded).

| Item | What | Why deferred | Fable? |
|---|---|---|---|
| R4 | ✅ **DONE (Fable, 2026-06-12, user-directed).** DK projector section redesigned onto `Submodule.starProjection` of orthonormal-subfamily spans: RCLike (was ℝ-only), arbitrary `s : Finset (Fin m)` (was `< d` cutoff), bespoke `spectralProjection` def deleted. Plus three reusable bridge lemmas (`Orthonormal.starProjection_span_image_apply` etc.), generalized (Opus follow-on) to **any inner product space** via a `[HasOrthogonalProjection]` binder (no `FiniteDimensional` on the ambient space). Audit §4.1–§4.3 discharged. | — | done |
| R5 | **Courant–Fischer full min-max** (canonical min-over-subspaces). | Net-new; Mathlib has only the extremal Rayleigh case, and our directional bounds already suffice for Weyl. Pursue only if a reviewer asks. | yes |

### Track 4 — decisions needing human / Zulip input (R6)

**Prepared with recommendations in `pr-decisions.md`** (D-1…D-9). **Naming
decisions APPLIED 2026-06-12** (user-directed — pristine, fully-consistent Mathlib
names before Task E): D-2 the whole Gram family now uses a uniform `map_eq`
descriptor (`exists_linearIsometry_map_eq_of_inner_eq`,
`exists_linearIsometryEquiv_map_eq_of_inner_eq`,
`gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`); D-4 PSD forward →
`Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le`. Non-standard
convenience names live downstream as wrappers (only
`Acharyya2025.exists_linearIsometryEquiv_of_inner_eq`). Build green. The
remaining items (D-3/D-5/D-6 file moves — names unchanged; D-8 Zulip destinations;
D-9 in-tree imports) don't change declaration names and are safely left for the
mechanical Task-E pass / Zulip. None require Fable.

---

## C. Formalization-internal follow-ups (optional, not PR work)

| Item | What | Status |
|---|---|---|
| C1 | **Form B — raw-stress Helm bridge** (alternate `alignmentConsistency_of_*` via eigengap-free raw-stress consistency, surfacing `UniquePairProfile`). Side-by-side with spectral Form A as a "value of formalization" artifact. | future / opt-in |
| C2 | **Derive `halign`'s eigengap** by feeding B1 into the Helm Form-A bridge (replace the explicit `α ≤ λ_d` hypothesis). B1 is done, so this is now unblocked. | open (opt-in) |

(Also archived from `acharyya-plan.md`: optional strengthenings — sub-Gaussian
tails vs Chebyshev, sufficient conditions for `UniquePairProfile`, Helm per-ω
capstone.)

---

## A. Optional generalizations of staged candidates (low priority)

Make a staged candidate marginally stronger; none are reviewer-blocking. Deferred
under the current priority. Examples: #10 → `cfc`/RCLike (A1/A2); EntrywiseOpNorm
→ RCLike + sharp √card (A3); polar-factor sharp constant (A5); TendstoInMeasure →
pseudometric (A6). Full list preserved in git history (pre-2026-06-12 version).

---

## D. Gated / out of scope

| Item | Note |
|---|---|
| D1 | **Task E — submit the Mathlib PRs**: the final mechanical re-authoring per the AI-contribution policy (unwrap `ForMathlib` namespace, copyright headers, move AI-provenance from code comments to the PR description) + actual PR submission. **Gated** until a domain expert reviews the repo. Track 1 brings everything *up to* this line. |
| D2 | Old Fable list `historical/for-fable.md` F1–F6 — all DONE. |
