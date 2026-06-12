# PR-readiness decisions awaiting sign-off (R6)

These are the decisions that block "mechanically droppable into a Mathlib PR" but
are NOT auto-resolvable by Opus — they are naming/shape/destination choices a
human (or Zulip) should bless. Each has a recommendation; once chosen, applying
it is mechanical (rename + update references, or move file). Nothing here is
applied yet. Downstream-coupling noted so the cost of each is clear.

Convention reminder: the actual rename/move + the AI-provenance re-authoring is
Task E (gated). This doc just fixes *what* the final shapes should be.

---

## D-1. Gram — public face / which theorem leads

**Question.** We have three Gram results: the span-level core
`exists_linearIsometry_of_inner_eq` (two spaces, no finiteness), the finite-dim
ambient equivalence `exists_linearIsometryEquiv_of_inner_eq`, and the
`Matrix.gram` iff. Which is the headline of the PR?

- **Option A (recommended):** lead with the **span-level core** as the
  fundamental result (audit §1.2 — "arguably the fundamental result"), with the
  equivalence and `gram` iff as corollaries. Matches how Mathlib prefers
  general-core + specialized-corollaries.
- Option B: keep the ambient equivalence as the headline (most intuitive:
  "equal Grams ⇒ orthogonal alignment"), core as a supporting lemma.

**Recommendation: A.** Coupling: none (both already exist and build).

## D-2. Gram — naming

**Question.** Audit §1.3 suggests the equivalence's name should reflect that the
conclusion is a `map_eq`.

| Current | Audit suggestion | Alt |
|---|---|---|
| `exists_linearIsometryEquiv_of_inner_eq` | `exists_linearIsometryEquiv_map_eq_of_inner_eq` | `..._apply_eq_of_inner_eq` |

- **Recommendation:** adopt `exists_linearIsometryEquiv_map_eq_of_inner_eq` (the
  `map_eq` suffix is the Mathlib idiom for "∃ f, ∀ i, f xᵢ = yᵢ"). Keep
  `exists_linearIsometry_of_inner_eq` and `inner_linearCombination_linearCombination`
  as-is (already idiomatic).
- ✅ **APPLIED 2026-06-12** (user-directed: get names right before Task E).
  Renamed across `GramMatrix.lean` and the `Challenge/Gram/` +
  `Challenge/Inventory/` conformance & leaderboard files; the `ForMathlib.`-qualified
  call in `Acharyya2025/Procrustes.lean` was repointed. The DKPS ℝ-wrapper
  `Acharyya2025.exists_linearIsometryEquiv_of_inner_eq` deliberately **keeps its own
  name** (it is a downstream convenience, not a Mathlib candidate; its docstring
  says so). Full build green.

## D-3. Gram — destination file

Mathlib already has `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean` (defines
`Matrix.gram`). **Recommendation:** add all three results there. No new file.
Coupling: none.

---

## D-4. PSD — naming

**Question.** Audit §2.4 finds the iff name verbose/conjunctive.

| Role | Current | Suggested |
|---|---|---|
| iff | `posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self` | keep, or `PosSemidef.exists_conjTranspose_mul_self_iff_rank_le` |
| forward | `exists_conjTranspose_mul_self_of_posSemidef_of_rank_le` | `PosSemidef.exists_conjTranspose_mul_self_of_rank_le` (dot-notation) |

- **Recommendation:** put the forward lemma in the `Matrix.PosSemidef` namespace so
  `hB.exists_conjTranspose_mul_self_of_rank_le hrank` works by dot notation; keep
  the iff name (it is searchable and the convention for `↔`).
- ✅ **APPLIED 2026-06-12.** Forward lemma is now
  `ForMathlib.Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le` (drops the
  now-redundant `_of_posSemidef`); at PR time `ForMathlib.` strips to
  `Matrix.PosSemidef.…` and `hB.…` dot notation works. The iff calls it as
  `PosSemidef.exists_conjTranspose_mul_self_of_rank_le h.1 h.2`; `#print axioms` in
  `Inventory/Leaderboard.lean` updated. Iff name kept. Full build green.

## D-5. PSD — entry-helper location

`isHermitian_entry_eq_sum_eigenvalues` (entrywise spectral theorem) currently
lives in `PosDef.lean`. Audit §2.2: it belongs in a spectrum-focused home
(`Mathlib/Analysis/Matrix/Spectrum.lean`). **Recommendation:** move it to the
spectrum file at PR time; it is a general spectral fact, not PSD-specific.
Coupling: referenced by `Challenge/*` (`#print axioms`) — update those paths.

## D-6. PSD — destination

The factorization theorem fits near `Matrix.PosSemidef` (`LinearAlgebra/Matrix/
PosDef.lean`). **Recommendation:** factorization → `PosDef.lean`; entry helper →
`Spectrum.lean` (per D-5). Confirm on Zulip (could also live near `Matrix.gram`).

## D-7. PSD — discovered upstream gap (NOT for now)

R2b recon verdict: **no cleaner proof exists** — Mathlib has no rank-factorization
API (`M = L·R`, `L : m×r`, `R : r×n`, `r = rank`), so the rank-≤d compression must
be hand-built. The current spectral+`Classical.choose` proof is near-optimal; keep
it. *Discovered candidate (deferred, net-new):* a general
`Matrix.exists_mul_eq_of_rank_le` would clean this up and is broadly useful — but
it is net-new content, so not pursued under the current priority.

---

## D-8. Spectral stack — destinations & sequencing

Per `spectral-pr-decomposition.md`: PR-1 cross-term (`Spectrum.lean` addition),
then Weyl (`Analysis/InnerProductSpace/CourantFischer.lean`, new file, CF + Weyl
together — they are one coherent PR). DK is a later PR (and needs R4 first).
The current 3-file ForMathlib structure already maps to these PRs; **no physical
re-split is needed.** Decisions: confirm destination files on Zulip;
`specSubspace`/`spectralProjection` public-vs-private (recommend **private** until
asked).

---

## D-9. Import minimization — defer to in-tree PR time

Out-of-tree `shake` gives false positives here (it flagged genuinely-used imports
in `PosDef.lean` and `DavisKahan.lean`). One safe trim was verified and applied
(`Mathlib.Algebra.Order.Star.Real` from `PosDef.lean`). **Recommendation:** do the
remaining import minimization in-tree at PR time, where Mathlib CI `shake` is
authoritative; do not trim further out-of-tree.

---

## Summary — what unblocks "drop-ready"

| Decision | Recommendation | Status |
|---|---|---|
| D-1 face | span-level core leads | satisfied (core already presented first) |
| D-2 Gram name | `..._map_eq_of_inner_eq` | ✅ APPLIED 2026-06-12 |
| D-3 Gram dest | existing `GramMatrix.lean` | accepted; move at PR time |
| D-4 PSD name | forward in `PosSemidef` namespace | ✅ APPLIED 2026-06-12 |
| D-5 helper loc | move to `Spectrum.lean` | accepted; move at PR time (name unchanged) |
| D-6 PSD dest | `PosDef.lean` | accepted; PR time |
| D-8 spectral dest | confirm on Zulip; helpers private | Zulip |
| D-9 imports | in-tree shake | accepted; PR time |

Naming decisions (D-2, D-4) are **applied**; the remaining items are file
moves / destination confirmations whose declaration *names* don't change, so they
are safely left for the mechanical Task-E pass (D-5/D-6) or Zulip (D-8). None
require Fable.
