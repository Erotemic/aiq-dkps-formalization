# PR-readiness decisions awaiting sign-off (R6)

These are the decisions that block "mechanically droppable into a Mathlib PR" but
are NOT auto-resolvable by Opus — they are naming/shape/destination choices a
human (or Zulip) should bless. Each has a recommendation; once chosen, applying
it is mechanical (rename + update references, or move file). Nothing here is
applied yet. Downstream-coupling noted so the cost of each is clear.

Convention reminder: the actual rename/move + the AI-provenance re-authoring is
Task E (gated). This doc just fixes *what* the final shapes should be.

> **Note (2026-06-14):** the challenge layer was restructured into
> `Challenge/MathlibCandidate/` + `Challenge/MathlibPending/` (see
> `Challenge/README.md`). Older `Challenge/Gram`, `Challenge/PsdGram`,
> `Challenge/Spectral`, and `Challenge/Inventory/*` paths mentioned below are
> historical; the live homes are the candidate/pending folders and
> `comparator/{candidate,pending}-*.json`.

---

## D-1. Gram — public face / which theorem leads

**Question.** We now have four Gram results: the **span-to-span core**
`exists_linearIsometry_span_map_eq_of_inner_eq` (`span φ →ₗᵢ span ψ`, two spaces,
no finiteness), its **span-to-ambient corollary**
`exists_linearIsometry_map_eq_of_inner_eq` (`span φ →ₗᵢ F`, the core composed with
the inclusion `span ψ ↪ F`), the finite-dim ambient equivalence
`exists_linearIsometryEquiv_map_eq_of_inner_eq`, and the `Matrix.gram` iff.

- ✅ **APPLIED 2026-06-13 (user-directed):** the span-to-span core is now the
  fundamental theorem and is a **`LinearIsometryEquiv`**
  `exists_linearIsometryEquiv_span_map_eq_of_inner_eq` (`span φ ≃ₗᵢ span ψ`, the
  two spans isometrically isomorphic, codomain the full `span 𝕜 (range ψ)`; audit
  §1.2). Below it: the `LinearIsometry`
  `exists_linearIsometry_span_map_eq_of_inner_eq` (`.toLinearIsometry`,
  compatibility corollary), the span-to-ambient
  `exists_linearIsometry_map_eq_of_inner_eq` (`(span ψ).subtypeₗᵢ.comp L`), the
  ambient equivalence, and the `gram` iff — each a thin derivation of the
  previous. Downstream callers unaffected (all kept names/signatures). Build
  green; axiom audit clean (propext/Classical.choice/Quot.sound only); added to
  the headline `Challenge/Gram` conformance + leaderboard + comparator config.

## D-2. Gram — naming

**Question.** Audit §1.3 suggests the equivalence's name should reflect that the
conclusion is a `map_eq`.

| Current | Audit suggestion | Alt |
|---|---|---|
| `exists_linearIsometryEquiv_of_inner_eq` | `exists_linearIsometryEquiv_map_eq_of_inner_eq` | `..._apply_eq_of_inner_eq` |

- **Recommendation:** make the whole Gram family use the `map_eq` descriptor
  uniformly (the Mathlib idiom for "∃ f, ∀ i, f xᵢ = yᵢ").
- ✅ **APPLIED 2026-06-12** (user-directed: pristine, fully-consistent Mathlib
  names before Task E). All three existence statements now read uniformly:
  `exists_linearIsometry_map_eq_of_inner_eq` (core),
  `exists_linearIsometryEquiv_map_eq_of_inner_eq` (equiv),
  `gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq` (iff);
  `inner_linearCombination_linearCombination` unchanged. Updated `GramMatrix.lean`
  and the `Challenge/Gram/` + `Challenge/Inventory/` conformance & leaderboard
  files; repointed the `ForMathlib.`-qualified call in `Procrustes.lean`.
- **Wrapper policy (user-directed):** Mathlib-candidate names must be pristine
  with no inconsistency; any non-standard convenience name lives **downstream** as
  a wrapper in the DKPS libs. The only such wrapper is
  `Acharyya2025.exists_linearIsometryEquiv_of_inner_eq` (the ℝ-instantiation kept
  for DKPS call-sites). Full build green.

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
Coupling: post-restructure it is no longer a separately-listed challenge leaf (it
is covered transitively by the RankPsdRealization leaf), so no `#print axioms`
path needs updating; just move the source declaration at PR time.

## D-6. PSD — destination

The factorization theorem fits near `Matrix.PosSemidef` (`LinearAlgebra/Matrix/
PosDef.lean`). **Recommendation:** factorization → `PosDef.lean`; entry helper →
`Spectrum.lean` (per D-5). Confirm on Zulip (could also live near `Matrix.gram`).

## D-7. PSD — discovered upstream gap (NOT for now)

**RESOLVED (Fable, 2026-06-12):** the gap is now filled — candidate #14
(`ForMathlib/LinearAlgebra/Matrix/RankFactorization.lean`) supplies
`exists_eq_mul_rank` / `exists_eq_mul_of_rank_le` / `rank_le_iff_exists_eq_mul`,
and the PSD forward direction is reproved through it (square factorization →
rank-factor → square factorization), eliminating the `Classical.choose`/embedding
construction entirely (audit §2.3 discharged).

---

## D-8. Spectral stack — destinations & sequencing

Per `spectral-pr-decomposition.md`: PR-1 cross-term (`Spectrum.lean` addition),
then Weyl (`Analysis/InnerProductSpace/CourantFischer.lean`, new file, CF + Weyl
together — they are one coherent PR). DK is a later PR (and needs R4 first).
The current 3-file ForMathlib structure already maps to these PRs; **no physical
re-split is needed.** **Update (Fable, 2026-06-12):** the PR-7 API decision is
made — the projector form is redesigned onto `Submodule.starProjection`
(`spectralProjection` deleted; RCLike; arbitrary `Finset` index sets), so PR-7 is
no longer blocked on a redesign. Remaining decisions: confirm destination files
on Zulip; `specSubspace` public-vs-private (recommend **private** until asked).

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
| D-2 Gram name | whole family uniform `map_eq` (core + equiv + iff) | ✅ APPLIED 2026-06-12 |
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
