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
- **Coupling (non-trivial):** the equiv name is referenced by
  `Acharyya2025/Procrustes.lean`, `Challenge/Gram/{Conformance,Leaderboard}.lean`,
  `Challenge/Inventory/{Conformance,Leaderboard}.lean`. A rename must update all of
  these (mechanical, ~6 files). **Because of this coupling, hold the rename until
  PR time (Task E)** rather than churn now — but fix the target name here.

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
- **Coupling:** the iff is used by `Acharyya2025/GramRealization.lean` and the
  Challenge suites; the forward lemma is new. Renaming/moving-namespace the forward
  lemma is low-coupling (only `#print axioms` in `Inventory/Leaderboard.lean`).
  Hold until PR time.

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

| Decision | Recommendation | Apply when |
|---|---|---|
| D-1 face | span-level core leads | PR time |
| D-2 Gram name | `..._map_eq_of_inner_eq` | PR time (6-file rename) |
| D-3 Gram dest | existing `GramMatrix.lean` | PR time |
| D-4 PSD name | forward in `PosSemidef` namespace | PR time |
| D-5 helper loc | move to `Spectrum.lean` | PR time |
| D-6 PSD dest | `PosDef.lean` | PR time |
| D-8 spectral dest | confirm on Zulip; helpers private | Zulip |
| D-9 imports | in-tree shake | PR time |

All recommendations are low-risk; the only non-trivial mechanical cost is the
D-2 rename (≈6 files). None require Fable.
