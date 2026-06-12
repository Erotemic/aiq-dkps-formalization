# Remaining work tracker

Consolidated 2026-06-12 (Opus). Single place for the open work after the
documentation pass, the `hmeas_spec` discharge, the `halign` Form-A reduction,
and the staging of Mathlib candidates #1–#11. Cross-refs:
`mathlib-candidates.md` (the candidate dossiers), `for-fable.md` (the F-items),
`hmeas-spec-discharge.md` (the seam history).

Legend — **Fable?**: whether the item is expected to need a Fable session (deep
new proof / large refactor) vs. doable by Opus. Most items below are
Opus-doable; Fable is flagged only where genuinely uncertain.

---

## A. Generalizations of already-staged candidates (existing → stronger)

These make a staged candidate more PR-worthy; low/medium effort, Opus-doable.

| Item | What | Effort | Fable? | Status |
|---|---|---|---|---|
| A1 | **#10 → connect to `Matrix.IsHermitian.cfc`**: prove `specTransform h B = cfc h B`, restate `measurable_specTransform` about the recognized `cfc` object. Unifies #9 (general C⋆) and #10 (matrix, no BorelSpace). | M | no | open |
| A2 | **#10 → RCLike (ℂ)**: generalize `measurable_specTransform` from `Matrix _ _ ℝ` to `RCLike 𝕜`. Rides on A1. | S–M | no | open |
| A3 | **EntrywiseOpNorm → RCLike** (`norm_toEuclideanLin_le_of_entry_le`, flagged `TODO(RCLike)`); plus loose `n` constant → sharp `√card` (Frobenius). | S | no | open |
| A4 | **F4 Davis–Kahan projector form**: sharp `ε²/gap²` per-block constant (vs loose `nε²`) + RCLike projector identity (cross-block bound is already RCLike). | M | no | open |
| A5 | **#6 polar factor sharp constant** `√(1+δ)·δ` (we ship `2δ`, documented). | S | no | open |
| A6 | **#7 `TendstoInMeasure` → pseudometric** (currently ℝ/EDist specific). | S | no | open |

---

## B. New Mathlib contributions (genuine new proof work)

| Item | What | Effort | Fable? | Status |
|---|---|---|---|---|
| **B1** | **Sample-covariance / empirical-Gram eigenvalue concentration** (the `halign` eigengap route). For `n` iid latents with a well-conditioned population covariance `Σ` (`λ_d(Σ) ≥ c`), the empirical (centred) Gram / sample covariance has `λ_d ≥ c/2` with high probability. **Plan (no matrix Bernstein needed):** entrywise Chebyshev on each sample-covariance entry (reuse `Acharyya2024.SecondMoment` + `Probability`) + union bound ⇒ entrywise `ε` ⇒ operator-norm `≤ d·ε` (`ForMathlib.norm_toEuclideanLin_le_of_entry_le`) ⇒ Weyl (`ForMathlib.abs_eigenvalues_sub_le`) ⇒ `λ_d` lower bound. Mathlib has *no* sample-covariance concentration. | L | maybe (assess after entrywise route) | **IN PROGRESS** |
| B2 | **Berge maximum theorem** (upper-hemicontinuity of the argmin/argmax correspondence) — would give the general form of `exists_modulus_pairDist` (for-fable F3). Mathlib has `Topology/Semicontinuity/Hemicontinuity.lean` but no Berge. **Decision pending:** raise upstream as a feature request vs. formalize the general theorem here. | L | likely | queued (after B1) |

---

## C. Non-Mathlib work (formalization-internal)

| Item | What | Effort | Fable? | Status |
|---|---|---|---|---|
| C1 | **Form B — raw-stress Helm bridge.** Alternate `alignmentConsistency_of_*` routed through the eigengap-free asymptotic raw-stress consistency (Acharyya 2024), surfacing the milder `UniquePairProfile` identifiability instead of the eigenvalue stability. Pairs with the spectral Form A as the side-by-side "value of formalization" artifact. | M–L | no | future / opt-in |
| C2 | **Fully derive `halign`'s eigengap** by feeding B1 into the Helm Form-A bridge (replace the explicit `α ≤ λ_d` HP hypothesis with a derivation from latent-distribution assumptions). Depends on B1. | M | no | blocked on B1 |

---

## D. Gated / out of scope

| Item | Note |
|---|---|
| D1 | **Task E — submit the Mathlib PRs** (re-author the 11 staged ForMathlib candidates per the AI-contribution policy). **Gated:** hold until a domain expert reviews the repo (user instruction). |
| D2 | `for-fable.md` F1/F2/F4/F5/F6 — DONE. F3 = B2 above. |

---

## Working order (user-directed 2026-06-12)

1. **B1 — sample-covariance eigenvalue concentration** (in progress).
2. **B2 — Berge maximum theorem** (next).

"Note if we need to bring in Fable at any point, but we can probably get very far
without it." — flagged per-item in the Fable? column; reassess B1 after the
entrywise route is in.
