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
| **B1** | **Sample-covariance / empirical-Gram eigenvalue concentration** (the `halign` eigengap route). | L | no | **✅ DONE** |
| B1a | ✅ **DONE** — the generic engine (no matrix Bernstein): `ForMathlib.Matrix.abs_sortedEig_sub_le_of_entry_le` (entrywise ⇒ eigenvalue via Weyl), `ForMathlib.measure_exists_entry_gt_le` (entrywise Chebyshev + union bound), `ForMathlib.measure_forall_abs_sortedEig_sub_le_ge` (eigenvalue concentration), `ForMathlib.measure_forall_sortedEig_ge_ge` (eigenvalue **lower bound** — take `η = c/(2n)`). Takes per-entry second-moment bounds as hypotheses (matches the existing dissimilarity-concentration style). Commit `2356fd0`. | — | no | ✅ |
| B1b | ✅ **DONE** — the iid → per-entry-second-moment layer specializing B1a to the actual *sample covariance* `Σ̂_{kl} = n⁻¹ Σᵢ Vᵢ(k)Vᵢ(l)`. File `ForMathlib/Probability/Moments/SampleCovariance.lean`: `ForMathlib.sampleCovariance` (the empirical covariance), `ForMathlib.integral_sq_sampleCovariance_entry_le` (feeds the coordinate products `Yᵢ = Vᵢ(·)ₖ Vᵢ(·)ₗ` into the scalar `integral_norm_sq_average_sub_of_iid` to get `∫(Σ̂_{kl}−Cov_{kl})² ≤ v/n`), `ForMathlib.isHermitian_sampleCovariance`, and the capstone `ForMathlib.measure_forall_sampleCovariance_sortedEig_ge_ge` (composes the entry bound with the B1a engine `measure_forall_sortedEig_ge_ge`). The product-level iid hypotheses (`MemLp`/`IndepFun`/identical-distribution of the coordinate products) are taken as inputs, matching the existing dissimilarity-concentration style; per-coordinate measurability `∀ i k, Measurable (V i · k)` avoids the `EuclideanSpace` measurable-space friction. | M | no | ✅ |
| **B2** | ✅ **DONE** (upper-hemicontinuity half, no Fable) — **Berge maximum theorem** for a fixed compact constraint, staged in `ForMathlib/Topology/Berge.lean`: `tendsto_eval_sub_of_isCompact` (uniform conv. on compact from joint continuity), `tendsto_subseq_isMinOn_of_isMinOn` (sequential upper hemicontinuity / closed graph), `upperHemicontinuousAt_isMinOn` (lands on Mathlib's `UpperHemicontinuousAt` via `of_sequences`), `exists_modulus_isMinOn` (uniform `ε`–`δ` modulus = general form of `exists_modulus_pairDist`). Plus engine sibling `exists_subseq_tendsto_isMinOn_of_approxMinOn`. Candidate #13. | L | no | **✅** |
| B2b | ✅ **DONE** — (i) the *value-function-continuity* half of Berge: `ForMathlib.continuous_iInf_of_isCompact` (`p ↦ ⨅ x ∈ K, g p x` continuous, via a squeeze using `tendsto_eval_sub_of_isCompact`). (ii) The modulus generalized to a **finite family of jointly-continuous closeness invariants** `ForMathlib.exists_modulus_isMinOn_family` (subsumes the affine-invariant `pairDistErr` shape; the metric `exists_modulus_isMinOn` is now its `ι = Unit`, `ρ = dist` corollary). **Finding:** a *literal* re-derivation of `exists_modulus_pairDist` is NOT a clean instantiation — MDS minimizes over the non-compact config space and recovers compactness only via coercive centering into a `Δ`-dependent box; that ingredient is genuinely MDS-specific and not subsumed by the fixed-`K` Berge theorem. Documented honestly at both `exists_modulus_pairDist` and in `Berge.lean`; the bespoke MDS proof is kept. | M | no | **✅** |

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
| D1 | **Task E — submit the Mathlib PRs** (re-author the staged ForMathlib candidates #1–#13 per the AI-contribution policy). **Gated:** hold until a domain expert reviews the repo (user instruction). |
| D2 | `for-fable.md` F1/F2/F4/F5/F6 — DONE. F3 = B2 above. |

---

## Working order (user-directed 2026-06-12)

1. ✅ **B1 — sample-covariance eigenvalue concentration** (done: B1a engine + B1b iid layer).
2. ✅ **B2 — Berge maximum theorem** (done: upper-hemicontinuity half + value-function half (B2b) + finite-family modulus generalization + engine sibling).

"Note if we need to bring in Fable at any point, but we can probably get very far
without it." — flagged per-item in the Fable? column; reassess B1 after the
entrywise route is in.
