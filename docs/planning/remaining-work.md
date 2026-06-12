# Remaining work tracker

Consolidated 2026-06-12 (Opus). Single place for the open work after the
documentation pass, the `hmeas_spec` discharge, the `halign` Form-A reduction,
and the staging of Mathlib candidates #1–#11. Cross-refs:
`mathlib-candidates.md` (the candidate dossiers), `for-fable.md` (the F-items),
`hmeas-spec-discharge.md` (the seam history).

Legend — **Fable?**: whether the item is expected to need a Fable session (deep
new proof / large refactor) vs. doable by Opus. Most items below are
Opus-doable; Fable is flagged only where genuinely uncertain.

> **PIVOT 2026-06-12 (user-directed):** the new-contribution track below
> (sections **A**, **B2b-MDS-rederivation**, **C**) is **SHELVED — explicitly NOT
> complete.** Work pivots to a **Mathlib-readiness pass** (section **R**):
> bringing the staged headline candidates to a quality/API standard that would
> survive human expert review. This is **distinct from Task E** (the actual PR
> submission / AI-provenance re-authoring, still gated): R covers proof-quality,
> statement-shape, lemma decomposition, naming, and destination decisions — not
> namespace-unwrapping, copyright headers, or provenance stripping. Anchored to
> the AI audit `prep_mathlib_review_and_readiness.md` (commit b3b2569), verified
> independently (none of the headline results duplicate existing Mathlib).

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

## R. Mathlib-readiness pass (ACTIVE TRACK — quality for expert review, NOT Task E)

Goal: bring the four **headline** candidates to a standard a Mathlib reviewer
would accept on quality grounds (statement shape, lemma decomposition, naming,
API fit, destination). Stops short of PR mechanics (D1/Task E). Independent
Mathlib check confirms all four are non-duplicative.

| Item | What | Effort | Fable? | Status |
|---|---|---|---|---|
| R1 | ✅ **DONE** — **Gram/Procrustes rigidity** refactored (`ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean`). Extracted the reusable identity `inner_linearCombination_linearCombination` (inner product of two finite linear combinations over Gram data; no finiteness). Split out the **span-level core** `exists_linearIsometry_of_inner_eq` — equal inner products ⟹ a `LinearIsometry` from `span 𝕜 (range φ)` into `E` with `L (φ i) = ψ i`, needing **no finite-dimensionality** (strictly more general; addresses audit §1.2). `exists_linearIsometryEquiv_of_inner_eq` is now a thin finite-dim corollary (extend + surjectivity upgrade); `Matrix.gram` iff unchanged. Public names preserved (no downstream breakage); full build green, no sorries, ≤100-char lines. | M | no | **✅** |
| R1b | Gram **two-ambient-space** generalization (`φ : ι → E`, `ψ : ι → F`). The core machinery is space-agnostic; the span-level isometry into `F` is Opus-doable. The equiv-level corollary needs a `finrank E = finrank F` (or same-space) hypothesis. | M | attempt Opus, Fable fallback | open |
| R2 | **Rank-controlled PSD factorization** (`ForMathlib/LinearAlgebra/Matrix/PosDef.lean`). Split forward/backward into named one-direction lemmas; relocate the entrywise spectral helper `isHermitian_entry_eq_sum_eigenvalues` to a spectrum-focused home; rename. | M | no | open |
| R2b | PSD **alternate proof exploration** through existing Mathlib factorization/CFC APIs (vs. the hand-rolled embedding+`Classical.choose`). **Uncertain payoff** — the rank-compression step looks largely inherent; may end up justifying the spectral proof instead. | M–L | **likely** (exploratory) | open |
| R3 | **Spectral stack PR decomposition** (`CourantFischer.lean` 299 / `Spectrum.lean` 53 / `DavisKahan.lean` 418): split into PR-sized files + dependency graph: (1) cross-term identity, (2) quadratic-form diagonalization, (3) Courant–Fischer directional bounds, (4) Weyl, (5) Davis–Kahan corollaries. Mechanical file surgery + naming. | M | no | open |
| R3b | **Weyl operator-norm corollary**: a statement using `ContinuousLinearMap.opNorm` alongside the current `∀ x, ‖(T−S)x‖ ≤ ε‖x‖` form. Likely a thin wrap. | S | no (assess) | open |
| R4 | **Davis–Kahan redesign** to a reusable statement in terms of spectral subspaces / `orthogonalProjection` rather than DKPS index-cutoffs (audit §4). Genuine new statement + proof; clearest Fable item. | L | **yes** | open |
| R5 | **Courant–Fischer full min-max** (intermediate eigenvalues, canonical min-over-subspaces form) if reviewers want the variational statement vs. our directional bounds. Mathlib has only the extremal (iSup/iInf Rayleigh) case. | L | **yes** | open (defer; decide via Zulip) |
| R6 | **Statement-shape decisions needing human/Zulip input** (NOT auto-resolvable): same-space vs two-space Gram core; Davis–Kahan formulation; destination files for each. Prepare drafted alternatives, don't unilaterally finalize. | — | — | prepare options |

---

## D. Gated / out of scope

| Item | Note |
|---|---|
| D1 | **Task E — submit the Mathlib PRs** (re-author candidates #1–#13 per the AI-contribution policy: unwrap `ForMathlib` namespace, copyright headers, strip AI-provenance comments, PR mechanics). **Gated:** hold until a domain expert reviews the repo. Distinct from the R track above. |
| D2 | `for-fable.md` F1/F2/F4/F5/F6 — DONE. F3 = B2. |

---

## Working order

1. ✅ **B1 — sample-covariance eigenvalue concentration** (B1a engine + B1b iid layer).
2. ✅ **B2 — Berge maximum theorem** (UHC half + value-function half + finite-family modulus + engine sibling).
3. ⏸ **A / C / B2b-MDS-rederivation — SHELVED, not complete** (see PIVOT banner).
4. ▶ **R — Mathlib-readiness pass** (active). R1 ✅ done. Next R2 → R3 → R3b, with R1b/R2b/R4/R5 as the Fable-leaning follow-ups and R6 decisions surfaced to the user before finalizing.

### R-track naming note (R6, prepared option — NOT yet applied)
Audit §1.3 suggests `exists_linearIsometryEquiv_map_eq_of_inner_eq` (the
conclusion is a `map_eq`) over the current `exists_linearIsometryEquiv_of_inner_eq`.
Kept the current names in R1 to avoid churn / preserve downstream references;
surface for human decision before PR.
