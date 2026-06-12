# for-fable.md — remaining ForMathlib extraction items that need real proving

Written 2026-06-12 by Claude Opus 4.8. These are the items NOT yet staged where
the obstacle is genuine proof work or missing upstream API (not just mechanical
porting). Each is scoped so a Fable session can execute it without re-doing the
discovery — **read the named source + the pointers before starting; do not
re-survey.** Verify per file with `~/.elan/bin/lake env lean <file>`; do not run
a full `lake build` until the end.

Context: `ForMathlib/README.md` (staging conventions), `planning/
mathlib-candidates.md` (full dossiers + what is already staged). Everything in
the candidate table #1–#8 plus the norm comparisons and the approximate-
minimizer stability lemma is ALREADY staged and building green; do not redo
those. Author new staged files as the current model (set the provenance line to
your own model label, not Fable, unless you are Fable).

## Why these were deferred (so they are not re-attempted blindly)

The clean, genuinely-general hard results are all already extracted. What
remains is exactly the set of items blocked on missing upstream API or requiring
a substantial new proof/redesign. Each entry says which.

---

## F1. #5 Gram factorization over `RCLike` (currently ℝ-only) — MEDIUM

File: `ForMathlib/LinearAlgebra/Matrix/PosDef.lean`, theorem
`posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self` (carries an in-file
`TODO(RCLike)`). The reverse direction is already field-general; only the
forward spectral construction is ℝ-specialized.

What to change: generalize `{B : Matrix (Fin n) (Fin n) ℝ}` →
`{𝕜} [RCLike 𝕜] {B : Matrix (Fin n) (Fin n) 𝕜}`. The construction is
`A k i = RCLike.ofReal (Real.sqrt (eigenvalues k)) * conj (eigenvectorUnitary i k)`
(note the `conj` — over ℝ it was absent). The Gram entry becomes
`(Aᴴ * A) i j = ∑_k conj (A k i) * A k j`; with the above `A`,
`conj (A k i) * A k j = ofReal (√λ_k) * U i k * (ofReal (√λ_k) * conj (U j k))
  = ofReal λ_k * U i k * conj (U j k)` (using `ofReal (√λ)² = ofReal λ` for
`λ ≥ 0`, `RCLike.conj_ofReal`, `RCLike.mul_conj`-style steps), matching the
RCLike spectral expansion `B i j = ∑_k λ_k U i k conj (U j k)`.

Watch: the entrywise spectral expansion helper
`isHermitian_entry_eq_sum_eigenvalues` must also be generalized (it currently
drops conjugation because over ℝ `star = id`). The `star_trivial` step in
`hconj` becomes `RCLike.conj_ofReal` / explicit `conj`. Estimate: ~1–2 hours of
conjugation bookkeeping; no missing upstream API. Keep the ℝ rewire in
`Acharyya2025/GramRealization.lean` working (instantiate at `𝕜 = ℝ`).

## F2. #5 ride-along: `eigenvalues₀` tail-vanishing — BLOCKED on upstream API

Goal: stage `Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le : B.PosSemidef →
B.rank ≤ d → ∀ i : Fin (card n), d ≤ i → hB.isHermitian.eigenvalues₀ i = 0`
against Mathlib's SORTED `Matrix.IsHermitian.eigenvalues₀`
(`Mathlib/Analysis/Matrix/Spectrum.lean`).

Blocker: `eigenvalues₀` exposes essentially only `eigenvalues₀_antitone`. The
counting proof needs "number of nonzero `eigenvalues₀` = rank", i.e. a bijection
between the nonzero `eigenvalues₀` (sorted) and the nonzero `eigenvalues`
(unsorted, where `rank_eq_card_non_zero_eigs` lives). Upstream does NOT provide
`eigenvalues₀ ≈ eigenvalues` as a permutation/multiset equality. Options for
Fable: (a) prove that bijection first (a real sub-lemma — `eigenvalues₀` is
defined via `Tuple.sort ∘ unsortedEigenvalues`, so relate to `eigenvalues` via
the sort permutation), then the counting + antitone argument is short; or
(b) raise it as an upstream feature request and skip. The local
`Acharyya2025/MatrixPerturbation.lean` `sortedEigenvalues_tail_eq_zero` already
works (operator-range proof) and is untouched — there is no downstream pressure,
so this is purely a Mathlib-niceness item. LOW priority.

## F3. `exists_modulus_pairDist` general form (Berge maximum theorem) — BLOCKED/REDESIGN

Source: `Acharyya2024/RawStress.lean:582` `exists_modulus_pairDist`. This is the
argmin-set stability with an explicit modulus: a uniform `δ` such that
`frobSub D Δ < δ ⇒ every minimizer of D has pairwise distances within ε of the
Δ-profile`. The general statement is a Berge-maximum-theorem / upper-hemicontinuity
of the argmin correspondence.

Blocker: Mathlib gained `Topology/Semicontinuity/Hemicontinuity.lean` but has NO
Berge maximum theorem. A clean general extraction would be the Berge theorem
itself (a substantial contribution and its own design project). The MDS-specific
proof here uses the already-staged `exists_subseq_tendsto_forall_le_of_approxMin`
(`ForMathlib/Topology/ApproxMinimizer.lean`) plus a contradiction at
`δ = 1/(k+1)`. NOT worth porting the MDS-specific version; the general Berge
theorem is the real target and should be its own scoped effort. Leave as-is.

## F4. Davis–Kahan: sharp / projector-form sin-Θ — STRENGTHENING (optional)

Staged `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean` has the correct
but loose constant `n ε² / gap²` (documented in-file). The sharp sin-Θ is
`ε² / gap²` per block, and the canonical statement is in terms of the spectral
PROJECTORS (`‖P̂ − P‖`), not the eigenvector-overlap sum. Strengthening to the
projector form / sharp constant is a genuine redesign (needs the projector
machinery and a tighter per-pair argument). Optional; the current form is a
valid first contribution. If attempted, keep the existing lemmas (they are
consumed by `Acharyya2025/RankGap.lean`) and ADD the projector form.

## F5. `h_conc_meas` measurable-selection seam — ✅ DISCHARGED 2026-06-12 (Fable)

RESOLVED without any measurable-selection theorem, by relocating the seam:

1. **Choice elimination** (`Acharyya2025/AlignedPipeline.lean`
   `configError_alignedSpectralConfig_le_iff_alignExists`): the aligned
   estimator's error event EQUALS the choice-free existential `AlignExists`
   (a raw embedding satisfying the bound witnesses it with `W = id`), so
   `Classical.choose` never enters the measurability question.
2. **Compact-existential measurability** (staged
   `ForMathlib/MeasureTheory/CompactExists.lean`
   `measurableSet_exists_mem_le`): `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable for
   compact `S`, `F` continuous in `y` / measurable in `ω` — countable dense
   approximation + sequential compactness, no selection.  Applied with `S` =
   the (closed, bounded, hence compact) set of inner-product-preserving CLMs of
   `ℝ^d` (`measurableSet_setOf_alignExists`).
3. **Sub-event Theorem 2** (`DkpsQuench/Basic.lean` `Theorem2_part1_subevent`
   … `Theorem2_part2_paper_subevent`): the concentration input generalized from
   (event HP + event measurable) to (a measurable HP sub-event contained in the
   event); originals recovered with `E := event`.
4. **Capstone** (`DkpsQuench/AcharyyaBridge.lean`
   `Theorem2_part2_of_aligned_spectral`): `h_conc_meas` REPLACED by the honest
   primitive `hmeas_spec` — measurability of the RAW spectral embedding
   `ω ↦ spectralConfig …(Dhat k ω)`.

**Remaining primitive (new, smaller seam): `hmeas_spec`.**  Borel measurability
of the fixed eigendecomposition-based map `SqMat n → Config n d`,
`B̂ ↦ spectralConfig (toEuclideanLin B̂)` (composed with measurable `Dhat`).  No
`ω`-dependent choice remains, but `spectralConfig` selects an eigenbasis
(`Classical.choice` inside Mathlib's spectral theorem), so its measurability in
the MATRIX argument is a real question: continuous on the open dense set where
the d-th spectral gap is positive (eigenprojector continuity), needs a Borel
patching argument at eigenvalue crossings — OR a redesign of `spectralConfig`
through the (continuous) rank-d spectral truncation `B̂ ↦ Σ_{k<d} λ_k u_k u_kᵀ`
Gram route.  Genuinely Fable-scale; substantially smaller than the original
selection problem.

---

## Priority for spending Fable credits (if any)

1. **F1** (RCLike Gram factorization) — purely mechanical, no blocker, makes #5
   a clean Mathlib PR. Best credit-per-value. → OPUS work.
2. **F5 residual** (`hmeas_spec`: Borel measurability of the raw spectral
   embedding in the matrix argument) — the only remaining load-bearing seam;
   see the discharged-F5 entry for the two candidate routes. Fable-scale.
3. **F4** (sharp Davis–Kahan) — only if aiming for a top-tier spectral PR.
4. **F2** — UNBLOCKED (discovery 2026-06-12): current Mathlib *defines*
   `IsHermitian.eigenvalues` as `eigenvalues₀ ∘ (Fintype equiv)`
   (`Mathlib/Analysis/Matrix/Spectrum.lean:65`), so the sorted/unsorted
   bijection is definitional; the counting proof (equiv transport of
   `rank_eq_card_non_zero_eigs` + `eigenvalues₀_antitone` + PSD nonnegativity)
   is mechanical. → OPUS work.
5. **F3** — skip; raise the Berge maximum theorem upstream instead.

Everything else (the whole spectral-perturbation toolkit, probability lemmas,
norm comparisons, approximate-minimizer stability) is DONE and needs no Fable.
