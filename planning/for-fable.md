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

## F1. #5 Gram factorization over `RCLike` — ✅ DONE 2026-06-12 (Opus)

`ForMathlib/LinearAlgebra/Matrix/PosDef.lean`
`posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self` is now stated and
proved over `{𝕜} [RCLike 𝕜]`.  Construction
`A k i = (√λ_k : 𝕜) * conj (eigenvectorUnitary i k)`; the entrywise spectral
expansion helper `isHermitian_entry_eq_sum_eigenvalues` carries the conjugation
(`B i j = ∑_k (λ_k : 𝕜) · U i k · conj (U j k)`).  `open scoped ComplexOrder`
supplies `StarOrderedRing 𝕜` for the reverse direction.  The ℝ consumer
`Acharyya2025/GramRealization.lean` builds unchanged (ℝ is `RCLike`, conj = id).

## F2. #5 ride-along: `eigenvalues₀` tail-vanishing — ✅ DONE 2026-06-12 (Opus)

UNBLOCKED (the "missing bijection" was definitional): current Mathlib *defines*
`IsHermitian.eigenvalues i = eigenvalues₀ ((Fintype.equivOfCardEq …).symm i)`
(`Mathlib/Analysis/Matrix/Spectrum.lean`).  Staged
`ForMathlib/Analysis/Matrix/Spectrum.lean`
`PosSemidef.eigenvalues₀_eq_zero_of_le : B.PosSemidef → B.rank ≤ d →
∀ i ≥ d, eigenvalues₀ i = 0`, over `RCLike 𝕜`: nonnegativity (PSD) + antitonicity
give `> d` nonzero sorted eigenvalues at any nonzero tail index, but their count
equals `rank ≤ d` via `Equiv.subtypeEquiv` transport of
`rank_eq_card_non_zero_eigs`; `omega` closes.

NOT rewired into `Acharyya2025/MatrixPerturbation.lean`: retiring the local
operator-world `sortedEigenvalues` for `eigenvalues₀` is a large refactor
(RankGap, ConfigPerturbation, AlignedPipeline, the capstone hypotheses all
thread `sortedEigenvalues`) with NO downstream benefit and high regression risk.
Deliberately left; the staged lemma stands alone as a Mathlib addition.

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

**Opus assessment 2026-06-12 (after F1/F2).**  `hmeas_spec` as stated is most
likely NOT provable as-is, and is the right primitive to leave for the domain
expert.  Reason: `spectralConfig` is built from `eigenvectorBasis`, which is a
non-canonical `Classical.choice` eigenbasis and is discontinuous at eigenvalue
crossings, so `B̂ ↦ eigenvectorBasis(B̂)` is not measurable in general.  Note
also the capstone does NOT assume `Dhat` itself measurable — `hmeas_spec`
silently bundles that too.  The only honest discharge routes both require real
new theory:
  (a) **O(d)-invariant relocation.**  `AlignExists` is invariant under post-
      composing `spectralConfig` with any isometry, so it depends on `B̂` only
      through the rank-`d` weighted spectral projector `P_d(B̂) = Σ_{k<d} λ_k
      u_k u_kᵀ` (= the truncated `B̂`), which IS measurable (continuous on the
      open gap-positive set, Borel everywhere).  Re-derive
      `measurableSet_setOf_alignExists` from `Measurable (B̂ ↦ P_d(B̂))` plus a
      `ConfigError`-via-Gram reformulation — but `P_d` measurability is itself a
      genuine theorem (continuous spectral truncation) and the Gram
      reformulation of `AlignExists` is nontrivial.
  (b) **Redefine `spectralConfig`** through the (continuous) rank-`d` truncation
      Gram route so it is manifestly measurable, then re-thread the whole
      `ConfigPerturbation` capstone.  Larger blast radius.
Recommendation: leave `hmeas_spec` as the documented honest primitive for the
review; both routes are a scoped research task, not mechanical work.

---

## Priority for spending Fable credits (if any)

1. ~~F1 (RCLike Gram factorization)~~ — ✅ DONE 2026-06-12 (Opus).
2. ~~F2 (eigenvalues₀ tail)~~ — ✅ DONE 2026-06-12 (Opus).
3. **F4** (sharp / projector-form Davis–Kahan) — the remaining genuine
   ForMathlib strengthening; medium effort (needs the spectral-projector
   Frobenius identity `‖P̂−P‖_F² = 2·Σ_cross ⟪uᵢ,v̂ⱼ⟫²`).
4. **F5 residual** (`hmeas_spec`) — scoped research task (see assessment above),
   not mechanical; leave documented for the domain expert.
5. **F3** — skip; raise the Berge maximum theorem upstream instead.

Everything else (the whole spectral-perturbation toolkit, probability lemmas,
norm comparisons, approximate-minimizer stability) is DONE and needs no Fable.
