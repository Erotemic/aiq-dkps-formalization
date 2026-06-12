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

## F3. `exists_modulus_pairDist` general form (Berge maximum theorem) — ✅ DONE 2026-06-12 (Opus)

Source: `Acharyya2024/RawStress.lean:687` `exists_modulus_pairDist`. This is the
argmin-set stability with an explicit modulus: a uniform `δ` such that
`frobSub D Δ < δ ⇒ every minimizer of D has pairwise distances within ε of the
Δ-profile`. The general statement is a Berge-maximum-theorem / upper-hemicontinuity
of the argmin correspondence.

Resolved WITHOUT Fable. The general upper-hemicontinuity half of Berge's maximum
theorem (fixed compact constraint) is now staged in
`ForMathlib/Topology/Berge.lean`:
* `tendsto_eval_sub_of_isCompact` — sequential uniform convergence on a compact set
  from joint continuity (the only consequence of "`g (pₖ) → g p₀` uniformly on `K`"
  Berge needs).
* `tendsto_subseq_isMinOn_of_isMinOn` — sequential upper hemicontinuity (closed
  graph): minimizers for `pₖ → p₀` subconverge to a minimizer for `p₀`.
* `upperHemicontinuousAt_isMinOn` — the same on Mathlib's own
  `UpperHemicontinuousAt` predicate for `p ↦ {x ∈ K | IsMinOn (g p) K x}`, via
  `UpperHemicontinuousAt.of_sequences` (needs `X` Hausdorff).
* `exists_modulus_isMinOn` — the uniform `ε`–`δ` modulus form (metric `P`, `X`):
  exactly the shape of `exists_modulus_pairDist`, generalized to an arbitrary
  jointly-continuous objective.

Engine generalization added: `ForMathlib.exists_subseq_tendsto_isMinOn_of_approxMinOn`
(the `K`-constrained sibling of `exists_subseq_tendsto_forall_le_of_approxMin`,
concluding `IsMinOn F K` instead of a global minimizer).

Remaining (optional, NOT blocking): the value-function-continuity half of Berge
(`p ↦ ⨅ x ∈ K, g p x` continuous) and instantiating `exists_modulus_isMinOn` at
the raw-stress objective to literally re-derive `exists_modulus_pairDist` (the MDS
version compares `pairDistErr`, a different pseudometric — a wiring exercise). See
`mathlib-candidates.md` candidate #13.

## F4. Davis–Kahan: projector-form sin-Θ — ✅ DONE 2026-06-12 (Opus)

The canonical projector form is now staged in
`ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean` (section `RealProjector`,
over ℝ):
* `spectralProjection b d` — the rank-`d` orthogonal projector
  `x ↦ ∑_{i<d} ⟪bᵢ,x⟫ • bᵢ` of an orthonormal basis;
* `sum_norm_sub_spectralProjection_sq_eq` — the IDENTITY (any two orthonormal
  bases): `∑ₖ ‖(P_v − P_u) uₖ‖² = 2 · Σ_{i<d,j≥d} ⟪uᵢ,vⱼ⟫²`, i.e. the squared
  Frobenius distance between the two rank-`d` projectors is twice the
  cross-block overlap (proof = `‖a−b‖²` expansion + Parseval, no operator
  algebra / no trace API needed);
* `sum_norm_sub_spectralProjection_sq_le` — the resulting `‖P̂−P‖_F² ≤ 2nε²/gap²`
  Davis–Kahan sin-Θ bound (instantiates the eigenbases + the staged cross-block
  bound).

Remaining (truly optional): the SHARP constant (`ε²/gap²` per block, vs the
loose `nε²` total cross-energy) and the `RCLike` generalization of the projector
section (the cross-block bound is already RCLike; only the projector identity is
ℝ — the conj/re bookkeeping is routine but omitted). Neither blocks anything.

## F6. `hcenter` discharged one level deeper to response-mean — ✅ DONE 2026-06-12 (Opus)

`DkpsQuench/AcharyyaBridge.lean` now has `Theorem2_part2_of_response_mean`: the
Quench query-efficiency capstone with the packaged entrywise CMDS-closeness
event `hcenter` REPLACED by the paper's actual upstream input — the uniform
response-mean closeness HP event `{ω | UniformResponseMeanClose (Xbar u ω) μ
(η u)}` — deriving the entrywise CMDS chain internally via
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean`.
The shared sub-event/measurability + Theorem-2 machinery was extracted into the
reusable `quench_part2_from_aligned_configError_hp` (both capstones feed it).
The residual primitives are unchanged: `hmeas_spec` (raw response-based spectral
embedding measurability — see F5 residual) and the model coverage `h_cover`.
Completed further: `Theorem2_part2_of_second_moment` derives the response-mean
event itself from iid second-moment bounds `∫ ‖X̄ᵢ − μᵢ‖² ≤ σ2` with vanishing
Chebyshev ratio, via `RateChain.highProb_uniformResponseMeanClose_of_secondMoment`.
The DkpsQuench query-efficiency conclusion now follows end-to-end from the
literal bottom of the chain (iid second moments) + spectral structure + the
genuine Quench assumptions; only `hmeas_spec` and `h_cover` remain primitive.

## F5. `h_conc_meas` / `hmeas_spec` measurability seam — ✅ FULLY DISCHARGED 2026-06-12 (Fable + Opus)

**FINAL STATUS: `hmeas_spec` is eliminated** (commit "Eliminate hmeas_spec from
the Quench capstones"). The four `queryEfficient_nn_of_*` capstones now assume
only the trivially-true `Measurable Dhat` (sample dissimilarity matrix measurable
in the sample). The chain below relocated `h_conc_meas` to `hmeas_spec`; the
final step removed `hmeas_spec` too: the matrix capstone
`exists_isometry_configError_le_of_entrywise_close` is *deterministic*, so the
CMDS-entrywise event is directly Borel
(`SpectralMeasurability.measurableSet_entrywiseClose_event`) and deterministically
contained in `{AlignExists}` (`AlignedPipeline.alignExists_of_entrywiseClose`) —
so it serves as the measurable HP sub-event with no eigenvector measurability.
Helm's `halign` is no longer assumed either: `alignmentConsistency_of_aligned_spectral`
now *derives* it from estimation closeness + an **explicit** latent
eigenvalue-stability assumption (`α ≤ λ_d`, = Acharyya 2025 Assumption 2), which
the formalization surfaced as required-by-the-spectral-estimator but absent from
Helm's stated A1–A4 (Helm's prose avoids it via the eigengap-free raw-stress
consistency it cites — a documented theory/practice MDS-variant discrepancy; the
raw-stress "Form B" bridge is future work).  See
`docs/planning/hmeas-spec-discharge.md`. History of the relocation below.

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

**UPDATE 2026-06-12 (Opus): obstruction BROKEN — see
`docs/planning/hmeas-spec-discharge.md`.**  The literal `hmeas_spec` is indeed
not provable (reason below), but the honest discharge is now tractable and its
load-bearing lemma is proved and committed: `ForMathlib.measurable_cfc_comp`
(`ForMathlib/MeasureTheory/CfcMeasurable.lean`) proves `ω ↦ cfc f (B ω)` is
measurable for a fixed continuous `f` from `Measurable B` alone.  The consuming
events depend on the embedding only through its Gram = rank-`d` spectral
truncation = `cfc h B̂`, which that lemma makes measurable from `Measurable Dhat`.
Route (a) below was the right idea; the cfc formulation is what avoids building
eigenprojector continuity from scratch.  Remaining = integration only (steps A–D
in the discharge doc).  Original assessment kept for context.

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
3. ~~F4 (projector-form Davis–Kahan)~~ — ✅ DONE 2026-06-12 (Opus).  Only the
   SHARP constant + RCLike projector generalization remain, both optional.
4. ~~F5 residual (`hmeas_spec`)~~ — ✅ ELIMINATED 2026-06-12 (Fable + Opus).
   Replaced by the trivially-true `Measurable Dhat`; no honest seam remains in
   the DkpsQuench chain.
5. **F3** — skip; raise the Berge maximum theorem upstream instead.

Everything else (the whole spectral-perturbation toolkit, probability lemmas,
norm comparisons, approximate-minimizer stability) is DONE and needs no Fable.
