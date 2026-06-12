# Discharging `hmeas_spec` — the cfc route (warm start)

Written 2026-06-12 by Claude Opus 4.8. **Supersedes the F5 "likely not provable"
assessment in `docs/planning/for-fable.md`.** The core measurability obstruction is now broken
and the load-bearing lemma is proved and committed.

## TL;DR

`hmeas_spec` ([`DkpsQuench/AcharyyaBridge.lean`](../../DkpsQuench/AcharyyaBridge.lean), assumed in the four
`queryEfficient_nn_of_*` capstones) asserts measurability of the **raw spectral
embedding** `ω ↦ spectralConfig (toEuclideanLin B̂(ω)) …` — an *eigenvector*-valued
map. As literally stated it is **not provable**: `spectralConfig` is built from
`Matrix.IsHermitian.eigenvectorBasis`, a `Classical.choice` eigenbasis that is
discontinuous (and not provably measurable) at eigenvalue crossings.

But the events that consume it (`AlignExists`, hence the aligned-`ConfigError`
event) depend on the embedding **only through its Gram matrix**, and the Gram
matrix is the rank-`d` *spectral truncation* of `B̂`, which equals `cfc h B̂` for a
fixed continuous `h` — and **that is measurable**, with no eigenbasis, by the now-committed

> `ForMathlib.measurable_cfc_comp` (`ForMathlib/MeasureTheory/CfcMeasurable.lean`):
> for fixed continuous `f`, `ω ↦ cfc f (B ω)` is measurable when `B` is measurable
> and self-adjoint-valued in a C*-algebra.

So the honest discharge replaces the **unprovable** `hmeas_spec` with the
**trivially-true** `Measurable (fun ω => Dhat u ω)` (the sample dissimilarity
matrix is a measurable function of the sample — it is built from sample means).

## What is DONE (committed, building green)

- `ForMathlib.measurable_cfc_comp` and the supporting countable-cover lemma
  `ForMathlib.measurable_of_iUnion_restrict`. This is the part the prior
  assessment deemed research-grade / likely impossible.

## What REMAINS (the integration — a Fable-sized task)

Four steps, in dependency order. None require new Mathlib theory; all are
"ordinary" (if laborious) Lean.

### (A) Gram = cfc identity, on the gap-positive event

Choose `h : ℝ → ℝ` continuous with `h(x) = x` for `x ≥ α/2` and `h(x) = 0` for
`x ≤ α/4` (linear ramp between; `α` is the eigenvalue floor from Assumption 2).
Prove, on the event `G(ω) := {ω | the d-th sorted eigenvalue of B̂(ω) ≥ α/2 and the
(d+1)-th ≤ α/4}`:

    ⟪spectralConfig (toEuclideanLin B̂ω) … i, spectralConfig … j⟫  =  (cfc h B̂ω) i j

i.e. `GramMatrix (spectralConfig …) = cfc h B̂ω` as `n×n` matrices.
- LHS `= ∑_{k<d} λ_k (u_k)_i (u_k)_j` (expand `spectralConfig`, `√λ_k·√λ_k = λ_k`).
- RHS `= ∑_k h(λ_k) (u_k)_i (u_k)_j` via `Matrix.IsHermitian.cfc_eq` /
  `cfc f A = U diag(f∘λ) Uᴴ`.
- On `G`, `h(λ_k) = λ_k` for `k<d` and `h(λ_k) = 0` for `k≥d`, so the sums agree.
Both `spectralConfig` and the eigendata use the SAME `eigenvectorBasis`, so the
`u_k` match definitionally — no canonicality issue *as long as we stay on `G`*.

### (B) `AlignExists` depends only on the Gram (S-invariance)

`AlignExists ω = ∃ W ∈ S, ∑ᵢ ‖W(spec ω i) − ψ i‖ ≤ c` with `S` = the
inner-product-preserving maps (a group). Replacing `spec ω` by `R ∘ spec ω`
(`R ∈ S`) leaves the event unchanged (`W ↦ W R⁻¹`), and two configs share an
`S`-orbit iff they have equal Gram (Procrustes —
[`Acharyya2025/Procrustes.lean`](../../Acharyya2025/Procrustes.lean) `exists_linearIsometryEquiv_*` gives this).
Conclude `AlignExists ω = P(GramMatrix (spec ω))` for a predicate `P` on `n×n`
matrices, where `P M := ∃ z, GramMatrix z = M ∧ ∃ W ∈ S, ∑ ‖W (z i) − ψ i‖ ≤ c`.

### (C) Re-prove `measurableSet_setOf_alignExists` from `Measurable Dhat`

Replace the `hmeas` hypothesis of
[`Acharyya2025/AlignedPipeline.lean`](../../Acharyya2025/AlignedPipeline.lean) `measurableSet_setOf_alignExists`
by `hDhat : Measurable (fun ω => Dhat u ω)`. Then on `G`:
`{ω ∈ G | AlignExists ω} = {ω ∈ G | P (cfc h B̂ω)}` by (A)+(B); and
`ω ↦ cfc h B̂ω` is measurable by `measurable_cfc_comp` (with `B̂ = toEuclideanLin ∘
disMatToMatrix ∘ classicalMDSMatrix ∘ Dhat`, measurable from `hDhat` since each
stage is continuous/linear). Measurability of `{M | P M}` follows from the
existing `ForMathlib.measurableSet_exists_mem_le` applied in the Gram variable
(the same compact-`S` argument already used here). Instantiate the C*-algebra `A`
as `Matrix (Fin n) (Fin n) ℝ` under `open scoped Matrix.Norms.L2Operator`
(provides `CStarAlgebra`, hence `IsometricContinuousFunctionalCalculus`,
`ContinuousStar`, `CompleteSpace`, `NormOneClass` for `n ≥ 1`) and `borelize`.

### (D) Thread `G` as the measurable sub-event and re-wire the four capstones

`G` is itself a high-probability event (the concentration hypothesis already in
the bridge forces the spectral gap — Weyl on `‖B̂ − B‖` small + `B`'s floor `α`,
cap `Λ`, and rank `d`). Feed `E := G ∩ {AlignExists}` into the existing
`*_of_subevent` machinery (`highProb_*_nn_of_subevent`), exactly as the current
bridge does — but now `E` is measurable *unconditionally* (from `Measurable Dhat`)
rather than via the assumed `hmeas_spec`. Update the four
`queryEfficient_nn_of_{aligned_spectral,response_mean,second_moment}` (and the
shared `quench_part2_from_aligned_configError_hp`) to take `hDhat` in place of
`hmeas_spec`.

## Risk notes

- The only place canonicality could bite is OFF `G` (eigenvalue crossings); the
  gap-positive restriction in (A)/(D) avoids it entirely — and `G` is where the
  whole concentration argument already lives, so no probability mass is lost.
- The C*-algebra instantiation for matrices needs the `Matrix.Norms.L2Operator`
  scope; check the `BorelSpace`/Pi-`MeasurableSpace` compatibility there
  (`borelize` on the matrix type) — this is the most likely instance-wrangling
  point, mirror `Acharyya2025/OperatorBridge.lean`'s operator-world choices if
  the matrix world fights back (you may prefer `A := EuclideanSpace ℝ (Fin n) →L[ℝ]
  EuclideanSpace ℝ (Fin n)` and carry `toEuclideanLin`).
