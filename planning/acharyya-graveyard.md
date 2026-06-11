# Acharyya formalization graveyard

Approaches tried and abandoned, dead ends, and known-bad patterns — recorded so
neither we nor helper agents re-visit them. Add a dated entry when you kill an
idea; say *why* it died.

## Known-bad patterns (from the existing scaffold, pre-dating this effort)

- **Vacuous `Prop`-field hypothesis structures** (`ResponseRegularity`,
  `MDSStabilityAssumptions`, parts of `CMDSpectralAssumptions`): fields like
  `eigengap : Prop` constrain nothing, so theorems taking them are stated
  *stronger than the paper* and are mostly false. Do not prove around them;
  harden the structure first. (Same disease previously found in DRSB sorry'd
  lemmas — omitted `Measurable`/`Integrable`/`n ≠ 0` hypotheses.)
- **Placeholder rates `1/(u+1)`** in `HighProbAtTop` statements: makes the
  statement quantify over nothing real; downstream proofs that "consume" the
  rate prove nothing about the paper's `Poly₃((n³/r)^{1/2−δ})`.
- **`ConfigError` without alignment** in perturbation conclusions: CMDS/MDS
  output is only defined up to O(d) (2025 paper) or affine maps (2024 paper);
  unaligned conclusions are false. Any perturbation statement must carry
  `∃ W ∈ O(d)` (or an infimum over the transformation class).

## Dead ends (this effort)

- 2026-06-11 — `set S : Type := {k // ...}` in GramRealization: `set`-bound
  type variables are fvars the unifier will not unfold, so `Finset.sum_subtype`
  (and anything matching `Subtype p` syntactically) fails against `∑ k : S, _`.
  Fix: inline the subtype literally (no `set` for types). Also:
  `Finset.sum_subtype`'s function argument is applied as `f ↑a` — a non-Miller
  pattern — so HO unification cannot infer `f`; pass it explicitly.
- 2026-06-11 — `rw [← Finset.sum_map univ e f]` cannot fire against a goal of
  shape `∑ a : Fin d, g a = ∑ k : S, h k` when the RHS is not literally
  `∑ k ∈ univ, f (e k)`; rewrite the RHS into image form first
  (`Finset.sum_congr` with the evaluation lemma), then `sum_map`/`sum_subset`.
- 2026-06-11 — `Matrix.toEuclideanLin` application: WithLp is now a one-field
  structure (`toLp`), so `fun i a => ...` is NOT defeq-accepted for
  `Config n d`; wrap with `WithLp.toLp 2 (fun a => ...)`. Coordinate evaluation
  `(toEuclideanLin M x) i` is still rfl-equal to `(M.mulVec (WithLp.ofLp x)) i`
  (use `show` to switch).

- 2026-06-11 — WP7(c) trap: after Procrustes-aligning the eigenvector blocks,
  the residual `‖Λ̂^{1/2}W − WΛ^{1/2}‖` CANNOT be bounded by naive triangle
  splitting — entries `(√λ̂_k − √λ_l)W_{kl}` are large for k ≠ l without
  per-eigenvalue gaps inside the top block. Resolution: the Sylvester-style
  identity `Λ̂Q − QΛ = Ûᵀ(B̂−B)U` for the UNALIGNED overlap `Q = ÛᵀU`, then
  divide entrywise by `√λ̂_k + √λ_l ≥ √(α/2)+√α`. See plan WP7(c).
- 2026-06-11 — scoped notation: `⟪·,·⟫_ℝ` needs BOTH
  `open scoped RealInnerProductSpace` and (in this Mathlib rev) the plain
  notation came through `InnerProductSpace` scope in DavisKahan.lean; missing
  the latter produced a confusing parse error at the `⟫_ℝ` token, far from the
  actual cause.

## Open questions / watch list

- Does Mathlib have Courant–Fischer / sorted eigenvalues for
  `Matrix.IsHermitian`? (Affects WP5 cost; `eigenvalues` is basis-indexed,
  not sorted.) To investigate before committing to WP5 route.
- `MatrixOperatorNormClose` uses the **sup norm** on the output `Fin n → ℝ`
  (plain pi type) while `‖x‖` is the EuclideanSpace L² norm — an instance
  mismatch baked into the def. RESOLVED 2026-06-11: `OperatorBridge.lean` adds
  the honest `MatrixL2OperatorClose` (via `toEuclideanLin`) with
  `matrixL2OperatorClose_of_entrywise` (constant n·ε); the old predicate is
  left untouched for the legacy seam.
- 2024 paper convergence is *subsequence-based* (`∃ u, Subseq u`) — when wiring
  WP2 into `fixed_models_growing_queries_consistency`, the subsequence comes
  only from the Trosset–Priebe seam, not from the probability step. Keep the
  layering that way.
