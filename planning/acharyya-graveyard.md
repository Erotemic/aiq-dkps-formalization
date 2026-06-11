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

- 2026-06-11 — *(none yet)*

## Open questions / watch list

- Does Mathlib have Courant–Fischer / sorted eigenvalues for
  `Matrix.IsHermitian`? (Affects WP5 cost; `eigenvalues` is basis-indexed,
  not sorted.) To investigate before committing to WP5 route.
- `MatrixOperatorNormClose` uses the **sup norm** on the output `Fin n → ℝ`
  (plain pi type) while `‖x‖` is the EuclideanSpace L² norm — an instance
  mismatch baked into the def. Works for WP1's purposes, but WP7 will want an
  honest L²→L² operator bound; may need a def change (note: changing the def
  changes what seam #9 consumers receive).
- 2024 paper convergence is *subsequence-based* (`∃ u, Subseq u`) — when wiring
  WP2 into `fixed_models_growing_queries_consistency`, the subsequence comes
  only from the Trosset–Priebe seam, not from the probability step. Keep the
  layering that way.
