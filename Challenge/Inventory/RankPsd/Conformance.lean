/-
# AIQ DKPS ForMathlib inventory challenge: Rank factorization and PSD Gram realization

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/Analysis/Matrix/Spectrum.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Vanishing tail of the sorted eigenvalues of a low-rank PSD matrix

For a positive semidefinite matrix of rank at most `d`, the sorted eigenvalues
`Matrix.IsHermitian.eigenvalues₀` (decreasing) vanish from index `d` on.

Mathlib's `eigenvalues₀` currently exposes little beyond `eigenvalues₀_antitone`.
The proof here is the elementary counting argument: by antitonicity and
nonnegativity (PSD), a nonzero sorted eigenvalue at an index `≥ d` would force
`> d` nonzero sorted eigenvalues, but their number equals `rank ≤ d` (the
sorted and unsorted eigenvalues differ by the index equivalence used to *define*
`eigenvalues`, so `rank_eq_card_non_zero_eigs` transports).

## Main result

* `ForMathlib.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le`
-/

namespace ForMathlib.Matrix

open scoped BigOperators ComplexOrder
open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/--
**Vanishing tail of the sorted eigenvalues.** If `B` is positive semidefinite
with `B.rank ≤ d`, then its sorted (decreasing) eigenvalues
`hB.isHermitian.eigenvalues₀` are zero at every index `≥ d`.
-/
theorem PosSemidef.eigenvalues₀_eq_zero_of_le {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) {d : ℕ} (hrank : B.rank ≤ d)
    (i : Fin (Fintype.card n)) (hi : d ≤ (i : ℕ)) :
    hB.isHermitian.eigenvalues₀ i = 0 := by
  sorry
end ForMathlib.Matrix
/-!
## Source: `ForMathlib/LinearAlgebra/Matrix/PosDef.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Rank-constrained positive-semidefinite factorization

A real positive-semidefinite matrix `B` factors as `B = Aᴴ * A` with `A` having
at most `d` rows **iff** its rank is at most `d`. The square-factor version
(`B = Aᴴ * A` with `A` square, e.g. the PSD square root) is already available;
this is the dimension-controlled refinement, equivalently the statement that a
PSD matrix of rank `≤ d` is the Gram matrix of `n` points in `ℝ^d` — the
classical multidimensional-scaling embedding step.

The forward (hard) direction is the spectral construction: `B = Σ_k λ_k uₖ uₖᵀ`
with `λ_k ≥ 0` and exactly `rank B` nonzero eigenvalues; scaling each nonzero
eigenvector by `√λ_k` and packing the `rank B ≤ d` resulting coordinates into
`d` rows yields `A`. The reverse direction is `posSemidef_conjTranspose_mul_self`
together with `rank_conjTranspose_mul_self` and `rank_le_height`.

## Main results

* `ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`:
  the rank-`≤ d` PSD factorization characterization, over `RCLike 𝕜`.

## References

* Cox & Cox, *Multidimensional Scaling*, 2nd ed., §2.2–2.3 (classical scaling).
* Horn & Johnson, *Matrix Analysis*, 2nd ed. (spectral theorem and PSD Gram
  factorizations).
-/

namespace ForMathlib.Matrix

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/--
Entrywise spectral expansion of a Hermitian matrix over `𝕜 = ℝ, ℂ`:
`B i j = Σ_k (eigenvalues k) * U i k * conj (U j k)`, where `U` is the
eigenvector unitary.  This is the entrywise form of
`Matrix.IsHermitian.spectral_theorem`.
-/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  sorry
theorem PosSemidef.exists_eq_conjTranspose_mul_self
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) :
    ∃ A : Matrix (Fin n) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry
theorem PosSemidef.exists_conjTranspose_mul_self_of_rank_le
    {d : ℕ} {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef)
    (hrank : B.rank ≤ d) :
    ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry
end ForMathlib.Matrix
/-!
## Source: `ForMathlib/LinearAlgebra/Matrix/RankFactorization.lean`
-/
/-! # Rank factorization

Every matrix over a field factors as `M = L * R` with inner dimension exactly
`M.rank`, hence through `Fin r` for any `r ≥ M.rank`; conversely any product
through `Fin r` has rank at most `r`.  Mathlib has the rank API but no
factorization realizing the rank as an inner dimension. -/

namespace ForMathlib.Matrix

variable {𝕜' m' n' : Type*} [Field 𝕜'] [Fintype n'] [DecidableEq n']

theorem exists_eq_mul_rank (M : Matrix m' n' 𝕜') :
    ∃ (L : Matrix m' (Fin M.rank) 𝕜') (R : Matrix (Fin M.rank) n' 𝕜'), M = L * R := by
  sorry
theorem exists_eq_mul_of_rank_le (M : Matrix m' n' 𝕜') {r : ℕ} (h : M.rank ≤ r) :
    ∃ (L : Matrix m' (Fin r) 𝕜') (R : Matrix (Fin r) n' 𝕜'), M = L * R := by
  sorry
theorem rank_le_iff_exists_eq_mul (M : Matrix m' n' 𝕜') (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m' (Fin r) 𝕜') (R : Matrix (Fin r) n' 𝕜'), M = L * R := by
  sorry
end ForMathlib.Matrix
