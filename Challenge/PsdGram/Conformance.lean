/-
# Rank-controlled PSD Gram realization challenge conformance file

This file imports only Mathlib and states the PSD/Gram-realization contribution
family. Each theorem is intentionally left as `sorry`; the filled file is
`Challenge/PsdGram/Leaderboard.lean`.
-/

import Mathlib

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

namespace ForMathlib.Matrix

open scoped BigOperators ComplexOrder
open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/--
If `B` is positive semidefinite and has rank at most `d`, then the sorted
nonnegative eigenvalues vanish from index `d` onward.
-/
theorem PosSemidef.eigenvalues₀_eq_zero_of_le {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) {d : ℕ} (hrank : B.rank ≤ d)
    (i : Fin (Fintype.card n)) (hi : d ≤ (i : ℕ)) :
    hB.isHermitian.eigenvalues₀ i = 0 := by
  sorry

end ForMathlib.Matrix

namespace ForMathlib.Matrix

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/--
Entrywise spectral expansion of a Hermitian matrix over `𝕜 = ℝ, ℂ`.
-/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  sorry

/--
A Hermitian matrix is positive semidefinite with rank at most `d` iff it is a
Gram matrix `Aᴴ * A` with `d` rows.
-/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry

end ForMathlib.Matrix
