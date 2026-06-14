/-
# Rank-controlled PSD Gram realization (pending: only the rank-control is novel)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib.Matrix

open scoped BigOperators ComplexOrder
open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Vanishing tail of the sorted eigenvalues** of a PSD matrix of rank `≤ d`. -/
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

/-- **Rank-controlled PSD Gram realization.** -/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry

end ForMathlib.Matrix
