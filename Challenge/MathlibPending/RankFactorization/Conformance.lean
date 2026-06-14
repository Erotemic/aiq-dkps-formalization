/-
# Matrix rank factorization (pending: relate to abstract rank_le_iff_exists_linearMap)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib.Matrix

-- Binder names match the ForMathlib source (`{𝕜 m n}`); the comparator exports
-- de Bruijn terms so names do not affect matching, but keeping them identical
-- avoids any ambiguity.
variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  sorry

end ForMathlib.Matrix
