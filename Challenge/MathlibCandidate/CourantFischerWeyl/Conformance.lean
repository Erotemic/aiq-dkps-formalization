/-
# Weyl eigenvalue perturbation, via Courant-Fischer min-max (Mathlib candidate 02)

The surfaced leaf is Weyl's perturbation inequality; the discrete Courant-Fischer
min-max characterization is the proof vehicle (developed in
`ForMathlib.Analysis.InnerProductSpace.CourantFischer`), not a separately listed leaf.

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}
variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- **Weyl's inequality (operator-norm form).** The `k`-th sorted eigenvalues of two
symmetric operators differ by at most the operator norm of their difference. This is the
leaf of the Courant-Fischer + Weyl development (it is proved through the discrete
Courant-Fischer min-max characterization of the sorted eigenvalues). -/
theorem abs_eigenvalues_sub_le_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  sorry

end ForMathlib
