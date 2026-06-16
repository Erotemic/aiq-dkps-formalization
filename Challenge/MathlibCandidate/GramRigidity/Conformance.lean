/-
# Gram rigidity (Mathlib candidate 01)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

open scoped InnerProductSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Module (finrank)
open _root_.Matrix

namespace ForMathlib

open scoped InnerProductSpace

-- The unused `F` (with its instances) mirrors the ForMathlib source's
-- `variable {𝕜 E F ι}` so the exported universe parameters match the solution
-- (the comparator compares universe signatures without alpha-normalizing).
variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

end Matrix
end ForMathlib
