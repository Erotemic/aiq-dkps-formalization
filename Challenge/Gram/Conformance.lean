/-
# Gram / Procrustes rigidity challenge conformance file

This file imports only Mathlib and states the first proposed Mathlib-facing
contribution family from the AIQ DKPS formalization.

Each theorem is intentionally left as `sorry`. The corresponding filled file is
`Challenge/Gram/Leaderboard.lean`.
-/

import Mathlib

open scoped InnerProductSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Module (finrank)
open _root_.Matrix

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/--
**Gram rigidity.** If two families `φ ψ : ι → E` of vectors in a
finite-dimensional inner product space have equal pairwise inner products,
then there is a linear isometry equivalence `W` of `E` with `W (φ i) = ψ i`
for every `i`.
-/
theorem exists_linearIsometryEquiv_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

end Matrix
end ForMathlib
