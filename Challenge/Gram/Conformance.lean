/-
# Gram / Procrustes rigidity challenge conformance file

This file imports only Mathlib and states the headline Mathlib-facing
contribution from the AIQ DKPS formalization: the `Matrix.gram` rigidity
characterisation. It is the top-level result — the supporting lemmas it is built
from are tracked separately in the `Challenge/Inventory/GramGeometry` challenge.

The theorem is intentionally left as `sorry`. The corresponding filled file is
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
