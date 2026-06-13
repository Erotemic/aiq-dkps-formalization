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

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/--
The inner product of two finite linear combinations of a vector family, expanded
over the family's Gram data.
-/
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  sorry

/--
**Gram rigidity, span-to-span core.** If two families in possibly different inner
product spaces have equal pairwise inner products, then the map sending one
family to the other is a linear isometry *equivalence* of the first span onto the
second (the codomain is the full submodule `span 𝕜 (range ψ)`).
-/
theorem exists_linearIsometryEquiv_span_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  sorry

/--
**Gram rigidity, span-to-span isometry.** The `LinearIsometry` underlying the
span-to-span equivalence (compatibility corollary).
-/
theorem exists_linearIsometry_span_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  sorry

/--
**Gram rigidity, span-to-ambient form.** The span-to-span core composed with the
inclusion `span 𝕜 (range ψ) ↪ F`.
-/
theorem exists_linearIsometry_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] F,
      ∀ i, L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ = ψ i := by
  sorry

variable [FiniteDimensional 𝕜 E]

/--
**Gram rigidity.** If two families `φ ψ : ι → E` of vectors in a
finite-dimensional inner product space have equal pairwise inner products,
then there is a linear isometry equivalence `W` of `E` with `W (φ i) = ψ i`
for every `i`.
-/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq {φ ψ : ι → E}
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
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

end Matrix
end ForMathlib
