/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); refactored into a
span-to-span core plus corollaries by Claude Opus 4.8 (claude-opus-4-8[1m]);
folded and turned into a `def` with an `@[simp]` apply lemma following review
by @wwylele on mathlib4 PR #40567.  After the PR was closed, restructured for
elegance by Claude Fable 5 (claude-fable-5[1m]): the quotient plumbing is now a
standalone *isometric first isomorphism theorem* (`LinearMap.rangeEquivOfInnerEq`)
about an arbitrary pair of linear maps, whose `@[simp]` apply lemma carries an
arbitrary membership proof so that every downstream proof is a short `simp`;
the span, ambient, and `gram` statements are thin corollaries.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import ForMathlib.Analysis.InnerProductSpace.Basic
import ForMathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Gram matrix rigidity

Two families of vectors in inner product spaces over `𝕜 = ℝ, ℂ` with equal
pairwise inner products are related by a linear isometry.  In finite dimension
this upgrades to a linear isometry *equivalence* of the ambient space, and the
hypothesis can be packaged as equality of `Matrix.gram` matrices.

The engine is a general fact about a pair of linear maps, an isometric
refinement of the first isomorphism theorem:

* `LinearMap.ker_eq_ker_of_inner_eq`: linear maps `S`, `T` (out of a common
  module, into two inner product spaces) with equal pullback inner products
  `⟪S x, S y⟫ = ⟪T x, T y⟫` have equal kernels, since `S x = 0` iff
  `⟪S x, S x⟫ = 0`.
* `LinearMap.rangeEquivOfInnerEq`: consequently `S x ↦ T x` descends to a
  linear isometry equivalence `range S ≃ₗᵢ range T`: both ranges are canonically
  isomorphic to the coimage `M ⧸ ker S = M ⧸ ker T` by the first isomorphism
  theorem, and the hypothesis says exactly that the two induced inner products
  on the coimage agree.

Everything else is specialization.  Applying it to the two linear-combination
maps `Finsupp.linearCombination 𝕜 φ` and `Finsupp.linearCombination 𝕜 ψ` of
families `φ`, `ψ` with equal pairwise inner products (their pullback inner
products then agree by sesquilinearity, `inner_linearCombination_eq_of_inner_eq`)
turns "equal Gram data" into an isometry of spans:

* `linearIsometryEquivSpanOfInnerEq`: a linear isometry equivalence
  `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each `φ i` to `ψ i`.
  No finiteness is assumed, and the ambient spaces may differ.
* `exists_linearIsometryEquiv_map_eq_of_inner_eq`: in a finite-dimensional
  ambient space this extends (by `LinearIsometry.extend`) to a linear isometry
  equivalence of the whole space.
* `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`: the
  same statement packaged as a characterization of `Matrix.gram` equality.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University
  Press, 2013 — Gram matrices and factorization up to a unitary factor.
* T.-Y. Chien and S. Waldron, *A Characterization of Projective Unitary
  Equivalence of Finite Frames and Applications*, SIAM J. Discrete Math. **30**
  (2016), no. 2, 976–994, arXiv:1312.5393 — the frame-theoretic form: finite
  frames are unitarily equivalent iff their Gram matrices coincide.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### The isometric first isomorphism theorem -/

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module 𝕜 M]
variable (S : M →ₗ[𝕜] E) (T : M →ₗ[𝕜] F) (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜)
include h

/-- Linear maps with equal pullback inner products have equal kernels:
`S x = 0` iff `⟪S x, S x⟫ = 0` iff `⟪T x, T x⟫ = 0` iff `T x = 0`. -/
theorem ker_eq_ker_of_inner_eq : LinearMap.ker S = LinearMap.ker T := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← inner_self_eq_zero (𝕜 := 𝕜), h x x,
    inner_self_eq_zero]

/-- **Isometric first isomorphism theorem.**  Two linear maps `S`, `T` out of a common
module with equal pullback inner products, `⟪S x, S y⟫ = ⟪T x, T y⟫`, have canonically
isometric ranges, by `S x ↦ T x`.  This is well defined because both ranges are
first-isomorphism-theorem images of the common coimage `M ⧸ ker S = M ⧸ ker T`
(`ker_eq_ker_of_inner_eq`), and isometric because the hypothesis is precisely the
statement that the two inner products induced on the coimage agree. -/
noncomputable def rangeEquivOfInnerEq : LinearMap.range S ≃ₗᵢ[𝕜] LinearMap.range T :=
  (S.quotKerEquivRange.symm.trans <| (Submodule.quotEquivOfEq _ _
      (ker_eq_ker_of_inner_eq S T h)).trans T.quotKerEquivRange).isometryOfInner fun x y => by
    obtain ⟨-, x, rfl⟩ := x
    obtain ⟨-, y, rfl⟩ := y
    simp [h x y]

@[simp]
theorem rangeEquivOfInnerEq_apply (x : M) (hx : S x ∈ LinearMap.range S) :
    (rangeEquivOfInnerEq S T h ⟨S x, hx⟩ : F) = T x := by
  simp [rangeEquivOfInnerEq]

end LinearMap

/-! ### Families with equal pairwise inner products -/

section
variable {φ : ι → E} {ψ : ι → F} (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜)
include h

/-- For families `φ`, `ψ` with equal pairwise inner products, the maps of linear combinations
`∑ cᵢ • φ i` and `∑ cᵢ • ψ i` have equal pairwise inner products. -/
theorem inner_linearCombination_eq_of_inner_eq (c c' : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 φ c, Finsupp.linearCombination 𝕜 φ c'⟫_𝕜
      = ⟪Finsupp.linearCombination 𝕜 ψ c, Finsupp.linearCombination 𝕜 ψ c'⟫_𝕜 := by
  simp [inner_linearCombination_linearCombination, h]

/-- Families with equal pairwise inner products have linear-combination maps with equal kernels:
`∑ cᵢ • φ i = 0 ↔ ∑ cᵢ • ψ i = 0`. -/
theorem ker_linearCombination_eq_of_inner_eq :
    LinearMap.ker (Finsupp.linearCombination 𝕜 φ)
      = LinearMap.ker (Finsupp.linearCombination 𝕜 ψ) :=
  LinearMap.ker_eq_ker_of_inner_eq _ _ (inner_linearCombination_eq_of_inner_eq h)

variable (φ ψ)

/-- A linear isometry equivalence `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each
`φ i` to `ψ i`, when the families `φ`, `ψ` (in possibly different inner product spaces over `𝕜`)
have equal pairwise inner products.  It is the isometric first isomorphism theorem
`LinearMap.rangeEquivOfInnerEq` applied to the two linear-combination maps, whose ranges
are the spans.  No finiteness is required, and the ambient spaces need not coincide.

Such an isometry is determined on the spanning family `φ` (`LinearMap.eqOn_span`), hence unique;
this uniqueness is not separately formalized here. -/
noncomputable def linearIsometryEquivSpanOfInnerEq :
    (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜).symm).trans
    ((LinearMap.rangeEquivOfInnerEq _ _ (inner_linearCombination_eq_of_inner_eq h)).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)))

/-- `linearIsometryEquivSpanOfInnerEq` computes on linear combinations:
it sends `∑ cᵢ • φ i` to `∑ cᵢ • ψ i`. -/
@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply_linearCombination (c : ι →₀ 𝕜)
    (hc : Finsupp.linearCombination 𝕜 φ c ∈ Submodule.span 𝕜 (Set.range φ)) :
    (linearIsometryEquivSpanOfInnerEq φ ψ h ⟨Finsupp.linearCombination 𝕜 φ c, hc⟩ : F)
      = Finsupp.linearCombination 𝕜 ψ c := by
  simp [linearIsometryEquivSpanOfInnerEq]

/-- `linearIsometryEquivSpanOfInnerEq` sends each generator `φ i` to `ψ i`: the
`c = Finsupp.single i 1` case of
`linearIsometryEquivSpanOfInnerEq_apply_linearCombination`. -/
@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply (i : ι)
    (hi : φ i ∈ Submodule.span 𝕜 (Set.range φ)) :
    (linearIsometryEquivSpanOfInnerEq φ ψ h ⟨φ i, hi⟩ : F) = ψ i := by
  simpa using linearIsometryEquivSpanOfInnerEq_apply_linearCombination φ ψ h
    (Finsupp.single i 1) (by simpa using Submodule.subset_span (Set.mem_range_self (f := φ) i))

end

/-- If two families `φ ψ : ι → E` in a finite-dimensional inner product space have equal
pairwise inner products, then there is a linear isometry equivalence `W` of `E` with
`W (φ i) = ψ i` for every `i`.  The span-to-span equivalence
`linearIsometryEquivSpanOfInnerEq` is extended to `E` by `LinearIsometry.extend` and
bundled as an equivalence by finite dimensionality. -/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq [FiniteDimensional 𝕜 E] {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  let L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] E :=
    (Submodule.span 𝕜 (Set.range ψ)).subtypeₗᵢ.comp
      (linearIsometryEquivSpanOfInnerEq φ ψ h).toLinearIsometry
  exact ⟨L.extend.toLinearIsometryEquiv rfl, fun i => by
    simpa [L] using L.extend_apply ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩⟩

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq [FiniteDimensional 𝕜 E] {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  constructor
  · intro hg
    exact exists_linearIsometryEquiv_map_eq_of_inner_eq fun i j => by
      simpa using congrFun₂ hg i j
  · rintro ⟨W, hW⟩
    ext i j
    simp [gram_apply, ← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix

end ForMathlib
