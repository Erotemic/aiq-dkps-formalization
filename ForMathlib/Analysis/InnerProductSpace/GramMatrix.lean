/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); refactored into a
span-to-span core plus corollaries by Claude Opus 4.8 (claude-opus-4-8[1m]).
The span-to-span proof was then "folded" (rewrite-friendly local lemmas +
`simp`/`simpa` for bookkeeping) and, following further review by @wwylele,
turned into a `def` (`linearIsometryEquivSpanOfInnerEq`, built via
`LinearEquiv.isometryOfInner` on the quotient/range equivalence) with an
`@[simp]` apply lemma, keeping `exists_…` as a thin corollary.  Applied here by
Claude Opus 4.8 to stay in sync with the Mathlib fork.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Gram matrix rigidity (exact Procrustes)

Two families of vectors in an inner product space over `𝕜 = ℝ, ℂ` with equal
pairwise inner products are related by a linear isometry.  In finite dimension
this upgrades to a single linear isometry *equivalence* of the ambient space, and
the hypothesis can be packaged as equality of `Matrix.gram` matrices.

This is the rigidity statement underlying *Procrustes alignment* in classical
multidimensional scaling: a configuration recovered from a Gram matrix is
determined exactly up to an orthogonal (unitary) transformation.

## Main results

* `ForMathlib.inner_linearCombination_linearCombination`: the inner product of two
  finite linear combinations of a vector family, expanded over the family's Gram
  data.  (Reusable; independent of the rigidity statement.)
* `ForMathlib.exists_linearIsometryEquiv_span_map_eq_of_inner_eq`: the
  **span-to-span core** — for families `φ : ι → E`, `ψ : ι → F` in two (possibly
  different) inner product spaces over `𝕜`, equal pairwise inner products give a
  linear isometry *equivalence* `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending
  each `φ i` to `ψ i` (the two spans are isometrically isomorphic).  No finiteness
  is needed.
* `ForMathlib.exists_linearIsometry_span_map_eq_of_inner_eq`: the underlying
  `LinearIsometry` `span 𝕜 (range φ) →ₗᵢ span 𝕜 (range ψ)` (compatibility corollary).
* `ForMathlib.exists_linearIsometry_map_eq_of_inner_eq`: the span-to-ambient
  corollary — the isometry composed with the inclusion `span 𝕜 (range ψ) ↪ F`.
* `ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq`: in finite dimension, the
  core extends to a linear isometry *equivalence* of the ambient space.
* `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`: the same
  statement packaged as a characterization of `Matrix.gram` equality.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University
  Press, 2013 — Gram matrices and factorization up to a unitary factor.
* P. H. Schönemann, *A generalized solution of the orthogonal Procrustes
  problem*, Psychometrika **31** (1966), 1–10 — the (least-squares) Procrustes
  problem, of which this is the exact, zero-residual case.
* T.-Y. Chien and S. Waldron, *A Characterization of Projective Unitary
  Equivalence of Finite Frames and Applications*, SIAM J. Discrete Math. **30**
  (2016), no. 2, 976–994, arXiv:1312.5393 — the frame-theoretic form: finite
  frames are unitarily equivalent iff their Gram matrices coincide.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/--
The inner product of two finite linear combinations `Σ aᵢ • v i` and `Σ bⱼ • v j`
of a vector family `v`, expanded over the family's Gram data
`⟪v i, v j⟫`:
`⟪Σ aᵢ • vᵢ, Σ bⱼ • vⱼ⟫ = Σᵢ Σⱼ conj aᵢ * bⱼ * ⟪vᵢ, vⱼ⟫`.
-/
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]

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
      = LinearMap.ker (Finsupp.linearCombination 𝕜 ψ) := by
  ext c
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    ← inner_self_eq_zero (𝕜 := 𝕜) (x := Finsupp.linearCombination 𝕜 φ c),
    inner_linearCombination_eq_of_inner_eq h c c, inner_self_eq_zero]

/-- **Gram rigidity, span-to-span core.** The (unique) linear isometry equivalence
`span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each `φ i` to `ψ i`, when the families `φ`, `ψ`
(in possibly different inner product spaces over `𝕜`) have equal pairwise inner products.  It is
the map of linear combinations `∑ cᵢ • φ i ↦ ∑ cᵢ • ψ i` (well defined since the two
linear-combination maps have equal kernels), transported to the spans and upgraded to an isometry
via `LinearEquiv.isometryOfInner`.  No finiteness is required, and the ambient spaces need not
coincide.

It is the unique such isometry: a linear isometry equivalence of the spans sending `φ i ↦ ψ i` is
determined on the spanning family `φ` (`LinearMap.eqOn_span`). -/
noncomputable def linearIsometryEquivSpanOfInnerEq :
    (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)).symm.trans
    ((((Finsupp.linearCombination 𝕜 φ).quotKerEquivRange.symm.trans
        ((Submodule.quotEquivOfEq _ _ (ker_linearCombination_eq_of_inner_eq h)).trans
          (Finsupp.linearCombination 𝕜 ψ).quotKerEquivRange)).isometryOfInner fun x y => by
        obtain ⟨_, c, rfl⟩ := x
        obtain ⟨_, c', rfl⟩ := y
        simp only [LinearEquiv.trans_apply, LinearMap.quotKerEquivRange_symm_apply_image,
          Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
          Submodule.coe_inner]
        exact (inner_linearCombination_eq_of_inner_eq h c c').symm).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)))

@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply (i : ι) :
    (linearIsometryEquivSpanOfInnerEq h ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  simp only [linearIsometryEquivSpanOfInnerEq, LinearIsometryEquiv.trans_apply]
  rw [show ((LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜 (v := φ))).symm
        ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ :
        LinearMap.range (Finsupp.linearCombination 𝕜 φ))
      = ⟨Finsupp.linearCombination 𝕜 φ (Finsupp.single i 1), LinearMap.mem_range_self _ _⟩
      from Subtype.ext (by simp)]
  simp only [LinearEquiv.coe_isometryOfInner, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivRange_apply_mk, LinearIsometryEquiv.coe_ofEq_apply]
  simp [Finsupp.linearCombination_single]

/-- **Gram rigidity, span-to-span core (existence form).** If a family `φ : ι → E` and a family
`ψ : ι → F` in two inner product spaces over `𝕜` have equal pairwise inner products, then the map
`φ i ↦ ψ i` extends to a linear isometry equivalence of the span of the `φ i` onto the span of the
`ψ i`.  See `linearIsometryEquivSpanOfInnerEq` for the construction.  No finiteness is required,
and the ambient spaces need not coincide. -/
theorem exists_linearIsometryEquiv_span_map_eq_of_inner_eq :
    ∃ L :
      (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i :=
  ⟨linearIsometryEquivSpanOfInnerEq h, linearIsometryEquivSpanOfInnerEq_apply h⟩

end

/--
**Gram rigidity, span-to-span isometry.** The `LinearIsometry` underlying the
span-to-span equivalence `exists_linearIsometryEquiv_span_map_eq_of_inner_eq`
(kept as a compatibility corollary): equal pairwise inner products give a linear
isometry `span 𝕜 (range φ) →ₗᵢ span 𝕜 (range ψ)` sending each `φ i` to `ψ i`.
-/
theorem exists_linearIsometry_span_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_span_map_eq_of_inner_eq h
  exact ⟨L.toLinearIsometry, hL⟩

/--
**Gram rigidity, span-to-ambient form.** The span-to-span isometry
`exists_linearIsometry_span_map_eq_of_inner_eq` composed with the inclusion
`span 𝕜 (range ψ) ↪ F`: equal pairwise inner products give a linear isometry from
`span 𝕜 (range φ)` into `F` sending each `φ i` to `ψ i`.
-/
theorem exists_linearIsometry_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] F,
      ∀ i, L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ = ψ i := by
  obtain ⟨L, hL⟩ := exists_linearIsometry_span_map_eq_of_inner_eq h
  exact ⟨(Submodule.span 𝕜 (Set.range ψ)).subtypeₗᵢ.comp L, hL⟩

variable [FiniteDimensional 𝕜 E]

/--
**Gram rigidity.** If two families `φ ψ : ι → E` of vectors in a
finite-dimensional inner product space have equal pairwise inner products, then
there is a linear isometry equivalence `W` of `E` with `W (φ i) = ψ i` for every
`i`.

This extends the span-level core `exists_linearIsometry_map_eq_of_inner_eq` to a
self-equivalence: the isometry on `span 𝕜 (range φ)` extends to `E` by
`LinearIsometry.extend`, and finite dimensionality upgrades the resulting
injective self-map to an equivalence.
-/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  obtain ⟨L, hL⟩ := exists_linearIsometry_map_eq_of_inner_eq h
  -- Extend `L` to a self-isometry of `E`, then bundle it as an equivalence.
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun i => ?_⟩
  rw [LinearIsometry.coe_toLinearIsometryEquiv,
    show φ i = ((⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ :
      Submodule.span 𝕜 (Set.range φ)) : E) from rfl, L.extend_apply, hL i]

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  constructor
  · intro hg
    refine exists_linearIsometryEquiv_map_eq_of_inner_eq fun i j => ?_
    simpa only [gram_apply] using congrFun₂ hg i j
  · rintro ⟨W, hW⟩
    ext i j
    simp [gram_apply, ← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix

end ForMathlib
