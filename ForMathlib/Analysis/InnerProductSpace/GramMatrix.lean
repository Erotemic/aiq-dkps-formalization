/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); refactored into a
span-to-span core plus corollaries by Claude Opus 4.8 (claude-opus-4-8[1m]).
The span-to-span proof was then "folded" (rewrite-friendly local lemmas +
`simp`/`simpa` for bookkeeping) following review suggestions by @wwylele on the
Mathlib PR; applied here by Claude Opus 4.8 to stay in sync with the fork.
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

/--
**Gram rigidity, span-to-span core.** If a family `φ : ι → E` in one inner product
space and a family `ψ : ι → F` in another (over the same `𝕜`) have equal pairwise
inner products `⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫`, then the map `φ i ↦ ψ i` extends to a
linear isometry *equivalence* `L` of the span of the `φ i` onto the span of the
`ψ i`, with `L (φ i) = ψ i` for every `i`.

The codomain is the full submodule `span 𝕜 (range ψ)`: the map is onto it (its
image is the span of the `ψ i`), so the two spans are isometrically isomorphic.

No finiteness of `ι`, `E`, or `F` is required, and the two ambient spaces need not
coincide.  The map is `φ i ↦ ψ i` on `span 𝕜 (range φ)` (the range of `φ`'s
linear-combination map); equality of inner products makes it well defined
(`ker Tφ ≤ ker Tψ`) and norm preserving, it lands in `span 𝕜 (range ψ)` (the range
of `ψ`'s linear-combination map), and it is surjective onto that span.
-/
theorem exists_linearIsometryEquiv_span_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L :
      (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  -- Linear-combination maps of the two families.
  set Tφ : (ι →₀ 𝕜) →ₗ[𝕜] E := Finsupp.linearCombination 𝕜 φ with hTφ
  set Tψ : (ι →₀ 𝕜) →ₗ[𝕜] F := Finsupp.linearCombination 𝕜 ψ with hTψ
  -- The two maps preserve the same inner products on all linear combinations.
  have key (c c' : ι →₀ 𝕜) : ⟪Tφ c, Tφ c'⟫_𝕜 = ⟪Tψ c, Tψ c'⟫_𝕜 := by
    simp [hTφ, hTψ, inner_linearCombination_linearCombination, h]
  -- Equal norms, hence `ker Tφ ≤ ker Tψ`.
  have norm_eq (c : ι →₀ 𝕜) : ‖Tψ c‖ = ‖Tφ c‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_re_inner (𝕜 := 𝕜),
      norm_sq_eq_re_inner (𝕜 := 𝕜), key]
  have hker : LinearMap.ker Tφ ≤ LinearMap.ker Tψ := by
    intro c hc
    rw [LinearMap.mem_ker, ← norm_eq_zero] at ⊢ hc
    rw [norm_eq, hc]
  -- Factor `Tψ` through `(ι →₀ 𝕜) ⧸ ker Tφ ≃ range Tφ` to get `f : range Tφ → F`.
  set f₀ : ((ι →₀ 𝕜) ⧸ LinearMap.ker Tφ) →ₗ[𝕜] F :=
    (LinearMap.ker Tφ).liftQ Tψ hker with hf₀
  set f : (LinearMap.range Tφ) →ₗ[𝕜] F :=
    f₀.comp (Tφ.quotKerEquivRange.symm.toLinearMap) with hf
  have hf_apply (c : ι →₀ 𝕜) : f ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ = Tψ c := by
    simp [hf, hf₀]
  -- `f` is norm preserving and lands in `range Tψ`.
  have hf_isom (s : LinearMap.range Tφ) : ‖f s‖ = ‖s‖ := by
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp s.2
    have hs : s = ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ := Subtype.ext hc.symm
    simp [hs, hf_apply, norm_eq]
  have hf_mem (s : LinearMap.range Tφ) : f s ∈ LinearMap.range Tψ := by
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp s.2
    have hs : s = ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ := Subtype.ext hc.symm
    simp [hs, hf_apply]
  -- Corestrict `f` to `range Tψ` as a linear isometry.
  set f' : (LinearMap.range Tφ) →ₗ[𝕜] (LinearMap.range Tψ) :=
    LinearMap.codRestrict (LinearMap.range Tψ) f hf_mem with hf'
  have hf'_isom (s : LinearMap.range Tφ) : ‖f' s‖ = ‖s‖ := by
    simpa [Submodule.coe_norm (f' s), hf', LinearMap.codRestrict_apply] using hf_isom s
  set Lr : (LinearMap.range Tφ) →ₗᵢ[𝕜] (LinearMap.range Tψ) :=
    ⟨f', hf'_isom⟩ with hLr
  -- `Lr` is surjective: `t = Tψ c` is the image of `Tφ c`.
  have hsurj : Function.Surjective Lr := by
    intro t
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp t.2
    refine ⟨⟨Tφ c, LinearMap.mem_range_self Tφ c⟩, Subtype.ext ?_⟩
    simpa [hLr, hf', hf_apply] using hc
  -- Transport both sides along `range T = span (range ·)`.
  have hrangeφ : LinearMap.range Tφ = Submodule.span 𝕜 (Set.range φ) := by
    simpa [hTφ] using Finsupp.range_linearCombination 𝕜
  have hrangeψ : LinearMap.range Tψ = Submodule.span 𝕜 (Set.range ψ) := by
    simpa [hTψ] using Finsupp.range_linearCombination 𝕜
  refine ⟨((LinearIsometryEquiv.ofEq _ _ hrangeφ).symm.trans
      (LinearIsometryEquiv.ofSurjective Lr hsurj)).trans
      (LinearIsometryEquiv.ofEq _ _ hrangeψ), fun i => ?_⟩
  -- Carrier bookkeeping: `(L ⟨φ i, _⟩ : F) = f ⟨φ i, _⟩ = ψ i`.
  have hmemRφ : φ i ∈ LinearMap.range Tφ := by
    simpa [hrangeφ] using Submodule.mem_span_of_mem (Set.mem_range_self i)
  have htransφ : (LinearIsometryEquiv.ofEq _ _ hrangeφ).symm
      ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ = ⟨φ i, hmemRφ⟩ := Subtype.ext rfl
  have hfφ : f ⟨φ i, hmemRφ⟩ = ψ i := by
    have hsubtype : (⟨φ i, hmemRφ⟩ : LinearMap.range Tφ)
        = ⟨Tφ (Finsupp.single i 1), LinearMap.mem_range_self Tφ _⟩ :=
      Subtype.ext (by simp [hTφ])
    simp [hsubtype, hf_apply, hTψ]
  simp only [LinearIsometryEquiv.trans_apply]
  rw [LinearIsometryEquiv.coe_ofEq_apply, htransφ, LinearIsometryEquiv.coe_ofSurjective]
  simp [hLr, hf', hfφ]

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
    rw [← gram_apply (𝕜 := 𝕜) φ i j, ← gram_apply (𝕜 := 𝕜) ψ i j, hg]
  · rintro ⟨W, hW⟩
    ext i j
    simp only [gram_apply]
    rw [← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix

end ForMathlib
