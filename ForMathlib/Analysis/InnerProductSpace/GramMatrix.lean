/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); refactored into a span-level
core plus corollaries by Claude Opus 4.8 (claude-opus-4-8[1m]).
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
* `ForMathlib.exists_linearIsometry_map_eq_of_inner_eq`: the **span-level core** — for
  families `φ : ι → E`, `ψ : ι → F` in two (possibly different) inner product
  spaces over `𝕜`, equal pairwise inner products give a linear isometry from
  `span 𝕜 (range φ)` into `F` sending each `φ i` to `ψ i`.  No finiteness is
  needed.
* `ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq`: in finite dimension, the
  core extends to a linear isometry *equivalence* of the ambient space.
* `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`: the same
  statement packaged as a characterization of `Matrix.gram` equality.

## References

* R. Sibson, *Studies in the robustness of multidimensional scaling:
  Perturbational analysis of classical scaling*, J. Roy. Statist. Soc. Ser. B
  **41** (1979), 217–229.
* I. Borg and P. J. F. Groenen, *Modern Multidimensional Scaling*, 2nd ed.,
  Springer, 2005, Ch. 12.
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
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]

/--
**Gram rigidity, span-level core.** If a family `φ : ι → E` in one inner product
space and a family `ψ : ι → F` in another (over the same `𝕜`) have equal pairwise
inner products `⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫`, then there is a linear isometry `L` from
the span of the `φ i` into `F` with `L (φ i) = ψ i` for every `i`.

No finiteness of `ι`, `E`, or `F` is required, and the two ambient spaces need not
coincide.  The map is built as `φ i ↦ ψ i` on `span 𝕜 (range φ)` (the range of
`φ`'s linear-combination map); equality of inner products makes it well defined
(`ker Tφ ≤ ker Tψ`) and norm preserving.
-/
theorem exists_linearIsometry_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] F,
      ∀ i, L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ = ψ i := by
  classical
  -- Linear-combination maps of the two families.
  set Tφ : (ι →₀ 𝕜) →ₗ[𝕜] E := Finsupp.linearCombination 𝕜 φ with hTφ
  set Tψ : (ι →₀ 𝕜) →ₗ[𝕜] F := Finsupp.linearCombination 𝕜 ψ with hTψ
  -- The two maps preserve the same inner products on all linear combinations.
  have key : ∀ c c' : ι →₀ 𝕜, ⟪Tφ c, Tφ c'⟫_𝕜 = ⟪Tψ c, Tψ c'⟫_𝕜 := by
    intro c c'
    rw [hTφ, hTψ, inner_linearCombination_linearCombination,
      inner_linearCombination_linearCombination]
    refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
    rw [h i j]
  -- Equal norms, hence `ker Tφ ≤ ker Tψ`.
  have norm_eq : ∀ c : ι →₀ 𝕜, ‖Tψ c‖ = ‖Tφ c‖ := by
    intro c
    have hsq : ‖Tψ c‖ ^ 2 = ‖Tφ c‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) (Tψ c),
        ← inner_self_eq_norm_sq (𝕜 := 𝕜) (Tφ c), key c c]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hker : LinearMap.ker Tφ ≤ LinearMap.ker Tψ := by
    intro c hc
    have hφ0 : Tφ c = 0 := by simpa [LinearMap.mem_ker] using hc
    have : ‖Tψ c‖ = 0 := by rw [norm_eq c, hφ0, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp this
  -- Factor `Tψ` through `(ι →₀ 𝕜) ⧸ ker Tφ ≃ range Tφ` to get `f : range Tφ → E`.
  set f₀ : ((ι →₀ 𝕜) ⧸ LinearMap.ker Tφ) →ₗ[𝕜] F :=
    (LinearMap.ker Tφ).liftQ Tψ hker with hf₀
  set f : (LinearMap.range Tφ) →ₗ[𝕜] F :=
    f₀.comp (Tφ.quotKerEquivRange.symm.toLinearMap) with hf
  have hf_apply : ∀ c : ι →₀ 𝕜,
      f ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ = Tψ c := by
    intro c
    rw [hf]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Tφ.quotKerEquivRange_symm_apply_image c (LinearMap.mem_range_self Tφ c)]
    rw [hf₀, Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- `f` is a linear isometry on `range Tφ`.
  have hf_isom : ∀ s : (LinearMap.range Tφ), ‖f s‖ = ‖s‖ := by
    intro s
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp s.2
    have hs : s = ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ := Subtype.ext hc.symm
    rw [hs, hf_apply c, Submodule.coe_norm ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩, norm_eq c]
  set Lr : (LinearMap.range Tφ) →ₗᵢ[𝕜] F := ⟨f, hf_isom⟩ with hLr
  -- Transport along `range Tφ = span 𝕜 (range φ)`.
  have hrange : LinearMap.range Tφ = Submodule.span 𝕜 (Set.range φ) := by
    rw [hTφ]; exact Finsupp.range_linearCombination 𝕜
  refine ⟨Lr.comp (LinearIsometryEquiv.ofEq _ _ hrange).symm.toLinearIsometry, fun i => ?_⟩
  -- The carrier element is unchanged by the transport, so `L (φ i) = Lr ⟨φ i, _⟩`.
  have hmemR : φ i ∈ LinearMap.range Tφ := by rw [hrange]; exact Submodule.subset_span ⟨i, rfl⟩
  have htrans : (LinearIsometryEquiv.ofEq _ _ hrange).symm
      ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ = ⟨φ i, hmemR⟩ := Subtype.ext rfl
  show Lr ((LinearIsometryEquiv.ofEq _ _ hrange).symm ⟨φ i, _⟩) = ψ i
  rw [htrans]
  show f ⟨φ i, hmemR⟩ = ψ i
  -- `φ i = Tφ (single i 1)`, so this is `hf_apply (single i 1)`.
  have hφi : φ i = Tφ (Finsupp.single i 1) := by
    rw [hTφ, Finsupp.linearCombination_single, one_smul]
  have hsubtype : (⟨φ i, hmemR⟩ : LinearMap.range Tφ)
      = ⟨Tφ (Finsupp.single i 1), LinearMap.mem_range_self Tφ _⟩ := Subtype.ext hφi
  rw [hsubtype, hf_apply, hTψ, Finsupp.linearCombination_single, one_smul]

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
  -- Extend `L` to a self-isometry of `E`, then upgrade to an equivalence.
  set W₀ : E →ₗᵢ[𝕜] E := L.extend with hW₀
  have hW₀_surj : Function.Surjective W₀ :=
    LinearMap.injective_iff_surjective.mp W₀.injective
  refine ⟨LinearIsometryEquiv.ofSurjective W₀ hW₀_surj, fun i => ?_⟩
  rw [LinearIsometryEquiv.coe_ofSurjective, hW₀]
  rw [show φ i = ((⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ :
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
