/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Gram matrix rigidity (exact Procrustes)

Two families of vectors in a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ` have equal Gram matrices if and only if they are related by a single
linear isometry equivalence of the ambient space.

This is the rigidity statement underlying *Procrustes alignment* in classical
multidimensional scaling: a configuration recovered from a Gram matrix is
determined exactly up to an orthogonal (unitary) transformation.

## Main results

* `ForMathlib.exists_linearIsometryEquiv_of_inner_eq`: equal pairwise inner
  products yield a linear isometry equivalence mapping one family to the other.
* `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv`: the same
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

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/--
**Gram rigidity.** If two families `φ ψ : ι → E` of vectors in a
finite-dimensional inner product space have equal pairwise inner products,
i.e. `⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫` for all `i, j`, then there is a linear isometry
equivalence `W` of `E` with `W (φ i) = ψ i` for every `i`.

The index type `ι` is arbitrary (no finiteness needed).  The proof builds the
map `φ i ↦ ψ i` on the span of the `φ i` (the range of the linear-combination
map of `φ`), shows it is an isometry there using the equal inner products,
extends it to all of `E` by `LinearIsometry.extend`, and upgrades the result to
an equivalence by finite dimensionality.
-/
theorem exists_linearIsometryEquiv_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  classical
  -- Linear-combination maps of the two families.
  set Tφ : (ι →₀ 𝕜) →ₗ[𝕜] E := Finsupp.linearCombination 𝕜 φ with hTφ
  set Tψ : (ι →₀ 𝕜) →ₗ[𝕜] E := Finsupp.linearCombination 𝕜 ψ with hTψ
  -- The two maps preserve the same inner products.
  have key : ∀ c c' : ι →₀ 𝕜, ⟪Tφ c, Tφ c'⟫_𝕜 = ⟪Tψ c, Tψ c'⟫_𝕜 := by
    intro c c'
    have expand : ∀ (χ : ι → E) (a b : ι →₀ 𝕜),
        ⟪Finsupp.linearCombination 𝕜 χ a, Finsupp.linearCombination 𝕜 χ b⟫_𝕜
          = a.sum fun i s => b.sum fun j t =>
              starRingEnd 𝕜 s * t * ⟪χ i, χ j⟫_𝕜 := by
      intro χ a b
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        Finsupp.sum_inner]
      refine Finsupp.sum_congr ?_
      intro i _
      rw [Finsupp.inner_sum]
      refine Finsupp.sum_congr ?_
      intro j _
      rw [inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [hTφ, hTψ, expand φ c c', expand ψ c c']
    refine Finsupp.sum_congr ?_
    intro i _
    refine Finsupp.sum_congr ?_
    intro j _
    rw [h i j]
  -- Equal norms.
  have norm_eq : ∀ c : ι →₀ 𝕜, ‖Tψ c‖ = ‖Tφ c‖ := by
    intro c
    have hsq : ‖Tψ c‖ ^ 2 = ‖Tφ c‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) (Tψ c),
        ← inner_self_eq_norm_sq (𝕜 := 𝕜) (Tφ c), key c c]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  -- ker Tφ ≤ ker Tψ.
  have hker : LinearMap.ker Tφ ≤ LinearMap.ker Tψ := by
    intro c hc
    have hφ0 : Tφ c = 0 := by simpa [LinearMap.mem_ker] using hc
    have : ‖Tψ c‖ = 0 := by rw [norm_eq c, hφ0, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp this
  -- Factor Tψ through (ι →₀ 𝕜) ⧸ ker Tφ and through range Tφ.
  set f₀ : ((ι →₀ 𝕜) ⧸ LinearMap.ker Tφ) →ₗ[𝕜] E :=
    (LinearMap.ker Tφ).liftQ Tψ hker with hf₀
  set f : (LinearMap.range Tφ) →ₗ[𝕜] E :=
    f₀.comp (Tφ.quotKerEquivRange.symm.toLinearMap) with hf
  have hf_apply : ∀ c : ι →₀ 𝕜,
      f ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ = Tψ c := by
    intro c
    rw [hf]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Tφ.quotKerEquivRange_symm_apply_image c (LinearMap.mem_range_self Tφ c)]
    rw [hf₀]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- f is a linear isometry on range Tφ.
  have hf_isom : ∀ s : (LinearMap.range Tφ), ‖f s‖ = ‖s‖ := by
    intro s
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp s.2
    have hs : s = ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ := Subtype.ext hc.symm
    rw [hs, hf_apply c]
    rw [Submodule.coe_norm ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩, norm_eq c]
  set L : (LinearMap.range Tφ) →ₗᵢ[𝕜] E := ⟨f, hf_isom⟩ with hL
  -- Extend to a self-isometry of E.
  set W₀ : E →ₗᵢ[𝕜] E := L.extend with hW₀
  -- Upgrade to an equivalence (finite dimension ⇒ injective ⇒ surjective).
  have hW₀_surj : Function.Surjective W₀ := by
    have hinj : Function.Injective W₀.toLinearMap := W₀.injective
    exact LinearMap.injective_iff_surjective.mp hinj
  set W : E ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.ofSurjective W₀ hW₀_surj with hW
  refine ⟨W, ?_⟩
  intro i
  have hφi : φ i = Tφ (Finsupp.single i 1) := by
    rw [hTφ, Finsupp.linearCombination_single, one_smul]
  have hψi : ψ i = Tψ (Finsupp.single i 1) := by
    rw [hTψ, Finsupp.linearCombination_single, one_smul]
  have hmem : φ i ∈ LinearMap.range Tφ := by
    rw [hφi]; exact LinearMap.mem_range_self Tφ _
  have hWeq : W (φ i) = W₀ (φ i) := by
    rw [hW, LinearIsometryEquiv.coe_ofSurjective]
  rw [hWeq, hW₀]
  have : (⟨φ i, hmem⟩ : LinearMap.range Tφ)
      = ⟨Tφ (Finsupp.single i 1), LinearMap.mem_range_self Tφ _⟩ := by
    apply Subtype.ext; exact hφi
  calc
    L.extend (φ i) = L.extend ((⟨φ i, hmem⟩ : LinearMap.range Tφ) : E) := rfl
    _ = L (⟨φ i, hmem⟩ : LinearMap.range Tφ) := L.extend_apply _
    _ = f (⟨φ i, hmem⟩ : LinearMap.range Tφ) := rfl
    _ = f ⟨Tφ (Finsupp.single i 1), LinearMap.mem_range_self Tφ _⟩ := by rw [this]
    _ = Tψ (Finsupp.single i 1) := hf_apply _
    _ = ψ i := hψi.symm

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the
other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  constructor
  · intro h
    refine exists_linearIsometryEquiv_of_inner_eq fun i j => ?_
    rw [← gram_apply (𝕜 := 𝕜) φ i j, ← gram_apply (𝕜 := 𝕜) ψ i j, h]
  · rintro ⟨W, hW⟩
    ext i j
    simp only [gram_apply]
    rw [← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix

end ForMathlib
