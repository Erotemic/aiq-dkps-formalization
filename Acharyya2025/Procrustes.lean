/-
# Procrustes rigidity (exact Gram case)

Two configurations of vectors with identical Gram matrices (all pairwise inner
products equal) are related by a single linear isometry of the ambient space.

This is the deterministic, exact-data core underlying *Procrustes alignment* in
classical multidimensional scaling (CMDS): a configuration recovered from a
Gram matrix is determined only up to an orthogonal transformation, so any two
configurations realizing the same Gram matrix are orthogonally congruent.  In
the finite-sample CMDS perturbation theorems this rigidity is what makes the
"up to `W ∈ O(d)`" alignment in the conclusion *statable*: it is the exact
limit of the approximate alignment.

References:
* T. F. Cox and M. A. A. Cox, *Multidimensional Scaling*, 2nd ed.,
  Chapman & Hall/CRC, 2001, §2.2 (classical scaling and the role of the Gram
  matrix `B`).
* I. Borg and P. J. F. Groenen, *Modern Multidimensional Scaling*, 2nd ed.,
  Springer, 2005, Ch. 12 (Procrustes problems).
* R. Sibson, "Studies in the robustness of multidimensional scaling:
  Perturbational analysis of classical scaling", *J. Roy. Statist. Soc. Ser. B*
  **41** (1979), 217–229.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Acharyya2024.Common

open scoped RealInnerProductSpace BigOperators

namespace Acharyya2025.Procrustes

/--
**Procrustes rigidity (abstract form).**

If two families `φ ψ : ι → E` of vectors in a finite-dimensional real inner
product space have equal Gram matrices, i.e. `⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫` for all
`i, j`, then there is a linear isometry equivalence `W` of `E` with
`W (φ i) = ψ i` for every `i`.

The proof builds the linear map `φ i ↦ ψ i` on `span {φ i}` (the range of the
linear-combination map of `φ`), shows it is an isometry there using the equal
Gram matrices, extends it to all of `E` via `LinearIsometry.extend`, and
upgrades the resulting self-isometry to an equivalence by finite dimensionality.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem exists_linearIsometryEquiv_of_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} (φ ψ : ι → E)
    (h : ∀ i j, ⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ i, W (φ i) = ψ i := by
  classical
  -- Linear-combination maps of the two families.
  set Tφ : (ι →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ φ with hTφ
  set Tψ : (ι →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ ψ with hTψ
  -- Step 2: the two maps preserve the same inner products.
  have key : ∀ c c' : ι →₀ ℝ, ⟪Tφ c, Tφ c'⟫ = ⟪Tψ c, Tψ c'⟫ := by
    intro c c'
    have expand : ∀ (χ : ι → E) (a b : ι →₀ ℝ),
        ⟪Finsupp.linearCombination ℝ χ a, Finsupp.linearCombination ℝ χ b⟫
          = a.sum fun i s => b.sum fun j t => (s * t) * ⟪χ i, χ j⟫ := by
      intro χ a b
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        Finsupp.sum_inner]
      refine Finsupp.sum_congr ?_
      intro i _
      rw [Finsupp.inner_sum]
      refine Finsupp.sum_congr ?_
      intro j _
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
    rw [hTφ, hTψ, expand φ c c', expand ψ c c']
    refine Finsupp.sum_congr ?_
    intro i _
    refine Finsupp.sum_congr ?_
    intro j _
    rw [h i j]
  -- Equal norms.
  have norm_eq : ∀ c : ι →₀ ℝ, ‖Tψ c‖ = ‖Tφ c‖ := by
    intro c
    have hsq : ‖Tψ c‖ ^ 2 = ‖Tφ c‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, key c c]
    nlinarith [norm_nonneg (Tψ c), norm_nonneg (Tφ c), hsq]
  -- Step 3: ker Tφ ≤ ker Tψ.
  have hker : LinearMap.ker Tφ ≤ LinearMap.ker Tψ := by
    intro c hc
    have hφ0 : Tφ c = 0 := by simpa [LinearMap.mem_ker] using hc
    have : ‖Tψ c‖ = 0 := by rw [norm_eq c, hφ0, norm_zero]
    simpa [LinearMap.mem_ker] using (norm_eq_zero.mp this)
  -- Step 4: factor Tψ through (ι →₀ ℝ) ⧸ ker Tφ and through range Tφ.
  -- f₀ : ((ι →₀ ℝ) ⧸ ker Tφ) →ₗ[ℝ] E.
  set f₀ : ((ι →₀ ℝ) ⧸ LinearMap.ker Tφ) →ₗ[ℝ] E :=
    (LinearMap.ker Tφ).liftQ Tψ hker with hf₀
  -- f : range Tφ →ₗ[ℝ] E, with f ⟨Tφ c, _⟩ = Tψ c.
  set f : (LinearMap.range Tφ) →ₗ[ℝ] E :=
    f₀.comp (Tφ.quotKerEquivRange.symm.toLinearMap) with hf
  have hf_apply : ∀ c : ι →₀ ℝ,
      f ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ = Tψ c := by
    intro c
    rw [hf]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Tφ.quotKerEquivRange_symm_apply_image c (LinearMap.mem_range_self Tφ c)]
    rw [hf₀]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- Step 5: f is a linear isometry on range Tφ.
  have hf_isom : ∀ s : (LinearMap.range Tφ), ‖f s‖ = ‖s‖ := by
    intro s
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp s.2
    have hs : s = ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩ := Subtype.ext hc.symm
    rw [hs, hf_apply c]
    rw [Submodule.coe_norm ⟨Tφ c, LinearMap.mem_range_self Tφ c⟩, norm_eq c]
  set L : (LinearMap.range Tφ) →ₗᵢ[ℝ] E := ⟨f, hf_isom⟩ with hL
  -- Step 6: extend to a self-isometry of E.
  set W₀ : E →ₗᵢ[ℝ] E := L.extend with hW₀
  -- Step 7: upgrade to an equivalence (finite dimension ⇒ injective ⇒ surjective).
  have hW₀_surj : Function.Surjective W₀ := by
    have hinj : Function.Injective W₀.toLinearMap := W₀.injective
    exact LinearMap.injective_iff_surjective.mp hinj
  set W : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ofSurjective W₀ hW₀_surj with hW
  refine ⟨W, ?_⟩
  -- Step 8: W (φ i) = ψ i.
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

/--
**Procrustes rigidity for DKPS configurations.**

Specialization of `exists_linearIsometryEquiv_of_inner_eq` to the DKPS
configuration type `Acharyya2024.Config n d = Fin n → EuclideanSpace ℝ (Fin d)`,
with the Gram condition phrased entrywise as `∑ k, φ i k * φ j k`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem exists_linearIsometryEquiv_of_gram_eq
    {n d : Nat} (φ ψ : Acharyya2024.Config n d)
    (h : ∀ i j, ∑ k : Fin d, φ i k * φ j k = ∑ k : Fin d, ψ i k * ψ j k) :
    ∃ W : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ i, W (φ i) = ψ i := by
  apply exists_linearIsometryEquiv_of_inner_eq φ ψ
  intro i j
  -- Over ℝ, ⟪x, y⟫ on EuclideanSpace is ∑ k, x k * y k (conj is identity).
  rw [show (⟪φ i, φ j⟫ : ℝ) = ∑ k : Fin d, φ i k * φ j k by
        simp [PiLp.inner_apply, mul_comm],
      show (⟪ψ i, ψ j⟫ : ℝ) = ∑ k : Fin d, ψ i k * ψ j k by
        simp [PiLp.inner_apply, mul_comm]]
  exact h i j

end Acharyya2025.Procrustes
