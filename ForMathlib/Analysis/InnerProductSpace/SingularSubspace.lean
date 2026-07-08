/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SingularSubspace.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W4 of
`dev/davis-kahan-gap-closure-plan.md`.

Groundwork for the Yu–Wang–Samworth singular-vector extension: perturbing the
Gram operator `A⋆A` by `Â⋆Â − A⋆A`, controlled by `Â − A`.  Includes the operator
adjoint norm bound `‖A⋆‖ = ‖A‖` in elementwise form.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.YuWangSamworth

/-! # Gram-operator perturbation

For `A, Â : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
singular subspaces are the spectral subspaces of the Gram operators `A⋆A` and
`Â⋆Â`.  The Yu–Wang–Samworth singular-vector bound applies the symmetric result
to these Gram operators, so it needs the Gram perturbation `Â⋆Â − A⋆A` bounded in
terms of `Â − A`.

## Main results

* `ForMathlib.norm_adjoint_apply_le`: the adjoint of a `c`-bounded operator is
  `c`-bounded (`‖A⋆‖ ≤ ‖A‖` in elementwise form).
* `ForMathlib.norm_gram_sub_gram_apply_le`: `‖(Â⋆Â − A⋆A) x‖ ≤ (a + â) ε ‖x‖`
  when `A, Â, Â − A` are `a`-, `â`-, `ε`-bounded, via
  `Â⋆Â − A⋆A = Â⋆(Â − A) + (Â − A)⋆A`.
* `ForMathlib.abs_sq_singularValues_sub_le`: Weyl for squared singular values,
  `|σₖ(Â)² − σₖ(A)²| ≤ (a + â) ε` — the singular-value stability underlying the
  singular-subspace bound.
* `ForMathlib.sum_sq_singularValues`: the squared Frobenius norm equals the sum
  of squared singular values, `∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²`.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), §"singular-vector extension".
-/

namespace ForMathlib

open scoped InnerProductSpace
open LinearMap
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The adjoint preserves an operator-norm bound.** If `‖A x‖ ≤ c ‖x‖` for all
`x`, then `‖A⋆ y‖ ≤ c ‖y‖` for all `y` — the elementwise form of `‖A⋆‖ = ‖A‖`.
Proof: `‖A⋆ y‖² = re⟪y, A (A⋆ y)⟫ ≤ ‖y‖ ‖A (A⋆ y)‖ ≤ c ‖y‖ ‖A⋆ y‖`. -/
theorem norm_adjoint_apply_le {A : E →ₗ[𝕜] F} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖A x‖ ≤ c * ‖x‖) (y : F) : ‖A.adjoint y‖ ≤ c * ‖y‖ := by
  have key : ‖A.adjoint y‖ ^ 2 ≤ c * ‖y‖ * ‖A.adjoint y‖ :=
    calc ‖A.adjoint y‖ ^ 2
        = RCLike.re ⟪A.adjoint y, A.adjoint y⟫_𝕜 := (inner_self_eq_norm_sq _).symm
      _ = RCLike.re ⟪y, A (A.adjoint y)⟫_𝕜 := by rw [LinearMap.adjoint_inner_left]
      _ ≤ ‖⟪y, A (A.adjoint y)⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖y‖ * ‖A (A.adjoint y)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (c * ‖A.adjoint y‖) := by gcongr; exact h _
      _ = c * ‖y‖ * ‖A.adjoint y‖ := by ring
  rcases eq_or_ne ‖A.adjoint y‖ 0 with h0 | h0
  · rw [h0]; positivity
  · have hpos : 0 < ‖A.adjoint y‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
    nlinarith [key, hpos]

/-- **Gram-operator perturbation bound.** With `A, Â, Â − A` bounded by `a, â, ε`
respectively, `‖(Â⋆Â − A⋆A) x‖ ≤ (a + â) ε ‖x‖`.  From the splitting
`Â⋆Â − A⋆A = Â⋆(Â − A) + (Â − A)⋆A`, the two pieces are bounded by `â ε` and
`ε a` (using `norm_adjoint_apply_le`). -/
theorem norm_gram_sub_gram_apply_le {A Â : E →ₗ[𝕜] F} {a â ε : ℝ}
    (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖) (x : E) :
    ‖(Â.adjoint ∘ₗ Â - A.adjoint ∘ₗ A) x‖ ≤ (a + â) * ε * ‖x‖ := by
  have hadj : (Â - A).adjoint = Â.adjoint - A.adjoint := map_sub _ _ _
  have hsplit : (Â.adjoint ∘ₗ Â - A.adjoint ∘ₗ A) x
      = Â.adjoint ((Â - A) x) + (Â - A).adjoint (A x) := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hadj]
    abel
  rw [hsplit]
  calc ‖Â.adjoint ((Â - A) x) + (Â - A).adjoint (A x)‖
      ≤ ‖Â.adjoint ((Â - A) x)‖ + ‖(Â - A).adjoint (A x)‖ := norm_add_le _ _
    _ ≤ â * ‖(Â - A) x‖ + ε * ‖A x‖ := by
        gcongr
        · exact norm_adjoint_apply_le hâ hÂ _
        · exact norm_adjoint_apply_le hε hE _
    _ ≤ â * (ε * ‖x‖) + ε * (a * ‖x‖) := by
        gcongr
        · exact hE x
        · exact hA x
    _ = (a + â) * ε * ‖x‖ := by ring

/-- **Squared Frobenius norm = sum of squared singular values.** For any
orthonormal basis `b` of `E`, `∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²`.  Via the dictionary
`σᵢ² = λᵢ(A⋆A)`, basis independence of the trace, and
`re⟪bₖ, A⋆A bₖ⟫ = ‖A bₖ‖²`. -/
theorem sum_sq_singularValues (A : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ i : Fin n, A.singularValues (i : ℕ) ^ 2 = ∑ k, ‖A (b k)‖ ^ 2 := by
  have h1 : ∑ i : Fin n, A.singularValues (i : ℕ) ^ 2
      = ∑ i, A.isSymmetric_adjoint_comp_self.eigenvalues hn i :=
    Finset.sum_congr rfl fun i _ => A.sq_singularValues_fin hn i
  rw [h1, ← sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues
    A.isSymmetric_adjoint_comp_self hn b]
  exact Finset.sum_congr rfl fun k _ => by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]

/-- **Weyl's inequality for squared singular values.** The `k`-th squared singular
values of `A` and `Â` differ by at most the Gram perturbation bound:
`|σₖ(Â)² − σₖ(A)²| ≤ (a + â) ε`.  Via the dictionary `σₖ² = λₖ(·⋆·)`
(`sq_singularValues_fin`) and Weyl's inequality on the Gram operators, fed by the
perturbation bound `norm_gram_sub_gram_apply_le`. -/
theorem abs_sq_singularValues_sub_le {A Â : E →ₗ[𝕜] F} {a â ε : ℝ}
    (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (k : Fin n) :
    |Â.singularValues k ^ 2 - A.singularValues k ^ 2| ≤ (a + â) * ε := by
  rw [Â.sq_singularValues_fin hn, A.sq_singularValues_fin hn]
  exact abs_eigenvalues_sub_le Â.isSymmetric_adjoint_comp_self A.isSymmetric_adjoint_comp_self hn
    (fun x => norm_gram_sub_gram_apply_le hâ hε hA hÂ hE x) k

/-- **Yu–Wang–Samworth singular-vector extension (operator-norm branch).** The
right singular vectors of `A, Â : E →ₗ[𝕜] F` are the eigenvectors of the Gram
operators `A⋆A, Â⋆Â`, whose eigenvalues are the squared singular values.
Applying the symmetric YWS bound (`sq_gap_mul_sum_cross_le_of_population_gap_opNorm`)
to the Gram operators — with the perturbation controlled by
`norm_gram_sub_gram_apply_le` — gives, for a squared-singular-value population gap
`Γ` separating the block `s`, `Γ² · overlap ≤ 4 · d · ((a + â) ε)²`. -/
theorem sq_gap_mul_sum_cross_singularVectors_le
    {A Â : E →ₗ[𝕜] F} {Γ a â ε : ℝ} (hΓ : 0 ≤ Γ) (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Γ ≤ |A.isSymmetric_adjoint_comp_self.eigenvalues hn j
            - A.isSymmetric_adjoint_comp_self.eigenvalues hn k|) :
    Γ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn k,
            Â.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ((a + â) * ε) ^ 2 :=
  sq_gap_mul_sum_cross_le_of_population_gap_opNorm
    A.isSymmetric_adjoint_comp_self Â.isSymmetric_adjoint_comp_self hn s hΓ hgap
    (fun x => norm_gram_sub_gram_apply_le hâ hε hA hÂ hE x)

end ForMathlib
