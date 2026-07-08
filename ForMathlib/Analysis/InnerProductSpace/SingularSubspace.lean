/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SingularSubspace.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W4 of
`dev/davis-kahan-gap-closure-plan.md`.

Groundwork for the Yu–Wang–Samworth singular-vector extension: perturbing the
Gram operator `A⋆A` by `Â⋆Â − A⋆A`, controlled by `Â − A`.  Includes the operator
adjoint norm bound `‖A⋆‖ = ‖A‖` in elementwise form.

Plan step W0.1(d) added by Claude Opus 4.8 (claude-opus-4-8[1m]): the
singular-value symmetry `σ(A⋆) = σ(A)` for a square operator, proved through the
eigenvalue invariance of a symmetric operator under unitary conjugation
(`eigenvalues_conj_unitary`, a Courant–Fischer consequence) applied to the polar
identity `A A⋆ = U (A⋆A) U⁻¹` with `U = polarUnitary A`.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.YuWangSamworth
import ForMathlib.Analysis.InnerProductSpace.PolarDecomposition

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
* `ForMathlib.eigenvalues_conj_unitary`: the sorted eigenvalues of a symmetric
  operator are invariant under unitary conjugation `S ↦ U S U⁻¹`.
* `ForMathlib.singularValues_adjoint`: the singular values of a square operator
  and its adjoint coincide, `σ(A⋆) = σ(A)`.

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

/-- **Trace of the modulus = sum of singular values.** For an endomorphism
`A : E →ₗ[𝕜] E`, `∑ₖ re⟪|A| bₖ, bₖ⟫ = ∑ᵢ σᵢ(A)` in any orthonormal basis `b`.
The modulus `|A| = √(A⋆A)` is diagonal in the `A⋆A`-eigenbasis with entries
`√λᵢ(A⋆A) = σᵢ(A)`, and the trace is basis-independent. -/
theorem sum_re_inner_abs_self_eq_sum_singularValues (A : E →ₗ[𝕜] E)
    {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, RCLike.re ⟪abs A (b k), b k⟫_𝕜 = ∑ i : Fin n, A.singularValues (i : ℕ) := by
  subst hn
  have hP := LinearMap.isPositive_adjoint_comp_self A
  have hsym : (abs A).IsSymmetric := (isPositive_abs A).isSymmetric
  -- Basis independence: the trace of `|A|` is the same in any basis.
  have key : ∀ b' : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∑ k, RCLike.re ⟪abs A (b' k), b' k⟫_𝕜
        = ∑ i : Fin (finrank 𝕜 E), hsym.eigenvalues rfl i :=
    fun b' => sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues hsym rfl b'
  rw [key b, ← key (hP.isSymmetric.eigenvectorBasis rfl)]
  refine Finset.sum_congr rfl fun k _ => ?_
  set w := hP.isSymmetric.eigenvectorBasis rfl with hw
  rw [show abs A (w k)
        = (Real.sqrt (hP.isSymmetric.eigenvalues rfl k) : 𝕜) • w k from
      hP.sqrt_apply_eigenvectorBasis k,
    inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
    w.orthonormal.norm_eq_one k, one_pow, mul_one]
  exact (A.singularValues_fin rfl k).symm

/-- **Contraction ⇒ singular values ≤ 1.** If `A` is a contraction
(`‖A x‖ ≤ ‖x‖`), then every singular value satisfies `σᵢ(A) ≤ 1`.  Each eigenvalue
`λᵢ(A⋆A) = re⟪A wᵢ, A wᵢ⟫ = ‖A wᵢ‖² ≤ 1` (`wᵢ` the unit eigenvector), and
`σᵢ = √λᵢ`. -/
theorem singularValues_le_one_of_contraction {A : E →ₗ[𝕜] F}
    (h : ∀ x, ‖A x‖ ≤ ‖x‖) {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    A.singularValues (i : ℕ) ≤ 1 := by
  have hSsym := A.isSymmetric_adjoint_comp_self
  have hunit : ‖hSsym.eigenvectorBasis hn i‖ = 1 :=
    (hSsym.eigenvectorBasis hn).orthonormal.norm_eq_one i
  have hquad : RCLike.re ⟪(A.adjoint ∘ₗ A) (hSsym.eigenvectorBasis hn i),
      hSsym.eigenvectorBasis hn i⟫_𝕜 = ‖A (hSsym.eigenvectorBasis hn i)‖ ^ 2 := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
  have heig : RCLike.re ⟪(A.adjoint ∘ₗ A) (hSsym.eigenvectorBasis hn i),
      hSsym.eigenvectorBasis hn i⟫_𝕜 = hSsym.eigenvalues hn i := by
    rw [hSsym.apply_eigenvectorBasis hn i, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hunit, one_pow, mul_one]
  have heval : hSsym.eigenvalues hn i ≤ 1 := by
    rw [← heig, hquad]
    have := h (hSsym.eigenvectorBasis hn i)
    rw [hunit] at this
    nlinarith [norm_nonneg (A (hSsym.eigenvectorBasis hn i))]
  rw [A.singularValues_fin hn]
  calc √(hSsym.eigenvalues hn i) ≤ √1 := Real.sqrt_le_sqrt heval
    _ = 1 := Real.sqrt_one

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

/-- **Frobenius² ≤ trace of the modulus, for a contraction.** If `A : E →ₗ[𝕜] E`
is a contraction, then `∑ₖ ‖A bₖ‖² ≤ ∑ₖ re⟪|A| bₖ, bₖ⟫`, i.e. `∑ σᵢ² ≤ ∑ σᵢ`
(each `σᵢ ∈ [0, 1]`).  This is the core inequality of the aligned-basis
(orthogonal-Procrustes) argument: `∑‖wⱼ − uⱼ‖² = 2d − 2∑σ ≤ 2d − 2∑σ² = 2·sinΘ²`. -/
theorem sum_sq_norm_le_sum_re_inner_abs_of_contraction {A : E →ₗ[𝕜] E}
    (h : ∀ x, ‖A x‖ ≤ ‖x‖) {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, ‖A (b k)‖ ^ 2 ≤ ∑ k, RCLike.re ⟪abs A (b k), b k⟫_𝕜 := by
  rw [← sum_sq_singularValues A hn b, sum_re_inner_abs_self_eq_sum_singularValues A hn b]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := singularValues_le_one_of_contraction h hn i
  have h0 := A.singularValues_nonneg (i : ℕ)
  nlinarith

/-- **Unitary invariance of the Frobenius sum.** Pre-composing with a unitary `U`
does not change `∑ₖ ‖A (b k)‖²`: `∑ₖ ‖A (U bₖ)‖² = ∑ₖ ‖A bₖ‖²`.  Both equal the
sum of squared singular values (`sum_sq_singularValues`), since `k ↦ U bₖ` is
another orthonormal basis. -/
theorem sum_sq_norm_apply_unitary_comp (A : E →ₗ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E)
    {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, ‖A (U (b k))‖ ^ 2 = ∑ k, ‖A (b k)‖ ^ 2 := by
  have h1 := sum_sq_singularValues A hn (b.map U)
  have h2 := sum_sq_singularValues A hn b
  simp only [OrthonormalBasis.map_apply] at h1
  rw [← h2, ← h1]

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

/-! ### Singular values of the adjoint (square case)

`σ(A⋆) = σ(A)` for a square operator `A : E →ₗ[𝕜] E`.  The Gram operators
`A⋆A` and `A A⋆` are unitarily conjugate (`A A⋆ = U (A⋆A) U⁻¹` with
`U = polarUnitary A`), so they have equal sorted eigenvalues, hence `A` and
`A⋆` have equal singular values.  This is the symmetry `cosPrincipalAngles`
needs (plan step W0.1(d)). -/

section Adjoint

variable {n : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The conjugate `U S U⁻¹` of a symmetric operator by a unitary is symmetric. -/
theorem isSymmetric_conj_unitary {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (U : E ≃ₗᵢ[𝕜] E) :
    (U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  calc ⟪U (S (U.symm x)), y⟫_𝕜
      = ⟪U (S (U.symm x)), U (U.symm y)⟫_𝕜 := by rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪S (U.symm x), U.symm y⟫_𝕜 := U.inner_map_map _ _
    _ = ⟪U.symm x, S (U.symm y)⟫_𝕜 := hS _ _
    _ = ⟪U (U.symm x), U (S (U.symm y))⟫_𝕜 := (U.inner_map_map _ _).symm
    _ = ⟪x, U (S (U.symm y))⟫_𝕜 := by rw [LinearIsometryEquiv.apply_symm_apply]

/-- Sorted eigenvalues are congruent along an operator equality (the eigenvalue
enumeration depends only on the operator, not on the symmetry proof). -/
theorem eigenvalues_congr {S₁ S₂ : E →ₗ[𝕜] E} (h : S₁ = S₂)
    (hS₁ : S₁.IsSymmetric) (hS₂ : S₂.IsSymmetric) (hn : finrank 𝕜 E = n) :
    hS₁.eigenvalues hn = hS₂.eigenvalues hn := by
  subst h; rfl

/-- One direction of unitary-conjugation eigenvalue invariance:
`λₖ(S) ≤ λₖ(U S U⁻¹)`.  Courant–Fischer — a witness `(k+1)`-subspace for `S`
maps under `U` to one for the conjugate, on which the same Rayleigh values
recur. -/
private theorem eigenvalues_conj_unitary_le {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (U : E ≃ₗᵢ[𝕜] E) (k : Fin n) :
    hS.eigenvalues hn k ≤ (isSymmetric_conj_unitary hS U).eigenvalues hn k := by
  obtain ⟨V, hVdim, hVlow⟩ := forall_unit_vector_eigenvalue_le_re_inner hS hn k
  have hmapfin : finrank 𝕜 (V.map U.toLinearMap) = (k : ℕ) + 1 := by
    rw [show (U.toLinearMap : E →ₗ[𝕜] E) = (U.toLinearEquiv : E →ₗ[𝕜] E) from rfl,
      LinearEquiv.finrank_map_eq, hVdim]
  obtain ⟨y, hyV', hny, hup⟩ := exists_unit_vector_re_inner_le_eigenvalue
    (isSymmetric_conj_unitary hS U) hn k (V.map U.toLinearMap) hmapfin
  obtain ⟨x, hxV, hUxy⟩ := Submodule.mem_map.mp hyV'
  simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hUxy
  have hnx : ‖x‖ = 1 := by rw [← hny, ← hUxy, U.norm_map]
  have hyx : U.symm y = x := by rw [← hUxy, U.symm_apply_apply]
  have hray : RCLike.re ⟪(U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap) y, y⟫_𝕜
      = RCLike.re ⟪S x, x⟫_𝕜 := by
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
    rw [hyx, ← hUxy, U.inner_map_map]
  calc hS.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
    _ = RCLike.re ⟪(U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap) y, y⟫_𝕜 := hray.symm
    _ ≤ (isSymmetric_conj_unitary hS U).eigenvalues hn k := hup

/-- **Unitary conjugation preserves sorted eigenvalues.** For a symmetric
operator `S` and a unitary `U`, `S` and `U S U⁻¹` have the same sorted
eigenvalues.  (Courant–Fischer: the Rayleigh minimax is invariant under the
subspace bijection `V ↦ U V`.) -/
theorem eigenvalues_conj_unitary {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (U : E ≃ₗᵢ[𝕜] E) :
    (isSymmetric_conj_unitary hS U).eigenvalues hn = hS.eigenvalues hn := by
  funext k
  refine le_antisymm ?_ (eigenvalues_conj_unitary_le hS hn U k)
  -- Reverse direction: `S` is the conjugate of `U S U⁻¹` by `U⁻¹`.
  have hback : U.symm.toLinearMap ∘ₗ (U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap)
      ∘ₗ U.symm.symm.toLinearMap = S := by
    ext v
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have hcong := eigenvalues_congr hback
    (isSymmetric_conj_unitary (isSymmetric_conj_unitary hS U) U.symm) hS hn
  have := eigenvalues_conj_unitary_le (isSymmetric_conj_unitary hS U) hn U.symm k
  rwa [hcong] at this

/-- The Gram operators `A A⋆` and `A⋆A` are unitarily conjugate:
`A A⋆ = U (A⋆A) U⁻¹` with `U = polarUnitary A`.  From `A = U |A|`,
`A⋆ = |A| U⁻¹`, so `A A⋆ = U |A|² U⁻¹ = U (A⋆A) U⁻¹`. -/
theorem comp_adjoint_eq_conj_adjoint_comp (A : E →ₗ[𝕜] E) :
    A ∘ₗ A.adjoint = (polarUnitary A).toLinearMap ∘ₗ (A.adjoint ∘ₗ A)
      ∘ₗ (polarUnitary A).symm.toLinearMap := by
  set U := polarUnitary A with hU
  have hpolar : A = U.toLinearMap ∘ₗ abs A := polar_decomposition_unitary A
  have hadj : A.adjoint = abs A ∘ₗ U.symm.toLinearMap := by
    conv_lhs => rw [hpolar]
    rw [LinearMap.adjoint_comp, (isPositive_abs A).adjoint_eq, U.adjoint_toLinearMap_eq_symm]
  calc A ∘ₗ A.adjoint
      = (U.toLinearMap ∘ₗ abs A) ∘ₗ (abs A ∘ₗ U.symm.toLinearMap) := by rw [← hpolar, ← hadj]
    _ = U.toLinearMap ∘ₗ (abs A ∘ₗ abs A) ∘ₗ U.symm.toLinearMap := by
        ext v; simp only [LinearMap.comp_apply]
    _ = U.toLinearMap ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ U.symm.toLinearMap := by rw [abs_mul_self A]

/-- The Gram operators of `A` and `A⋆` have equal sorted eigenvalues. -/
theorem eigenvalues_gram_adjoint (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n) :
    A.adjoint.isSymmetric_adjoint_comp_self.eigenvalues hn
      = A.isSymmetric_adjoint_comp_self.eigenvalues hn := by
  have hAA : A.adjoint.adjoint ∘ₗ A.adjoint = (polarUnitary A).toLinearMap
      ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ (polarUnitary A).symm.toLinearMap := by
    rw [LinearMap.adjoint_adjoint]; exact comp_adjoint_eq_conj_adjoint_comp A
  have hcong := eigenvalues_congr hAA A.adjoint.isSymmetric_adjoint_comp_self
    (isSymmetric_conj_unitary A.isSymmetric_adjoint_comp_self (polarUnitary A)) hn
  rw [hcong, eigenvalues_conj_unitary A.isSymmetric_adjoint_comp_self hn (polarUnitary A)]

/-- **Singular values of the adjoint (square case).** For `A : E →ₗ[𝕜] E`,
`σ(A⋆) = σ(A)`: both `A⋆A` and `A A⋆` have the same nonzero spectrum.  Absent
from the pinned Mathlib; the symmetry underlying `cosPrincipalAngles`. -/
theorem singularValues_adjoint (A : E →ₗ[𝕜] E) :
    A.adjoint.singularValues = A.singularValues := by
  obtain ⟨n, hn⟩ : ∃ n, finrank 𝕜 E = n := ⟨_, rfl⟩
  have heig := eigenvalues_gram_adjoint A hn
  ext i
  rcases lt_or_ge i n with hi | hi
  · rw [A.adjoint.singularValues_of_lt hn hi, A.singularValues_of_lt hn hi, heig]
  · rw [A.adjoint.singularValues_of_finrank_le (by rw [hn]; exact hi),
      A.singularValues_of_finrank_le (by rw [hn]; exact hi)]

end Adjoint

end ForMathlib
