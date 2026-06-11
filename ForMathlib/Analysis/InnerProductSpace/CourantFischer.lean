/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/CourantFischer.lean`
(new file).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Courant–Fischer min-max and Weyl's eigenvalue perturbation inequality

For a symmetric operator `T` on a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ`, Mathlib provides the decreasingly sorted eigenvalues
`LinearMap.IsSymmetric.eigenvalues` together with an orthonormal eigenbasis
`LinearMap.IsSymmetric.eigenvectorBasis`.  This file proves the discrete
Courant–Fischer characterization of these sorted eigenvalues and derives from
it Weyl's eigenvalue perturbation inequality
`|λₖ(T) − λₖ(S)| ≤ ε` whenever `∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`.

## Main results

* `ForMathlib.re_inner_map_self_eq_sum_eigenvalues_mul_sq`: diagonalization of
  the quadratic form, `re ⟪T x, x⟫ = ∑ i, λᵢ * ‖(b.repr x) i‖ ^ 2` in the
  eigenbasis `b` of `T`.
* `ForMathlib.exists_unit_vector_re_inner_le_eigenvalue`: Courant–Fischer,
  upper direction — every subspace of dimension `k + 1` contains a unit vector
  `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`.
* `ForMathlib.forall_unit_vector_eigenvalue_le_re_inner`: Courant–Fischer,
  lower direction — some subspace of dimension `k + 1` satisfies
  `λₖ(T) ≤ re ⟪T x, x⟫` for all unit vectors `x` in it.
* `ForMathlib.abs_eigenvalues_sub_le`: **Weyl's inequality** — the `k`-th
  sorted eigenvalues of two symmetric operators differ by at most an operator
  norm bound on their difference.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Theorem 4.2.6
  (Courant–Fischer) and Theorem 4.3.1 (Weyl).
* R. Bhatia, *Matrix Analysis*, Corollary III.2.6 (Weyl).
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-! ### Spectral subspaces

Given an orthonormal basis `b` and a predicate `p` on the index set, the
subspace spanned by the basis vectors selected by `p`.  We record its dimension
(the number of selected indices) and the key orthogonality fact: a vector in
this subspace has vanishing `b`-coordinates outside `p`. -/

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices `i`
satisfying `p i`. -/
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

/-- A spectral subspace has dimension equal to the number of selected indices. -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]

/-- A vector in a spectral subspace has zero `b`-coordinate at any index outside
the selecting predicate. -/
theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  -- `⟪b i, ·⟫` vanishes on the spanning set, hence on the whole span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi j.2
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Parseval: in an orthonormal basis the squared norms of the coordinates sum
to the squared norm.  Thin wrapper around
`OrthonormalBasis.sum_sq_norm_inner_right`. -/
private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

/-! ### The quadratic form in the eigenbasis -/

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- The quadratic form `re ⟪T x, x⟫` of a symmetric operator `T` expressed in
its eigenbasis: it is the eigenvalue-weighted sum of the squared norms of the
coordinates of `x`.  This is the diagonalization of the quadratic form.  (For
symmetric `T` the inner product `⟪T x, x⟫` is real, so no information is lost
by taking the real part.) -/
theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ⟪T x, x⟫_𝕜
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

/-! ### Discrete Courant–Fischer directional bounds -/

/-- Counting lemma: the number of indices `i : Fin n` with `k ≤ i` is `n - k`. -/
private theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  classical
  have : (Finset.univ.filter (fun i : Fin n => k ≤ i)).card
      = (Finset.Ici k).card := by
    congr 1
    ext i
    simp [Finset.mem_Ici]
  rw [this, Fin.card_Ici]

/-- Counting lemma: the number of indices `i : Fin n` with `i ≤ k` is `k + 1`. -/
private theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  classical
  have : (Finset.univ.filter (fun i : Fin n => i ≤ k)).card
      = (Finset.Iic k).card := by
    congr 1
    ext i
    simp [Finset.mem_Iic]
  rw [this, Fin.card_Iic]

/-- **Courant–Fischer, upper direction.** On any subspace `V` of dimension
`k + 1` there is a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`, where `λ` is the
decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the eigenvalues
of the symmetric operator `T`.

Proof idea: `V` must intersect the `(n - k)`-dimensional "tail" eigenspace
`span {bᵢ : k ≤ i}` nontrivially by dimension counting; on that intersection
the quadratic form is bounded above by `λₖ` since the involved eigenvalues are
all `≤ λₖ` (eigenvalues are sorted decreasingly). -/
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  classical
  set b := hT.eigenvectorBasis hn with hb
  set W := specSubspace b (fun i : Fin n => k ≤ i) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_specSubspace, card_filter_le]
  -- Dimension counting: `finrank V + finrank W > finrank E`, so `V ⊓ W ≠ ⊥`.
  have hsum : finrank 𝕜 V + finrank 𝕜 W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hle := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero] at hle
    have hsup : finrank 𝕜 (↑(V ⊔ W) : Submodule 𝕜 E) ≤ n := by
      rw [← hn]; exact Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  refine ⟨((‖z‖⁻¹ : ℝ) : 𝕜) • z, V.smul_mem _ hzV, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  -- The unit vector still lies in `W`, so its coordinates vanish for `i < k`.
  · set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
    have hxW : x ∈ W := W.smul_mem _ hzW
    have hnx : ‖x‖ = 1 := by
      rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
    rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x]
    -- Bound each surviving term by `λₖ * ‖(b.repr x) i‖ ^ 2`.
    have hbound : ∀ i ∈ Finset.univ,
        hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2 ≤ hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 := by
      intro i _
      by_cases hik : k ≤ i
      · exact mul_le_mul_of_nonneg_right
          (hT.eigenvalues_antitone hn hik) (sq_nonneg _)
      · have : b.repr x i = 0 :=
          repr_eq_zero_of_mem_specSubspace b _ hxW hik
        simp [this]
    calc ∑ i : Fin n, hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2
        ≤ ∑ i : Fin n, hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 :=
          Finset.sum_le_sum hbound
      _ = hT.eigenvalues hn k * ∑ i : Fin n, ‖b.repr x i‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [sum_sq_norm_repr_eq_sq_norm]
      _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-- **Courant–Fischer, lower direction.** There is a subspace `V` of dimension
`k + 1` on which every unit vector `x` satisfies `λₖ(T) ≤ re ⟪T x, x⟫`, where
`λ` is the decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the
eigenvalues of the symmetric operator `T`.

Witness: `V = span {bᵢ : i ≤ k}`; on it the quadratic form is bounded below by
`λₖ` since all involved eigenvalues are `≥ λₖ`. -/
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  classical
  set b := hT.eigenvectorBasis hn with hb
  refine ⟨specSubspace b (fun i : Fin n => i ≤ k), ?_, ?_⟩
  · rw [finrank_specSubspace, card_filter_ge]
  · intro x hxV hnx
    rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x]
    have hbound : ∀ i ∈ Finset.univ,
        hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 ≤ hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2 := by
      intro i _
      by_cases hik : i ≤ k
      · exact mul_le_mul_of_nonneg_right
          (hT.eigenvalues_antitone hn hik) (sq_nonneg _)
      · have : b.repr x i = 0 := by
          rw [hb]
          exact repr_eq_zero_of_mem_specSubspace b _ hxV hik
        simp [this]
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ = hT.eigenvalues hn k * ∑ i : Fin n, ‖b.repr x i‖ ^ 2 := by
          rw [sum_sq_norm_repr_eq_sq_norm]
      _ = ∑ i : Fin n, hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin n, hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2 := Finset.sum_le_sum hbound

/-! ### Weyl's inequality -/

/-- One-sided Weyl bound: `λₖ(S) − λₖ(T) ≤ ‖S − T‖op`.  This is the core
estimate; Weyl's inequality follows by symmetry.

We take a witness subspace `V` of dimension `k + 1` on which
`λₖ(S) ≤ re ⟪S x, x⟫` (lower direction for `S`), then a unit vector `x ∈ V`
with `re ⟪T x, x⟫ ≤ λₖ(T)` (upper direction for `T`).  The difference is
controlled by Cauchy–Schwarz. -/
private theorem eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ := forall_unit_vector_eigenvalue_le_re_inner hS hn k
  obtain ⟨x, hxV, hnx, hTup⟩ := exists_unit_vector_re_inner_le_eigenvalue hT hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
  -- `λₖ(S) − λₖ(T) ≤ re ⟪Sx,x⟫ − re ⟪Tx,x⟫ = re ⟪(S−T)x,x⟫ ≤ ‖(S−T)x‖ ≤ ε`.
  have hdiff : RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜
      = RCLike.re ⟪(S - T) x, x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_𝕜 ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    rw [hnx, mul_one]
    have := hε x
    rwa [hnx, mul_one] at this
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜 := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_𝕜 := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

/-- **Weyl's inequality** for symmetric operators on a finite-dimensional inner
product space over `𝕜 = ℝ, ℂ`: the `k`-th (decreasingly sorted) eigenvalues of
`T` and `S` differ by at most the operator norm of `T − S`.

Here the operator-norm bound is supplied as the hypothesis
`∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia,
*Matrix Analysis*, Corollary III.2.6. -/
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  -- The two directions of `eigenvalues_sub_le`, with the roles of `T` and `S`
  -- swapped, using `‖(T − S) x‖ = ‖(S − T) x‖`.
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

end ForMathlib
