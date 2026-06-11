/-
Quantitative polar factor for a near-isometry on a finite-dimensional real inner
product space.

Given a linear map `M` whose induced quadratic form `x ↦ ⟪M x, M x⟫` is uniformly
close to `x ↦ ⟪x, x⟫` (`|⟪M x, M x⟫ − ⟪x, x⟫| ≤ δ ⟪x, x⟫` for `δ ≤ 1/2`), we
produce a genuine linear isometry `W` with `‖(M − W) x‖ ≤ 2 δ ‖x‖`.

This is the (c3) sub-deliverable of WP7(c) of `planning/acharyya-plan.md` — the
elementary polar-factor construction.  The route is entirely via the sorted
spectral API for symmetric operators (no Mathlib CFC):

* `G := Mᵀ ∘ M` (the Gram operator) is symmetric and its Rayleigh quotients lie
  in `[1 − δ, 1 + δ]`, hence every sorted eigenvalue `μ_k` satisfies
  `|μ_k − 1| ≤ δ`, in particular `μ_k ≥ 1 − δ ≥ 1/2 > 0`.
* `R := G^{-1/2}` is built as `Basis.constr` of the eigenbasis scaling
  `b_k ↦ (√μ_k)⁻¹ • b_k`.  Then `W := M ∘ R` is an isometry
  (`⟪W x, W y⟫ = ⟪x, y⟫`) because on the eigenbasis
  `⟪W b_j, W b_k⟫ = (√μ_j)⁻¹ (√μ_k)⁻¹ μ_j δ_{jk} = δ_{jk}`.
* `M − W = M ∘ (id − R)`; `(id − R)` shrinks every coordinate by
  `|1 − (√μ_k)⁻¹| ≤ δ` (Parseval), and `‖M z‖ ≤ √(1+δ) ‖z‖`, giving the
  constant `√(1+δ) · δ ≤ √(3/2) · δ ≤ 2 δ`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2025.Weyl

open scoped BigOperators RealInnerProductSpace InnerProductSpace
open Module (finrank)

namespace Acharyya2025.PolarFactor

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Scalar inequality for the inverse square root -/

/-- If `|μ − 1| ≤ δ ≤ 1/2`, then `|1 − (√μ)⁻¹| ≤ δ`.

The point: `1 − (√μ)⁻¹ = (μ − 1)/(μ + √μ)` and the denominator `μ + √μ ≥ 1`
when `μ ≥ 1/2`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1/2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  have hμlb : 1 - δ ≤ μ := by rw [abs_le] at hμ; linarith
  have hμpos : (0:ℝ) < μ := by linarith
  set s := Real.sqrt μ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμpos
  have hssq : s ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos)
  -- s ≥ √(1/2) ≥ 1/2  (since s² = μ ≥ 1/2)
  have hssqlb : (1:ℝ)/2 ≤ s ^ 2 := by rw [hssq]; linarith
  have hsge : (1:ℝ)/2 ≤ s := by nlinarith [hs0, hssqlb]
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hμ
  rw [abs_le] at hμ ⊢
  obtain ⟨hμ1, hμ2⟩ := hμ
  -- The inverse `s⁻¹` is positive and `s * s⁻¹ = 1`.
  have hsinv0 : 0 < s⁻¹ := inv_pos.mpr hs0
  have hsmul : s * s⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs0)
  -- `μ = s²` rewritten as `s * s` for `nlinarith`.
  have hssq' : s * s = μ := by nlinarith [hssq]
  -- Lower bound `1 ≤ (1+δ)·s`: its square is `(1+δ)²μ ≥ (1+δ)²(1-δ) ≥ 1`.
  have hlow : 1 ≤ (1 + δ) * s := by
    have hpos : 0 < (1 + δ) * s := by positivity
    nlinarith [hpos, hssq', hμ1, hμ2, hδ0, hsge, mul_nonneg hδ0 hδ0,
      mul_nonneg (mul_nonneg hδ0 hδ0) hδ0]
  -- Upper bound `(1-δ)·s ≤ 1`: equivalently `(1-δ)²μ ≤ 1` when `1-δ ≥ 0`.
  have hhigh : (1 - δ) * s ≤ 1 := by
    rcases le_or_gt (1 - δ) 0 with h | h
    · nlinarith [hs0, h]
    · nlinarith [hssq', hμ1, hμ2, hδ0, hsge, h, mul_nonneg hδ0 hδ0]
  -- Translate the two multiplicative bounds into bounds on `s⁻¹`.
  have hinv_le : s⁻¹ ≤ 1 + δ := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]; linarith [hlow]
  have hle_inv : 1 - δ ≤ s⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hs0]; linarith [hhigh]
  constructor
  · linarith [hinv_le]
  · linarith [hle_inv]

/-! ### The quantitative polar factor -/

/-- **Quantitative polar factor for a near-isometry.**  If the quadratic form of a
linear map `M` is uniformly `δ`-close to the identity quadratic form
(`|⟪M x, M x⟫ − ⟪x, x⟫| ≤ δ ⟪x, x⟫`, with `δ ≤ 1/2`), then `M` differs from a
genuine linear isometry `W` by an operator of norm at most `2 δ`:
`‖(M − W) x‖ ≤ 2 δ ‖x‖`.

`W := M ∘ G^{-1/2}` where `G := Mᵀ ∘ M` is the Gram operator; `G^{-1/2}` is built
from the sorted eigenbasis of `G`.  The constant `2 δ` is not sharp (the
construction gives `√(1+δ) · δ ≤ √(3/2) · δ`), but suffices.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]). -/
theorem exists_isometry_close_of_self_adjoint_comp_close
    {d : ℕ} (hd : finrank ℝ F = d)
    (M : F →ₗ[ℝ] F)
    {δ : ℝ} (hδ_lt : δ ≤ 1/2)
    (hclose : ∀ x : F, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : F →ₗ[ℝ] F,
      (∀ x y : F, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      (∀ x : F, ‖(M - W) x‖ ≤ 2 * δ * ‖x‖) := by
  classical
  -- Degenerate case: if `F` is a subsingleton every vector is `0`, so `W := id`
  -- works (both inner products and the difference are identically `0`).
  rcases subsingleton_or_nontrivial F with hsub | hnt
  · refine ⟨LinearMap.id, ?_, ?_⟩
    · intro x y
      simp [Subsingleton.elim x 0, Subsingleton.elim y 0]
    · intro x
      simp [Subsingleton.elim x 0]
  -- Main case: `F` is nontrivial.  Derive `δ ≥ 0` from a nonzero vector.
  have hδ0 : 0 ≤ δ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : F)
    have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
    have hc := hclose v
    have hmul : 0 ≤ δ * ⟪v, v⟫_ℝ :=
      le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) hc
    exact nonneg_of_mul_nonneg_left hmul hvpos
  -- The Gram operator and its symmetry.
  set G : F →ₗ[ℝ] F := M.adjoint * M with hG
  have hGsymm : G.IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self M
  -- `⟪G x, x⟫ = ⟪M x, M x⟫` (the defining identity of the Gram operator).
  have hGquad : ∀ x : F, ⟪G x, x⟫_ℝ = ⟪M x, M x⟫_ℝ := by
    intro x
    rw [hG, Module.End.mul_apply, LinearMap.adjoint_inner_left]
  -- Sorted eigen-data of `G`.
  set b := hGsymm.eigenvectorBasis hd with hb
  set μ := hGsymm.eigenvalues hd with hμ
  -- Each eigenvalue lies in `[1 − δ, 1 + δ]`, in particular `≥ 1/2 > 0`.
  have hμbound : ∀ k : Fin d, |μ k - 1| ≤ δ := by
    intro k
    have hnorm1 : ⟪b k, b k⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one k]; ring
    -- `⟪G (b k), b k⟫ = μ k`.
    have hGbk : ⟪G (b k), b k⟫_ℝ = μ k := by
      rw [hb, hGsymm.apply_eigenvectorBasis, real_inner_smul_left, ← hb, ← hμ, hnorm1]
      simp
    have := hclose (b k)
    rw [← hGquad, hGbk, hnorm1, mul_one] at this
    exact this
  have hμpos : ∀ k : Fin d, (1:ℝ)/2 ≤ μ k := by
    intro k
    have := hμbound k
    rw [abs_le] at this
    linarith
  -- The inverse-square-root operator `R := G^{-1/2}` via the eigenbasis scaling.
  set R : F →ₗ[ℝ] F := b.toBasis.constr ℝ (fun k => (Real.sqrt (μ k))⁻¹ • b k) with hR
  -- `R` acts diagonally on the eigenbasis.
  have hRbasis : ∀ k : Fin d, R (b k) = (Real.sqrt (μ k))⁻¹ • b k := by
    intro k
    rw [hR]
    have := b.toBasis.constr_basis ℝ (fun k => (Real.sqrt (μ k))⁻¹ • b k) k
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  -- `M` applied to the eigenbasis gives inner products `μ_j δ_{jk}`.
  have hMM : ∀ j k : Fin d, ⟪M (b j), M (b k)⟫_ℝ = if j = k then μ j else 0 := by
    intro j k
    have hadj : ⟪M (b j), M (b k)⟫_ℝ = ⟪G (b j), b k⟫_ℝ := by
      rw [hG, Module.End.mul_apply, LinearMap.adjoint_inner_left]
    rw [hadj, hb, hGsymm.apply_eigenvectorBasis, real_inner_smul_left, ← hb, ← hμ]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    by_cases hjk : j = k
    · subst hjk
      have : ⟪b j, b j⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one j]; ring
      rw [this, if_pos rfl, mul_one]
    · rw [b.inner_eq_zero hjk, if_neg hjk, mul_zero]
  -- The candidate isometry.
  set W : F →ₗ[ℝ] F := M ∘ₗ R with hW
  -- `W` applied to the eigenbasis: `W (b k) = (√μ_k)⁻¹ • M (b k)`.
  have hWbasis : ∀ k : Fin d, W (b k) = (Real.sqrt (μ k))⁻¹ • M (b k) := by
    intro k
    rw [hW, LinearMap.comp_apply, hRbasis, map_smul]
  -- Key: `W` preserves inner products on the eigenbasis.
  have hWortho : ∀ j k : Fin d, ⟪W (b j), W (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ := by
    intro j k
    rw [hWbasis, hWbasis, real_inner_smul_left, real_inner_smul_right, hMM]
    have hμj : (0:ℝ) < μ j := by have := hμpos j; linarith
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have hsj : Real.sqrt (μ j) > 0 := Real.sqrt_pos.mpr hμj
      have hsqj : Real.sqrt (μ j) ^ 2 = μ j := Real.sq_sqrt (le_of_lt hμj)
      have hbb : ⟪b j, b j⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one j]; ring
      rw [hbb]
      -- `(√μ)⁻¹ · ((√μ)⁻¹ · μ) = μ⁻¹ · μ = 1`.
      field_simp
      nlinarith [hsqj, hsj]
    · rw [if_neg hjk, b.inner_eq_zero hjk, mul_zero, mul_zero]
  -- Bilinear extension: `W` preserves all inner products.
  have hWinner : ∀ x y : F, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    -- Expand `x` and `y` in the eigenbasis.
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hWortho k j]
  -- Provide the witness; the isometry property is `hWinner`.
  refine ⟨W, hWinner, ?_⟩
  -- Now the operator-norm bound.  First, `M − W = M ∘ (id − R)`.
  have hMW : M - W = M ∘ₗ (LinearMap.id - R) := by
    rw [hW, LinearMap.comp_sub, LinearMap.comp_id]
  -- The eigenbasis coordinates of `R x`: diagonal scaling by `(√μ_k)⁻¹`.
  have hreprR : ∀ (x : F) (k : Fin d),
      b.repr (R x) k = (Real.sqrt (μ k))⁻¹ * b.repr x k := by
    intro x k
    -- `R x = ∑ j, (b.repr x j) • ((√μ_j)⁻¹ • b j)`.
    have hRx : R x = ∑ j : Fin d, (b.repr x j) • ((Real.sqrt (μ j))⁻¹ • b j) := by
      conv_lhs => rw [← b.sum_repr x, map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, hRbasis]
    -- Read off the `k`-th coordinate as an inner product.
    rw [b.repr_apply_apply, hRx, inner_sum]
    rw [Finset.sum_eq_single k]
    · rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        b.orthonormal.norm_eq_one k, b.repr_apply_apply]
      ring
    · intro j _ hjk
      rw [real_inner_smul_right, real_inner_smul_right, b.inner_eq_zero hjk.symm]
      ring
    · intro hk; exact absurd (Finset.mem_univ k) hk
  -- `(id − R)` shrinks each coordinate by `|1 − (√μ_k)⁻¹| ≤ δ`; hence `‖·‖ ≤ δ‖·‖`.
  set D : F →ₗ[ℝ] F := LinearMap.id - R with hD
  have hidR : ∀ x : F, ‖D x‖ ≤ δ * ‖x‖ := by
    intro x
    have hcoord : ∀ k : Fin d,
        b.repr (D x) k = (1 - (Real.sqrt (μ k))⁻¹) * b.repr x k := by
      intro k
      rw [b.repr_apply_apply, hD, LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right,
        ← b.repr_apply_apply, ← b.repr_apply_apply, hreprR]
      ring
    -- Parseval squared: `‖(id−R)x‖² = Σ ((1−(√μ_k)⁻¹) (b.repr x k))²`.
    have hpar : ‖D x‖ ^ 2
        = ∑ k : Fin d, ((1 - (Real.sqrt (μ k))⁻¹) * b.repr x k) ^ 2 := by
      rw [← Acharyya2025.Weyl.sum_repr_sq_eq_norm_sq b]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hcoord k]
    -- Bound each squared term by `δ² (b.repr x k)²`.
    have hbnd : ‖D x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
      rw [hpar, ← Acharyya2025.Weyl.sum_repr_sq_eq_norm_sq b x, Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro k _
      have hc := abs_one_sub_inv_sqrt_le hδ_lt (hμbound k)
      have habs : (1 - (Real.sqrt (μ k))⁻¹) ^ 2 ≤ δ ^ 2 := by
        have h1 := abs_nonneg (1 - (Real.sqrt (μ k))⁻¹)
        nlinarith [hc, h1, abs_le.mp hc]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    -- Take square roots.
    have hnn : 0 ≤ δ * ‖x‖ := mul_nonneg hδ0 (norm_nonneg _)
    nlinarith [hbnd, norm_nonneg (D x), hnn, sq_nonneg (‖D x‖ - δ * ‖x‖)]
  -- `‖M z‖ ≤ √(1+δ) ‖z‖` from the closeness hypothesis.
  have hMz : ∀ z : F, ‖M z‖ ≤ Real.sqrt (1 + δ) * ‖z‖ := by
    intro z
    have hquad : ⟪M z, M z⟫_ℝ ≤ (1 + δ) * ⟪z, z⟫_ℝ := by
      have hc := hclose z
      rw [abs_le] at hc
      nlinarith [hc.2]
    have hMz2 : ‖M z‖ ^ 2 ≤ (1 + δ) * ‖z‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact hquad
    have h1δ : 0 ≤ 1 + δ := by linarith
    have hrhs : 0 ≤ Real.sqrt (1 + δ) * ‖z‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hsq : (Real.sqrt (1 + δ) * ‖z‖) ^ 2 = (1 + δ) * ‖z‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h1δ]
    nlinarith [hMz2, hrhs, norm_nonneg (M z), hsq,
      sq_nonneg (‖M z‖ - Real.sqrt (1 + δ) * ‖z‖)]
  -- Assemble: `‖(M−W)x‖ ≤ √(1+δ)·δ·‖x‖ ≤ 2δ‖x‖`.
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrtbound : Real.sqrt (1 + δ) ≤ 2 := by
    rw [← hsqrt4]
    exact Real.sqrt_le_sqrt (by linarith)
  intro x
  rw [hMW, LinearMap.comp_apply]
  calc ‖M (D x)‖
      ≤ Real.sqrt (1 + δ) * ‖D x‖ := hMz _
    _ ≤ Real.sqrt (1 + δ) * (δ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hidR x) (Real.sqrt_nonneg _)
    _ = Real.sqrt (1 + δ) * δ * ‖x‖ := by ring
    _ ≤ 2 * δ * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right hsqrtbound hδ0

end Acharyya2025.PolarFactor
