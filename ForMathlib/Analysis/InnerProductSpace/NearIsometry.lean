/-
Staged for Mathlib: a proposed new file `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); golf pass (drop unused
`set … with`, `rwa` consolidation, dedupe the repeated `⟪b k, b k⟫ = 1` fact to
a single `hunit`) by Claude Opus 4.8 (claude-opus-4-8[1m]) per the
`mathlib-quality` rules.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Quantitative polar factor for a near-isometry

A linear map `M` on a finite-dimensional real inner product space whose quadratic form
`x ↦ ⟪M x, M x⟫` is uniformly `δ`-close to `x ↦ ⟪x, x⟫` (with `δ ≤ 1 / 2`) lies within
`2 * δ` of a genuine linear isometry equivalence: there is `W : E ≃ₗᵢ[ℝ] E` with
`‖M x - W x‖ ≤ 2 * δ * ‖x‖` for all `x`.

The isometry is the *polar factor* `W = M ∘ (Mᵀ ∘ M)^(-1/2)`: the inverse square root of the
Gram operator `G = Mᵀ ∘ M` is built directly from its orthonormal eigenbasis
(`LinearMap.IsSymmetric.eigenvectorBasis`), so the proof uses neither the continuous functional
calculus nor a singular value decomposition.  Mathlib currently has no polar decomposition in
any form, and a future CFC-based polar decomposition would not directly give the quantitative
bound proved here.

The constant `2 * δ` is not sharp: the construction actually yields `√(1 + δ) * δ`, which is
the known sharp constant, but the statement rounds it up to `2 * δ` for usability (as in the
source development).

## Main results

* `ForMathlib.Real.abs_one_sub_inv_sqrt_le`: the scalar inequality `|1 - (√μ)⁻¹| ≤ δ` for
  `|μ - 1| ≤ δ ≤ 1 / 2`, used to control the eigenvalue rescaling.  It belongs with the
  `Real.sqrt` API (`Mathlib/Analysis/Real/Sqrt.lean`) and is staged here next to its consumer.
* `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le`: the quantitative polar
  factor, with the pointwise quadratic-form hypothesis
  `|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`.
* `ForMathlib.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`: the corollary for
  the operator-norm hypothesis `‖adjoint M * M - 1‖ ≤ δ`.

## TODO

* `TODO(RCLike)`: generalize the two operator results from `ℝ` to `RCLike 𝕜`.  The eigenbasis
  machinery (`LinearMap.IsSymmetric.eigenvectorBasis`) already works over `RCLike`; only the
  real-inner-product bookkeeping below would need to be redone.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Ch. 8
  (the unitary polar factor as the nearest isometry).
-/

namespace ForMathlib

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

namespace Real

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The point: `1 - (√μ)⁻¹ = (μ - 1) / (μ + √μ)` and the denominator `μ + √μ ≥ 1` when
`μ ≥ 1 / 2`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  have hμlb : 1 - δ ≤ μ := by rw [abs_le] at hμ; linarith
  have hμpos : (0 : ℝ) < μ := by linarith
  set s := Real.sqrt μ
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμpos
  have hssq : s ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos)
  -- `s ≥ 1/2` (since `s² = μ ≥ 1/2`)
  have hssqlb : (1 : ℝ) / 2 ≤ s ^ 2 := by rw [hssq]; linarith
  have hsge : (1 : ℝ) / 2 ≤ s := by nlinarith [hs0, hssqlb]
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hμ
  rw [abs_le] at hμ ⊢
  obtain ⟨hμ1, hμ2⟩ := hμ
  -- The inverse `s⁻¹` is positive and `s * s⁻¹ = 1`.
  have hsinv0 : 0 < s⁻¹ := inv_pos.mpr hs0
  have hsmul : s * s⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs0)
  -- `μ = s²` rewritten as `s * s` for `nlinarith`.
  have hssq' : s * s = μ := by nlinarith [hssq]
  -- Lower bound `1 ≤ (1 + δ) * s`: its square is `(1 + δ)² μ ≥ (1 + δ)² (1 - δ) ≥ 1`.
  have hlow : 1 ≤ (1 + δ) * s := by
    have hpos : 0 < (1 + δ) * s := by positivity
    nlinarith [hpos, hssq', hμ1, hμ2, hδ0, hsge, mul_nonneg hδ0 hδ0,
      mul_nonneg (mul_nonneg hδ0 hδ0) hδ0]
  -- Upper bound `(1 - δ) * s ≤ 1`: equivalently `(1 - δ)² μ ≤ 1` when `1 - δ ≥ 0`.
  have hhigh : (1 - δ) * s ≤ 1 := by
    rcases le_or_gt (1 - δ) 0 with h | h
    · nlinarith [hs0, h]
    · nlinarith [hssq', hμ1, hμ2, hδ0, hsge, h, mul_nonneg hδ0 hδ0]
  -- Translate the two multiplicative bounds into bounds on `s⁻¹`.
  have hinv_le : s⁻¹ ≤ 1 + δ := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]; linarith [hlow]
  have hle_inv : 1 - δ ≤ s⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hs0]; linarith [hhigh]
  exact ⟨by linarith [hinv_le], by linarith [hle_inv]⟩

end Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Quantitative polar factor for a near-isometry.**  If the quadratic form of a linear map
`M` on a finite-dimensional real inner product space is uniformly `δ`-close to the identity
quadratic form (`|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`, with `δ ≤ 1 / 2`), then `M` differs
from a linear isometry equivalence `W` by at most `2 * δ` pointwise:
`‖M x - W x‖ ≤ 2 * δ * ‖x‖`.

`W` is the polar factor `M ∘ G^(-1/2)` where `G = Mᵀ ∘ M` is the Gram operator; its inverse
square root is built from the orthonormal eigenbasis of `G`, with the eigenvalue rescaling
controlled by `ForMathlib.Real.abs_one_sub_inv_sqrt_le`.  The constant `2 * δ` is not sharp:
the construction gives `√(1 + δ) * δ` (the known sharp constant), and the statement rounds it
up to `2 * δ`. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  -- Degenerate case: if `E` is a subsingleton every vector is `0`, so `W := refl` works.
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · exact ⟨LinearIsometryEquiv.refl ℝ E, fun x => by simp [Subsingleton.elim x 0]⟩
  -- Main case: `E` is nontrivial.  Derive `δ ≥ 0` from a nonzero vector.
  have hδ0 : 0 ≤ δ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
    have hmul : 0 ≤ δ * ⟪v, v⟫_ℝ :=
      le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)
    exact nonneg_of_mul_nonneg_left hmul hvpos
  obtain ⟨d, hd⟩ : ∃ d, finrank ℝ E = d := ⟨_, rfl⟩
  -- The Gram operator and its symmetry.
  set G : E →ₗ[ℝ] E := M.adjoint * M with hG
  have hGsymm : G.IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self M
  -- `⟪G x, x⟫ = ⟪M x, M x⟫` (the defining identity of the Gram operator).
  have hGquad : ∀ x : E, ⟪G x, x⟫_ℝ = ⟪M x, M x⟫_ℝ := by
    intro x
    rw [hG, Module.End.mul_apply, LinearMap.adjoint_inner_left]
  -- Sorted eigen-data of `G`.
  set b := hGsymm.eigenvectorBasis hd with hb
  set μ := hGsymm.eigenvalues hd with hμ
  -- The eigenbasis vectors are unit vectors.
  have hunit : ∀ k : Fin d, ⟪b k, b k⟫_ℝ = 1 := fun k => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one k]; ring
  -- Parseval: in the eigenbasis the squared coordinates sum to the squared norm.
  have hpars : ∀ y : E, ∑ k : Fin d, b.repr y k ^ 2 = ‖y‖ ^ 2 := by
    intro y
    rw [← b.sum_sq_inner_right y]
    exact Finset.sum_congr rfl fun k _ => by rw [b.repr_apply_apply]
  -- Each eigenvalue lies in `[1 - δ, 1 + δ]`, in particular `≥ 1/2 > 0`.
  have hμbound : ∀ k : Fin d, |μ k - 1| ≤ δ := by
    intro k
    have hGbk : ⟪G (b k), b k⟫_ℝ = μ k := by
      rw [hb, hGsymm.apply_eigenvectorBasis, real_inner_smul_left, ← hb, ← hμ, hunit k]
      simp
    have := hM (b k)
    rwa [← hGquad, hGbk, hunit k, mul_one] at this
  have hμpos : ∀ k : Fin d, (1 : ℝ) / 2 ≤ μ k := by
    intro k
    have := hμbound k
    rw [abs_le] at this
    linarith
  -- The inverse-square-root operator `R := G^(-1/2)` via the eigenbasis scaling.
  set R : E →ₗ[ℝ] E := b.toBasis.constr ℝ (fun k => (Real.sqrt (μ k))⁻¹ • b k) with hR
  -- `R` acts diagonally on the eigenbasis.
  have hRbasis : ∀ k : Fin d, R (b k) = (Real.sqrt (μ k))⁻¹ • b k := by
    intro k
    rw [hR]
    have := b.toBasis.constr_basis ℝ (fun k => (Real.sqrt (μ k))⁻¹ • b k) k
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  -- `M` applied to the eigenbasis gives inner products `μ j * δ_{jk}`.
  have hMM : ∀ j k : Fin d, ⟪M (b j), M (b k)⟫_ℝ = if j = k then μ j else 0 := by
    intro j k
    have hadj : ⟪M (b j), M (b k)⟫_ℝ = ⟪G (b j), b k⟫_ℝ := by
      rw [hG, Module.End.mul_apply, LinearMap.adjoint_inner_left]
    rw [hadj, hb, hGsymm.apply_eigenvectorBasis, real_inner_smul_left, ← hb, ← hμ]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    by_cases hjk : j = k
    · subst hjk
      rw [hunit j, if_pos rfl, mul_one]
    · rw [b.inner_eq_zero hjk, if_neg hjk, mul_zero]
  -- The candidate isometry.
  set W : E →ₗ[ℝ] E := M ∘ₗ R with hW
  -- `W` applied to the eigenbasis: `W (b k) = (√(μ k))⁻¹ • M (b k)`.
  have hWbasis : ∀ k : Fin d, W (b k) = (Real.sqrt (μ k))⁻¹ • M (b k) := by
    intro k
    rw [hW, LinearMap.comp_apply, hRbasis, map_smul]
  -- Key: `W` preserves inner products on the eigenbasis.
  have hWortho : ∀ j k : Fin d, ⟪W (b j), W (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ := by
    intro j k
    rw [hWbasis, hWbasis, real_inner_smul_left, real_inner_smul_right, hMM]
    have hμj : (0 : ℝ) < μ j := by have := hμpos j; linarith
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have hsj : Real.sqrt (μ j) > 0 := Real.sqrt_pos.mpr hμj
      have hsqj : Real.sqrt (μ j) ^ 2 = μ j := Real.sq_sqrt (le_of_lt hμj)
      rw [hunit j]
      -- `(√μ)⁻¹ * ((√μ)⁻¹ * μ) = μ⁻¹ * μ = 1`.
      field_simp
      nlinarith [hsqj, hsj]
    · rw [if_neg hjk, b.inner_eq_zero hjk, mul_zero, mul_zero]
  -- Bilinear extension: `W` preserves all inner products.
  have hWinner : ∀ x y : E, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hWortho k j]
  -- The operator bound `‖(M - W) x‖ ≤ 2 δ ‖x‖`.  First, `M - W = M ∘ (id - R)`.
  have hMW : M - W = M ∘ₗ (LinearMap.id - R) := by
    rw [hW, LinearMap.comp_sub, LinearMap.comp_id]
  -- The eigenbasis coordinates of `R x`: diagonal scaling by `(√(μ k))⁻¹`.
  have hreprR : ∀ (x : E) (k : Fin d),
      b.repr (R x) k = (Real.sqrt (μ k))⁻¹ * b.repr x k := by
    intro x k
    have hRx : R x = ∑ j : Fin d, b.repr x j • ((Real.sqrt (μ j))⁻¹ • b j) := by
      conv_lhs => rw [← b.sum_repr x, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hRbasis]
    rw [b.repr_apply_apply, hRx, inner_sum]
    rw [Finset.sum_eq_single k]
    · rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        b.orthonormal.norm_eq_one k, b.repr_apply_apply]
      ring
    · intro j _ hjk
      rw [real_inner_smul_right, real_inner_smul_right, b.inner_eq_zero hjk.symm]
      ring
    · intro hk; exact absurd (Finset.mem_univ k) hk
  -- `(id - R)` shrinks each coordinate by `|1 - (√(μ k))⁻¹| ≤ δ`; hence `‖·‖ ≤ δ ‖·‖`.
  set D : E →ₗ[ℝ] E := LinearMap.id - R with hD
  have hidR : ∀ x : E, ‖D x‖ ≤ δ * ‖x‖ := by
    intro x
    have hcoord : ∀ k : Fin d,
        b.repr (D x) k = (1 - (Real.sqrt (μ k))⁻¹) * b.repr x k := by
      intro k
      rw [b.repr_apply_apply, hD, LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right,
        ← b.repr_apply_apply, ← b.repr_apply_apply, hreprR]
      ring
    -- Parseval squared: `‖(id - R) x‖² = ∑ ((1 - (√(μ k))⁻¹) * b.repr x k)²`.
    have hpar : ‖D x‖ ^ 2
        = ∑ k : Fin d, ((1 - (Real.sqrt (μ k))⁻¹) * b.repr x k) ^ 2 := by
      rw [← hpars (D x)]
      exact Finset.sum_congr rfl fun k _ => by rw [hcoord k]
    -- Bound each squared term by `δ² * (b.repr x k)²`.
    have hbnd : ‖D x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
      rw [hpar, ← hpars x, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have hc := Real.abs_one_sub_inv_sqrt_le hδ (hμbound k)
      have habs : (1 - (Real.sqrt (μ k))⁻¹) ^ 2 ≤ δ ^ 2 := by
        have h1 := abs_nonneg (1 - (Real.sqrt (μ k))⁻¹)
        nlinarith [hc, h1, abs_le.mp hc]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    -- Take square roots.
    have hnn : 0 ≤ δ * ‖x‖ := mul_nonneg hδ0 (norm_nonneg _)
    nlinarith [hbnd, norm_nonneg (D x), hnn, sq_nonneg (‖D x‖ - δ * ‖x‖)]
  -- `‖M z‖ ≤ √(1 + δ) * ‖z‖` from the closeness hypothesis.
  have hMz : ∀ z : E, ‖M z‖ ≤ Real.sqrt (1 + δ) * ‖z‖ := by
    intro z
    have hquad : ⟪M z, M z⟫_ℝ ≤ (1 + δ) * ⟪z, z⟫_ℝ := by
      have hc := hM z
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
  -- Assemble: `‖(M - W) x‖ ≤ √(1 + δ) * δ * ‖x‖ ≤ 2 δ ‖x‖`.
  have hsqrtbound : Real.sqrt (1 + δ) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hbound : ∀ x : E, ‖(M - W) x‖ ≤ 2 * δ * ‖x‖ := by
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
  -- Bundle `W` as a linear isometry and upgrade to an equivalence by finite dimensionality.
  have hWcoe : ⇑(W.isometryOfInner hWinner) = ⇑W := W.coe_isometryOfInner hWinner
  have hWsurj : Function.Surjective (W.isometryOfInner hWinner) := by
    rw [hWcoe]
    exact LinearMap.injective_iff_surjective.mp
      (hWcoe ▸ (W.isometryOfInner hWinner).injective)
  refine ⟨LinearIsometryEquiv.ofSurjective _ hWsurj, fun x => ?_⟩
  have hx : LinearIsometryEquiv.ofSurjective _ hWsurj x = W x := by
    rw [LinearIsometryEquiv.coe_ofSurjective, hWcoe]
  rw [hx, ← LinearMap.sub_apply]
  exact hbound x

end LinearMap

namespace ContinuousLinearMap

/-- **Quantitative polar factor, operator-norm form.**  If a continuous linear map `M` on a
finite-dimensional real inner product space satisfies `‖adjoint M * M - 1‖ ≤ δ` with
`δ ≤ 1 / 2`, then `M` differs from a linear isometry equivalence `W` by at most `2 * δ`
pointwise: `‖M x - W x‖ ≤ 2 * δ * ‖x‖`.

This is a corollary of `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le` via
Cauchy–Schwarz: `|⟪M x, M x⟫ - ⟪x, x⟫| = |⟪(adjoint M * M - 1) x, x⟫| ≤ δ * ⟪x, x⟫`. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  have hclose : ∀ x : E,
      |⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ := by
    intro x
    have hid : ⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ
        = ⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ := by
      rw [sub_apply, mul_apply_eq_comp, one_apply_eq_self, inner_sub_left,
        ContinuousLinearMap.adjoint_inner_left]
      simp
    rw [← hid]
    calc |⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ|
        ≤ ‖(ContinuousLinearMap.adjoint M * M - 1) x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖ContinuousLinearMap.adjoint M * M - 1‖ * ‖x‖ * ‖x‖ :=
          mul_le_mul_of_nonneg_right
            ((ContinuousLinearMap.adjoint M * M - 1).le_opNorm x) (norm_nonneg x)
      _ ≤ δ * ‖x‖ * ‖x‖ := by gcongr
      _ = δ * ⟪x, x⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]; ring
  obtain ⟨W, hW⟩ :=
    LinearMap.exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) hδ hclose
  exact ⟨W, fun x => by simpa using hW x⟩

end ContinuousLinearMap

end ForMathlib
