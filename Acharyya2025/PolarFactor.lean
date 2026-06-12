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

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import ForMathlib.Analysis.InnerProductSpace.NearIsometry
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
    |1 - (Real.sqrt μ)⁻¹| ≤ δ :=
  ForMathlib.Real.abs_one_sub_inv_sqrt_le hδ hμ

/-! ### The quantitative polar factor -/

/-- **Quantitative polar factor for a near-isometry.**  If the quadratic form of a
linear map `M` is uniformly `δ`-close to the identity quadratic form
(`|⟪M x, M x⟫ − ⟪x, x⟫| ≤ δ ⟪x, x⟫`, with `δ ≤ 1/2`), then `M` differs from a
genuine linear isometry `W` by an operator of norm at most `2 δ`:
`‖(M − W) x‖ ≤ 2 δ ‖x‖`.

`W := M ∘ G^{-1/2}` where `G := Mᵀ ∘ M` is the Gram operator; `G^{-1/2}` is built
from the sorted eigenbasis of `G`.  The constant `2 δ` is not sharp (the
construction gives `√(1+δ) · δ ≤ √(3/2) · δ`), but suffices.

Formalized by Claude Fable 5 (claude-fable-5[1m]). -/
theorem exists_isometry_close_of_self_adjoint_comp_close
    {d : ℕ} (_hd : finrank ℝ F = d)
    (M : F →ₗ[ℝ] F)
    {δ : ℝ} (hδ_lt : δ ≤ 1/2)
    (hclose : ∀ x : F, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : F →ₗ[ℝ] F,
      (∀ x y : F, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      (∀ x : F, ‖(M - W) x‖ ≤ 2 * δ * ‖x‖) := by
  obtain ⟨W, hW⟩ :=
    ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le M hδ_lt hclose
  refine ⟨W.toLinearEquiv.toLinearMap, fun x y => W.inner_map_map x y, fun x => ?_⟩
  rw [LinearMap.sub_apply]
  simpa using hW x

end Acharyya2025.PolarFactor
