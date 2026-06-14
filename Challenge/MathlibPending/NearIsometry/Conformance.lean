/-
# Quantitative polar factor / near-isometry (pending: niche)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Quantitative polar factor for a near-isometry** (quadratic-form hypothesis). -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  sorry

end LinearMap

namespace ContinuousLinearMap

/-- **Quantitative polar factor, operator-norm form.** -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  sorry

end ContinuousLinearMap
end ForMathlib
