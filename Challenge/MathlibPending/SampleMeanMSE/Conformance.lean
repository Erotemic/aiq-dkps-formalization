/-
# Vector-valued sample-mean MSE (pending: confirm novelty vs scalar variance)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integral_norm_sq_average_sub_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P = ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : ℝ)⁻¹ * ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P := by
  sorry

theorem integral_norm_sq_average_sub_le_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    {γ : ℝ} (hbound : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P ≤ γ) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P ≤ γ / r := by
  sorry

end ForMathlib
