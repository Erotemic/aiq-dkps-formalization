/-
# CFC-in-element + compact-existential measurability (pending: destination unsettled)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open MeasureTheory Set

variable {Ω A : Type*} [MeasurableSpace Ω]
  [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [ContinuousStar A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NormOneClass A]
  [MeasurableSpace A] [BorelSpace A]

/-- **Measurability of the continuous functional calculus in the element.** -/
theorem measurable_cfc_comp
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : Ω → A) (hB : Measurable B) (hsa : ∀ ω, IsSelfAdjoint (B ω)) :
    Measurable (fun ω => cfc f (B ω)) := by
  sorry

end ForMathlib

namespace ForMathlib

open Filter Topology TopologicalSpace

/-- **Measurability of a compactly-quantified existential constraint.** -/
theorem measurableSet_exists_mem_le
    {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Y} (hS : IsCompact S)
    {F : Y → Ω → ℝ}
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hFm : ∀ y ∈ S, Measurable (F y)) (c : ℝ) :
    MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ c} := by
  sorry

end ForMathlib
