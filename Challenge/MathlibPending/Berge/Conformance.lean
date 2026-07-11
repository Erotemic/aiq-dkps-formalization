/-
# Berge maximum theorem fragments (pending: likely too narrow)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open Filter Topology Set

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

theorem upperHemicontinuousAt_isMinOn {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [T2Space X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := by
  sorry

-- `[FirstCountableTopology X]` precedes `[FirstCountableTopology P]` to match the
-- ForMathlib source, where the former is an accumulated section instance and the
-- latter the theorem's own; the comparator needs the exact instance order.
theorem continuous_iInf_of_isCompact [FirstCountableTopology X] [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := by
  sorry

theorem exists_modulus_isMinOn {P X : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε := by
  sorry

end ForMathlib
