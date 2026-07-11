/-
# Countable restrict-cover measurability (pending: minor)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open MeasureTheory Set

/-- **Measurability from a countable restrict-cover** (countable version of
`measurable_of_restrict_of_restrict_compl`). -/
theorem measurable_of_iUnion_restrict {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {g : Ω → A} {s : ℕ → Set Ω}
    (hs : ∀ k, MeasurableSet (s k)) (hcov : (⋃ k, s k) = univ)
    (hg : ∀ k, Measurable ((s k).restrict g)) : Measurable g := by
  sorry

end ForMathlib
