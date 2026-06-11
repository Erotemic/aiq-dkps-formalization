/-
Staged for Mathlib: additions to
`Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Measurability-free complement bound for probability measures

For a probability measure, `1 - μ sᶜ ≤ μ s` for an **arbitrary** set `s`.

Mathlib's `prob_compl_eq_one_sub₀` requires `NullMeasurableSet s` and
`prob_compl_le_one_sub_of_le_prob` requires `MeasurableSet s`; this lemma needs
nothing, because subadditivity `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ` holds for outer
measures.  This is the form in which high-probability events are consumed when
converting vanishing failure probabilities into convergence statements, where
the event sets are often not (easily) measurable.
-/

namespace ForMathlib

open MeasureTheory
open scoped ENNReal

/--
For a probability measure, `1 - μ sᶜ ≤ μ s`, with no measurability assumption
on `s`: subadditivity gives `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ`.
-/
theorem one_sub_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) : 1 - μ sᶜ ≤ μ s :=
  tsub_le_iff_right.mpr <| by
    calc (1 : ℝ≥0∞) = μ (s ∪ sᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ s + μ sᶜ := measure_union_le _ _

end ForMathlib
