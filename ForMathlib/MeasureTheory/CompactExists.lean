/-
Staged for Mathlib: addition to `Mathlib/MeasureTheory/Constructions/BorelSpace/`
(measurability of events defined by a compactly-quantified constraint).

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Measurability of compactly-quantified existential events

For a Carathéodory-type function `F : Y → Ω → ℝ` — continuous in the parameter
`y` on a compact set `S`, measurable in the sample `ω` for each fixed `y` — the
event `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable.

The point is that the existential quantifies over an *uncountable* compact set,
yet no measurable-selection theorem is needed: by separability of the compact
set the event is a countable intersection of countable unions
`⋂ k, ⋃ (y ∈ D), {ω | F y ω < c + 1/(k+1)}` (`D ⊆ S` countable dense), the
nontrivial inclusion being sequential compactness plus continuity in `y` to pass
the approximate witnesses to a limit witness.

This is the standard device for showing measurability of events of the form
"some alignment/transformation in a compact group achieves error ≤ c" without
selecting the optimal transformation measurably.

## Main result

* `ForMathlib.measurableSet_exists_mem_le`
-/

namespace ForMathlib

open Filter Topology TopologicalSpace

/--
**Measurability of a compactly-quantified existential constraint.**

Let `S` be a compact set in a pseudometric space, and `F : Y → Ω → ℝ` be
continuous in `y` on `S` (for each `ω`) and measurable in `ω` (for each
`y ∈ S`).  Then `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable.
-/
theorem measurableSet_exists_mem_le
    {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Y} (hS : IsCompact S)
    {F : Y → Ω → ℝ}
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hFm : ∀ y ∈ S, Measurable (F y)) (c : ℝ) :
    MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ c} := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · have hempty : {ω | ∃ y ∈ S, F y ω ≤ c} = ∅ := by
      ext ω; simp [hSe]
    rw [hempty]; exact MeasurableSet.empty
  -- A countable dense subset `D ⊆ S`.
  haveI : SeparableSpace ↥S := hS.isSeparable.separableSpace
  obtain ⟨t, htc, htd⟩ := TopologicalSpace.exists_countable_dense ↥S
  set D : Set Y := (fun y : ↥S => (y : Y)) '' t with hD
  have hDS : D ⊆ S := by rintro _ ⟨⟨y, hy⟩, _, rfl⟩; exact hy
  have hDc : D.Countable := htc.image _
  -- Approximation: every point of `S` has points of `D` arbitrarily close.
  have happrox : ∀ y₀ ∈ S, ∀ ε > 0, ∃ y ∈ D, dist y y₀ < ε := by
    intro y₀ hy₀ ε hε
    have hmem : (⟨y₀, hy₀⟩ : ↥S) ∈ closure t := htd.closure_eq ▸ Set.mem_univ _
    rcases Metric.mem_closure_iff.mp hmem ε hε with ⟨d, hdt, hdist⟩
    exact ⟨(d : Y), ⟨d, hdt, rfl⟩, by simpa [dist_comm, Subtype.dist_eq] using hdist⟩
  -- The event as a countable intersection of countable unions.
  have hset : {ω | ∃ y ∈ S, F y ω ≤ c}
      = ⋂ k : ℕ, ⋃ y ∈ D, {ω | F y ω < c + 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y₀, hy₀S, hy₀⟩ k
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hcw := hFc ω y₀ hy₀S
      rw [Metric.continuousWithinAt_iff] at hcw
      rcases hcw (1 / ((k : ℝ) + 1)) hk with ⟨δ, hδ, hball⟩
      rcases happrox y₀ hy₀S δ hδ with ⟨y, hyD, hyd⟩
      refine ⟨y, hyD, ?_⟩
      have hclose := hball (hDS hyD) hyd
      have habs : |F y ω - F y₀ ω| < 1 / ((k : ℝ) + 1) := by
        simpa [Real.dist_eq] using hclose
      have hlt := (abs_lt.mp habs).2
      linarith
    · intro h
      choose y hyD hylt using h
      have hyS : ∀ k, y k ∈ S := fun k => hDS (hyD k)
      obtain ⟨ystar, hystarS, φ, hφ, hconv⟩ := hS.isSeqCompact hyS
      refine ⟨ystar, hystarS, ?_⟩
      -- `F (y (φ j)) ω → F ystar ω` by continuity within `S`.
      have hwithin : Tendsto (fun j => y (φ j)) atTop (𝓝[S] ystar) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv
          (Eventually.of_forall fun j => hyS (φ j))
      have htend : Tendsto (fun j => F (y (φ j)) ω) atTop (𝓝 (F ystar ω)) :=
        Filter.Tendsto.comp (hFc ω ystar hystarS) hwithin
      -- The bounds `c + 1/(j+1)` tend to `c`.
      have hbound : ∀ j, F (y (φ j)) ω ≤ c + 1 / ((j : ℝ) + 1) := by
        intro j
        have h1 : F (y (φ j)) ω < c + 1 / ((φ j : ℝ) + 1) := hylt (φ j)
        have hj : ((j : ℝ) + 1) ≤ ((φ j : ℝ) + 1) := by
          have : j ≤ φ j := hφ.le_apply
          exact_mod_cast Nat.add_le_add_right this 1
        have h2 : (1 : ℝ) / ((φ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) hj
        linarith
      have hlim : Tendsto (fun j : ℕ => c + 1 / ((j : ℝ) + 1)) atTop (𝓝 c) := by
        have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
        simpa using hc.add h0
      exact le_of_tendsto_of_tendsto htend hlim (Eventually.of_forall hbound)
  rw [hset]
  exact MeasurableSet.iInter fun k =>
    MeasurableSet.biUnion hDc fun y hy =>
      measurableSet_lt (hFm y (hDS hy)) measurable_const

end ForMathlib
