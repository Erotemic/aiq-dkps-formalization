/-
# AIQ DKPS ForMathlib inventory challenge: Measurability and compact-existential infrastructure

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/MeasureTheory/CfcMeasurable.lean`
-/
/-
Staged for Mathlib: addition to
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/` (measurability of
`ω ↦ cfc f (a ω)`) and `Mathlib/MeasureTheory/MeasurableSpace/` (a countable
restrict-cover measurability criterion).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Measurability of the continuous functional calculus in the element

For a *fixed* continuous `f : ℝ → ℝ`, the map `ω ↦ cfc f (a ω)` is measurable
whenever `a` is measurable and self-adjoint-valued in a C⋆-algebra `A`.

The point is that no measurable selection of an eigenbasis is needed — even
though `cfc f a = ∑ₖ f(λₖ) uₖ uₖ*` is built from eigenvectors `uₖ` that depend
*discontinuously* on `a` at eigenvalue crossings.  The functional-calculus map
`a ↦ cfc f a` is itself continuous on each set of uniformly bounded spectrum
(`continuousOn_cfc`), and `A` is covered by countably many such sets
`{a | ‖a‖ ≤ k}`; measurability glues over the cover.

This is exactly the tool that lets a "spectral embedding" `ψ̂(ω)` enter a
probability statement: while `ψ̂(ω)` (an eigenvector configuration) need not be
measurable, its Gram matrix — a rank-`d` *spectral truncation* `cfc f` of the
sample matrix — is, and the events one cares about depend only on that Gram.

## Main results

* `ForMathlib.measurable_of_iUnion_restrict` — measurability from a countable
  measurable cover on which the restrictions are measurable.
* `ForMathlib.measurable_cfc_comp` — `ω ↦ cfc f (a ω)` is measurable.
-/

namespace ForMathlib

open MeasureTheory Set

/--
**Measurability from a countable restrict-cover.**

If `Ω = ⋃ₖ sₖ` with each `sₖ` measurable and the restriction of `g` to each
`sₖ` measurable, then `g` is measurable.  (The two-set case is
`measurable_of_restrict_of_restrict_compl`; this is the countable version.)
-/
theorem measurable_of_iUnion_restrict {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {g : Ω → A} {s : ℕ → Set Ω}
    (hs : ∀ k, MeasurableSet (s k)) (hcov : (⋃ k, s k) = univ)
    (hg : ∀ k, Measurable ((s k).restrict g)) : Measurable g := by
  sorry
variable {Ω A : Type*} [MeasurableSpace Ω]
  [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [ContinuousStar A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NormOneClass A]
  [MeasurableSpace A] [BorelSpace A]

/--
**Measurability of the continuous functional calculus in the element.**

For a fixed continuous `f : ℝ → ℝ`, if `B : Ω → A` is measurable and
self-adjoint-valued, then `ω ↦ cfc f (B ω)` is measurable — with no measurable
selection of an eigenbasis.
-/
theorem measurable_cfc_comp
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : Ω → A) (hB : Measurable B) (hsa : ∀ ω, IsSelfAdjoint (B ω)) :
    Measurable (fun ω => cfc f (B ω)) := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/MeasureTheory/CompactExists.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/MeasureTheory/Constructions/BorelSpace/`
(measurability of events defined by a compactly-quantified constraint).

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


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
  sorry
end ForMathlib
