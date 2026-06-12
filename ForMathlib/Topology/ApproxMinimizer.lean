/-
Staged for Mathlib: additions to `Mathlib/Topology/Order/Compact.lean` (companion
to `IsCompact.exists_isMinOn`), or a dedicated file alongside
`Mathlib/Topology/Sequences.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Stability of minimizers under approximate minimization

If a sequence `z k` lives in a compact set and each `z k` *approximately*
minimizes a continuous real function `F` — for every point `x`, `F (z k) ≤
F x + ε x k` with `ε x k → 0` — then a subsequence of `z k` converges to a
genuine global minimizer of `F`.

This is the elementary "recovery" half of the fundamental theorem of
Γ-convergence: a perturbed family of variational problems whose minimizers stay
in a fixed compact set has a limit point that solves the unperturbed problem.
The typical source of the approximate-minimizer hypothesis is a second family
`F k` with `z k ∈ argmin (F k)` and `F k → F` in a suitable uniform sense.

## Main results

* `ForMathlib.exists_subseq_tendsto_forall_le_of_approxMin`
-/

namespace ForMathlib

open Filter Topology

/--
**Stability of minimizers under approximate minimization.**

Let `K` be a compact subset of a first-countable topological space, `F : X → ℝ`
continuous, and `z : ℕ → X` a sequence in `K` such that each `z k` approximately
minimizes `F`: for every `x`, `F (z k) ≤ F x + ε x k`, where `ε x k → 0` as
`k → ∞` (the error may depend on the comparison point `x`). Then there is a
strictly monotone `φ` and a point `ψ ∈ K` with `z ∘ φ → ψ` and `ψ` a global
minimizer of `F` (`∀ x, F ψ ≤ F x`).
-/
theorem exists_subseq_tendsto_forall_le_of_approxMin
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, (∀ x, F ψ ≤ F x) ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  obtain ⟨ψ, hψK, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq hz
  refine ⟨φ, hφ_mono, ψ, hψK, ?_, hφ_tendsto⟩
  intro x
  -- `F (z (φ t)) → F ψ` by continuity of `F`.
  have hcont : Tendsto (fun t => F (z (φ t))) atTop (𝓝 (F ψ)) :=
    (hF.tendsto ψ).comp hφ_tendsto
  -- `F x + ε x (φ t) → F x` since the (subsequenced) error vanishes.
  have hrhs : Tendsto (fun t => F x + ε x (φ t)) atTop (𝓝 (F x)) := by
    have hεφ : Tendsto (fun t => ε x (φ t)) atTop (𝓝 0) :=
      (hε x).comp hφ_mono.tendsto_atTop
    simpa using tendsto_const_nhds.add hεφ
  -- Pass the pointwise bound to the limit.
  exact le_of_tendsto_of_tendsto hcont hrhs
    (Eventually.of_forall fun t => happrox x (φ t))

end ForMathlib
