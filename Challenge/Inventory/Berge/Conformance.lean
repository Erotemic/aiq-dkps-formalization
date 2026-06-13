/-
# AIQ DKPS ForMathlib inventory challenge: Approximate minimizers and Berge-style continuity

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/Topology/ApproxMinimizer.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Topology/Order/Compact.lean` (companion
to `IsCompact.exists_isMinOn`), or a dedicated file alongside
`Mathlib/Topology/Sequences.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


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
* `ForMathlib.exists_subseq_tendsto_isMinOn_of_approxMinOn` — the variant where the
  approximate-minimization comparison ranges only over the compact set `K`, so the
  limit is a minimizer *on `K`* (`IsMinOn F K`) rather than a global one. This is
  the form the Berge maximum theorem consumes (the feasible set is constrained).
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
  sorry
theorem exists_subseq_tendsto_isMinOn_of_approxMinOn
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x ∈ K, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x ∈ K, ∀ k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, IsMinOn F K ψ ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Topology/Berge.lean`
-/
/-
Staged for Mathlib: the Berge maximum theorem (upper hemicontinuity of the
parametric argmin correspondence over a fixed compact feasible set).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Berge's maximum theorem (fixed compact constraint)

Let `g : P → X → ℝ` be jointly continuous and let `K ⊆ X` be a fixed nonempty
compact set.  Consider the parametric minimization of `g p` over `K`, with
argmin correspondence
`M p = {x ∈ K | IsMinOn (g p) K x}`.
Berge's maximum theorem says the value function `p ↦ ⨅ x ∈ K, g p x` is continuous
and the correspondence `M` is upper hemicontinuous (and compact-valued and
nonempty).

Mathlib has the hemicontinuity *definitions* (`Mathlib/Topology/Semicontinuity/
Hemicontinuity.lean`) and the extreme-value theorem (`IsCompact.exists_isMinOn`),
but no Berge theorem.  This file supplies the upper-hemicontinuity half in two
usable forms, building on the approximate-minimizer stability engine
`ForMathlib.exists_subseq_tendsto_isMinOn_of_approxMinOn`:

* `tendsto_eval_sub_of_isCompact` — along a convergent parameter sequence
  `p k → p₀`, the evaluation difference `g (p k) (x k) − g p₀ (x k)` vanishes
  uniformly over points `x k` staying in the compact `K` (a uniform-convergence-
  on-compacts fact, here in the sequential form actually needed).
* `tendsto_subseq_isMinOn_of_isMinOn` — **sequential upper hemicontinuity**: any
  sequence of constrained minimizers `x k ∈ argmin (g (p k))` for `p k → p₀` has
  a subsequence converging to a constrained minimizer of `g p₀`.  This is the
  closed-graph form of Berge's theorem.
* `upperHemicontinuousAt_isMinOn` — the same conclusion phrased through Mathlib's
  own `UpperHemicontinuousAt` predicate for the argmin correspondence
  `p ↦ {x ∈ K | IsMinOn (g p) K x}` (requires `X` Hausdorff so the compact `K` is
  closed and limits of feasible points stay feasible).
* `exists_modulus_isMinOn_family` / `exists_modulus_isMinOn` — the **uniform
  `ε`–`δ` modulus** form (metric `P`): for every `ε > 0` there is a `δ > 0` such
  that whenever `dist p p₀ ≤ δ`, *every* minimizer of `g p` over `K` is `ε`-close
  (in the ambient metric, or in any finite family of continuous invariants) to
  *some* minimizer of `g p₀` over `K`.  The family form captures the
  affine-invariant `pairDistErr` closeness of MDS; it is the general core of the
  raw-stress modulus `Acharyya2024.exists_modulus_pairDist`, which additionally
  needs the MDS-specific coercive compactness (centering into a parameter-
  dependent box) that the fixed-`K` theorem here does not subsume.

## Main results

* `ForMathlib.tendsto_subseq_isMinOn_of_isMinOn`
* `ForMathlib.upperHemicontinuousAt_isMinOn`
* `ForMathlib.continuous_iInf_of_isCompact` — value-function continuity.
* `ForMathlib.exists_modulus_isMinOn_family` / `ForMathlib.exists_modulus_isMinOn`
-/

namespace ForMathlib

open Filter Topology Set

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [FirstCountableTopology X]

/-- **Sequential uniform convergence on a compact set from joint continuity.**
If `g : P → X → ℝ` is jointly continuous, `p k → p₀`, and the points `x k` stay in
a compact set `K`, then the evaluation difference `g (p k) (x k) − g p₀ (x k)`
tends to `0`.  (This is the only consequence of "`g (p k) → g p₀` uniformly on
`K`" needed for Berge; it is proved directly via the subsequence criterion and
sequential compactness, avoiding the compact-open topology.) -/
theorem tendsto_eval_sub_of_isCompact
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hx : ∀ k, x k ∈ K) :
    Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) := by
  sorry
theorem tendsto_subseq_isMinOn_of_isMinOn
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K)
    (hxmin : ∀ k, IsMinOn (g (p k)) K (x k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  sorry
theorem upperHemicontinuousAt_isMinOn {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [T2Space X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := by
  sorry
theorem continuous_iInf_of_isCompact [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := by
  sorry
theorem exists_modulus_isMinOn_family {P X : Type*} [PseudoMetricSpace P]
    [TopologicalSpace X] [FirstCountableTopology X]
    {ι : Type*} [Finite ι]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {ρ : ι → X → X → ℝ} (hρ : ∀ i, Continuous (Function.uncurry (ρ i)))
    (hρ0 : ∀ i x, ρ i x x = 0)
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ ∀ i, ρ i x x₀ < ε := by
  sorry
theorem exists_modulus_isMinOn {P X : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε := by
  sorry
end ForMathlib
