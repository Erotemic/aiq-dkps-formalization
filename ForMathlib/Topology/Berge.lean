/-
Staged for Mathlib: the Berge maximum theorem (upper hemicontinuity of the
parametric argmin correspondence over a fixed compact feasible set).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Topology.ApproxMinimizer
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity

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
* `exists_modulus_isMinOn` — the **uniform `ε`–`δ` modulus** form (metric `P`,
  `X`): for every `ε > 0` there is a `δ > 0` such that whenever `dist p p₀ < δ`,
  *every* minimizer of `g p` over `K` is within `ε` of *some* minimizer of `g p₀`
  over `K`.  This is the form that, instantiated at the raw-stress objective,
  yields the MDS-stability modulus `exists_modulus_pairDist`.

## Main results

* `ForMathlib.tendsto_subseq_isMinOn_of_isMinOn`
* `ForMathlib.upperHemicontinuousAt_isMinOn`
* `ForMathlib.exists_modulus_isMinOn`
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
  -- Continuity of `g p₀ = (uncurry g) ∘ (p₀, ·)`.
  have hgp0 : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  -- It suffices to find, in every subsequence, a convergent sub-subsequence.
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- `x ∘ ns` lives in `K`; extract a convergent sub-subsequence `x (ns (φ ·)) → a`.
  obtain ⟨a, _ha, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq (fun n => hx (ns n))
  refine ⟨φ, ?_⟩
  have hns' : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ_mono.tendsto_atTop
  have hpns : Tendsto (fun n => p (ns (φ n))) atTop (𝓝 p₀) := hp.comp hns'
  -- Joint continuity along `(p (ns φ n), x (ns φ n)) → (p₀, a)`.
  have h1 : Tendsto (fun n => g (p (ns (φ n))) (x (ns (φ n)))) atTop (𝓝 (g p₀ a)) :=
    (hg.tendsto (p₀, a)).comp (hpns.prodMk_nhds hφ_tendsto)
  -- Continuity in the second argument at the fixed parameter `p₀`.
  have h2 : Tendsto (fun n => g p₀ (x (ns (φ n)))) atTop (𝓝 (g p₀ a)) :=
    (hgp0.tendsto a).comp hφ_tendsto
  simpa using h1.sub h2

/-- **Sequential upper hemicontinuity of the argmin correspondence (Berge).**
Let `g : P → X → ℝ` be jointly continuous and `K` a fixed compact set.  If
`p k → p₀` and each `x k` minimizes `g (p k)` over `K`, then a subsequence of
`x k` converges to a point `x₀ ∈ K` that minimizes `g p₀` over `K`.

This is the closed-graph form of Berge's maximum theorem: the argmin
correspondence `p ↦ {x ∈ K | IsMinOn (g p) K x}` has closed graph (equivalently,
is upper hemicontinuous, since `K` is compact). -/
theorem tendsto_subseq_isMinOn_of_isMinOn
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K)
    (hxmin : ∀ k, IsMinOn (g (p k)) K (x k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  have hgp0 : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  -- The evaluation difference vanishes (uniform convergence on `K`).
  have hsub : Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) :=
    tendsto_eval_sub_of_isCompact hK hg hp hxK
  -- `x k` approximately minimizes `g p₀` on `K`, with error
  -- `ε y k = (g (p k) y − g p₀ y) + (g p₀ (x k) − g (p k) (x k))`.
  refine exists_subseq_tendsto_isMinOn_of_approxMinOn hK hgp0 hxK
    (ε := fun y k => (g (p k) y - g p₀ y) + (g p₀ (x k) - g (p k) (x k))) ?_ ?_
  · -- the error tends to `0` for each fixed comparison point `y ∈ K`
    intro y _hy
    have ha : Tendsto (fun k => g (p k) y - g p₀ y) atTop (𝓝 0) := by
      have hy' : Tendsto (fun k => g (p k) y) atTop (𝓝 (g p₀ y)) :=
        (hg.tendsto (p₀, y)).comp (hp.prodMk_nhds tendsto_const_nhds)
      have hc : Tendsto (fun _ : ℕ => g p₀ y) atTop (𝓝 (g p₀ y)) := tendsto_const_nhds
      simpa using hy'.sub hc
    have hb : Tendsto (fun k => g p₀ (x k) - g (p k) (x k)) atTop (𝓝 0) := by
      simpa [neg_sub] using hsub.neg
    simpa using ha.add hb
  · -- the approximate-minimization inequality, from `IsMinOn (g (p k)) K`
    intro y hy k
    have hmin : g (p k) (x k) ≤ g (p k) y := (isMinOn_iff.mp (hxmin k)) y hy
    linarith

/-- **Berge's maximum theorem via Mathlib's `UpperHemicontinuousAt`.**
For `X` Hausdorff (so the compact feasible set `K` is closed), jointly continuous
`g`, and `P` first-countable at `p₀`, the argmin correspondence
`p ↦ {x ∈ K | IsMinOn (g p) K x}` is upper hemicontinuous at `p₀` in the sense of
`Mathlib.Topology.Semicontinuity.Hemicontinuity`.

This lands the closed-graph statement on Mathlib's own predicate, via its
sequential characterization `UpperHemicontinuousAt.of_sequences`: the
correspondence is `K`-valued (so the containment premise is trivial) and the
closed-graph obligation is discharged by passing the minimization inequality
`g (p n) (c n) ≤ g (p n) y` to the limit through joint continuity. -/
theorem upperHemicontinuousAt_isMinOn {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [T2Space X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := by
  refine UpperHemicontinuousAt.of_sequences hK.isSeqCompact
    (Eventually.of_forall fun p => Set.sep_subset _ _) ?_
  intro p hp c hc c₀ hc₀
  -- `c n ∈ K` and `IsMinOn (g (p n)) K (c n)`; `p n → p₀`, `c n → c₀`.
  have hcK : ∀ n, c n ∈ K := fun n => (hc n).1
  refine ⟨hK.isClosed.mem_of_tendsto hc₀ (Eventually.of_forall hcK), ?_⟩
  rw [isMinOn_iff]
  intro y hy
  -- pass `g (p n) (c n) ≤ g (p n) y` to the limit via joint continuity
  have hL : Tendsto (fun n => g (p n) (c n)) atTop (𝓝 (g p₀ c₀)) :=
    (hg.tendsto (p₀, c₀)).comp (hp.prodMk_nhds hc₀)
  have hR : Tendsto (fun n => g (p n) y) atTop (𝓝 (g p₀ y)) :=
    (hg.tendsto (p₀, y)).comp (hp.prodMk_nhds tendsto_const_nhds)
  exact le_of_tendsto_of_tendsto hL hR
    (Eventually.of_forall fun n => (isMinOn_iff.mp (hc n).2) y hy)

/-- **Berge's maximum theorem, uniform `ε`–`δ` modulus form.**
With `P`, `X` (pseudo)metric spaces, `g` jointly continuous, and `K` a fixed
compact set: for every `ε > 0` there is `δ > 0` such that whenever
`dist p p₀ ≤ δ`, *every* feasible minimizer `x` of `g p` over `K` (i.e. `x ∈ K`
with `IsMinOn (g p) K x`) is within `ε` of *some* feasible minimizer `x₀` of
`g p₀` over `K`.

The `δ` depends only on `p₀` and `ε` (a genuine modulus of upper hemicontinuity),
exactly the shape needed downstream to avoid measurable selection of minimizers.
Instantiated at the raw-stress objective this is the MDS-stability modulus
`Acharyya2024.exists_modulus_pairDist`. -/
theorem exists_modulus_isMinOn {P X : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε := by
  by_contra hcon
  push Not at hcon
  -- Counterexamples at `δ = 1/(k+1)`: feasible minimizers `x k` for parameters
  -- `p k → p₀`, none of which is `ε`-close to any minimizer of `g p₀`.
  have hex := fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  choose p x hxK hxmin hpδ hbad using hex
  -- The parameters converge to `p₀` (squeeze `0 ≤ dist (p k) p₀ ≤ 1/(k+1)`).
  have hp : Tendsto p atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) hpδ tendsto_one_div_add_atTop_nhds_zero_nat
  -- Berge: a subsequence of the minimizers converges to a minimizer of `g p₀`.
  obtain ⟨φ, _hφ, x₀, hx₀K, hx₀min, htend⟩ :=
    tendsto_subseq_isMinOn_of_isMinOn hK hg hp hxK hxmin
  -- That limit is eventually within `ε`, contradicting the counterexample bound.
  have hd : Tendsto (fun t => dist (x (φ t)) x₀) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp htend
  obtain ⟨t, ht⟩ := (hd.eventually (eventually_lt_nhds hε)).exists
  exact absurd ht (not_lt.mpr (hbad (φ t) x₀ hx₀K hx₀min))

end ForMathlib
