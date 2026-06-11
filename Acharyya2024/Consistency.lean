/-
Scaffold for:

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel perspective space"
arXiv:2409.17308.

Status:
- This is a scaffold, not a completed formalization.
- Load-bearing future proof obligations are expressed as theorem statements ending
  in `by sorry`, not declaration-level assumptions.
- This makes the open work visible in editor/build warnings and avoids hiding it
  behind a theorem that appears assumption-free.
-/

import Acharyya2024.Common

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2024.Consistency

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## Paper layer 1: fixed model set, fixed query set -/

/--
Trosset-style raw-stress MDS stability.

This is the deterministic/geometric bridge used by the 2024 paper: if observed
dissimilarity matrices converge to a limiting dissimilarity matrix, then raw-stress
MDS configurations have a convergent subsequence whose pairwise distances match a
limiting MDS solution.

This is load-bearing: replacing this `sorry` requires the MDS stability proof.

Mathematical source/citation:
- Trosset and Priebe, "Continuous multidimensional scaling", cited as Theorem 2
  in Acharyya et al. 2024, Appendix A.1/A.2.

PARTIAL (2026-06-11): the deterministic core is PROVED in
`Acharyya2024.RawStress` — minimizer existence (`mds_nonempty`), √-stress
1-Lipschitz continuity, and deterministic subsequence stability
(`exists_subseq_tendsto_mds`, `pairDist_tendsto`). The remaining gap in THIS
statement is the probabilistic upgrade: the deterministic subsequence and
limit configuration are ω-dependent, while this statement asserts a single
subsequence and a fixed `ψ ∈ MDS` with convergence in probability — a
measurable-selection argument the paper does not spell out (see the plan
watch-list).
-/
theorem rawStress_mds_stability
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  sorry

/-- Fixed `n,m` consistency theorem: paper Theorem 1 shape. -/
theorem fixed_models_fixed_queries_consistency
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact rawStress_mds_stability P Dseq DeltaInf ψhat hψhat hD

/-! ## Paper layer 2: fixed model set, growing query set -/

/--
Convergence in probability to zero survives adding a deterministic vanishing
perturbation: if `0 ≤ C r ω ≤ A r ω + b r` with `A → 0` in probability and
`b → 0` deterministically, then `C → 0` in probability.

This is the triangle-inequality layer of the paper's Theorem 2: it splits the
empirical-to-limit error into the sampling error (handled by
`Acharyya2024.Probability`) and the deterministic Assumption-1 error.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem convergesInProbabilityZero_of_le_add
    (P : Measure Ω)
    (A C : Nat → Ω → Real)
    (b : Nat → Real)
    (hC_nonneg : ∀ r ω, 0 ≤ C r ω)
    (hle : ∀ r ω, C r ω ≤ A r ω + b r)
    (hA : ConvergesInProbabilityZero P A)
    (hb : Tendsto b atTop (𝓝 0)) :
    ConvergesInProbabilityZero P C := by
  intro ε hε
  have hb_event : ∀ᶠ r in atTop, b r ≤ ε / 2 := by
    have hball : ∀ᶠ r in atTop, b r ∈ Metric.ball (0 : Real) (ε / 2) :=
      hb.eventually (Metric.ball_mem_nhds _ (by linarith))
    filter_upwards [hball] with r hr
    have : |b r| < ε / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hr
    exact ((abs_lt.mp this).2).le
  have hA_half := hA (ε / 2) (by linarith)
  rw [ENNReal.tendsto_nhds_zero] at hA_half ⊢
  intro δ hδ
  filter_upwards [hA_half δ hδ, hb_event] with r hAr hbr
  refine le_trans (measure_mono ?_) hAr
  intro ω hω
  have hCω : ε < C r ω := by
    have : dist (C r ω) 0 > ε := hω
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hC_nonneg r ω)] at this
  have hAω : ε / 2 < A r ω := by
    have := hle r ω
    linarith
  show dist (A r ω) 0 > ε / 2
  rw [Real.dist_eq, sub_zero]
  exact lt_of_lt_of_le hAω (le_abs_self _)

/--
Probability step for the fixed-model/growing-query regime (paper Theorem 2),
REPAIRED version.

The original scaffold statement had no hypotheses and was false. The honest
content splits as `frobSub (Dseq r ω) DeltaInf ≤
frobSub (Dseq r ω) (Delta r) + frobSub (Delta r) DeltaInf` where:

* `hsample` — the sampling error `frobSub (Dseq r ω) (Delta r)` converges to
  zero in probability; in the paper this is supplied by the Markov/variance
  argument, formalized in `Acharyya2024.Probability`
  (`dissimilarity_convergesInProbability_of_secondMoment`) together with
  `Acharyya2024.SecondMoment` (the iid `trace(Σ)/r` computation).
* `hlimit` — the deterministic Assumption-1 error
  `frobSub (Delta r) DeltaInf → 0`.

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, arXiv:2409.17308, Theorem 2 and Appendix
  A.2 (the final triangle-inequality step invoking Assumption 1).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem growing_queries_dissimilarity_converges
  (P : Measure Ω)
  {n : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf) := by
  refine convergesInProbabilityZero_of_le_add P
    (fun r ω => frobSub (Dseq r ω) (Delta r))
    (fun r ω => frobSub (Dseq r ω) DeltaInf)
    (fun r => frobSub (Delta r) DeltaInf)
    (fun r ω => Real.sqrt_nonneg _)
    (fun r ω => ?_) hsample hlimit
  -- Triangle inequality for the Frobenius distance, via the `ℓ²(pairs)` norm.
  have htri := abs_norm_sub_norm_le
    (WithLp.toLp 2 (fun p : Fin n × Fin n => Dseq r ω p.1 p.2 - DeltaInf p.1 p.2))
    (WithLp.toLp 2 (fun p : Fin n × Fin n => Delta r p.1 p.2 - DeltaInf p.1 p.2))
  have hnorm : ∀ (A B : DisMat n),
      ‖WithLp.toLp 2 (fun p : Fin n × Fin n => A p.1 p.2 - B p.1 p.2)‖
        = frobSub A B := by
    intro A B
    rw [EuclideanSpace.norm_eq, frobSub, frob, frobSq]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have hdiff : ‖WithLp.toLp 2 (fun p : Fin n × Fin n => Dseq r ω p.1 p.2 - DeltaInf p.1 p.2)
        - WithLp.toLp 2 (fun p : Fin n × Fin n => Delta r p.1 p.2 - DeltaInf p.1 p.2)‖
      = frobSub (Dseq r ω) (Delta r) := by
    rw [← hnorm (Dseq r ω) (Delta r)]
    congr 1
    apply (WithLp.linearEquiv 2 ℝ _).injective
    ext p
    show (Dseq r ω p.1 p.2 - DeltaInf p.1 p.2) - (Delta r p.1 p.2 - DeltaInf p.1 p.2)
      = Dseq r ω p.1 p.2 - Delta r p.1 p.2
    ring
  rw [hnorm, hnorm, hdiff] at htri
  have := (abs_le.mp htri).2
  linarith

/--
Fixed `n`, growing-query consistency: paper Theorem 3 shape, with the repaired
probability-step hypotheses threaded through.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem fixed_models_growing_queries_consistency
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency P Dseq DeltaInf ψhat hψhat
    (growing_queries_dissimilarity_converges P Dseq Delta DeltaInf hsample hlimit)

/-! ## Paper layer 3: growing model set and growing query set -/

/--
A deliberately abstract statement for the growing-model regime.

The paper's final regime involves a triangular array of model sets and query sets.
This theorem records the shape downstream users usually need: for each finite
stage `k`, along one shared subsequence of sampling/query budgets, the estimated
MDS pairwise distances converge in probability to pairwise distances in an MDS
configuration for the limiting `k`-model dissimilarity matrix.

This is load-bearing and currently only a target statement.

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, "Consistent estimation of generative model
  representations in the data kernel perspective space", Theorem 4 and Appendix
  A.3.

TODO(false-statement): no probability hypotheses connect `Dseq` to `DeltaInf`,
so this is false as written (same disease as
`growing_queries_dissimilarity_converges`). Repair deferred; see
planning/acharyya-plan.md WP8.
-/
theorem growing_models_growing_queries_consistency
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  sorry

end Acharyya2024.Consistency
