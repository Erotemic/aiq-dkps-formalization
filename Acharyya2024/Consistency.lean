/-
Consistency theorems for:

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel perspective space"
arXiv:2409.17308.

Status (2026-06-11): COMPLETE — no open obligations remain in this file.

- The probabilistic Trosset–Priebe raw-stress stability is proved in
  `Acharyya2024.RawStress`: deterministic core (minimizer existence, √-stress
  Lipschitz continuity, subsequence stability) + a modulus of continuity at the
  limit matrix + outer-measure event inclusion.  No measurable selection of
  minimizers is needed anywhere.
- Statements that were false as written in the original scaffold (missing
  probability hypotheses; an unconditional fixed-limit claim that fails when
  the limiting matrix admits minimizers with distinct distance profiles) have
  been REPAIRED: each now carries the honest hypotheses
  (`hsample`/`hlimit`/`huniq`) and is proved.  The repair history is recorded
  in planning/acharyya-plan.md and in git.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Acharyya2024.Common
import Acharyya2024.RawStress

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2024.Consistency

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## Paper layer 1: fixed model set, fixed query set -/

/--
**Unconditional raw-stress MDS stability (set version).**

If the observed dissimilarity matrices converge in probability to `DeltaInf`,
then with probability tending to one, the random MDS output is `ε`-close in
every pairwise distance to *some* raw-stress minimizer of `DeltaInf`.  This is
the strongest statement that is true without further hypotheses: when
`DeltaInf` admits minimizers with genuinely different distance profiles, no
fixed limit configuration (and no subsequence) can serve all sample paths.

Proved in `Acharyya2024.RawStress.mds_stability_inProbability_set` via a
modulus of continuity at `DeltaInf` plus outer-measure event inclusion — no
measurable selection of minimizers is required.

Mathematical source/citation:
- Trosset and Priebe, "Continuous multidimensional scaling", cited as Theorem 2
  in Acharyya et al. 2024, Appendix A.1/A.2.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: the *unconditional* (minimizer-SET) form behind paper
-- Theorem 1 / Lemma 1. It is the honest version of those subsequence claims when
-- `DeltaInf` may admit several minimizers with different distance profiles.
theorem rawStress_mds_stability_set
  (P : Measure Ω)
  {n d : Nat}                                  -- n = #models (fixed), d = embedding dimension
  -- Data: a sequence (indexed by replicate count r) of random dissimilarity matrices,
  -- their deterministic limit `DeltaInf`, and a random MDS minimizer `ψhat r ω` for each.
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: `ψhat r ω` is genuinely a raw-stress minimizer of the observed matrix `Dseq r ω`.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `hD`: observed dissimilarities converge to `DeltaInf` in probability (paper's `‖D − Δ^(∞)‖_F →P 0`).
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf))
  {ε : Real} (hε : 0 < ε) :
  -- Conclusion: with probability → 1, every pairwise distance of `ψhat r ω` is within ε
  -- of those of *some* minimizer of `DeltaInf` (closeness to the minimizer SET).
  Tendsto (fun r => P {ω | ¬ ∃ ψ ∈ MDS n d DeltaInf,
    ∀ i j : Fin n, pairDistErr (ψhat r ω) ψ i j ≤ ε}) atTop (𝓝 0) :=
  RawStress.mds_stability_inProbability_set P Dseq DeltaInf ψhat hψhat hD hε

/--
Trosset-style raw-stress MDS stability — REPAIRED + PROVED (2026-06-11).

The original scaffold statement asserted a single subsequence and a fixed
`ψ ∈ MDS n d DeltaInf` with convergence in probability, with no hypothesis on
the minimizer set of `DeltaInf`.  That is not provable: if `DeltaInf` has two
minimizers with distinct pairwise-distance profiles and the sample output
oscillates between their neighborhoods with probability `1/2` each, no
subsequence converges in probability to a fixed profile.  The repaired
statement adds the profile-uniqueness hypothesis `huniq` the paper implicitly
needs, and in exchange concludes along the FULL sequence (the witness
subsequence is `id`) — strictly stronger than the paper's subsequence claim.

The unconditional content (closeness to the minimizer SET) is
`rawStress_mds_stability_set` above.

Mathematical source/citation:
- Trosset and Priebe, "Continuous multidimensional scaling", cited as Theorem 2
  in Acharyya et al. 2024, Appendix A.1/A.2.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: this is the paper's Theorem 1 / Lemma 1 shape
-- (`‖ψ̂_i − ψ̂_{i'}‖ − ‖ψ_i − ψ_{i'}‖ →P 0` along a subsequence), here REPAIRED with the
-- extra profile-uniqueness hypothesis `huniq` (see below) and proved along the FULL sequence.
theorem rawStress_mds_stability
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: each `ψhat r ω` is a raw-stress minimizer of the observed matrix.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — all minimizers of `DeltaInf`
  -- share one pairwise-distance profile. The paper's subsequence claim implicitly needs this
  -- (otherwise no fixed profile serves all sample paths); in exchange the conclusion holds
  -- along the full sequence, strictly stronger than the paper's subsequence statement.
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  -- `hD`: observed dissimilarities → `DeltaInf` in probability (paper's `‖D − Δ^(∞)‖_F →P 0`).
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  -- Conclusion: there is a subsequence `u` (here `id`) and a minimizer `ψ` of `DeltaInf`
  -- such that every pairwise distance error `‖ψ̂_i − ψ̂_{i'}‖ − ‖ψ_i − ψ_{i'}‖` → 0 in probability.
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  obtain ⟨ψ, hψ_mem, hψ_conv⟩ :=
    RawStress.mds_stability_inProbability_of_uniqueProfile P Dseq DeltaInf ψhat hψhat huniq hD
  exact ⟨id, strictMono_id, ψ, hψ_mem, fun i j => hψ_conv i j⟩

/--
Fixed `n,m` consistency theorem: paper Theorem 1 shape, with the repaired
profile-uniqueness hypothesis threaded through.

Paper correspondence: this is the **fixed-models / fixed-queries** regime —
the paper's Theorem 1 (Section 4.1). It is a thin renaming wrapper around
`rawStress_mds_stability`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem fixed_models_fixed_queries_consistency_of_uniqueProfile
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: each `ψhat r ω` is a raw-stress minimizer of the observed matrix.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — uniqueness of the minimizer
  -- distance profile of `DeltaInf` (see `rawStress_mds_stability`).
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  -- `hD`: observed dissimilarities → `DeltaInf` in probability.
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  -- Conclusion: a subsequence of MDS minimizers has pairwise distances converging (in
  -- probability) to those of a true minimizer `ψ` of `DeltaInf` (paper Theorem 1).
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact rawStress_mds_stability P Dseq DeltaInf ψhat hψhat huniq hD

/--
Fixed-model consistency when the limiting dissimilarities are exactly
realizable in the chosen embedding dimension.

Exact realizability supplies the distance-profile uniqueness premise required
by the repaired fixed-limit theorem, so callers need not prove that technical
condition separately.
-/
theorem fixed_models_fixed_queries_consistency_of_exactRealization
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hexact : ∃ ψ : Config n d, RealizesDissimilarity ψ DeltaInf)
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_uniqueProfile P Dseq DeltaInf ψhat hψhat
    (RawStress.uniquePairProfile_of_exists_realizes hexact) hD

/-! ## Paper layer 2: fixed model set, growing query set -/

/--
Convergence in probability to zero survives adding a deterministic vanishing
perturbation: if `0 ≤ C r ω ≤ A r ω + b r` with `A → 0` in probability and
`b → 0` deterministically, then `C → 0` in probability.

This is the triangle-inequality layer of the paper's Theorem 2: it splits the
empirical-to-limit error into the sampling error (handled by
`Acharyya2024.Probability`) and the deterministic Assumption-1 error.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: internal helper (a general "squeeze" for convergence in
-- probability). Not a named paper result; it supplies the triangle-inequality step
-- of paper Theorem 2 used in `growing_queries_dissimilarity_converges`.
theorem convergesInProbabilityZero_of_le_add
    (P : Measure Ω)
    (A C : Nat → Ω → Real)
    (b : Nat → Real)
    -- `hC_nonneg`: `C` is nonnegative (it is a Frobenius distance in the application).
    (hC_nonneg : ∀ r ω, 0 ≤ C r ω)
    -- `hle`: pointwise bound `C ≤ A + b` splitting `C` into a random part `A` and a
    -- deterministic part `b`.
    (hle : ∀ r ω, C r ω ≤ A r ω + b r)
    -- `hA`: random part → 0 in probability; `hb`: deterministic part → 0.
    (hA : ConvergesInProbabilityZero P A)
    (hb : Tendsto b atTop (𝓝 0)) :
    -- Conclusion: `C → 0` in probability.
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

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: this is the dissimilarity-concentration content of paper
-- Theorem 2 (`‖D − Δ^(∞)‖_F →P 0`), split via the triangle inequality into a sampling
-- error against the model-mean-discrepancy matrix `Delta r` plus an Assumption-1 error.
theorem growing_queries_dissimilarity_converges
  (P : Measure Ω)
  {n : Nat}
  -- `Dseq` = observed dissimilarities; `Delta r` = stage-`r` population (model-mean
  -- discrepancy) matrix `Δ`; `DeltaInf` = limit `Δ^(∞)` from Assumption 1.
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  -- `hsample`: sampling error `‖D − Δ‖_F →P 0` (supplied in the paper by the Markov/
  -- variance argument of Theorem 2, formalized in `Acharyya2024.Probability`).
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  -- `hlimit`: deterministic Assumption-1 error `‖Δ − Δ^(∞)‖_F → 0`.
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  -- Conclusion: observed dissimilarities converge to `Δ^(∞)` in probability (paper Thm 2).
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
The growing-query dissimilarity conclusion with the deterministic limit
assumption reduced to entrywise convergence.

Because the model set is fixed and finite, pointwise convergence of every
population dissimilarity entry automatically gives the required Frobenius
convergence.
-/
theorem growing_queries_dissimilarity_converges_of_entrywise
  (P : Measure Ω)
  {n : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hentry : ∀ i j : Fin n,
    Tendsto (fun r => Delta r i j) atTop (𝓝 (DeltaInf i j))) :
  ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf) := by
  exact growing_queries_dissimilarity_converges P Dseq Delta DeltaInf hsample
    (tendsto_frobSub_zero_of_entrywise Delta DeltaInf hentry)

/--
Fixed `n`, growing-query consistency: paper Theorem 3 shape, with the repaired
probability-step hypotheses threaded through.

Paper correspondence: this is the **fixed-models / growing-queries** regime
(Section 4.2). It combines paper Theorem 2 (the dissimilarity step,
`growing_queries_dissimilarity_converges`) with Lemma 1 / the layer-1 stability
to yield paper Theorem 3 (under the `o(r)` variance condition, here supplied
abstractly via `hsample`/`hlimit`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem fixed_models_growing_queries_consistency_of_uniqueProfile
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: each `ψhat r ω` minimizes raw stress for the observed matrix.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — minimizer profile uniqueness.
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  -- `hsample` + `hlimit`: the two parts of the paper Theorem 2 dissimilarity step
  -- (sampling error and Assumption-1 error). In the paper these follow from the
  -- variance condition `(1/m)∑_j γ_ij = o(r)`; here they are taken as hypotheses.
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  -- Conclusion: a subsequence of MDS minimizers has pairwise distances converging in
  -- probability to those of a true minimizer `ψ` of `Δ^(∞)` (paper Theorem 3).
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_uniqueProfile P Dseq DeltaInf ψhat hψhat huniq
    (growing_queries_dissimilarity_converges P Dseq Delta DeltaInf hsample hlimit)

/--
Fixed-model, growing-query consistency with both technical limit assumptions
dispatched by natural structural hypotheses: exact realizability of the limit
and entrywise convergence of the population dissimilarities.
-/
theorem fixed_models_growing_queries_consistency_of_exactRealization_entrywise
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hexact : ∃ ψ : Config n d, RealizesDissimilarity ψ DeltaInf)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hentry : ∀ i j : Fin n,
    Tendsto (fun r => Delta r i j) atTop (𝓝 (DeltaInf i j))) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_exactRealization P Dseq DeltaInf ψhat
    hψhat hexact
    (growing_queries_dissimilarity_converges_of_entrywise P Dseq Delta DeltaInf hsample hentry)

/-! ## Paper layer 3: growing model set and growing query set -/

/--
Triangular-array consistency for the growing-model regime — REPAIRED + PROVED
(2026-06-11, WP8).

The paper's final regime involves a triangular array of model sets and query
sets: at stage `k` there are `nOf k` models, and for each fixed `k` the sampled
dissimilarity matrices converge (in probability) to the stage-`k` limit
`DeltaInf k`.  The original scaffold statement had NO probability hypotheses
connecting `Dseq` to `DeltaInf` and was false as written; the repaired version
adds the per-stage hypotheses `hD` (dissimilarity convergence) and `huniq`
(profile uniqueness, as in `rawStress_mds_stability`).

The paper extracts one shared subsequence across all stages by a diagonal
argument.  Under the repaired layer-1 stability the diagonal argument is
unnecessary: the full sequence converges at every stage, so the shared
subsequence is simply `id` — a strictly stronger conclusion.

SCOPE CAVEAT (honesty).  This is the *per-stage, finite* form: a countable family
of finite (`Fin (nOf k)`) consistency statements, one per stage `k`.  It is NOT
the paper's full Theorem 4/5 conclusion, which is an `Lᵖ` average over a
*continuum* of iid model draws `φ ~ P` from the model space —
`∫∫ |‖ψ̂₁ − ψ̂₂‖ − ‖mds(φ₁) − mds(φ₂)‖|ᵖ dP dP →P 0`.  Modelling the model
distribution `P`, the iid draw of models, and the continuous-MDS map `mds(φ)` is
not formalized here; this theorem is the finite consistency content that the
paper's argument specializes to at each stage, re-indexed over stages.

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, "Consistent estimation of generative model
  representations in the data kernel perspective space", Theorem 4 and Appendix
  A.3 (the finite per-stage content; the integral-over-`P` form is not
  formalized — see the scope caveat).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: the **growing-models / growing-queries** regime (Section 4.3),
-- corresponding to the FINITE per-stage content of paper Theorem 4. See the SCOPE CAVEAT
-- above: this is NOT the paper's full Lᵖ-over-the-model-distribution conclusion.
theorem growing_models_growing_queries_perStage_consistency_of_uniqueProfile
  (P : Measure Ω)
  (d : Nat)
  -- `nOf k` = number of models at stage `k` (a triangular array; the model count grows in `k`).
  (nOf : Nat → Nat)
  -- Per-stage data: observed dissimilarities `Dseq`, limits `DeltaInf k`, minimizers `ψhat`.
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  -- `hψhat`: at every stage `k`, `ψhat r ω k` minimizes raw stress for the observed matrix.
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — per-stage minimizer profile uniqueness.
  (huniq : ∀ k, RawStress.UniquePairProfile (nOf k) d (DeltaInf k))
  -- `hD`: per-stage dissimilarity convergence in probability (paper's `D →P Δ^(∞)`, each stage).
  (hD : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (DeltaInf k))) :
  -- Conclusion: a single subsequence `u` (here `id`) such that, at every stage `k`, the MDS
  -- minimizers' pairwise distances converge in probability to those of a true minimizer `ψ`.
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  refine ⟨id, strictMono_id, fun k => ?_⟩
  obtain ⟨ψ, hψ_mem, hψ_conv⟩ :=
    RawStress.mds_stability_inProbability_of_uniqueProfile P
      (fun r ω => Dseq r ω k) (DeltaInf k) (fun r ω => ψhat r ω k)
      (fun r ω => hψhat r ω k) (huniq k) (hD k)
  exact ⟨ψ, hψ_mem, fun i j => hψ_conv i j⟩

/--
Per-stage growing-model consistency when every stage limit is exactly
realizable in the common embedding dimension.
-/
theorem growing_models_growing_queries_perStage_consistency_of_exactRealization
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  (hexact : ∀ k, ∃ ψ : Config (nOf k) d,
    RealizesDissimilarity ψ (DeltaInf k))
  (hD : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (DeltaInf k))) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  exact growing_models_growing_queries_perStage_consistency_of_uniqueProfile P d nOf Dseq
    DeltaInf ψhat hψhat
    (fun k => RawStress.uniquePairProfile_of_exists_realizes (hexact k)) hD

/--
Triangular-array consistency in the paper's Theorem-5 *shape*: the per-stage
dissimilarity convergence is split into a per-stage sampling error against a
stage-and-budget population `Delta r k` plus a deterministic per-stage
Assumption-1 error, mirroring `fixed_models_growing_queries_consistency_of_uniqueProfile`.

Same SCOPE CAVEAT as `growing_models_growing_queries_perStage_consistency_of_uniqueProfile`:
this is the finite per-stage form, not the paper's `Lᵖ`-over-the-model-distribution
conclusion (the model distribution and the continuous-MDS map are not
formalized).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: the **growing-models / growing-queries** regime in the paper's
-- Theorem 5 *shape* (the finite per-stage content). Same SCOPE CAVEAT as above: not the
-- paper's full Lᵖ-over-the-model-distribution conclusion.
theorem growing_models_growing_queries_perStage_consistency_of_sample_limit_uniqueProfile
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)                                   -- stage-`k` model count
  -- Per-stage data, with `Delta r k` the stage-`k`, budget-`r` population matrix.
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (Delta : Nat → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  -- `hψhat`: per-stage raw-stress minimality of `ψhat`.
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — per-stage profile uniqueness.
  (huniq : ∀ k, RawStress.UniquePairProfile (nOf k) d (DeltaInf k))
  -- `hsample` + `hlimit`: per-stage split of the dissimilarity convergence (paper Theorem 4)
  -- into sampling error and deterministic Assumption-2 error.
  (hsample : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (Delta r k)))
  (hlimit : ∀ k, Tendsto (fun r => frobSub (Delta r k) (DeltaInf k)) atTop (𝓝 0)) :
  -- Conclusion: one subsequence `u` (here `id`) giving per-stage in-probability convergence
  -- of MDS pairwise distances to those of a true minimizer `ψ` (paper Theorem 5 shape).
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  refine growing_models_growing_queries_perStage_consistency_of_uniqueProfile P d nOf Dseq DeltaInf ψhat
    hψhat huniq (fun k => ?_)
  exact growing_queries_dissimilarity_converges P
    (fun r ω => Dseq r ω k) (fun r => Delta r k) (DeltaInf k)
    (hsample k) (hlimit k)

end Acharyya2024.Consistency
