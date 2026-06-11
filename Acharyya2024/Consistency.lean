/-
Consistency theorems for:

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel perspective space"
arXiv:2409.17308.

Status (2026-06-11): COMPLETE — no `sorry` remains in this file.

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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem rawStress_mds_stability_set
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf))
  {ε : Real} (hε : 0 < ε) :
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem rawStress_mds_stability
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem fixed_models_fixed_queries_consistency
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact rawStress_mds_stability P Dseq DeltaInf ψhat hψhat huniq hD

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
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency P Dseq DeltaInf ψhat hψhat huniq
    (growing_queries_dissimilarity_converges P Dseq Delta DeltaInf hsample hlimit)

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

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, "Consistent estimation of generative model
  representations in the data kernel perspective space", Theorem 4 and Appendix
  A.3.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem growing_models_growing_queries_consistency
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  (huniq : ∀ k, RawStress.UniquePairProfile (nOf k) d (DeltaInf k))
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
  refine ⟨id, strictMono_id, fun k => ?_⟩
  obtain ⟨ψ, hψ_mem, hψ_conv⟩ :=
    RawStress.mds_stability_inProbability_of_uniqueProfile P
      (fun r ω => Dseq r ω k) (DeltaInf k) (fun r ω => ψhat r ω k)
      (fun r ω => hψhat r ω k) (huniq k) (hD k)
  exact ⟨ψ, hψ_mem, fun i j => hψ_conv i j⟩

/--
Triangular-array consistency in the paper's Theorem-5 form: the per-stage
dissimilarity convergence is split into a per-stage sampling error against a
stage-and-budget population `Delta r k` plus a deterministic per-stage
Assumption-1 error, mirroring `fixed_models_growing_queries_consistency`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem growing_models_growing_queries_consistency_of_sample_limit
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (Delta : Nat → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  (huniq : ∀ k, RawStress.UniquePairProfile (nOf k) d (DeltaInf k))
  (hsample : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (Delta r k)))
  (hlimit : ∀ k, Tendsto (fun r => frobSub (Delta r k) (DeltaInf k)) atTop (𝓝 0)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  refine growing_models_growing_queries_consistency P d nOf Dseq DeltaInf ψhat
    hψhat huniq (fun k => ?_)
  exact growing_queries_dissimilarity_converges P
    (fun r ω => Dseq r ω k) (fun r => Delta r k) (DeltaInf k)
    (hsample k) (hlimit k)

end Acharyya2024.Consistency
