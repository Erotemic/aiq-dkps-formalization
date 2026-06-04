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
Probability step for the fixed-model/growing-query regime.

This packages the paper's response-sampling argument: empirical dissimilarities
constructed from sample-average embedded responses converge in probability to the
population limiting dissimilarity matrix.

This is load-bearing: replacing this `sorry` requires the variance, trace,
Markov/union-bound, and query-growth formalization.

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, "Consistent estimation of generative model
  representations in the data kernel perspective space", Theorem 2 and Appendix
  A.2.
-/
theorem growing_queries_dissimilarity_converges
  (P : Measure Ω)
  {n : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n) :
  ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf) := by
  sorry

/-- Fixed `n`, growing-query consistency: paper Theorem 3 shape. -/
theorem fixed_models_growing_queries_consistency
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency P Dseq DeltaInf ψhat hψhat
    (growing_queries_dissimilarity_converges P Dseq DeltaInf)

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
