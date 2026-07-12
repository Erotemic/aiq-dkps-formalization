/-
Population-geometry obligations for Perfect Quench.

Goal of this module:

  response distances equal true perspective distances
    -> centered augmented perspective configuration
    -> classical-MDS Gram identity
    -> radial identity used by nearest-neighbor Quench.

The final public theorem should ask for only the first line.  The current
production bridge asks callers to provide all three lines separately.
-/

import DkpsQuench.Perfect.Definitions

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench.Perfect

open Acharyya2024
open Acharyya2025.Deterministic

universe u v wr

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- Centering is a translation, so pairwise differences are unchanged. -/
theorem centerConfig_sub_centerConfig
    {n d : Nat} (z : Config n d) (i j : Fin n) :
    centerConfig z i - centerConfig z j = z i - z j := by
  simp only [centerConfig]
  abel

/-- Centering preserves every pairwise Euclidean distance. -/
theorem norm_centerConfig_sub_centerConfig
    {n d : Nat} (z : Config n d) (i j : Fin n) :
    ‖centerConfig z i - centerConfig z j‖ = ‖z i - z j‖ := by
  rw [centerConfig_sub_centerConfig]

/-- A centered finite configuration has coordinate sum zero.

Suggested proof route for a weaker agent:
1. unfold `centerConfig` and `configCentroid`;
2. commute the finite sum with subtraction and scalar multiplication;
3. use `Finset.sum_const` and `Fintype.card_fin`;
4. cancel `n * n⁻¹` using `hn` after casting `n` to `Real`.
Keep the result coordinate-free if possible; only descend to coordinates if the
finite-sum simplifier cannot see the scalar cancellation. -/
theorem sum_centerConfig_eq_zero
    {n d : Nat} (hn : 0 < n) (z : Config n d) :
    ∑ i, centerConfig z i = 0 := by
  sorry

/-- Classical double centering of exact Euclidean distances recovers the Gram
matrix of the centered configuration.

This is the main algebraic obligation in the population-geometry track.  A
robust proof should be split internally into the following identities:

* expand `‖z i - z j‖²` as two squared norms minus twice the inner product;
* compute row, column, and grand means of that expansion;
* use `sum_centerConfig_eq_zero` to remove mixed terms;
* convert real inner products in `EuclideanSpace` to coordinate sums.

Do not prove this by invoking a spectral decomposition.  It is a direct finite
sum identity and should remain independent of all eigenvalue machinery. -/
theorem classicalMDSMatrix_pairDist_eq_centered_gram
    {n d : Nat} (hn : 0 < n) (z : Config n d) (i j : Fin n) :
    classicalMDSMatrix (fun a b => ‖z a - z b‖) i j =
      ∑ k, centerConfig z i k * centerConfig z j k := by
  sorry

/-- The centered target-augmented perspective configuration has the radial
identity needed by the Quench nearest-neighbor engine.

The proof is short once `Fin.lastCases` reduces the reference coordinate and
the final target coordinate.  Use `norm_centerConfig_sub_centerConfig`; avoid
expanding the centroid. -/
theorem centeredAugmentedPerspectiveConfig_radial
    {Ωref : Type wr} {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (f : Model Q X) (i : Fin n) :
    ‖centeredAugmentedPerspectiveConfig ψ f_ref n ωref f i.castSucc -
        centeredAugmentedPerspectiveConfig ψ f_ref n ωref f (Fin.last n)‖ =
      ‖ψ (f_ref n ωref i) - ψ f‖ := by
  sorry

/-- A single population distance-realization assumption yields the exact Gram
identity currently supplied manually to the growing CMDS theorem.

Suggested proof route:
1. rewrite every population dissimilarity using `hrealize`;
2. apply `classicalMDSMatrix_pairDist_eq_centered_gram` to the uncentered
   augmented perspective configuration;
3. orient the resulting equality to match the existing `hzGram` interface.
The batch has size `n+1`, so positivity is discharged by `omega`. -/
theorem centeredAugmentedPerspectiveConfig_gram_eq
    {Ωref : Type wr} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    (n : Nat) (ωref : Ωref) (f : Model Q X) (i j : Fin (n + 1)) :
    (∑ k,
      centeredAugmentedPerspectiveConfig ψ f_ref n ωref f i k *
      centeredAugmentedPerspectiveConfig ψ f_ref n ωref f j k) =
      classicalMDSMatrix (responseDist (μbar n ωref f)) i j := by
  sorry

/-- Construct all population geometry consumed by growing Quench from the one
paper-facing distance-realization hypothesis.

When the two preceding obligations are completed, every preferred public
capstone can delete the separate `z`, Gram, and radial hypotheses and use this
constructor instead. -/
noncomputable def populationGeometry_of_responseRealization
    {Ωref : Type wr} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar) :
    AugmentedPopulationGeometry ψ f_ref μbar where
  config := centeredAugmentedPerspectiveConfig ψ f_ref
  gram_eq := centeredAugmentedPerspectiveConfig_gram_eq
    ψ f_ref μbar hrealize
  radial_eq := centeredAugmentedPerspectiveConfig_radial ψ f_ref

end DkpsQuench.Perfect
