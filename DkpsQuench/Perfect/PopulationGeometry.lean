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
finite-sum simplifier cannot see the scalar cancellation.

Implementation recipe (execute in this order):
1. Apply `funext`/`ext k` so the vector equality becomes a scalar equality in
   coordinate `k : Fin d`.
2. Unfold `centerConfig` and `configCentroid`; rewrite the finite sum of
   differences with `Finset.sum_sub_distrib`, and rewrite evaluation of a scalar
   multiple and a finite sum pointwise.
3. Reduce the constant-centroid sum to `(n : Real) * ((n : Real)⁻¹ * S)` using
   `Finset.sum_const`, `Finset.card_univ`, and `Fintype.card_fin`, where
   `S = ∑ i, z i k`.
4. Prove `(n : Real) ≠ 0` from `hn` using `exact_mod_cast` or
   `Nat.cast_ne_zero.mpr`, then simplify `(n : Real) * (n : Real)⁻¹`.
5. Finish the scalar identity with `ring` or `linarith` after the inverse
   cancellation.  Do not use a coordinate basis expansion before step 1.
-/
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
sum identity and should remain independent of all eigenvalue machinery.

Implementation recipe (execute in this order):
1. Let `c := centerConfig z`; rewrite every pairwise distance from `z` to `c`
   with `norm_centerConfig_sub_centerConfig`.
2. Record `hsum : ∑ a, c a = 0` from `sum_centerConfig_eq_zero hn z`; obtain the
   coordinate version `∑ a, c a k = 0` by applying `congrArg (fun v => v k)`.
3. Unfold `classicalMDSMatrix`, `doubleCenter`, `rowMean`, and `grandMean` only
   after introducing abbreviations for `‖c a‖ ^ 2` and
   `∑ k, c a k * c b k`; this keeps the generated goal readable.
4. Rewrite `‖c a - c b‖ ^ 2` as
   `‖c a‖ ^ 2 + ‖c b‖ ^ 2 - 2 * ⟪c a, c b⟫_ℝ` using the real inner-product
   norm identity.  Rewrite the inner product as the finite coordinate sum using
   the Euclidean-space inner-product lemma already imported by the Acharyya
   files.
5. Compute the row mean, column mean, and grand mean separately.  In each
   computation, distribute finite sums and kill mixed terms using the coordinate
   form of `hsum`; prove these as local `have` statements rather than one `simp`.
6. Substitute the three mean formulas into `doubleCenter`; the squared-norm
   terms cancel and the remaining factor `-(1/2) * (-2)` is one.  Close with
   `ring`.
7. If the inner-product-to-coordinate lemma is hard to locate, search for
   `real_inner`, `EuclideanSpace`, and `sum_mul` in the existing Gram-realization
   proofs.  Do not invoke eigenvalues or spectral decomposition.
-/
theorem classicalMDSMatrix_pairDist_eq_centered_gram
    {n d : Nat} (hn : 0 < n) (z : Config n d) (i j : Fin n) :
    classicalMDSMatrix (fun a b => ‖z a - z b‖) i j =
      ∑ k, centerConfig z i k * centerConfig z j k := by
  sorry

/-- The centered target-augmented perspective configuration has the radial
identity needed by the Quench nearest-neighbor engine.

The proof is short once `Fin.lastCases` reduces the reference coordinate and
the final target coordinate.  Use `norm_centerConfig_sub_centerConfig`; avoid
expanding the centroid.

Implementation recipe (execute in this order):
1. Unfold only `centeredAugmentedPerspectiveConfig` and
   `augmentedPerspectiveConfig`.
2. Rewrite the left side with `norm_centerConfig_sub_centerConfig`; this removes
   the centroid without any algebra.
3. Simplify `augmentedModelAt` at `i.castSucc` and `Fin.last n` using
   `Fin.lastCases`, `Fin.lastCases_last`, and the cast-successor simp lemmas.
4. The goal should become reflexive.  Finish with `simp [augmentedModelAt]`.
   If `simp` leaves a dependent-function cast, use `Fin.lastCases` on the index
   before simplifying; do not expand `configCentroid`.
-/
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
The batch has size `n+1`, so positivity is discharged by `omega`.

Implementation recipe (execute in this order):
1. Set `z := augmentedPerspectiveConfig ψ f_ref n ωref f` and note that the
   centered configuration in the goal is definitionally `centerConfig z`.
2. Apply `classicalMDSMatrix_pairDist_eq_centered_gram` to `z` with the batch
   size `n + 1`; discharge positivity by `omega`.
3. For every `a b : Fin (n+1)`, rewrite the dissimilarity in that theorem with
   `hrealize n ωref f a b`.
4. Unfold `z`, `augmentedPerspectiveConfig`, and `responseDist` only as needed
   to align the two sides; normally `simpa [z]` after rewriting is enough.
5. Orient the final equality with `.symm` if necessary because the public
   `gram_eq` field places the coordinate sum on the left.
-/
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
