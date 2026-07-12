/-
Compactness, boundedness, and response-regularity bridges for Perfect Quench.

The final theorem should not expose finite nets, covering-number certificates,
replicate-mean Lipschitz proofs, population-mean Lipschitz proofs, or response
norm envelopes as independent assumptions.  This module derives those objects
from finite-dimensional compactness and one pathwise raw-response Lipschitz
condition.
-/

import DkpsQuench.Perfect.RawResponses

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory ProbabilityTheory

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
open Acharyya2025.GrowingResponse

universe u v wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- A probability measure cannot live on an empty model type.

Suggested proof route: assume the model type is empty, identify `Set.univ` with
`∅`, and contradict `measure_univ = 1`.  This small lemma lets later existence
proofs choose an anchor model without adding a redundant `Nonempty` hypothesis
to every public capstone.

Implementation recipe (execute in this order):
1. Use `Classical.choice` only after constructing `Nonempty`; do not add a
   `Nonempty` hypothesis to the theorem.
2. Prove by contradiction with `not_nonempty_iff.mp` or `isEmpty_iff`; install
   the resulting `IsEmpty (Model Q X)` instance locally.
3. Show `(Set.univ : Set (Model Q X)) = ∅` by extensionality and eliminate the
   impossible element.
4. Rewrite `measure_univ` and `measure_empty` for `Pf`; the probability instance
   gives `Pf univ = 1`, contradicting `Pf ∅ = 0` by `norm_num`.
5. Prefer the existing theorem `MeasureTheory.nonempty_of_isProbabilityMeasure`
   if search finds it, but retain this wrapper so callers do not need to know the
   Mathlib theorem name.
-/
theorem nonempty_model_of_probability
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf] :
    Nonempty (Model Q X) := by
  sorry

/-- A population response map on a finite model class has a uniform norm
bound automatically.

Use the maximum of the finite set of norms, enlarged by zero.  This theorem
removes the explicit population response envelope from the finite-model final
interface.

Implementation recipe (execute in this order):
1. Work classically and define the finite set
   `S := Finset.univ.image (fun f => ‖μmodel f‖)`.
2. Choose `B := max 0 (S.max' hS)` when the model type is nonempty.  Handle the
   empty-model branch separately with `B := 0`; no probability measure is
   available in this theorem to rule emptiness out.
3. Prove `0 ≤ B` by `le_max_left`.
4. For arbitrary `f`, show `‖μmodel f‖ ∈ S`, apply `Finset.le_max'`, and then
   compose with `le_max_right`.
5. An alternative shorter route is `Finite.exists_le` on the finite range of the
   norm.  Do not introduce an arbitrary default model into the theorem
   signature.
-/
theorem exists_populationMean_norm_bound_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μmodel : Model Q X → Acharyya2024.Mat m p) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖μmodel f‖ ≤ B := by
  sorry

/-- Pathwise raw-response Lipschitzness passes to the concrete replicate mean.

Expand `modelReplicateMean`, apply the norm-of-sum bound, and use
`RawResponseLipschitz.bound` termwise.  Split the zero-replicate case from the
positive case: the average is definitionally zero when there are no indices,
while the positive case permits cancellation of the replicate count.  Keep this
proof independent of probability and integration.

Implementation recipe (execute in this order):
1. Unfold `modelReplicateMean` and `replicateMean`; set `r := replicates n`.
2. Split on `r = 0`.  In the zero branch, eliminate every `Fin 0` sum and close
   with `simp [r, replicateMean]`.
3. In the positive branch, rewrite the difference of averages as the average of
   pointwise differences using `Finset.sum_sub_distrib` and scalar-linearity.
4. Apply `norm_smul_le`, `norm_sum_le`, and `Hlip.bound n f g k ω` termwise.
5. Replace the sum of the constant bound by
   `(r : Real) * (L * ‖ψ f - ψ g‖)` using `Finset.sum_const` and
   `Fintype.card_fin`; cancel the averaging factor from the positive branch.
6. Finish the scalar coefficient with `field_simp`/`ring_nf`, using
   `Hlip.constant_nonneg` only for monotonicity.  No measure or expectation
   should appear.
-/
theorem modelReplicateMean_lipschitz_of_raw
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (L : Real)
    (Hlip : RawResponseLipschitz ψ replicates Y L)
    (n : Nat) (ω : Ωresp) (f g : Model Q X) :
    ‖modelReplicateMean replicates Y n ω f -
        modelReplicateMean replicates Y n ω g‖ ≤
      L * ‖ψ f - ψ g‖ := by
  sorry

/-- Pathwise raw-response Lipschitzness passes to the population mean.

Suggested proof route for a weaker agent:

1. identify each coordinate of `μmodel f - μmodel g` with the integral of
   `Y f - Y g` using `RawIIDResponseModel.mean_entry`;
2. package the coordinate equalities as a Bochner-integral equality;
3. apply `norm_integral_le_of_norm_le_const` to the pathwise Lipschitz bound;
4. simplify the probability-space mass to one.

Do not assume population Lipschitzness separately in a final theorem; this is
exactly the bridge that derives it.

Implementation recipe (execute in this order):
1. Fix `n f g`.  Use `Hraw.mean_entry n f 0` and `Hraw.mean_entry n g 0` for one
   replicate index; obtain that index from `Hraw.replicates_pos n` via
   `Fin.ofNat'` or `Fin.mk 0`.
2. Prove a matrix-valued Bochner-integral identity
   `μmodel f - μmodel g = ∫ ω, (Y n f k ω - Y n g k ω) ∂μresp n` by extensionality
   over matrix coordinates and the two `mean_entry` equalities.
3. Establish integrability of the difference from `Hraw.memLp_two ...` using
   `MemLp.integrable` and `Integrable.sub`.
4. Apply `norm_integral_le_of_norm_le_const` (or `norm_integral_le_of_norm_le`) to
   `Hlip.bound n f g k ω`.
5. Simplify the integral of the constant with `measure_univ` under
   `Hraw.probability n`; the result is exactly
   `L * ‖ψ f - ψ g‖`.
6. If the direct Bochner identity is awkward, prove the norm inequality
   coordinatewise and use the finite-dimensional matrix norm API, but do not add
   population Lipschitzness as a new hypothesis.
-/
theorem populationMean_lipschitz_of_raw
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (L : Real)
    (Hlip : RawResponseLipschitz ψ replicates Y L)
    (n : Nat) (f g : Model Q X) :
    ‖μmodel f - μmodel g‖ ≤ L * ‖ψ f - ψ g‖ := by
  sorry

/-- Construct the two regularity certificates used by finite-net extension from
one pathwise raw-response Lipschitz condition.

The sample and population constants are both the same fixed `L`.  This theorem
is the intended constructor used by the infinite-model capstone.

Implementation recipe (execute in this order):
1. Refine the `UniformModelResponseRegularity` structure with both constants
   equal to `fun _ => L`.
2. Fill `sample_nonneg` and `population_nonneg` with
   `Hlip.constant_nonneg`.
3. Fill `sample_lipschitz` by exact application of
   `modelReplicateMean_lipschitz_of_raw`.
4. Fill `population_lipschitz` by exact application of
   `populationMean_lipschitz_of_raw`; all stage arguments are explicit, so use
   named arguments if elaboration chooses the wrong `n`.
5. This theorem should contain no new estimates.  If a field does not close by
   `exact`, repair the preceding bridge theorem rather than duplicating its proof.
-/
theorem uniformModelResponseRegularity_of_raw_lipschitz
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (L : Real)
    (Hlip : RawResponseLipschitz ψ replicates Y L) :
    UniformModelResponseRegularity ψ
      (modelReplicateMean replicates Y) μmodel
      (fun _ => L) (fun _ => L) := by
  sorry

/-- Compact perspective range and population Lipschitzness imply a population
response norm envelope.

Choose an anchor model using `nonempty_model_of_probability`; compactness gives
a perspective norm bound.  Then compare every population response with the
anchor response and use the Lipschitz estimate.  The returned bound may be very
loose; its purpose is to eliminate a caller-visible envelope hypothesis.

Implementation recipe (execute in this order):
1. Obtain an anchor `f0 : Model Q X` from `nonempty_model_of_probability Pf`.
2. Obtain `Bψ ≥ 0` with `∀ f, ‖ψ f‖ ≤ Bψ` from
   `exists_perspective_norm_bound_of_isCompact_range ψ hcompact`.
3. For arbitrary `f`, write
   `‖μmodel f‖ ≤ ‖μmodel f - μmodel f0‖ + ‖μmodel f0‖` using
   `norm_le_norm_sub_add` or the triangle inequality.
4. Apply `hμlip f f0`, then bound
   `‖ψ f - ψ f0‖ ≤ ‖ψ f‖ + ‖ψ f0‖ ≤ 2 * Bψ`.
5. Choose `B := max 0 (L * (2 * Bψ) + ‖μmodel f0‖)`; use `hL` and the norm
   bounds to prove every response norm is below `B`.
6. Keep the constant loose.  The purpose is existence and hypothesis removal,
   not a sharp envelope.
-/
theorem exists_populationMean_norm_bound_of_compact_lipschitz
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ))
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (L : Real) (hL : 0 ≤ L)
    (hμlip : ∀ f g,
      ‖μmodel f - μmodel g‖ ≤ L * ‖ψ f - ψ g‖) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖μmodel f‖ ≤ B := by
  sorry

/-- Polynomial finite covers for a compact subset of finite-dimensional
Euclidean space, with centers pulled back to models.

A suitable proof can use Mathlib's total-boundedness API followed by a bounded
box grid, or an existing covering-number theorem if one is available.  The
important conclusion is the exponent `d`; the constant is existential and may
absorb norm equivalences and the diameter of the compact range.

The `max 1 ρ⁻¹` form handles large radii and avoids separate early-stage cases.

Implementation recipe (execute in this order):
1. Move from models to the compact set `K := Set.range ψ ⊆ EuclideanSpace Real
   (Fin d)`; use `hcompact.isTotallyBounded` to obtain finite covers for every
   positive radius.
2. To obtain the polynomial cardinality, enclose `K` in a cube
   `[-B,B]^d` using a norm bound from compactness.
3. For `0 < ρ ≤ 1`, build a coordinate grid with mesh comparable to
   `ρ / sqrt d`; prove every point of the cube is within `ρ` of a grid point and
   bound the grid cardinality by `C * ρ⁻¹ ^ d`.
4. For `ρ > 1`, use one fixed center (or the total-boundedness cover) and absorb
   the finite early-radius cost into `C`; this is why the statement uses
   `max 1 ρ⁻¹`.
5. Pull each selected grid/cover point in `K` back to a model using its range
   witness, form a `Finset (Model Q X)`, and prove `PerspectiveFiniteCover`.
6. Isolate the Euclidean grid lemma as a local helper if Mathlib lacks an exact
   covering-number theorem.  Search anchors: `IsCompact.isTotallyBounded`,
   `Metric.isCompact_iff_totallyBounded_isComplete`, `Finset.pi`, and existing
   finite-dimensional entropy lemmas.
7. Do not expose the constructed grid or its constants in the final theorem.
-/
theorem exists_polynomial_perspective_covers_of_isCompact_range
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ)) :
    ∃ C : Real, 0 ≤ C ∧ ∀ ρ : Real, 0 < ρ →
      ∃ centers : Finset (Model Q X),
        PerspectiveFiniteCover ψ ρ centers ∧
        ((centers.card : Nat) : Real) ≤ C * (max 1 ρ⁻¹) ^ d := by
  sorry

/-- Turn polynomial covers at arbitrary radii into a coherent growing finite
net for a prescribed shrinking radius sequence.

Use classical choice stage-by-stage on
`exists_polynomial_perspective_covers_of_isCompact_range`.  No nesting of the
nets is required by the later concentration proof.

Implementation recipe (execute in this order):
1. Obtain `C` and the radius-by-radius cover theorem from
   `exists_polynomial_perspective_covers_of_isCompact_range ψ hcompact`.
2. For each `n`, apply that theorem to `radius n` and `hradiusPos n`; use
   classical choice to select `centers n` and its cover/cardinality proofs.
3. Define `net.radius := radius`, `net.centers := centers`, and fill
   `radius_pos`, `radius_zero`, and `covers` directly.
4. Return the same `C`; the cardinality field is exactly the selected stagewise
   bound, and `net.radius n = radius n` is `rfl`.
5. Use `choose centers hcover hcard` or nested `Classical.choose`; no coherence
   or nesting of centers is required.
-/
theorem exists_growingPerspectiveNet_with_polynomial_card
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ))
    (radius : Nat → Real)
    (hradiusPos : ∀ n, 0 < radius n)
    (hradiusZero : Tendsto radius atTop (𝓝 0)) :
    ∃ net : GrowingPerspectiveNet ψ, ∃ C : Real,
      0 ≤ C ∧
      (∀ n, ((net.centers n).card : Real) ≤
        C * (max 1 (radius n)⁻¹) ^ d) ∧
      (∀ n, net.radius n = radius n) := by
  sorry

end DkpsQuench.Perfect
