/-
Shared finite-dimensional definitions for the Acharyya DKPS foundation scaffolds.

This file intentionally contains definitions only. The two paper-specific libraries
use `sorry` for unfinished proof obligations rather than declaration-level
assumptions, so `#print axioms` on scaffold theorems exposes only the usual
trusted Lean/Mathlib basis plus any completed dependencies, while `grep sorry`
shows the open work directly.
-/

import Mathlib
import Acharyya2024.WellKnown

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2024

/-- Vector space used for response embeddings or model embeddings. -/
abbrev Rvec (d : Nat) := EuclideanSpace Real (Fin d)

/-- A row-stacked matrix represented as a Euclidean vector over finite indices. -/
abbrev Mat (m p : Nat) := EuclideanSpace Real (Fin m × Fin p)

/-- Curried dissimilarity matrix on `n` objects. -/
abbrev DisMat (n : Nat) := Fin n → Fin n → Real

/-- A finite model configuration: one vector per model. -/
abbrev Config (n d : Nat) := Fin n → Rvec d

/-- Subsequences of natural numbers. -/
def Subseq (u : Nat → Nat) : Prop := StrictMono u

/-- Frobenius norm squared of a dissimilarity matrix. -/
noncomputable def frobSq {n : Nat} (A : DisMat n) : Real :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j)^2

/-- Frobenius norm of a dissimilarity matrix. -/
noncomputable def frob {n : Nat} (A : DisMat n) : Real :=
  Real.sqrt (frobSq A)

/-- Frobenius norm of a difference of dissimilarity matrices. -/
noncomputable def frobSub {n : Nat} (A B : DisMat n) : Real :=
  frob (fun i j => A i j - B i j)

/-- Raw-stress objective for metric multidimensional scaling. -/
noncomputable def rawStress (n d : Nat) (Δ : DisMat n) (z : Config n d) : Real :=
  ∑ i : Fin n, ∑ j : Fin n, (‖z i - z j‖ - Δ i j)^2

/-- Set of raw-stress minimizers. This encodes the non-uniqueness of MDS. -/
def MDS (n d : Nat) (Δ : DisMat n) : Set (Config n d) :=
  { z | ∀ z' : Config n d, rawStress n d Δ z ≤ rawStress n d Δ z' }

/-- Pairwise Euclidean distance induced by a configuration. -/
noncomputable def pairDist {n d : Nat} (z : Config n d) (i j : Fin n) : Real :=
  ‖z i - z j‖

/-- Absolute error in a single pairwise distance. -/
noncomputable def pairDistErr {n d : Nat} (z z' : Config n d) (i j : Fin n) : Real :=
  |pairDist z i j - pairDist z' i j|

/-- Convergence in probability to a fixed target. -/
def ConvergesInProbability {Ω α : Type} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) (X : Nat → Ω → α) (x : α) : Prop :=
  ∀ ε : Real, 0 < ε →
    Tendsto (fun n => P {ω | dist (X n ω) x > ε}) atTop (𝓝 0)

/-- Convergence in probability to zero. -/
def ConvergesInProbabilityZero {Ω α : Type} [MeasurableSpace Ω] [PseudoMetricSpace α]
    [Zero α] (P : Measure Ω) (X : Nat → Ω → α) : Prop :=
  ConvergesInProbability P X 0

/-- High-probability events along a natural-number asymptotic. -/
def HighProbAtTop {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) (E : Nat → Set Ω) : Prop :=
  ∀ δ : ENNReal, 0 < δ → ∃ N : Nat, ∀ n > N, P n (E n) ≥ 1 - δ

/-- A generic alignment error for configurations, leaving the transformation class abstract. -/
noncomputable def ConfigError {n d : Nat} (ψhat ψ : Config n d) : Real :=
  ∑ i : Fin n, ‖ψhat i - ψ i‖

/--
High-probability events are monotone under pointwise event inclusion.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem HighProbAtTop.mono {Ω : Type} [MeasurableSpace Ω]
    {P : Nat → Measure Ω} {E F : Nat → Set Ω}
    (hE : HighProbAtTop P E)
    (h_subset : ∀ n, E n ⊆ F n) :
    HighProbAtTop P F := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hE δ hδ
  exact ⟨N, fun n hn => (hN n hn).trans (MeasureTheory.measure_mono (h_subset n))⟩

/--
High-probability metric error bounds with deterministic rate tending to zero
imply convergence in probability.

This wraps the paper-independent real-valued probability lemma in
`Acharyya2024.WellKnown` into the `ConvergesInProbability` interface used by the
DKPS scaffolds.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem ConvergesInProbability.of_highProb_dist_le_rate
    {Ω α : Type} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Nat → Ω → α)
    (x : α)
    (rate : Nat → Real)
    (hgood_meas :
      ∀ n, MeasurableSet {ω | |dist (X n ω) x| ≤ rate n})
    (hrate : Tendsto rate atTop (𝓝 0))
    (hgood :
      HighProbAtTop (fun _n : Nat => P)
        (fun n => {ω | dist (X n ω) x ≤ rate n})) :
    ConvergesInProbability P X x := by
  intro ε hε
  have h :=
    tendsto_measure_abs_gt_zero_of_highProb_abs_le_rate P
    (fun n ω => dist (X n ω) x) rate hgood_meas hrate
    (HighProbAtTop.mono hgood
      (fun n ω hω => by
        simpa [abs_of_nonneg dist_nonneg] using hω))
  simpa [abs_of_nonneg dist_nonneg] using h ε hε

/--
Each component error is bounded by the total configuration error.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem norm_config_le_ConfigError {n d : Nat} (ψhat ψ : Config n d) (i : Fin n) :
    ‖ψhat i - ψ i‖ ≤ ConfigError ψhat ψ := by
  classical
  unfold ConfigError
  exact Finset.single_le_sum (fun j _ => norm_nonneg (ψhat j - ψ j)) (Finset.mem_univ i)

/--
Every entry of a dissimilarity matrix is bounded by its Frobenius norm.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_entry_le_frob {n : Nat} (A : DisMat n) (i j : Fin n) :
    |A i j| ≤ frob A := by
  have hsq_entry_le_row :
      (A i j)^2 ≤ ∑ j' : Fin n, (A i j')^2 :=
    Finset.single_le_sum (fun j' _ => sq_nonneg (A i j')) (Finset.mem_univ j)
  have hsq_entry_le_total :
      (A i j)^2 ≤ ∑ i' : Fin n, ∑ j' : Fin n, (A i' j')^2 := by
    exact hsq_entry_le_row.trans
      (Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg (A i' j'))
        (Finset.mem_univ i))
  unfold frob frobSq
  exact Real.le_sqrt_of_sq_le (by simpa [sq_abs] using hsq_entry_le_total)

/--
Every entrywise difference is bounded by the Frobenius norm of the matrix
difference.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_entry_sub_le_frobSub {n : Nat} (A B : DisMat n) (i j : Fin n) :
    |A i j - B i j| ≤ frobSub A B := by
  simpa [frobSub] using abs_entry_le_frob (fun i j => A i j - B i j) i j

/-! ## Response-matrix dissimilarities -/

/--
Paper dissimilarity entry built from row-stacked response matrices.

The paper writes this as `(1 / m) ‖Xbar_i - Xbar_i'‖_F`; Lean's
`EuclideanSpace` norm is the corresponding finite Frobenius/Euclidean norm on
the row-stacked matrix representation.
-/
noncomputable def responseDistEntry {n m p : Nat} (Xbar : Fin n → Mat m p)
    (i j : Fin n) : Real :=
  ((m : Real)⁻¹) * ‖Xbar i - Xbar j‖

/-- Curried dissimilarity matrix built from response matrices. -/
noncomputable def responseDist {n m p : Nat} (Xbar : Fin n → Mat m p) : DisMat n :=
  fun i j => responseDistEntry Xbar i j

/--
Deterministic Appendix A.2 inequality for one dissimilarity entry.

This is the bridge from response-matrix estimation error to distance-matrix
estimation error before the probabilistic Markov/union-bound step.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_responseDistEntry_sub_responseDistEntry_le
    {n m p : Nat} (Xbar μ : Fin n → Mat m p) (i j : Fin n) :
    |responseDistEntry Xbar i j - responseDistEntry μ i j|
      ≤ ((m : Real)⁻¹) * (‖Xbar i - μ i‖ + ‖Xbar j - μ j‖) := by
  have hm_nonneg : 0 ≤ ((m : Real)⁻¹) := by
    exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le m)
  simpa [responseDistEntry] using
    abs_mul_norm_sub_sub_le_mul_norm_sub_add hm_nonneg
      (Xbar i) (Xbar j) (μ i) (μ j)

/--
Frobenius distance between two response-distance matrices is controlled by the
sum of the per-model response-matrix errors.

This is a finite-dimensional deterministic reduction used before the
probabilistic part of Theorem 2.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem frobSub_responseDist_le_sum_errors
    {n m p : Nat} (Xbar μ : Fin n → Mat m p) :
    frobSub (responseDist Xbar) (responseDist μ)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          ((m : Real)⁻¹) * (‖Xbar i - μ i‖ + ‖Xbar j - μ j‖) := by
  classical
  let diff : Fin n × Fin n → Real :=
    fun ij => responseDistEntry Xbar ij.1 ij.2 - responseDistEntry μ ij.1 ij.2
  have h_l2_l1 : Real.sqrt (∑ ij : Fin n × Fin n, (diff ij)^2)
      ≤ ∑ ij : Fin n × Fin n, |diff ij| :=
    sqrt_sum_sq_le_sum_abs diff
  have h_entries :
      (∑ ij : Fin n × Fin n, |diff ij|)
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            ((m : Real)⁻¹) * (‖Xbar i - μ i‖ + ‖Xbar j - μ j‖) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ =>
        abs_responseDistEntry_sub_responseDistEntry_le Xbar μ i j
  calc
    frobSub (responseDist Xbar) (responseDist μ)
        = Real.sqrt (∑ i : Fin n, ∑ j : Fin n, (diff (i, j))^2) := by
          simp [frobSub, frob, frobSq, responseDist, diff]
    _ = Real.sqrt (∑ ij : Fin n × Fin n, (diff ij)^2) := by
          rw [Fintype.sum_prod_type]
    _ ≤ ∑ ij : Fin n × Fin n, |diff ij| := h_l2_l1
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          ((m : Real)⁻¹) * (‖Xbar i - μ i‖ + ‖Xbar j - μ j‖) := h_entries

/--
Uniform response-matrix error gives an explicit Frobenius bound for the induced
dissimilarity matrices.

This is a quantitative deterministic version of the paper's Appendix A.2
reduction.  It is deliberately stated without probability: probabilistic
concentration theorems can prove the hypothesis event and then use this lemma to
propagate that event to the distance-matrix layer.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem frobSub_responseDist_le_of_uniform_errors
    {n m p : Nat} (Xbar μ : Fin n → Mat m p) {η : Real}
    (hη : ∀ i : Fin n, ‖Xbar i - μ i‖ ≤ η) :
    frobSub (responseDist Xbar) (responseDist μ)
      ≤ ((n : Real) * (n : Real)) * (((m : Real)⁻¹) * (2 * η)) := by
  have hm_inv_nonneg : 0 ≤ ((m : Real)⁻¹) :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le m)
  calc
    frobSub (responseDist Xbar) (responseDist μ)
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            ((m : Real)⁻¹) * (‖Xbar i - μ i‖ + ‖Xbar j - μ j‖) :=
          frobSub_responseDist_le_sum_errors Xbar μ
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((m : Real)⁻¹) * (2 * η) := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (by linarith [hη i, hη j]) hm_inv_nonneg
    _ = ((n : Real) * (n : Real)) * (((m : Real)⁻¹) * (2 * η)) := by
          simp [mul_assoc]

end Acharyya2024
