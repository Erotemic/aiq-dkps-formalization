/-
Downstream wiring of the matrix-world spectral capstone into aligned CMDS
embeddings and the high-probability concentration chain.

This file connects the proved spectral bridge
(`Acharyya2025.MatrixPerturbation.exists_isometry_configError_le_of_entrywise_close`)
to the DKPS finite-sample concentration chain proved in `Acharyya2025.Bridge`,
producing an *aligned* CMDS spectral estimator whose `ConfigError` against the
population configuration is high-probability `configBound`-close.

The estimator `alignedSpectralConfig` is built by `Classical.choose` from the
capstone's existential alignment isometry `W`: whenever the alignment exists with
a given bound `c u`, the estimator achieves `ConfigError ≤ c u`; otherwise it
falls back to the raw sample spectral embedding.  This packaging makes the two
downstream consumer files (`DkpsQuench`, `Helm2025`) a one-application-deep honest
composition.

Contents:
* `symmetricDisMat_responseDist`, `symmetricDisMat_classicalMDSMatrix` — symmetry
  plumbing for the CMDS Gram matrix;
* `alignedSpectralConfig` and `configError_alignedSpectralConfig_le` — the
  choice-based aligned estimator and its defining property;
* `highProb_aligned_configError_of_entrywise_close` — the repaired (TRUE) version
  of the legacy unaligned CMDS-perturbation seam;
* `highProb_aligned_configError_of_response_mean` — the end-to-end
  response-mean → aligned `ConfigError` theorem, composing `Bridge.lean`'s HP
  chain with the capstone.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2024.Common
import Acharyya2025.Deterministic
import Acharyya2025.MathlibBridge
import Acharyya2025.OperatorBridge
import Acharyya2025.ConfigPerturbation
import Acharyya2025.MatrixPerturbation
import Acharyya2025.Bridge
import ForMathlib.MeasureTheory.CompactExists

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open Filter MeasureTheory

namespace Acharyya2025.AlignedPipeline

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.MatrixPerturbation

/-! ### (1) Symmetry plumbing -/

/--
The response-distance dissimilarity matrix is symmetric: its entries are
normalized norms `‖Xbar i - Xbar j‖`, symmetric in `i, j` via `norm_sub_rev`.

Internal helper (symmetry plumbing for the CMDS Gram matrix). Used so that the
sample CMDS matrices are Hermitian, which the spectral capstone requires.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- `Xbar` : the mean (vector-embedded) responses (one matrix per model).
-- Conclusion: the response-distance dissimilarity matrix is symmetric.
theorem symmetricDisMat_responseDist {n m p : Nat} (Xbar : Fin n → Mat m p) :
    SymmetricDisMat (responseDist Xbar) := by
  intro i j
  simp only [responseDist, responseDistEntry]
  rw [norm_sub_rev]

/--
The classical-MDS centered matrix of a symmetric dissimilarity matrix is
symmetric.

`classicalMDSMatrix D i j = -(1/2) · doubleCenter (D²) i j`, and
`doubleCenter A i j = A i j - rowMean A i - colMean A j + grandMean A`.  For the
squared matrix `A i j = (D i j)²`, symmetry of `D` gives `A i j = A j i`, so the
row means and column means swap, making `doubleCenter A` symmetric.

Internal helper (symmetry plumbing for the CMDS Gram matrix).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- `hD` : input dissimilarity matrix `D` is symmetric.
-- Conclusion: the classical-MDS (double-centered) matrix of `D` is symmetric.
theorem symmetricDisMat_classicalMDSMatrix {n : Nat} {D : DisMat n}
    (hD : SymmetricDisMat D) : SymmetricDisMat (classicalMDSMatrix D) := by
  classical
  -- abbreviation for the squared matrix (kept as a literal lambda).
  let A : DisMat n := fun i j => (D i j)^2
  -- The squared matrix is symmetric.
  have hAsym : ∀ i j : Fin n, A j i = A i j := by
    intro i j; show (D j i)^2 = (D i j)^2; rw [hD i j]
  -- row and column means swap under symmetry of `A`.
  have hrc : ∀ i : Fin n, rowMean A i = colMean A i := by
    intro i
    simp only [rowMean, colMean]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (hAsym i j).symm
  intro i j
  -- unfold `classicalMDSMatrix` and `doubleCenter`, then match symmetric pieces.
  show -(1 / 2 : Real) * doubleCenter A j i = -(1 / 2 : Real) * doubleCenter A i j
  simp only [doubleCenter]
  rw [hAsym j i, hrc i, hrc j]
  ring

/-! ### (2) The aligned estimator (choice-based) -/

/--
The alignment existential at sample `(u, ω)` for the CMDS spectral embedding of
`Dhat u ω`, compared against an external configuration `ψ` with bound `c u`.

This is exactly the existential produced by the matrix-world capstone
`exists_isometry_configError_le_of_entrywise_close`.

In the paper, `W` corresponds to the orthogonal alignment matrix `W*` of
Theorem 2 (the embedding is only identified up to an orthogonal transform). This
`AlignExists` predicate is a choice-free *device*: it asserts the mere existence
of such a `W` achieving the bound, without selecting one. EXTRA (implicit)
assumption beyond the paper: the formalization works in finite dimension `d`
(`hd : d ≤ n`) and packages the alignment as this explicit existential.
-/
-- `hd`    : target embedding dimension `d` is at most `n` (finite-dimensional).
-- `Dhat`  : sample dissimilarity matrix at budget index `u` and sample point `ω`.
-- `hsym`  : EXTRA assumption — each sample CMDS matrix is Hermitian (so it has a
--           real spectral decomposition); supplied automatically downstream.
-- `ψ`     : the population/target configuration.
-- `c u`   : the target error bound at budget `u`.
def AlignExists {n d : Nat} (hd : d ≤ n) {Ω : Type} (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (ψ : Config n d) (c : Nat → Real) (u : Nat) (ω : Ω) : Prop :=
  ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
    (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
    ConfigError
      (fun i => W (spectralConfig
          (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
          (opSym (hsym u ω)) hd i)) ψ ≤ c u

open Classical in
/--
The aligned CMDS spectral estimator.  When the alignment isometry exists (with
bound `c u`), apply the chosen isometry to the raw sample spectral embedding;
otherwise fall back to the raw embedding.

This is the formal counterpart of the paper's aligned sample embedding `ψ̂ W*`.
EXTRA (implicit) assumption beyond the paper: the isometry is selected via
`Classical.choose` (the noncomputable choice device); the falling-back branch is
a Lean technicality with no analogue in the prose.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
noncomputable def alignedSpectralConfig {n d : Nat} (hd : d ≤ n)
    {Ω : Type} (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (ψ : Config n d) (c : Nat → Real) (u : Nat) (ω : Ω) : Config n d :=
  if h : AlignExists hd Dhat hsym ψ c u ω
  then fun i => (Classical.choose h)
      (spectralConfig
        (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
        (opSym (hsym u ω)) hd i)
  else fun i => spectralConfig
      (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
      (opSym (hsym u ω)) hd i

/--
Defining property of the aligned estimator: when the alignment exists with bound
`c u`, the aligned estimator achieves `ConfigError ≤ c u`.

Internal helper: this is what makes the choice-based estimator usable — it
discharges the `Classical.choose` and exposes the achieved bound.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem configError_alignedSpectralConfig_le {n d : Nat} (hd : d ≤ n)
    {Ω : Type} (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)  -- EXTRA: sample CMDS matrix Hermitian
    (ψ : Config n d) (c : Nat → Real) (u : Nat) (ω : Ω)
    (h : AlignExists hd Dhat hsym ψ c u ω)  -- the alignment exists at bound `c u`
    -- Conclusion: the aligned estimator's `ConfigError` against `ψ` is `≤ c u`.
    :
    ConfigError (alignedSpectralConfig hd Dhat hsym ψ c u ω) ψ ≤ c u := by
  have hspec := (Classical.choose_spec h).2
  have heq : alignedSpectralConfig hd Dhat hsym ψ c u ω
      = fun i => (Classical.choose h)
          (spectralConfig
            (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
            (opSym (hsym u ω)) hd i) := by
    simp only [alignedSpectralConfig, dif_pos h]
  rw [heq]
  exact hspec

/--
**The aligned-estimator error event is exactly the alignment existential.**

The forward direction is the dite analysis: on the positive branch
`AlignExists` already holds; on the negative branch the estimator is the *raw*
spectral embedding, and a raw embedding satisfying the bound witnesses
`AlignExists` with `W = id`.  The backward direction is the defining property
`configError_alignedSpectralConfig_le`.

This eliminates the `Classical.choose` inside `alignedSpectralConfig` from any
measurability question about the error event: the event equals a set defined by
an existential over isometries, with no choice function in sight.

Internal helper (measurability-machinery seam): identifies the error event with
the choice-free `AlignExists`, enabling the measurability proof below.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem configError_alignedSpectralConfig_le_iff_alignExists {n d : Nat} (hd : d ≤ n)
    {Ω : Type} (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)  -- EXTRA: sample CMDS matrix Hermitian
    (ψ : Config n d) (c : Nat → Real) (u : Nat) (ω : Ω)
    -- Conclusion: the aligned error event equals the choice-free `AlignExists` event.
    :
    ConfigError (alignedSpectralConfig hd Dhat hsym ψ c u ω) ψ ≤ c u ↔
      AlignExists hd Dhat hsym ψ c u ω := by
  constructor
  · intro hle
    by_cases h : AlignExists hd Dhat hsym ψ c u ω
    · exact h
    · refine ⟨LinearMap.id, fun x y => rfl, ?_⟩
      have heq : alignedSpectralConfig hd Dhat hsym ψ c u ω
          = fun i => spectralConfig
              (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
              (opSym (hsym u ω)) hd i := by
        simp only [alignedSpectralConfig, dif_neg h]
      rw [heq] at hle
      simpa using hle
  · exact configError_alignedSpectralConfig_le hd Dhat hsym ψ c u ω

/--
**Measurability of the alignment existential.**

If the raw spectral embedding `ω ↦ spectralConfig … (Dhat u ω) …` is measurable
(coordinatewise), then the event `{ω | AlignExists …}` is measurable — with no
measurable selection of the alignment: the set of inner-product-preserving
continuous linear maps of `ℝ^d` is compact (closed and bounded in the
finite-dimensional operator space), so the existential is a compactly-quantified
constraint and `ForMathlib.measurableSet_exists_mem_le` applies.

Combined with `configError_alignedSpectralConfig_le_iff_alignExists`, this makes
the aligned-estimator error event measurable from the single honest primitive
"the raw spectral embedding is measurable in the sample".

Internal helper (measurability machinery). EXTRA (implicit) assumptions beyond
the paper: a `MeasurableSpace` structure on the sample space, the raw-spectral-
embedding measurability primitive `hmeas` (assumed, not derived — see below), and
the finite-dimensionality used to make the isometry set `S` compact. The paper
treats measurability informally.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem measurableSet_setOf_alignExists {n d : Nat} (hd : d ≤ n)
    {Ω : Type} [MeasurableSpace Ω] (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)  -- EXTRA: sample CMDS matrix Hermitian
    (ψ : Config n d) (c : Nat → Real) (u : Nat)
    -- EXTRA (assumed primitive): the raw sample spectral embedding is measurable
    -- in `ω`, coordinatewise. This is taken as a hypothesis, not proved.
    (hmeas : ∀ i : Fin n, Measurable (fun ω =>
      spectralConfig
        (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
        (opSym (hsym u ω)) hd i)) :
    -- Conclusion: the alignment-existence event `{ω | AlignExists …}` is measurable.
    MeasurableSet {ω | AlignExists hd Dhat hsym ψ c u ω} := by
  classical
  set spec : Ω → Fin n → EuclideanSpace ℝ (Fin d) := fun ω i =>
    spectralConfig
      (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
      (opSym (hsym u ω)) hd i with hspec
  -- The compact parameter set: inner-product-preserving continuous linear maps.
  set S : Set (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    {W | ∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ} with hSdef
  -- Rewrite the existential over linear maps as one over `S` (finite dimension:
  -- every linear map is continuous, and the coercions match pointwise).
  have hevent : {ω | AlignExists hd Dhat hsym ψ c u ω}
      = {ω | ∃ W ∈ S, (∑ i : Fin n, ‖W (spec ω i) - ψ i‖) ≤ c u} := by
    ext ω
    constructor
    · rintro ⟨W, hWinner, hWerr⟩
      refine ⟨LinearMap.toContinuousLinearMap W, fun x y => by simpa using hWinner x y, ?_⟩
      simpa [ConfigError, hspec] using hWerr
    · rintro ⟨W, hWS, hWerr⟩
      refine ⟨(W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)),
        fun x y => by simpa using hWS x y, ?_⟩
      simpa [ConfigError, hspec] using hWerr
  -- `S` is closed: an intersection of inner-product equation sets.
  have hSclosed : IsClosed S := by
    have hrw : S = ⋂ (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)),
        {W : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) |
          ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ} := by
      ext W; simp only [hSdef, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    refine isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (Continuous.inner ?_ ?_) continuous_const
    · exact (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d)) x).continuous
    · exact (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d)) y).continuous
  -- `S` is bounded: inner-product preservation forces operator norm `≤ 1`.
  have hSbounded : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d))) (r := 1)).subset ?_
    intro W hW
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hW x x]
    have hnorm : ‖W x‖ = ‖x‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    rw [hnorm, one_mul]
  have hScompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbounded
  -- The compactly-quantified existential is measurable.
  rw [hevent]
  refine ForMathlib.measurableSet_exists_mem_le hScompact (fun ω => ?_) (fun W _ => ?_) (c u)
  · -- Continuity in `W` of the error sum.
    refine Continuous.continuousOn ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact (((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d))
      (spec ω i)).continuous).sub continuous_const).norm
  · -- Measurability in `ω` of the error sum, from the raw-embedding measurability.
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((W.continuous.measurable.comp (hmeas i)).sub measurable_const).norm

/-! ### (3) High-probability aligned perturbation (repaired legacy seam) -/

/--
**Deterministic: entrywise CMDS-closeness implies the alignment existential.**

On any sample where the CMDS matrices are entrywise `rate u`-close, the
matrix-world capstone produces the aligning isometry achieving
`ConfigError ≤ configBound`.  This is the deterministic core of
`highProb_aligned_configError_of_entrywise_close`, extracted so the Quench
bridge can use the (directly measurable) entrywise event itself as its
high-probability sub-event — replacing the unprovable raw-embedding
measurability primitive `hmeas_spec`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem alignExists_of_entrywiseClose {Ω : Type}
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → DisMat n) (D : DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (disMatToMatrix (classicalMDSMatrix D)).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l, MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k) = classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hsmall : ∀ u, (n : Real) * rate u ≤ α / 2)
    (hpolar : ∀ u, (d : Real) * (4 * (n : Real) * ((n : Real) * rate u)^2 / α^2) ≤ 1/2)
    (u : Nat) (ω : Ω)
    (hω : Acharyya2025.Bridge.EntrywiseClose
      (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)) :
    AlignExists hd Dhat hsym ψ (fun u => configBound n d α Λ ((n : Real) * rate u)) u ω := by
  have hentry : ∀ i j,
      |disMatToMatrix (classicalMDSMatrix (Dhat u ω)) i j
          - disMatToMatrix (classicalMDSMatrix D) i j| ≤ rate u := fun i j => hω i j
  exact MatrixPerturbation.exists_isometry_configError_le_of_entrywise_close
    hd (disMatToMatrix (classicalMDSMatrix D))
    (disMatToMatrix (classicalMDSMatrix (Dhat u ω)))
    hB (hsym u ω) hrank hα_pos (hrate_nonneg u) hfloor hΛ hentry (hsmall u) (hpolar u) ψ hψ


/--
**Repaired aligned CMDS perturbation seam.**

Given a high-probability event that the sample CMDS matrices `classicalMDSMatrix
(Dhat u ω)` are entrywise `rate u`-close to the population CMDS matrix
`classicalMDSMatrix D` (whose Gram realization is the configuration `ψ`), the
aligned spectral estimator `alignedSpectralConfig` is high-probability
`configBound`-close to `ψ`.

This is the honest, TRUE replacement for the legacy unaligned
`cited_cmds_embedding_perturbation_from_centered_entrywise`: the conclusion now
carries the alignment isometry (baked into `alignedSpectralConfig`), and every
hypothesis matches the matrix-world capstone exactly.

This is the high-probability form of **Theorem 2** (the bound `‖ψ̂ W* − ψ‖ ≤ κ`
with high probability), assembled by feeding the entrywise CMDS-closeness event
(the high-probability input from **Theorem 1**) through the deterministic
configuration bound (Theorem 2's deterministic core, `configBound`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProb_aligned_configError_of_entrywise_close
    {Ω : Type} [MeasurableSpace Ω]                      -- EXTRA: measurable-space structure
    (P : Nat → MeasureTheory.Measure Ω)                 -- family of measures indexed by budget `u`
    {n d : Nat} (hd : d ≤ n)                            -- EXTRA: finite embedding dim `d ≤ n`
    (Dhat : Nat → Ω → DisMat n) (D : DisMat n)          -- sample vs population dissimilarity matrices
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)  -- EXTRA: sample CMDS matrix Hermitian
    -- Spectral structure of the population CMDS Gram matrix (Assumptions 1/2):
    (hB : (disMatToMatrix (classicalMDSMatrix D)).PosSemidef)   -- PSD
    (hrank : (disMatToMatrix (classicalMDSMatrix D)).rank ≤ d)  -- rank ≤ d
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)  -- eigenvalue floor α on top-d block
    (hΛ : ∀ l, MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)  -- eigenvalue cap Λ
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k) = classicalMDSMatrix D i j)  -- ψ is a Gram factor of the population CMDS matrix
    -- Rate / smallness side-conditions (per budget `u`):
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hsmall : ∀ u, (n : Real) * rate u ≤ α / 2)  -- EXTRA: numeric smallness of the perturbation
    (hpolar : ∀ u, (d : Real) * (4 * (n : Real) * ((n : Real) * rate u)^2 / α^2) ≤ 1/2)  -- EXTRA: numeric polar-factor condition
    -- Theorem 1 input: high-probability entrywise closeness of sample to population CMDS matrices.
    (hcenter : HighProbAtTop P (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)})) :
    -- Conclusion (high-probability Theorem 2): with high probability the aligned
    -- estimator's `ConfigError` against `ψ` is `≤ configBound …`.
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfig hd Dhat hsym ψ
          (fun u => configBound n d α Λ ((n : Real) * rate u)) u ω) ψ
        ≤ configBound n d α Λ ((n : Real) * rate u)}) := by
  refine HighProbAtTop.mono hcenter (fun u ω hω => ?_)
  -- The entrywise event is contained in the alignment-existence event (deterministic core);
  -- conclude via the aligned estimator's defining property.
  exact configError_alignedSpectralConfig_le hd Dhat hsym ψ
    (fun u => configBound n d α Λ ((n : Real) * rate u)) u ω
    (alignExists_of_entrywiseClose hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψ hψ
      rate hrate_nonneg hsmall hpolar u ω hω)

/-! ### (4) End-to-end response-mean → aligned ConfigError -/

/-- **Response-mean concentration to CMDS-entrywise closeness (high-probability).**
The `Bridge.lean` deterministic chain (response-mean → Frobenius → entrywise →
CMDS-entrywise), packaged to expose the CMDS-entrywise high-probability event
directly — the measurable sub-event the response-mean Quench capstones consume.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem highProb_cmdsEntrywise_of_response_mean
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → MeasureTheory.Measure Ω)
    {n m p : Nat} (hn : 0 < n)
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)
    (η R : Nat → Real)
    (hmean : HighProbAtTop P
      (fun u => {ω | Acharyya2025.Bridge.UniformResponseMeanClose (Xbar u ω) μ (η u)}))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j, |responseDist μ i j| ≤ R u) :
    HighProbAtTop P (fun u => {ω | Acharyya2025.Bridge.EntrywiseClose
      (classicalMDSMatrix (responseDist (Xbar u ω))) (classicalMDSMatrix (responseDist μ))
      (Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))}) := by
  set Dhat : Nat → Ω → DisMat n := fun u ω => responseDist (Xbar u ω) with hDhat
  set D : DisMat n := responseDist μ with hD
  have hfrob :
      HighProbAtTop P
        (fun u => {ω | frobSub (Dhat u ω) D
          ≤ Acharyya2025.Bridge.responseFrobRate n m (η u)}) := by
    simpa [Dhat, D] using
      Acharyya2025.Bridge.response_mean_close_hp_to_frob_hp P Xbar μ η hmean
  have hentry :
      HighProbAtTop P
        (fun u => {ω | Acharyya2025.Bridge.EntrywiseClose (Dhat u ω) D
          (Acharyya2025.Bridge.responseFrobRate n m (η u))}) :=
    Acharyya2025.Bridge.frob_close_hp_to_entrywise_close_hp P Dhat D
      (fun u => Acharyya2025.Bridge.responseFrobRate n m (η u)) hfrob
  refine HighProbAtTop.mono hentry (fun u ω hω => ?_)
  exact Acharyya2025.Bridge.entrywise_close_to_cmds_entrywise_close_of_bounded hn hω
    (fun i j => by simpa [Dhat] using hsample_bound u ω i j)
    (fun i j => by simpa [D] using hpopulation_bound u i j)


/--
A symmetric curried dissimilarity matrix induces a Hermitian Mathlib matrix
(over `ℝ`, Hermitian = symmetric).

Internal helper (Hermitian plumbing — discharges the `hsym` hypothesis above).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- `hD` : the dissimilarity matrix is symmetric.
-- Conclusion: its Mathlib-matrix realization is Hermitian.
theorem isHermitian_disMatToMatrix_of_symmetricDisMat {n : Nat} {D : DisMat n}
    (hD : SymmetricDisMat D) : (disMatToMatrix D).IsHermitian := by
  show Matrix.conjTranspose (disMatToMatrix D) = disMatToMatrix D
  ext i j
  simpa [Matrix.conjTranspose_apply, disMatToMatrix] using hD i j

/--
The CMDS matrix of a response-distance matrix induces a Hermitian Mathlib matrix.

Internal helper (Hermitian plumbing): supplies the `hsym` hypothesis
automatically for response-distance pipelines.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- `Xbar` : the mean (vector-embedded) responses.
-- Conclusion: the response-distance CMDS matrix is Hermitian.
theorem isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
    {n m p : Nat} (Xbar : Fin n → Mat m p) :
    (disMatToMatrix (classicalMDSMatrix (responseDist Xbar))).IsHermitian :=
  isHermitian_disMatToMatrix_of_symmetricDisMat
    (symmetricDisMat_classicalMDSMatrix (symmetricDisMat_responseDist Xbar))

/--
**End-to-end response-mean concentration to aligned CMDS `ConfigError`.**

Composing `Bridge.lean`'s proved high-probability chain
(response-mean → Frobenius → entrywise → CMDS-entrywise) with the matrix-world
spectral capstone (via `highProb_aligned_configError_of_entrywise_close`), a
high-probability uniform response-mean event yields a high-probability bound on
the aligned CMDS spectral `ConfigError` against the population configuration `ψ`.

The population CMDS Gram matrix is `classicalMDSMatrix (responseDist μ)`; the
sample estimator is built from `Dhat u ω := responseDist (Xbar u ω)`.  Hermitian-
ness of every sample CMDS matrix is supplied automatically (symmetry plumbing);
the remaining spectral hypotheses (PSD, rank, floor, cap, smallness, polar) are
exactly those of the capstone.

This is the response-mean-driven high-probability form of **Theorem 2**: it takes
a high-probability uniform response-mean event and emits the high-probability
aligned `ConfigError` bound, composing `Bridge.lean`'s concentration chain
(response-mean → Frobenius → entrywise → CMDS-entrywise, i.e. the Theorem 1
input) with the deterministic configuration bound.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem highProb_aligned_configError_of_response_mean
    {Ω : Type} [MeasurableSpace Ω]                      -- EXTRA: measurable-space structure
    (P : Nat → MeasureTheory.Measure Ω)
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)          -- EXTRA: finite embedding dim `d ≤ n`, nonempty index set
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)  -- sample mean responses vs population means
    -- Spectral structure of the population CMDS Gram matrix (Assumptions 1/2):
    (hB : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).PosSemidef)      -- PSD
    (hrank : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).rank ≤ d)     -- rank ≤ d
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)  -- eigenvalue floor α on top-d block
    (hΛ : ∀ l, MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)  -- eigenvalue cap Λ
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k)
      = classicalMDSMatrix (responseDist μ) i j)  -- ψ is a Gram factor of the population CMDS matrix
    -- Rate / smallness side-conditions (per budget `u`):
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u, 0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hsmall : ∀ u,
      (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u) ≤ α / 2)  -- EXTRA: numeric smallness
    (hpolar : ∀ u, (d : Real) *
      (4 * (n : Real) *
        ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))^2 / α^2)
        ≤ 1/2)  -- EXTRA: numeric polar-factor condition
    -- Theorem 1 input: high-probability uniform response-mean closeness at level `η u`.
    (hmean : HighProbAtTop P
      (fun u => {ω | Acharyya2025.Bridge.UniformResponseMeanClose (Xbar u ω) μ (η u)}))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R u)  -- uniform dissimilarity bound (sample)
    (hpopulation_bound : ∀ u i j, |responseDist μ i j| ≤ R u) :       -- uniform dissimilarity bound (population)
    -- Conclusion (high-probability Theorem 2, response-mean form): with high
    -- probability the aligned estimator's `ConfigError` against `ψ` is `≤ configBound …`.
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfig hd (fun u ω => responseDist (Xbar u ω))
          (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist (Xbar u ω))
          ψ
          (fun u => configBound n d α Λ
            ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))) u ω) ψ
        ≤ configBound n d α Λ
            ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))}) := by
  -- Set up the chain's intermediate objects.
  set Dhat : Nat → Ω → DisMat n := fun u ω => responseDist (Xbar u ω) with hDhat
  set D : DisMat n := responseDist μ with hD
  set rate : Nat → Real :=
    fun u => Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u) with hrate
  -- response-mean HP event → entrywise CMDS-matrix HP event (Bridge chain).
  have hcenter :
      HighProbAtTop P
        (fun u => {ω | Acharyya2025.Bridge.EntrywiseClose
          (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)}) :=
    highProb_cmdsEntrywise_of_response_mean P hn Xbar μ η R hmean
      hsample_bound hpopulation_bound
  -- Apply (3) with this CMDS-entrywise event.
  exact highProb_aligned_configError_of_entrywise_close P hd Dhat D
    (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist (Xbar u ω))
    hB hrank hα_pos hfloor hΛ ψ hψ rate hrate_nonneg hsmall hpolar hcenter

end Acharyya2025.AlignedPipeline
