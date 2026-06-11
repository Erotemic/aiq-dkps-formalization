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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2024.Common
import Acharyya2025.Deterministic
import Acharyya2025.MathlibBridge
import Acharyya2025.OperatorBridge
import Acharyya2025.ConfigPerturbation
import Acharyya2025.MatrixPerturbation
import Acharyya2025.Bridge

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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
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
-/
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem configError_alignedSpectralConfig_le {n d : Nat} (hd : d ≤ n)
    {Ω : Type} (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (ψ : Config n d) (c : Nat → Real) (u : Nat) (ω : Ω)
    (h : AlignExists hd Dhat hsym ψ c u ω) :
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

/-! ### (3) High-probability aligned perturbation (repaired legacy seam) -/

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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem highProb_aligned_configError_of_entrywise_close
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → MeasureTheory.Measure Ω)
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
    (hcenter : HighProbAtTop P (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)})) :
    HighProbAtTop P (fun u => {ω |
      ConfigError
        (alignedSpectralConfig hd Dhat hsym ψ
          (fun u => configBound n d α Λ ((n : Real) * rate u)) u ω) ψ
        ≤ configBound n d α Λ ((n : Real) * rate u)}) := by
  refine HighProbAtTop.mono hcenter (fun u ω hω => ?_)
  -- The entrywise event gives entrywise closeness of the Mathlib matrices.
  have hentry : ∀ i j,
      |disMatToMatrix (classicalMDSMatrix (Dhat u ω)) i j
          - disMatToMatrix (classicalMDSMatrix D) i j| ≤ rate u := by
    intro i j
    -- `disMatToMatrix` entries are definitionally the curried entries.
    exact hω i j
  -- The Gram realization hypothesis transported to `disMatToMatrix B`.
  have hψ' : ∀ i j, (∑ k, ψ i k * ψ j k)
      = disMatToMatrix (classicalMDSMatrix D) i j := hψ
  -- Apply the matrix-world capstone to produce the alignment existential.
  have hcap := MatrixPerturbation.exists_isometry_configError_le_of_entrywise_close
    hd (disMatToMatrix (classicalMDSMatrix D))
    (disMatToMatrix (classicalMDSMatrix (Dhat u ω)))
    hB (hsym u ω) hrank hα_pos
    (hrate_nonneg u) hfloor hΛ hentry (hsmall u) (hpolar u)
    ψ hψ'
  -- The capstone's existential is exactly `AlignExists` at this bound.
  have hexists : AlignExists hd Dhat hsym ψ
      (fun u => configBound n d α Λ ((n : Real) * rate u)) u ω := hcap
  -- Conclude via the estimator's defining property.
  exact configError_alignedSpectralConfig_le hd Dhat hsym ψ
    (fun u => configBound n d α Λ ((n : Real) * rate u)) u ω hexists

/-! ### (4) End-to-end response-mean → aligned ConfigError -/

/--
A symmetric curried dissimilarity matrix induces a Hermitian Mathlib matrix
(over `ℝ`, Hermitian = symmetric).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem isHermitian_disMatToMatrix_of_symmetricDisMat {n : Nat} {D : DisMat n}
    (hD : SymmetricDisMat D) : (disMatToMatrix D).IsHermitian := by
  show Matrix.conjTranspose (disMatToMatrix D) = disMatToMatrix D
  ext i j
  simpa [Matrix.conjTranspose_apply, disMatToMatrix] using hD i j

/--
The CMDS matrix of a response-distance matrix induces a Hermitian Mathlib matrix.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem highProb_aligned_configError_of_response_mean
    {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → MeasureTheory.Measure Ω)
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Mat m p) (μ : Fin n → Mat m p)
    (hB : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix (responseDist μ))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l, MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)
    (ψ : Config n d)
    (hψ : ∀ i j, (∑ k, ψ i k * ψ j k)
      = classicalMDSMatrix (responseDist μ) i j)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u, 0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hsmall : ∀ u,
      (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u) ≤ α / 2)
    (hpolar : ∀ u, (d : Real) *
      (4 * (n : Real) *
        ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))^2 / α^2)
        ≤ 1/2)
    (hmean : HighProbAtTop P
      (fun u => {ω | Acharyya2025.Bridge.UniformResponseMeanClose (Xbar u ω) μ (η u)}))
    (hsample_bound : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j, |responseDist μ i j| ≤ R u) :
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
  -- response-mean HP event → Frobenius HP event.
  have hfrob :
      HighProbAtTop P
        (fun u => {ω | frobSub (Dhat u ω) D
          ≤ Acharyya2025.Bridge.responseFrobRate n m (η u)}) := by
    simpa [Dhat, D] using
      Acharyya2025.Bridge.response_mean_close_hp_to_frob_hp P Xbar μ η hmean
  -- Frobenius HP event → entrywise distance HP event.
  have hentry :
      HighProbAtTop P
        (fun u => {ω | Acharyya2025.Bridge.EntrywiseClose (Dhat u ω) D
          (Acharyya2025.Bridge.responseFrobRate n m (η u))}) :=
    Acharyya2025.Bridge.frob_close_hp_to_entrywise_close_hp P Dhat D
      (fun u => Acharyya2025.Bridge.responseFrobRate n m (η u)) hfrob
  -- entrywise distance HP event → entrywise CMDS-matrix HP event.
  have hcenter :
      HighProbAtTop P
        (fun u => {ω | Acharyya2025.Bridge.EntrywiseClose
          (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)}) := by
    refine HighProbAtTop.mono hentry (fun u ω hω => ?_)
    exact Acharyya2025.Bridge.entrywise_close_to_cmds_entrywise_close_of_bounded hn hω
      (fun i j => by simpa [Dhat] using hsample_bound u ω i j)
      (fun i j => by simpa [D] using hpopulation_bound u i j)
  -- Apply (3) with this CMDS-entrywise event.
  exact highProb_aligned_configError_of_entrywise_close P hd Dhat D
    (fun u ω => isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist (Xbar u ω))
    hB hrank hα_pos hfloor hΛ ψ hψ rate hrate_nonneg hsmall hpolar hcenter

end Acharyya2025.AlignedPipeline
