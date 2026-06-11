/-
Pipeline for the real classical-MDS/spectral perturbation proof.

This file is intentionally a map between "worlds":

1. DKPS/CMDS world:
   curried dissimilarity matrices, double-centering, `classicalMDSMatrix`.
2. Mathlib matrix world:
   `Matrix (Fin n) (Fin n) ℝ`, symmetry, Frobenius/entrywise/operator bounds.
3. Spectral world:
   eigengaps, invariant subspaces, Davis-Kahan perturbation.
4. Configuration world:
   Euclidean configurations, Gram matrices, Procrustes/alignment error.

The elementary representation bridges are proved in `MathlibBridge`.  The hard
spectral facts are theorem-shaped `sorry`s with citations and deliberately
isolated statements, so replacing them can proceed one stage at a time.
-/

import Acharyya2025.MathlibBridge
import Acharyya2025.Bridge
import Acharyya2025.GramRealization

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2025.SpectralPipeline

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.Bridge

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## Configuration/Gram side -/

/-- Gram matrix of a finite Euclidean configuration. -/
noncomputable def configGram {n d : Nat} (ψ : Config n d) : DisMat n :=
  fun i j => ∑ k : Fin d, (ψ i k) * (ψ j k)

/-- A configuration realizes a CMDS matrix when its Gram matrix is the CMDS matrix. -/
def GramRealizesCMDS {n d : Nat} (D : DisMat n) (ψ : Config n d) : Prop :=
  ∀ i j : Fin n, configGram ψ i j = classicalMDSMatrix D i j

/--
The Gram matrix of a real configuration is symmetric.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem symmetric_configGram {n d : Nat} (ψ : Config n d) :
    SymmetricDisMat (configGram ψ) := by
  intro i j
  simp [configGram, mul_comm]

/-! ## Pipeline stage hypotheses -/

/--
The population CMDS matrix has the spectral structure needed for a `d`-dimensional
classical-MDS embedding: positive semidefiniteness and rank at most `d`.

HARDENED (2026-06-11, WP6): the original scaffold carried bare `Prop` fields
(`positive_rank_d : Prop`, `eigengap_at_d : Prop`, `nonzero_gap_constant : Prop`)
that constrained nothing (see planning/acharyya-graveyard.md, known-bad
patterns).  The structure now carries the actual mathematical content; symmetry
is implied by positive semidefiniteness.  Quantitative eigengap/floor data is
deliberately NOT part of this structure — perturbation statements take it as
explicit hypotheses (see `Acharyya2025.ConfigPerturbation`).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
structure CMDSpectralAssumptions (n d : Nat) (B : SqMat n) where
  posSemidef : B.PosSemidef
  rank_le : B.rank ≤ d

/--
Configuration-level output of the population CMDS spectral stage.

The intended construction is: take the positive `d`-dimensional eigenspace of the
centered matrix `B`, scale eigenvectors by square roots of eigenvalues, and use
the resulting rows as the CMDS configuration.
-/
structure PopulationCMDSStage (n d : Nat) (D : DisMat n) where
  ψ : Config n d
  realizes : GramRealizesCMDS D ψ
  stable : CMDSpectralAssumptions n d (disMatToMatrix (classicalMDSMatrix D))

/--
Perturbation output after passing through Weyl/Davis-Kahan and Procrustes
alignment.

`alignedError ≤ rate` is intentionally configuration-level: this is the shape
needed by `DkpsQuench` and `Helm2025`.
-/
structure PerturbedCMDSStage (n d : Nat)
    (Dhat D : DisMat n) (ψhat ψ : Config n d) (rate : Real) where
  centeredClose :
    MatrixEntrywiseClose
      (disMatToMatrix (classicalMDSMatrix Dhat))
      (disMatToMatrix (classicalMDSMatrix D))
      rate
  alignedError : ConfigError ψhat ψ ≤ rate

/-! ## Mathlib-candidate norm-comparison seam -/

/--
Finite-dimensional norm comparison from entrywise matrix control to an operator
bound for matrix-vector multiplication.

This is a paper-independent bridge that should be developed toward Mathlib.  A
typical proof uses Cauchy-Schwarz plus finite-dimensional norm equivalence:
`‖(A-B)x‖₂ ≤ n * ε * ‖x‖₂` when all entries of `A-B` are bounded by `ε`.

Mathematical source/citation:
- Horn and Johnson, *Matrix Analysis*, 2nd ed., Section 5.6 on matrix norms and
  norm equivalence.
- Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Chapter I on
  matrix norms.
-/
theorem cited_entrywise_to_operatorNormClose
    {n : Nat} {A B : SqMat n} {ε : Real}
    (hentry : MatrixEntrywiseClose A B ε) :
    MatrixOperatorNormClose A B ((n : Real) * ε) := by
  intro x
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : (A - B).mulVec x = 0 := Subsingleton.elim _ _
    simp [hzero]
  · have hε : 0 ≤ ε := (abs_nonneg _).trans (hentry ⟨0, hn⟩ ⟨0, hn⟩)
    have hcoord : ∀ j : Fin n, |x j| ≤ ‖x‖ := by
      intro j
      rw [EuclideanSpace.norm_eq]
      have hsq : (x j) ^ 2 ≤ ∑ i : Fin n, ‖x i‖ ^ 2 := by
        have h := Finset.single_le_sum
          (f := fun i : Fin n => ‖x i‖ ^ 2)
          (fun i _ => sq_nonneg ‖x i‖) (Finset.mem_univ j)
        simpa [Real.norm_eq_abs, sq_abs] using h
      exact Real.le_sqrt_of_sq_le (by simpa [sq_abs] using hsq)
    have hRHS : 0 ≤ (n : Real) * ε * ‖x‖ := by positivity
    rw [pi_norm_le_iff_of_nonneg hRHS]
    intro i
    rw [Real.norm_eq_abs]
    calc
      |(A - B).mulVec x i|
          = |∑ j : Fin n, (A i j - B i j) * x j| := by
            simp [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      _ ≤ ∑ j : Fin n, |(A i j - B i j) * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j - B i j| * |x j| := by
            simp [abs_mul]
      _ ≤ ∑ _j : Fin n, ε * ‖x‖ :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul (hentry i j) (hcoord j) (abs_nonneg _) hε
      _ = (n : Real) * ε * ‖x‖ := by
            simp [Finset.sum_const, Finset.card_univ, mul_assoc]

/-! ## Spectral/MDS hard seams -/

/--
Population CMDS spectral realization seam.

This is the place where the classical theorem "positive semidefinite Gram matrix
of rank `d` gives a `d`-dimensional Euclidean realization" should connect to the
paper's CMDS matrix.  In the final proof this should be built from Mathlib's
spectral theorem for real symmetric/self-adjoint matrices plus the standard Gram
factorization.

Mathematical source/citation:
- Cox and Cox, *Multidimensional Scaling*, 2nd ed., Sections 2.2-2.3.
- Borg and Groenen, *Modern Multidimensional Scaling*, 2nd ed., Chapter 12.
- Horn and Johnson, *Matrix Analysis*, 2nd ed., spectral theorem and positive
  semidefinite Gram factorizations.
-/
theorem cited_population_cmds_realization
    {n d : Nat}
    (D : DisMat n)
    (stable :
      CMDSpectralAssumptions n d (disMatToMatrix (classicalMDSMatrix D))) :
    ∃ ψ : Config n d, GramRealizesCMDS D ψ := by
  -- REPAIRED + PROVED (2026-06-11, WP6): the spectral construction is
  -- `Acharyya2025.GramRealization.exists_config_gram_eq_of_posSemidef_rank_le`,
  -- applicable now that `CMDSpectralAssumptions` carries real content.
  obtain ⟨ψ, hψ⟩ :=
    Acharyya2025.GramRealization.exists_config_gram_eq_of_posSemidef_rank_le
      (disMatToMatrix (classicalMDSMatrix D)) stable.posSemidef stable.rank_le
  exact ⟨ψ, fun i j => hψ i j⟩

/--
Davis-Kahan/Weyl/Procrustes perturbation seam for CMDS configurations.

This is the central hard bridge from Mathlib matrix perturbation to DKPS
configuration error.  It should eventually be decomposed into:

1. entrywise/Frobenius control to operator-norm control;
2. Weyl eigenvalue perturbation under eigengap assumptions;
3. Davis-Kahan invariant-subspace perturbation;
4. Procrustes/alignment conversion from subspace error to row-wise configuration
   error after eigenvalue square-root scaling.

Mathematical source/citation:
- Yu, Wang, Samworth (2015), "A useful variant of the Davis-Kahan theorem for
  statisticians", Biometrika 102(2):315-323.
- Stewart and Sun, *Matrix Perturbation Theory*, Academic Press, 1990.
- Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169.
- Agterberg, Lubberts, Arroyo (2022), decomposition strategy cited by Acharyya
  et al. for CMDS perturbation.
- Acharyya, Agterberg, Park, Priebe, *Concentration bounds on response-based
  vector embeddings of black-box generative models*, Theorem 2 and Appendix A.
-/
theorem cited_cmds_spectral_to_config_perturbation
    {n d : Nat}
    (Dhat D : DisMat n)
    (ψhat ψ : Config n d)
    (stable :
      CMDSpectralAssumptions n d (disMatToMatrix (classicalMDSMatrix D)))
    (rate : Real)
    (hcenter :
      MatrixEntrywiseClose
        (disMatToMatrix (classicalMDSMatrix Dhat))
        (disMatToMatrix (classicalMDSMatrix D))
        rate)
    (hψ : GramRealizesCMDS D ψ) :
    ConfigError ψhat ψ ≤ rate := by
  sorry

/-! ## Paper-facing reduction from the new pipeline to the existing seam -/

/--
New pipeline-shaped replacement for the old one-step CMDS perturbation seam.

This theorem does not prove Davis-Kahan yet; instead it makes the pipeline
explicit.  The only hard ingredient is
`cited_cmds_spectral_to_config_perturbation`, whose statement is now phrased in
terms of Mathlib matrices and a population CMDS spectral stage.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem cmds_embedding_perturbation_from_pipeline
    (P : Nat → Measure Ω)
    {n d : Nat}
    (Dhat : Nat → Ω → DisMat n)
    (D : DisMat n)
    (ψhat : Nat → Ω → Config n d)
    (ψ : Config n d)
    (stable :
      CMDSpectralAssumptions n d (disMatToMatrix (classicalMDSMatrix D)))
    (rate : Nat → Real)
    (hψ : GramRealizesCMDS D ψ)
    (hcenter :
      HighProbAtTop P
        (fun u => {ω | EntrywiseClose
          (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)})) :
    HighProbAtTop P (fun u => {ω | ConfigError (ψhat u ω) ψ ≤ rate u}) := by
  exact HighProbAtTop.mono hcenter
    (fun u ω hω =>
      cited_cmds_spectral_to_config_perturbation
        (Dhat u ω) D (ψhat u ω) ψ stable (rate u)
        (by
          rw [matrixEntrywiseClose_disMatToMatrix_iff]
          exact hω)
        hψ)

end Acharyya2025.SpectralPipeline
