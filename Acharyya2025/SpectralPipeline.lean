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
   Euclidean configurations, Gram matrices, orthogonal-alignment error.

The elementary representation bridges are proved in `MathlibBridge`.  The hard
spectral facts are now FULLY PROVED, one stage per file: Weyl eigenvalue
perturbation (`Acharyya2025.Weyl`), Davis-Kahan eigenspace perturbation
(`Acharyya2025.DavisKahan`), polar-factor alignment
(`Acharyya2025.PolarFactor`), the configuration-level capstone
(`Acharyya2025.ConfigPerturbation`), its matrix-world packaging
(`Acharyya2025.MatrixPerturbation`), and the high-probability aligned pipeline
(`Acharyya2025.AlignedPipeline`).  This file retains the world-map definitions
(`configGram`, `GramRealizesCMDS`, the hardened `CMDSpectralAssumptions`, the
stage records), the proved norm-comparison bridge
(`operatorNormClose_of_entrywiseClose`), and the proved population CMDS
realization (`exists_config_gramRealizesCMDS_of_spectralAssumptions`).
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

/-- Gram matrix of a finite Euclidean configuration: the `(i,j)` entry is the
inner product `⟪ψ i, ψ j⟫ = ∑ k, ψ i k · ψ j k`.  This is the object that the
classical-MDS embedding inverts (configuration ↦ Gram matrix). -/
noncomputable def configGram {n d : Nat} (ψ : Config n d) : DisMat n :=
  fun i j => ∑ k : Fin d, (ψ i k) * (ψ j k)

/-- A configuration realizes a CMDS matrix when its Gram matrix equals that CMDS
matrix entrywise.  This is the predicate "`ψ` is a `d`-dimensional embedding of
the classical-MDS matrix of `D`" — the configurations `ψ`, `ψ̂` of Theorem 2 are
exactly such realizations of the population/sample CMDS matrices. -/
def GramRealizesCMDS {n d : Nat} (D : DisMat n) (ψ : Config n d) : Prop :=
  ∀ i j : Fin n, configGram ψ i j = classicalMDSMatrix D i j

/--
The Gram matrix of a real configuration is symmetric.

Role: internal helper / standard fact (Gram matrices are symmetric).

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem symmetric_configGram {n d : Nat} (ψ : Config n d) :
    -- Conclusion: the Gram matrix of any real configuration is symmetric.
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

Note (extra implicit assumptions beyond the paper): this structure encodes the
classical-MDS preconditions as a finite real symmetric matrix that is positive
semidefinite and of rank ≤ d.  These are the Lean modelling assumptions on the
population CMDS matrix `B` that make the `d`-dimensional embedding (and hence the
configurations of Theorem 2) well-defined.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
structure CMDSpectralAssumptions (n d : Nat) (B : SqMat n) where
  posSemidef : B.PosSemidef   -- PSD/Gram structure: `B` is a valid inner-product matrix
  rank_le : B.rank ≤ d        -- rank/dimension: `B`'s rank fits the embedding dimension `d`

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

Role: internal helper / standard norm-comparison fact (entrywise control to an
operator bound).
-/
theorem operatorNormClose_of_entrywiseClose
    {n : Nat} {A B : SqMat n} {ε : Real}
    (hentry : MatrixEntrywiseClose A B ε) :   -- hypothesis: every entry of `A − B` is bounded by `ε`
    -- Conclusion: `A` and `B` are operator-norm close with constant `n · ε`.
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

/-! ## Spectral realization (proved) -/

/--
Population CMDS spectral realization seam.

This is where the classical theorem "positive semidefinite Gram matrix of rank
`d` gives a `d`-dimensional Euclidean realization" connects to the paper's CMDS
matrix.  It is proved (below) from
`Acharyya2025.GramRealization.exists_config_gram_eq_of_posSemidef_rank_le`, the
Mathlib-spectral-theorem-based Gram factorization for real symmetric PSD matrices.

Mathematical source/citation:
- Cox and Cox, *Multidimensional Scaling*, 2nd ed., Sections 2.2-2.3.
- Borg and Groenen, *Modern Multidimensional Scaling*, 2nd ed., Chapter 12.
- Horn and Johnson, *Matrix Analysis*, 2nd ed., spectral theorem and positive
  semidefinite Gram factorizations.

Paper correspondence: this is the **spectral-embedding / Gram-realization**
endpoint of the pipeline.  It produces the `d`-dimensional configuration `ψ`
realizing the population classical-MDS matrix of `D` — i.e. the population
perspective `ψ` that Theorem 2 aligns the sample embedding `ψ̂` to.  It does not
itself produce W*; it produces one of the two configurations W* relates.
-/
theorem exists_config_gramRealizesCMDS_of_spectralAssumptions
    {n d : Nat}
    (D : DisMat n)
    -- hypothesis: the population CMDS matrix is PSD and rank ≤ d (classical-MDS preconditions)
    (stable :
      CMDSpectralAssumptions n d (disMatToMatrix (classicalMDSMatrix D))) :
    -- Conclusion: there is a `d`-dimensional configuration `ψ` whose Gram matrix
    -- is the classical-MDS matrix of `D` (a spectral embedding of `D` exists).
    ∃ ψ : Config n d, GramRealizesCMDS D ψ := by
  -- REPAIRED + PROVED (2026-06-11, WP6): the spectral construction is
  -- `Acharyya2025.GramRealization.exists_config_gram_eq_of_posSemidef_rank_le`,
  -- applicable now that `CMDSpectralAssumptions` carries real content.
  obtain ⟨ψ, hψ⟩ :=
    Acharyya2025.GramRealization.exists_config_gram_eq_of_posSemidef_rank_le
      (disMatToMatrix (classicalMDSMatrix D)) stable.posSemidef stable.rank_le
  exact ⟨ψ, fun i j => hψ i j⟩

end Acharyya2025.SpectralPipeline
