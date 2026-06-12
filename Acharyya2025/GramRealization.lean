/-
Gram realization of a positive-semidefinite, low-rank real matrix.

This file proves the true linear-algebra theorem underlying the `sorry`'d
population CMDS realization seam in `Acharyya2025.SpectralPipeline`:

  a real symmetric positive-semidefinite matrix `B` of rank at most `d` is the
  Gram matrix of some `d`-dimensional Euclidean configuration.

This is the classical-MDS embedding step: by the spectral theorem
`B = Σ_k λ_k u_k u_kᵀ` with eigenvalues `λ_k ≥ 0` (positive semidefiniteness)
and exactly `rank B` nonzero eigenvalues.  Packing the nonzero-eigenvalue
coordinates `√(λ_k) · u_k` into `d ≥ rank B` columns yields a configuration whose
Gram matrix is `B`.

Mathematical source/citation:
- Cox and Cox, *Multidimensional Scaling*, 2nd ed., Sections 2.2-2.3 (classical
  scaling: a centered, positive-semidefinite inner-product matrix of rank `d`
  yields a `d`-dimensional point configuration).
- Horn and Johnson, *Matrix Analysis*, 2nd ed., spectral theorem for real
  symmetric matrices and positive-semidefinite Gram factorizations.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Acharyya2024.Common
import ForMathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators
open Matrix

namespace Acharyya2025.GramRealization

open Acharyya2024

/--
Entrywise spectral expansion of a real Hermitian (symmetric) matrix:
`B i j = Σ_k (eigenvalues k) * U i k * U j k`, where `U` is the eigenvector
unitary.  This is the entrywise form of `Matrix.IsHermitian.spectral_theorem`
specialized to `ℝ`, where the conjugate transpose is just the transpose.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem isHermitian_entry_eq_sum_eigenvalues {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      hB.eigenvalues k * (hB.eigenvectorUnitary i k) * (hB.eigenvectorUnitary j k) := by
  classical
  -- Spectral theorem: B = U * diagonal(λ) * star U.
  have hspec := hB.spectral_theorem
  -- Rewrite the (i, j) entry using the conjugation form.
  have : B i j =
      (hB.eigenvectorUnitary *
        (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hB.eigenvalues) *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))) i j := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply]
    simp [mul_assoc]
  rw [this]
  -- Expand the matrix products entrywise.
  rw [Matrix.mul_apply]
  have hexp : ∀ k : Fin n,
      hB.eigenvectorUnitary i k *
        (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hB.eigenvalues) *
            (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) k j
        = hB.eigenvalues k * hB.eigenvectorUnitary i k * hB.eigenvectorUnitary j k := by
    intro k
    rw [Matrix.mul_apply]
    -- The middle factor is diagonal, so only k = l survives.
    have : ∑ l : Fin n,
        diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hB.eigenvalues) k l *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) l j
        = hB.eigenvalues k * hB.eigenvectorUnitary j k := by
      rw [Finset.sum_eq_single k]
      · simp [Matrix.diagonal_apply_eq]
      · intro l _ hl
        simp [Matrix.diagonal_apply_ne _ (Ne.symm hl)]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]

/--
**Gram realization of a low-rank PSD matrix.**

A real positive-semidefinite matrix `B` of rank at most `d` is the Gram matrix of
a `d`-dimensional Euclidean configuration: there is `ψ : Config n d` with
`Σ_k ψ i k * ψ j k = B i j` for all `i, j`.

The construction is classical scaling (Cox and Cox, Sections 2.2-2.3): use the
spectral decomposition, scale each eigenvector with a nonzero eigenvalue by the
square root of that eigenvalue, and embed those `rank B ≤ d` coordinates into the
`d` available dimensions.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem exists_config_gram_eq_of_posSemidef_rank_le
    {n d : Nat} (B : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hrank : B.rank ≤ d) :
    ∃ ψ : Acharyya2024.Config n d,
      ∀ i j : Fin n, (∑ k : Fin d, ψ i k * ψ j k) = B i j := by
  -- Derive the configuration from the Mathlib-staged matrix factorization
  -- `B = Aᴴ * A` with `A : Matrix (Fin d) (Fin n) ℝ`: the columns of `A` are the
  -- configuration vectors.
  obtain ⟨A, hA⟩ :=
    (ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self B).mp
      ⟨hB, hrank⟩
  refine ⟨fun i => WithLp.toLp 2 (fun k => A k i), ?_⟩
  intro i j
  show (∑ k : Fin d, A k i * A k j) = B i j
  rw [hA, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.conjTranspose_apply, star_trivial]

end Acharyya2025.GramRealization
