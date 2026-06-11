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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Acharyya2024.Common

open scoped BigOperators
open Matrix

namespace Acharyya2025.GramRealization

open Acharyya2024

/--
Entrywise spectral expansion of a real Hermitian (symmetric) matrix:
`B i j = Σ_k (eigenvalues k) * U i k * U j k`, where `U` is the eigenvector
unitary.  This is the entrywise form of `Matrix.IsHermitian.spectral_theorem`
specialized to `ℝ`, where the conjugate transpose is just the transpose.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem exists_config_gram_eq_of_posSemidef_rank_le
    {n d : Nat} (B : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hrank : B.rank ≤ d) :
    ∃ ψ : Acharyya2024.Config n d,
      ∀ i j : Fin n, (∑ k : Fin d, ψ i k * ψ j k) = B i j := by
  classical
  have hHerm : B.IsHermitian := hB.isHermitian
  -- Nonzero-eigenvalue index subtype (written literally so unification sees it).
  -- card {k // λ k ≠ 0} = rank B ≤ d.
  have hcardS : Fintype.card {k : Fin n // hHerm.eigenvalues k ≠ 0} = B.rank :=
    (hHerm.rank_eq_card_non_zero_eigs).symm
  have hcard_le : Fintype.card {k : Fin n // hHerm.eigenvalues k ≠ 0} ≤ Fintype.card (Fin d) := by
    simpa [Fintype.card_fin, hcardS] using hrank
  -- An injection of the nonzero-eigenvalue indices into the d coordinates.
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard_le
  -- Coordinate weight for a single nonzero index `k` and row `i`.
  set w : Fin n → Fin n → Real := fun i k =>
    Real.sqrt (hHerm.eigenvalues k) * hHerm.eigenvectorUnitary i k with hw
  -- The configuration: at coordinate `a`, if `a = e k` for a nonzero index `k`,
  -- place `√(λ_k) · U i k`, otherwise `0`.
  set ψcoord : Acharyya2024.Config n d := fun i => WithLp.toLp 2 (fun a =>
      if h : ∃ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k = a then w i (Classical.choose h).1 else 0) with hψcoord
  refine ⟨ψcoord, ?_⟩
  intro i j
  -- For `a = e k` the dite evaluates to `w · k`.
  have hψ_at : ∀ (i : Fin n) (k : {k : Fin n // hHerm.eigenvalues k ≠ 0}), ψcoord i (e k) = w i k.1 := by
    intro i k
    have hex : ∃ k' : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k' = e k := ⟨k, rfl⟩
    have : ψcoord i (e k) = w i (Classical.choose hex).1 := by
      simp only [hψcoord, dif_pos hex]
    rw [this]
    have := e.injective (Classical.choose_spec hex)
    rw [this]
  -- Off the range of `e`, the coordinate is zero.
  have hψ_off : ∀ (i : Fin n) (a : Fin d), (∀ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k ≠ a) → ψcoord i a = 0 := by
    intro i a ha
    have : ¬ ∃ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k = a := by rintro ⟨k, hk⟩; exact ha k hk
    simp only [hψcoord, dif_neg this]
  -- Reduce the sum over Fin d to a sum over S (image of e), then to the full
  -- spectral sum over Fin n (the zero eigenvalues contribute nothing).
  calc
    (∑ a : Fin d, ψcoord i a * ψcoord j a)
        = ∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, w i k.1 * w j k.1 := by
          have hstep : (∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, w i k.1 * w j k.1)
              = ∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, ψcoord i (e k) * ψcoord j (e k) :=
            Finset.sum_congr rfl fun k _ => by rw [hψ_at i k, hψ_at j k]
          rw [hstep,
            ← Finset.sum_map (Finset.univ : Finset {k : Fin n // hHerm.eigenvalues k ≠ 0}) e
              (fun a => ψcoord i a * ψcoord j a)]
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro a _ ha
          have hnotrange : ∀ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k ≠ a := by
            intro k hk
            apply ha
            simp only [Finset.mem_map, Finset.mem_univ, true_and]
            exact ⟨k, hk⟩
          rw [hψ_off i a hnotrange, zero_mul]
      _ = ∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0},
            hHerm.eigenvalues k.1 * hHerm.eigenvectorUnitary i k.1 *
              hHerm.eigenvectorUnitary j k.1 := by
          -- Use √λ * √λ = λ for nonzero (hence nonnegative) eigenvalues.
          apply Finset.sum_congr rfl
          intro k _
          have hnn : 0 ≤ hHerm.eigenvalues k.1 := hB.eigenvalues_nonneg k.1
          simp only [hw]
          rw [show
              Real.sqrt (hHerm.eigenvalues k.1) * hHerm.eigenvectorUnitary i k.1 *
                  (Real.sqrt (hHerm.eigenvalues k.1) * hHerm.eigenvectorUnitary j k.1)
                = (Real.sqrt (hHerm.eigenvalues k.1) * Real.sqrt (hHerm.eigenvalues k.1)) *
                    (hHerm.eigenvectorUnitary i k.1 * hHerm.eigenvectorUnitary j k.1)
              from by ring]
          rw [Real.mul_self_sqrt hnn]
          ring
      _ = ∑ k : Fin n,
            hHerm.eigenvalues k * hHerm.eigenvectorUnitary i k *
              hHerm.eigenvectorUnitary j k := by
          -- Extend the sum over nonzero eigenvalues to all of Fin n: the
          -- omitted indices have zero eigenvalue, hence contribute nothing.
          have hsubtype :
              (∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0},
                hHerm.eigenvalues k.1 * hHerm.eigenvectorUnitary i k.1 *
                  hHerm.eigenvectorUnitary j k.1)
                = ∑ k ∈ Finset.univ.filter (fun k => hHerm.eigenvalues k ≠ 0),
                    hHerm.eigenvalues k * hHerm.eigenvectorUnitary i k *
                      hHerm.eigenvectorUnitary j k :=
            (Finset.sum_subtype
              (p := fun k => hHerm.eigenvalues k ≠ 0)
              (Finset.univ.filter (fun k => hHerm.eigenvalues k ≠ 0))
              (fun x => by simp)
              (fun k => hHerm.eigenvalues k * hHerm.eigenvectorUnitary i k *
                hHerm.eigenvectorUnitary j k)).symm
          rw [hsubtype]
          apply Finset.sum_filter_of_ne
          intro k _ hne hzero
          exact hne (by rw [hzero, zero_mul, zero_mul])
      _ = B i j := (isHermitian_entry_eq_sum_eigenvalues B hHerm i j).symm

end Acharyya2025.GramRealization
