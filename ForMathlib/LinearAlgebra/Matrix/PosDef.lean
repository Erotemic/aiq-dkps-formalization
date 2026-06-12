/-
Staged for Mathlib: additions to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! # Rank-constrained positive-semidefinite factorization

A real positive-semidefinite matrix `B` factors as `B = Aᴴ * A` with `A` having
at most `d` rows **iff** its rank is at most `d`. The square-factor version
(`B = Aᴴ * A` with `A` square, e.g. the PSD square root) is already available;
this is the dimension-controlled refinement, equivalently the statement that a
PSD matrix of rank `≤ d` is the Gram matrix of `n` points in `ℝ^d` — the
classical multidimensional-scaling embedding step.

The forward (hard) direction is the spectral construction: `B = Σ_k λ_k uₖ uₖᵀ`
with `λ_k ≥ 0` and exactly `rank B` nonzero eigenvalues; scaling each nonzero
eigenvector by `√λ_k` and packing the `rank B ≤ d` resulting coordinates into
`d` rows yields `A`. The reverse direction is `posSemidef_conjTranspose_mul_self`
together with `rank_conjTranspose_mul_self` and `rank_le_height`.

## Main results

* `ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`:
  the rank-`≤ d` PSD factorization characterization (over `ℝ`).

TODO(RCLike): generalize from `ℝ` to `RCLike 𝕜`. The reverse direction is
already field-general; the forward construction needs `A k i =
RCLike.ofReal (√λ_k) * conj (U i k)` with the corresponding conjugation
bookkeeping in the entry expansion.

## References

* Cox & Cox, *Multidimensional Scaling*, 2nd ed., §2.2–2.3 (classical scaling).
* Horn & Johnson, *Matrix Analysis*, 2nd ed. (spectral theorem and PSD Gram
  factorizations).
-/

namespace ForMathlib.Matrix

open scoped BigOperators Matrix
open _root_.Matrix

variable {n : ℕ}

/--
Entrywise spectral expansion of a real symmetric matrix:
`B i j = Σ_k (eigenvalues k) * U i k * U j k`, where `U` is the eigenvector
unitary. This is the entrywise form of `Matrix.IsHermitian.spectral_theorem`
specialized to `ℝ`, where the conjugate transpose is the transpose.
-/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      hB.eigenvalues k * (hB.eigenvectorUnitary i k) * (hB.eigenvectorUnitary j k) := by
  classical
  have hspec := hB.spectral_theorem
  have hentry : B i j =
      (hB.eigenvectorUnitary *
        (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hB.eigenvalues) *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))) i j := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply]
    simp [mul_assoc]
  rw [hentry, Matrix.mul_apply]
  have hexp : ∀ k : Fin n,
      hB.eigenvectorUnitary i k *
        (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hB.eigenvalues) *
            (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) k j
        = hB.eigenvalues k * hB.eigenvectorUnitary i k * hB.eigenvectorUnitary j k := by
    intro k
    rw [Matrix.mul_apply]
    have hdiag : ∑ l : Fin n,
        diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hB.eigenvalues) k l *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) l j
        = hB.eigenvalues k * hB.eigenvectorUnitary j k := by
      rw [Finset.sum_eq_single k]
      · simp [Matrix.diagonal_apply_eq]
      · intro l _ hl
        simp [Matrix.diagonal_apply_ne _ (Ne.symm hl)]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hdiag]; ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]

/--
**Rank-constrained PSD factorization.** A real matrix `B` is positive
semidefinite with rank at most `d` if and only if `B = Aᴴ * A` for some
`A : Matrix (Fin d) (Fin n) ℝ` (equivalently, `B` is the Gram matrix of `n`
points in `ℝ^d`).
-/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) ℝ, B = Aᴴ * A := by
  classical
  constructor
  · rintro ⟨hB, hrank⟩
    have hHerm : B.IsHermitian := hB.isHermitian
    -- card {nonzero eigenvalues} = rank B ≤ d, giving an embedding into `Fin d`.
    have hcardS : Fintype.card {k : Fin n // hHerm.eigenvalues k ≠ 0} = B.rank :=
      hHerm.rank_eq_card_non_zero_eigs.symm
    have hcard_le :
        Fintype.card {k : Fin n // hHerm.eigenvalues k ≠ 0} ≤ Fintype.card (Fin d) := by
      simpa [Fintype.card_fin, hcardS] using hrank
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard_le
    -- Coordinate weight `√λ_k · U i k`.
    set w : Fin n → Fin n → ℝ := fun i k =>
      Real.sqrt (hHerm.eigenvalues k) * hHerm.eigenvectorUnitary i k with hw
    -- The factor `A`: row `a`, column `i` carries `√λ_k · U i k` when `a = e k`.
    set A : Matrix (Fin d) (Fin n) ℝ := fun a i =>
      if h : ∃ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k = a then
        w i (Classical.choose h).1 else 0 with hA
    refine ⟨A, ?_⟩
    have hA_at : ∀ (i : Fin n) (k : {k : Fin n // hHerm.eigenvalues k ≠ 0}),
        A (e k) i = w i k.1 := by
      intro i k
      have hex : ∃ k' : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k' = e k := ⟨k, rfl⟩
      have hval : A (e k) i = w i (Classical.choose hex).1 := by
        simp only [hA, dif_pos hex]
      rw [hval, e.injective (Classical.choose_spec hex)]
    have hA_off : ∀ (i : Fin n) (a : Fin d),
        (∀ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k ≠ a) → A a i = 0 := by
      intro i a ha
      have : ¬ ∃ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k = a := by
        rintro ⟨k, hk⟩; exact ha k hk
      simp only [hA, dif_neg this]
    -- Entrywise: `(Aᴴ * A) i j = Σ_a A a i * A a j = B i j`.
    ext i j
    rw [Matrix.mul_apply]
    have hconj : ∀ a, (Aᴴ) i a * A a j = A a i * A a j := by
      intro a; rw [Matrix.conjTranspose_apply, star_trivial]
    rw [Finset.sum_congr rfl (fun a _ => hconj a)]
    symm
    calc
      (∑ a : Fin d, A a i * A a j)
          = ∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, w i k.1 * w j k.1 := by
            have hstep : (∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, w i k.1 * w j k.1)
                = ∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, A (e k) i * A (e k) j :=
              Finset.sum_congr rfl fun k _ => by rw [hA_at i k, hA_at j k]
            rw [hstep,
              ← Finset.sum_map (Finset.univ : Finset {k : Fin n // hHerm.eigenvalues k ≠ 0}) e
                (fun a => A a i * A a j)]
            refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
            intro a _ ha
            have hnotrange : ∀ k : {k : Fin n // hHerm.eigenvalues k ≠ 0}, e k ≠ a := by
              intro k hk; apply ha
              simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨k, hk⟩
            rw [hA_off i a hnotrange, zero_mul]
        _ = ∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0},
              hHerm.eigenvalues k.1 * hHerm.eigenvectorUnitary i k.1 *
                hHerm.eigenvectorUnitary j k.1 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hnn : 0 ≤ hHerm.eigenvalues k.1 := hB.eigenvalues_nonneg k.1
            simp only [hw]
            rw [show
                Real.sqrt (hHerm.eigenvalues k.1) * hHerm.eigenvectorUnitary i k.1 *
                    (Real.sqrt (hHerm.eigenvalues k.1) * hHerm.eigenvectorUnitary j k.1)
                  = (Real.sqrt (hHerm.eigenvalues k.1) * Real.sqrt (hHerm.eigenvalues k.1)) *
                      (hHerm.eigenvectorUnitary i k.1 * hHerm.eigenvectorUnitary j k.1)
                from by ring, Real.mul_self_sqrt hnn]
            ring
        _ = ∑ k : Fin n,
              hHerm.eigenvalues k * hHerm.eigenvectorUnitary i k *
                hHerm.eigenvectorUnitary j k := by
            have hsubtype :
                (∑ k : {k : Fin n // hHerm.eigenvalues k ≠ 0},
                  hHerm.eigenvalues k.1 * hHerm.eigenvectorUnitary i k.1 *
                    hHerm.eigenvectorUnitary j k.1)
                  = ∑ k ∈ Finset.univ.filter (fun k => hHerm.eigenvalues k ≠ 0),
                      hHerm.eigenvalues k * hHerm.eigenvectorUnitary i k *
                        hHerm.eigenvectorUnitary j k :=
              (Finset.sum_subtype (p := fun k => hHerm.eigenvalues k ≠ 0)
                (Finset.univ.filter (fun k => hHerm.eigenvalues k ≠ 0)) (fun x => by simp)
                (fun k => hHerm.eigenvalues k * hHerm.eigenvectorUnitary i k *
                  hHerm.eigenvectorUnitary j k)).symm
            rw [hsubtype]
            apply Finset.sum_filter_of_ne
            intro k _ hne hzero
            exact hne (by rw [hzero, zero_mul, zero_mul])
        _ = B i j := (isHermitian_entry_eq_sum_eigenvalues B hHerm i j).symm
  · rintro ⟨A, rfl⟩
    refine ⟨posSemidef_conjTranspose_mul_self A, ?_⟩
    rw [rank_conjTranspose_mul_self]
    exact A.rank_le_height

end ForMathlib.Matrix
