/-
Staged for Mathlib: additions to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); rank-controlled direction
reproved through the rank-factorization API by Claude Fable 5 (claude-fable-5[1m]).
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import ForMathlib.LinearAlgebra.Matrix.RankFactorization

/-! # Rank-constrained positive-semidefinite factorization

A positive-semidefinite matrix `B` factors as `B = Aᴴ * A` with `A` having at
most `d` rows **iff** its rank is at most `d` — equivalently, a PSD matrix of
rank `≤ d` is the Gram matrix of `n` points in `𝕜^d`, the classical
multidimensional-scaling embedding step.

The factorization is assembled from two reusable pieces:
* the **square** factorization `B = Aᴴ * A` with `A` square, built spectrally
  (`A = √D · Uᴴ` for the spectral decomposition `B = U D Uᴴ`); and
* the **rank factorization** `A = L * R` through `Fin d`
  (`ForMathlib.Matrix.exists_eq_mul_of_rank_le`), which compresses the inner
  dimension.

A second application of the square factorization to `Lᴴ * L` then yields the
rank-controlled Gram factor `(S * R)ᴴ * (S * R)`.  The reverse direction is
`posSemidef_conjTranspose_mul_self` with `rank_conjTranspose_mul_self` and
`rank_le_height`.

## Main results

* `ForMathlib.Matrix.PosSemidef.exists_eq_conjTranspose_mul_self`: the square
  factorization `B = Aᴴ * A` of a PSD matrix (spectral construction).
* `ForMathlib.Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le`: the
  rank-controlled factorization, `A` of size `d × n` for any `rank B ≤ d`.
* `ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`:
  the iff characterization, over `RCLike 𝕜`.

## References

* Cox & Cox, *Multidimensional Scaling*, 2nd ed., §2.2–2.3 (classical scaling).
* Horn & Johnson, *Matrix Analysis*, 2nd ed. (spectral theorem and PSD Gram
  factorizations).
-/

namespace ForMathlib.Matrix

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/--
Entrywise spectral expansion of a Hermitian matrix over `𝕜 = ℝ, ℂ`:
`B i j = Σ_k (eigenvalues k) * U i k * conj (U j k)`, where `U` is the
eigenvector unitary.  This is the entrywise form of
`Matrix.IsHermitian.spectral_theorem`.
-/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  classical
  have hspec := hB.spectral_theorem
  have hentry : B i j =
      (hB.eigenvectorUnitary *
        (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜))) i j := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply]
    simp [mul_assoc]
  rw [hentry, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply]
  have hdiag : ∑ l : Fin n,
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) k l *
        (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) l j
      = (hB.eigenvalues k : 𝕜) * conj (hB.eigenvectorUnitary j k) := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, Matrix.star_apply, RCLike.star_def]
      rfl
    · intro l _ hl
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hdiag]; ring

/--
**Square PSD factorization.** A positive-semidefinite matrix `B` over `𝕜 = ℝ, ℂ`
factors as `B = Aᴴ * A` with `A` square: take `A = √D · Uᴴ` for the spectral
decomposition `B = U D Uᴴ` (row `k` of `A` is the `k`-th eigenvector scaled by
`√λ_k`).
-/
theorem PosSemidef.exists_eq_conjTranspose_mul_self
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) :
    ∃ A : Matrix (Fin n) (Fin n) 𝕜, B = Aᴴ * A := by
  have hHerm : B.IsHermitian := hB.1
  refine ⟨fun k i =>
    (Real.sqrt (hHerm.eigenvalues k) : 𝕜) * conj (hHerm.eigenvectorUnitary i k), ?_⟩
  ext i j
  rw [Matrix.mul_apply, isHermitian_entry_eq_sum_eigenvalues B hHerm i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def]
  have hnn : 0 ≤ hHerm.eigenvalues k := _root_.Matrix.PosSemidef.eigenvalues_nonneg hB k
  simp only [map_mul, RCLike.conj_ofReal, RCLike.conj_conj]
  rw [show RCLike.ofReal (Real.sqrt (hHerm.eigenvalues k)) * hHerm.eigenvectorUnitary i k *
      ((Real.sqrt (hHerm.eigenvalues k) : 𝕜) * conj (hHerm.eigenvectorUnitary j k))
    = ((Real.sqrt (hHerm.eigenvalues k) : 𝕜) * (Real.sqrt (hHerm.eigenvalues k) : 𝕜))
        * (hHerm.eigenvectorUnitary i k * conj (hHerm.eigenvectorUnitary j k)) from by ring]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hnn]
  ring

/--
**Rank-constrained PSD factorization, forward direction.** A positive
semidefinite matrix `B` of rank `≤ d` is the Gram matrix of `n` points in
`𝕜^d`: it factors as `B = Aᴴ * A` for some `A : Matrix (Fin d) (Fin n) 𝕜`.

Proof through the factorization API: write `B = A₀ᴴ * A₀` with `A₀` square
(`PosSemidef.exists_eq_conjTranspose_mul_self`), compress `A₀ = L * R` through
`Fin d` by rank factorization (`rank A₀ = rank B ≤ d`), and absorb the leftover
Gram factor `Lᴴ * L` by a second square factorization `Lᴴ * L = Sᴴ * S`, giving
`B = (S * R)ᴴ * (S * R)`.
-/
theorem PosSemidef.exists_conjTranspose_mul_self_of_rank_le
    {d : ℕ} {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) (hrank : B.rank ≤ d) :
    ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  -- Square factorization of `B`, whose factor has the same rank as `B`.
  obtain ⟨A₀, hA₀⟩ := PosSemidef.exists_eq_conjTranspose_mul_self hB
  have hrankA₀ : A₀.rank ≤ d := by
    rwa [hA₀, rank_conjTranspose_mul_self] at hrank
  -- Compress the inner dimension to `Fin d` by rank factorization.
  obtain ⟨L, R, hLR⟩ := exists_eq_mul_of_rank_le A₀ hrankA₀
  -- Absorb the leftover Gram factor `Lᴴ * L` by a second square factorization.
  obtain ⟨S, hS⟩ :=
    PosSemidef.exists_eq_conjTranspose_mul_self (posSemidef_conjTranspose_mul_self L)
  refine ⟨S * R, ?_⟩
  calc B = A₀ᴴ * A₀ := hA₀
    _ = Rᴴ * (Lᴴ * L) * R := by
        rw [hLR, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Rᴴ * (Sᴴ * S) * R := by rw [← hS]
    _ = (S * R)ᴴ * (S * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]

/--
**Rank-constrained PSD factorization.** A matrix `B` over `𝕜 = ℝ, ℂ` is positive
semidefinite with rank at most `d` if and only if `B = Aᴴ * A` for some
`A : Matrix (Fin d) (Fin n) 𝕜` (equivalently, `B` is the Gram matrix of `n`
points in `𝕜^d`).  Splits into the forward direction
`PosSemidef.exists_conjTranspose_mul_self_of_rank_le` and the elementary
converse (`posSemidef_conjTranspose_mul_self` + `rank_conjTranspose_mul_self`).
-/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  refine ⟨fun h => PosSemidef.exists_conjTranspose_mul_self_of_rank_le h.1 h.2, ?_⟩
  rintro ⟨A, rfl⟩
  refine ⟨posSemidef_conjTranspose_mul_self A, ?_⟩
  rw [rank_conjTranspose_mul_self]
  exact A.rank_le_height

end ForMathlib.Matrix
