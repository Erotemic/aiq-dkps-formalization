/-
Staged for Mathlib: additions to `Mathlib/LinearAlgebra/Matrix/Rank.lean`
(rank factorization).

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Rank factorization

Every matrix over a field factors as `M = L * R` with inner dimension exactly
`M.rank` (the classical *rank factorization* / full-rank factorization), hence
through `Fin r` for any `r ≥ M.rank`; and conversely any product through `Fin r`
has rank at most `r`.

Mathlib has the rank API (`Matrix.rank`, `rank_mul_le`, …) but no factorization
realizing the rank as an inner dimension; this supplies the missing converse
making `M.rank ≤ r ↔ ∃ L R, M = L * R` an equivalence.

The construction: the columns of `M` span the column space
`LinearMap.range M.mulVecLin`, whose dimension is `M.rank`; choosing a basis of
the column space, `L` lists the basis vectors and `R` the coordinates of each
column of `M` in that basis.

## Main results

* `ForMathlib.Matrix.exists_eq_mul_rank`: the exact rank factorization, inner
  dimension `Fin M.rank`.
* `ForMathlib.Matrix.exists_eq_mul_of_rank_le`: zero-padded to `Fin r` for any
  `M.rank ≤ r`.
* `ForMathlib.Matrix.rank_le_iff_exists_eq_mul`: the characterization
  `M.rank ≤ r ↔ ∃ L R, M = L * R`.
-/

namespace ForMathlib.Matrix

open Module (finrank)
open _root_.Matrix

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

/--
**Rank factorization (exact).** Every matrix factors as `M = L * R` with inner
dimension `Fin M.rank`: `L` lists a basis of the column space of `M` and `R` the
coordinates of each column of `M` in that basis.
-/
theorem exists_eq_mul_rank (M : Matrix m n 𝕜) :
    ∃ (L : Matrix m (Fin M.rank) 𝕜) (R : Matrix (Fin M.rank) n 𝕜), M = L * R := by
  -- A basis of the column space, indexed by `Fin M.rank`.
  have hdim : finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank := rfl
  let b : Module.Basis (Fin M.rank) 𝕜 (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq 𝕜 _ hdim
  -- Each column of `M` lies in the column space.
  have hcol : ∀ j : n, (fun i => M i j) ∈ LinearMap.range M.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨fun i k => (b k : m → 𝕜) i, fun k j => b.repr ⟨_, hcol j⟩ k, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  -- Expand column `j` in the basis and evaluate the resulting identity at row `i`.
  have hrepr := congrArg Subtype.val (b.sum_repr ⟨_, hcol j⟩)
  rw [Submodule.coe_sum] at hrepr
  have := congrFun hrepr i
  simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Finset.sum_congr rfl fun k _ => mul_comm ((b k : m → 𝕜) i) (b.repr ⟨_, hcol j⟩ k)]
  exact this.symm

/--
**Rank factorization (padded).** A matrix `M` with `M.rank ≤ r` factors as
`M = L * R` with `L : Matrix m (Fin r) 𝕜` and `R : Matrix (Fin r) n 𝕜`
(the exact factorization, zero-padded to inner dimension `r`).
-/
theorem exists_eq_mul_of_rank_le (M : Matrix m n 𝕜) {r : ℕ} (h : M.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  obtain ⟨L₀, R₀, hM⟩ := exists_eq_mul_rank M
  refine ⟨fun i k => if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0,
    fun k j => if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0, ?_⟩
  ext i j
  -- Reduce the padded sum over `Fin r` to the exact sum over `Fin M.rank`.
  set f : ℕ → 𝕜 := fun k => if hk : k < M.rank then L₀ i ⟨k, hk⟩ * R₀ ⟨k, hk⟩ j else 0 with hf
  have hpad : ∀ k : Fin r,
      (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
        * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0) = f (k : ℕ) := by
    intro k
    by_cases hk : (k : ℕ) < M.rank <;> simp [hf, hk]
  have hexact : ∀ k : Fin M.rank, L₀ i k * R₀ k j = f (k : ℕ) := by
    intro k
    simp [hf, k.isLt]
  have hsum : (∑ k : Fin r,
        (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
          * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0))
      = ∑ k : Fin M.rank, L₀ i k * R₀ k j := by
    rw [Finset.sum_congr rfl fun k _ => hpad k, Fin.sum_univ_eq_sum_range f r,
      Finset.sum_congr rfl fun k _ => hexact k, Fin.sum_univ_eq_sum_range f M.rank]
    -- The padding terms vanish above `M.rank`.
    refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le h))
      fun k _ hk => dif_neg (by simpa using hk)).symm
  rw [Matrix.mul_apply, hsum, ← Matrix.mul_apply, ← hM]

/--
**Rank-`r` factorization characterization.** A matrix has rank at most `r` if
and only if it factors through `Fin r`: `M.rank ≤ r ↔ ∃ L R, M = L * R`.
-/
theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  refine ⟨exists_eq_mul_of_rank_le M, ?_⟩
  rintro ⟨L, R, rfl⟩
  calc (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card (Fin r) := L.rank_le_card_width
    _ = r := Fintype.card_fin r

end ForMathlib.Matrix
