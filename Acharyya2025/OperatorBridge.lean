/-
Bridge between the DKPS curried-matrix world and the operator world.

The hard spectral results (Courant–Fischer/Weyl in `Acharyya2025.Weyl`,
Davis–Kahan in `Acharyya2025.DavisKahan`) live in the operator world
(`T : E →ₗ[ℝ] E`, `LinearMap.IsSymmetric`, sorted eigenvalues), because that is
where Mathlib's sorted spectral API exists.  The DKPS pipeline produces events
about curried matrices (`DisMat n`) and Mathlib matrices (`SqMat n`).  This file
provides the conversion layer:

* `MatrixL2OperatorClose` — the honest `ℓ² → ℓ²` operator-norm closeness
  predicate via `Matrix.toEuclideanLin` (the older
  `MathlibBridge.MatrixOperatorNormClose` mixes the sup norm on the output with
  the `ℓ²` norm on the input; see planning/acharyya-graveyard.md watch-list).
* `matrixL2OperatorClose_of_entrywise` — entrywise `ε` control gives `ℓ² → ℓ²`
  operator control with constant `n·ε`.
* `isSymmetric_toEuclideanLin_of_isHermitian` — transport of symmetry, so that
  matrix-world events can invoke the operator-world spectral theorems.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Acharyya2025.MathlibBridge
import Acharyya2025.Weyl

open scoped BigOperators RealInnerProductSpace
open Module (finrank)

namespace Acharyya2025.OperatorBridge

open Acharyya2024 Acharyya2025.MathlibBridge

/--
Honest `ℓ² → ℓ²` operator-norm closeness for square real matrices:
`‖(A − B) x‖₂ ≤ ε‖x‖₂` for every Euclidean vector `x`, where the matrix acts
via `Matrix.toEuclideanLin`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
def MatrixL2OperatorClose {n : Nat} (A B : SqMat n) (ε : Real) : Prop :=
  ∀ x : EuclideanSpace Real (Fin n),
    ‖Matrix.toEuclideanLin (A - B) x‖ ≤ ε * ‖x‖

/--
The `ℓ¹`–`ℓ²` comparison on Euclidean coordinates: `∑ |xⱼ| ≤ √n · ‖x‖₂`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem sum_abs_le_sqrt_card_mul_norm {n : Nat} (x : EuclideanSpace Real (Fin n)) :
    ∑ j : Fin n, |x j| ≤ Real.sqrt n * ‖x‖ := by
  have hcs : (∑ j : Fin n, |x j|) ^ 2 ≤ (n : Real) * ∑ j : Fin n, |x j| ^ 2 := by
    simpa [Finset.card_univ] using
      sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n))) (f := fun j => |x j|)
  have hnorm : ‖x‖ ^ 2 = ∑ j : Fin n, |x j| ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp [Real.norm_eq_abs]
  have hsum_nonneg : 0 ≤ ∑ j : Fin n, |x j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hrhs_nonneg : 0 ≤ Real.sqrt n * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (∑ j : Fin n, |x j|) ^ 2 ≤ (Real.sqrt n * ‖x‖) ^ 2 := by
    have : (Real.sqrt n * ‖x‖) ^ 2 = (n : Real) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : Real) ≤ (n : Real))]
    rw [this, hnorm]
    exact hcs
  exact (abs_le_of_sq_le_sq' hsq hrhs_nonneg).2

/--
Entrywise closeness gives honest `ℓ² → ℓ²` operator-norm closeness with
constant `n · ε`.

This is the `ℓ²` analogue of
`Acharyya2025.SpectralPipeline.cited_entrywise_to_operatorNormClose` (which
bounds the sup norm of the output) and is the form consumed by the
operator-world spectral perturbation theorems (Weyl, Davis–Kahan).

Mathematical source: Horn and Johnson, *Matrix Analysis*, 2nd ed., §5.6
(norm equivalence).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem matrixL2OperatorClose_of_entrywise
    {n : Nat} {A B : SqMat n} {ε : Real}
    (hentry : MatrixEntrywiseClose A B ε) :
    MatrixL2OperatorClose A B ((n : Real) * ε) := by
  intro x
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : Matrix.toEuclideanLin (A - B) x = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    simp
  · have hε : 0 ≤ ε := (abs_nonneg _).trans (hentry ⟨0, hn⟩ ⟨0, hn⟩)
    -- Row-wise bound: |((A-B) ·ᵥ x) i| ≤ ε * Σ |x j| ≤ ε √n ‖x‖.
    have hrow : ∀ i : Fin n,
        |(Matrix.toEuclideanLin (A - B) x) i| ≤ ε * (Real.sqrt n * ‖x‖) := by
      intro i
      have happ : (Matrix.toEuclideanLin (A - B) x) i
          = ∑ j : Fin n, (A i j - B i j) * x j := by
        show ((A - B).mulVec (WithLp.ofLp x)) i = _
        simp [Matrix.mulVec, dotProduct, Matrix.sub_apply, sub_mul,
          Finset.sum_sub_distrib]
      calc
        |(Matrix.toEuclideanLin (A - B) x) i|
            = |∑ j : Fin n, (A i j - B i j) * x j| := by rw [happ]
        _ ≤ ∑ j : Fin n, |(A i j - B i j) * x j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |A i j - B i j| * |x j| := by
              simp [abs_mul]
        _ ≤ ∑ j : Fin n, ε * |x j| :=
              Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _)
        _ = ε * ∑ j : Fin n, |x j| := by rw [Finset.mul_sum]
        _ ≤ ε * (Real.sqrt n * ‖x‖) :=
              mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_mul_norm x) hε
    -- Sum the squared rows.
    have hnorm_sq : ‖Matrix.toEuclideanLin (A - B) x‖ ^ 2
        ≤ (n : Real) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      have hexp : ‖Matrix.toEuclideanLin (A - B) x‖ ^ 2
          = ∑ i : Fin n, |(Matrix.toEuclideanLin (A - B) x) i| ^ 2 := by
        rw [EuclideanSpace.norm_eq]
        rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
        simp [Real.norm_eq_abs]
      rw [hexp]
      calc
        ∑ i : Fin n, |(Matrix.toEuclideanLin (A - B) x) i| ^ 2
            ≤ ∑ _i : Fin n, (ε * (Real.sqrt n * ‖x‖)) ^ 2 :=
              Finset.sum_le_sum fun i _ =>
                pow_le_pow_left₀ (abs_nonneg _) (hrow i) 2
        _ = (n : Real) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- Take square roots.
    have hrhs_nonneg : 0 ≤ (n : Real) * ε * ‖x‖ := by positivity
    have hsq_eq : ((n : Real) * ε * ‖x‖) ^ 2
        = (n : Real) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      have hs : Real.sqrt (n : Real) * Real.sqrt (n : Real) = (n : Real) :=
        Real.mul_self_sqrt (by positivity)
      calc ((n : Real) * ε * ‖x‖) ^ 2
          = (n : Real) * (((n : Real)) * (ε ^ 2 * ‖x‖ ^ 2)) := by ring
        _ = (n : Real) * ((Real.sqrt (n : Real) * Real.sqrt (n : Real))
              * (ε ^ 2 * ‖x‖ ^ 2)) := by rw [hs]
        _ = (n : Real) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by ring
    have : ‖Matrix.toEuclideanLin (A - B) x‖ ^ 2 ≤ ((n : Real) * ε * ‖x‖) ^ 2 := by
      rw [hsq_eq]; exact hnorm_sq
    exact (abs_le_of_sq_le_sq' this hrhs_nonneg).2

/--
A Hermitian (over `ℝ`: symmetric) matrix induces a symmetric operator on
Euclidean space.  Thin wrapper around `Matrix.isSymmetric_toEuclideanLin_iff`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem isSymmetric_toEuclideanLin_of_isHermitian
    {n : Nat} {A : SqMat n} (hA : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hA

/--
A symmetric curried dissimilarity matrix induces a symmetric Euclidean operator.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem isSymmetric_toEuclideanLin_of_symmetricDisMat
    {n : Nat} {D : DisMat n} (hD : SymmetricDisMat D) :
    (Matrix.toEuclideanLin (disMatToMatrix D)).IsSymmetric := by
  refine isSymmetric_toEuclideanLin_of_isHermitian ?_
  show Matrix.conjTranspose (disMatToMatrix D) = disMatToMatrix D
  ext i j
  simpa [Matrix.conjTranspose_apply, disMatToMatrix] using hD i j

end Acharyya2025.OperatorBridge
