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

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Acharyya2025.MathlibBridge
import Acharyya2025.Weyl
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm

open scoped BigOperators RealInnerProductSpace
open Module (finrank)

namespace Acharyya2025.OperatorBridge

open Acharyya2024 Acharyya2025.MathlibBridge

/--
Honest `ℓ² → ℓ²` operator-norm closeness for square real matrices:
`‖(A − B) x‖₂ ≤ ε‖x‖₂` for every Euclidean vector `x`, where the matrix acts
via `Matrix.toEuclideanLin`.

Role: the operator-norm closeness predicate consumed by the operator-world
spectral perturbation theorems (Weyl, Davis–Kahan).  In the paper's pipeline it
quantifies how close the sample CMDS matrix is to the population one.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
def MatrixL2OperatorClose {n : Nat} (A B : SqMat n) (ε : Real) : Prop :=
  ∀ x : EuclideanSpace Real (Fin n),
    ‖Matrix.toEuclideanLin (A - B) x‖ ≤ ε * ‖x‖

/--
The `ℓ¹`–`ℓ²` comparison on Euclidean coordinates: `∑ |xⱼ| ≤ √n · ‖x‖₂`.

Role: internal helper / standard norm-comparison fact.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem sum_abs_le_sqrt_card_mul_norm {n : Nat} (x : EuclideanSpace Real (Fin n)) :
    -- Conclusion: the ℓ¹ norm of `x`'s coordinates is at most `√n` times its ℓ² norm.
    ∑ j : Fin n, |x j| ≤ Real.sqrt n * ‖x‖ := by
  -- Thin ℝ-instantiation of the Mathlib-staged RCLike version.
  simpa [Real.norm_eq_abs, Fintype.card_fin] using
    ForMathlib.sum_norm_le_sqrt_card_mul_norm x

/--
Entrywise closeness gives honest `ℓ² → ℓ²` operator-norm closeness with
constant `n · ε`.

This is the `ℓ²` analogue of
`Acharyya2025.SpectralPipeline.operatorNormClose_of_entrywiseClose` (which
bounds the sup norm of the output) and is the form consumed by the
operator-world spectral perturbation theorems (Weyl, Davis–Kahan).

Mathematical source: Horn and Johnson, *Matrix Analysis*, 2nd ed., §5.6
(norm equivalence).

Role: internal helper / standard norm-comparison fact bridging entrywise control
to operator-norm control, so matrix-world events can be fed to the spectral
perturbation theorems.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem matrixL2OperatorClose_of_entrywise
    {n : Nat} {A B : SqMat n} {ε : Real}
    (hentry : MatrixEntrywiseClose A B ε) :   -- hypothesis: every entry of `A − B` is bounded by `ε`
    -- Conclusion: `A` and `B` are `ℓ² → ℓ²` operator-close with constant `n · ε`.
    MatrixL2OperatorClose A B ((n : Real) * ε) := by
  intro x
  -- Thin reduction to the Mathlib-staged entrywise -> operator-norm bound,
  -- applied to the difference matrix `A - B`.
  have hentry' : ∀ i j, |(A - B) i j| ≤ ε := by
    intro i j; rw [Matrix.sub_apply]; exact hentry i j
  exact ForMathlib.norm_toEuclideanLin_le_of_entry_le hentry' x

/--
A Hermitian (over `ℝ`: symmetric) matrix induces a symmetric operator on
Euclidean space.  Thin wrapper around `Matrix.isSymmetric_toEuclideanLin_iff`.

Role: internal helper transporting symmetry from the matrix world to the operator
world, so the spectral theorems apply to the CMDS matrix.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem isSymmetric_toEuclideanLin_of_isHermitian
    {n : Nat} {A : SqMat n}
    (hA : A.IsHermitian) :   -- hypothesis: `A` is symmetric (Hermitian over ℝ)
    -- Conclusion: the induced Euclidean operator `toEuclideanLin A` is symmetric.
    (Matrix.toEuclideanLin A).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hA

/--
A symmetric curried dissimilarity matrix induces a symmetric Euclidean operator.

Role: internal helper specializing the previous transport to the DKPS
dissimilarity-matrix type.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem isSymmetric_toEuclideanLin_of_symmetricDisMat
    {n : Nat} {D : DisMat n}
    (hD : SymmetricDisMat D) :   -- hypothesis: the dissimilarity matrix `D` is symmetric
    -- Conclusion: the induced Euclidean operator is symmetric.
    (Matrix.toEuclideanLin (disMatToMatrix D)).IsSymmetric := by
  refine isSymmetric_toEuclideanLin_of_isHermitian ?_
  show Matrix.conjTranspose (disMatToMatrix D) = disMatToMatrix D
  ext i j
  simpa [Matrix.conjTranspose_apply, disMatToMatrix] using hD i j

end Acharyya2025.OperatorBridge
