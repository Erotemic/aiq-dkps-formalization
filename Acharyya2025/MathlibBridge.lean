/-
Paper-independent bridges between the DKPS finite-function representation and
Mathlib's matrix/linear-algebra world.

These definitions are intentionally small and general.  They are candidates for
eventual cleanup into Mathlib-facing lemmas, while the paper-specific CMDS and
spectral perturbation statements live in `Acharyya2025.SpectralPipeline`.
-/

import Acharyya2025.Deterministic

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2025.MathlibBridge

open Acharyya2024

/-- Square real matrices indexed by `Fin n`, the native Mathlib matrix world. -/
abbrev SqMat (n : Nat) := Matrix (Fin n) (Fin n) Real

/-- Convert a curried dissimilarity matrix into a Mathlib matrix. -/
def disMatToMatrix {n : Nat} (D : DisMat n) : SqMat n :=
  fun i j => D i j

/-- Convert a Mathlib matrix back into the curried dissimilarity representation. -/
def matrixToDisMat {n : Nat} (A : SqMat n) : DisMat n :=
  fun i j => A i j

@[simp]
theorem matrixToDisMat_disMatToMatrix {n : Nat} (D : DisMat n) :
    matrixToDisMat (disMatToMatrix D) = D := by
  rfl

@[simp]
theorem disMatToMatrix_matrixToDisMat {n : Nat} (A : SqMat n) :
    disMatToMatrix (matrixToDisMat A) = A := by
  rfl

/--
Entrywise closeness in Mathlib matrix notation.

Formalized by Codex 5.5 High, per user-observed model label.
-/
def MatrixEntrywiseClose {n : Nat} (A B : SqMat n) (ε : Real) : Prop :=
  ∀ i j : Fin n, |A i j - B i j| ≤ ε

/--
Entrywise closeness for a curried square matrix.  This is paper-independent and
definitionally matches the matrix predicate after `disMatToMatrix`.

Formalized by Codex 5.5 High, per user-observed model label.
-/
def CurriedEntrywiseClose {n : Nat} (A B : DisMat n) (ε : Real) : Prop :=
  ∀ i j : Fin n, |A i j - B i j| ≤ ε

/--
Symmetry of a curried dissimilarity matrix, in the orientation used by
`Matrix.IsSymm`.

Formalized by Codex 5.5 High, per user-observed model label.
-/
def SymmetricDisMat {n : Nat} (D : DisMat n) : Prop :=
  ∀ i j : Fin n, D j i = D i j

/--
The curried and matrix entrywise-closeness predicates agree definitionally after
conversion.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem matrixEntrywiseClose_disMatToMatrix_iff {n : Nat}
    (A B : DisMat n) (ε : Real) :
    MatrixEntrywiseClose (disMatToMatrix A) (disMatToMatrix B) ε ↔
      CurriedEntrywiseClose A B ε := by
  rfl

/--
Curried symmetry is exactly Mathlib matrix symmetry after conversion.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem disMatToMatrix_isSymm_iff {n : Nat} (D : DisMat n) :
    (disMatToMatrix D).IsSymm ↔ SymmetricDisMat D := by
  rw [Matrix.IsSymm.ext_iff]
  rfl

/-- Frobenius norm squared for Mathlib matrices, matching `Acharyya2024.frobSq`. -/
noncomputable def matrixFrobSq {n : Nat} (A : SqMat n) : Real :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j)^2

/-- Frobenius norm for Mathlib matrices, matching `Acharyya2024.frob`. -/
noncomputable def matrixFrob {n : Nat} (A : SqMat n) : Real :=
  Real.sqrt (matrixFrobSq A)

/-- Frobenius norm of a matrix difference, in Mathlib matrix notation. -/
noncomputable def matrixFrobSub {n : Nat} (A B : SqMat n) : Real :=
  matrixFrob (A - B)

/--
The Mathlib-matrix Frobenius difference agrees with the curried Frobenius
difference after conversion.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem matrixFrobSub_disMatToMatrix_eq_frobSub {n : Nat} (A B : DisMat n) :
    matrixFrobSub (disMatToMatrix A) (disMatToMatrix B) = frobSub A B := by
  rfl

/--
A direct operator-norm bound predicate avoiding any choice of bundled operator
norm.  This is the shape needed to bridge entrywise/Frobenius bounds to
Davis-Kahan-style perturbation statements in Mathlib's linear-map world.

`MatrixOperatorNormClose A B ε` means `‖(A - B) x‖ ≤ ε ‖x‖` for every vector.

Formalized by Codex 5.5 High, per user-observed model label.
-/
def MatrixOperatorNormClose {n : Nat} (A B : SqMat n) (ε : Real) : Prop :=
  ∀ x : Rvec n, ‖(A - B).mulVec x‖ ≤ ε * ‖x‖

end Acharyya2025.MathlibBridge
