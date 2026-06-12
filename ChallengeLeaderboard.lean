/-
# AIQ DKPS ForMathlib challenge solution file

This file has the same theorem names and statements as `ChallengeConformance.lean`,
but imports the AIQ DKPS `ForMathlib` library and fills the proofs by referring
to the staged declarations.

Run:

  lake env lean ChallengeLeaderboard.lean

or, after installing comparator and its prerequisites, use
`comparator/aiq-mathlib-candidates.json`.
-/

import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.GramMatrix
import ForMathlib.LinearAlgebra.Matrix.PosDef

open scoped InnerProductSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Module (finrank)
open _root_.Matrix

namespace AIQChallenge

/-! ## Procrustes / Gram-matrix rigidity -/

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem procrustes_rigidity_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  exact ForMathlib.exists_linearIsometryEquiv_of_inner_eq h

theorem gram_eq_gram_iff_exists_linearIsometryEquiv {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  simpa using
    (ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv
      (𝕜 := 𝕜) (E := E) (ι := ι) (φ := φ) (ψ := ψ))

/-! ## Rank-controlled PSD Gram realization -/

variable {n : ℕ}

theorem psd_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  simpa using
    (ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
      (𝕜 := 𝕜) (n := n) (d := d) B)

/-! ## Weyl spectral perturbation -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {T S : F →ₗ[𝕜] F}

theorem weyl_abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 F = n)
    {ε : ℝ} (hε : ∀ x : F, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  exact ForMathlib.abs_eigenvalues_sub_le hT hS hn hε k

/-! ## Axiom audit commands

These are non-failing inspection commands. In the current downstream project,
the expected axiom set for these theorems is the usual Mathlib kernel trio:
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#print axioms AIQChallenge.procrustes_rigidity_of_inner_eq
#print axioms AIQChallenge.gram_eq_gram_iff_exists_linearIsometryEquiv
#print axioms AIQChallenge.psd_rank_le_iff_exists_conjTranspose_mul_self
#print axioms AIQChallenge.weyl_abs_eigenvalues_sub_le

end AIQChallenge
