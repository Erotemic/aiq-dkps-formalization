/-
# AIQ DKPS ForMathlib challenge conformance file

This file states a first small set of reusable, Mathlib-facing claims extracted
from the AIQ DKPS formalization. It imports only Mathlib. Each theorem is
intentionally left as `sorry`: this is the trusted challenge surface for
external comparison tools.

Run the filled version with:

  lake env lean ChallengeLeaderboard.lean

The comparator config is in `comparator/aiq-mathlib-candidates.json`.
-/

import Mathlib

open scoped InnerProductSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Module (finrank)
open _root_.Matrix

namespace AIQChallenge

/-! ## Procrustes / Gram-matrix rigidity -/

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/--
If two indexed families of vectors in a finite-dimensional inner product space
have equal pairwise inner products, then one family is obtained from the other
by a single linear isometry equivalence of the ambient space.
-/
theorem procrustes_rigidity_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

/--
Equivalent `Matrix.gram` form of Procrustes rigidity: equal Gram matrices are
exactly the condition for two finite configurations to differ by a linear
isometry equivalence.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

/-! ## Rank-controlled PSD Gram realization -/

variable {n : ℕ}

/--
A Hermitian matrix is positive semidefinite with rank at most `d` if and only if
it is realized as a Gram matrix `Aᴴ * A` with `d` rows.
-/
theorem psd_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry

/-! ## Weyl spectral perturbation -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {T S : F →ₗ[𝕜] F}

/--
Weyl's eigenvalue perturbation inequality for symmetric operators: if `T - S`
is bounded by `ε` in operator-norm form, then each sorted eigenvalue differs by
at most `ε`.
-/
theorem weyl_abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 F = n)
    {ε : ℝ} (hε : ∀ x : F, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  sorry

end AIQChallenge
