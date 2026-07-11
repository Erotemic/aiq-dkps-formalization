/-
# Davis-Kahan cross-block / sin-Theta (Mathlib candidate 03)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- A cross-block eigenvector-overlap bound in the spirit of the Davis-Kahan sin-Θ
theorem, with a *non-sharp* constant: the bound carries an extra factor `n`
(`4 n ε²/α²`), whereas the sharp sin-Θ constant is `ε²/gap²`. Rank-floor corollary. -/
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * (n : ℝ) * ε ^ 2 / α ^ 2 := by
  sorry

section Projector

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] {m : ℕ}

/-- Projector-form bound in the spirit of Davis-Kahan sin-Θ, with a *non-sharp*
constant: `‖P̂ − P‖_F² ≤ 2 m ε² / gap²` for the projections onto the leading-`d`
spectral subspaces — loose by the factor `m` relative to the sharp `ε²/gap²`. -/
theorem sum_norm_sub_starProjection_span_sq_le {T S : F →ₗ[𝕜] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 F = m)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin m, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : F, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ k, ‖((Submodule.span 𝕜 (hS.eigenvectorBasis hn ''
          ↑(Finset.univ.filter fun j : Fin m => (j : ℕ) < d))).starProjection
        - (Submodule.span 𝕜 (hT.eigenvectorBasis hn ''
          ↑(Finset.univ.filter fun i : Fin m => (i : ℕ) < d))).starProjection)
        (hT.eigenvectorBasis hn k)‖ ^ 2
      ≤ 2 * ((m : ℝ) * ε ^ 2 / gap ^ 2) := by
  sorry

end Projector
end ForMathlib
