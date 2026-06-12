/-
Gap derivation for the Davis–Kahan cross-block bound in the rank-`d` setting.

In the Acharyya 2025 application, the population doubly-centered matrix `B` is
positive semidefinite of rank `d` with a spectral floor `α` on its nonzero
eigenvalues: sorted eigenvalues satisfy `λ₀ ≥ ... ≥ λ_{d-1} ≥ α > 0 = λ_d = ...`.
If the sample matrix is `ε`-close in operator norm with `ε ≤ α/2`, then Weyl's
inequality pushes every trailing sample eigenvalue below `α/2`, so the leading
population eigenvalues and trailing sample eigenvalues are separated by
`gap = α/2`.  This file derives that separation and composes it with the
Davis–Kahan cross-block bound.

References:
* Yu, Wang, Samworth (2015), "A useful variant of the Davis–Kahan theorem for
  statisticians", Biometrika 102(2):315–323 (the population-eigengap form).
* Acharyya, Agterberg, Park, Priebe, arXiv:2511.08307, Assumptions 1–2 and
  Theorem 2 (rank-`d`, eigenvalue floor `C₁`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Acharyya2025.DavisKahan
import ForMathlib.Analysis.InnerProductSpace.DavisKahan

open scoped BigOperators RealInnerProductSpace InnerProductSpace
open Module (finrank)

namespace Acharyya2025.RankGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} {T S : E →ₗ[ℝ] E}

/--
**Gap from rank and eigenvalue floor.**  If the population operator `T` has its
leading `d` (sorted) eigenvalues at least `α` and its trailing eigenvalues equal
to `0`, and `S` is `ε`-operator-close to `T` with `ε ≤ α/2`, then every leading
population eigenvalue is separated from every trailing sample eigenvalue by
`α/2`.  This is exactly the `hgap` hypothesis of
`Acharyya2025.DavisKahan.sum_cross_inner_sq_le`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem gap_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n)
    (d : Nat) {α ε : ℝ}
    (hα : ∀ i : Fin n, (i : Nat) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : Nat) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∀ i j : Fin n, (i : Nat) < d → d ≤ (j : Nat) →
      α / 2 ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := by
  -- Thin ℝ-instantiation of the Mathlib-staged version.
  exact ForMathlib.gap_of_rank_floor hT hS hn d hα htail hε hsmall

/--
**Davis–Kahan cross-block bound under the rank-`d` population structure.**

Composition of `gap_of_rank_floor` with
`Acharyya2025.DavisKahan.sum_cross_inner_sq_le`: in the Acharyya setting
(population rank `d` with spectral floor `α`, sample `ε`-operator-close,
`ε ≤ α/2`), the squared overlap between leading population eigenvectors and
trailing sample eigenvectors is at most `4 n ε² / α²`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem sum_cross_inner_sq_le_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n)
    (d : Nat) {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : Nat) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : Nat) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
        (⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_ℝ)^2
      ≤ 4 * (n : ℝ) * ε^2 / α^2 := by
  -- Thin ℝ-instantiation of the Mathlib-staged version.
  have h := ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor
    hT hS hn d hα_pos hα htail hε hsmall
  simpa [Real.norm_eq_abs, sq_abs] using h

end Acharyya2025.RankGap
