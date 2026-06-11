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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Acharyya2025.DavisKahan

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

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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
  intro i j hi hj
  -- Weyl: the j-th sample eigenvalue is within ε of the j-th population
  -- eigenvalue, which is 0.
  have hweyl := Acharyya2025.Weyl.abs_eigenvalues_sub_le hT hS hn hε j
  have hTj : hT.eigenvalues hn j = 0 := htail j hj
  have hSj_abs : |hS.eigenvalues hn j| ≤ ε := by
    have : |hT.eigenvalues hn j - hS.eigenvalues hn j| ≤ ε := hweyl
    rw [hTj] at this
    simpa [abs_sub_comm] using this
  have hSj_le : hS.eigenvalues hn j ≤ α / 2 :=
    le_trans (le_trans (le_abs_self _) hSj_abs) hsmall
  have hTi : α ≤ hT.eigenvalues hn i := hα i hi
  have hdiff : α / 2 ≤ hT.eigenvalues hn i - hS.eigenvalues hn j := by
    linarith
  exact le_trans hdiff (le_abs_self _)

/--
**Davis–Kahan cross-block bound under the rank-`d` population structure.**

Composition of `gap_of_rank_floor` with
`Acharyya2025.DavisKahan.sum_cross_inner_sq_le`: in the Acharyya setting
(population rank `d` with spectral floor `α`, sample `ε`-operator-close,
`ε ≤ α/2`), the squared overlap between leading population eigenvectors and
trailing sample eigenvectors is at most `4 n ε² / α²`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
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
  have hε' : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    have hflip : (T - S) x = -((S - T) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [hflip, norm_neg]
    exact hε x
  have hgap := gap_of_rank_floor hT hS hn d hα htail hε' hsmall
  have hbound := Acharyya2025.DavisKahan.sum_cross_inner_sq_le hT hS hn d
    (by positivity : (0 : ℝ) < α / 2) hgap hε
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
        (⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_ℝ)^2
        ≤ (n : ℝ) * ε^2 / (α / 2)^2 := hbound
    _ = 4 * (n : ℝ) * ε^2 / α^2 := by
        field_simp
        ring

end Acharyya2025.RankGap
