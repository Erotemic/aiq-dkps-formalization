/-
Davis–Kahan / sin-Θ eigenvector perturbation for symmetric operators on a
finite-dimensional real inner product space.

This file develops the elementary finite-dimensional "cross-term" route to a
Davis–Kahan-type bound: given two symmetric operators `T`, `S` that are close in
operator norm (`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`) and an eigenvalue gap separating the
first `d` eigenvalues of `T` from the trailing eigenvalues of `S`, the squared
inner products between the corresponding eigenvectors are controlled by
`(n · ε²) / gap²`.  The constant here is the crude `n · ε² / gap²` obtained by
summing the per-coordinate cross-energy bound; no attempt is made at the sharp
operator-norm constant of the classical sin-Θ theorem.

The argument is purely linear-algebraic and resolvent-free.  For a cross pair of
eigenvectors `uᵢ` (of `T`, eigenvalue `λᵢ`) and `ûⱼ` (of `S`, eigenvalue `λ̂ⱼ`)
the key identity is
`⟪uᵢ, (S − T) ûⱼ⟫ = (λ̂ⱼ − λᵢ) ⟪uᵢ, ûⱼ⟫`,
so when `gap ≤ |λᵢ − λ̂ⱼ|` one gets
`gap² ⟪uᵢ, ûⱼ⟫² ≤ ⟪uᵢ, (S − T) ûⱼ⟫²`,
and summing the right-hand side over all pairs is bounded by `n · ε²` via
Parseval (it is the total cross-energy `∑ⱼ ‖(S − T) ûⱼ‖² ≤ n ε²`).

This supports WP7(a)+(b) of `planning/acharyya-plan.md` (the spectral-projector
perturbation step of the DKPS finite-sample bridge).  It reuses the discrete
Courant–Fischer / Weyl machinery from `Acharyya2025.Weyl`, in particular the
Parseval lemma `sum_repr_sq_eq_norm_sq`.

References:
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1–46.
* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis–Kahan
  theorem for statisticians*, Biometrika 102 (2015), no. 2, 315–323.
* R. Bhatia, *Matrix Analysis*, Chapter VII (Sin Θ theorems).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import ForMathlib.Analysis.InnerProductSpace.Spectrum
import Acharyya2025.Weyl

open scoped BigOperators RealInnerProductSpace InnerProductSpace
open Module (finrank)

namespace Acharyya2025.DavisKahan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} {T S : E →ₗ[ℝ] E}

/-! ### Step (a): the cross-term identity

For an eigenvector `uᵢ` of `T` (eigenvalue `λᵢ`) and an eigenvector `ûⱼ` of `S`
(eigenvalue `λ̂ⱼ`), the off-diagonal entry of the perturbation `S − T` in the two
eigenbases is the inner product scaled by the eigenvalue difference. -/

/-- **Cross-term identity.** The matrix entry of `S − T` between the `i`-th
eigenvector of `T` and the `j`-th eigenvector of `S` equals the eigenvalue
difference times the overlap of the two eigenvectors:
`⟪uᵢ, (S − T) ûⱼ⟫ = (λ̂ⱼ − λᵢ) ⟪uᵢ, ûⱼ⟫`.

Thin `ℝ`-instantiation of the Mathlib-staged
`ForMathlib.inner_eigenvectorBasis_map_sub_eigenvectorBasis` (stated over
`RCLike 𝕜`); kept under its original name for downstream call-sites. -/
theorem inner_eigenvector_map_sub_eq
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n)
    (i j : Fin n) :
    ⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_ℝ
      = (hS.eigenvalues hn j - hT.eigenvalues hn i)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_ℝ := by
  simpa using
    ForMathlib.inner_eigenvectorBasis_map_sub_eigenvectorBasis hT hS hn i j

/-! ### Helper: total cross-energy bound (Parseval in the `u`-basis)

The total squared cross-energy `∑ᵢⱼ ⟪uᵢ, (S − T) ûⱼ⟫²` is bounded by `n ε²`.
For each fixed `j` the inner sum over `i` is the squared norm of `(S − T) ûⱼ`
(Parseval in the orthonormal eigenbasis `u`), which is `≤ ε²` since `ûⱼ` is a unit
vector. -/

/-- **Total cross-energy bound.** With the operator-closeness hypothesis
`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`, the sum over all eigenvector pairs of the squared
off-diagonal entries of `S − T` is at most `n ε²`. -/
theorem sum_inner_map_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i : Fin n, ∑ j : Fin n,
      (⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_ℝ)^2
      ≤ (n : ℝ) * ε^2 := by
  set u := hT.eigenvectorBasis hn with hu
  set v := hS.eigenvectorBasis hn with hv
  -- Swap the order of summation so Parseval (over `i`) is the inner sum.
  rw [Finset.sum_comm]
  -- For each `j`, the inner sum over `i` equals `‖(S − T) ûⱼ‖²`.
  have hinner : ∀ j : Fin n,
      ∑ i : Fin n, (⟪u i, (S - T) (v j)⟫_ℝ)^2 = ‖(S - T) (v j)‖^2 := by
    intro j
    rw [← Acharyya2025.Weyl.sum_repr_sq_eq_norm_sq u ((S - T) (v j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [u.repr_apply_apply]
  -- Each `‖(S − T) ûⱼ‖²` is at most `ε²` since `ûⱼ` is a unit vector.
  have hunit : ∀ j : Fin n, ‖v j‖ = 1 := fun j => by rw [hv]; exact v.orthonormal.1 j
  have hbound : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ‖(S - T) (v j)‖^2 ≤ ε^2 := by
    intro j _
    have h1 : ‖(S - T) (v j)‖ ≤ ε := by
      have := hε (v j)
      rwa [hunit j, mul_one] at this
    have h0 : 0 ≤ ‖(S - T) (v j)‖ := norm_nonneg _
    rw [sq, sq]
    exact mul_self_le_mul_self h0 h1
  calc ∑ j : Fin n, ∑ i : Fin n, (⟪u i, (S - T) (v j)⟫_ℝ)^2
      = ∑ j : Fin n, ‖(S - T) (v j)‖^2 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hinner j]
    _ ≤ ∑ _j : Fin n, ε^2 := Finset.sum_le_sum hbound
    _ = (n : ℝ) * ε^2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Step (b): the Davis–Kahan cross-block bound

Summing the per-pair estimate `gap² ⟪uᵢ, ûⱼ⟫² ≤ ⟪uᵢ, (S − T) ûⱼ⟫²` over the
cross block `{i < d} × {d ≤ j}` and applying the total cross-energy bound gives
the sin-Θ-type inequality with the crude constant `n ε² / gap²`. -/

/-- **Davis–Kahan cross-block bound (elementary finite-dimensional form).**
Suppose `T`, `S` are symmetric, close in operator norm
(`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), and there is a positive `gap` separating the first
`d` eigenvalues of `T` from the trailing eigenvalues of `S`
(`(i : ℕ) < d → d ≤ (j : ℕ) → gap ≤ |λᵢ(T) − λⱼ(S)|`).  Then the total squared
overlap between the leading eigenvectors of `T` and the trailing eigenvectors of
`S` is bounded:
`∑_{i < d} ∑_{d ≤ j} ⟪uᵢ, ûⱼ⟫² ≤ (n ε²) / gap²`. -/
theorem sum_cross_inner_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n)
    (d : Nat)
    {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin n, (i : Nat) < d → d ≤ (j : Nat) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
        (⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_ℝ)^2
      ≤ (n : ℝ) * ε^2 / gap^2 := by
  classical
  set u := hT.eigenvectorBasis hn with hu
  set v := hS.eigenvectorBasis hn with hv
  -- Per-pair: `gap² ⟪uᵢ, ûⱼ⟫² ≤ ⟪uᵢ, (S − T) ûⱼ⟫²` for cross pairs.
  have hpair : ∀ i j : Fin n, (i : Nat) < d → d ≤ (j : Nat) →
      gap^2 * (⟪u i, v j⟫_ℝ)^2
        ≤ (⟪u i, (S - T) (v j)⟫_ℝ)^2 := by
    intro i j hi hj
    have hg : gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := hgap i j hi hj
    -- `gap² ≤ (λᵢ − λ̂ⱼ)²`
    have hsq : gap^2 ≤ (hS.eigenvalues hn j - hT.eigenvalues hn i)^2 := by
      have h0 : (0 : ℝ) ≤ gap := le_of_lt hgap_pos
      have := mul_self_le_mul_self h0 hg
      rw [← sq, ← sq, sq_abs] at this
      -- `(λᵢ − λ̂ⱼ)² = (λ̂ⱼ − λᵢ)²`
      have hflip : (hT.eigenvalues hn i - hS.eigenvalues hn j)^2
          = (hS.eigenvalues hn j - hT.eigenvalues hn i)^2 := by ring
      rwa [hflip] at this
    -- multiply through by `⟪uᵢ, ûⱼ⟫² ≥ 0` and rewrite the RHS via step (a)
    have hmul : gap^2 * (⟪u i, v j⟫_ℝ)^2
        ≤ (hS.eigenvalues hn j - hT.eigenvalues hn i)^2 * (⟪u i, v j⟫_ℝ)^2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    calc gap^2 * (⟪u i, v j⟫_ℝ)^2
        ≤ (hS.eigenvalues hn j - hT.eigenvalues hn i)^2 * (⟪u i, v j⟫_ℝ)^2 := hmul
      _ = ((hS.eigenvalues hn j - hT.eigenvalues hn i) * ⟪u i, v j⟫_ℝ)^2 := by ring
      _ = (⟪u i, (S - T) (v j)⟫_ℝ)^2 := by
          rw [hu, hv, inner_eigenvector_map_sub_eq hT hS hn i j]
  -- Sum the per-pair bound over the cross block.
  have hcross : gap^2 * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
          (⟪u i, v j⟫_ℝ)^2)
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
            (⟪u i, (S - T) (v j)⟫_ℝ)^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hpair i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  -- Bound the cross-block RHS by the full double sum (all terms nonneg).
  -- First extend the inner sum from the `j`-filter to all of `Fin n`, then the
  -- outer sum from the `i`-filter to all of `Fin n`.
  have hsub : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
          (⟪u i, (S - T) (v j)⟫_ℝ)^2
      ≤ ∑ i : Fin n, ∑ j : Fin n, (⟪u i, (S - T) (v j)⟫_ℝ)^2 := by
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
              (⟪u i, (S - T) (v j)⟫_ℝ)^2
        ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
            ∑ j : Fin n, (⟪u i, (S - T) (v j)⟫_ℝ)^2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro j _ _
          exact sq_nonneg _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (⟪u i, (S - T) (v j)⟫_ℝ)^2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro i _ _
          exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  -- Chain: gap² · CROSS ≤ full cross-energy ≤ n ε².
  have htotal : gap^2 * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
          (⟪u i, v j⟫_ℝ)^2)
      ≤ (n : ℝ) * ε^2 := by
    calc gap^2 * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
              (⟪u i, v j⟫_ℝ)^2)
        ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : Nat) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
              (⟪u i, (S - T) (v j)⟫_ℝ)^2 := hcross
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (⟪u i, (S - T) (v j)⟫_ℝ)^2 := hsub
      _ ≤ (n : ℝ) * ε^2 := by
          rw [hu, hv]; exact sum_inner_map_sq_le hT hS hn hε
  -- Divide by `gap² > 0`.
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < gap^2), mul_comm]
  exact htotal

end Acharyya2025.DavisKahan
