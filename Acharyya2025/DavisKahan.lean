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
import ForMathlib.Analysis.InnerProductSpace.DavisKahan
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
  -- Thin ℝ-instantiation of the Mathlib-staged RCLike version.
  have h := ForMathlib.sum_norm_inner_eigenvectorBasis_map_sub_sq_le hT hS hn hε
  simpa [Real.norm_eq_abs, sq_abs] using h

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
  -- Thin ℝ-instantiation of the Mathlib-staged RCLike version.
  have h := ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le hT hS hn d hgap_pos hgap hε
  simpa [Real.norm_eq_abs, sq_abs] using h

end Acharyya2025.DavisKahan
