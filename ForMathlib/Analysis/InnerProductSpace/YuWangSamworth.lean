/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`YuWangSamworth.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W2.4 of
`dev/davis-kahan-gap-closure-plan.md`.

The Yu–Wang–Samworth variant of the Davis–Kahan theorem: a sin-Θ bound whose
denominator is a *population-only* eigengap `Δ` (formed from `T` alone), with the
statistician-friendly constant `2`.  The deterministic core is a residual
sandwich `Δ ‖sinΘ‖_F ≤ ‖R‖_F ≤ 2 ‖S − T‖_F`, where the lower bound is a
population-gap separation estimate (both eigenvalue multipliers come from `T`)
and the upper bound is Hoffman–Wielandt.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.HoffmanWielandt

/-! # The Yu–Wang–Samworth Davis–Kahan variant (Frobenius, population gap)

For symmetric `T, S` on a finite-dimensional inner product space, fix an index
block `s` (the target eigenvectors).  Write `u` for `T`'s eigenbasis and `w` for
`S`'s.  The **sin-Θ overlap** between the `S`-block subspace `span (w j : j ∈ s)`
and the `T`-block subspace `span (u k : k ∈ s)` is

`overlap = ∑_{j ∈ s} ∑_{k ∉ s} ‖⟪u k, w j⟫‖²`.

Yu, Wang and Samworth bound this using only a **population eigengap**
`Δ ≤ |λⱼ(T) − λₖ(T)|` for `j ∈ s`, `k ∉ s` — a separation of `T`'s own spectrum,
with no mixed `T`/`S` term — at the cost of the constant `2`:

`Δ² · overlap ≤ 4 · ‖S − T‖²_F`,  i.e.  `‖sinΘ‖_F ≤ 2 ‖S − T‖_F / Δ`.

The proof is the residual sandwich around `Rⱼ = λⱼ(T) wⱼ − T wⱼ`:

* **Lower bound** (`Δ² overlap ≤ ∑_{j ∈ s} ‖Rⱼ‖²`): the cross-term identity
  `⟪uₖ, Rⱼ⟫ = (λⱼ(T) − λₖ(T)) ⟪uₖ, wⱼ⟫` uses *only* `T`-eigenvalues on both
  sides, so the population gap applies directly; Bessel's inequality then sums
  the complement block into `‖Rⱼ‖²`.
* **Upper bound** (`∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 ‖S − T‖²_F`): from
  `Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ` and `(a + b)² ≤ 2a² + 2b²`, the two
  pieces are the Frobenius norm of `S − T` and — via **Hoffman–Wielandt** — the
  eigenvalue displacement, each `≤ ‖S − T‖²_F`.

## Main results

* `ForMathlib.sq_gap_mul_sum_cross_le_of_population_gap`: the squared bound
  `Δ² · overlap ≤ 4 · ∑ₖ ‖(S − T) uₖ‖²`.
* `ForMathlib.sqrt_sum_cross_le_of_population_gap`: the `‖sinΘ‖_F` form
  `√overlap ≤ 2 · √(∑ₖ ‖(S − T) uₖ‖²) / Δ`.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), 315–323.  arXiv:1405.0680.
-/

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- **The YWS population residual columns.** `residualColumn j = λⱼ(T) wⱼ − T wⱼ`,
where `wⱼ` is the `j`-th eigenvector of `S`.  Its `T`-eigenbasis coordinates are
governed by *population* eigenvalue differences (see
`inner_eigenvectorBasis_residualColumn`), which is what lets the population gap
drive the lower bound. -/
noncomputable def residualColumn (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j : Fin n) : E :=
  (hT.eigenvalues hn j : 𝕜) • hS.eigenvectorBasis hn j - T (hS.eigenvectorBasis hn j)

/-- **T-only cross-term identity.** `⟪uₖ, Rⱼ⟫ = (λⱼ(T) − λₖ(T)) ⟪uₖ, wⱼ⟫`.  Both
eigenvalue multipliers are `T`'s, so a separation of `T`'s spectrum alone bounds
the coordinate.  (Contrast the mixed identity in `Spectrum.lean`.) -/
theorem inner_eigenvectorBasis_residualColumn (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j k : Fin n) :
    ⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜
      = ((hT.eigenvalues hn j - hT.eigenvalues hn k : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜 := by
  rw [residualColumn, inner_sub_right, inner_smul_right,
    ← hT (hT.eigenvectorBasis hn k) (hS.eigenvectorBasis hn j),
    hT.apply_eigenvectorBasis hn k, inner_smul_left, RCLike.conj_ofReal]
  push_cast
  ring

/-- Norm-square form of the cross-term identity. -/
theorem sq_norm_inner_eigenvectorBasis_residualColumn (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (j k : Fin n) :
    ‖⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜‖ ^ 2
      = (hT.eigenvalues hn j - hT.eigenvalues hn k) ^ 2
          * ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 := by
  rw [inner_eigenvectorBasis_residualColumn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- **Residual column as a perturbation column.**
`Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ`, the identity behind the upper bound. -/
theorem residualColumn_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j : Fin n) :
    residualColumn hT hS hn j
      = (S - T) (hS.eigenvectorBasis hn j)
        - ((hS.eigenvalues hn j - hT.eigenvalues hn j : ℝ) : 𝕜) • hS.eigenvectorBasis hn j := by
  rw [residualColumn, LinearMap.sub_apply, hS.apply_eigenvectorBasis hn j]
  push_cast
  module

/-- **Lower bound (population-gap separation).** With a population gap
`Δ ≤ |λⱼ(T) − λₖ(T)|` separating the block `s` from its complement, the sin-Θ
overlap is controlled by the residual columns: `Δ² · overlap ≤ ∑_{j ∈ s} ‖Rⱼ‖²`. -/
theorem sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  -- Per column `j ∈ s`: `Δ² ∑_{k ∉ s} ‖⟪uₖ, wⱼ⟫‖² ≤ ‖Rⱼ‖²`.
  calc Δ ^ 2 * ∑ k ∈ sᶜ, ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      = ∑ k ∈ sᶜ, Δ ^ 2 * ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ sᶜ, ‖⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜‖ ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [sq_norm_inner_eigenvectorBasis_residualColumn]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [show (hT.eigenvalues hn j - hT.eigenvalues hn k) ^ 2
            = |hT.eigenvalues hn j - hT.eigenvalues hn k| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ hΔ (hgap j hj k (Finset.mem_compl.mp hk)) 2
    _ ≤ ∑ k, ‖⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _
    _ = ‖residualColumn hT hS hn j‖ ^ 2 :=
        (hT.eigenvectorBasis hn).sum_sq_norm_inner_right _

/-- **Upper bound (Hoffman–Wielandt).** The residual columns over the block are
bounded by the squared Frobenius norm of the perturbation:
`∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 · ∑ₖ ‖(S − T) uₖ‖²`.  From
`Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ` and `(a + b)² ≤ 2a² + 2b²`, the two pieces
are the Frobenius norm and the eigenvalue displacement (bounded by
Hoffman–Wielandt), each `≤ ‖S − T‖²_F`. -/
theorem sum_sq_norm_residualColumn_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  -- Frobenius norm of `S − T` is basis-independent (evaluate on `S`'s eigenbasis).
  have hST : (S - T).IsSymmetric := hS.sub hT
  have hbasis : ∑ j, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2 = frob := by
    rw [sum_sq_norm_apply_eq_sum_sq_eigenvalues hST hn (hS.eigenvectorBasis hn), hfrob,
      sum_sq_norm_apply_eq_sum_sq_eigenvalues hST hn (hT.eigenvectorBasis hn)]
  -- Eigenvalue displacement is bounded by the Frobenius norm (Hoffman–Wielandt).
  have hHW : ∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 ≤ frob := by
    rw [show (∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
        = ∑ j, (hT.eigenvalues hn j - hS.eigenvalues hn j) ^ 2 from
        Finset.sum_congr rfl fun j _ => by ring]
    exact sum_sq_eigenvalues_sub_le_sum_sq_norm_apply hT hS hn
  -- Per-column bound `‖Rⱼ‖² ≤ 2‖(S−T)wⱼ‖² + 2(λⱼ(S)−λⱼ(T))²`.
  have hcol : ∀ j, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ 2 * ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
        + 2 * (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 := by
    intro j
    have htri : ‖residualColumn hT hS hn j‖
        ≤ ‖(S - T) (hS.eigenvectorBasis hn j)‖
          + |hS.eigenvalues hn j - hT.eigenvalues hn j| := by
      rw [residualColumn_eq]
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_smul, RCLike.norm_ofReal, (hS.eigenvectorBasis hn).orthonormal.norm_eq_one j,
        mul_one]
    have h1 : ‖residualColumn hT hS hn j‖ ^ 2
        ≤ (‖(S - T) (hS.eigenvectorBasis hn j)‖
            + |hS.eigenvalues hn j - hT.eigenvalues hn j|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [h1, sq_nonneg (‖(S - T) (hS.eigenvectorBasis hn j)‖
      - |hS.eigenvalues hn j - hT.eigenvalues hn j|),
      sq_abs (hS.eigenvalues hn j - hT.eigenvalues hn j)]
  calc ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ ∑ j ∈ s, (2 * ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
          + 2 * (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2) :=
        Finset.sum_le_sum fun j _ => hcol j
    _ ≤ ∑ j, (2 * ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
          + 2 * (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
    _ = 2 * ∑ j, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
          + 2 * ∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * frob := by rw [hbasis]; linarith [hHW]

/-- **Yu–Wang–Samworth sin-Θ bound (Frobenius, population gap), squared form.**
With a population gap `Δ ≤ |λⱼ(T) − λₖ(T)|` separating the block `s` from its
complement, the sin-Θ overlap obeys `Δ² · overlap ≤ 4 · ‖S − T‖²_F`. -/
theorem sq_gap_mul_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 :=
  (sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn hT hS hn s hΔ hgap).trans
    (sum_sq_norm_residualColumn_le hT hS hn s)

/-- **Yu–Wang–Samworth sin-Θ bound (Frobenius, population gap), `‖sinΘ‖_F` form.**
For a positive population gap `Δ`, `√overlap ≤ 2 · √(∑ₖ ‖(S − T) uₖ‖²) / Δ`, the
statistician's `‖sinΘ‖_F ≤ 2 ‖S − T‖_F / Δ`. -/
theorem sqrt_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
      ≤ 2 * Real.sqrt (∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2) / Δ := by
  set overlap := ∑ j ∈ s, ∑ k ∈ sᶜ,
    ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 with hov
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  have hkey := sq_gap_mul_sum_cross_le_of_population_gap hT hS hn s hΔ.le hgap
  rw [← hov, ← hfrob] at hkey
  have hov0 : 0 ≤ overlap := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hfr0 : 0 ≤ frob := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [le_div_iff₀ hΔ]
  -- `√overlap · Δ ≤ 2 √frob`; square both sides (both nonneg).
  have hsq : (Real.sqrt overlap * Δ) ^ 2 ≤ (2 * Real.sqrt frob) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hov0, mul_pow, Real.sq_sqrt hfr0]
    nlinarith [hkey]
  have hL : 0 ≤ Real.sqrt overlap * Δ := by positivity
  have hR : 0 ≤ 2 * Real.sqrt frob := by positivity
  nlinarith [hsq, hL, hR, sq_nonneg (Real.sqrt overlap * Δ - 2 * Real.sqrt frob)]

end ForMathlib
