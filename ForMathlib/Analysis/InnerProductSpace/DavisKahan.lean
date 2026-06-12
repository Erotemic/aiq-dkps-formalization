/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`DavisKahan.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import ForMathlib.Analysis.InnerProductSpace.Spectrum
import ForMathlib.Analysis.InnerProductSpace.CourantFischer

/-! # Davis–Kahan cross-block bound (elementary finite-dimensional form)

For two self-adjoint operators `T`, `S` on a finite-dimensional inner product
space that are close in operator norm, the eigenvectors associated to a
well-separated block of the spectrum are nearly orthogonal across the gap.  This
is the (squared) sin-Θ theorem of Davis and Kahan, in the most elementary
finite-dimensional packaging: a direct consequence of the spectral cross-term
identity `⟪uᵢ, (S − T) v̂ⱼ⟫ = (λ̂ⱼ − λᵢ) ⟪uᵢ, v̂ⱼ⟫` and Parseval, with no
resolvents or contour integrals.

Mathlib has no Davis–Kahan / sin-Θ result; `Analysis/InnerProductSpace/Rayleigh`
covers only the extreme eigenvalues.  The constant here (`n ε² / gap²`) is crude
— the sharp sin-Θ constant is `ε² / gap²` summed over the block — but the result
is self-contained and correct.

## Main results

* `ForMathlib.sum_norm_inner_eigenvectorBasis_map_sub_sq_le`: the total
  cross-energy bound `∑_{i,j} ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖² ≤ n ε²`.
* `ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le`: the Davis–Kahan
  cross-block bound `∑_{i < d, j ≥ d} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ n ε² / gap²`.
* `ForMathlib.sum_norm_sub_spectralProjection_sq_eq` (real): the canonical
  projector form — the squared Frobenius distance between the two rank-`d`
  spectral projectors is `2 ·` the cross-block sum.
* `ForMathlib.sum_norm_sub_spectralProjection_sq_le` (real): the resulting
  `‖P̂ − P‖_F² ≤ 2 n ε² / gap²` sin-Θ bound.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), 315–323.
-/

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/--
**Total cross-energy bound.** With `T`, `S` self-adjoint and close in operator
norm (`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), the sum over all eigenvector pairs of the
squared off-diagonal entries of `S − T` is at most `n ε²`.

For each fixed `j` the inner sum over `i` is `‖(S − T) v̂ⱼ‖²` by Parseval in the
orthonormal eigenbasis of `T`, which is `≤ ε²` since `v̂ⱼ` is a unit vector.
-/
theorem sum_norm_inner_eigenvectorBasis_map_sub_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i : Fin n, ∑ j : Fin n,
      ‖⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜‖ ^ 2
      ≤ (n : ℝ) * ε ^ 2 := by
  set u := hT.eigenvectorBasis hn with hu
  set v := hS.eigenvectorBasis hn with hv
  -- Swap the order of summation so Parseval (over `i`) is the inner sum.
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin n,
      ∑ i : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 = ‖(S - T) (v j)‖ ^ 2 :=
    fun j => u.sum_sq_norm_inner_right ((S - T) (v j))
  have hunit : ∀ j : Fin n, ‖v j‖ = 1 := fun j => v.orthonormal.1 j
  calc ∑ j : Fin n, ∑ i : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
      = ∑ j : Fin n, ‖(S - T) (v j)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => hinner j
    _ ≤ ∑ _j : Fin n, ε ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ‖(S - T) (v j)‖ ≤ ε := by
          have := hε (v j); rwa [hunit j, mul_one] at this
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (n : ℝ) * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/--
**Davis–Kahan cross-block bound (elementary finite-dimensional form).**
Suppose `T`, `S` are self-adjoint, close in operator norm
(`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), and there is a positive `gap` separating the first
`d` eigenvalues of `T` from the trailing eigenvalues of `S`
(`(i : ℕ) < d → d ≤ (j : ℕ) → gap ≤ |λᵢ(T) − λⱼ(S)|`).  Then the total squared
overlap between the leading eigenvectors of `T` and the trailing eigenvectors of
`S` is bounded: `∑_{i < d} ∑_{d ≤ j} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ n ε² / gap²`.
-/
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ (n : ℝ) * ε ^ 2 / gap ^ 2 := by
  classical
  set u := hT.eigenvectorBasis hn with hu
  set v := hS.eigenvectorBasis hn with hv
  -- Per-pair: `gap² ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖²` for cross pairs.
  have hpair : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ^ 2 * ‖⟪u i, v j⟫_𝕜‖ ^ 2 ≤ ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 := by
    intro i j hi hj
    -- The cross-term identity turns the perturbation entry into the eigenvalue
    -- difference times the overlap.
    have hnorm : ‖⟪u i, (S - T) (v j)⟫_𝕜‖
        = |hS.eigenvalues hn j - hT.eigenvalues hn i| * ‖⟪u i, v j⟫_𝕜‖ := by
      rw [hu, hv, inner_eigenvectorBasis_map_sub_eigenvectorBasis hT hS hn i j,
        norm_mul, RCLike.norm_ofReal]
    have hsq : ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
        = (hS.eigenvalues hn j - hT.eigenvalues hn i) ^ 2 * ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
      rw [hnorm, mul_pow, sq_abs]
    rw [hsq]
    have hg : gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := hgap i j hi hj
    have hsqgap : gap ^ 2 ≤ (hS.eigenvalues hn j - hT.eigenvalues hn i) ^ 2 := by
      have := mul_self_le_mul_self hgap_pos.le hg
      rw [← sq, ← sq, sq_abs] at this
      have hflip : (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
          = (hS.eigenvalues hn j - hT.eigenvalues hn i) ^ 2 := by ring
      rwa [hflip] at this
    exact mul_le_mul_of_nonneg_right hsqgap (sq_nonneg _)
  -- Sum the per-pair bound over the cross block.
  have hcross : gap ^ 2 * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          ‖⟪u i, v j⟫_𝕜‖ ^ 2)
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    exact hpair i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  -- Bound the cross-block RHS by the full double sum (all terms nonneg).
  have hsub : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
      ≤ ∑ i : Fin n, ∑ j : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 := by
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
              ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
        ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
            ∑ j : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => sq_nonneg _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- Chain: gap² · CROSS ≤ full cross-energy ≤ n ε².
  have htotal : gap ^ 2 * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          ‖⟪u i, v j⟫_𝕜‖ ^ 2)
      ≤ (n : ℝ) * ε ^ 2 :=
    (hcross.trans hsub).trans (by
      rw [hu, hv]; exact sum_norm_inner_eigenvectorBasis_map_sub_sq_le hT hS hn hε)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < gap ^ 2), mul_comm]
  exact htotal

/-! ### Rank-`d` population structure: gap from an eigenvalue floor

The common statistical setup (Yu–Wang–Samworth): the population operator `T` is
positive semidefinite of rank `d` with a spectral floor `α` on its nonzero
eigenvalues, and the sample `S` is `ε`-operator-close with `ε ≤ α / 2`.  Weyl's
inequality then pushes every trailing sample eigenvalue below `α / 2`, giving a
population eigengap of `α / 2` and a clean `4 n ε² / α²` cross-block bound. -/

/--
**Gap from rank and eigenvalue floor.**  If `T`'s leading `d` (sorted)
eigenvalues are at least `α` and its trailing eigenvalues vanish, and `S` is
`ε`-operator-close to `T` with `ε ≤ α / 2`, then every leading eigenvalue of `T`
is separated from every trailing eigenvalue of `S` by at least `α / 2`.  This is
exactly the gap hypothesis of `sum_cross_norm_inner_eigenvectorBasis_sq_le`.
-/
theorem gap_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ}
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      α / 2 ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := by
  intro i j hi hj
  have hweyl := abs_eigenvalues_sub_le hT hS hn hε j
  have hTj : hT.eigenvalues hn j = 0 := htail j hj
  have hSj_abs : |hS.eigenvalues hn j| ≤ ε := by
    have : |hT.eigenvalues hn j - hS.eigenvalues hn j| ≤ ε := hweyl
    rw [hTj] at this
    simpa [abs_sub_comm] using this
  have hSj_le : hS.eigenvalues hn j ≤ α / 2 :=
    le_trans (le_trans (le_abs_self _) hSj_abs) hsmall
  have hdiff : α / 2 ≤ hT.eigenvalues hn i - hS.eigenvalues hn j := by
    have := hα i hi; linarith
  exact le_trans hdiff (le_abs_self _)

/--
**Davis–Kahan cross-block bound under rank-`d` population structure.**
Composition of `gap_of_rank_floor` with
`sum_cross_norm_inner_eigenvectorBasis_sq_le`: when `T` is positive semidefinite
of rank `d` with spectral floor `α` and `S` is `ε`-operator-close with
`ε ≤ α / 2`, the squared overlap between the leading eigenvectors of `T` and the
trailing eigenvectors of `S` is at most `4 n ε² / α²`.
-/
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
  have hε' : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    have hflip : (T - S) x = -((S - T) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [hflip, norm_neg]; exact hε x
  have hgap := gap_of_rank_floor hT hS hn d hα htail hε' hsmall
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
        ≤ (n : ℝ) * ε ^ 2 / (α / 2) ^ 2 :=
          sum_cross_norm_inner_eigenvectorBasis_sq_le hT hS hn d
            (by positivity : (0 : ℝ) < α / 2) hgap hε
    _ = 4 * (n : ℝ) * ε ^ 2 / α ^ 2 := by field_simp; ring

/-! ### Projector (canonical sin-Θ) form over `ℝ`

The cross-block sum is exactly half the squared Frobenius distance between the
two rank-`d` spectral projectors.  We record this over a real inner product
space, where the conjugation bookkeeping is trivial; it turns the cross-block
bounds above into the canonical `‖P̂ − P‖_F²` Davis–Kahan sin-Θ statement. -/

section RealProjector

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ}

open scoped RealInnerProductSpace

/-- The orthogonal projection onto the span of the first `d` vectors of an
orthonormal basis `b`, as a linear map `x ↦ ∑_{i < d} ⟪bᵢ, x⟫ • bᵢ`. -/
noncomputable def spectralProjection (b : OrthonormalBasis (Fin m) ℝ F) (d : ℕ) :
    F →ₗ[ℝ] F :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d),
    LinearMap.smulRight ((innerSL ℝ (b i)).toLinearMap) (b i)

omit [FiniteDimensional ℝ F] in
theorem spectralProjection_apply (b : OrthonormalBasis (Fin m) ℝ F) (d : ℕ) (x : F) :
    spectralProjection b d x
      = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d), ⟪b i, x⟫ • b i := by
  simp [spectralProjection, LinearMap.sum_apply, LinearMap.smulRight_apply]

omit [FiniteDimensional ℝ F] in
/-- On a vector of its own basis, the projector keeps it iff its index is `< d`. -/
theorem spectralProjection_apply_self (b : OrthonormalBasis (Fin m) ℝ F) (d : ℕ)
    (k : Fin m) :
    spectralProjection b d (b k) = if (k : ℕ) < d then b k else 0 := by
  classical
  rw [spectralProjection_apply]
  have hk : ∀ i, ⟪b i, b k⟫ • b i = if i = k then b k else 0 := by
    intro i
    rw [orthonormal_iff_ite.mp b.orthonormal i k]
    split <;> rename_i h
    · rw [h, one_smul]
    · rw [zero_smul]
  rw [Finset.sum_congr rfl fun i _ => hk i, Finset.sum_ite_eq' _ k]
  simp [Finset.mem_filter]

omit [FiniteDimensional ℝ F] in
/--
**Projector form of the Davis–Kahan identity (real).** For two orthonormal bases
`u`, `v` of a finite-dimensional real inner product space and a cutoff `d`, the
squared Frobenius distance between the two rank-`d` spectral projectors (computed
in the `u` basis) is twice the cross-block overlap sum:
`∑ₖ ‖(P_v − P_u) uₖ‖² = 2 · ∑_{i < d} ∑_{j ≥ d} ⟪uᵢ, vⱼ⟫²`.

(The left side `∑ₖ ‖A uₖ‖²` is the Frobenius / Hilbert–Schmidt norm² of
`A = P_v − P_u`, evaluated in the orthonormal basis `u`.)
-/
theorem sum_norm_sub_spectralProjection_sq_eq
    (u v : OrthonormalBasis (Fin m) ℝ F) (d : ℕ) :
    ∑ k, ‖(spectralProjection v d - spectralProjection u d) (u k)‖ ^ 2
      = 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => d ≤ (j : ℕ)), ⟪u i, v j⟫ ^ 2 := by
  classical
  set s := Finset.univ.filter (fun i : Fin m => (i : ℕ) < d) with hs
  set t := Finset.univ.filter (fun j : Fin m => d ≤ (j : ℕ)) with ht
  -- `P_u uₖ = [k < d] uₖ`,  `P_v uₖ = ∑_{j<d} ⟪vⱼ,uₖ⟫ vⱼ`.
  have hP : ∀ k, spectralProjection u d (u k) = if (k : ℕ) < d then u k else 0 :=
    spectralProjection_apply_self u d
  have hQ : ∀ k, spectralProjection v d (u k) = ∑ j ∈ s, ⟪v j, u k⟫ • v j := fun k =>
    spectralProjection_apply v d (u k)
  -- Expand each squared norm via `‖a - b‖² = ‖a‖² - 2⟪a,b⟫ + ‖b‖²`.
  have hterm : ∀ k, ‖(spectralProjection v d - spectralProjection u d) (u k)‖ ^ 2
      = ‖spectralProjection v d (u k)‖ ^ 2
        - 2 * ⟪spectralProjection v d (u k), spectralProjection u d (u k)⟫
        + ‖spectralProjection u d (u k)‖ ^ 2 := by
    intro k
    rw [LinearMap.sub_apply, ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm
      (spectralProjection u d (u k)) (spectralProjection v d (u k))]
    ring
  -- `‖P_v uₖ‖² = ∑_{j<d} ⟪vⱼ,uₖ⟫²`.
  have hQnorm : ∀ k, ‖spectralProjection v d (u k)‖ ^ 2 = ∑ j ∈ s, ⟪v j, u k⟫ ^ 2 := by
    intro k
    rw [← real_inner_self_eq_norm_sq, hQ k, v.orthonormal.inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [pow_two]
  -- `‖P_u uₖ‖² = [k < d]`.
  have hPnorm : ∀ k, ‖spectralProjection u d (u k)‖ ^ 2 = if (k : ℕ) < d then 1 else 0 := by
    intro k
    rw [hP k]
    split
    · simp [u.orthonormal.1 k]
    · simp
  -- `⟪P_v uₖ, P_u uₖ⟫ = [k < d] · ∑_{j<d} ⟪vⱼ,uₖ⟫²`.
  have hcross : ∀ k, ⟪spectralProjection v d (u k), spectralProjection u d (u k)⟫
      = if (k : ℕ) < d then ∑ j ∈ s, ⟪v j, u k⟫ ^ 2 else 0 := by
    intro k
    rw [hP k]
    split
    · rw [hQ k, sum_inner]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_left, ← pow_two]
    · simp
  -- The three component sums.
  have hsumP : ∑ k, ‖spectralProjection u d (u k)‖ ^ 2 = (s.card : ℝ) := by
    simp_rw [hPnorm]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsumQ : ∑ k, ‖spectralProjection v d (u k)‖ ^ 2 = (s.card : ℝ) := by
    simp_rw [hQnorm, Finset.sum_comm (s := Finset.univ) (t := s)]
    have hrow : ∀ j ∈ s, ∑ k, ⟪v j, u k⟫ ^ 2 = 1 := by
      intro j _
      have hpar := u.sum_sq_norm_inner_right (v j)
      simp only [Real.norm_eq_abs, sq_abs] at hpar
      rw [show (1 : ℝ) = ‖v j‖ ^ 2 by rw [v.orthonormal.1 j]; norm_num, ← hpar]
      exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsumC : ∑ k, ⟪spectralProjection v d (u k), spectralProjection u d (u k)⟫
      = ∑ k ∈ s, ∑ j ∈ s, ⟪v j, u k⟫ ^ 2 := by
    simp_rw [hcross]
    rw [← Finset.sum_filter]
  -- The cross-block sum equals `d − ∑_{i<d,j<d} ⟪uᵢ,vⱼ⟫²` (Parseval over `v`).
  have hsplit : ∑ i ∈ s, ∑ j ∈ t, ⟪u i, v j⟫ ^ 2
      = (s.card : ℝ) - ∑ k ∈ s, ∑ j ∈ s, ⟪v j, u k⟫ ^ 2 := by
    have hrow : ∀ i ∈ s, ∑ j ∈ s, ⟪v j, u i⟫ ^ 2 + ∑ j ∈ t, ⟪u i, v j⟫ ^ 2 = 1 := by
      intro i _
      have hpar := v.sum_sq_norm_inner_right (u i)
      simp only [Real.norm_eq_abs, sq_abs] at hpar
      have hsplit_univ : ∑ j, ⟪v j, u i⟫ ^ 2
          = ∑ j ∈ s, ⟪v j, u i⟫ ^ 2 + ∑ j ∈ t, ⟪v j, u i⟫ ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin m => (j : ℕ) < d)]
        congr 1
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j; simp [ht, not_lt]
      have hcommt : ∑ j ∈ t, ⟪u i, v j⟫ ^ 2 = ∑ j ∈ t, ⟪v j, u i⟫ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
      rw [hcommt, ← hsplit_univ, hpar, u.orthonormal.1 i]; norm_num
    have hsum_one : ∑ i ∈ s, (∑ j ∈ s, ⟪v j, u i⟫ ^ 2 + ∑ j ∈ t, ⟪u i, v j⟫ ^ 2)
        = (s.card : ℝ) := by
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib] at hsum_one
    linarith [hsum_one]
  -- Assemble: `∑ₖ ‖(Q−P)uₖ‖² = ∑‖Quₖ‖² − 2∑⟪Quₖ,Puₖ⟫ + ∑‖Puₖ‖² = 2·cross`.
  calc ∑ k, ‖(spectralProjection v d - spectralProjection u d) (u k)‖ ^ 2
      = ∑ k, ‖spectralProjection v d (u k)‖ ^ 2
          - 2 * (∑ k, ⟪spectralProjection v d (u k), spectralProjection u d (u k)⟫)
          + ∑ k, ‖spectralProjection u d (u k)‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ i ∈ s, ∑ j ∈ t, ⟪u i, v j⟫ ^ 2) := by
        rw [hsumP, hsumQ, hsumC, hsplit]; ring

/--
**Davis–Kahan, projector form (real).** The squared Frobenius distance between
the rank-`d` spectral projectors of two `ε`-operator-close self-adjoint operators
with eigengap `gap` is at most `2 n ε² / gap²`.
-/
theorem sum_norm_sub_spectralProjection_sq_le {T S : F →ₗ[ℝ] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ F = m)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin m, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : F, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ k, ‖(spectralProjection (hS.eigenvectorBasis hn) d
        - spectralProjection (hT.eigenvectorBasis hn) d) (hT.eigenvectorBasis hn k)‖ ^ 2
      ≤ 2 * ((m : ℝ) * ε ^ 2 / gap ^ 2) := by
  rw [sum_norm_sub_spectralProjection_sq_eq]
  have hbound := sum_cross_norm_inner_eigenvectorBasis_sq_le hT hS hn d hgap_pos hgap hε
  have hb : ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => d ≤ (j : ℕ)),
        ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫ ^ 2
      ≤ (m : ℝ) * ε ^ 2 / gap ^ 2 := by
    refine le_trans (le_of_eq ?_) hbound
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  linarith [hb]

end RealProjector

end ForMathlib
