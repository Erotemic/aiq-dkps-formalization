/-
# AIQ DKPS ForMathlib inventory challenge: Operator spectral perturbation and projections

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/Spectrum.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Eigenvector cross-term identity for a perturbation

For symmetric operators `T`, `S` on a finite-dimensional inner product space,
with `u i` the `i`-th eigenvector of `T` (eigenvalue `λ i`) and `v j` the
`j`-th eigenvector of `S` (eigenvalue `μ j`),

`⟪u i, (S - T) (v j)⟫ = (μ j - λ i) * ⟪u i, v j⟫`.

This three-line identity is the seed of every Davis–Kahan-style subspace
perturbation bound: cross terms between well-separated parts of the spectra
are controlled by the perturbation `S - T` divided by the eigenvalue gap.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/--
**Cross-term identity.** The matrix entry of the perturbation `S - T` between
the `i`-th eigenvector of `T` and the `j`-th eigenvector of `S` is the
eigenvalue difference times the overlap of the two eigenvectors.
-/
theorem inner_eigenvectorBasis_map_sub_eigenvectorBasis
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i j : Fin n) :
    ⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hS.eigenvalues hn j - hT.eigenvalues hn i : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/CourantFischer.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Courant–Fischer min-max and Weyl's eigenvalue perturbation inequality

For a symmetric operator `T` on a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ`, Mathlib provides the decreasingly sorted eigenvalues
`LinearMap.IsSymmetric.eigenvalues` together with an orthonormal eigenbasis
`LinearMap.IsSymmetric.eigenvectorBasis`.  This file proves the discrete
Courant–Fischer characterization of these sorted eigenvalues and derives from
it Weyl's eigenvalue perturbation inequality
`|λₖ(T) − λₖ(S)| ≤ ε` whenever `∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`.

## Main results

* `ForMathlib.re_inner_map_self_eq_sum_eigenvalues_mul_sq`: diagonalization of
  the quadratic form, `re ⟪T x, x⟫ = ∑ i, λᵢ * ‖(b.repr x) i‖ ^ 2` in the
  eigenbasis `b` of `T`.
* `ForMathlib.exists_unit_vector_re_inner_le_eigenvalue`: Courant–Fischer,
  upper direction — every subspace of dimension `k + 1` contains a unit vector
  `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`.
* `ForMathlib.forall_unit_vector_eigenvalue_le_re_inner`: Courant–Fischer,
  lower direction — some subspace of dimension `k + 1` satisfies
  `λₖ(T) ≤ re ⟪T x, x⟫` for all unit vectors `x` in it.
* `ForMathlib.abs_eigenvalues_sub_le`: **Weyl's inequality** — the `k`-th
  sorted eigenvalues of two symmetric operators differ by at most an operator
  norm bound on their difference.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Theorem 4.2.6
  (Courant–Fischer) and Theorem 4.3.1 (Weyl).
* R. Bhatia, *Matrix Analysis*, Corollary III.2.6 (Weyl).
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-! ### Spectral subspaces

Given an orthonormal basis `b` and a predicate `p` on the index set, the
subspace spanned by the basis vectors selected by `p`.  We record its dimension
(the number of selected indices) and the key orthogonality fact: a vector in
this subspace has vanishing `b`-coordinates outside `p`. -/

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices `i`
satisfying `p i`. -/
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

/-- A spectral subspace has dimension equal to the number of selected indices. -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  sorry
theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  sorry
variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- The quadratic form `re ⟪T x, x⟫` of a symmetric operator `T` expressed in
its eigenbasis: it is the eigenvalue-weighted sum of the squared norms of the
coordinates of `x`.  This is the diagonalization of the quadratic form.  (For
symmetric `T` the inner product `⟪T x, x⟫` is real, so no information is lost
by taking the real part.) -/
theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  sorry
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  sorry
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  sorry
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  sorry
theorem abs_eigenvalues_sub_le_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`DavisKahan.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


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
* `ForMathlib.sum_norm_sub_starProjection_span_sq_eq`: the canonical projector
  identity over `RCLike 𝕜`, phrased with `Submodule.starProjection` of
  orthonormal-subfamily spans (arbitrary index subsets).
* `ForMathlib.sum_norm_sub_starProjection_span_sq_le`: the resulting
  `‖P̂ − P‖_F² ≤ 2 n ε² / gap²` Davis–Kahan sin-Θ bound.

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
  sorry
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
  sorry
theorem gap_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ}
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      α / 2 ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := by
  sorry
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

/--
**Projection onto the span of an orthonormal subfamily.** For an orthonormal
family `w` and a finite index set `s`, the orthogonal projection onto
`span 𝕜 (w '' s)` acts as `x ↦ ∑ i ∈ s, ⟪w i, x⟫ • w i`.  (No finite-dimensionality
of the ambient space: the finite span carries its own projection.)
-/
theorem Orthonormal.starProjection_span_image_apply {ι : Type*} {w : ι → F}
    (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (x : F) :
    (Submodule.span 𝕜 (w '' ↑s)).starProjection x = ∑ i ∈ s, ⟪w i, x⟫_𝕜 • w i := by
  sorry
theorem Orthonormal.starProjection_span_image_apply_self {ι : Type*} [DecidableEq ι]
    {w : ι → F} (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (k : ι) :
    (Submodule.span 𝕜 (w '' ↑s)).starProjection (w k) = if k ∈ s then w k else 0 := by
  sorry
theorem Orthonormal.norm_sq_starProjection_span_image {ι : Type*} {w : ι → F}
    (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (x : F) :
    ‖(Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ ^ 2 = ∑ i ∈ s, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  sorry
variable [FiniteDimensional 𝕜 F] {m : ℕ}

/--
**Projector form of the Davis–Kahan identity.** The squared Frobenius distance
(computed in the basis `u`) between the orthogonal projections onto
`span (v '' s)` and `span (u '' s)` is twice the cross overlap sum.
-/
theorem sum_norm_sub_starProjection_span_sq_eq (u v : OrthonormalBasis (Fin m) 𝕜 F)
    (s : Finset (Fin m)) :
    ∑ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = 2 * ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  sorry
/--
**Davis–Kahan, projector form.** `‖P̂ − P‖_F² ≤ 2 m ε² / gap²` for the
projections onto the leading-`d` spectral subspaces.
-/
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
