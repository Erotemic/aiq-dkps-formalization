/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/CourantFischer.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]); golfed/polished to Mathlib
style by Claude Opus 4.8 (claude-opus-4-8[1m]) following the `mathlib-quality`
rules (dedup, drop unused `set … with` bindings, `simpa`/`rwa` consolidation).
PR-prep by Claude Opus 4.8: the `specSubspace` helper and its two lemmas are a
general orthonormal-subfamily-span fact (not Courant–Fischer-specific) used only
internally, so they are `private` — keeping a `CourantFischer.lean` file's public
surface to Courant–Fischer/Weyl.  Minimal imports: `FiniteDimensional.Lemmas`
dropped (its `finrank` lemmas arrive transitively via `PiL2`/`Spectrum`).
Elegance pass by Claude Opus 4.8 (claude-opus-4-8[1m]): the two min-max directions
previously duplicated a `diagonalize → bound each surviving term → Parseval` calc.
That mechanism is now the pair of dual private lemmas
`re_inner_map_self_le_of_mem_specSubspace` / `le_re_inner_map_self_of_mem_specSubspace`
(the quadratic form on a spectral subspace is bounded by any bound on the selected
eigenvalues), and each Courant–Fischer direction is a two-line application.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

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
  norm bound `ε` on their difference (`∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`).
* `ForMathlib.abs_eigenvalues_sub_le_opNorm`: Weyl's inequality phrased directly
  with the continuous-linear-map operator norm `‖T − S‖`.

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
satisfying `p i`.  Internal scaffolding for the Courant–Fischer proofs (a general
orthonormal-subfamily span, not Courant–Fischer-specific), hence `private`. -/
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

/-- A spectral subspace has dimension equal to the number of selected indices. -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]

/-- A vector in a spectral subspace has zero `b`-coordinate at any index outside
the selecting predicate. -/
private theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E)
    (p : Fin n → Prop) {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  -- `⟪b i, ·⟫` vanishes on the spanning set, hence on the whole span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi j.2
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Parseval: in an orthonormal basis the squared norms of the coordinates sum
to the squared norm.  Thin wrapper around
`OrthonormalBasis.sum_sq_norm_inner_right`. -/
private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

/-! ### The quadratic form in the eigenbasis -/

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
  have key : ⟪T x, x⟫_𝕜
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

/-- On a spectral subspace, the quadratic form is bounded by any bound on the selected
eigenvalues.  If `x ∈ specSubspace b p` (so its coordinates vanish off `p`) and every
selected eigenvalue satisfies `λᵢ ≤ c`, then `re ⟪T x, x⟫ ≤ c ‖x‖²`: the diagonalized form
`∑ λᵢ ‖repr x i‖²` only sees eigenvalues `≤ c`, and the weights sum to `‖x‖²`. -/
theorem re_inner_map_self_le_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp

/-- Dual of `re_inner_map_self_le_of_mem_specSubspace`: if `x ∈ specSubspace b p` and every
selected eigenvalue satisfies `c ≤ λᵢ`, then `c ‖x‖² ≤ re ⟪T x, x⟫`. -/
theorem le_re_inner_map_self_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp

/-! ### Discrete Courant–Fischer directional bounds -/

/-- Counting lemma: the number of indices `i : Fin n` with `k ≤ i` is `n - k`. -/
private theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  have : (Finset.univ.filter (fun i : Fin n => k ≤ i)).card
      = (Finset.Ici k).card := by
    congr 1
    ext i
    simp [Finset.mem_Ici]
  rw [this, Fin.card_Ici]

/-- Counting lemma: the number of indices `i : Fin n` with `i ≤ k` is `k + 1`. -/
private theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  have : (Finset.univ.filter (fun i : Fin n => i ≤ k)).card
      = (Finset.Iic k).card := by
    congr 1
    ext i
    simp [Finset.mem_Iic]
  rw [this, Fin.card_Iic]

/-- **Courant–Fischer, upper direction.** On any subspace `V` of dimension
`k + 1` there is a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`, where `λ` is the
decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the eigenvalues
of the symmetric operator `T`.

Proof idea: `V` must intersect the `(n - k)`-dimensional "tail" eigenspace
`span {bᵢ : k ≤ i}` nontrivially by dimension counting; on that intersection
the quadratic form is bounded above by `λₖ` since the involved eigenvalues are
all `≤ λₖ` (eigenvalues are sorted decreasingly). -/
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := specSubspace b (fun i : Fin n => k ≤ i) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_specSubspace, card_filter_le]
  -- Dimension counting: `finrank V + finrank W > finrank E`, so `V ⊓ W ≠ ⊥`.
  have hsum : finrank 𝕜 V + finrank 𝕜 W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hle := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero] at hle
    have hsup : finrank 𝕜 (↑(V ⊔ W) : Submodule 𝕜 E) ≤ n := by
      rw [← hn]; exact Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  -- The unit vector still lies in `W`; on `W` the selected eigenvalues are all `≤ λₖ`
  -- (antitone), so the spectral-subspace bound gives `re ⟪T x, x⟫ ≤ λₖ · ‖x‖² = λₖ`.
  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        re_inner_map_self_le_of_mem_specSubspace hT hn
          (fun _ hik => hT.eigenvalues_antitone hn hik) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-- **Courant–Fischer, lower direction.** There is a subspace `V` of dimension
`k + 1` on which every unit vector `x` satisfies `λₖ(T) ≤ re ⟪T x, x⟫`, where
`λ` is the decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the
eigenvalues of the symmetric operator `T`.

Witness: `V = span {bᵢ : i ≤ k}`; on it the quadratic form is bounded below by
`λₖ` since all involved eigenvalues are `≥ λₖ`. -/
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨specSubspace b (fun i : Fin n => i ≤ k), ?_, ?_⟩
  · rw [finrank_specSubspace, card_filter_ge]
  · intro x hxV hnx
    -- On this subspace the selected eigenvalues are all `≥ λₖ` (antitone), so the dual
    -- spectral-subspace bound gives `λₖ = λₖ · ‖x‖² ≤ re ⟪T x, x⟫`.
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
          le_re_inner_map_self_of_mem_specSubspace hT hn
            (fun _ hik => hT.eigenvalues_antitone hn hik) hxV

/-! ### Weyl's inequality -/

/-- One-sided Weyl bound: `λₖ(S) − λₖ(T) ≤ ‖S − T‖op`.  This is the core
estimate; Weyl's inequality follows by symmetry.

We take a witness subspace `V` of dimension `k + 1` on which
`λₖ(S) ≤ re ⟪S x, x⟫` (lower direction for `S`), then a unit vector `x ∈ V`
with `re ⟪T x, x⟫ ≤ λₖ(T)` (upper direction for `T`).  The difference is
controlled by Cauchy–Schwarz. -/
private theorem eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ := forall_unit_vector_eigenvalue_le_re_inner hS hn k
  obtain ⟨x, hxV, hnx, hTup⟩ := exists_unit_vector_re_inner_le_eigenvalue hT hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
  -- `λₖ(S) − λₖ(T) ≤ re ⟪Sx,x⟫ − re ⟪Tx,x⟫ = re ⟪(S−T)x,x⟫ ≤ ‖(S−T)x‖ ≤ ε`.
  have hdiff : RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜
      = RCLike.re ⟪(S - T) x, x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_𝕜 ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    have := hε x
    rwa [hnx, mul_one] at this ⊢
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜 := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_𝕜 := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

/-- **Weyl's inequality** for symmetric operators on a finite-dimensional inner
product space over `𝕜 = ℝ, ℂ`: the `k`-th (decreasingly sorted) eigenvalues of
`T` and `S` differ by at most the operator norm of `T − S`.

Here the operator-norm bound is supplied as the hypothesis
`∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia,
*Matrix Analysis*, Corollary III.2.6. -/
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  -- The two directions of `eigenvalues_sub_le`, with the roles of `T` and `S`
  -- swapped, using `‖(T − S) x‖ = ‖(S − T) x‖`.
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

/-- **Weyl's inequality**, operator-norm form.  The `k`-th sorted eigenvalues of
two symmetric operators `T`, `S` on a finite-dimensional inner product space
differ by at most the (continuous-linear-map) operator norm `‖T − S‖` of their
difference.  This is `abs_eigenvalues_sub_le` with the bound supplied by
`ContinuousLinearMap.le_opNorm`. -/
theorem abs_eigenvalues_sub_le_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  refine abs_eigenvalues_sub_le hT hS hn (fun x => ?_) k
  have hx := (LinearMap.toContinuousLinearMap (T - S)).le_opNorm x
  rwa [LinearMap.coe_toContinuousLinearMap'] at hx

/-! ### Spectral subspaces: invariance and orthogonal complement

Public API for consumers of `specSubspace` (the operator-norm sin-Θ and
sin 2θ/tan 2θ spectral corollaries; plan step E3 of
`dev/davis-kahan-expert-completion-plan.md`). -/

/-- A spectral subspace of a symmetric operator (the span of a selected
subfamily of its eigenvectors) is invariant. -/
theorem map_mem_specSubspace (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (p : Fin n → Prop) {x : E}
    (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    T x ∈ specSubspace (hT.eigenvectorBasis hn) p := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [hT.apply_eigenvectorBasis hn j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- The orthogonal complement of a spectral subspace is the complementary
spectral subspace: `(span {bᵢ : p i})ᗮ = span {bᵢ : ¬ p i}`. -/
theorem orthogonal_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    (specSubspace b p)ᗮ = specSubspace b (fun i => ¬ p i) := by
  have hEn : finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · -- the complementary span is orthogonal to the selected span.
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    show ⟪u, b ↑j⟫_𝕜 = 0
    rw [← inner_conj_symm, ← b.repr_apply_apply,
      repr_eq_zero_of_mem_specSubspace b p hu j.2, map_zero]
  · -- dimensions match: `n − #p` on both sides.
    have h1 : finrank 𝕜 (specSubspace b p)
        + finrank 𝕜 ((specSubspace b p)ᗮ : Submodule 𝕜 E) = n := by
      rw [Submodule.finrank_add_finrank_orthogonal, hEn]
    have h2 := finrank_specSubspace b p
    have h3 := finrank_specSubspace b (fun i => ¬ p i)
    have h4 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) p
    have h5 : (Finset.univ : Finset (Fin n)).card = n := by
      rw [Finset.card_univ, Fintype.card_fin]
    omega

end ForMathlib
