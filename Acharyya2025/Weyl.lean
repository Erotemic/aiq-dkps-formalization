/-
Courant–Fischer min-max and Weyl's eigenvalue perturbation inequality for
symmetric operators on a finite-dimensional real inner product space.

This file is paper-agnostic: it develops the discrete Courant–Fischer
characterization of the (decreasingly sorted) eigenvalues of a self-adjoint
operator and derives Weyl's inequality
`|λₖ(T) − λₖ(S)| ≤ ‖T − S‖op` from it.  These are general results and are
intended as Mathlib-contribution candidates; they support WP5 of
`planning/acharyya-plan.md` (the spectral-perturbation bridge for the DKPS
finite-sample concentration results).

References:
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Theorem 4.2.6
  (Courant–Fischer) and Theorem 4.3.1 (Weyl).
* R. Bhatia, *Matrix Analysis*, Corollary III.2.6 (Weyl).

We work in the operator world using Mathlib's sorted spectral API from
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`:
`LinearMap.IsSymmetric.eigenvalues` (decreasing, `eigenvalues_antitone`) and
`LinearMap.IsSymmetric.eigenvectorBasis` (orthonormal eigenbasis).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import ForMathlib.Analysis.InnerProductSpace.CourantFischer

open scoped BigOperators RealInnerProductSpace
open Module (finrank)

namespace Acharyya2025.Weyl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} {T S : E →ₗ[ℝ] E}

/-! ### Spectral subspaces

Given an orthonormal basis `b` and a predicate `p` on the index set, the
subspace spanned by the basis vectors selected by `p`.  We record its dimension
(the number of selected indices) and the key orthogonality fact: a vector in
this subspace has vanishing `b`-coordinates outside `p`. -/

/-- Internal helper (scaffolding for Courant–Fischer).
The subspace spanned by the eigenbasis vectors `b i` for the indices `i`
satisfying the predicate `p`.  Used below to carve out "leading" vs "trailing"
eigenspaces in the min-max argument. -/
-- `b`         : an orthonormal eigenbasis
-- `p`         : selects which basis vectors span the subspace
-- `DecidablePred p` : extra (implicit) assumption beyond the paper (Lean must be
--                     able to decide membership in `p` to form the filtered span)
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → Prop)
    [DecidablePred p] : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i : {i : Fin n // p i} => b i))

omit [FiniteDimensional ℝ E] in
/-- Internal helper.
A spectral subspace has dimension equal to the number of selected indices
(the basis vectors selected by `p` are orthonormal, hence independent). -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → Prop)
    [DecidablePred p] :
    -- Conclusion: dim of the selected-eigenvector span = number of selected indices.
    finrank ℝ (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]

omit [FiniteDimensional ℝ E] in
/-- Internal helper.
A vector in a spectral subspace has zero `b`-coordinate at any index outside
the selecting predicate. -/
theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → Prop)
    [DecidablePred p] {x : E} (hx : x ∈ specSubspace b p)  -- `x` lies in the selected span
    {i : Fin n} (hi : ¬ p i) :                              -- `i` is an unselected index
    -- Conclusion: the `i`-th coordinate of `x` in the eigenbasis vanishes.
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

/-! ### Step 1: the quadratic form in the eigenbasis -/

omit [FiniteDimensional ℝ E] in
/-- Internal helper (Parseval identity).
In any orthonormal basis the squared coordinates of a vector sum to its squared
norm.  Thin wrapper around `OrthonormalBasis.sum_sq_inner_right`. -/
theorem sum_repr_sq_eq_norm_sq (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    -- Conclusion: ∑ᵢ (coordinate i)² = ‖x‖² (Parseval).
    ∑ i : Fin n, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  rw [← b.sum_sq_inner_right x]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [b.repr_apply_apply]

/-- Internal helper (diagonalization of the quadratic form).
The quadratic form `⟪T x, x⟫` expressed in the eigenbasis of the symmetric
operator `T`: it is the eigenvalue-weighted sum of squared coordinates. -/
theorem inner_map_self_eq_sum_eigenvalues_sq
    (hT : T.IsSymmetric)            -- `T` self-adjoint (so it has a real eigenbasis)
    (hn : finrank ℝ E = n)          -- finite-dimensionality: dim E = n (implicit in the paper)
    (x : E) :
    -- Conclusion: ⟪T x, x⟫ = ∑ᵢ λᵢ · (coordinate i of x)²  (diagonal form).
    ⟪T x, x⟫ = ∑ i : Fin n, hT.eigenvalues hn i * ((hT.eigenvectorBasis hn).repr x i) ^ 2 := by
  set b := hT.eigenvectorBasis hn with hb
  -- Expand only the inner `x` (the argument of `T`) in the eigenbasis, then use
  -- linearity and the diagonal action of `T`.
  have hTx : T x = ∑ i : Fin n, b.repr x i • T (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]; simp_rw [map_smul]
  rw [hTx, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [hb, hT.apply_eigenvectorBasis, real_inner_smul_left, real_inner_smul_left,
    ← (hT.eigenvectorBasis hn).repr_apply_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-! ### Step 2: discrete Courant–Fischer directional bounds

The proofs are now thin specializations (at `𝕜 = ℝ`) of the staged Mathlib
candidate `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean`, which
proves them over any `RCLike` field with `RCLike.re ⟪T x, x⟫` in place of
`⟪T x, x⟫`. -/

/-- **Courant–Fischer, upper direction.** On any subspace `V` of dimension
`k + 1` there is a unit vector `x` with `⟪T x, x⟫ ≤ λₖ(T)`.

Proof idea: `V` must intersect the `(n - k)`-dimensional "tail" eigenspace
`span {bᵢ : k ≤ i}` nontrivially by dimension counting; on that intersection
the quadratic form is bounded above by `λₖ` since the involved eigenvalues are
all `≤ λₖ` (eigenvalues are sorted decreasingly).

Internal helper: one of the two directional Courant–Fischer bounds feeding
Weyl's inequality below. -/
theorem exists_unit_vector_inner_le_eigenvalue
    (hT : T.IsSymmetric)               -- `T` self-adjoint
    (hn : finrank ℝ E = n)             -- finite-dimensionality (implicit in the paper)
    (k : Fin n)
    (V : Submodule ℝ E) (hV : finrank ℝ V = (k : ℕ) + 1) :  -- any (k+1)-dim subspace
    -- Conclusion: V contains a unit vector whose Rayleigh quotient is ≤ λₖ(T).
    ∃ x ∈ V, ‖x‖ = 1 ∧ ⟪T x, x⟫ ≤ hT.eigenvalues hn k := by
  simpa using ForMathlib.exists_unit_vector_re_inner_le_eigenvalue hT hn k V hV

/-- **Courant–Fischer, lower direction.** There is a subspace `V` of dimension
`k + 1` on which every unit vector `x` satisfies `λₖ(T) ≤ ⟪T x, x⟫`.

Witness: `V = span {bᵢ : i ≤ k}`; on it the quadratic form is bounded below by
`λₖ` since all involved eigenvalues are `≥ λₖ`.

Internal helper: the second directional Courant–Fischer bound. -/
theorem forall_unit_vector_eigenvalue_le_inner
    (hT : T.IsSymmetric)               -- `T` self-adjoint
    (hn : finrank ℝ E = n)             -- finite-dimensionality (implicit in the paper)
    (k : Fin n) :
    -- Conclusion: some (k+1)-dim subspace has every unit vector's Rayleigh quotient ≥ λₖ(T).
    ∃ V : Submodule ℝ E, finrank ℝ V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ ⟪T x, x⟫ := by
  simpa using ForMathlib.forall_unit_vector_eigenvalue_le_re_inner hT hn k

/-! ### Step 3: Weyl's inequality -/

/-- **Weyl's inequality (standard).** For symmetric operators on a
finite-dimensional real inner product space: the `k`-th (decreasingly sorted)
eigenvalues of `T` and `S` differ by at most the operator norm of `T − S`.

This is the classical eigenvalue-perturbation tool the paper invokes (prose:
"Weyl's Inequality, which puts a bound on the eigenvalue perturbations").  In
the Theorem 2 argument it guarantees the sorted eigenvalues of the sample matrix
B̂ stay close to those of the population B, which (together with the eigenvalue
floor α of Assumption 2) keeps the sample's leading eigenvalues above α/2 and
its trailing ones below — i.e. it provides the eigengap fed to Davis–Kahan.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia,
*Matrix Analysis*, Corollary III.2.6. -/
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)  -- both operators self-adjoint
    (hn : finrank ℝ E = n)                      -- finite-dimensionality (implicit in the paper)
    {ε : ℝ}
    (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖)       -- operator-norm bound: ‖T − S‖op ≤ ε
    (k : Fin n) :
    -- Conclusion: |λₖ(T) − λₖ(S)| ≤ ε (eigenvalues move by at most ‖T − S‖op).
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε :=
  ForMathlib.abs_eigenvalues_sub_le hT hS hn hε k
