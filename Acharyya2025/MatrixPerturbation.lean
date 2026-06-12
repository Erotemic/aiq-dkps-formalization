/-
WP6-core — matrix-world capstone (transport layer) of `planning/acharyya-plan.md`.

The operator-world configuration-perturbation theorem
`Acharyya2025.ConfigPerturbation.exists_isometry_configError_spectralConfig_le`
is stated for symmetric operators `T, S` on `EuclideanSpace ℝ (Fin n)` with the
sorted-eigenvalue hypotheses (spectral floor `α`, rank-`d` tail, top eigenvalue
`≤ Λ`).  This file is the *transport layer* that lets the matrix world
(`B, Bhat : Matrix (Fin n) (Fin n) ℝ`) invoke that theorem.

Given a population Gram matrix `B` that is positive semidefinite with
`B.rank ≤ d` and an entrywise-close Hermitian sample `Bhat`, set
`T := Matrix.toEuclideanLin B`, `S := Matrix.toEuclideanLin Bhat`.  We prove:

* `sortedEigenvalues_nonneg`  — every sorted eigenvalue of `T` is `≥ 0`
  (PSD ⇒ `IsPositive` ⇒ nonneg eigenvalues);
* `sortedEigenvalues_tail_eq_zero` — the sorted eigenvalues of `T` from index
  `d` on vanish (rank transport: the matrix rank equals the finrank of the
  operator range, and a `>d`-block of nonzero eigenvalues would force the range
  to have finrank `> d`);
* `gram_spectralConfig_eq` — the Gram matrix of the spectral configuration
  `spectralConfig T` equals `B` (operator spectral expansion evaluated at the
  standard basis vectors);
* `exists_isometry_configError_le_of_entrywise_close` — the **matrix-world
  capstone**: for any external configuration `ψ` realizing `B` as its Gram
  matrix, the sample spectral embedding `spectralConfig S`, transported by a
  single linear isometry `W`, is `configBound`-close to `ψ`.

The capstone assembles the operator bound (via `OperatorBridge`), the rank/PSD
eigenvalue transport, the Gram identity, and Procrustes rigidity
(`Acharyya2025.Procrustes`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2024.Common
import Acharyya2025.ConfigPerturbation
import Acharyya2025.OperatorBridge
import Acharyya2025.Procrustes
import Acharyya2025.GramRealization

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix
open Module (finrank)

namespace Acharyya2025.MatrixPerturbation

open Acharyya2025.ConfigPerturbation
open Acharyya2025.OperatorBridge

variable {n d : ℕ}

/-- The canonical finrank witness for `EuclideanSpace ℝ (Fin n)`. -/
private theorem hn_eq : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin

/-- The symmetric-operator structure of `toEuclideanLin B` for Hermitian `B`. -/
noncomputable def opSym {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    (Matrix.toEuclideanLin B).IsSymmetric :=
  isSymmetric_toEuclideanLin_of_isHermitian hB

/-- The sorted (decreasing) eigenvalues of the operator `toEuclideanLin B`
attached to a Hermitian `B`.  Consumers state spectral floors against this. -/
noncomputable def sortedEigenvalues {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) : Fin n → ℝ :=
  (opSym hB).eigenvalues hn_eq

/-! ### Deliverable (2a): nonnegativity of the sorted eigenvalues

A positive semidefinite matrix `B` induces a *positive* operator
`toEuclideanLin B`: the quadratic form `⟪T x, x⟫` equals the matrix quadratic
form `ofLp x ⬝ᵥ (B *ᵥ ofLp x)`, which is `≥ 0` by definition of `PosSemidef`.
`LinearMap.IsPositive.nonneg_eigenvalues` then gives nonnegativity. -/

/-- The quadratic form of `toEuclideanLin B` equals the matrix quadratic form
`star x ⬝ᵥ (B *ᵥ x)` on the underlying coordinate vector. -/
private theorem inner_toEuclideanLin_self {B : Matrix (Fin n) (Fin n) ℝ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanLin B x, x⟫_ℝ
      = star (WithLp.ofLp x) ⬝ᵥ (B *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  show WithLp.ofLp x ⬝ᵥ star (B *ᵥ WithLp.ofLp x) = _
  -- over ℝ, `star = id`.
  simp only [star_trivial]

/-- A positive semidefinite matrix induces a positive operator. -/
theorem isPositive_toEuclideanLin {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    (Matrix.toEuclideanLin B).IsPositive := by
  refine ⟨opSym hB.isHermitian, fun x => ?_⟩
  rw [inner_toEuclideanLin_self x]
  -- the inner product is real, so `re` is the identity
  simpa using hB.dotProduct_mulVec_nonneg (WithLp.ofLp x)

/-- **Deliverable (2a).**  Every sorted eigenvalue of `toEuclideanLin B` is `≥ 0`
for positive semidefinite `B`. -/
theorem sortedEigenvalues_nonneg {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    (i : Fin n) : 0 ≤ sortedEigenvalues hB.isHermitian i :=
  (isPositive_toEuclideanLin hB).nonneg_eigenvalues hn_eq i

/-! ### Deliverable (2b): tail eigenvalues vanish (rank transport)

The matrix rank of `B` equals the finrank of the range of `toEuclideanLin B`
(the matrix rank is the finrank of the range of `mulVecLin`, which corresponds
to the range of `toEuclideanLin` under the canonical orthonormal basis).  If a
sorted eigenvalue `λ_j ≠ 0` with `j ≥ d`, then by antitonicity and
nonnegativity all `λ_i ≥ λ_j > 0` for `i ≤ j`, so the `≥ d+1` eigenvectors
`u_i = λ_i⁻¹ • T u_i` lie in `range T` and are orthonormal hence linearly
independent, forcing `finrank (range T) ≥ d+1 > rank B`, a contradiction. -/

/-- The matrix rank of `B` equals the finrank of the range of `toEuclideanLin B`. -/
theorem rank_eq_finrank_range_toEuclideanLin (B : Matrix (Fin n) (Fin n) ℝ) :
    B.rank = finrank ℝ (LinearMap.range (Matrix.toEuclideanLin B)) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin B
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- An eigenvector with nonzero eigenvalue lies in the range of the operator:
`u = λ⁻¹ • (T u)` when `T u = λ • u` and `λ ≠ 0`. -/
private theorem eigenvector_mem_range {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) (i : Fin n) (hi : sortedEigenvalues hB i ≠ 0) :
    (opSym hB).eigenvectorBasis hn_eq i ∈ LinearMap.range (Matrix.toEuclideanLin B) := by
  refine ⟨(sortedEigenvalues hB i)⁻¹ • (opSym hB).eigenvectorBasis hn_eq i, ?_⟩
  rw [map_smul, (opSym hB).apply_eigenvectorBasis]
  show (sortedEigenvalues hB i)⁻¹ •
      ((sortedEigenvalues hB i : ℝ) • (opSym hB).eigenvectorBasis hn_eq i) = _
  rw [smul_smul, inv_mul_cancel₀ hi, one_smul]

/-- **Deliverable (2b).**  For positive semidefinite `B` with `B.rank ≤ d`, the
sorted eigenvalues of `toEuclideanLin B` vanish from index `d` on. -/
theorem sortedEigenvalues_tail_eq_zero {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) {d : ℕ} (hrank : B.rank ≤ d) :
    ∀ j : Fin n, d ≤ (j : ℕ) → sortedEigenvalues hB.isHermitian j = 0 := by
  classical
  intro j hj
  by_contra hne
  -- the `j`-th eigenvalue is strictly positive.
  have hjpos : 0 < sortedEigenvalues hB.isHermitian j :=
    (sortedEigenvalues_nonneg hB j).lt_of_ne (Ne.symm hne)
  set T := Matrix.toEuclideanLin B with hT
  set hS := opSym hB.isHermitian with hSdef
  set u := hS.eigenvectorBasis hn_eq with hu
  -- The `(j+1)`-element family of leading eigenvectors, valued in `range T`.
  -- index by `Fin (j.val + 1)`; the underlying `Fin n` index has value `≤ j`.
  have hidx : ∀ m : Fin ((j : ℕ) + 1), ((m : ℕ)) < n := by
    intro m; exact lt_of_le_of_lt (Nat.lt_succ_iff.mp m.2) j.2
  set g : Fin ((j : ℕ) + 1) → Fin n := fun m => ⟨(m : ℕ), hidx m⟩ with hg
  -- each eigenvalue in the family is positive (antitone, dominates the j-th).
  have hpos : ∀ m : Fin ((j : ℕ) + 1), 0 < sortedEigenvalues hB.isHermitian (g m) := by
    intro m
    have hle : g m ≤ j := by
      rw [Fin.le_def, hg]; exact Nat.lt_succ_iff.mp m.2
    have hanti := hS.eigenvalues_antitone hn_eq hle
    -- the eigenvalue at `g m` dominates the (positive) eigenvalue at `j`.
    exact lt_of_lt_of_le hjpos hanti
  have hne' : ∀ m : Fin ((j : ℕ) + 1), sortedEigenvalues hB.isHermitian (g m) ≠ 0 :=
    fun m => ne_of_gt (hpos m)
  -- the family valued in `range T`.
  set f : Fin ((j : ℕ) + 1) → LinearMap.range T :=
    fun m => ⟨u (g m), eigenvector_mem_range hB.isHermitian (g m) (hne' m)⟩ with hf
  -- `f` is linearly independent: orthonormal eigenvectors, lifted to the submodule.
  have hortho : Orthonormal ℝ (fun m : Fin ((j : ℕ) + 1) => u (g m)) := by
    refine (hS.eigenvectorBasis hn_eq).orthonormal.comp g ?_
    intro m₁ m₂ hgm
    apply Fin.ext
    have : ((g m₁ : Fin n) : ℕ) = ((g m₂ : Fin n) : ℕ) := by rw [hgm]
    simpa [hg] using this
  have hli : LinearIndependent ℝ f := by
    refine LinearIndependent.of_comp (LinearMap.range T).subtype ?_
    have : (LinearMap.range T).subtype ∘ f = fun m : Fin ((j : ℕ) + 1) => u (g m) := by
      funext m; rfl
    rw [this]
    exact hortho.linearIndependent
  -- finrank (range T) ≥ j + 1.
  have hcard : Fintype.card (Fin ((j : ℕ) + 1)) ≤ finrank ℝ (LinearMap.range T) :=
    hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  -- but finrank (range T) = rank B ≤ d ≤ j.
  rw [← rank_eq_finrank_range_toEuclideanLin] at hcard
  omega

/-! ### Deliverable (3): the Gram identity

The Gram matrix of the spectral configuration of `T := toEuclideanLin B` is `B`.
This is the operator spectral expansion `T x = ∑_k λ_k ⟪u_k, x⟫ • u_k`, evaluated
at the standard basis vector `x := single j 1`, whose `i`-th coordinate gives
`B i j`. -/

/-- Entry recovery: the `(i, j)` matrix entry is the `i`-th coordinate of
`T (single j 1)`. -/
private theorem toEuclideanLin_single_apply (B : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (Matrix.toEuclideanLin B (EuclideanSpace.single j (1 : ℝ))) i = B i j := by
  show (B *ᵥ WithLp.ofLp (EuclideanSpace.single j (1 : ℝ))) i = B i j
  rw [PiLp.ofLp_single, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- **Operator spectral expansion (coordinatewise).**
`(T x) i = ∑_k λ_k ⟪u_k, x⟫ u_k(i)`. -/
private theorem toEuclideanLin_apply_eq_sum {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (Matrix.toEuclideanLin B x) i
      = ∑ k : Fin n, sortedEigenvalues hB k
          * ⟪(opSym hB).eigenvectorBasis hn_eq k, x⟫_ℝ
          * ((opSym hB).eigenvectorBasis hn_eq k i) := by
  set hS := opSym hB with hSdef
  set u := hS.eigenvectorBasis hn_eq with hu
  -- expand `x` in the eigenbasis, apply `T`, use the diagonal action.
  have hTx : Matrix.toEuclideanLin B x
      = ∑ k : Fin n, (sortedEigenvalues hB k * ⟪u k, x⟫_ℝ) • u k := by
    conv_lhs => rw [← u.sum_repr' x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, hu, hS.apply_eigenvectorBasis]
    rw [smul_smul]
    congr 1
    show ⟪hS.eigenvectorBasis hn_eq k, x⟫_ℝ * (sortedEigenvalues hB k : ℝ) = _
    rw [mul_comm]
  rw [hTx]
  -- read off the `i`-th coordinate of the finite sum.
  have hcoord : (∑ k : Fin n, (sortedEigenvalues hB k * ⟪u k, x⟫_ℝ) • u k) i
      = ∑ k : Fin n, (sortedEigenvalues hB k * ⟪u k, x⟫_ℝ) * (u k) i := by
    show (∑ k : Fin n, (sortedEigenvalues hB k * ⟪u k, x⟫_ℝ) • u k).ofLp i = _
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [WithLp.ofLp_smul]; rfl
  rw [hcoord]

/-- The unsorted operator spectral expansion of a single matrix entry:
`B i j = ∑_k λ_k u_k(i) u_k(j)`. -/
private theorem entry_eq_sum_sorted_eigenvalues {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n, sortedEigenvalues hB k
        * ((opSym hB).eigenvectorBasis hn_eq k i)
        * ((opSym hB).eigenvectorBasis hn_eq k j) := by
  rw [← toEuclideanLin_single_apply B i j, toEuclideanLin_apply_eq_sum hB]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- `⟪u_k, single j 1⟫ = u_k(j)` over ℝ.
  have hinner : ⟪(opSym hB).eigenvectorBasis hn_eq k, EuclideanSpace.single j (1 : ℝ)⟫_ℝ
      = (opSym hB).eigenvectorBasis hn_eq k j := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [hinner]; ring

/-- Local copy of the `castLE`-image reindexing
(`ConfigPerturbation.sum_castLE_eq_filter` is private):
`∑_{m : Fin d} f (castLE m) = ∑_{j : j < d} f j`. -/
private theorem sum_castLE_eq_filter {d : ℕ} (hd : d ≤ n) (f : Fin n → ℝ) :
    ∑ m : Fin d, f (Fin.castLE hd m)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < d), f j := by
  classical
  refine Finset.sum_bij'
    (fun (m : Fin d) _ => Fin.castLE hd m)
    (fun (j : Fin n) hj => ⟨(j : ℕ), (Finset.mem_filter.mp hj).2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro m _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Fin.castLE]⟩
  · intro j _; exact Finset.mem_univ _
  · intro m _; apply Fin.ext; simp [Fin.castLE]
  · intro j _; apply Fin.ext; simp [Fin.castLE]
  · intro m _; rfl

/-- **Deliverable (3): the Gram identity.**  The Gram matrix of the spectral
configuration of `T := toEuclideanLin B` equals `B`, for positive semidefinite
`B` with `B.rank ≤ d`. -/
theorem gram_spectralConfig_eq {d : ℕ} (hd : d ≤ n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) (hrank : B.rank ≤ d) :
    ∀ i j : Fin n,
      (∑ k : Fin d, spectralConfig (Matrix.toEuclideanLin B) (opSym hB.isHermitian) hd i k
          * spectralConfig (Matrix.toEuclideanLin B) (opSym hB.isHermitian) hd j k)
        = B i j := by
  classical
  intro i j
  set hS := opSym hB.isHermitian with hSdef
  set u := hS.eigenvectorBasis hn_eq with hu
  set lam := sortedEigenvalues hB.isHermitian with hlam
  have hlam_nonneg : ∀ k : Fin n, 0 ≤ lam k := fun k => sortedEigenvalues_nonneg hB k
  -- `√λ_{castLE k} · √λ_{castLE k} = λ_{castLE k}` since `λ ≥ 0`.
  have hsqsq : ∀ k : Fin d,
      spectralConfig (Matrix.toEuclideanLin B) hS hd i k
        * spectralConfig (Matrix.toEuclideanLin B) hS hd j k
        = lam (Fin.castLE hd k) * (u (Fin.castLE hd k) i) * (u (Fin.castLE hd k) j) := by
    intro k
    show (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) i)
        * (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) j) = _
    have hsq : Real.sqrt (lam (Fin.castLE hd k)) * Real.sqrt (lam (Fin.castLE hd k))
        = lam (Fin.castLE hd k) :=
      Real.mul_self_sqrt (hlam_nonneg _)
    calc (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) i)
            * (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) j)
        = (Real.sqrt (lam (Fin.castLE hd k)) * Real.sqrt (lam (Fin.castLE hd k)))
            * (u (Fin.castLE hd k) i * u (Fin.castLE hd k) j) := by ring
      _ = lam (Fin.castLE hd k) * (u (Fin.castLE hd k) i) * (u (Fin.castLE hd k) j) := by
            rw [hsq]; ring
  -- the configuration sum over `Fin d` collapses to the leading filtered sum.
  rw [Finset.sum_congr rfl (fun k _ => hsqsq k)]
  rw [sum_castLE_eq_filter hd (fun k : Fin n => lam k * (u k i) * (u k j))]
  -- extend the leading sum to all of `Fin n`: tail terms vanish (`λ = 0`).
  have htail : ∀ k : Fin n, d ≤ (k : ℕ) → lam k = 0 :=
    sortedEigenvalues_tail_eq_zero hB hrank
  have hext : ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < d),
        (lam k * (u k i) * (u k j))
      = ∑ k : Fin n, (lam k * (u k i) * (u k j)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => (k : ℕ) < d)]
    have hzero : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ ((k : ℕ) < d)),
        (lam k * (u k i) * (u k j)) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hge : d ≤ (k : ℕ) := by
        have := (Finset.mem_filter.mp hk).2; omega
      rw [htail k hge]; ring
    rw [hzero, add_zero]
  rw [hext]
  -- the full spectral sum is `B i j`.
  rw [entry_eq_sum_sorted_eigenvalues hB.isHermitian i j]

/-! ### Deliverable (4): the matrix-world capstone

Assemble: operator closeness (`OperatorBridge`), the rank/PSD eigenvalue
transport, the operator-world configuration bound
(`ConfigPerturbation.exists_isometry_configError_spectralConfig_le`), the Gram
identity, and Procrustes rigidity (`Procrustes.exists_linearIsometryEquiv_of_gram_eq`). -/

/-- **Matrix-world capstone.**

Let `B` be a positive semidefinite Gram matrix with `B.rank ≤ d` (population),
and `Bhat` a Hermitian sample matrix entrywise `η`-close to `B`.  Set
`ε := n·η`.  Under the operator-side hypotheses (spectral floor `α`, top
eigenvalue `≤ Λ`, smallness `n·η ≤ α/2`, polar-factor smallness), for *any*
external configuration `ψ` realizing `B` as its Gram matrix, the sample spectral
embedding `spectralConfig (toEuclideanLin Bhat)`, transported by a single linear
isometry `W`, is `configBound n d α Λ (n·η)`-close to `ψ`.

Formalized by Claude Fable 5 (claude-fable-5[1m]). -/
theorem exists_isometry_configError_le_of_entrywise_close
    {n d : ℕ} (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (hBhat : Bhat.IsHermitian) (hrank : B.rank ≤ d)
    {α Λ η : ℝ} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d → α ≤ sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l : Fin n, sortedEigenvalues hB.isHermitian l ≤ Λ)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (hsmall : (n : ℝ) * η ≤ α / 2)
    (hpolar : (d : ℝ) * (4 * (n : ℝ) * ((n : ℝ) * η)^2 / α^2) ≤ 1/2)
    (ψ : Acharyya2024.Config n d)
    (hψ : ∀ i j, (∑ k : Fin d, ψ i k * ψ j k) = B i j) :
    ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      Acharyya2024.ConfigError
        (fun i => W (spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i)) ψ
        ≤ configBound n d α Λ ((n : ℝ) * η) := by
  classical
  set T := Matrix.toEuclideanLin B with hTdef
  set S := Matrix.toEuclideanLin Bhat with hSdef
  set hT := opSym hB.isHermitian with hTsym
  set hSsym := opSym hBhat with hSsymdef
  set ε : ℝ := (n : ℝ) * η with hε
  have hε_nonneg : 0 ≤ ε := by rw [hε]; positivity
  -- operator-norm closeness: `‖(S − T) x‖ ≤ ε ‖x‖`.
  have hclose : ∀ x : EuclideanSpace ℝ (Fin n), ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    have hbridge := matrixL2OperatorClose_of_entrywise
      (A := Bhat) (B := B) (ε := η) hentry
    intro x
    -- `(S − T) x = toEuclideanLin (Bhat − B) x` via `map_sub`.
    have hmapsub : (S - T) x = Matrix.toEuclideanLin (Bhat - B) x := by
      rw [hSdef, hTdef, ← map_sub]
    rw [hmapsub]
    exact hbridge x
  -- the eigenvalue hypotheses, restated against the operator's sorted eigenvalues.
  have hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i := hfloor
  have htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0 :=
    sortedEigenvalues_tail_eq_zero hB hrank
  have hΛ' : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ := hΛ
  -- operator-world configuration bound: alignment `W₀`.
  obtain ⟨W₀, hW₀_isom, hW₀_bound⟩ :=
    exists_isometry_configError_spectralConfig_le hd T S hT hSsym hα_pos hε_nonneg
      hα htail hΛ' hclose hsmall hpolar
  -- Procrustes: Gram(spectralConfig T) = B = Gram(ψ), so an isometry `V` aligns them.
  have hgramT : ∀ i j : Fin n,
      (∑ k : Fin d, spectralConfig T hT hd i k * spectralConfig T hT hd j k) = B i j :=
    gram_spectralConfig_eq hd hB hrank
  obtain ⟨V, hV⟩ := Acharyya2025.Procrustes.exists_linearIsometryEquiv_of_gram_eq
    (spectralConfig T hT hd) ψ (fun i j => by rw [hgramT i j, hψ i j])
  -- the combined isometry `W := V ∘ W₀`.
  refine ⟨V.toLinearMap ∘ₗ W₀, ?_, ?_⟩
  · -- `W` preserves inner products (composition of isometries).
    intro x y
    show ⟪V (W₀ x), V (W₀ y)⟫_ℝ = ⟪x, y⟫_ℝ
    rw [V.inner_map_map, hW₀_isom x y]
  · -- ConfigError comparison: `V` linear isometry preserves norms.
    have hConfigEq : Acharyya2024.ConfigError
        (fun i => (V.toLinearMap ∘ₗ W₀) (spectralConfig S hSsym hd i)) ψ
        = Acharyya2024.ConfigError
            (fun i => W₀ (spectralConfig S hSsym hd i)) (spectralConfig T hT hd) := by
      unfold Acharyya2024.ConfigError
      refine Finset.sum_congr rfl (fun i _ => ?_)
      -- `‖V(W₀ ψ̂ᵢ) − ψᵢ‖ = ‖V(W₀ ψ̂ᵢ) − V(spectralConfig T ᵢ)‖ = ‖W₀ ψ̂ᵢ − spectralConfig T ᵢ‖`.
      have hψi : ψ i = V (spectralConfig T hT hd i) := (hV i).symm
      show ‖V (W₀ (spectralConfig S hSsym hd i)) - ψ i‖
          = ‖W₀ (spectralConfig S hSsym hd i) - spectralConfig T hT hd i‖
      rw [hψi, ← map_sub, V.norm_map]
    rw [hConfigEq]
    exact hW₀_bound

end Acharyya2025.MatrixPerturbation
