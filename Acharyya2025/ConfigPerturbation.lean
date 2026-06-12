/-
Configuration-assembly step of the DKPS finite-sample concentration bridge
(WP7(c4) of `planning/acharyya-plan.md`): the *final* spectral-bridge theorem.

Given a population symmetric operator `T` on `EuclideanSpace ℝ (Fin n)` whose
leading `d` (sorted) eigenvalues are `≥ α > 0` with all trailing eigenvalues `0`
(the doubly-centered CMDS Gram operator, rank `d`, spectral floor `α`, top
eigenvalue `≤ Λ`), and a sample symmetric operator `S` that is `ε`-close in
operator norm (`ε ≤ α/2`), the *spectral embeddings*
`ψ̂ := spectralConfig S`, `ψ := spectralConfig T`
(the classical MDS coordinates `√λ̂_k · v_k(i)` and `√λ_l · u_l(i)`) are close
*up to a linear isometry* `W`:
`ConfigError (W ∘ ψ̂) ψ ≤ CBOUND` with an explicit closed-form `CBOUND` in
`n, d, α, Λ, ε`.

The proof is entirely elementary and coordinatewise — no SVD, no von Neumann
trace inequality.  It reuses the spectral toolkit built in this session:

* `Acharyya2025.Weyl` (Weyl perturbation, eigenbasis Parseval),
* `Acharyya2025.DavisKahan` (cross-energy / sin-Θ bound),
* `Acharyya2025.RankGap` (cross-energy under the rank-`d` floor),
* `Acharyya2025.Overlap` (overlap matrix `Q`, commutator identity,
  `QᵀQ − I` deviation bound),
* `Acharyya2025.PolarFactor` (quantitative polar factor of a near-isometry).

The three-term decomposition `ψ̂W − ψ = Term1 + Term2 + Term3` is:

* `Term1 = (W − M) ψ̂` where `M := toEuclideanLin Qᵀ` is the near-isometry whose
  Gram deviation `QᵀQ − I` is small (polar-factor estimate);
* `Term2 = M ψ̂ − (the QΛ^{1/2}-rescaled vector)` — the commutator term, each
  entry `Q_{kl}(√λ̂_k − √λ_l)` controlled by the Sylvester identity;
* `Term3` — the population reconstruction defect `√λ_l(Σ_k Q_{kl} v_k − u_l)`,
  controlled by the Davis–Kahan cross energy.

Frobenius triangle inequality (`norm_add_le` on `EuclideanSpace ℝ (Fin n × Fin d)`)
combines the three, and `ConfigError ≤ √n · ‖·‖_F` (Cauchy–Schwarz) converts the
Frobenius bound to the `ℓ¹`-over-points `ConfigError`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2024.Common
import Acharyya2025.Weyl
import Acharyya2025.DavisKahan
import Acharyya2025.RankGap
import Acharyya2025.Overlap
import Acharyya2025.PolarFactor

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix
open Module (finrank)

namespace Acharyya2025.ConfigPerturbation

/-! ### The spectral configuration (classical MDS embedding) -/

/-- The **spectral embedding / CMDS configuration** of a symmetric operator `S`:
the `i`-th point has `k`-th coordinate `√λ̂_k · v_k(i)`, where `v_k` is the
`k`-th sample eigenvector and `λ̂_k` the `k`-th (decreasingly sorted) eigenvalue.
`Real.sqrt` clamps possibly-negative trailing eigenvalues to `0` (the CMDS
convention); under the main theorem's hypotheses the top-`d` block eigenvalues
are `≥ α/2 > 0`, so no clamping occurs there.

Paper correspondence: this is the classical-MDS embedding `ψ̂` (when `S` is the
sample Gram operator) or `ψ` (when `S` is the population Gram operator) appearing
in Theorem 2. It is a plain definition, not a claim. -/
noncomputable def spectralConfig {n d : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.IsSymmetric) (hd : d ≤ n) : Acharyya2024.Config n d :=
  fun i => WithLp.toLp 2 (fun k =>
    Real.sqrt (hS.eigenvalues finrank_euclideanSpace_fin (Fin.castLE hd k))
      * hS.eigenvectorBasis finrank_euclideanSpace_fin (Fin.castLE hd k) i)

variable {n d : ℕ}
variable {T S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}

/-- Internal helper / bookkeeping fact: the dimension of `EuclideanSpace ℝ (Fin n)`
is `n`. This is a Lean-specific witness threaded through the eigenvalue/eigenvector
API; it has no mathematical content in the paper. -/
private theorem hn_eq : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin

/-- Internal helper / purely combinatorial reindexing (`Overlap`'s is private):
summing `f` over the image of the inclusion `Fin d ↪ Fin n` equals summing over
the first `d` indices `{ j : (j:ℕ) < d }`. No mathematical content from the paper. -/
private theorem sum_castLE_eq_filter (hd : d ≤ n) (f : Fin n → ℝ) :
    -- Conclusion: the two indexings of the leading `d`-block give the same sum.
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

/-! ### Step 1: Weyl in the top block

The sample top-`d` eigenvalues are squeezed between `α/2` and `Λ + α/2`; the
trailing population eigenvalues vanish.  These per-eigenvalue facts feed the gap
and the `√λ̂` denominators below. -/

/-- Internal helper (Weyl, lower bound). The sample top-block eigenvalues satisfy
`λ̂_k ≥ α/2 > 0`. This is the eigenvalue-stability half of Theorem 2's argument
(Weyl's inequality), specialized to the leading block.

Hypotheses:
* `hd : d ≤ n` — dimension/rank `d` (encodes Assumption 1: the population operator
  has rank `d`).
* `hα` — eigenvalue floor: leading population eigenvalues are `≥ α` (the paper's
  spectral lower bound `λ_d`, the `C1` side of Assumption 2).
* `hε` — the sample `S` is `ε`-close to the population `T` in operator norm.
* `hsmall : ε ≤ α/2` — smallness/perturbation side-condition (extra explicit numeric
  condition beyond the paper's asymptotic statement). -/
private theorem sample_eig_lb (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ}
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) (k : Fin d) :
    -- Conclusion: the `k`-th leading sample eigenvalue is at least `α/2`.
    α / 2 ≤ hS.eigenvalues hn_eq (Fin.castLE hd k) := by
  have hε' : ∀ x, ‖(T - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (T - S) x = -((S - T) x) := by rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  have hweyl := Acharyya2025.Weyl.abs_eigenvalues_sub_le hT hS hn_eq hε' (Fin.castLE hd k)
  rw [abs_le] at hweyl
  have hlt : ((Fin.castLE hd k : Fin n) : ℕ) < d := by simp [Fin.castLE]
  have hαk : α ≤ hT.eigenvalues hn_eq (Fin.castLE hd k) := hα (Fin.castLE hd k) hlt
  linarith [hweyl.2, hαk]

/-- Internal helper (Weyl, upper bound). The sample top-block eigenvalues satisfy
`λ̂_k ≤ Λ + ε`. Eigenvalue-stability (Weyl) companion to `sample_eig_lb`.

Hypotheses:
* `hΛ` — eigenvalue cap `Λ` on all population eigenvalues (the paper's `λ_1` upper
  bound, the `C2` side of Assumption 2).
* `hε` — sample/population operator-norm closeness. -/
private theorem sample_eig_ub (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {Λ ε : ℝ}
    (hΛ : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin d) :
    -- Conclusion: the `k`-th leading sample eigenvalue is at most `Λ + ε`.
    hS.eigenvalues hn_eq (Fin.castLE hd k) ≤ Λ + ε := by
  have hε' : ∀ x, ‖(T - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (T - S) x = -((S - T) x) := by rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  have hweyl := Acharyya2025.Weyl.abs_eigenvalues_sub_le hT hS hn_eq hε' (Fin.castLE hd k)
  rw [abs_le] at hweyl
  linarith [hweyl.1, hΛ (Fin.castLE hd k)]

/-! ### Step 2a: the two cross-energy bounds

`crossPop`: population leading vs sample trailing, `∑_{i<d}∑_{j≥d}⟪u_i,v_j⟫²`,
bounded directly by `Acharyya2025.RankGap` (population structure on `T`).

`crossSamp`: sample leading vs population trailing, `∑_{i<d}∑_{j≥d}⟪v_i,u_j⟫²`,
bounded by `Acharyya2025.DavisKahan` with a manually supplied gap (`λ̂_i ≥ α/2`
for `i < d`, `λ_j = 0` for `j ≥ d`).  Both bounds are `4 n ε² / α²`. -/

/-- Internal helper (Davis–Kahan / rank-gap cross energy). `crossPop ≤ 4 n ε² / α²`:
total squared overlap of leading population eigenvectors against trailing sample
eigenvectors. This is the eigenvector-perturbation half of Theorem 2's argument.

Hypotheses:
* `hα_pos`, `hα` — eigenvalue floor `α > 0` on the leading block (Assumption 2 lower
  bound `λ_d` / `C1`).
* `htail` — all trailing population eigenvalues vanish (rank `= d`, encoding
  Assumption 1).
* `hε`, `hsmall : ε ≤ α/2` — operator-norm closeness and smallness side-condition. -/
private theorem crossPop_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) :
    -- Conclusion: the leading-population / trailing-sample cross energy is `≤ 4nε²/α²`.
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2
      ≤ 4 * (n : ℝ) * ε^2 / α^2 :=
  Acharyya2025.RankGap.sum_cross_inner_sq_le_of_rank_floor hT hS hn_eq d hα_pos hα htail hε hsmall

/-- Internal helper (Davis–Kahan cross energy, swapped roles). `crossSamp ≤ 4 n ε² / α²`:
total squared overlap of leading sample eigenvectors against trailing population
eigenvectors. The spectral gap is `α/2` because each leading sample eigenvalue
exceeds `α/2` (Weyl) while every trailing population eigenvalue is `0`. Same
hypothesis roles as `crossPop_le` (floor `α`, rank-`d` tail, closeness `ε`). -/
private theorem crossSamp_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) :
    -- Conclusion: the leading-sample / trailing-population cross energy is `≤ 4nε²/α²`.
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2
      ≤ 4 * (n : ℝ) * ε^2 / α^2 := by
  -- `‖(T − S) x‖ ≤ ε ‖x‖` for the Weyl step (symmetric direction).
  have hε' : ∀ x, ‖(T - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (T - S) x = -((S - T) x) := by rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  -- Gap: for `i < d`, `λ̂_i ≥ α/2`; for `j ≥ d`, `λ_j = 0`.
  have hgap : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      α / 2 ≤ |hS.eigenvalues hn_eq i - hT.eigenvalues hn_eq j| := by
    intro i j hi hj
    -- Weyl on index `i`: `λ̂_i ≥ λ_i − ε ≥ α − ε ≥ α/2`.
    have hweyl := Acharyya2025.Weyl.abs_eigenvalues_sub_le hT hS hn_eq hε' i
    rw [abs_le] at hweyl
    have hSi : α / 2 ≤ hS.eigenvalues hn_eq i := by
      have := hα i hi; linarith [hweyl.2]
    have hTj : hT.eigenvalues hn_eq j = 0 := htail j hj
    rw [hTj, sub_zero]
    calc α / 2 ≤ hS.eigenvalues hn_eq i := hSi
      _ ≤ |hS.eigenvalues hn_eq i| := le_abs_self _
  have hbound := Acharyya2025.DavisKahan.sum_cross_inner_sq_le hS hT hn_eq d
    (by positivity : (0 : ℝ) < α / 2) hgap hε'
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2
        ≤ (n : ℝ) * ε^2 / (α / 2)^2 := hbound
    _ = 4 * (n : ℝ) * ε^2 / α^2 := by field_simp; ring

/-- Internal helper / algebraic step. A single trailing-energy column of the
`(overlap hS hT)ᵀ * (overlap hS hT)` deviation is bounded by `crossSamp`:
`∑_{j≥d}⟪hT.basis j, hS.basis (castLE k)⟫² ≤ 4 n ε² / α²`. Same hypothesis roles
as `crossSamp_le`. -/
private theorem tailS_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) (k : Fin d) :
    -- Conclusion: the `k`-th trailing-energy column is `≤ 4nε²/α²`.
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2
      ≤ 4 * (n : ℝ) * ε^2 / α^2 := by
  classical
  -- Rewrite the column (with `u_j` first, `v_{castLE k}` second) into the
  -- `crossSamp` orientation (`v` leading, `u` trailing) via `real_inner_comm`.
  have hcomm : ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k), hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_comm]
  rw [hcomm]
  -- This column is the `i = castLE k` slice of `crossSamp`; bound by the whole sum.
  have hmem : (Fin.castLE hd k) ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩; simp [Fin.castLE]
  have hslice :
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k), hT.eigenvectorBasis hn_eq j⟫_ℝ)^2
        ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
              (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 :=
    Finset.single_le_sum
      (f := fun i : Fin n => ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) hmem
  exact le_trans hslice (crossSamp_le hT hS hα_pos hα htail hε hsmall)

/-! ### Step 2b: the near-isometry `M` and its Gram deviation

`M := toEuclideanLin Qᵀ`, where `Q := overlap hT hS`.  Then
`(M x)_l = ∑_k Q_{kl} x_k`, and the quadratic-form deviation is governed by the
deviation matrix `QQᵀ − I = (overlap hS hT)ᵀ * (overlap hS hT) − I`, each entry
of which is `≤ τ := 4 n ε² / α²`. -/

/-- The near-isometry `M := toEuclideanLin Qᵀ`, where `Q := overlap hT hS` is the
overlap (cosine) matrix between the population and sample leading eigenbases.
`M` is the linear map whose polar factor will furnish the alignment matrix `W`
(the paper's orthogonal `W*`). It is `≈` an isometry because `Q` is `≈`
orthogonal under the rank-`d` floor; a plain definition, not a claim. -/
noncomputable def nearIsometry (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanLin (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ

/-- Internal helper / algebraic step: coordinate formula for `M`,
`(M x)_l = ∑_k Q_{kl} x_k`. -/
private theorem nearIsometry_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (x : EuclideanSpace ℝ (Fin d)) (l : Fin d) :
    -- Conclusion: the `l`-th coordinate of `M x` is the `Q`-weighted combination of `x`.
    (nearIsometry hT hS hd x) l
      = ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l * x k := by
  show ((Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ.mulVec (WithLp.ofLp x)) l = _
  rw [Matrix.mulVec_eq_sum]
  simp [mul_comm]

/-- Internal helper / algebraic step: the deviation matrix `QQᵀ` equals
`(overlap hS hT)ᵀ * (overlap hS hT)` (rewrites the Gram deviation into the form the
`Overlap` toolkit bounds). -/
private theorem dev_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    -- Conclusion: the two ways of writing the overlap-Gram product agree.
    (Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
        (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
      = (Acharyya2025.Overlap.overlap hS hT hn_eq hd)ᵀ *
          (Acharyya2025.Overlap.overlap hS hT hn_eq hd) := by
  have h : Acharyya2025.Overlap.overlap hS hT hn_eq hd
      = (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ := by
    ext k l
    simp only [Acharyya2025.Overlap.overlap, Matrix.transpose_apply]
    rw [real_inner_comm]
  rw [h, Matrix.transpose_transpose]

/-- Internal helper / algebraic step (**entrywise Gram-deviation bound**). Each
entry of `QQᵀ − I` is at most `τ := 4 n ε² / α²` in absolute value. This
quantifies how close the overlap matrix `Q` is to orthogonal (a Davis–Kahan
consequence). Same hypothesis roles as `crossPop_le` (floor `α`, rank-`d` tail,
closeness `ε`). -/
private theorem abs_dev_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) (k m : Fin d) :
    -- Conclusion: each entry of the Gram deviation `QQᵀ − I` is `≤ 4nε²/α²`.
    |((Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
          (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
        - (1 : Matrix (Fin d) (Fin d) ℝ)) k m|
      ≤ 4 * (n : ℝ) * ε^2 / α^2 := by
  rw [dev_eq hT hS hd]
  -- Apply the Overlap deviation bound (swapped roles `hS hT`).
  have hbnd := Acharyya2025.Overlap.abs_overlapT_mul_overlap_sub_one_le hS hT hn_eq hd k m
  -- The two trailing-energy factors are each `≤ τ`, hence their product `≤ τ`.
  set τ : ℝ := 4 * (n : ℝ) * ε^2 / α^2 with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have htk := tailS_le hd hT hS hα_pos hα htail hε hsmall k
  have htm := tailS_le hd hT hS hα_pos hα htail hε hsmall m
  have hsk : Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2)
      ≤ Real.sqrt τ := Real.sqrt_le_sqrt htk
  have hsm : Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd m)⟫_ℝ)^2)
      ≤ Real.sqrt τ := Real.sqrt_le_sqrt htm
  calc |((Acharyya2025.Overlap.overlap hS hT hn_eq hd)ᵀ *
            (Acharyya2025.Overlap.overlap hS hT hn_eq hd)
          - (1 : Matrix (Fin d) (Fin d) ℝ)) k m|
      ≤ Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2)
          * Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd m)⟫_ℝ)^2) :=
        hbnd
    _ ≤ Real.sqrt τ * Real.sqrt τ :=
        mul_le_mul hsk hsm (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = τ := by rw [← Real.sqrt_mul hτ0, Real.sqrt_mul_self hτ0]

/-- Internal helper / algebraic step (**Gram-deviation identity**). The
quadratic-form deviation of `M` is the quadratic form of the deviation matrix
`D := QQᵀ − I`: `⟪M x, M x⟫ − ⟪x, x⟫ = ∑_k ∑_m D_{km} (x_k x_m)`. Pure algebra,
no hypotheses on the spectrum. -/
private theorem gram_dev_identity (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (x : EuclideanSpace ℝ (Fin d)) :
    -- Conclusion: the isometry defect of `M` at `x` is the `D`-quadratic form of `x`.
    ⟪nearIsometry hT hS hd x, nearIsometry hT hS hd x⟫_ℝ - ⟪x, x⟫_ℝ
      = ∑ k, ∑ m, ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
            (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
          - (1 : Matrix (Fin d) (Fin d) ℝ)) k m * (x k * x m) := by
  set Q := Acharyya2025.Overlap.overlap hT hS hn_eq hd with hQ
  have happly : ∀ l, (nearIsometry hT hS hd x) l = ∑ k, Q k l * x k :=
    fun l => nearIsometry_apply hT hS hd x l
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  -- `⟪Mx,Mx⟫ = ∑_k ∑_m (QQᵀ)_{km} (x_k x_m)`.
  have hMM : ∑ i, (nearIsometry hT hS hd x).ofLp i * (nearIsometry hT hS hd x).ofLp i
      = ∑ k, ∑ m, (Q * Qᵀ) k m * (x k * x m) := by
    calc ∑ i, (nearIsometry hT hS hd x).ofLp i * (nearIsometry hT hS hd x).ofLp i
        = ∑ l, (∑ k, Q k l * x k) * (∑ m, Q m l * x m) := by
          refine Finset.sum_congr rfl (fun l _ => by rw [happly])
      _ = ∑ l, ∑ k, ∑ m, (Q k l * x k) * (Q m l * x m) := by
          refine Finset.sum_congr rfl (fun l _ => by rw [Finset.sum_mul_sum])
      _ = ∑ k, ∑ m, ∑ l, (Q k l * x k) * (Q m l * x m) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => by rw [Finset.sum_comm])
      _ = ∑ k, ∑ m, (Q * Qᵀ) k m * (x k * x m) := by
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => ?_))
          rw [Matrix.mul_apply]
          simp only [Matrix.transpose_apply]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun l _ => by ring)
  -- `⟪x,x⟫ = ∑_k ∑_m I_{km} (x_k x_m)`.
  have hxx : ∑ i, x.ofLp i * x.ofLp i
      = ∑ k, ∑ m, (1 : Matrix (Fin d) (Fin d) ℝ) k m * (x k * x m) := by
    symm
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hmk; rw [Matrix.one_apply_ne (Ne.symm hmk), zero_mul]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hMM, hxx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Matrix.sub_apply]; ring

/-- Internal helper / algebraic step: `⟪x, x⟫` as the coordinate sum of squares
on `EuclideanSpace ℝ (Fin d)`. -/
private theorem inner_self_eq_sum (x : EuclideanSpace ℝ (Fin d)) :
    -- Conclusion: the self inner product equals the sum of squared coordinates.
    ⟪x, x⟫_ℝ = ∑ k, (x k)^2 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [pow_two]

/-- Internal helper / algebraic step (**Gram-deviation quadratic-form bound**).
`M` is a near-isometry: `|⟪M x, M x⟫ − ⟪x, x⟫| ≤ δ ⟪x, x⟫` with `δ := d · τ`,
`τ := 4 n ε² / α²`. This is the input to the polar-factor step that produces the
alignment `W`. Same hypothesis roles as `crossPop_le` (floor `α`, rank-`d` tail,
closeness `ε`, smallness `ε ≤ α/2`). -/
private theorem gram_dev_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    -- Conclusion: `M`'s isometry defect at `x` is `≤ δ ⟪x,x⟫` with `δ = d·4nε²/α²`.
    |⟪nearIsometry hT hS hd x, nearIsometry hT hS hd x⟫_ℝ - ⟪x, x⟫_ℝ|
      ≤ ((d : ℝ) * (4 * (n : ℝ) * ε^2 / α^2)) * ⟪x, x⟫_ℝ := by
  set τ : ℝ := 4 * (n : ℝ) * ε^2 / α^2 with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  set D := (Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
      (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
        - (1 : Matrix (Fin d) (Fin d) ℝ) with hD
  have hDbnd : ∀ k m : Fin d, |D k m| ≤ τ :=
    fun k m => abs_dev_le hd hT hS hα_pos hα htail hε hsmall k m
  rw [gram_dev_identity hT hS hd x]
  -- `|∑∑ D x x| ≤ ∑∑ τ |x_k| |x_m| = τ (∑|x_k|)² ≤ τ d ∑ x_k² = τ d ⟪x,x⟫`.
  have step1 : |∑ k, ∑ m, D k m * (x k * x m)| ≤ ∑ k, ∑ m, τ * (|x k| * |x m|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hDbnd k m) (by positivity)
  have hsumsum : ∑ k, ∑ m, τ * (|x k| * |x m|) = τ * (∑ k, |x k|)^2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
  have hcard : (∑ k, |x k|)^2 ≤ (d : ℝ) * ∑ k, (x k)^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun k => |x k|)
    simpa only [Finset.card_univ, Fintype.card_fin, sq_abs] using h
  rw [inner_self_eq_sum x]
  calc |∑ k, ∑ m, D k m * (x k * x m)|
      ≤ ∑ k, ∑ m, τ * (|x k| * |x m|) := step1
    _ = τ * (∑ k, |x k|)^2 := hsumsum
    _ ≤ τ * ((d : ℝ) * ∑ k, (x k)^2) := mul_le_mul_of_nonneg_left hcard hτ0
    _ = (d : ℝ) * τ * ∑ k, (x k)^2 := by ring

/-! ### Coordinate / Parseval utilities -/

/-- Internal helper / algebraic step: the `i`-th coordinate of a finite
`smul`-combination in `EuclideanSpace`. -/
private theorem smul_sum_apply {m p : ℕ} (c : Fin p → ℝ)
    (v : Fin p → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    -- Conclusion: coordinate of a linear combination is the combination of coordinates.
    (∑ k, c k • v k) i = ∑ k, c k * (v k) i := by
  show (∑ k, c k • v k).ofLp i = ∑ k, c k * (v k).ofLp i
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [WithLp.ofLp_smul]; rfl

/-- Internal helper / algebraic step (**Parseval for an orthonormal family**):
`‖∑ k, c k • v k‖² = ∑ k, (c k)²`. -/
private theorem norm_sq_smul_sum_orthonormal {m p : ℕ}
    {v : Fin p → EuclideanSpace ℝ (Fin m)} (hv : Orthonormal ℝ v) (c : Fin p → ℝ) :
    -- Conclusion: the squared norm of an orthonormal combination is the coefficient energy.
    ‖∑ k, c k • v k‖^2 = ∑ k, (c k)^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  have key := hv.inner_left_right_finset (s := (Finset.univ : Finset (Fin p)))
    (a := fun i j => c i * c j)
  calc ∑ i, ⟪c i • v i, ∑ j, c j • v j⟫_ℝ
      = ∑ i, ∑ j, (c i * c j) * ⟪v j, v i⟫_ℝ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inner_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (v i) (v j)]; ring
    _ = ∑ k, c k * c k := by simp_rw [smul_eq_mul] at key; exact key
    _ = ∑ k, (c k)^2 := by refine Finset.sum_congr rfl (fun k _ => by ring)

/-! ### Step 3 helper: the Term-3 reconstruction defect

For the canonical population vector `u_l := hT.eigenvectorBasis (castLE l)` and
the partial reconstruction `∑_k Q_{kl} v_k` (over the top-`d` sample eigenbasis),
the defect vector `w_l := (∑_k Q_{kl} • v_k) − u_l` has squared norm equal to the
trailing cross-energy `∑_{j ≥ d} ⟪v_j, u_l⟫²`. -/

/-- Internal helper / algebraic step. The `v`-coordinate of the Term-3
reconstruction defect vanishes in the leading block and equals `−⟪v_j, u_l⟫` in
the trailing block. (Term 3 is the Davis–Kahan reconstruction-defect term.) -/
private theorem defect_repr (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (l : Fin d) (j : Fin n) :
    -- Conclusion: the defect's `j`-th sample coordinate is `−⟪v_j,u_l⟫` (trailing) or `0` (leading).
    (hS.eigenvectorBasis hn_eq).repr
        ((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
          - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) j
      = if d ≤ (j : ℕ)
          then - ⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq (Fin.castLE hd l)⟫_ℝ
          else 0 := by
  classical
  set v := hS.eigenvectorBasis hn_eq with hv
  set u := hT.eigenvectorBasis hn_eq with hu
  set Q := Acharyya2025.Overlap.overlap hT hS hn_eq hd with hQ
  -- `repr (·) j = ⟪v_j, ·⟫`, split the subtraction.
  rw [(v).repr_apply_apply, inner_sub_right, inner_sum]
  -- `⟪v_j, Σ_k Q_kl v_k⟫ = Σ_k Q_kl ⟪v_j, v_{castLE k}⟫ = Σ_k Q_kl (if j = castLE k then 1 else 0)`.
  have hortho : ∀ k : Fin d, ⟪v j, v (Fin.castLE hd k)⟫_ℝ = if j = Fin.castLE hd k then (1:ℝ) else 0 := by
    intro k
    rw [hv]
    exact orthonormal_iff_ite.mp (hS.eigenvectorBasis hn_eq).orthonormal j (Fin.castLE hd k)
  have hsum1 : ∑ k, ⟪v j, Q k l • v (Fin.castLE hd k)⟫_ℝ
      = ∑ k, Q k l * (if j = Fin.castLE hd k then (1:ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_smul_right, hortho k]
  rw [hsum1]
  by_cases hj : d ≤ (j : ℕ)
  · -- trailing block: the leading sum vanishes
    rw [if_pos hj]
    have hzero : ∑ k, Q k l * (if j = Fin.castLE hd k then (1:ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have hne : j ≠ Fin.castLE hd k := by
        intro h; rw [h] at hj; simp only [Fin.val_castLE] at hj; omega
      rw [if_neg hne, mul_zero]
    rw [hzero, zero_sub]
  · -- leading block: cancellation `Q_{⟨j⟩,l} = ⟪v_j, u_l⟫`
    rw [if_neg hj]
    push Not at hj
    have hcollapse : ∑ k, Q k l * (if j = Fin.castLE hd k then (1:ℝ) else 0) = Q ⟨(j:ℕ), hj⟩ l := by
      rw [Finset.sum_eq_single ⟨(j:ℕ), hj⟩]
      · have hje : j = Fin.castLE hd ⟨(j:ℕ), hj⟩ := by apply Fin.ext; simp [Fin.castLE]
        rw [if_pos hje, mul_one]
      · intro k _ hk
        have hne : j ≠ Fin.castLE hd k := by
          intro h; apply hk; apply Fin.ext
          have heq : (j : ℕ) = ((Fin.castLE hd k : Fin n) : ℕ) := by rw [h]
          simp only [Fin.val_castLE] at heq; exact heq.symm
        rw [if_neg hne, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    rw [hcollapse]
    -- `Q_{⟨j⟩,l} = ⟪v_{castLE ⟨j⟩}, u_l⟫ = ⟪v_j, u_l⟫`, so the difference is 0
    have hjcast : Fin.castLE hd ⟨(j:ℕ), hj⟩ = j := by apply Fin.ext; simp [Fin.castLE]
    have : Q ⟨(j:ℕ), hj⟩ l = ⟪v j, u (Fin.castLE hd l)⟫_ℝ := by
      rw [hQ, Acharyya2025.Overlap.overlap, hjcast]
    rw [this, sub_self]

/-- Internal helper / algebraic step (**Term-3 defect squared norm**):
`‖w_l‖² = ∑_{j ≥ d} ⟪v_j, u_l⟫²` — the defect's energy equals the trailing
cross-energy (which `crossPop_le` bounds). -/
private theorem defect_norm_sq (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (l : Fin d) :
    -- Conclusion: the `l`-th defect's squared norm equals its trailing cross energy.
    ‖(∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
        - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)‖^2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq (Fin.castLE hd l)⟫_ℝ)^2 := by
  classical
  set w := (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
        - hT.eigenvectorBasis hn_eq (Fin.castLE hd l) with hw
  rw [← Acharyya2025.Weyl.sum_repr_sq_eq_norm_sq (hS.eigenvectorBasis hn_eq) w]
  -- Split the full sum into leading (`0`) and trailing (`⟪v_j,u_l⟫²`) blocks.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => d ≤ (j : ℕ))]
  have hlead : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (d ≤ (j : ℕ))),
      ((hS.eigenvectorBasis hn_eq).repr w j)^2 = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hjlt : ¬ (d ≤ (j : ℕ)) := (Finset.mem_filter.mp hj).2
    rw [hw, defect_repr hT hS hd l j, if_neg hjlt]; ring
  rw [hlead, add_zero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjge : d ≤ (j : ℕ) := (Finset.mem_filter.mp hj).2
  rw [hw, defect_repr hT hS hd l j, if_pos hjge]
  ring

/-! ### Frobenius packaging

The total error and the three terms are packaged as elements of
`EuclideanSpace ℝ (Fin n × Fin d)`, so the Minkowski (triangle) inequality is
just `norm_add_le`. -/

/-- Internal helper / algebraic step: the squared Frobenius norm of a
product-space vector as an iterated (rows × columns) sum. -/
private theorem frob_sq (t : EuclideanSpace ℝ (Fin n × Fin d)) :
    -- Conclusion: the squared norm equals the double sum of squared entries.
    ‖t‖^2 = ∑ i : Fin n, ∑ l : Fin d, (t (i, l))^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp [Real.norm_eq_abs, sq_abs]

/-- Notation abbreviation: the `k`-th sample top-block eigenvalue `λ̂_k`. -/
private noncomputable abbrev lamHat (hS : S.IsSymmetric) (hd : d ≤ n) (k : Fin d) : ℝ :=
  hS.eigenvalues hn_eq (Fin.castLE hd k)

/-- Notation abbreviation: the `l`-th population top-block eigenvalue `λ_l`. -/
private noncomputable abbrev lamPop (hT : T.IsSymmetric) (hd : d ≤ n) (l : Fin d) : ℝ :=
  hT.eigenvalues hn_eq (Fin.castLE hd l)

/-- The **Term-2 (commutator) vector**, packaged as a Frobenius vector:
`(i,l) ↦ ∑_k Q_{kl}(√λ̂_k − √λ_l) v_k(i)`. This is the second of the three terms
in the decomposition `ψ̂W − ψ = Term1 + Term2 + Term3`; a plain definition. -/
private noncomputable def term2vec (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 (fun p : Fin n × Fin d =>
    ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k p.2
        * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd p.2))
        * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) p.1)

/-- The **Term-3 (Davis–Kahan reconstruction-defect) vector**, packaged as a
Frobenius vector: `(i,l) ↦ √λ_l (∑_k Q_{kl} v_k(i) − u_l(i))`. Third of the three
decomposition terms; a plain definition. -/
private noncomputable def term3vec (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 (fun p : Fin n × Fin d =>
    Real.sqrt (lamPop hT hd p.2)
      * (((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k p.2
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
          - hT.eigenvectorBasis hn_eq (Fin.castLE hd p.2)) p.1))

/-- Internal helper / algebraic step: coordinate formula for `term3vec`. -/
private theorem term3vec_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (i : Fin n) (l : Fin d) :
    -- Conclusion: the `(i,l)` entry of the Term-3 vector unfolds to its defining expression.
    (term3vec hT hS hd) (i, l)
      = Real.sqrt (lamPop hT hd l)
        * (((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
            - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) i) := rfl

/-- Internal helper / algebraic step (**Term-3 squared Frobenius bound**):
`‖term3vec‖² ≤ Λ · (4 n ε² / α²)`. Bounds the Davis–Kahan reconstruction-defect
term using the eigenvalue cap `Λ` and the cross energy.

Hypotheses combine the eigenvalue floor `α` (`hα_pos`, `hα`), the rank-`d` tail
(`htail`, Assumption 1), the cap `Λ` (`hΛ`, Assumption 2 upper bound), and
operator-norm closeness `ε` with smallness `ε ≤ α/2`. -/
private theorem term3_norm_sq_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α Λ ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hΛ : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) :
    -- Conclusion: the Term-3 Frobenius energy is `≤ Λ · 4nε²/α²`.
    ‖term3vec hT hS hd‖^2 ≤ Λ * (4 * (n : ℝ) * ε^2 / α^2) := by
  classical
  -- `0 ≤ Λ`: when `n = 0` both sides vanish; otherwise eigenvalue `0` witnesses it.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have : term3vec hT hS hd = 0 := by
      ext p; exact (Fin.elim0 p.1)
    rw [this]; simp
  have hΛ0 : 0 ≤ Λ := by
    set z : Fin n := ⟨0, hnpos⟩ with hz
    by_cases hd0 : 0 < d
    · have hlt : (z : ℕ) < d := by rw [hz]; simpa using hd0
      exact le_trans (le_of_lt hα_pos) (le_trans (hα z hlt) (hΛ z))
    · push Not at hd0
      have hdz : d = 0 := Nat.le_zero.mp hd0
      have hge : d ≤ (z : ℕ) := by omega
      have hez := htail z hge
      linarith [hΛ z, hez]
  -- `‖t3‖² = ∑_l λ_l ‖w_l‖²`.
  set w := fun l : Fin d => (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
        - hT.eigenvectorBasis hn_eq (Fin.castLE hd l) with hw
  have hpop_nonneg : ∀ l : Fin d, 0 ≤ lamPop hT hd l := by
    intro l
    have hlt : ((Fin.castLE hd l : Fin n) : ℕ) < d := by simp [Fin.castLE]
    exact le_trans (le_of_lt hα_pos) (hα (Fin.castLE hd l) hlt)
  have hstep : ‖term3vec hT hS hd‖^2 = ∑ l : Fin d, (lamPop hT hd l) * ‖w l‖^2 := by
    rw [frob_sq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    -- ∑_i (√λ_l · (w l) i)² = λ_l · ∑_i ((w l) i)² = λ_l ‖w l‖²
    have hsqrt : (Real.sqrt (lamPop hT hd l))^2 = lamPop hT hd l :=
      Real.sq_sqrt (hpop_nonneg l)
    have hnormw : ∑ i : Fin n, ((w l) i)^2 = ‖w l‖^2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
    calc ∑ i : Fin n, ((term3vec hT hS hd) (i, l))^2
        = ∑ i : Fin n, (lamPop hT hd l) * ((w l) i)^2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [term3vec_apply, mul_pow, hsqrt]
      _ = (lamPop hT hd l) * ∑ i : Fin n, ((w l) i)^2 := by rw [Finset.mul_sum]
      _ = (lamPop hT hd l) * ‖w l‖^2 := by rw [hnormw]
  rw [hstep]
  -- Each `‖w l‖² = ∑_{j≥d}⟪v_j,u_l⟫²`; `λ_l ≤ Λ`.
  have hnormwl : ∀ l : Fin d, ‖w l‖^2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq (Fin.castLE hd l)⟫_ℝ)^2 :=
    fun l => defect_norm_sq hT hS hd l
  -- `∑_l λ_l ‖w_l‖² ≤ Λ ∑_l ‖w_l‖²` and `∑_l ‖w_l‖² = crossPop' ≤ 4nε²/α²`.
  have hbound1 : ∑ l : Fin d, (lamPop hT hd l) * ‖w l‖^2
      ≤ ∑ l : Fin d, Λ * ‖w l‖^2 := by
    refine Finset.sum_le_sum (fun l _ => ?_)
    exact mul_le_mul_of_nonneg_right (hΛ (Fin.castLE hd l)) (sq_nonneg _)
  -- `∑_l ‖w_l‖² = ∑_{l<d (castLE)}∑_{j≥d}⟪v_j,u_l⟫² ≤ crossPop`.
  have hcrossPop := crossPop_le hT hS hα_pos hα htail hε hsmall
  -- Bridge: ∑_{l:Fin d} (column at castLE l) = ∑_{i ∈ filter <d} (column at i).
  have hbridge : ∑ l : Fin d, ‖w l‖^2
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
    -- rewrite each ‖w_l‖² and reindex castLE → filter
    have hrw : ∑ l : Fin d, ‖w l‖^2
        = ∑ l : Fin d, ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq (Fin.castLE hd l), hS.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hnormwl l]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_comm]
    rw [hrw]
    -- reindex castLE ↦ filter (<d)
    rw [sum_castLE_eq_filter hd
        (fun i : Fin n => ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2)]
  calc ∑ l : Fin d, (lamPop hT hd l) * ‖w l‖^2
      ≤ ∑ l : Fin d, Λ * ‖w l‖^2 := hbound1
    _ = Λ * ∑ l : Fin d, ‖w l‖^2 := by rw [Finset.mul_sum]
    _ ≤ Λ * (4 * (n : ℝ) * ε^2 / α^2) :=
        mul_le_mul_of_nonneg_left (le_trans hbridge hcrossPop) hΛ0

/-- Internal helper / algebraic step: coordinate formula for `term2vec`. -/
private theorem term2vec_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (i : Fin n) (l : Fin d) :
    -- Conclusion: the `(i,l)` entry of the Term-2 vector unfolds to its defining expression.
    (term2vec hT hS hd) (i, l)
      = ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))
          * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i := rfl

/-- Internal helper / algebraic step. The Term-2 coefficient
`c_{kl} = Q_{kl}(√λ̂_k − √λ_l)` is bounded by `ε / √(α/2)` in absolute value
(Sylvester/commutator identity + the `√a − √b = (a−b)/(√a+√b)` quotient, with the
denominator bounded below using the floor `α`). -/
private theorem abs_term2_coeff_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α) (hε_nonneg : 0 ≤ ε)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) (k l : Fin d) :
    -- Conclusion: each Term-2 coefficient is `≤ ε / √(α/2)` in absolute value.
    |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
        * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))|
      ≤ ε / Real.sqrt (α / 2) := by
  set a := lamHat hS hd k with ha
  set b := lamPop hT hd l with hb
  -- positivity facts: `a ≥ α/2 > 0`, `b ≥ α > 0`.
  have hapos : α / 2 ≤ a := sample_eig_lb hd hT hS hα hε hsmall k
  have hbpos : α ≤ b := by
    have hlt : ((Fin.castLE hd l : Fin n) : ℕ) < d := by simp [Fin.castLE]
    exact hα (Fin.castLE hd l) hlt
  have ha0 : 0 ≤ a := le_trans (by positivity) hapos
  have hb0 : 0 ≤ b := le_trans (le_of_lt hα_pos) hbpos
  have hsa : Real.sqrt (α / 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt hapos
  have hsa_pos : 0 < Real.sqrt (α / 2) := Real.sqrt_pos.mpr (by positivity)
  have hden_pos : 0 < Real.sqrt a + Real.sqrt b := by
    have : 0 < Real.sqrt a := lt_of_lt_of_le hsa_pos hsa
    positivity
  -- `√a − √b = (a − b)/(√a + √b)`.
  have hsqrt : Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
    rw [eq_div_iff (ne_of_gt hden_pos)]
    have h1 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
    have h2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0
    nlinarith [h1, h2]
  -- `|(a − b)·Q| ≤ ε` (Sylvester identity).
  have hcomm : |(a - b) * (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l| ≤ ε :=
    Acharyya2025.Overlap.abs_eigenvalue_diff_mul_overlap_le hT hS hn_eq hd hε k l
  -- `√(α/2) ≤ √a + √b`.
  have hdenlb : Real.sqrt (α / 2) ≤ Real.sqrt a + Real.sqrt b := by
    have : Real.sqrt (α / 2) ≤ Real.sqrt a := hsa
    have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
    linarith
  -- Assemble via the `√`-quotient inequality.
  rw [hsqrt, show (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
        * ((a - b) / (Real.sqrt a + Real.sqrt b))
      = ((a - b) * (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l)
          / (Real.sqrt a + Real.sqrt b) by ring,
    abs_div, abs_of_pos hden_pos, div_le_div_iff₀ hden_pos hsa_pos]
  calc |(a - b) * (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l| * Real.sqrt (α / 2)
      ≤ ε * Real.sqrt (α / 2) := mul_le_mul_of_nonneg_right hcomm (le_of_lt hsa_pos)
    _ ≤ ε * (Real.sqrt a + Real.sqrt b) := mul_le_mul_of_nonneg_left hdenlb hε_nonneg

/-- Internal helper / algebraic step (**Term-2 squared Frobenius bound**):
`‖term2vec‖² ≤ d² · (ε / √(α/2))²`. Bounds the commutator term by Parseval
(orthonormal sample eigenbasis) plus the per-coefficient bound `abs_term2_coeff_le`,
with `d²` summands. Same hypothesis roles (floor `α`, closeness `ε`, smallness). -/
private theorem term2_norm_sq_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α) (hε_nonneg : 0 ≤ ε)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) :
    -- Conclusion: the Term-2 Frobenius energy is `≤ d²·(ε/√(α/2))²`.
    ‖term2vec hT hS hd‖^2 ≤ (d : ℝ)^2 * (ε / Real.sqrt (α / 2))^2 := by
  classical
  set c := fun (k l : Fin d) => (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
      * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l)) with hc
  -- `‖t2‖² = ∑_l ∑_k c_{kl}²` via Parseval per `l`.
  have hstep : ‖term2vec hT hS hd‖^2 = ∑ l : Fin d, ∑ k : Fin d, (c k l)^2 := by
    rw [frob_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    -- ∑_i (∑_k c_{kl} v_k(i))² = ‖∑_k c_{kl} • v_k‖² = ∑_k c_{kl}²
    have hcoord : ∀ i : Fin n, (term2vec hT hS hd) (i, l)
        = (∑ k, (c k l) • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) i := by
      intro i
      rw [smul_sum_apply, term2vec_apply]
    calc ∑ i : Fin n, ((term2vec hT hS hd) (i, l))^2
        = ∑ i : Fin n, ((∑ k, (c k l) • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) i)^2 := by
          refine Finset.sum_congr rfl (fun i _ => by rw [hcoord i])
      _ = ‖∑ k, (c k l) • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)‖^2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
          refine Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
      _ = ∑ k : Fin d, (c k l)^2 := by
          have hortho : Orthonormal ℝ (fun k : Fin d =>
              hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) :=
            (hS.eigenvectorBasis hn_eq).orthonormal.comp _ (Fin.castLE_injective hd)
          exact norm_sq_smul_sum_orthonormal hortho (fun k => c k l)
  rw [hstep]
  -- Each `c_{kl}² ≤ (ε/√(α/2))²`; double sum has `d²` terms.
  have hcoeff : ∀ k l : Fin d, (c k l)^2 ≤ (ε / Real.sqrt (α / 2))^2 := by
    intro k l
    have habs := abs_term2_coeff_le hd hT hS hα_pos hε_nonneg hα hε hsmall k l
    have h0 : 0 ≤ ε / Real.sqrt (α / 2) := by positivity
    rw [hc]
    calc ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l)))^2
        = |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))|^2 := by rw [sq_abs]
      _ ≤ (ε / Real.sqrt (α / 2))^2 := by
          apply sq_le_sq'
          · linarith [abs_nonneg ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))), habs, h0]
          · exact habs
  calc ∑ l : Fin d, ∑ k : Fin d, (c k l)^2
      ≤ ∑ _l : Fin d, ∑ _k : Fin d, (ε / Real.sqrt (α / 2))^2 := by
        refine Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => hcoeff k l))
    _ = (d : ℝ)^2 * (ε / Real.sqrt (α / 2))^2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Step 4 (Term 1): total energy of the spectral embedding `ψ̂`

`∑_i ‖ψ̂ i‖² = ∑_k λ̂_k ≤ d (Λ + ε)`, where the orthonormality of the sample
eigenbasis collapses the `i`-sum and Weyl bounds each `λ̂_k`. -/

/-- Internal helper / algebraic step: coordinate of the spectral embedding,
`ψ̂ i k = √λ̂_k · v_k(i)`. -/
private theorem spectralConfig_apply (hS : S.IsSymmetric) (hd : d ≤ n) (i : Fin n) (k : Fin d) :
    -- Conclusion: the `(i,k)` coordinate of the embedding unfolds to `√λ̂_k · v_k(i)`.
    spectralConfig S hS hd i k
      = Real.sqrt (lamHat hS hd k) * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i := rfl

/-- Internal helper / algebraic step (**total spectral energy bound**):
`∑_i ‖ψ̂ i‖² ≤ d (Λ + ε)`. The sample embedding has bounded total energy (its
columns are the orthonormal eigenvectors scaled by `√λ̂_k`, each `λ̂_k ≤ Λ + ε`
by Weyl). Feeds the Term-1 bound. Uses the cap `Λ` (Assumption 2 upper bound) and
operator-norm closeness `ε`. -/
private theorem sum_norm_sq_spectralConfig_le (hd : d ≤ n) (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) {α Λ ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (hΛ : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (hsmall : ε ≤ α / 2) :
    -- Conclusion: the sample embedding's total energy is `≤ d(Λ+ε)`.
    ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2 ≤ (d : ℝ) * (Λ + ε) := by
  classical
  -- each top-block sample eigenvalue is `≥ α/2 ≥ 0`, so `(√λ̂_k)² = λ̂_k`.
  have hsqrtsq : ∀ k : Fin d, (Real.sqrt (lamHat hS hd k))^2 = lamHat hS hd k :=
    fun k => Real.sq_sqrt (le_trans (by positivity) (sample_eig_lb hd hT hS hα hε hsmall k))
  -- `‖ψ̂ i‖² = ∑_k λ̂_k v_k(i)²`; swap sums; collapse the `i`-sum by orthonormality.
  have hnormi : ∀ i : Fin n, ‖spectralConfig S hS hd i‖^2
      = ∑ k : Fin d, (lamHat hS hd k) * (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2 := by
    intro i
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (spectralConfig S hS hd i).ofLp k = spectralConfig S hS hd i k from rfl,
      spectralConfig_apply, Real.norm_eq_abs, sq_abs, mul_pow, hsqrtsq k]
  have hstep : ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2
      = ∑ k : Fin d, (lamHat hS hd k)
          * ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2 := by
    rw [Finset.sum_congr rfl (fun i _ => hnormi i), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
  -- `∑_i v_k(i)² = ‖v_k‖² = 1`.
  have hunit : ∀ k : Fin d, ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2 = 1 := by
    intro k
    have h1 : ‖hS.eigenvectorBasis hn_eq (Fin.castLE hd k)‖ = 1 :=
      (hS.eigenvectorBasis hn_eq).orthonormal.1 (Fin.castLE hd k)
    have heq : ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2
        = ‖hS.eigenvectorBasis hn_eq (Fin.castLE hd k)‖^2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
    rw [heq, h1]; norm_num
  rw [hstep]
  -- `∑_k λ̂_k · 1 = ∑_k λ̂_k ≤ ∑_k (Λ + ε) = d(Λ+ε)`.
  calc ∑ k : Fin d, (lamHat hS hd k)
          * ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2
      = ∑ k : Fin d, (lamHat hS hd k) := by
        refine Finset.sum_congr rfl (fun k _ => by rw [hunit k, mul_one])
    _ ≤ ∑ _k : Fin d, (Λ + ε) := by
        refine Finset.sum_le_sum (fun k _ => sample_eig_ub hd hT hS hΛ hε k)
    _ = (d : ℝ) * (Λ + ε) := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The configuration-perturbation theorem (WP7(c4)) -/

/-- The explicit closed-form configuration-error bound `CBOUND` produced by the
three-term decomposition, as a function of the sample size `n`, embedding
dimension `d`, eigenvalue floor `α` (paper's `λ_d`/`C1`), eigenvalue cap `Λ`
(paper's `λ_1`/`C2`), and operator-norm perturbation `ε`.

The three `Real.sqrt` summands are the Frobenius bounds of Term 1 (polar factor),
Term 2 (commutator), and Term 3 (Davis–Kahan defect) respectively; the leading
`√n` converts the Frobenius norm to the per-point `ConfigError`. Here
`δ := d · (4 n ε² / α²)` is the polar-factor parameter. This is the explicit
`κ`-style bound on `‖ψ̂W* − ψ‖` in the deterministic core of Theorem 2; a plain
definition (the bound is asserted in the theorem below). -/
noncomputable def configBound (n d : ℕ) (α Λ ε : ℝ) : ℝ :=
  Real.sqrt n *
    ( Real.sqrt ((2 * ((d : ℝ) * (4 * (n : ℝ) * ε^2 / α^2)))^2 * ((d : ℝ) * (Λ + ε)))
    + Real.sqrt ((d : ℝ)^2 * (ε / Real.sqrt (α / 2))^2)
    + Real.sqrt (Λ * (4 * (n : ℝ) * ε^2 / α^2)) )

/--
**Configuration perturbation for the classical-MDS spectral embedding.**

Let `T` (population) be a symmetric operator on `EuclideanSpace ℝ (Fin n)` whose
leading `d` sorted eigenvalues are `≥ α > 0`, with all trailing eigenvalues `0`
(rank `d`, spectral floor `α`) and top eigenvalue `≤ Λ`; let `S` (sample) be
symmetric and `ε`-close in operator norm (`ε ≤ α/2`).  Then the spectral
embeddings `spectralConfig S` and `spectralConfig T` agree up to a linear isometry
`W` of `EuclideanSpace ℝ (Fin d)`, with
`ConfigError (W ∘ spectralConfig S) (spectralConfig T) ≤ configBound n d α Λ ε`.

The constant is the explicit (loose) `configBound`; the alignment `W` is the
polar factor of the eigenvector overlap matrix.  The proof is the elementary
three-term decomposition `ψ̂W − ψ = Term1 + Term2 + Term3` (polar / commutator /
Davis–Kahan), combined by the Minkowski inequality on
`EuclideanSpace ℝ (Fin n × Fin d)` and `ConfigError ≤ √n · ‖·‖_F`.

PAPER CORRESPONDENCE: this is the **deterministic core of Theorem 2** (the
Weyl + Davis–Kahan part). The existential `W` is the paper's orthogonal matrix
`W* ∈ O(d)`; the conclusion is the deterministic version of `‖ψ̂W* − ψ‖ ≤ κ`,
here with the explicit `κ = configBound n d α Λ ε`. The probabilistic
"with high probability" content of Theorem 2 (turning `ε` and the asymptotic
regime `r = ω(n³)` into a tail bound) lives elsewhere; this theorem supplies the
deterministic bound that holds once `S` is `ε`-close to `T`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem exists_isometry_configError_spectralConfig_le
    {n d : ℕ} (hd : d ≤ n)               -- embedding dimension/rank `d ≤ n` (Assumption 1: rank = d)
    (T S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))  -- `T` population, `S` sample Gram operators
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)  -- extra (encoding) assumption: operators are symmetric/self-adjoint
    {α Λ ε : ℝ} (hα_pos : 0 < α) (hε_nonneg : 0 ≤ ε)  -- floor `α > 0`, perturbation `ε ≥ 0`
    -- Assumption 2 (lower): leading `d` population eigenvalues `≥ α` (paper's `λ_d`/`C1`):
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues finrank_euclideanSpace_fin i)
    -- Assumption 1 (rank = d, encoded): all trailing population eigenvalues vanish:
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues finrank_euclideanSpace_fin j = 0)
    -- Assumption 2 (upper): all population eigenvalues `≤ Λ` (paper's `λ_1`/`C2`):
    (hΛ : ∀ l : Fin n, hT.eigenvalues finrank_euclideanSpace_fin l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖)   -- sample/population operator-norm closeness `‖S − T‖ ≤ ε`
    (hsmall : ε ≤ α / 2)                 -- smallness side-condition (extra explicit numeric condition)
    -- polar-factor applicability: `δ = d·4nε²/α² ≤ 1/2` (extra explicit smallness condition):
    (hpolar : (d : ℝ) * (4 * (n : ℝ) * ε^2 / α^2) ≤ 1/2) :
    -- Conclusion: there is an isometry `W` of `ℝ^d` aligning the sample embedding to the
    -- population embedding with configuration error `≤ configBound n d α Λ ε`.
    ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      Acharyya2024.ConfigError (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd)
        ≤ configBound n d α Λ ε := by
  classical
  set δ : ℝ := (d : ℝ) * (4 * (n : ℝ) * ε^2 / α^2) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- The near-isometry `M` and its Gram-deviation bound feed the polar factor.
  set M := nearIsometry hT hS hd with hM
  have hclose : ∀ x : EuclideanSpace ℝ (Fin d),
      |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ := by
    intro x
    rw [hM, hδ]
    exact gram_dev_le hd hT hS hα_pos hα htail hε hsmall x
  obtain ⟨W, hWiso, hWclose⟩ :=
    Acharyya2025.PolarFactor.exists_isometry_close_of_self_adjoint_comp_close
      (finrank_euclideanSpace_fin (n := d)) M hpolar hclose
  refine ⟨W, hWiso, ?_⟩
  -- The total error and the three terms as product-space vectors.
  set etot : EuclideanSpace ℝ (Fin n × Fin d) :=
    WithLp.toLp 2 (fun p : Fin n × Fin d =>
      (W (spectralConfig S hS hd p.1)) p.2 - (spectralConfig T hT hd p.1) p.2) with hetot
  set t1 : EuclideanSpace ℝ (Fin n × Fin d) :=
    WithLp.toLp 2 (fun p : Fin n × Fin d =>
      ((W - M) (spectralConfig S hS hd p.1)) p.2) with ht1
  have hsplit : etot = t1 + term2vec hT hS hd + term3vec hT hS hd := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    ext p
    obtain ⟨i, l⟩ := p
    -- expand each coordinate
    show (W (spectralConfig S hS hd i)) l - (spectralConfig T hT hd i) l
      = _
    -- LHS pieces; RHS pieces via term apply lemmas
    have hMpsi : (M (spectralConfig S hS hd i)) l
        = ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k)
                * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i) := by
      rw [hM, nearIsometry_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show (spectralConfig S hS hd i) k = spectralConfig S hS hd i k from rfl,
        spectralConfig_apply]
    have ht1coord : t1 (i, l) = (W (spectralConfig S hS hd i)) l - (M (spectralConfig S hS hd i)) l := by
      show ((W - M) (spectralConfig S hS hd i)) l = _
      rw [LinearMap.sub_apply]; rfl
    have ht3coord : (term3vec hT hS hd) (i, l)
        = Real.sqrt (lamPop hT hd l)
          * ((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
                * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)
              - hT.eigenvectorBasis hn_eq (Fin.castLE hd l) i) := by
      rw [term3vec_apply]
      congr 1
      rw [show (((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
          - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) i)
          = ((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) i)
            - (hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) i from rfl]
      rw [smul_sum_apply]
    have hψcoord : (spectralConfig T hT hd i) l
        = Real.sqrt (lamPop hT hd l) * hT.eigenvectorBasis hn_eq (Fin.castLE hd l) i := by
      rw [show (spectralConfig T hT hd i) l = spectralConfig T hT hd i l from rfl]
      rfl
    show (W (spectralConfig S hS hd i)) l - (spectralConfig T hT hd i) l
      = t1 (i, l) + (term2vec hT hS hd) (i, l) + (term3vec hT hS hd) (i, l)
    rw [ht1coord, hMpsi, term2vec_apply, ht3coord, hψcoord]
    -- telescoping
    have h1 : (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))
            * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)
        = (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k)
              * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i))
          - (∑ k, Real.sqrt (lamPop hT hd l)
              * ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
                * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    have h2 : Real.sqrt (lamPop hT hd l)
          * (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)
        = ∑ k, Real.sqrt (lamPop hT hd l)
            * ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i) := by
      rw [Finset.mul_sum]
    rw [h1, mul_sub, h2]
    ring
  -- Minkowski: `‖etot‖ ≤ ‖t1‖ + ‖t2‖ + ‖t3‖`.
  have hmink : ‖etot‖ ≤ ‖t1‖ + ‖term2vec hT hS hd‖ + ‖term3vec hT hS hd‖ := by
    rw [hsplit]
    refine le_trans (norm_add_le (t1 + term2vec hT hS hd) (term3vec hT hS hd)) ?_
    gcongr
    exact norm_add_le t1 (term2vec hT hS hd)
  -- Term-1 norm bound.
  have ht1bound : ‖t1‖ ≤
      Real.sqrt ((2 * δ)^2 * ((d : ℝ) * (Λ + ε))) := by
    have ht1sq : ‖t1‖^2 ≤ (2 * δ)^2 * ((d : ℝ) * (Λ + ε)) := by
      rw [frob_sq]
      have hperi : ∀ i : Fin n, ∑ l : Fin d, (t1 (i, l))^2
          ≤ (2 * δ)^2 * ‖spectralConfig S hS hd i‖^2 := by
        intro i
        have hcoord : ∀ l : Fin d, t1 (i, l) = ((W - M) (spectralConfig S hS hd i)) l := by
          intro l; rfl
        have hnorm : ∑ l : Fin d, (t1 (i, l))^2 = ‖(W - M) (spectralConfig S hS hd i)‖^2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcoord l]; simp [Real.norm_eq_abs, sq_abs]
        rw [hnorm]
        have hWM : ‖(W - M) (spectralConfig S hS hd i)‖ = ‖(M - W) (spectralConfig S hS hd i)‖ := by
          rw [show (W - M) (spectralConfig S hS hd i) = -((M - W) (spectralConfig S hS hd i)) by
            rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel, norm_neg]
        rw [hWM]
        have h2δ := hWclose (spectralConfig S hS hd i)
        have h0 : 0 ≤ ‖(M - W) (spectralConfig S hS hd i)‖ := norm_nonneg _
        calc ‖(M - W) (spectralConfig S hS hd i)‖^2
            ≤ (2 * δ * ‖spectralConfig S hS hd i‖)^2 := by
              apply sq_le_sq'
              · linarith [h0, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ0)
                  (norm_nonneg (spectralConfig S hS hd i))]
              · exact h2δ
          _ = (2 * δ)^2 * ‖spectralConfig S hS hd i‖^2 := by ring
      calc ∑ i : Fin n, ∑ l : Fin d, (t1 (i, l))^2
          ≤ ∑ i : Fin n, (2 * δ)^2 * ‖spectralConfig S hS hd i‖^2 := Finset.sum_le_sum (fun i _ => hperi i)
        _ = (2 * δ)^2 * ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2 := by rw [Finset.mul_sum]
        _ ≤ (2 * δ)^2 * ((d : ℝ) * (Λ + ε)) :=
            mul_le_mul_of_nonneg_left
              (sum_norm_sq_spectralConfig_le hd hT hS hα_pos hα hΛ hε hsmall) (by positivity)
    calc ‖t1‖ = Real.sqrt (‖t1‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((2 * δ)^2 * ((d : ℝ) * (Λ + ε))) := Real.sqrt_le_sqrt ht1sq
  -- Term-2 norm bound.
  have ht2bound : ‖term2vec hT hS hd‖ ≤ Real.sqrt ((d : ℝ)^2 * (ε / Real.sqrt (α / 2))^2) := by
    calc ‖term2vec hT hS hd‖ = Real.sqrt (‖term2vec hT hS hd‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((d : ℝ)^2 * (ε / Real.sqrt (α / 2))^2) :=
          Real.sqrt_le_sqrt (term2_norm_sq_le hd hT hS hα_pos hε_nonneg hα hε hsmall)
  -- Term-3 norm bound.
  have ht3bound : ‖term3vec hT hS hd‖ ≤ Real.sqrt (Λ * (4 * (n : ℝ) * ε^2 / α^2)) := by
    calc ‖term3vec hT hS hd‖ = Real.sqrt (‖term3vec hT hS hd‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (Λ * (4 * (n : ℝ) * ε^2 / α^2)) :=
          Real.sqrt_le_sqrt (term3_norm_sq_le hd hT hS hα_pos hα htail hΛ hε hsmall)
  -- `ConfigError ≤ √n · ‖etot‖`.
  have hconfig : Acharyya2024.ConfigError (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd)
      ≤ Real.sqrt n * ‖etot‖ := by
    -- `ConfigError = ∑_i ‖W(ψ̂ i) − ψ i‖`; each is `√(∑_l etot(i,l)²)`.
    have hai : ∀ i : Fin n, ‖W (spectralConfig S hS hd i) - spectralConfig T hT hd i‖
        = Real.sqrt (∑ l : Fin d, (etot (i, l))^2) := by
      intro i
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl (fun l _ => ?_)
      show ‖(W (spectralConfig S hS hd i) - spectralConfig T hT hd i) l‖^2 = (etot (i, l))^2
      rw [hetot]
      show ‖(W (spectralConfig S hS hd i)) l - (spectralConfig T hT hd i) l‖^2 = _
      rw [Real.norm_eq_abs, sq_abs]
    -- `∑_i √(rowSq i) ≤ √n · √(∑_i rowSq i) = √n · ‖etot‖`.
    have hetotsq : ‖etot‖^2 = ∑ i : Fin n, ∑ l : Fin d, (etot (i, l))^2 := frob_sq etot
    have hrow_nn : ∀ i : Fin n, 0 ≤ Real.sqrt (∑ l : Fin d, (etot (i, l))^2) :=
      fun i => Real.sqrt_nonneg _
    unfold Acharyya2024.ConfigError
    calc ∑ i : Fin n, ‖W (spectralConfig S hS hd i) - spectralConfig T hT hd i‖
        = ∑ i : Fin n, Real.sqrt (∑ l : Fin d, (etot (i, l))^2) := by
          refine Finset.sum_congr rfl (fun i _ => hai i)
      _ ≤ Real.sqrt n * Real.sqrt (∑ i : Fin n, (Real.sqrt (∑ l : Fin d, (etot (i, l))^2))^2) := by
          have hcard : (∑ i : Fin n, Real.sqrt (∑ l : Fin d, (etot (i, l))^2))^2
              ≤ (n : ℝ) * ∑ i : Fin n, (Real.sqrt (∑ l : Fin d, (etot (i, l))^2))^2 := by
            have h := sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun i => Real.sqrt (∑ l : Fin d, (etot (i, l))^2))
            simpa [Finset.card_univ] using h
          have hsum_nn : 0 ≤ ∑ i : Fin n, Real.sqrt (∑ l : Fin d, (etot (i, l))^2) :=
            Finset.sum_nonneg (fun i _ => hrow_nn i)
          rw [← Real.sqrt_mul (by positivity)]
          rw [show ∑ i : Fin n, Real.sqrt (∑ l : Fin d, (etot (i, l))^2)
              = Real.sqrt ((∑ i : Fin n, Real.sqrt (∑ l : Fin d, (etot (i, l))^2))^2) by
                rw [Real.sqrt_sq hsum_nn]]
          exact Real.sqrt_le_sqrt hcard
      _ = Real.sqrt n * ‖etot‖ := by
          congr 1
          rw [show (∑ i : Fin n, (Real.sqrt (∑ l : Fin d, (etot (i, l))^2))^2)
              = ∑ i : Fin n, ∑ l : Fin d, (etot (i, l))^2 by
                refine Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (by positivity))]
          rw [← hetotsq, Real.sqrt_sq (norm_nonneg _)]
  -- Assemble into `configBound`.
  calc Acharyya2024.ConfigError (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd)
      ≤ Real.sqrt n * ‖etot‖ := hconfig
    _ ≤ Real.sqrt n * (‖t1‖ + ‖term2vec hT hS hd‖ + ‖term3vec hT hS hd‖) :=
        mul_le_mul_of_nonneg_left hmink (Real.sqrt_nonneg _)
    _ ≤ configBound n d α Λ ε := by
        rw [configBound]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        have h12 := add_le_add ht1bound ht2bound
        have h123 := add_le_add h12 ht3bound
        -- `δ` is definitionally `↑d * (4 * ↑n * ε² / α²)`, matching `configBound`.
        exact h123

end Acharyya2025.ConfigPerturbation
