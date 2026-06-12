/-
Overlap-matrix lemmas for the configuration-assembly step of the DKPS
finite-sample concentration bridge.

Let `T`, `S` be symmetric operators on a finite-dimensional real inner product
space `E` with orthonormal eigenbases `u := hT.eigenvectorBasis hn`,
`v := hS.eigenvectorBasis hn` and sorted eigenvalues `λT`, `λS`.  The *overlap
matrix* of the top-`d` blocks is `Q_{kl} := ⟪v_k, u_l⟫` (rows indexed by the
sample eigenbasis `v`, columns by the population eigenbasis `u`).  This file
records the three algebraic facts about `Q` needed to assemble the perturbed
configuration `ψ̂ W` against the canonical `ψ` (WP7(c2) of
`planning/acharyya-plan.md`):

* a **bilinear Parseval** identity `⟪x, y⟫ = ∑ⱼ ⟪bⱼ, x⟫ ⟪bⱼ, y⟫`;
* the **`QᵀQ − I` deviation bound**: each entry of `QᵀQ − I` is, up to sign, the
  trailing cross-energy `−∑_{j ≥ d} ⟪v_j, u_k⟫ ⟪v_j, u_l⟫`, hence bounded
  entrywise by a Cauchy–Schwarz product of trailing-energy square roots;
* the **Sylvester-style commutator identity**
  `(λS_k − λT_l) Q_{kl} = ⟪v_k, (S − T) u_l⟫` and its entrywise operator-norm
  corollary `|(λS_k − λT_l) Q_{kl}| ≤ ε`.

The commutator identity is the algebraic heart of the Term-2 estimate in the
three-term decomposition `ψ̂W − ψ = ÛΛ̂^{1/2}(W − Q) + Û(Λ̂^{1/2}Q − QΛ^{1/2})
+ (ÛQ − U)Λ^{1/2}`; the `QᵀQ − I` bound feeds the Term-1 polar-factor estimate.

The overlap/commutator strategy follows Agterberg, Lubberts, and Arroyo,
*Entrywise estimation of singular vectors of low-rank matrices with heteroskedastic
noise*, IEEE Trans. Inform. Theory 68 (2022), no. 7, 4618–4650; the two-to-infinity
Procrustes viewpoint is from Cape, Tang, and Priebe, *The two-to-infinity norm and
singular subspace geometry with applications to high-dimensional statistics*,
Ann. Statist. 47 (2019), no. 5, 2405–2439.

This file reuses the eigenbasis Parseval machinery of `Acharyya2025.Weyl`
(`sum_repr_sq_eq_norm_sq`, `OrthonormalBasis.repr_apply_apply`) and the
cross-term identity of `Acharyya2025.DavisKahan`
(`inner_eigenvector_map_sub_eq`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2025.Weyl
import Acharyya2025.DavisKahan

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix
open Module (finrank)

namespace Acharyya2025.Overlap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n d : ℕ} {T S : E →ₗ[ℝ] E}

/-! ### (1) Bilinear Parseval

In any orthonormal basis `b`, the inner product factors as the coordinatewise
sum `⟪x, y⟫ = ∑ⱼ ⟪bⱼ, x⟫ ⟪bⱼ, y⟫`.  This is Mathlib's
`OrthonormalBasis.sum_inner_mul_inner` with the inner-product arguments reordered
to the `⟪bⱼ, ·⟫` convention used throughout the overlap matrix. -/

omit [FiniteDimensional ℝ E] in
/-- **Bilinear Parseval.**  Expanding both arguments in an orthonormal basis `b`,
`⟪x, y⟫ = ∑ⱼ ⟪bⱼ, x⟫ ⟪bⱼ, y⟫`.  (Real inner product; arguments ordered so the
basis vector appears first, matching the overlap-matrix convention.)

Role: internal helper / standard fact (Parseval's identity), used to expand the
overlap-matrix entries below. -/
theorem inner_eq_sum_inner_basis_mul
    (b : OrthonormalBasis (Fin n) ℝ E)   -- hypothesis: `b` is an orthonormal basis
    (x y : E) :
    -- Conclusion: the inner product factors coordinatewise in the basis `b`.
    ⟪x, y⟫_ℝ = ∑ j : Fin n, ⟪b j, x⟫_ℝ * ⟪b j, y⟫_ℝ := by
  rw [← b.sum_inner_mul_inner x y]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [real_inner_comm x (b j)]

/-! ### (2) The overlap matrix and the `QᵀQ − I` deviation bound -/

/-- The **overlap matrix** of the top-`d` eigenblocks: `Q_{kl} = ⟪v_k, u_l⟫`,
where `v_k = hS.eigenvectorBasis hn (castLE k)` (sample eigenbasis, rows) and
`u_l = hT.eigenvectorBasis hn (castLE l)` (population eigenbasis, columns).

Paper correspondence: `Q` measures the **subspace overlap / inner-product
preservation** between the leading sample and population eigenbases.  Its
closeness to an orthogonal matrix (lemmas below) is exactly what underlies the
existence of the aligning orthogonal `W*` in Theorem 2: `W*` is the orthogonal
matrix nearest to `Q`.

`hT`, `hS`: symmetry of the population (`T`) and sample (`S`) operators (so they
have orthonormal eigenbases and real sorted eigenvalues).  `hn`, `hd`: the
ambient dimension is `n` and the leading block size `d ≤ n`. -/
noncomputable def overlap (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℝ E = n) (hd : d ≤ n) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => ⟪hS.eigenvectorBasis hn (Fin.castLE hd k),
              hT.eigenvectorBasis hn (Fin.castLE hd l)⟫_ℝ

/-- The image of `Fin.castLE hd` is exactly the index set `{j : Fin n | (j:ℕ) < d}`:
the sum over `Fin d` reindexes to the sum over the leading-block filter.

Role: internal helper / reindexing bookkeeping. -/
private theorem sum_castLE_eq_sum_filter_lt (hd : d ≤ n) (f : Fin n → ℝ) :
    ∑ m : Fin d, f (Fin.castLE hd m)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : Nat) < d), f j := by
  classical
  refine Finset.sum_bij'
    (fun (m : Fin d) _ => Fin.castLE hd m)
    (fun (j : Fin n) hj => ⟨(j : Nat), (Finset.mem_filter.mp hj).2⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- forward map lands in the filter
    intro m _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp [Fin.castLE]
  · -- backward map lands in `univ`
    intro j _
    exact Finset.mem_univ _
  · -- left inverse
    intro m _
    apply Fin.ext
    simp [Fin.castLE]
  · -- right inverse
    intro j hj
    apply Fin.ext
    simp [Fin.castLE]
  · -- value compatibility
    intro m _
    rfl

/-- The leading-block `j`-coordinate of `⟪u_k, u_l⟫` collected as `(QᵀQ)_{kl}`:
`(QᵀQ)_{kl} = ∑_{j < d} ⟪v_j, u_k⟫ ⟪v_j, u_l⟫`.

Role: internal helper (entrywise expansion of `QᵀQ`). -/
private theorem transpose_mul_overlap_apply
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n) (hd : d ≤ n)
    (k l : Fin d) :
    ((overlap hT hS hn hd)ᵀ * (overlap hT hS hn hd)) k l
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : Nat) < d),
          ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn (Fin.castLE hd k)⟫_ℝ
            * ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn (Fin.castLE hd l)⟫_ℝ := by
  rw [Matrix.mul_apply]
  -- `(QᵀQ)_{kl} = ∑_{m : Fin d} Q_{mk} Q_{ml}`, then reindex the `m`-sum.
  rw [← sum_castLE_eq_sum_filter_lt hd
        (fun j => ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn (Fin.castLE hd k)⟫_ℝ
          * ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn (Fin.castLE hd l)⟫_ℝ)]
  refine Finset.sum_congr rfl ?_
  intro m _
  simp only [Matrix.transpose_apply, overlap]

/-- `⟪u_k, u_l⟫ = δ_{kl}`: the leading population eigenvectors are orthonormal,
since `Fin.castLE` is injective.

Role: internal helper / standard fact (orthonormality of the eigenbasis). -/
private theorem inner_eigenvectorBasis_castLE
    (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (hd : d ≤ n) (k l : Fin d) :
    ⟪hT.eigenvectorBasis hn (Fin.castLE hd k),
        hT.eigenvectorBasis hn (Fin.castLE hd l)⟫_ℝ
      = if k = l then (1 : ℝ) else 0 := by
  classical
  have hortho := (hT.eigenvectorBasis hn).orthonormal
  rw [orthonormal_iff_ite.mp hortho (Fin.castLE hd k) (Fin.castLE hd l)]
  by_cases h : k = l
  · simp [h]
  · rw [if_neg h, if_neg (fun he => h (Fin.castLE_injective hd he))]

/-- **`QᵀQ − I` deviation bound (entrywise).**  Each off-orthogonality entry of
`QᵀQ` is the trailing cross-energy
`(QᵀQ − I)_{kl} = −∑_{j ≥ d} ⟪v_j, u_k⟫ ⟪v_j, u_l⟫`, hence bounded by the
Cauchy–Schwarz product of the trailing-energy square roots:
`|(QᵀQ − I)_{kl}| ≤ √(∑_{j ≥ d} ⟪v_j, u_k⟫²) · √(∑_{j ≥ d} ⟪v_j, u_l⟫²)`.

Paper correspondence: this measures how far the overlap matrix `Q` is from being
orthogonal (`QᵀQ ≈ I`).  It feeds the **Term-1 polar-factor estimate** in the
decomposition of `ψ̂W* − ψ`, i.e. it justifies that the orthogonal `W*` nearest
to `Q` is close to `Q`. -/
theorem abs_overlapT_mul_overlap_sub_one_le
    -- hypotheses: `T`, `S` symmetric; ambient dimension `n`; leading block `d ≤ n`
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n) (hd : d ≤ n)
    (k l : Fin d) :
    -- Conclusion: each entry of `QᵀQ − I` is bounded by the Cauchy–Schwarz product
    -- of the trailing (`j ≥ d`) cross-energies of the two columns.
    |((overlap hT hS hn hd)ᵀ * (overlap hT hS hn hd)) k l
        - (1 : Matrix (Fin d) (Fin d) ℝ) k l|
      ≤ Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
            (⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn (Fin.castLE hd k)⟫_ℝ)^2)
        * Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)),
            (⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn (Fin.castLE hd l)⟫_ℝ)^2) := by
  classical
  set u := hT.eigenvectorBasis hn with hu
  set v := hS.eigenvectorBasis hn with hv
  -- abbreviations for the trailing/leading coordinate functions
  set fk : Fin n → ℝ := fun j => ⟪v j, u (Fin.castLE hd k)⟫_ℝ with hfk
  set fl : Fin n → ℝ := fun j => ⟪v j, u (Fin.castLE hd l)⟫_ℝ with hfl
  -- bilinear Parseval (in the `v`-basis) for `⟪u_k, u_l⟫`
  have hpars : ⟪u (Fin.castLE hd k), u (Fin.castLE hd l)⟫_ℝ
      = ∑ j : Fin n, fk j * fl j := by
    rw [hfk, hfl]
    exact inner_eq_sum_inner_basis_mul v _ _
  -- split the full sum into leading (`< d`) and trailing (`≥ d`) blocks
  have hsplit : ∑ j : Fin n, fk j * fl j
      = (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : Nat) < d), fk j * fl j)
        + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ ((j : Nat) < d)), fk j * fl j :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => (j : Nat) < d) _).symm
  -- the `¬ (j < d)` filter is the `d ≤ j` filter
  have hfilter_eq : (Finset.univ.filter (fun j : Fin n => ¬ ((j : Nat) < d)))
      = Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)) := by
    ext j; simp [not_lt]
  -- the leading block is exactly `(QᵀQ)_{kl}`
  have hlead : (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : Nat) < d), fk j * fl j)
      = ((overlap hT hS hn hd)ᵀ * (overlap hT hS hn hd)) k l := by
    rw [transpose_mul_overlap_apply hT hS hn hd k l]
  -- `⟪u_k, u_l⟫ = δ_{kl} = I_{kl}`
  have hdelta : ⟪u (Fin.castLE hd k), u (Fin.castLE hd l)⟫_ℝ
      = (1 : Matrix (Fin d) (Fin d) ℝ) k l := by
    rw [hu, inner_eigenvectorBasis_castLE hT hn hd k l, Matrix.one_apply]
  -- assemble: `(QᵀQ − I)_{kl} = − (trailing sum)`
  have hkey : ((overlap hT hS hn hd)ᵀ * (overlap hT hS hn hd)) k l
        - (1 : Matrix (Fin d) (Fin d) ℝ) k l
      = - ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)), fk j * fl j := by
    have := hpars
    rw [hsplit, hfilter_eq, hlead, hdelta] at this
    linarith [this]
  rw [hkey, abs_neg]
  -- Cauchy–Schwarz on the trailing sum
  set sk := Finset.univ.filter (fun j : Fin n => d ≤ (j : Nat)) with hsk
  have hcs : (∑ j ∈ sk, fk j * fl j) ^ 2
      ≤ (∑ j ∈ sk, fk j ^ 2) * ∑ j ∈ sk, fl j ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq sk fk fl
  -- take square roots
  have hnn_k : (0 : ℝ) ≤ ∑ j ∈ sk, fk j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hnn_l : (0 : ℝ) ≤ ∑ j ∈ sk, fl j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  calc |∑ j ∈ sk, fk j * fl j|
      = Real.sqrt ((∑ j ∈ sk, fk j * fl j) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((∑ j ∈ sk, fk j ^ 2) * ∑ j ∈ sk, fl j ^ 2) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ j ∈ sk, fk j ^ 2) * Real.sqrt (∑ j ∈ sk, fl j ^ 2) :=
        Real.sqrt_mul hnn_k _

/-! ### (3) The Sylvester-style commutator identity

The key algebraic identity feeding the Term-2 commutator estimate:
`(λS_k − λT_l) Q_{kl} = ⟪v_k, (S − T) u_l⟫`.  This is the cross-term identity of
`Acharyya2025.DavisKahan` (`inner_eigenvector_map_sub_eq`) with the roles of the
two operators interchanged, transported through `real_inner_comm`. -/

/-- **Commutator identity.**  For the leading eigenvectors `v_k` (of `S`,
eigenvalue `λS_k`) and `u_l` (of `T`, eigenvalue `λT_l`),
`(λS_k − λT_l) Q_{kl} = ⟪v_k, (S − T) u_l⟫`.

Sign convention: the eigenvalue factor is `λS_k − λT_l` (sample minus population),
matching the design `(λ̂_k − λ_l) Q_{kl} = ⟪v_k, (S − T) u_l⟫`.

Role: this is the algebraic heart of the **Term-2** commutator estimate in the
decomposition of `ψ̂W* − ψ`; it relates the overlap entries to the perturbation
`S − T`. -/
theorem eigenvalue_commutator_eq
    -- hypotheses: `T`, `S` symmetric; ambient dimension `n`; leading block `d ≤ n`
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n) (hd : d ≤ n)
    (k l : Fin d) :
    -- Conclusion: the eigenvalue gap times the overlap entry equals the cross-term
    -- `⟪v_k, (S − T) u_l⟫` (Sylvester-style commutator identity).
    (hS.eigenvalues hn (Fin.castLE hd k) - hT.eigenvalues hn (Fin.castLE hd l))
        * (overlap hT hS hn hd) k l
      = ⟪hS.eigenvectorBasis hn (Fin.castLE hd k),
          (S - T) (hT.eigenvectorBasis hn (Fin.castLE hd l))⟫_ℝ := by
  -- `inner_eigenvector_map_sub_eq hS hT hn (castLE k) (castLE l)` instantiates the
  -- theorem's operator `T` with `S` (so its first basis is `v = hS.eigenvectorBasis`)
  -- and its operator `S` with `T` (so its second basis is `u = hT.eigenvectorBasis`),
  -- yielding `h : ⟪v_k, (T − S) u_l⟫ = (λT_l − λS_k) ⟪v_k, u_l⟫`.
  have h := Acharyya2025.DavisKahan.inner_eigenvector_map_sub_eq hS hT hn
    (Fin.castLE hd k) (Fin.castLE hd l)
  -- We transport `(T − S) → −(S − T)` and rearrange signs.
  have hswap : (T - S) (hT.eigenvectorBasis hn (Fin.castLE hd l))
      = - ((S - T) (hT.eigenvectorBasis hn (Fin.castLE hd l))) := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
  rw [hswap, inner_neg_right] at h
  -- now `h : -⟪v_k, (S−T) u_l⟫ = (λT_l − λS_k) ⟪v_k, u_l⟫`.
  simp only [overlap]
  -- the goal `(λS_k − λT_l)·Q_{kl} = ⟪v_k, (S−T) u_l⟫` follows from `h`.
  linear_combination h

/-! ### (4) Entrywise commutator bound -/

/-- **Entrywise commutator bound.**  If `S − T` is small in operator norm
(`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), then each commutator entry obeys
`|(λS_k − λT_l) Q_{kl}| ≤ ε`.  Immediate from the commutator identity and
Cauchy–Schwarz on unit eigenvectors.

Role: quantitative form of the Term-2 estimate feeding the `ψ̂W* − ψ` bound. -/
theorem abs_eigenvalue_diff_mul_overlap_le
    -- hypotheses: `T`, `S` symmetric; ambient dimension `n`; leading block `d ≤ n`
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℝ E = n) (hd : d ≤ n)
    -- hypothesis: `S − T` is `ε`-small in operator norm (perturbation size)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k l : Fin d) :
    -- Conclusion: each eigenvalue-gap-weighted overlap entry is bounded by `ε`.
    |(hS.eigenvalues hn (Fin.castLE hd k) - hT.eigenvalues hn (Fin.castLE hd l))
        * (overlap hT hS hn hd) k l| ≤ ε := by
  rw [eigenvalue_commutator_eq hT hS hn hd k l]
  -- `|⟪v_k, (S−T) u_l⟫| ≤ ‖v_k‖ ‖(S−T) u_l‖ ≤ ‖(S−T) u_l‖ ≤ ε ‖u_l‖ = ε`.
  set vk := hS.eigenvectorBasis hn (Fin.castLE hd k) with hvk
  set ul := hT.eigenvectorBasis hn (Fin.castLE hd l) with hul
  have hvk1 : ‖vk‖ = 1 := by rw [hvk]; exact (hS.eigenvectorBasis hn).orthonormal.1 _
  have hul1 : ‖ul‖ = 1 := by rw [hul]; exact (hT.eigenvectorBasis hn).orthonormal.1 _
  calc |⟪vk, (S - T) ul⟫_ℝ|
      ≤ ‖vk‖ * ‖(S - T) ul‖ := abs_real_inner_le_norm _ _
    _ = ‖(S - T) ul‖ := by rw [hvk1, one_mul]
    _ ≤ ε * ‖ul‖ := hε ul
    _ = ε := by rw [hul1, mul_one]

end Acharyya2025.Overlap
