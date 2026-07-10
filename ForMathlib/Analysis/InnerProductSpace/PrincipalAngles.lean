/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`PrincipalAngles.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W0.2 of
`dev/davis-kahan-gap-closure-plan.md`.

The canonical principal-angle API: the cosines of the principal angles between
two subspaces (given by orthonormal families) are the singular values of the
flat overlap operator `overlapOp` (from `AlignedBasis.lean`).  This packages the
`cos Θ`/`sin Θ` vectors, their basic order/range properties, the symmetry in the
two families (which needs `singularValues_adjoint`, W0.1(d)), and the bridge
`‖sin Θ‖²_F = d − overlap` to the flat overlap sum.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.AlignedBasis
import ForMathlib.Analysis.InnerProductSpace.DavisKahan
import ForMathlib.Analysis.InnerProductSpace.KyFan

/-! # Principal angles between subspaces

For orthonormal families `u : Fin d → E` and `v : Fin d → E` spanning two
`d`-dimensional subspaces `U = span u`, `V = span v`, the **cosines of the
principal angles** are the singular values of the flat overlap operator
`overlapOp hu hv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)`
(matrix `⟪uᵢ, vⱼ⟫`).  The singular values lie in `[0, 1]` (the operator is a
contraction), are sorted decreasingly, and are symmetric in `u, v` (`M⋆` is the
overlap operator of the swapped pair, and `σ(M⋆) = σ(M)`).

The complementary quantity `‖sin Θ‖²_F = ∑ᵢ sin²θᵢ = ∑ᵢ (1 − cos²θᵢ)` measures
the total misalignment of the two subspaces; here it equals `d − overlap` where
`overlap = ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` is the flat overlap sum used throughout the
Davis–Kahan development.

## Main definitions

* `ForMathlib.cosPrincipalAngles`: the sorted cosines `σ(overlapOp hu hv)`.
* `ForMathlib.sinThetaSq`: the squared Frobenius sine `∑ᵢ (1 − cos²θᵢ)`.

## Main results

* `ForMathlib.cosPrincipalAngles_nonneg` / `_le_one` / `_antitone`: range and
  order.
* `ForMathlib.overlapOp_adjoint`: `(overlapOp hu hv)⋆ = overlapOp hv hu`.
* `ForMathlib.cosPrincipalAngles_comm`: symmetry `cos Θ(u, v) = cos Θ(v, u)`.
* `ForMathlib.sinThetaSq_eq_sub_overlap`: `‖sin Θ‖²_F = d − overlap`.
* `ForMathlib.sum_sq_norm_aligned_le_sinThetaSq`: the Yu–Wang–Samworth
  aligned-basis bound restated as `∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`.
-/

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {d : ℕ}

/-- **The cosines of the principal angles** between the subspaces spanned by two
orthonormal families `u, v : Fin d → E`: the (sorted, `ℕ →₀ ℝ`-indexed) singular
values of the overlap operator `overlapOp hu hv`. -/
noncomputable def cosPrincipalAngles {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  (overlapOp hu hv).singularValues

theorem cosPrincipalAngles_nonneg {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : ℕ) : 0 ≤ cosPrincipalAngles hu hv i :=
  (overlapOp hu hv).singularValues_nonneg i

/-- The principal-angle cosines are at most `1`: the overlap operator is a
contraction. -/
theorem cosPrincipalAngles_le_one {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : Fin d) : cosPrincipalAngles hu hv (i : ℕ) ≤ 1 :=
  singularValues_le_one_of_contraction (overlapOp_contraction hu hv)
    finrank_euclideanSpace_fin i

theorem cosPrincipalAngles_antitone {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : Antitone (cosPrincipalAngles hu hv) :=
  (overlapOp hu hv).singularValues_antitone

/-- **The overlap operator of the swapped pair is the adjoint.**
`(overlapOp hu hv)⋆ = overlapOp hv hu`, immediate from `(P⋆ ∘ Q)⋆ = Q⋆ ∘ P`. -/
theorem overlapOp_adjoint {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (overlapOp hu hv).adjoint = overlapOp hv hu := by
  rw [overlapOp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, overlapOp]

/-- **Symmetry of the principal angles.**  `cos Θ(u, v) = cos Θ(v, u)`: the two
overlap operators are adjoint (`overlapOp_adjoint`) and adjoints share singular
values (`singularValues_adjoint`, plan step W0.1(d)). -/
theorem cosPrincipalAngles_comm {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : cosPrincipalAngles hu hv = cosPrincipalAngles hv hu := by
  rw [cosPrincipalAngles, cosPrincipalAngles, ← overlapOp_adjoint hu hv, singularValues_adjoint]

/-- **The squared Frobenius sine** `‖sin Θ‖²_F = ∑ᵢ sin²θᵢ = ∑ᵢ (1 − cos²θᵢ)`
between the subspaces spanned by two orthonormal families of the same size. -/
noncomputable def sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℝ :=
  ∑ k : Fin d, (1 - cosPrincipalAngles hu hv (k : ℕ) ^ 2)

/-- **`‖sin Θ‖²_F = d − overlap`.**  The squared Frobenius sine equals `d` minus
the flat overlap sum `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` (which is `∑ cos²θᵢ`). -/
theorem sinThetaSq_eq_sub_overlap {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = (d : ℝ) - ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 := by
  unfold sinThetaSq
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  congr 1
  unfold cosPrincipalAngles
  exact sum_sq_singularValues_overlapOp hu hv

theorem sinThetaSq_nonneg {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    0 ≤ sinThetaSq hu hv :=
  Finset.sum_nonneg fun k _ => by
    have h1 := cosPrincipalAngles_le_one hu hv k
    have h0 := cosPrincipalAngles_nonneg hu hv (k : ℕ)
    nlinarith

/-- Symmetry of the squared Frobenius sine, `‖sin Θ(u, v)‖²_F = ‖sin Θ(v, u)‖²_F`. -/
theorem sinThetaSq_comm {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = sinThetaSq hv hu := by
  unfold sinThetaSq
  rw [cosPrincipalAngles_comm hu hv]

/-- **Aligned-basis bound in principal-angle form.**  The Yu–Wang–Samworth
Procrustes-rotated basis `wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)` obeys
`∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`. -/
theorem sum_sq_norm_aligned_le_sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ j, ‖familyIsometry hv ((polarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))
        - u j‖ ^ 2
      ≤ 2 * sinThetaSq hu hv := by
  rw [sinThetaSq_eq_sub_overlap]
  exact sum_sq_norm_aligned_le hu hv

/-! ### Eigenblock families and the encoding-coherence bridges

The `sinThetaSq` of two eigenblock families equals the cross-block overlap sum
used throughout `DavisKahan.lean`, and (for equal blocks) half the squared
Frobenius distance of the two spectral projections (plan step E4 of
`dev/davis-kahan-expert-completion-plan.md`).  All the `sin Θ` encodings in
this development are therefore provably the same quantity. -/

section Block

variable {n : ℕ}

/-- The orthonormal family enumerating the `s`-selected vectors of an
orthonormal basis. -/
noncomputable def blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Fin d → E := fun i => b (s.orderIsoOfFin hd i)

omit [FiniteDimensional 𝕜 E] in
theorem orthonormal_blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Orthonormal 𝕜 (blockFamily b s hd) :=
  b.orthonormal.comp _ (Subtype.coe_injective.comp (s.orderIsoOfFin hd).injective)

omit [FiniteDimensional 𝕜 E] in
theorem range_blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Set.range (blockFamily b s hd) = b '' ↑s := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, (s.orderIsoOfFin hd i).2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(s.orderIsoOfFin hd).symm ⟨j, hj⟩, ?_⟩
    simp [blockFamily]

private theorem sum_blockFamily {s : Finset (Fin n)} (hd : s.card = d) (g : Fin n → ℝ) :
    ∑ i : Fin d, g ((s.orderIsoOfFin hd i : Fin n)) = ∑ i ∈ s, g i := by
  rw [← Finset.sum_coe_sort s g]
  exact Fintype.sum_equiv (s.orderIsoOfFin hd).toEquiv _ _ fun i => rfl

/-- **`sinThetaSq` of two eigenblocks is the cross-block overlap sum** — the
bridge from the principal-angle encoding to the `DavisKahan.lean` encoding. -/
theorem sinThetaSq_blockFamily_eq_sum_cross (bT bS : OrthonormalBasis (Fin n) 𝕜 E)
    {s s' : Finset (Fin n)} (hsd : s.card = d) (hs'd : s'.card = d) :
    sinThetaSq (orthonormal_blockFamily bT s hsd) (orthonormal_blockFamily bS s' hs'd)
      = ∑ j ∈ s', ∑ i ∈ sᶜ, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := by
  rw [sinThetaSq_eq_sub_overlap]
  have hrow : ∀ j : Fin n, ∑ i : Fin d, ‖⟪blockFamily bT s hsd i, bS j⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := fun j =>
    sum_blockFamily hsd fun i => ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
  have houter : ∑ k : Fin d, ∑ i : Fin d,
        ‖⟪blockFamily bT s hsd i, blockFamily bS s' hs'd k⟫_𝕜‖ ^ 2
      = ∑ j ∈ s', ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := by
    rw [show (fun k : Fin d => ∑ i : Fin d,
          ‖⟪blockFamily bT s hsd i, blockFamily bS s' hs'd k⟫_𝕜‖ ^ 2)
        = fun k : Fin d => ∑ i ∈ s,
          ‖⟪bT i, bS ((s'.orderIsoOfFin hs'd k : Fin n))⟫_𝕜‖ ^ 2 from
      funext fun k => hrow _]
    exact sum_blockFamily hs'd fun j => ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
  rw [houter]
  have hpars : ∀ j : Fin n, ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
      + ∑ i ∈ sᶜ, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 = 1 := fun j => by
    rw [Finset.sum_add_sum_compl, bT.sum_sq_norm_inner_right (bS j),
      bS.orthonormal.norm_eq_one j, one_pow]
  have hcard : (d : ℝ) = ∑ _j ∈ s', (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hs'd]
  rw [hcard, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by linarith [hpars j]

/-- **`sinThetaSq` is half the squared Frobenius projector distance**: for two
eigenblocks selected by the same `s`,
`∑ₖ ‖(P̂ − P)(bT k)‖² = 2 sinThetaSq`. -/
theorem sum_norm_sub_starProjection_sq_eq_two_mul_sinThetaSq
    (bT bS : OrthonormalBasis (Fin n) 𝕜 E) {s : Finset (Fin n)} (hsd : s.card = d) :
    ∑ k, ‖((Submodule.span 𝕜 (bS '' ↑s)).starProjection
        - (Submodule.span 𝕜 (bT '' ↑s)).starProjection) (bT k)‖ ^ 2
      = 2 * sinThetaSq (orthonormal_blockFamily bT s hsd)
          (orthonormal_blockFamily bS s hsd) := by
  rw [sum_norm_sub_starProjection_span_sq_eq bT bS s,
    sinThetaSq_comm, sinThetaSq_blockFamily_eq_sum_cross bS bT hsd hsd]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← norm_inner_symm]

end Block

/-! ### The operator-norm identification `‖Q̂ ∘L P‖ = sin θ_max`

The operator norm of "project onto `U`, then onto `Wᗮ`" is exactly the sine of
the largest principal angle between `U` and `W` (plan step E2 of
`dev/davis-kahan-expert-completion-plan.md`).  This certifies that the
operator-norm Davis–Kahan theorem (`SinThetaOpNorm.lean`) bounds a principal
angle. -/

@[simp] theorem cosPrincipalAngles_eq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : ℕ) :
    cosPrincipalAngles hu hv i = (overlapOp hu hv).singularValues i := rfl

omit [FiniteDimensional 𝕜 E] in
/-- The coordinate isometry maps into the span of the family. -/
theorem familyIsometry_mem_span {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (y : EuclideanSpace 𝕜 (Fin d)) :
    familyIsometry hu y ∈ Submodule.span 𝕜 (Set.range u) := by
  rw [familyIsometry_apply]
  exact Submodule.sum_smul_mem _ _ fun i _ => Submodule.subset_span (Set.mem_range_self i)

/-- **Coisometry padding: precomposing with the adjoint of a `familyIsometry`
preserves singular values.**  For an orthonormal family `u : Fin d → E` and an
endomorphism `X` of `EuclideanSpace 𝕜 (Fin d)`, the composite
`X ∘ₗ ι_u⋆ : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)` has the same singular values as
`X`, as finsupps — the `finrank 𝕜 E − d` extra slots on the left are the zero
padding.  `ι_u⋆ ∘ ι_u = 1` gives the gram identity
`gram (X ∘ₗ ι_u⋆) = ι_u ∘ₗ gram X ∘ₗ ι_u⋆`, whose eigendata is that of `gram X`
pushed through `ι_u` and extended by `0` on `(span (range u))ᗮ`; gram
eigenvalues are nonnegative and sorted, so the padded vector is still sorted
and the sorted-eigenvalue uniqueness (`eigenvalues_eq_of_eigenbasis`) closes.
This transports singular-value data between the coordinate model and the
ambient space (plan step OP3.0). -/
theorem singularValues_comp_adjoint_familyIsometry
    {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (X : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    (X ∘ₗ LinearMap.adjoint (familyIsometry hu).toLinearMap).singularValues
      = X.singularValues := by
  classical
  set ι : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E := (familyIsometry hu).toLinearMap with hι
  set Y : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) := X ∘ₗ LinearMap.adjoint ι with hYdef
  set U : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range u) with hUdef
  -- `ι` is isometric onto `U`: `ι⋆ ∘ ι = 1` and `ι⋆` kills `Uᗮ`.
  have hadj : ∀ x, LinearMap.adjoint ι (ι x) = x := fun x =>
    ext_inner_right 𝕜 fun y => by
      rw [LinearMap.adjoint_inner_left]
      exact (familyIsometry hu).inner_map_map x y
  have hker : ∀ y ∈ Uᗮ, LinearMap.adjoint ι y = 0 := fun y hy =>
    ext_inner_right 𝕜 fun z => by
      rw [LinearMap.adjoint_inner_left, inner_zero_left]
      exact Submodule.inner_left_of_mem_orthogonal (familyIsometry_mem_span hu z) hy
  -- The gram of `Y` is the gram of `X` conjugated through `ι`.
  have hgram : LinearMap.adjoint Y ∘ₗ Y
      = ι ∘ₗ ((LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint ι) := by
    rw [hYdef, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
    ext x
    simp only [LinearMap.comp_apply]
  -- Dimensions.
  have hd : finrank 𝕜 (EuclideanSpace 𝕜 (Fin d)) = d := finrank_euclideanSpace_fin
  have hdimU : finrank 𝕜 U = d := by
    rw [hUdef, finrank_span_eq_card hu.linearIndependent, Fintype.card_fin]
  have hsum := Submodule.finrank_add_finrank_orthogonal U
  have hdn : d ≤ finrank 𝕜 E := by omega
  have hdimperp : finrank 𝕜 (Uᗮ : Submodule 𝕜 E) = finrank 𝕜 E - d := by omega
  -- Eigendata of `gram X`.
  have hGX : (LinearMap.adjoint X ∘ₗ X).IsSymmetric := X.isSymmetric_adjoint_comp_self
  have hμ_anti : Antitone (hGX.eigenvalues hd) := hGX.eigenvalues_antitone hd
  have hμ_nonneg : ∀ i, 0 ≤ hGX.eigenvalues hd i := fun i =>
    X.isPositive_adjoint_comp_self.nonneg_eigenvalues hd i
  -- The glued eigenbasis of `gram Y`: `ι (fᵢ)` for `i < d` (`f` the eigenbasis
  -- of `gram X`), an orthonormal basis of `Uᗮ` beyond.
  set g := stdOrthonormalBasis 𝕜 (Uᗮ : Submodule 𝕜 E) with hg
  set w : Fin (finrank 𝕜 E) → E := fun i =>
    if h : (i : ℕ) < d then ι (hGX.eigenvectorBasis hd ⟨(i : ℕ), h⟩)
    else (g (Fin.cast hdimperp.symm ⟨(i : ℕ) - d, by have := i.isLt; omega⟩) : E)
    with hw
  have hw_lt : ∀ (i : Fin (finrank 𝕜 E)) (h : (i : ℕ) < d),
      w i = ι (hGX.eigenvectorBasis hd ⟨(i : ℕ), h⟩) := fun i h => by
    simp only [hw]; exact dif_pos h
  have hw_ge : ∀ (i : Fin (finrank 𝕜 E)) (h : ¬ (i : ℕ) < d),
      w i = (g (Fin.cast hdimperp.symm
        ⟨(i : ℕ) - d, by have := i.isLt; omega⟩) : E) := fun i h => by
    simp only [hw]; exact dif_neg h
  have hw_mem_lt : ∀ (i : Fin (finrank 𝕜 E)) (h : (i : ℕ) < d), w i ∈ U := fun i h => by
    rw [hw_lt i h, hUdef]; exact familyIsometry_mem_span hu _
  have hw_mem_ge : ∀ (i : Fin (finrank 𝕜 E)) (h : ¬ (i : ℕ) < d), w i ∈ Uᗮ := fun i h => by
    rw [hw_ge i h]; exact SetLike.coe_mem _
  -- Orthonormality of the glued family.
  have hw_on : Orthonormal 𝕜 w := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : (i : ℕ) < d
    · by_cases hj : (j : ℕ) < d
      · have hcoe : ∀ x, ι x = familyIsometry hu x := fun _ => rfl
        rw [hw_lt i hi, hw_lt j hj, hcoe, hcoe, (familyIsometry hu).inner_map_map,
          orthonormal_iff_ite.mp (hGX.eigenvectorBasis hd).orthonormal]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg (fun hc => hij (Fin.ext (by simpa using congrArg Fin.val hc))),
            if_neg hij]
      · rw [if_neg (fun hc : i = j => hj (hc ▸ hi))]
        exact Submodule.inner_right_of_mem_orthogonal (hw_mem_lt i hi) (hw_mem_ge j hj)
    · by_cases hj : (j : ℕ) < d
      · rw [if_neg (fun hc : i = j => hi (hc ▸ hj))]
        exact Submodule.inner_left_of_mem_orthogonal (hw_mem_lt j hj) (hw_mem_ge i hi)
      · rw [hw_ge i hi, hw_ge j hj, ← Submodule.coe_inner,
          orthonormal_iff_ite.mp g.orthonormal]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg (fun hc => ?_), if_neg hij]
          rw [Fin.cast_inj] at hc
          have hval : (i : ℕ) - d = (j : ℕ) - d := by
            simpa using congrArg Fin.val hc
          have hi' := i.isLt
          have hj' := j.isLt
          exact hij (Fin.ext (by omega))
  -- The glued family is an orthonormal basis (cardinality = dimension).
  have hw_span : ⊤ ≤ Submodule.span 𝕜 (Set.range w) := by
    refine (Submodule.eq_top_of_finrank_eq ?_).ge
    rw [finrank_span_eq_card hw_on.linearIndependent, Fintype.card_fin]
  set bE : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
    OrthonormalBasis.mk hw_on hw_span with hbE
  have hbE_apply : ∀ i, bE i = w i := fun i => by
    rw [hbE]; exact congrFun (OrthonormalBasis.coe_mk hw_on hw_span) i
  -- The padded eigenvalue vector is antitone (gram eigenvalues are `≥ 0`).
  have hμ'_anti : Antitone (fun i : Fin (finrank 𝕜 E) =>
      if h : (i : ℕ) < d then hGX.eigenvalues hd ⟨(i : ℕ), h⟩ else 0) := by
    intro i j hij
    have hvij : (i : ℕ) ≤ (j : ℕ) := hij
    dsimp only
    by_cases hj : (j : ℕ) < d
    · have hi : (i : ℕ) < d := lt_of_le_of_lt hvij hj
      rw [dif_pos hi, dif_pos hj]
      exact hμ_anti (Fin.mk_le_mk.mpr hvij)
    · rw [dif_neg hj]
      by_cases hi : (i : ℕ) < d
      · rw [dif_pos hi]; exact hμ_nonneg _
      · rw [dif_neg hi]
  -- The glued basis diagonalizes `gram Y` with the padded eigenvalues.
  have heig : ∀ i : Fin (finrank 𝕜 E), (LinearMap.adjoint Y ∘ₗ Y) (bE i)
      = (((if h : (i : ℕ) < d then hGX.eigenvalues hd ⟨(i : ℕ), h⟩ else 0 : ℝ)) : 𝕜)
        • bE i := by
    intro i
    rw [hbE_apply i, hgram]
    by_cases h : (i : ℕ) < d
    · rw [dif_pos h, hw_lt i h, LinearMap.comp_apply, LinearMap.comp_apply, hadj,
        hGX.apply_eigenvectorBasis hd, map_smul]
    · rw [dif_neg h, hw_ge i h, LinearMap.comp_apply, LinearMap.comp_apply,
        hker _ (SetLike.coe_mem _), map_zero, map_zero, RCLike.ofReal_zero, zero_smul]
  have heq := eigenvalues_eq_of_eigenbasis Y.isSymmetric_adjoint_comp_self rfl bE
    hμ'_anti heig
  -- Read off the singular values slot by slot.
  refine Finsupp.ext fun i => ?_
  rcases lt_or_ge i d with hid | hid
  · have hin : i < finrank 𝕜 E := lt_of_lt_of_le hid hdn
    rw [Y.singularValues_of_lt rfl hin, X.singularValues_of_lt hd hid, heq]
    simp only [dif_pos hid]
  · rcases lt_or_ge i (finrank 𝕜 E) with hin | hin
    · rw [Y.singularValues_of_lt rfl hin,
        X.singularValues_of_finrank_le (hd.trans_le hid), heq]
      simp only [dif_neg (not_lt.mpr hid)]
      exact Real.sqrt_zero
    · rw [Y.singularValues_of_finrank_le hin,
        X.singularValues_of_finrank_le (hd.trans_le hid)]

/-- Coordinates of the overlap operator: `(overlapOp hu hv y) i = ⟪uᵢ, ι_v y⟫`. -/
theorem overlapOp_coord {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (y : EuclideanSpace 𝕜 (Fin d)) (i : Fin d) :
    overlapOp hu hv y i = ⟪u i, familyIsometry hv y⟫_𝕜 := by
  have h1 : overlapOp hu hv y i
      = ⟪EuclideanSpace.single i (1 : 𝕜), overlapOp hu hv y⟫_𝕜 := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [h1, overlapOp_apply, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
    familyIsometry_single]

private theorem norm_sq_euclidean (z : EuclideanSpace 𝕜 (Fin d)) :
    ‖z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- Parseval for the projection onto the span of an orthonormal family
(`Set.range` phrasing of `Orthonormal.norm_sq_starProjection_span_image`). -/
private theorem norm_sq_starProjection_span_range {w : Fin d → E} (hw : Orthonormal 𝕜 w)
    (x : E) :
    ‖(Submodule.span 𝕜 (Set.range w)).starProjection x‖ ^ 2 = ∑ i, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  rw [← Set.image_univ, ← Finset.coe_univ]
  exact Orthonormal.norm_sq_starProjection_span_image hw Finset.univ x

/-- **The key Pythagoras computation**: for `x = ι_u y ∈ U = span u`,
`‖P_{Wᗮ} x‖² = ‖y‖² − ‖(overlapOp hw hu) y‖²`. -/
private theorem norm_sq_orthogonal_starProjection_familyIsometry
    {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w)
    (y : EuclideanSpace 𝕜 (Fin d)) :
    ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (familyIsometry hu y)‖ ^ 2
      = ‖y‖ ^ 2 - ‖overlapOp hw hu y‖ ^ 2 := by
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (familyIsometry hu y)
    (Submodule.span 𝕜 (Set.range w))
  have hWproj : ‖(Submodule.span 𝕜 (Set.range w)).starProjection (familyIsometry hu y)‖ ^ 2
      = ‖overlapOp hw hu y‖ ^ 2 := by
    rw [norm_sq_starProjection_span_range hw, norm_sq_euclidean]
    exact Finset.sum_congr rfl fun i _ => by rw [overlapOp_coord]
  have hiso : ‖familyIsometry hu y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [(familyIsometry hu).norm_map]
  linarith

/-- **Operator-norm principal-angle identification.**  For orthonormal families
`u, w : Fin d → E` spanning `U` and `W`, the operator norm of
`P_{Wᗮ} ∘L P_U` equals the sine of the largest principal angle between `U` and
`W`:

`‖P_{Wᗮ} ∘L P_U‖ = √(1 − cos²θ_max)`,

`cos θ_max` being the smallest principal-angle cosine
`cosPrincipalAngles hw hu (d − 1)`.  This certifies that the operator-norm
Davis–Kahan theorem (`norm_starProjection_comp_starProjection_le`) bounds
`sin θ_max`. -/
theorem norm_orthogonal_starProjection_comp_starProjection
    {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w) (hd : 0 < d) :
    ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection‖
      = Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) := by
  have hσ0 : 0 ≤ cosPrincipalAngles hw hu (d - 1) := cosPrincipalAngles_nonneg hw hu _
  have hσ1 : cosPrincipalAngles hw hu (d - 1) ≤ 1 := by
    have := cosPrincipalAngles_le_one hw hu (⟨d - 1, by omega⟩ : Fin d)
    simpa using this
  have h1σ : 0 ≤ 1 - cosPrincipalAngles hw hu (d - 1) ^ 2 := by nlinarith
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun z => ?_) ?_
  · -- upper bound: pull the projected vector back to coordinates via the
    -- adjoint of the coordinate isometry.
    set y : EuclideanSpace 𝕜 (Fin d) :=
      (familyIsometry hu).toLinearMap.adjoint
        ((Submodule.span 𝕜 (Set.range u)).starProjection z) with hy
    have hcoord : ∀ i, y i
        = ⟪u i, (Submodule.span 𝕜 (Set.range u)).starProjection z⟫_𝕜 := fun i => by
      have h1 : y i = ⟪EuclideanSpace.single i (1 : 𝕜), y⟫_𝕜 := by
        rw [EuclideanSpace.inner_single_left, map_one, one_mul]
      rw [h1, hy, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
        familyIsometry_single]
    have hxy : familyIsometry hu y
        = (Submodule.span 𝕜 (Set.range u)).starProjection z := by
      have hsum : familyIsometry hu y
          = ∑ i, ⟪u i, (Submodule.span 𝕜 (Set.range u)).starProjection z⟫_𝕜 • u i := by
        rw [familyIsometry_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [hcoord]
      rw [hsum, ← Orthonormal.starProjection_span_image_apply hu Finset.univ]
      apply Submodule.starProjection_eq_self_iff.mpr
      rw [Finset.coe_univ, Set.image_univ]
      exact Submodule.starProjection_apply_mem _ z
    have hyz : ‖y‖ ≤ ‖z‖ := by
      have h1 : ‖y‖ = ‖(Submodule.span 𝕜 (Set.range u)).starProjection z‖ := by
        rw [← hxy, (familyIsometry hu).norm_map]
      rw [h1]
      exact Submodule.norm_starProjection_apply_le _ z
    have hmin : cosPrincipalAngles hw hu (d - 1) * ‖y‖ ≤ ‖overlapOp hw hu y‖ := by
      rw [cosPrincipalAngles_eq]
      exact singularValues_last_mul_norm_le (overlapOp hw hu) finrank_euclideanSpace_fin hd y
    have h2 : ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection
          ((Submodule.span 𝕜 (Set.range u)).starProjection z)‖ ^ 2
        ≤ (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ ^ 2 := by
      rw [← hxy, norm_sq_orthogonal_starProjection_familyIsometry hu hw y]
      have p1 : cosPrincipalAngles hw hu (d - 1) ^ 2 * ‖y‖ ^ 2
          ≤ ‖overlapOp hw hu y‖ ^ 2 := by
        have h := mul_self_le_mul_self (mul_nonneg hσ0 (norm_nonneg y)) hmin
        nlinarith [h]
      have hyz2 : ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        have h := mul_self_le_mul_self (norm_nonneg y) hyz
        nlinarith [h]
      linarith [mul_le_mul_of_nonneg_left hyz2 h1σ, p1]
    calc ‖((Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection) z‖
        = ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection
            ((Submodule.span 𝕜 (Set.range u)).starProjection z)‖ := rfl
      _ ≤ Real.sqrt ((1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ ^ 2) := by
          rw [← Real.sqrt_sq (norm_nonneg _)]
          exact Real.sqrt_le_sqrt h2
      _ = Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ := by
          rw [Real.sqrt_mul h1σ, Real.sqrt_sq (norm_nonneg z)]
  · -- lower bound: the minimizing singular vector attains the angle.
    obtain ⟨y₀, hy₀n, hy₀⟩ := exists_norm_apply_eq_singularValues_last (overlapOp hw hu)
      finrank_euclideanSpace_fin hd
    have hx₀U : familyIsometry hu y₀ ∈ Submodule.span 𝕜 (Set.range u) :=
      familyIsometry_mem_span hu y₀
    have hx₀n : ‖familyIsometry hu y₀‖ = 1 := by
      rw [(familyIsometry hu).norm_map]; exact hy₀n
    have hPx₀ : (Submodule.span 𝕜 (Set.range u)).starProjection (familyIsometry hu y₀)
        = familyIsometry hu y₀ := Submodule.starProjection_eq_self_iff.mpr hx₀U
    have hval : ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (familyIsometry hu y₀)‖ ^ 2
        = 1 - cosPrincipalAngles hw hu (d - 1) ^ 2 := by
      rw [norm_sq_orthogonal_starProjection_familyIsometry hu hw y₀, hy₀n, hy₀,
        cosPrincipalAngles_eq, one_pow]
    calc Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2)
        = ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (familyIsometry hu y₀)‖ := by
          rw [← hval, Real.sqrt_sq (norm_nonneg _)]
      _ = ‖((Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection) (familyIsometry hu y₀)‖ := by
          rw [ContinuousLinearMap.comp_apply, hPx₀]
      _ ≤ ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection‖ * ‖familyIsometry hu y₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hx₀n, mul_one]

/-! ### The cos Θ singular-value dictionary (plan step OP3.A)

The singular values of `P_V ∘ P_U` are exactly the principal-angle cosines.
This upgrades the operator-norm/largest-angle identification
`norm_orthogonal_starProjection_comp_starProjection` to *all* singular values,
hence to every unitarily invariant norm.  The proof factors
`P_V ∘ P_U = ι_v ∘ overlapOp ∘ ι_u⋆` through the coordinate isometries, strips
the left isometry via `singularValues_eq_of_gram_eq`, and strips the right
`ι_u⋆` via the coisometry padding lemma `singularValues_comp_adjoint_familyIsometry`. -/

/-- The `i`-th coordinate of `ι_u⋆ x` is `⟪uᵢ, x⟫`. -/
theorem familyIsometry_adjoint_coord {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (x : E) (i : Fin d) :
    (familyIsometry hu).toLinearMap.adjoint x i = ⟪u i, x⟫_𝕜 := by
  have h1 : (familyIsometry hu).toLinearMap.adjoint x i
      = ⟪(EuclideanSpace.single i (1 : 𝕜)), (familyIsometry hu).toLinearMap.adjoint x⟫_𝕜 := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [h1, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap, familyIsometry_single]

/-- `P_{span u} = ι_u ∘ ι_u⋆`: the orthogonal projection onto `span u`
expressed through the coordinate isometry. -/
theorem starProjection_span_range_eq_comp {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (x : E) :
    (Submodule.span 𝕜 (Set.range u)).starProjection x
      = familyIsometry hu ((familyIsometry hu).toLinearMap.adjoint x) := by
  rw [familyIsometry_apply]
  have hsp := Orthonormal.starProjection_span_image_apply hu Finset.univ x
  rw [Finset.coe_univ, Set.image_univ] at hsp
  rw [hsp]
  exact Finset.sum_congr rfl fun i _ => by rw [familyIsometry_adjoint_coord]

/-- **The cos Θ dictionary.**  The singular values of `P_V ∘ P_U` are the
cosines of the principal angles between `span u` and `span v`:
`σ(P_V ∘ P_U) = cosPrincipalAngles hv hu`. -/
theorem singularValues_starProjection_comp_starProjection {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E)
        : E →ₗ[𝕜] E).singularValues
      = cosPrincipalAngles hv hu := by
  set M : E →ₗ[𝕜] E := (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
    (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) with hMdef
  set Y : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
    overlapOp hv hu ∘ₗ (familyIsometry hu).toLinearMap.adjoint with hYdef
  -- `ι_v⋆ ∘ ι_v = 1`.
  have hiso : (familyIsometry hv).toLinearMap.adjoint ∘ₗ (familyIsometry hv).toLinearMap
      = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact ext_inner_right 𝕜 fun z => by
      rw [LinearMap.adjoint_inner_left]; exact (familyIsometry hv).inner_map_map y z
  -- `M = ι_v ∘ Y`.
  have hM : M = (familyIsometry hv).toLinearMap ∘ₗ Y := by
    refine LinearMap.ext fun x => ?_
    simp only [hMdef, hYdef, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_coe,
      Function.comp_apply, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
    rw [starProjection_span_range_eq_comp hv, starProjection_span_range_eq_comp hu,
      overlapOp_apply]
  -- Strip the left isometry: `gram M = gram Y`.
  have hgram : M.adjoint ∘ₗ M = Y.adjoint ∘ₗ Y := by
    rw [hM, LinearMap.adjoint_comp]
    rw [show (LinearMap.adjoint Y ∘ₗ LinearMap.adjoint (familyIsometry hv).toLinearMap)
          ∘ₗ ((familyIsometry hv).toLinearMap ∘ₗ Y)
        = LinearMap.adjoint Y ∘ₗ ((familyIsometry hv).toLinearMap.adjoint
          ∘ₗ (familyIsometry hv).toLinearMap) ∘ₗ Y from by
      simp only [LinearMap.comp_assoc], hiso, LinearMap.id_comp]
  -- Strip the right isometry (OP3.0) and read off the definition.
  rw [singularValues_eq_of_gram_eq hgram, hYdef,
    singularValues_comp_adjoint_familyIsometry hu (overlapOp hv hu)]
  rfl

end ForMathlib
