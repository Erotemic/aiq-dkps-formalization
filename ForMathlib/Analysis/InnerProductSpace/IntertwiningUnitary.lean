/-
Staged for Mathlib: a new `Mathlib/Analysis/InnerProductSpace/IntertwiningUnitary.lean`.

Milestone 2 of the operator polar decomposition project — COMPLETE (sorry-free, axiom-clean:
`propext, Classical.choice, Quot.sound`). Tickets PD-13..PD-17.
-/

import ForMathlib.Analysis.InnerProductSpace.PolarDecomposition
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # The canonical intertwining (matching) unitary (Milestone 2)

Given two complete orthogonal families of projections `{Pⱼ}`, `{P'ⱼ}` on a finite-dimensional inner
product space, with the non-degeneracy hypothesis "`Pⱼ x ≠ 0 ⟹ P'ⱼ Pⱼ x ≠ 0`", Davis constructs the
canonical unitary
`U Pⱼ = (P'ⱼ Pⱼ P'ⱼ)^{-1/2} P'ⱼ Pⱼ = P'ⱼ (Pⱼ P'ⱼ Pⱼ)^{-1/2} Pⱼ`,  with  `U Pⱼ = P'ⱼ U`,
the polar factor of `P'ⱼ Pⱼ` on each block. It measures the rotation of the spectral resolution.

Here the unitary is assembled as `U = ∑ⱼ Uⱼ ∘ₗ Pⱼ` with `Uⱼ = polarFactor (P'ⱼ ∘ₗ Pⱼ)` the polar
factor of the `j`-th block map: under non-degeneracy, `ker (P'ⱼ Pⱼ) = ker Pⱼ`, so `Uⱼ` is isometric
on `range Pⱼ` and carries it into `range P'ⱼ`; since the `range P'ⱼ` are pairwise orthogonal and the
`Pⱼ` resolve the identity, `U` is isometric, hence unitary. The block polar factors
`range Pⱼ ≃ₗᵢ range P'ⱼ` are recovered from `U` by restriction (surjectivity comes from the
intertwining relation `U Pⱼ = P'ⱼ U`, with no dimension count).

Source: **Davis (1963)**, "The Rotation of Eigenvectors by a Perturbation", §2, lines 217–312
(`ForMathlib/prose/non-distributable/Davis-1963-...tex`); digest §2. This unblocks Davis Result B
(BL3/BL4) in `.mathlib-quality/decomposition-B.md`.

Deferred (source Davis 1958 §7 unavailable, off critical path): the minimality theorems 2.1/2.3.
-/

namespace ForMathlib

open scoped InnerProductSpace
open LinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}

/-! ### Spectral projections (prerequisite — API gap I.5, ticket PD-13) -/

/-- Orthogonal projection onto the span of a subset `S` of an orthonormal basis; the building block
for the spectral projections of a symmetric operator. -/
noncomputable def spectralProjection (b : OrthonormalBasis (Fin n) 𝕜 E) (S : Finset (Fin n)) :
    E →ₗ[𝕜] E :=
  ∑ i ∈ S, (InnerProductSpace.rankOne 𝕜 (b i) (b i)).toLinearMap

omit [FiniteDimensional 𝕜 E] in
theorem spectralProjection_apply (b : OrthonormalBasis (Fin n) 𝕜 E) (S : Finset (Fin n))
    (y : E) : spectralProjection b S y = ∑ i ∈ S, ⟪b i, y⟫_𝕜 • b i := by
  unfold spectralProjection
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by simp [InnerProductSpace.rankOne_apply]

omit [FiniteDimensional 𝕜 E] in
theorem spectralProjection_singleton_apply (b : OrthonormalBasis (Fin n) 𝕜 E) (i : Fin n)
    (y : E) : spectralProjection b {i} y = ⟪b i, y⟫_𝕜 • b i := by
  rw [spectralProjection_apply, Finset.sum_singleton]

omit [FiniteDimensional 𝕜 E] in
theorem spectralProjection_apply_basis (b : OrthonormalBasis (Fin n) 𝕜 E) (S : Finset (Fin n))
    (k : Fin n) : spectralProjection b S (b k) = if k ∈ S then b k else 0 := by
  rw [spectralProjection_apply]
  have hterm : ∀ i ∈ S, ⟪b i, b k⟫_𝕜 • b i = if i = k then b k else 0 := fun i _ => by
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [orthonormal_iff_ite.mp b.orthonormal i k, hik]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S k fun _ => b k]

omit [FiniteDimensional 𝕜 E] in
/-- Spectral projections multiply by intersecting their index sets. -/
theorem spectralProjection_comp (b : OrthonormalBasis (Fin n) 𝕜 E) (S T : Finset (Fin n)) :
    spectralProjection b S ∘ₗ spectralProjection b T = spectralProjection b (S ∩ T) := by
  apply b.toBasis.ext
  intro k
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, spectralProjection_apply_basis]
  by_cases hT : k ∈ T <;> by_cases hS : k ∈ S <;>
    simp [hT, hS, spectralProjection_apply_basis, Finset.mem_inter]

omit [FiniteDimensional 𝕜 E] in
/-- A spectral projection is positive (in particular symmetric). -/
theorem isPositive_spectralProjection (b : OrthonormalBasis (Fin n) 𝕜 E) (S : Finset (Fin n)) :
    (spectralProjection b S).IsPositive := by
  unfold spectralProjection
  exact isPositive_sum _ fun i _ => (InnerProductSpace.isPositive_rankOne_self _).toLinearMap

/-- A spectral projection is a projection (`IsStarProjection`). -/
theorem isStarProjection_spectralProjection (b : OrthonormalBasis (Fin n) 𝕜 E)
    (S : Finset (Fin n)) : IsStarProjection (spectralProjection b S) :=
  isStarProjection_iff'.mpr
    ⟨by
      rw [Module.End.mul_eq_comp]
      simpa [Finset.inter_self] using spectralProjection_comp b S S,
      by rw [LinearMap.star_eq_adjoint, (isPositive_spectralProjection b S).adjoint_eq]⟩

omit [FiniteDimensional 𝕜 E] in
/-- Spectral projections onto disjoint index sets are orthogonal. -/
theorem spectralProjection_comp_of_disjoint (b : OrthonormalBasis (Fin n) 𝕜 E)
    {S T : Finset (Fin n)} (h : Disjoint S T) :
    spectralProjection b S ∘ₗ spectralProjection b T = 0 := by
  rw [spectralProjection_comp, Finset.disjoint_iff_inter_eq_empty.mp h]
  simp [spectralProjection]

omit [FiniteDimensional 𝕜 E] in
/-- The spectral projections over a partition of `Fin n` sum to `1`. -/
theorem spectralProjection_univ (b : OrthonormalBasis (Fin n) 𝕜 E) :
    spectralProjection b Finset.univ = 1 := by
  apply b.toBasis.ext
  intro k
  simp [spectralProjection_apply_basis]

/-! ### Complete orthogonal projection families -/

/-- A **complete orthogonal family** of `m` projections on `E`: pairwise-orthogonal projections
summing to `1`. -/
structure OrthoProjFamily (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (m : ℕ) where
  /-- The `j`-th projection. -/
  proj : Fin m → (E →ₗ[𝕜] E)
  /-- Each `proj j` is an orthogonal projection. -/
  isStarProjection' : ∀ j, IsStarProjection (proj j)
  /-- Distinct projections are orthogonal. -/
  orthogonal' : ∀ j k, j ≠ k → proj j ∘ₗ proj k = 0
  /-- The family is complete: it sums to the identity. -/
  complete' : ∑ j, proj j = 1

variable {m : ℕ}

/-- The complete orthogonal family of rank-one spectral projections attached to an orthonormal
basis: `proj i` is the orthogonal projection onto `span (b i)`. -/
noncomputable def OrthoProjFamily.ofOrthonormalBasis (b : OrthonormalBasis (Fin n) 𝕜 E) :
    OrthoProjFamily 𝕜 E n where
  proj i := spectralProjection b {i}
  isStarProjection' i := isStarProjection_spectralProjection b {i}
  orthogonal' _ _ hij :=
    spectralProjection_comp_of_disjoint b (Finset.disjoint_singleton.mpr hij)
  complete' := by
    rw [← spectralProjection_univ b]
    unfold spectralProjection
    exact Finset.sum_congr rfl fun i _ => Finset.sum_singleton _ _

@[simp] theorem OrthoProjFamily.ofOrthonormalBasis_proj (b : OrthonormalBasis (Fin n) 𝕜 E)
    (i : Fin n) :
    (OrthoProjFamily.ofOrthonormalBasis b).proj i = spectralProjection b {i} :=
  rfl

namespace OrthoProjFamily

/-- **Non-degeneracy** (Davis's hypothesis): no nonzero vector in `range (P j)` is annihilated by
`P' j`. Equivalently `P'ⱼ Pⱼ` is injective on `range Pⱼ`. -/
def NonDegenerate (P P' : OrthoProjFamily 𝕜 E m) : Prop :=
  ∀ j, ∀ x, P.proj j x = x → x ≠ 0 → P'.proj j x ≠ 0

variable {P P' : OrthoProjFamily 𝕜 E m}

theorem isStarProjection (P : OrthoProjFamily 𝕜 E m) (j : Fin m) :
    IsStarProjection (P.proj j) :=
  P.isStarProjection' j

theorem orthogonal (P : OrthoProjFamily 𝕜 E m) {j k : Fin m} (h : j ≠ k) :
    P.proj j ∘ₗ P.proj k = 0 :=
  P.orthogonal' j k h

theorem proj_comp_self (P : OrthoProjFamily 𝕜 E m) (j : Fin m) :
    P.proj j ∘ₗ P.proj j = P.proj j :=
  (P.isStarProjection j).isIdempotentElem

theorem adjoint_proj (P : OrthoProjFamily 𝕜 E m) (j : Fin m) :
    (P.proj j).adjoint = P.proj j := by
  rw [← LinearMap.star_eq_adjoint]
  exact (P.isStarProjection j).isSelfAdjoint

theorem isSymmetric_proj (P : OrthoProjFamily 𝕜 E m) (j : Fin m) :
    (P.proj j).IsSymmetric := by
  intro x y
  conv_lhs => rw [← P.adjoint_proj j]
  rw [LinearMap.adjoint_inner_left]

theorem proj_apply_of_mem_range {j : Fin m} {x : E} (hx : x ∈ range (P.proj j)) :
    P.proj j x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact congrArg (fun f : E →ₗ[𝕜] E => f y) (P.proj_comp_self j)

theorem proj_apply_of_mem_range_of_ne {j k : Fin m} (h : j ≠ k) {x : E}
    (hx : x ∈ range (P.proj k)) : P.proj j x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact congrArg (fun f : E →ₗ[𝕜] E => f y) (P.orthogonal h)

theorem sum_proj_apply (P : OrthoProjFamily 𝕜 E m) (x : E) : ∑ j, P.proj j x = x := by
  have h := congrArg (fun f : E →ₗ[𝕜] E => f x) P.complete'
  simpa using h

/-- Vectors in the ranges of distinct projections of the family are orthogonal. -/
theorem inner_eq_zero_of_ne {j k : Fin m} (h : j ≠ k) {x y : E}
    (hx : x ∈ range (P.proj j)) (hy : y ∈ range (P.proj k)) : ⟪x, y⟫_𝕜 = 0 := by
  rw [← proj_apply_of_mem_range hx, P.isSymmetric_proj j,
    proj_apply_of_mem_range_of_ne h hy, inner_zero_right]

theorem ker_proj (P : OrthoProjFamily 𝕜 E m) (j : Fin m) :
    ker (P.proj j) = (range (P.proj j))ᗮ := by
  rw [LinearMap.orthogonal_range, adjoint_proj]

omit [FiniteDimensional 𝕜 E] in
/-- Pythagoras for a pairwise-orthogonal finite family of vectors. -/
private theorem norm_sq_sum_of_pairwise_inner_eq_zero {v : Fin m → E}
    (h : ∀ j k, j ≠ k → ⟪v j, v k⟫_𝕜 = 0) :
    ‖∑ j, v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
  have hin : ⟪∑ j, v j, ∑ j, v j⟫_𝕜 = ∑ j, ⟪v j, v j⟫_𝕜 := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    exact Finset.sum_eq_single j (fun k _ hk => h j k (Ne.symm hk))
      (fun hj => absurd (Finset.mem_univ j) hj)
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hin, map_sum]
  exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_re_inner (𝕜 := 𝕜) _).symm

/-! ### The block polar factors (ticket PD-14) -/

/-- **Non-degeneracy transfers the kernel (PD-14):** under Davis's hypothesis, composing with
`P'ⱼ` kills nothing new: `ker (P'ⱼ Pⱼ) = ker Pⱼ`. Davis §2 line 224. -/
theorem ker_comp_of_nonDegenerate (hnd : P.NonDegenerate P') (j : Fin m) :
    ker (P'.proj j ∘ₗ P.proj j) = ker (P.proj j) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [LinearMap.mem_ker] at hx ⊢
    by_contra hne
    exact hnd j (P.proj j x)
      (congrArg (fun f : E →ₗ[𝕜] E => f x) (P.proj_comp_self j)) hne hx
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply, hx, map_zero]

/-- **Block invertibility (PD-14):** under non-degeneracy, `P'ⱼ Pⱼ` is injective on `range Pⱼ`.
Davis §2 line 224. -/
theorem injOn_of_nonDegenerate (hnd : P.NonDegenerate P') (j : Fin m) :
    Set.InjOn (P'.proj j ∘ₗ P.proj j) (range (P.proj j)) := by
  intro x hx y hy hxy
  have hker : x - y ∈ ker (P'.proj j ∘ₗ P.proj j) := by
    rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  rw [ker_comp_of_nonDegenerate hnd j, ker_proj] at hker
  have hmem : x - y ∈ range (P.proj j) := Submodule.sub_mem _ hx hy
  exact sub_eq_zero.mp <| Submodule.disjoint_def.mp
    (Submodule.orthogonal_disjoint (range (P.proj j))) _ hmem hker

/-- The polar factor of the `j`-th block map is isometric on `range Pⱼ`. -/
private theorem norm_blockFactor_apply_proj (hnd : P.NonDegenerate P') (j : Fin m) (x : E) :
    ‖polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x)‖ = ‖P.proj j x‖ :=
  norm_polarFactor_apply_of_mem <| by
    rw [ker_comp_of_nonDegenerate hnd j, ker_proj, Submodule.orthogonal_orthogonal]
    exact LinearMap.mem_range_self _ x

/-- The polar factor of the `j`-th block map lands in `range P'ⱼ`. -/
private theorem blockFactor_apply_mem_range (P P' : OrthoProjFamily 𝕜 E m) (j : Fin m) (y : E) :
    polarFactor (P'.proj j ∘ₗ P.proj j) y ∈ range (P'.proj j) := by
  have h : polarFactor (P'.proj j ∘ₗ P.proj j) y
      ∈ range (polarFactor (P'.proj j ∘ₗ P.proj j)) := LinearMap.mem_range_self _ y
  rw [range_polarFactor] at h
  exact LinearMap.range_comp_le_range _ _ h

/-! ### The intertwining unitary (ticket PD-16) -/

private theorem norm_sum_blockFactor (hnd : P.NonDegenerate P') (x : E) :
    ‖∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x)‖ = ‖x‖ := by
  have hsq : ‖∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_sum_of_pairwise_inner_eq_zero fun j k hjk =>
      inner_eq_zero_of_ne (P := P') hjk (blockFactor_apply_mem_range P P' j _)
        (blockFactor_apply_mem_range P P' k _)]
    calc ∑ j, ‖polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x)‖ ^ 2
        = ∑ j, ‖P.proj j x‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [norm_blockFactor_apply_proj hnd j x]
      _ = ‖∑ j, P.proj j x‖ ^ 2 :=
          (norm_sq_sum_of_pairwise_inner_eq_zero fun j k hjk =>
            inner_eq_zero_of_ne (P := P) hjk (LinearMap.mem_range_self _ x)
              (LinearMap.mem_range_self _ x)).symm
      _ = ‖x‖ ^ 2 := by rw [sum_proj_apply]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg x), hsq]

/-- **The canonical intertwining unitary** `U({Pⱼ},{P'ⱼ})`, assembled from the block polar factors:
`U = ∑ⱼ Uⱼ ∘ₗ Pⱼ` with `Uⱼ` the polar factor of `P'ⱼ Pⱼ`, so `U Pⱼ = (P'ⱼ Pⱼ P'ⱼ)^{-1/2} P'ⱼ Pⱼ`.
Davis §2, lines 217–229. -/
noncomputable def intertwiningUnitary (hnd : P.NonDegenerate P') : E ≃ₗᵢ[𝕜] E :=
  have hnorm : ∀ x : E,
      ‖(∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) ∘ₗ P.proj j : E →ₗ[𝕜] E) x‖ = ‖x‖ := fun x => by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply]
    exact norm_sum_blockFactor hnd x
  have hinj : Function.Injective
      (∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) ∘ₗ P.proj j : E →ₗ[𝕜] E) := fun x y hxy => by
    have h0 : ‖x - y‖ = 0 := by rw [← hnorm (x - y), map_sub, hxy, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  { LinearEquiv.ofBijective
      (∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) ∘ₗ P.proj j : E →ₗ[𝕜] E)
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩ with
    norm_map' := hnorm }

@[simp] theorem coe_toLinearMap_intertwiningUnitary_apply (hnd : P.NonDegenerate P') (y : E) :
    (intertwiningUnitary hnd : E →ₗ[𝕜] E) y = intertwiningUnitary hnd y :=
  rfl

theorem intertwiningUnitary_apply (hnd : P.NonDegenerate P') (x : E) :
    intertwiningUnitary hnd x = ∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x) := by
  have h : intertwiningUnitary hnd x
      = (∑ j, polarFactor (P'.proj j ∘ₗ P.proj j) ∘ₗ P.proj j : E →ₗ[𝕜] E) x := rfl
  rw [h, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]

/-- **The intertwining property** `U Pⱼ = P'ⱼ U`. Davis §2 line 229. -/
theorem intertwiningUnitary_comp_proj (hnd : P.NonDegenerate P') (j : Fin m) :
    ((intertwiningUnitary hnd : E →ₗ[𝕜] E)) ∘ₗ P.proj j
      = P'.proj j ∘ₗ (intertwiningUnitary hnd : E →ₗ[𝕜] E) := by
  have hL : ∀ x : E, ∑ k, polarFactor (P'.proj k ∘ₗ P.proj k) (P.proj k (P.proj j x))
      = polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x) := fun x => by
    refine (Finset.sum_eq_single j (fun k _ hkj => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
    · rw [show P.proj k (P.proj j x) = 0 from
        congrArg (fun f : E →ₗ[𝕜] E => f x) (P.orthogonal hkj), map_zero]
    · rw [show P.proj j (P.proj j x) = P.proj j x from
        congrArg (fun f : E →ₗ[𝕜] E => f x) (P.proj_comp_self j)]
  have hR : ∀ x : E, ∑ k, P'.proj j (polarFactor (P'.proj k ∘ₗ P.proj k) (P.proj k x))
      = polarFactor (P'.proj j ∘ₗ P.proj j) (P.proj j x) := fun x => by
    refine (Finset.sum_eq_single j (fun k _ hkj => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
    · exact proj_apply_of_mem_range_of_ne (Ne.symm hkj) (blockFactor_apply_mem_range P P' k _)
    · exact proj_apply_of_mem_range (blockFactor_apply_mem_range P P' j _)
  ext x
  simp only [LinearMap.comp_apply, coe_toLinearMap_intertwiningUnitary_apply]
  rw [intertwiningUnitary_apply, intertwiningUnitary_apply, map_sum, hL x, hR x]

/-- `U` maps `range Pⱼ` into `range P'ⱼ` (it acts there as the block polar factor). -/
theorem intertwiningUnitary_mapsTo (hnd : P.NonDegenerate P') (j : Fin m) {x : E}
    (hx : x ∈ range (P.proj j)) :
    intertwiningUnitary hnd x ∈ range (P'.proj j) := by
  have h := congrArg (fun f : E →ₗ[𝕜] E => f x) (intertwiningUnitary_comp_proj hnd j)
  simp only [LinearMap.comp_apply] at h
  rw [proj_apply_of_mem_range hx] at h
  exact ⟨intertwiningUnitary hnd x, h.symm⟩

/-! ### The block polar factor as a unitary between the ranges (ticket PD-15) -/

/-- **Block polar factor (PD-15):** the polar factor of `P'ⱼ Pⱼ` is a unitary
`range Pⱼ ≃ₗᵢ range P'ⱼ` — the restriction of the intertwining unitary to the `j`-th block
(surjectivity onto `range P'ⱼ` follows from the intertwining relation). Davis §2 line 221. -/
noncomputable def blockPolar (hnd : P.NonDegenerate P') (j : Fin m) :
    ↥(range (P.proj j)) ≃ₗᵢ[𝕜] ↥(range (P'.proj j)) :=
  have hinj : Function.Injective
      (((intertwiningUnitary hnd : E →ₗ[𝕜] E)).restrict
        (p := range (P.proj j)) (q := range (P'.proj j))
        fun x hx => intertwiningUnitary_mapsTo hnd j hx) := fun y z hyz => by
    have h0 := congrArg Subtype.val hyz
    simp only [LinearMap.restrict_apply, coe_toLinearMap_intertwiningUnitary_apply] at h0
    exact Subtype.ext ((intertwiningUnitary hnd).injective h0)
  have hsurj : Function.Surjective
      (((intertwiningUnitary hnd : E →ₗ[𝕜] E)).restrict
        (p := range (P.proj j)) (q := range (P'.proj j))
        fun x hx => intertwiningUnitary_mapsTo hnd j hx) := by
    rintro ⟨y, hy⟩
    refine ⟨⟨P.proj j ((intertwiningUnitary hnd).symm y), LinearMap.mem_range_self _ _⟩, ?_⟩
    apply Subtype.ext
    show ((intertwiningUnitary hnd : E →ₗ[𝕜] E))
      (P.proj j ((intertwiningUnitary hnd).symm y)) = y
    have h := congrArg (fun f : E →ₗ[𝕜] E => f ((intertwiningUnitary hnd).symm y))
      (intertwiningUnitary_comp_proj hnd j)
    simp only [LinearMap.comp_apply, coe_toLinearMap_intertwiningUnitary_apply] at h
    rw [coe_toLinearMap_intertwiningUnitary_apply, h,
      (intertwiningUnitary hnd).apply_symm_apply]
    exact proj_apply_of_mem_range hy
  { LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩ with
    norm_map' := fun v => by
      show ‖((intertwiningUnitary hnd : E →ₗ[𝕜] E)) ↑v‖ = ‖(↑v : E)‖
      exact (intertwiningUnitary hnd).norm_map ↑v }

/-! ### Rotation-angle interpretation (ticket PD-17) — needed by Davis Result B (BL4)

`θᵢ = arccos ⟨U xᵢ, xᵢ⟩` for `xᵢ` an orthonormal basis adapted to `{Pⱼ}`; the "sum of squared
sines" `∑ᵢ (1 - ‖⟨U xᵢ, xᵢ⟩‖²)` is the Frobenius off-diagonal size `‖𝒞⊥ U‖²_F`. Stated here at the
inner-product level (the pinching/Frobenius identification joins the parent Result-B infrastructure
in Milestone 3). Davis §2, lines 265–312. -/

/-- The squared sine of the `i`-th rotation angle, `sin²θᵢ = 1 - ‖⟨U xᵢ, xᵢ⟩‖²`. -/
noncomputable def sqSinAngle (hnd : P.NonDegenerate P') (b : OrthonormalBasis (Fin n) 𝕜 E)
    (i : Fin n) : ℝ :=
  1 - ‖⟪b i, intertwiningUnitary hnd (b i)⟫_𝕜‖ ^ 2

/-- **Angle interpretation (PD-17):** the total squared rotation `∑ᵢ sin²θᵢ` equals
`(finrank) - ∑ᵢ ‖⟨U xᵢ, xᵢ⟩‖²`, the pinch-off-diagonal Frobenius size of `U`. Davis §2 line 276.
(The `‖𝒞⊥ U‖²_F` identification is completed in Milestone 3 against the parent's Frobenius setup.) -/
theorem sum_sqSinAngle (hnd : P.NonDegenerate P') (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ i, sqSinAngle hnd b i
      = (n : ℝ) - ∑ i, ‖⟪b i, intertwiningUnitary hnd (b i)⟫_𝕜‖ ^ 2 := by
  simp [sqSinAngle, Finset.sum_sub_distrib]

end OrthoProjFamily

end ForMathlib
