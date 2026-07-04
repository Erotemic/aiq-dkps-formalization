# Ticket Board — Davis eigenvalue-change bound (Result A) + sharper rotation (Result B)

## Summary
- **Result A (Davis Thm 4.1, eigenvalue-change lower bound) is COMPLETE.** All of L1–L5
  proven, sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`); `lake build
  ForMathlib` green. File: `ForMathlib/Analysis/InnerProductSpace/EigenvalueChange.lean`.
- Done: T001 (L1), T002 (L2), T003 (L4), T004 (L3), T005 (L5), CLEANUP-1 (incremental
  mathlib-style + docs refreshed). Open: T006 (Result B decomposition — planning).
- Full sketches + verbatim source quotes: `.mathlib-quality/decomposition.md`.

### [T004] L3 — Birkhoff bridge  ✅ DONE
- `diag_mem_convexHull_perm_spectrum`: doubly-stochastic `schurWeight` matrix → Birkhoff
  (`doublyStochastic_eq_convexHull_permMatrix`) → `permMatrix_mulVec`; transferred to the
  EuclideanSpace `permEV` orbit via `WithLp.linearEquiv` + `LinearMap.image_convexHull`.

### [T005] L5 — operator wrapper  ✅ DONE
- `sum_sq_eigenvalues_sub_ge`: Davis Thm 4.1, operator form; `‖𝒞⊥H‖²` written in Davis's own
  `∑λ'² − ∑(diag S)²` form. Wraps L3+L4; `re⟪vᵢ,S vᵢ⟫ − re⟪vᵢ,(S−T)vᵢ⟫ = λᵢ` recovers `λ`.

### [CLEANUP-1] ✅ DONE (incremental)

## Tickets

### [T001] L1 — combinatorial minimum displacement  ✅ DONE
- `two_mul_sq_le_sum_sq_sub_perm` (EigenvalueChange.lean) — proven, axiom-clean.

### [T002] L2 — geometric core (Davis eq. 4.2)  ✅ DONE
- Restated over `EuclideanSpace ℝ (Fin n)` with `permEV` coordinate-permutation orbit;
  `sqrt_two_inv_mul_norm_le_inner_of_mem_convexHull_perm` proven (direct vertex extraction via
  `mem_convexHull_iff_exists_fintype` + `norm_sum_le`), axiom-clean. Helpers: `permEV`,
  `permEV_apply`, `norm_permEV`, `norm_sub_permEV_sq`, `two_mul_inner_sub_permEV`.

### [T003] L4 — vector-level eigenvalue-change bound  ✅ DONE
- Restated over EuclideanSpace; `sum_sq_sub_pinch_ge` proven from L2 + Cauchy–Schwarz
  (`abs_real_inner_le_norm`) + `norm_add_sq_real`/`norm_sub_sq_real`, axiom-clean.

### [T002-old] (superseded)
- **Status**: done · **File**: EigenvalueChange.lean:~91 · **Depends on**: T001 · **Type**: lemma
- **Decl**: `sqrt_two_inv_mul_norm_le_inner_of_mem_convexHull_perm`
- **Sketch**: two routes — (a) `ConvexOn.exists_ge_of_mem_convexHull` on `g x = γ‖w−x‖ − √2⟪w−x,w⟫`
  (needs convexity of the Euclidean norm — cleanest over `EuclideanSpace ℝ (Fin n)`, so consider
  restating L2/L4 there); (b) direct: extract `c = ∑ a_π (w∘π)` from `convexHull` membership, use
  `⟪w−c,w⟫ = ∑ a_π ½‖w−w∘π‖²`, `‖w−w∘π‖ ≥ √2γ` (L1), and Minkowski `‖∑a_π(w−w∘π)‖ ≤ ∑a_π‖w−w∘π‖`.
- **Modelling note**: the sqrt/norm friction over `Fin n → ℝ` is the reason to move L2/L4 to
  `EuclideanSpace ℝ (Fin n)` (get `convexOn_norm`, `norm_sub`, `⟪·,·⟫_ℝ`, triangle for free). The
  permutation orbit element is `(fun i => w (π i) : EuclideanSpace ℝ (Fin n))`.

### [T003] L4 — vector-level eigenvalue-change bound (Davis Part 2)
- **Status**: open · **File**: EigenvalueChange.lean:~106 · **Depends on**: T002 · **Type**: lemma
- **Decl**: `sum_sq_sub_pinch_ge`
- **Sketch**: pure algebra from L2. `Δ = w − c + dH`; `‖Δ‖² − ‖dH‖² = ‖w−c‖² − 2⟪c−w,dH⟫`;
  Cauchy–Schwarz `⟪c−w,dH⟫ ≤ ‖c−w‖‖dH‖ ≤ ‖w−c‖·γ/√2`; add `‖w‖²−‖c‖²`; use
  `‖w−c‖²+‖w‖²−‖c‖² = 2⟪w−c,w⟫` and L2. ~50 LOC.

### [T004] L3 — Birkhoff bridge (diag ∈ convexHull of permutation orbit)
- **Status**: open · **File**: EigenvalueChange.lean:~123 · **Depends on**: none (parallel with T002/T003)
- **Decl**: `diag_mem_convexHull_perm_spectrum` · **Type**: lemma
- **Sketch**: weight `Dᵢⱼ = ‖⟪v'ⱼ, vᵢ⟫‖²` is doubly stochastic (`SchurHorn.schurWeight_row/col_sum`);
  `doublyStochastic_eq_convexHull_permMatrix` (Birkhoff) + `permMatrix_mulVec` give
  `D·λ' ∈ convexHull {λ'∘π}`; `re⟪vᵢ, S vᵢ⟫ = (D·λ')ᵢ` is
  `SchurHorn.re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul`. Main friction: assembling the
  `Matrix`/`mulVec` form and its convexHull image. ~80 LOC.

### [CLEANUP-1] /cleanup on EigenvalueChange.lean
- **Status**: open · **Depends on**: T002, T003, T004 · **Type**: cleanup

### [T005] L5 — operator wrapper (eigenvalue-change, operator form)
- **Status**: open · **File**: EigenvalueChange.lean:~135 · **Depends on**: T003, T004, CLEANUP-1
- **Decl**: `sum_sq_eigenvalues_sub_ge` · **Type**: theorem (Result A milestone)
- **Sketch**: instantiate L4 with `w = hS.eigenvalues`, `c i = re⟪vᵢ, S vᵢ⟫`, `dH i = re⟪vᵢ,(S−T)vᵢ⟫`;
  `c − dH = hT.eigenvalues` (since `re⟪vᵢ,T vᵢ⟫ = λᵢ`); `convexHull` membership from T004;
  identify `∑‖⟪vᵢ,(S−T)vᵢ⟫‖²`, `∑‖(S−T)vᵢ‖²` with `∑dH²`, `‖H‖²_F` (Parseval, `sum_sq_norm_inner`).

### [T006] Result B — decompose sharper total-rotation (matching unitary)  ✅ DONE
- Decomposition written to `.mathlib-quality/decomposition-B.md` (Davis Thm 3.2, transcribed
  from §3 + §2). Surfaced the gating API gap (BL3, below).

## Result B formalization tickets (all BLOCKED on BL3)

### [BL1] cross-term identity `⟨(A+𝒞H−λ'ᵢ)²xᵢ,xᵢ⟩ = (λᵢ−λ'ᵢ)² + ⟨(𝒞⊥H)²xᵢ,xᵢ⟩`
- **Status**: open · feasible from `Spectrum.lean` cross-term + pinching split.
### [BL2] Rayleigh lower bound `≥ (λᵢ−λ'ᵢ)² + (γ')² sin²θᵢ`
- **Status**: blocked on BL3 (needs the angles θᵢ) · feasible otherwise (cf. CourantFischer).
### [BL3] ⚠️ **API GAP (B3) — operator polar decomposition / canonical matching unitary**
- **Status**: BLOCKED — needs user scope decision.
- **Reason**: Mathlib has NO polar decomposition and NO partial-isometry API (grep-confirmed
  2026-07-04, empty across all of Mathlib). Davis's `U` = polar factor of `P'ⱼPⱼ` on each block.
  Building `A = U|A|` (`|A| = √(A*A)` via CFC) + the intertwining unitary is a **standalone
  multi-lemma development at Mathlib-contribution scale** — recommend its own `/develop` project.
### [BL4] `‖𝒞⊥U‖²_F = ∑ᵢ sin²θᵢ` · blocked on BL3.
### [BL5] assemble eq. 3.1 (Thm 3.2) · blocked on BL1–BL4.
### [BL6] corollary `(γ')²‖𝒞⊥U‖²_F ≤ 2‖𝒞⊥H‖²_F` (combine BL5 + Result A) · blocked on BL5.

## Next
Result A (the stated target) is complete. Result B is gated on BL3 (operator polar
decomposition), now opened as its own development — see the **Polar decomposition** board
below. Result B (BL1–BL6) resumes once Milestone 3 of that board unblocks BL3/BL4.

---
---

# Ticket Board — Operator polar decomposition `A = U|A|` + intertwining unitary

> Spun off from BL3 above. Plan: `.mathlib-quality/plan.md`. Full decomposition + verbatim source
> quotes + adversarial pass: `.mathlib-quality/decomposition-polar.md`. Scope (user 2026-07-04):
> hybrid carrier (CFC-ℂ headline + LinearMap/RCLike route), full chain to Davis BL3.
> **Milestone-1 skeleton is written and `lake build` green (sorries only)** — M1 tickets are
> "fill the sorry at file:line". M2/M3 skeleton is authored as the first step of their tickets.

## Summary
- Total: 18 proof/def tickets + 7 cleanups. Open: all. In Progress/Done: 0.
- Milestone 1 (PD-01..PD-12): general polar decomposition — self-contained, lands first.
- Milestone 2 (PD-13..PD-17): intertwining unitary (Davis §2) + spectral-projection prereq.
- Milestone 3 (PD-18): wire into Davis BL3/BL4.
- Parallel capacity at peak: 3 (Sub-devs I and II are independent; III depends on both).
- **Deferred (NOT ticketed):** Davis Thm 2.1/2.3 minimality of `W` — source Davis1958 §7 unavailable,
  off the BL3 critical path. Revisit via `/expert-review` only on request.

## Milestone 1 — general polar decomposition

### [PD-01] `IsPositive.sqrt` + positivity/symmetry  ✅ DONE
- **Status**: done · **File**: PositiveSqrt.lean:33 · **Depends on**: none · **Parallel**: yes · **Type**: def + API
- Def `∑ᵢ √λᵢ • (rankOne eᵢ eᵢ)`; `sqrt_isPositive` via `isPositive_sum` + `smul_of_nonneg` +
  `isPositive_rankOne_self.toLinearMap`; `sqrt_isSymmetric` derived. Sorry-free, axiom-clean
  (`propext, Classical.choice, Quot.sound`), `lake build` green (70s). NB: `positivity` hangs on
  `0 ≤ (√λ : 𝕜)` — use `RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)`.
#### Statement
Fill the def body and the two API sorries:
```lean
noncomputable def LinearMap.IsPositive.sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : E →ₗ[𝕜] E
theorem LinearMap.IsPositive.sqrt_isPositive (hT : T.IsPositive) : hT.sqrt.IsPositive
-- sqrt_isSymmetric already reduces to sqrt_isPositive.isSymmetric
```
#### Proof sketch
1. Body: `∑ i : Fin (Module.finrank 𝕜 E), (Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : 𝕜) •
   (InnerProductSpace.rankOne 𝕜 (hT.isSymmetric.eigenvectorBasis rfl i)
   (hT.isSymmetric.eigenvectorBasis rfl i)).toLinearMap`.
2. `sqrt_isPositive`: sum of PSD rank-ones is PSD — `isPositive_sum`, `isPositive_rankOne_self`,
   `√λ ≥ 0` from `IsPositive.nonneg_eigenvalues`. (Model on `Positive.lean:544` and project
   `PosDef.lean` `PosSemidef.exists_eq_conjTranspose_mul_self`.)
#### Mathlib lemmas needed
`InnerProductSpace.rankOne`/`rankOne_apply` (LinearMap.lean:303/322), `IsSymmetric.eigenvalues`/
`eigenvectorBasis` (Spectrum.lean:279/300), `IsPositive.nonneg_eigenvalues` (Positive.lean:155),
`InnerProductSpace.isPositive_rankOne_self`, `LinearMap.isPositive_sum`, `OrthonormalBasis.sum_repr`
(PiL2.lean:492).
#### Sources
Horn–Johnson *Matrix Analysis* 2nd ed. Thm 7.2.6, p.440 (see decomposition-polar.md leaf I.1 for
the verbatim quote).
#### Generality decision
`𝕜 : RCLike` (ℝ+ℂ), `E` finite-dim; on `LinearMap.IsPositive`. Weakest setting supporting the
eigenbasis. ~40 LOC (mathlib inline analog is ~6 lines; named def + bookkeeping adds overhead).

### [PD-02] `sqrt_mul_self` + `sq_norm_sqrt_apply`  ✅ DONE
- **Status**: done · **File**: PositiveSqrt.lean · **Depends on**: PD-01 · **Parallel**: with PD-03 · **Type**: lemma
- Added helper `sqrt_apply_eigenvectorBasis` (`sqrt (bₖ) = √λₖ • bₖ`, via `LinearMap.sum_apply` +
  `Finset.sum_eq_single` + `orthonormal_iff_ite`). `sqrt_mul_self` via `(...).toBasis.ext` +
  `Real.mul_self_sqrt`; `sq_norm_sqrt_apply` via `norm_sq_eq_re_inner` + `sqrt_isSymmetric` + T-symmetry.
  Sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`), `lake build` green.
  NB: `Basis.ext` as a qualified name failed to resolve — use dot notation `b.toBasis.ext`.
#### Statement
```lean
theorem sqrt_mul_self (hT : T.IsPositive) : hT.sqrt ∘ₗ hT.sqrt = T
theorem sq_norm_sqrt_apply (hT : T.IsPositive) (x : E) : ‖hT.sqrt x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜
```
#### Proof sketch
1. `sqrt_mul_self`: `(∑√λᵢPᵢ)(∑√λⱼPⱼ) = ∑ᵢ λᵢ Pᵢ = T`; cross terms vanish by orthonormality
   (`PᵢPⱼ=δᵢⱼPᵢ`), diagonal gives `√λᵢ·√λᵢ=λᵢ` (`Real.mul_self_sqrt` on `λᵢ≥0`); `∑λᵢPᵢ = T` from
   `apply_eigenvectorBasis` + `OrthonormalBasis.sum_repr`.
2. `sq_norm_sqrt_apply`: `‖Sx‖² = re⟪Sx,Sx⟫ = re⟪S²x,x⟫ = re⟪Tx,x⟫` for `S=sqrt` symmetric, via
   `sqrt_mul_self` and `real_inner_self_eq_norm_sq` / adjoint move (`sqrt_isSymmetric`).
#### Mathlib lemmas needed
`Real.mul_self_sqrt`, `OrthonormalBasis.sum_repr`, `apply_eigenvectorBasis`, `orthonormal_iff_*`,
`real_inner_self_eq_norm_sq`, `LinearMap.IsSymmetric` (adjoint move).
#### Sources
HJ 7.2.6 (`B²=A`). #### Generality: as PD-01. ~45 LOC combined.

### [PD-03] `ker_sqrt` + `range_sqrt`  ✅ DONE
- **Status**: done · **File**: PositiveSqrt.lean · **Depends on**: PD-02 · **Type**: lemma
- `ker_sqrt` via `ker_adjoint_comp_self` + `adjoint_eq` + `sqrt_mul_self`; `range_sqrt` via
  `orthogonal_ker` (range = kerᗮ for symmetric) + `ker_sqrt`. Axiom-clean.
#### Statement
```lean
theorem ker_sqrt (hT : T.IsPositive) : ker hT.sqrt = ker T
theorem range_sqrt (hT : T.IsPositive) : range hT.sqrt = range T
```
#### Proof sketch
1. `ker_sqrt`: `sqrt T x = 0 ↔ ‖sqrt T x‖=0 ↔ re⟪Tx,x⟫=0 ↔ Tx=0` (last step: `T≥0` ⟹
   `re⟪Tx,x⟫=0 ⟹ Tx=0`); use `sq_norm_sqrt_apply` (PD-02). Alternatively via
   `LinearMap.ker_adjoint_comp_self` (Adjoint.lean:620) on `T = sqrt·sqrt`.
2. `range_sqrt`: finite-dim rank-nullity from `ker_sqrt`, plus `range T ⊆ range sqrt` (`T=sqrt·sqrt`)
   and symmetry (`range = kerᗮ`).
#### Mathlib lemmas needed
`LinearMap.ker_adjoint_comp_self` (Adjoint.lean:620), `LinearMap.orthogonal_ker` (Adjoint.lean:607),
`inner_map_self_eq_zero`-style PSD lemma, rank-nullity (`LinearMap.finrank_range_add_finrank_ker`).
#### Sources
HJ 7.2.6(c) (`range A = range B`), 7.2.7(b) (`ker`). #### Generality: as PD-01. ~30 LOC.

### [CLEANUP-PD-1] /cleanup on PositiveSqrt.lean
- **Status**: open · **Depends on**: PD-03 · **Type**: cleanup (3 tickets on file since start)

### [PD-04] `sqrt_unique` + `isUnit_sqrt_of_isUnit`  ✅ DONE
- **Status**: done · **File**: PositiveSqrt.lean · **Depends on**: PD-03 · **Type**: lemma
- `isUnit_sqrt_of_isUnit` via `isUnit_iff_ker_eq_bot` + `ker_sqrt`. `sqrt_unique` via a private
  pointwise helper `sq_root_pointwise` (S≥0, S²v=μ²v, μ≥0 ⟹ Sv=μv: case μ=0 by ‖Sv‖²=re⟪v,S²v⟫=0;
  case μ>0 by (S+μ)(Sv−μv)=0 + positivity forcing w=0), then `Basis.ext` on T's eigenbasis with
  `sqrt_apply_eigenvectorBasis`. All axiom-clean (`propext, Classical.choice, Quot.sound`).
  **Sub-dev I (PositiveSqrt.lean) is now fully sorry-free.**
#### Statement
```lean
theorem sqrt_unique (hT : T.IsPositive) (hS : S.IsPositive) (h : S ∘ₗ S = T) : S = hT.sqrt
theorem isUnit_sqrt_of_isUnit (hT : T.IsPositive) (hunit : IsUnit T) : IsUnit hT.sqrt
```
#### Proof sketch
1. `sqrt_unique`: `S,sqrt` both PSD with square `T`; `S` commutes with `T=S²`, simultaneously
   diagonalize with `T`'s eigenbasis, on each eigenspace both act as `√λ` (nonneg-root uniqueness).
2. `isUnit_sqrt_of_isUnit`: `T` unit ⟺ all `λᵢ>0` ⟺ all `√λᵢ>0` ⟺ `sqrt T` unit (its eigenvalues).
#### Mathlib lemmas needed
`IsSymmetric.orthogonalComplement_iSup_eigenspaces`-style simultaneous diagonalization,
`Real.sqrt_pos`, unit-of-positive-eigenvalues. (HJ 7.2.6(a),(b) proof pattern.)
#### Sources
HJ 7.2.6(a) uniqueness verbatim (decomposition-polar.md I.6). #### Generality: as PD-01. ~60 LOC.

### [CLEANUP-PD-2] /cleanup on PositiveSqrt.lean (final per-file)
- **Status**: open · **Depends on**: PD-04 · **Type**: cleanup

### [PD-05] `IsPartialIsometry` def + abstract API
- **Status**: open · **File**: PartialIsometry.lean:33 · **Depends on**: none · **Parallel**: yes (with PD-01) · **Type**: def + API
#### Statement
```lean
def IsPartialIsometry {R : Type*} [Monoid R] [StarMul R] (u : R) : Prop := u * star u * u = u
theorem IsPartialIsometry.isStarProjection_star_mul_self (hu : IsPartialIsometry u) : IsStarProjection (star u * u)
theorem IsPartialIsometry.star_star (hu : IsPartialIsometry u) : IsPartialIsometry (star u)
theorem IsPartialIsometry.of_star_mul_self_eq_one (h : star u * u = 1) : IsPartialIsometry u
```
#### Proof sketch
`isStarProjection_star_mul_self`: `(u⋆u)² = u⋆(uu⋆u) = u⋆u` (idempotent, from defn), `star(u⋆u)=u⋆u`.
`star_star`, `of_star_mul_self_eq_one`: star-monoid algebra (`star_star`, `star_mul`, `mul_assoc`).
#### Mathlib lemmas needed
`IsStarProjection` (StarProjection.lean:27), `isStarProjection_iff`, `star_mul`, `star_star`.
#### Sources
Conway *A Course in Functional Analysis* 2nd ed. VI.3.1–VI.3.2.
#### Generality decision
Abstract `[Monoid R] [StarMul R]` — max generality (both `→ₗ`/`→L` and any C⋆-algebra). ~25 LOC.

### [PD-06] partial-isometry operator characterization
- **Status**: open · **File**: PartialIsometry.lean:56,62 · **Depends on**: PD-05 · **Type**: lemma
#### Statement
```lean
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] E} :
    IsPartialIsometry u ↔ ∀ x ∈ (ker u)ᗮ, ‖u x‖ = ‖x‖
theorem IsPartialIsometry.star_mul_self_eq_starProjection (hu : IsPartialIsometry u) :
    star u * u = ((ker u)ᗮ).starProjection.toLinearMap
```
#### Proof sketch
`u⋆u` is a projection (PD-05); its range is `(ker u)ᗮ` (`orthogonal_ker`), so `u⋆u = starProjection
(ker u)ᗮ`; `‖ux‖²=re⟪u⋆u x,x⟫` equals `‖x‖²` exactly on `(ker u)ᗮ`.
#### Mathlib lemmas needed
`Submodule.starProjection`/`starProjection_apply` (Projection/Basic.lean:124/138),
`LinearMap.orthogonal_ker` (Adjoint.lean:607), `IsStarProjection` range facts, `star_eq_adjoint`.
#### Sources
Conway VI.3.2. #### Generality: operator instance, `𝕜 : RCLike`, finite-dim. ~55 LOC combined.

### [PD-07] partial-isometry constructor (isometry-on-a-subspace)
- **Status**: open · **File**: PartialIsometry.lean:71 · **Depends on**: PD-06 · **Type**: lemma
#### Statement
```lean
theorem isPartialIsometry_of_isometryOn {u : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    (hker : ker u = Kᗮ) (hiso : ∀ x ∈ K, ‖u x‖ = ‖x‖) : IsPartialIsometry u
```
#### Proof sketch
`(ker u)ᗮ = Kᗮᗮ = K` (finite-dim `orthogonal_orthogonal`), then apply PD-06's `iff` direction.
#### Mathlib lemmas needed
`Submodule.orthogonal_orthogonal`, PD-06 (`isPartialIsometry_iff_norm_map`).
#### Sources
Conway VI.3.9 (the workhorse for the polar factor). #### Generality: as PD-06. ~20 LOC.

### [CLEANUP-PD-3] /cleanup on PartialIsometry.lean (3 tickets + final)
- **Status**: open · **Depends on**: PD-07 · **Type**: cleanup

### [PD-08] modulus `|A|` + `abs_mul_self` + `norm_abs_apply`
- **Status**: open · **File**: PolarDecomposition.lean:37,47,52 · **Depends on**: PD-02 · **Parallel**: no · **Type**: def + lemma
#### Statement
```lean
noncomputable def ForMathlib.abs (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E := (isPositive_adjoint_comp_self A).sqrt
theorem abs_mul_self (A) : abs A ∘ₗ abs A = A.adjoint ∘ₗ A          -- = sqrt_mul_self
theorem norm_abs_apply (A) (x) : ‖abs A x‖ = ‖A x‖                  -- the (★) identity
```
#### Proof sketch
`abs_mul_self` is `sqrt_mul_self` (PD-02) at `T = A.adjoint ∘ₗ A`. `norm_abs_apply`: square both
sides — `‖abs A x‖² = re⟪A⋆A x,x⟫` (`sq_norm_sqrt_apply`) `= ‖Ax‖²` (`re⟪A⋆Ax,x⟫ = ‖Ax‖²`).
#### Mathlib lemmas needed
`LinearMap.isPositive_adjoint_comp_self` (Positive.lean), `sq_norm_sqrt_apply` (PD-02),
`LinearMap.star_eq_adjoint` (Adjoint.lean:699), `‖·‖²`↔`re⟪A⋆A·,·⟫`.
#### Sources
HJ 7.3.1 (`Q=(A⋆A)^{1/2}`); (★) is route-ii (Conway VI.3.9). Cross-check `CFC.abs_mul_abs`
(Abs.lean:64). #### Generality: `𝕜 : RCLike`, finite-dim, `ForMathlib` namespace. ~20 LOC.

### [PD-09] `ker_abs` + `range_abs`
- **Status**: open · **File**: PolarDecomposition.lean:57,62 · **Depends on**: PD-08, PD-03 · **Type**: lemma
#### Statement
```lean
theorem ker_abs (A) : ker (abs A) = ker A
theorem range_abs (A) : range (abs A) = (ker A)ᗮ
```
#### Proof sketch
`ker_abs`: `ker_sqrt` (PD-03) + `ker_adjoint_comp_self` (`ker(A⋆A)=ker A`, Adjoint.lean:620).
`range_abs`: `abs A` symmetric ⟹ `range = (ker)ᗮ` (`orthogonal_ker`/normal `orthogonal_range`) `=
(ker A)ᗮ`.
#### Mathlib lemmas needed
`LinearMap.ker_adjoint_comp_self` (620), `LinearMap.orthogonal_ker`/`ContinuousLinearMap.IsStarNormal.orthogonal_range`,
`sqrt_isSymmetric`. #### Sources HJ 7.2.6(c)/7.2.7(b). #### Generality: as PD-08. ~20 LOC.

### [CLEANUP-PD-4] /cleanup on PolarDecomposition.lean (3 tickets)
- **Status**: open · **Depends on**: PD-09 · **Type**: cleanup

### [PD-10] the polar factor `U` and `A = U|A|` (construction — the meaty one)
- **Status**: open · **File**: PolarDecomposition.lean:68,73,78,83,88 · **Depends on**: PD-07, PD-09, CLEANUP-PD-4 · **Type**: def + lemma
#### Statement
```lean
noncomputable def polarUnitary (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E
theorem polar_decomposition (A) : A = polarUnitary A ∘ₗ abs A
theorem polarUnitary_isPartialIsometry (A) : IsPartialIsometry (polarUnitary A)
theorem ker_polarUnitary (A) : ker (polarUnitary A) = ker A
theorem norm_polarUnitary_apply_of_mem {x} (hx : x ∈ (ker A)ᗮ) : ‖polarUnitary A x‖ = ‖x‖
```
#### Proof sketch
1. Construct `V₀ : range(abs A) →ₗ E` well-defined by `abs A x ↦ A x` (well-def: `abs A x = abs A y
   ⟹ A x = A y` from `ker_abs`, PD-09). Extend to `U` via `Submodule.linearProjOfIsCompl` /
   `prodEquivOfIsCompl` on `range(abs A) ⊕ (range abs A)ᗮ` (`isCompl_orthogonal`), zero on the
   complement `= (ker A)ᗮᗮ`... = `ker A` (via `range_abs`).
2. `polar_decomposition`: `U (abs A x) = V₀(abs A x) = A x`, and `abs A x ∈ range(abs A)`.
3. `isPartialIsometry`: PD-07 with `K = range(abs A) = (ker A)ᗮ` (PD-09), isometric via `norm_abs_apply`.
4. `ker_polarUnitary`, `norm_..._of_mem`: from the construction.
#### Mathlib lemmas needed
`Submodule.isCompl_orthogonal` (Projection/Basic.lean:89), `Submodule.linearProjOfIsCompl`/
`prodEquivOfIsCompl` (Projection.lean:338/76), `Submodule.subtype`/`coprod`, `range_abs`/`ker_abs`
(PD-09), `norm_abs_apply` (PD-08), `isPartialIsometry_of_isometryOn` (PD-07).
#### Sources
Conway VI.3.9 (route-ii construction); HJ 7.3.1(b) statement (decomposition-polar.md III.6–III.10).
#### Generality decision
`𝕜 : RCLike`, finite-dim. The construction is finite-dim (no closure). ~90 LOC (hardest ticket).

### [PD-11] invertible case — the unitary factor
- **Status**: open · **File**: PolarDecomposition.lean:97,102,107 · **Depends on**: PD-10, PD-04 · **Type**: def + lemma
#### Statement
```lean
noncomputable def polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) : E ≃ₗᵢ[𝕜] E
theorem coe_polarUnitaryEquiv (hA) : ((polarUnitaryEquiv hA : E →ₗ[𝕜] E)) = polarUnitary A
theorem polar_decomposition_of_isUnit (hA) : A = (polarUnitaryEquiv hA : E →ₗ[𝕜] E) ∘ₗ abs A
```
#### Proof sketch
`A` unit ⟹ `abs A` unit (`isUnit_sqrt_of_isUnit`, PD-04) ⟹ `polarUnitary A = A ∘ₗ (abs A)⁻¹` is a
bijective isometry (isometric everywhere since `(ker A)ᗮ=⊤`, PD-10) ⟹ package as
`LinearIsometryEquiv` (`LinearIsometryEquiv.ofBijective` / `Unitary.linearIsometryEquiv`).
#### Mathlib lemmas needed
`isUnit_sqrt_of_isUnit` (PD-04), `LinearIsometryEquiv.ofBijective`/`Unitary.linearIsometryEquiv`
(Adjoint.lean:944), `norm_polarUnitary_apply_of_mem` (PD-10), `ker`-triviality of a unit.
#### Sources
HJ 7.3.1(b) verbatim: "U uniquely determined if A nonsingular", `U = P⁻¹A = AQ⁻¹`. #### Generality:
as PD-10. ~35 LOC.

### [CLEANUP-ALL-PD-1] /cleanup-all on the polar project so far (pre-milestone)
- **Status**: open · **Depends on**: PD-11, CLEANUP-PD-2, CLEANUP-PD-3 · **Type**: cleanup

### [PD-12] ★ MILESTONE 1 ★ CFC bridge — the via-CFC headline
- **Status**: open · **File**: PolarDecomposition.lean:116,122 · **Depends on**: PD-11, PD-04, CLEANUP-ALL-PD-1 · **Type**: theorem (milestone)
#### Statement
```lean
theorem abs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H) :
    (abs A).toContinuousLinearMap = CFC.abs A.toContinuousLinearMap
theorem continuousLinearMap_polar_decomposition (A : H →L[ℂ] H) :
    ∃ U : H →L[ℂ] H, IsPartialIsometry U ∧ A = U ∘L CFC.abs A
```
#### Proof sketch
1. `abs_toContinuousLinearMap_eq_cfcAbs`: both sides are the PSD sqrt of `A⋆A`. `(abs A).toCLM` is
   PSD with `((abs A).toCLM)² = (A⋆A).toCLM` (PD-08 + the **`rfl`** adjoint bridge
   `adjoint_toContinuousLinearMap`, Adjoint.lean:541); `CFC.abs (A.toCLM)` is PSD with square `A⋆A`
   (`CFC.abs_mul_abs`, `abs_nonneg`). Conclude by `sqrt_unique` (PD-04) transported, or CFC
   sqrt-uniqueness.
2. `continuousLinearMap_polar_decomposition`: transport `polar_decomposition` (PD-10) + step 1
   through the finite-dim `toContinuousLinearMap` ring equiv; `U := (polarUnitary A).toCLM`.
#### Mathlib lemmas needed
`CFC.abs`/`abs_mul_abs`/`abs_nonneg`/`abs_sq` (Abs.lean:46/64/53/277),
`LinearMap.adjoint_toContinuousLinearMap` (Adjoint.lean:541, `rfl`), `LinearMap.toContinuousLinearMap`
(FiniteDimension.lean:299), `ContinuousLinearMap.star_eq_adjoint` (Adjoint.lean:254),
`sqrt_unique` (PD-04). #### Sources HJ 7.2.6 uniqueness; decomposition-polar.md III.14–III.15.
#### Generality decision
Headline necessarily **ℂ / `H →L[ℂ] H`** (mathlib's C⋆ instance on CLM is ℂ-only). ~60 LOC.
**Skeleton for both statements already compiles (green)** — the type-level bridge is verified.

### [CLEANUP-PD-5] /cleanup on PolarDecomposition.lean (final per-file)
- **Status**: open · **Depends on**: PD-12 · **Type**: cleanup

## Milestone 2 — intertwining unitary (Davis §2)

> `IntertwiningUnitary.lean` **skeleton authored + `lake build` green** (2026-07-04) — M2 tickets are
> "fill the sorry at file:line", same contract as M1. Signatures may need light edits once M1's exact
> API lands. Full source quotes: decomposition-polar.md Milestone 2 (Davis §2 lines 218–312, verbatim).

### [PD-13] spectral-projection prerequisite (API gap I.5)
- **Status**: open · **File**: IntertwiningUnitary.lean (new) · **Depends on**: CLEANUP-PD-5 · **Type**: def + API
#### Statement (shape)
`spectralProjection` of a symmetric operator onto the eigenspace for a value / index-set, as an
`E →ₗ[𝕜] E`; `IsStarProjection`, `∑ⱼ Pⱼ = 1`, `Pⱼ ∘ₗ Pₖ = 0 (j≠k)`, `range Pⱼ = eigenspace`.
#### Proof sketch
Build from `eigenvectorBasis` + `Submodule.starProjection` of the eigenspace submodule; the family
properties from orthonormality of the eigenbasis.
#### Mathlib lemmas needed
`Submodule.starProjection` (Projection/Basic.lean:124), `IsSymmetric.eigenvectorBasis`, eigenspace
API, `OrthonormalBasis.sum_repr`. #### Sources Davis §2 setup (lines 183–188). #### Generality:
`𝕜 : RCLike`, finite-dim. ~70 LOC. (API gap — its own mini-tree.)

### [PD-14] non-degeneracy ⟹ `(P'ⱼPⱼP'ⱼ)^{-1/2}` exists
- **Status**: open · **File**: IntertwiningUnitary.lean · **Depends on**: PD-13, PD-04 · **Type**: lemma
#### Statement (shape)
`Pⱼx≠0 ⟹ P'ⱼPⱼx≠0` (per block) ⟹ `P'ⱼPⱼP'ⱼ` strictly positive on `range P'ⱼ`; inverse sqrt via
`isUnit_sqrt_of_isUnit` (PD-04).
#### Sources Davis §2 line 224 (verbatim in decomposition-polar.md M2.1). #### ~50 LOC.

### [PD-15] block polar factor `Wⱼ` is unitary
- **Status**: open · **File**: IntertwiningUnitary.lean · **Depends on**: PD-14, PD-11 · **Type**: lemma
#### Statement (shape)
`Wⱼ := (P'ⱼPⱼP'ⱼ)^{-1/2} P'ⱼPⱼ : range Pⱼ ≃ₗᵢ range P'ⱼ` unitary — the invertible-case polar
decomposition (PD-11, `polarUnitaryEquiv`) of `P'ⱼPⱼ` restricted to the block.
#### Sources Davis §2 line 221. #### ~60 LOC.

### [CLEANUP-PD-6] /cleanup on IntertwiningUnitary.lean (3 tickets)
- **Status**: open · **Depends on**: PD-15 · **Type**: cleanup

### [PD-16] assemble `intertwiningUnitary` + `W Pⱼ = P'ⱼ W`
- **Status**: open · **File**: IntertwiningUnitary.lean · **Depends on**: PD-15, CLEANUP-PD-6 · **Type**: def + theorem
#### Statement (shape)
`intertwiningUnitary : E ≃ₗᵢ[𝕜] E := ∑ⱼ Wⱼ ∘ Pⱼ`; `W` unitary; `intertwiningUnitary_apply_proj :
W ∘ₗ Pⱼ = P'ⱼ ∘ₗ W`.
#### Sources Davis §2 line 229 (verbatim). #### ~70 LOC.

### [PD-17] angle interpretation `‖𝒞⊥W‖²_F = ∑ᵢ sin²θᵢ`
- **Status**: open · **File**: IntertwiningUnitary.lean · **Depends on**: PD-16 · **Type**: theorem
#### Statement (shape)
`θᵢ = arccos⟨Wxᵢ,xᵢ⟩`; `‖𝒞⊥W‖²_F = ∑ᵢ sin²θᵢ` via `‖Off W‖² = ‖W‖² − ‖𝒞W‖²` (pinching orthogonality)
and `‖W‖²_F = dim`. Needed by parent BL4.
#### Sources Davis §2 lines 280–312 (Davis's own proof, verbatim in decomposition-polar.md M2.4). #### ~80 LOC.

### [CLEANUP-PD-7] /cleanup on IntertwiningUnitary.lean (final per-file)
- **Status**: open · **Depends on**: PD-17 · **Type**: cleanup

## Milestone 3 — wire into Davis Result B

### [PD-18] unblock Davis BL3/BL4
- **Status**: open · **File**: EigenvalueChange.lean / new bridge · **Depends on**: PD-17, CLEANUP-PD-7 · **Type**: theorem (milestone)
#### Statement (shape)
Instantiate `intertwiningUnitary` with the spectral projection families of the parent's `T`,`S`;
supply `W`, `W Pⱼ = P'ⱼ W`, angles `θᵢ`, `‖𝒞⊥W‖²=∑sin²θᵢ` to Result B's BL3/BL4. Then BL1,BL2,BL5,BL6
(decomposition-B.md) resume.
#### Sources decomposition-B.md (parent). #### ~40 LOC bridge; unblocks the parent board.

### [CLEANUP-FINAL-PD] /cleanup-all on the whole polar project
- **Status**: open · **Depends on**: PD-18 · **Type**: cleanup (final)

## Cleanup-cadence check
18 proof/def tickets ⟹ ≥⌈18/3⌉=6 per-file cleanups + finals. Inserted: CLEANUP-PD-1..7 (per-file +
finals across 4 files), CLEANUP-ALL-PD-1 (pre-M1-milestone PD-12), CLEANUP-FINAL-PD. ✓
