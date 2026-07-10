/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SinTwoThetaUINorm.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]), plan step G1 of
`dev/davis-kahan-expert-completion-plan.md`.

The subspace Davis–Kahan sin 2Θ theorem, in every unitarily invariant norm:
`N (Q ∘ P̂ ∘ P) ≤ N (S − T) / (b − a)`, where `P, Q = 1 − P` split along a
`T`-invariant subspace across whose splitting the quadratic form of `T` jumps
from `≤ a` to `≥ b`, and `P̂` projects onto any `S`-invariant subspace.  The
operator `2 (Q ∘ P̂ ∘ P)` has singular values `sin 2θᵢ` (the θᵢ the principal
angles between the two subspaces), so this is `‖sin 2Θ‖ ≤ 2 ‖S − T‖ / (b − a)`
— the gap hypothesis lives on ONE operator only, and no smallness of the
perturbation is assumed.

Proved by the mirror reduction (Davis–Kahan III, §8): reflect `T` through the
perturbed subspace, `T' := J T J` with `J = 2 P̂ − 1`, and apply the sin Θ
theorem (`SinThetaUINorm.lean`) to the pair `(T, T')` — the reflected subspace
`J (Uᗮ)` is `T'`-invariant with the transported form bound, so the pair is
separated by `T`'s own gap; the resulting cross-projection is `J`-conjugate to
`Q ∘ J ∘ P = 2 (Q ∘ P̂ ∘ P)`, and `N (T' − T) ≤ 2 N (S − T)` because `J`
commutes with `S`.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.SinThetaUINorm

/-! # The subspace Davis–Kahan sin 2Θ theorem, every unitarily invariant norm

## Statement cross-check (statement-first gate, plan step G1)

The classical subspace sin 2Θ theorem (Davis–Kahan 1970, part III, §8; see
also Bhatia, *Matrix Analysis*, VII.3 notes) reads: if the spectrum of the
symmetric `T` splits across a gap `(a, b)` along an invariant subspace `U`,
and `P̂` is a spectral projection of the perturbed operator `S = T + H`, then
`‖sin 2Θ‖ ≤ 2 ‖H‖ / (b − a)` in every unitarily invariant norm, where `Θ` is
the operator angle between `U` and `ran P̂`.  Distinctive features, mirrored
exactly here:

* the gap hypothesis constrains **one operator only** (`T`; two-sided:
  form `≥ b` on `U`, `≤ a` on `Uᗮ`) — unlike sin Θ, which needs a cross-gap
  between the two operators' spectral blocks;
* **no smallness** of `H` and **no location constraint** on the perturbed
  subspace are required (our `V` is merely `S`-invariant — spectral selection
  is not even mentioned, which is strictly more general than the classical
  statement; the degenerate sanity check `S = T` forces the conclusion `0 ≤ 0`
  because a `T`-invariant `V` then splits along `U ⊕ Uᗮ`);
* the constant is `2`, carried here by the identity
  `Q ∘ J ∘ P = 2 (Q ∘ P̂ ∘ P)` with `J = 2 P̂ − 1` the reflection.

Encoding of `sin 2Θ`: the conclusion bounds `N (Q ∘ P̂ ∘ P)` by
`N (S − T) / (b − a)`.  In a joint CS basis the operator `2 (Q ∘ P̂ ∘ P)` has
singular values `2 sin θᵢ cos θᵢ = sin 2θᵢ`, so `2 (Q ∘ P̂ ∘ P)` *is* the
`sin 2Θ` operator; certifying that dictionary in Lean (the analogue of the E2
identification for `sin Θ`) is the deferred principal-angle brick recorded in
the plan — the *norm bound* proved here is the analytic content of the
theorem.  The sharper mirror-defect form
`2 N (Q ∘ P̂ ∘ P) ≤ N (J T J − T) / (b − a)` (with `J T J − T` twice the
`J`-odd part of `H` when `J S = S J`) is stated separately: it needs no `S`
at all, only the reflection.

## Main results

* `ForMathlib.UnitarilyInvariantNorm.sin_two_theta_reflection_le`: the
  mirror-defect bound `2 N (Q ∘ W.starProjection ∘ P) ≤ N (J T J − T) / (b−a)`
  for an arbitrary subspace `W` with reflection `J`.
* `ForMathlib.UnitarilyInvariantNorm.sin_two_theta_starProjection_le`: the
  sin 2Θ theorem `N (Q ∘ P̂ ∘ P) ≤ N (S − T) / (b − a)`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46 (§8).
* R. Bhatia, *Matrix Analysis*, Chapter VII.
* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal.
  Appl. 6 (1963), 159–173 (the per-vector case, formalized in
  `RotationSharp.lean`).
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] {T S : E →ₗ[𝕜] E}

namespace UnitarilyInvariantNorm

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
private theorem coe_apply (f : E ≃ₗᵢ[𝕜] E) (v : E) : f.toLinearMap v = f v := rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
private theorem coe_equiv_apply (f : E ≃ₗᵢ[𝕜] E) (v : E) :
    (f.toLinearEquiv : E →ₗ[𝕜] E) v = f v := rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The scalar `((2 : ℝ) : 𝕜)`-multiple agrees with the `ℕ`-double appearing in
`Submodule.reflection_apply`.  Auxiliary. -/
private theorem ofReal_two_smul (y : E) : ((2 : ℝ) : 𝕜) • y = 2 • y := by
  rw [show ((2 : ℝ) : 𝕜) = ((2 : ℕ) : 𝕜) by norm_cast, Nat.cast_smul_eq_nsmul]

/-- **The mirror-defect sin 2Θ bound.**  Let `T` be symmetric with an invariant
subspace `U` across whose splitting the quadratic form of `T` jumps from `≤ a`
(on `Uᗮ`) to `≥ b` (on `U`), and let `W` be *any* subspace, with reflection
`J = 2 W.starProjection − 1`.  Then for every unitarily invariant norm,

`2 N (Uᗮ.starProjection ∘ W.starProjection ∘ U.starProjection) ≤ N (J T J − T) / (b − a)`.

The right side is the *mirror defect* of `T` — how far `T` is from commuting
with the reflection through `W`; no second operator is involved. -/
theorem sin_two_theta_reflection_le (N : UnitarilyInvariantNorm 𝕜 E)
    (hT : T.IsSymmetric) {U W : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    2 * N ((Uᗮ.starProjection ∘L W.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap - T)
        / (b - a) := by
  have hg : (0 : ℝ) < b - a := by linarith
  -- The reflected operator `T' = J T J` and the reflected subspace `J (Uᗮ)`.
  set T' : E →ₗ[𝕜] E :=
    W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap with hT'def
  have hT'sym : T'.IsSymmetric := by
    have h := isSymmetric_conj_unitary hT (W.reflection (𝕜 := 𝕜))
    rwa [Submodule.reflection_symm] at h
  have hUperp_inv : ∀ x ∈ Uᗮ, T x ∈ Uᗮ := fun x hx =>
    map_mem_orthogonal_of_forall_map_mem hT hUinv hx
  set V' : Submodule 𝕜 E :=
    Uᗮ.map ((W.reflection (𝕜 := 𝕜)).toLinearEquiv : E →ₗ[𝕜] E) with hV'def
  -- `V'` is `T'`-invariant.
  have hV'inv : ∀ x ∈ V', T' x ∈ V' := by
    rintro x ⟨w, hw, rfl⟩
    refine Submodule.mem_map.mpr ⟨T w, hUperp_inv w hw, ?_⟩
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      hT'def, LinearMap.comp_apply, Submodule.reflection_reflection]
  -- The form of `T'` on `V'` sits below `a`.
  have hV'form : ∀ x ∈ V', RCLike.re ⟪T' x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2 := by
    rintro x ⟨w, hw, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    have happly : T' (W.reflection w) = W.reflection (T w) := by
      simp only [hT'def, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, Submodule.reflection_reflection]
    rw [happly, (W.reflection (𝕜 := 𝕜)).inner_map_map,
      (W.reflection (𝕜 := 𝕜)).norm_map]
    exact hUa w hw
  -- The form of `T` on `U` sits above `a + (b − a) = b`.
  have hUform : ∀ x ∈ U, (a + (b - a)) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
    intro x hx
    have hb' : a + (b - a) = b := by ring
    rw [hb']
    exact hUb x hx
  -- The sin Θ theorem for the pair `(T, T')` across `T`'s own gap.
  have hmain := N.apply_starProjection_comp_starProjection_le hT hT'sym
    hUinv hV'inv hg hUform hV'form
  -- Identify the cross-projection: `P_{V'} ∘ P_U = J ∘ (P_{Uᗮ} ∘ J ∘ P_U)`.
  have hVsP : ∀ x, V'.starProjection x
      = W.reflection (Uᗮ.starProjection (W.reflection x)) := by
    intro x
    show (Uᗮ.map ((W.reflection (𝕜 := 𝕜)).toLinearEquiv : E →ₗ[𝕜] E)).starProjection x
      = W.reflection (Uᗮ.starProjection (W.reflection x))
    rw [Submodule.starProjection_map_apply, Submodule.reflection_symm]
  have hconj : ((V'.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = W.reflection.toLinearMap
          ∘ₗ ((Uᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ W.reflection.toLinearMap
          ∘ₗ ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    ext x
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      LinearMap.comp_apply, coe_apply]
    exact hVsP _
  -- Kill the outer reflection and halve the inner one: `Q ∘ J ∘ P = 2 Q P̂ P`.
  have hkey : ((Uᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
        ∘ₗ W.reflection.toLinearMap
        ∘ₗ ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = ((2 : ℝ) : 𝕜) • ((Uᗮ.starProjection ∘L W.starProjection
          ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    ext x
    have hz : Uᗮ.starProjection (U.starProjection x) = 0 := by
      refine Submodule.eq_starProjection_of_mem_orthogonal
        (Submodule.zero_mem Uᗮ) ?_
      simp only [sub_zero]
      exact U.le_orthogonal_orthogonal (U.starProjection_apply_mem x)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, coe_apply,
      Submodule.reflection_apply, map_sub, map_nsmul, hz, sub_zero,
      ofReal_two_smul]
  calc 2 * N ((Uᗮ.starProjection ∘L W.starProjection ∘L U.starProjection
          : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = N (((2 : ℝ) : 𝕜) • ((Uᗮ.starProjection ∘L W.starProjection
          ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
        rw [N.smul_eq, RCLike.norm_ofReal]
        norm_num
    _ = N (((V'.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E))
        := by rw [hconj, N.invariant_left, hkey]
    _ ≤ N (T' - T) / (b - a) := hmain

/-- **The subspace Davis–Kahan sin 2Θ theorem, every unitarily invariant
norm.**  Let `T, S` be symmetric, `U` a `T`-invariant subspace with the
two-sided form separation `re ⟪T x, x⟫ ≥ b ‖x‖²` on `U` and `≤ a ‖x‖²` on
`Uᗮ` (`a < b` — the gap constrains `T` alone), and `V` any `S`-invariant
subspace.  Then

`N (Uᗮ.starProjection ∘ V.starProjection ∘ U.starProjection) ≤ N (S − T) / (b − a)`.

The operator `2 (Q ∘ P̂ ∘ P)` on the left has singular values `sin 2θᵢ`, so
this is `‖sin 2Θ‖ ≤ 2 ‖S − T‖ / (b − a)` — no smallness of the perturbation,
and no spectral-location constraint on `V`. -/
theorem sin_two_theta_starProjection_le (N : UnitarilyInvariantNorm 𝕜 E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    N ((Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) := by
  have hg : (0 : ℝ) < b - a := by linarith
  -- The mirror-defect bound with the perturbed subspace as the mirror.
  have h1 := N.sin_two_theta_reflection_le (W := V) hT hUinv hab hUb hUa
  -- The reflection through the `S`-invariant `V` commutes with `S`.
  have hcomm : ∀ x, V.reflection (S x) = S (V.reflection x) := by
    intro x
    have hc := starProjection_comp_toContinuousLinearMap_comm hS hVinv x
    rw [Submodule.reflection_apply, Submodule.reflection_apply, map_sub,
      map_nsmul, hc]
  have hJSJ : V.reflection.toLinearMap ∘ₗ S ∘ₗ V.reflection.toLinearMap = S := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← hcomm, Submodule.reflection_reflection]
  -- The mirror defect of `T` is twice the perturbation:
  -- `J T J − T = J (T − S) J + (S − T)`.
  have hident : V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap - T
      = V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap
        + (S - T) := by
    have hexp : V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap
        = V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap
          - V.reflection.toLinearMap ∘ₗ S ∘ₗ V.reflection.toLinearMap := by
      ext x
      simp [map_sub]
    rw [hexp, hJSJ]
    abel
  have hbound : N (V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap - T)
      ≤ 2 * N (S - T) := by
    rw [hident]
    calc N (V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap
          + (S - T))
        ≤ N (V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap)
          + N (S - T) := N.add_le _ _
      _ = N (T - S) + N (S - T) := by
          rw [N.invariant' V.reflection V.reflection (T - S)]
      _ = 2 * N (S - T) := by
          rw [show T - S = -(S - T) by abel, N.apply_neg]
          ring
  have h2 : N (V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap - T)
        / (b - a)
      ≤ 2 * N (S - T) / (b - a) := by gcongr
  have h3 := h1.trans h2
  have h4 : 2 * N (S - T) / (b - a) = 2 * (N (S - T) / (b - a)) := by ring
  linarith

/-- **The Frobenius subspace sin 2Θ theorem.**  The every-UI-norm sin 2Θ bound
instantiated at the Frobenius norm:
`‖Uᗮ.sP ∘ V.sP ∘ U.sP‖_F ≤ ‖S − T‖_F / (b − a)`.  With
`sin_two_theta_starProjection_le`'s dictionary the left side is `‖½ sin 2Θ‖_F`;
unfold either side with `frobenius_apply` for the column-norm-sum reading. -/
theorem frobenius_sin_two_theta_starProjection_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    frobenius 𝕜 E ((Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ frobenius 𝕜 E (S - T) / (b - a) :=
  (frobenius 𝕜 E).sin_two_theta_starProjection_le hT hS hUinv hVinv hab hUb hUa

/-! ### Spectral (eigenvalue-hypothesis) forms

The subspace headline `sin_two_theta_starProjection_le` and its mirror-defect
companion, specialized to spectral subspaces: `U` is the span of the
`T`-eigenvectors selected by `s`, whose eigenvalues sit above `b` while the
complementary ones sit below `a`; `V` is the analogous `S`-eigenblock selected
by `s'`.  This is the every-UI-norm sin 2Θ theorem in the eigenvalue-hypothesis
form the literature states, mirroring
`SinThetaOpNorm.norm_starProjection_comp_starProjection_le_of_eigenvalues`
(plan step OP1). -/

section Spectral

variable {n : ℕ}

/-- **Subspace sin 2Θ, every unitarily invariant norm, spectral form.**  With
`U` the `T`-eigenblock selected by `s` (selected eigenvalues `≥ b`, complementary
`≤ a`) and `V` the `S`-eigenblock selected by `s'`,
`N (Uᗮ.sP ∘ V.sP ∘ U.sP) ≤ N (S − T) / (b − a)` for every unitarily invariant
norm `N`.  The left side is `N (½ sin 2Θ)` (see the module docstring). -/
theorem sin_two_theta_starProjection_le_of_eigenvalues (N : UnitarilyInvariantNorm 𝕜 E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {s s' : Finset (Fin n)} {a b : ℝ} (hab : a < b)
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a) :
    N (((specSubspace (hT.eigenvectorBasis hn) (· ∈ s))ᗮ.starProjection ∘L
        (specSubspace (hS.eigenvectorBasis hn) (· ∈ s')).starProjection ∘L
        (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) :=
  N.sin_two_theta_starProjection_le hT hS
    (fun _ hx => map_mem_specSubspace hT hn _ hx)
    (fun _ hx => map_mem_specSubspace hS hn _ hx) hab
    (fun _ hx => le_re_inner_map_self_of_mem_specSubspace hT hn (fun i hi => hb i hi) hx)
    (fun w hw => by
      rw [orthogonal_specSubspace] at hw
      exact re_inner_map_self_le_of_mem_specSubspace hT hn (fun i hi => ha i hi) hw)

/-- **Mirror-defect sin 2Θ, spectral form.**  As
`sin_two_theta_starProjection_le_of_eigenvalues` but with an arbitrary subspace
`W` in the middle and the sharper mirror-defect right side (no second operator):
`2 N (Uᗮ.sP ∘ W.sP ∘ U.sP) ≤ N (J T J − T) / (b − a)`, `J = W.reflection`. -/
theorem sin_two_theta_reflection_le_of_eigenvalues (N : UnitarilyInvariantNorm 𝕜 E)
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] {s : Finset (Fin n)} {a b : ℝ} (hab : a < b)
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a) :
    2 * N (((specSubspace (hT.eigenvectorBasis hn) (· ∈ s))ᗮ.starProjection ∘L
        W.starProjection ∘L
        (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap - T) / (b - a) :=
  N.sin_two_theta_reflection_le hT
    (fun _ hx => map_mem_specSubspace hT hn _ hx) hab
    (fun _ hx => le_re_inner_map_self_of_mem_specSubspace hT hn (fun i hi => hb i hi) hx)
    (fun w hw => by
      rw [orthogonal_specSubspace] at hw
      exact re_inner_map_self_le_of_mem_specSubspace hT hn (fun i hi => ha i hi) hw)

end Spectral

end UnitarilyInvariantNorm

end ForMathlib
