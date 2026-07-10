/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`UnitarilyInvariantNorm.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]), plan step F3 (v4 reroute) of
`dev/davis-kahan-expert-completion-plan.md`.

Unitarily invariant (semi)norms on the square operators over a
finite-dimensional inner product space, the operator SVD factorization
`A = U ∘ diag(σ(A)) ∘ V`, the symmetric-gauge representation `N A = Φ_N(σ(A))`,
and the **Fan dominance principle**: Ky Fan domination
`∀ k, kyFanSum k A ≤ kyFanSum k B` implies `N A ≤ N B` for every unitarily
invariant norm `N`.  The engine is a T-transform descent performed *directly on
the gauge* — no Hardy–Littlewood–Pólya theorem, no weak-majorization
completion, no Birkhoff: each transform step costs one triangle inequality,
one homogeneity, and one swap-permutation invariance of the gauge.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.KyFan
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! # Unitarily invariant norms and the Fan dominance principle

For a finite-dimensional inner product space `E` over `𝕜 = ℝ, ℂ`:

* `ForMathlib.diagOp b x`: the operator with (real) diagonal `x` in the
  orthonormal basis `b`, with its algebra (`diagOp_add`, `diagOp_real_smul`,
  `diagOp_comp`, symmetry) and its singular values
  (`singularValues_diagOp`: for antitone nonnegative `x` they are `x` itself);
* `ForMathlib.exists_unitary_diagOp_factorization` — the **operator SVD**:
  every `A : E →ₗ[𝕜] E` factors as `U ∘ₗ diagOp b σ(A) ∘ₗ V` with `U, V`
  unitary, relative to *any* fixed orthonormal basis `b`;
* `ForMathlib.UnitarilyInvariantNorm`: subadditive, absolutely homogeneous,
  and invariant under composition with unitaries on both sides (seminorm
  axioms — positivity is never needed for Davis–Kahan);
* `ForMathlib.UnitarilyInvariantNorm.apply_eq_gauge` — the **symmetric-gauge
  representation** `N A = Φ_N(σ(A))` where `Φ_N x := N (diagOp b x)`;
* `ForMathlib.UnitarilyInvariantNorm.gauge_le_gauge_of_prefix_sums_le` — the
  **T-transform descent**: for `z` antitone nonnegative and `y` nonnegative,
  prefix-sum domination `∀ m, ∑_{i<m} z ≤ ∑_{i<m} y` forces `Φ z ≤ Φ y`;
* `ForMathlib.UnitarilyInvariantNorm.apply_le_of_kyFanSum_le` — the
  **Fan dominance principle**;
* `ForMathlib.UnitarilyInvariantNorm.apply_adjoint` — `N (A⋆) = N A`.

The descent replaces the classical majorization pipeline (weak-majorization
completion + Hardy–Littlewood–Pólya + Birkhoff): given a violation `y l < z l`
pick the least such `l`; prefix domination produces `j < l` with `z j < y j`;
averaging `y` with its `(j l)`-swap by `c₂ = δ/(y j − y l)`,
`δ = min (y j − z j) (z l − y l)`, moves `y j ↦ y j − δ` and `y l ↦ y l + δ`,
kills a disagreement, preserves nonnegativity and prefix domination, and does
not increase the gauge.

## References

* R. Bhatia, *Matrix Analysis*, Chapter IV (symmetric gauge functions, Ky Fan
  dominance, Theorem IV.2.2).
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*,
  Quart. J. Math. Oxford 11 (1960), 50–59.
-/

namespace ForMathlib

open scoped InnerProductSpace
open LinearMap
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ}

/-! ### The diagonal operator of a real vector in an orthonormal basis -/

/-- The operator with (real) diagonal `x` in the orthonormal basis `b`:
`diagOp b x (b i) = x i • b i`. -/
noncomputable def diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    E →ₗ[𝕜] E :=
  ∑ i, ((x i : ℝ) : 𝕜) • (InnerProductSpace.rankOne 𝕜 (b i) (b i)).toLinearMap

omit [FiniteDimensional 𝕜 E] in
theorem diagOp_apply (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) (v : E) :
    diagOp b x v = ∑ i, ((x i : ℝ) : 𝕜) • ⟪b i, v⟫_𝕜 • b i := by
  unfold diagOp
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    simp [InnerProductSpace.rankOne_apply]

omit [FiniteDimensional 𝕜 E] in
theorem diagOp_apply_basis (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (j : Fin n) : diagOp b x (b j) = ((x j : ℝ) : 𝕜) • b j := by
  rw [diagOp_apply]
  have hterm : ∀ i ∈ Finset.univ, ((x i : ℝ) : 𝕜) • ⟪b i, b j⟫_𝕜 • b i
      = if i = j then ((x i : ℝ) : 𝕜) • b i else 0 := fun i _ => by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [orthonormal_iff_ite.mp b.orthonormal i j, hij]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' Finset.univ j fun i => ((x i : ℝ) : 𝕜) • b i]
  simp

omit [FiniteDimensional 𝕜 E] in
theorem diagOp_add (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    diagOp b (x + y) = diagOp b x + diagOp b y := by
  unfold diagOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, RCLike.ofReal_add, add_smul]

omit [FiniteDimensional 𝕜 E] in
theorem diagOp_real_smul (b : OrthonormalBasis (Fin n) 𝕜 E) (c : ℝ)
    (x : Fin n → ℝ) : diagOp b (c • x) = ((c : ℝ) : 𝕜) • diagOp b x := by
  unfold diagOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul, smul_smul]

omit [FiniteDimensional 𝕜 E] in
/-- A real diagonal operator is symmetric. -/
theorem isSymmetric_diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    (diagOp b x).IsSymmetric := by
  intro u v
  rw [diagOp_apply, diagOp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    inner_conj_symm]
  ring

theorem adjoint_diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    (diagOp b x).adjoint = diagOp b x :=
  (isSymmetric_diagOp b x).adjoint_eq

omit [FiniteDimensional 𝕜 E] in
/-- Diagonal operators in the same basis multiply diagonally. -/
theorem diagOp_comp (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    diagOp b x ∘ₗ diagOp b y = diagOp b (x * y) := by
  refine b.toBasis.ext fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagOp_apply_basis,
    map_smul, diagOp_apply_basis, diagOp_apply_basis, smul_smul, Pi.mul_apply,
    RCLike.ofReal_mul, mul_comm]

/-- The singular values of a diagonal operator with *antitone nonnegative*
diagonal are the diagonal itself. -/
theorem singularValues_diagOp (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {x : Fin n → ℝ}
    (hx_anti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (i : Fin n) :
    (diagOp b x).singularValues (i : ℕ) = x i := by
  have hgram : (diagOp b x).adjoint ∘ₗ diagOp b x = diagOp b (x * x) := by
    rw [adjoint_diagOp, diagOp_comp]
  have hsq_anti : Antitone fun i => x i ^ 2 := fun i j hij =>
    pow_le_pow_left₀ (hx0 j) (hx_anti hij) 2
  have heig : (diagOp b x).isSymmetric_adjoint_comp_self.eigenvalues hn
      = fun i => x i ^ 2 :=
    (eigenvalues_congr hgram (diagOp b x).isSymmetric_adjoint_comp_self
      (isSymmetric_diagOp b (x * x)) hn).trans
      (eigenvalues_eq_of_eigenbasis _ hn b hsq_anti fun i => by
        rw [diagOp_apply_basis]
        congr 1
        rw [Pi.mul_apply]
        push_cast
        ring)
  rw [(diagOp b x).singularValues_fin hn i, congrFun heig i,
    Real.sqrt_sq (hx0 i)]

/-! ### The operator SVD factorization -/

omit [FiniteDimensional 𝕜 E] in
private theorem coe_toLinearMap_apply (U : E ≃ₗᵢ[𝕜] E) (v : E) :
    U.toLinearMap v = U v := rfl

/-- **Operator SVD**: relative to *any* fixed orthonormal basis `b`, every
square operator factors as `A = U ∘ diag(σ(A)) ∘ V` with `U, V` unitary. -/
theorem exists_unitary_diagOp_factorization (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E) :
    ∃ U V : E ≃ₗᵢ[𝕜] E,
      A = U.toLinearMap ∘ₗ diagOp b (fun i => A.singularValues (i : ℕ))
        ∘ₗ V.toLinearMap := by
  subst hn
  set w := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hw
  set K := b.equiv w (Equiv.refl _) with hK
  have hKb : ∀ i, K (b i) = w i := fun i => by
    rw [hK, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
  have hKsymm : ∀ i, K.symm (w i) = b i := fun i => by
    rw [← hKb i, LinearIsometryEquiv.symm_apply_apply]
  have habs_w : ∀ i, abs A (w i)
      = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) • w i := by
    intro i
    rw [show abs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
      (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis i,
      ← A.singularValues_fin rfl i]
  have habs : abs A
      = K.toLinearMap ∘ₗ diagOp b (fun i => A.singularValues (i : ℕ))
        ∘ₗ K.symm.toLinearMap := by
    refine w.toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, habs_w i, LinearMap.comp_apply,
      LinearMap.comp_apply, coe_toLinearMap_apply, coe_toLinearMap_apply,
      hKsymm i, diagOp_apply_basis, map_smul, hKb i]
  refine ⟨K.trans (polarUnitary A), K.symm, ?_⟩
  ext v
  have hpolar := LinearMap.congr_fun (polar_decomposition_unitary A) v
  rw [LinearMap.comp_apply] at hpolar
  have habsv := LinearMap.congr_fun habs v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_toLinearMap_apply,
    coe_toLinearMap_apply] at habsv
  rw [hpolar, LinearMap.comp_apply, LinearMap.comp_apply,
    coe_toLinearMap_apply, coe_toLinearMap_apply, habsv,
    LinearIsometryEquiv.trans_apply]
  rfl

/-! ### Unitarily invariant norms -/

/-- A **unitarily invariant (semi)norm** on the square operators over a
finite-dimensional inner product space: subadditive, absolutely homogeneous,
and invariant under composition with unitaries on both sides.

Positivity (`N A = 0 → A = 0`) is deliberately *not* required — the
Davis–Kahan pipeline never uses it, and every consequence below (gauge
representation, Fan dominance) holds at the seminorm level. -/
structure UnitarilyInvariantNorm (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    where
  /-- The underlying function on square operators. -/
  toFun : (E →ₗ[𝕜] E) → ℝ
  /-- Subadditivity. -/
  add_le' : ∀ A B : E →ₗ[𝕜] E, toFun (A + B) ≤ toFun A + toFun B
  /-- Absolute homogeneity. -/
  smul' : ∀ (a : 𝕜) (A : E →ₗ[𝕜] E), toFun (a • A) = ‖a‖ * toFun A
  /-- Two-sided unitary invariance. -/
  invariant' : ∀ (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E),
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

namespace UnitarilyInvariantNorm

instance : CoeFun (UnitarilyInvariantNorm 𝕜 E) fun _ => (E →ₗ[𝕜] E) → ℝ :=
  ⟨UnitarilyInvariantNorm.toFun⟩

variable (N : UnitarilyInvariantNorm 𝕜 E)

theorem add_le (A B : E →ₗ[𝕜] E) : N (A + B) ≤ N A + N B := N.add_le' A B

theorem smul_eq (a : 𝕜) (A : E →ₗ[𝕜] E) : N (a • A) = ‖a‖ * N A := N.smul' a A

theorem invariant (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = N A := N.invariant' U V A

/-- Left unitary invariance. -/
theorem invariant_left (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    N (U.toLinearMap ∘ₗ A) = N A := by
  have h := N.invariant' U (LinearIsometryEquiv.refl 𝕜 E) A
  have hid : A ∘ₗ (LinearIsometryEquiv.refl 𝕜 E).toLinearMap = A := by
    ext v; rfl
  rwa [hid] at h

/-- Right unitary invariance. -/
theorem invariant_right (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    N (A ∘ₗ V.toLinearMap) = N A := by
  have h := N.invariant' (LinearIsometryEquiv.refl 𝕜 E) V A
  have hid : (LinearIsometryEquiv.refl 𝕜 E).toLinearMap
      ∘ₗ (A ∘ₗ V.toLinearMap) = A ∘ₗ V.toLinearMap := by
    ext v; rfl
  rwa [hid] at h

theorem apply_zero : N (0 : E →ₗ[𝕜] E) = 0 := by
  have h := N.smul' (0 : 𝕜) 0
  rwa [zero_smul, norm_zero, zero_mul] at h

theorem apply_neg (A : E →ₗ[𝕜] E) : N (-A) = N A := by
  have h := N.smul' (-1 : 𝕜) A
  rwa [neg_one_smul, norm_neg, norm_one, one_mul] at h

theorem nonneg (A : E →ₗ[𝕜] E) : 0 ≤ N A := by
  have h := N.add_le' A (-A)
  rw [add_neg_cancel, N.apply_zero, N.apply_neg] at h
  linarith

/-! ### The symmetric gauge -/

/-- The **symmetric gauge** of a unitarily invariant norm relative to an
orthonormal basis `b`: the norm of the diagonal operator with diagonal `x`.
Defined on *all* real vectors, not only sorted nonnegative ones — the
T-transform descent exploits its subadditivity, homogeneity, permutation
invariance, and single-coordinate sign invariance on arbitrary vectors. -/
noncomputable def gauge (N : UnitarilyInvariantNorm 𝕜 E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : ℝ :=
  N (diagOp b x)

theorem gauge_add_le (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    N.gauge b (x + y) ≤ N.gauge b x + N.gauge b y := by
  rw [gauge, diagOp_add]
  exact N.add_le' _ _

theorem gauge_real_smul (b : OrthonormalBasis (Fin n) 𝕜 E) (c : ℝ)
    (x : Fin n → ℝ) : N.gauge b (c • x) = |c| * N.gauge b x := by
  rw [gauge, diagOp_real_smul, N.smul', RCLike.norm_ofReal]
  rfl

/-- Permutation invariance of the gauge: conjugating the diagonal operator by
the basis-permutation unitary permutes the diagonal. -/
theorem gauge_perm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : N.gauge b (x ∘ π) = N.gauge b x := by
  have hconj : diagOp b (x ∘ π)
      = (b.equiv b π).symm.toLinearMap ∘ₗ diagOp b x
        ∘ₗ (b.equiv b π).toLinearMap := by
    refine b.toBasis.ext fun j => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
      LinearMap.comp_apply, coe_toLinearMap_apply, coe_toLinearMap_apply,
      OrthonormalBasis.equiv_apply_basis, diagOp_apply_basis,
      diagOp_apply_basis, map_smul, Function.comp_apply]
    congr 1
    rw [← OrthonormalBasis.equiv_apply_basis b b π j,
      LinearIsometryEquiv.symm_apply_apply]
  rw [gauge, hconj, N.invariant']
  rfl

/-- Single-coordinate sign flip invariance of the gauge: flipping the sign of
the `j`-th diagonal entry composes the diagonal operator with the reflection
through `(𝕜 ∙ b j)ᗮ`, a unitary. -/
theorem gauge_neg_single (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (j : Fin n) :
    N.gauge b (Function.update x j (-(x j))) = N.gauge b x := by
  have hcomp : diagOp b (Function.update x j (-(x j)))
      = diagOp b x ∘ₗ ((𝕜 ∙ b j)ᗮ).reflection.toLinearMap := by
    refine b.toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
      coe_toLinearMap_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
        map_neg, diagOp_apply_basis, diagOp_apply_basis, Function.update_self,
        RCLike.ofReal_neg, neg_smul]
    · have hmem : b i ∈ (𝕜 ∙ b j)ᗮ :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
          (b.orthonormal.2 (Ne.symm hij))
      rw [Submodule.reflection_mem_subspace_eq_self hmem, diagOp_apply_basis,
        diagOp_apply_basis, Function.update_of_ne hij]
  rw [gauge, hcomp, N.invariant_right]
  rfl

/-- **The gauge representation**: a unitarily invariant norm is the gauge of
the singular values, via the operator SVD. -/
theorem apply_eq_gauge (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E) :
    N A = N.gauge b fun i => A.singularValues (i : ℕ) := by
  obtain ⟨U, V, hUV⟩ := exists_unitary_diagOp_factorization hn b A
  conv_lhs => rw [hUV]
  exact N.invariant' U V _

/-! ### Coordinatewise monotonicity of the gauge -/

/-- Shrinking one coordinate of `y` (in absolute value) does not increase the
gauge: `update y j t` with `|t| ≤ y j` is a convex combination of `y` and its
`j`-th sign flip. -/
theorem gauge_update_le (b : OrthonormalBasis (Fin n) 𝕜 E) {y : Fin n → ℝ}
    {j : Fin n} {t : ℝ} (ht : |t| ≤ y j) :
    N.gauge b (Function.update y j t) ≤ N.gauge b y := by
  have hyj : 0 ≤ y j := le_trans (abs_nonneg t) ht
  rcases hyj.eq_or_lt with h0 | hpos
  · -- `y j = 0` forces `t = 0`: the update is trivial.
    have ht0 : t = 0 := by
      have h1 : |t| ≤ 0 := by rw [h0]; exact ht
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg t))
    have hupd : Function.update y j t = y := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, ht0, ← h0]
      · rw [Function.update_of_ne hij]
    rw [hupd]
  · set c₁ : ℝ := (y j + t) / (2 * y j) with hc₁
    set c₂ : ℝ := (y j - t) / (2 * y j) with hc₂
    obtain ⟨ht₁, ht₂⟩ := abs_le.mp ht
    have h2yj : 0 < 2 * y j := by linarith
    have hyj0 : (2 : ℝ) * y j ≠ 0 := ne_of_gt h2yj
    have hc₁0 : 0 ≤ c₁ := div_nonneg (by linarith) h2yj.le
    have hc₂0 : 0 ≤ c₂ := div_nonneg (by linarith) h2yj.le
    have hsum : c₁ + c₂ = 1 := by
      rw [hc₁, hc₂]
      field_simp
      ring
    have hdecomp : Function.update y j t
        = c₁ • y + c₂ • Function.update y j (-(y j)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, Function.update_self, hc₁, hc₂]
        field_simp
        ring
      · rw [Function.update_of_ne hij, Function.update_of_ne hij, ← add_mul,
          hsum, one_mul]
    calc N.gauge b (Function.update y j t)
        = N.gauge b (c₁ • y + c₂ • Function.update y j (-(y j))) := by
          rw [hdecomp]
      _ ≤ N.gauge b (c₁ • y) + N.gauge b (c₂ • Function.update y j (-(y j))) :=
          N.gauge_add_le b _ _
      _ = c₁ * N.gauge b y
          + c₂ * N.gauge b (Function.update y j (-(y j))) := by
          rw [N.gauge_real_smul, N.gauge_real_smul, abs_of_nonneg hc₁0,
            abs_of_nonneg hc₂0]
      _ = c₁ * N.gauge b y + c₂ * N.gauge b y := by
          rw [N.gauge_neg_single]
      _ = N.gauge b y := by
          rw [← add_mul, hsum, one_mul]

/-- **Coordinatewise monotonicity of the gauge** on nonnegative vectors. -/
theorem gauge_mono (b : OrthonormalBasis (Fin n) 𝕜 E) {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    N.gauge b x ≤ N.gauge b y := by
  -- Induct on the number of coordinates where `x` and `y` disagree.
  have H : ∀ d (y : Fin n → ℝ),
      (Finset.univ.filter fun i => x i ≠ y i).card ≤ d → (∀ i, x i ≤ y i) →
      N.gauge b x ≤ N.gauge b y := by
    intro d
    induction d with
    | zero =>
      intro y hcard _
      have hemp : (Finset.univ.filter fun i => x i ≠ y i) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hxy_eq : x = y := funext fun i => by
        by_contra hne
        have hi : i ∈ Finset.univ.filter fun i => x i ≠ y i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        rw [hemp] at hi
        simp at hi
      rw [hxy_eq]
    | succ d ih =>
      intro y hcard hxy
      by_cases hx_eq : x = y
      · rw [hx_eq]
      · have hne : (Finset.univ.filter fun i => x i ≠ y i).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          refine hx_eq (funext fun i => ?_)
          by_contra hne
          have hi : i ∈ Finset.univ.filter fun i => x i ≠ y i :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hemp] at hi
          simp at hi
        obtain ⟨j, hj⟩ := hne
        set y' := Function.update y j (x j) with hy'def
        have hstep : N.gauge b y' ≤ N.gauge b y := by
          refine N.gauge_update_le b ?_
          rw [abs_of_nonneg (hx0 j)]
          exact hxy j
        have hxy' : ∀ i, x i ≤ y' i := fun i => by
          rcases eq_or_ne i j with rfl | hij
          · rw [hy'def, Function.update_self]
          · rw [hy'def, Function.update_of_ne hij]
            exact hxy i
        have hsub : (Finset.univ.filter fun i => x i ≠ y' i)
            ⊆ (Finset.univ.filter fun i => x i ≠ y i).erase j := by
          intro i hi
          obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
          have hij : i ≠ j := by
            rintro rfl
            exact hine (by rw [hy'def, Function.update_self])
          refine Finset.mem_erase.mpr
            ⟨hij, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          rw [hy'def, Function.update_of_ne hij] at hine
          exact hine
        have hcard' : (Finset.univ.filter fun i => x i ≠ y' i).card ≤ d := by
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem hj
          omega
        exact le_trans (ih y' hcard' hxy') hstep
  exact H _ y le_rfl hxy

/-! ### The T-transform descent -/

/-- **The T-transform descent on the gauge** — the engine of Fan dominance.
If `z` is antitone and nonnegative, `y` is nonnegative, and every prefix sum
of `z` is dominated by the corresponding prefix sum of `y`, then
`Φ_N(z) ≤ Φ_N(y)`.

No total-sum equality is assumed, no majorization completion and no
Hardy–Littlewood–Pólya theorem is used: each descent step averages `y` with a
transposition of itself, which costs one triangle inequality, one
homogeneity, and one swap invariance of the gauge. -/
theorem gauge_le_gauge_of_prefix_sums_le (b : OrthonormalBasis (Fin n) 𝕜 E)
    {z y : Fin n → ℝ} (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y i) :
    N.gauge b z ≤ N.gauge b y := by
  -- Induct on the number of coordinates where `z` and `y` disagree.
  have H : ∀ d (y : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ y i).card ≤ d → (∀ i, 0 ≤ y i) →
      (∀ m : ℕ,
        ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
          ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y i) →
      N.gauge b z ≤ N.gauge b y := by
    intro d
    induction d with
    | zero =>
      intro y hcard _ _
      have hemp : (Finset.univ.filter fun i => z i ≠ y i) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hzy : z = y := funext fun i => by
        by_contra hne
        have hi : i ∈ Finset.univ.filter fun i => z i ≠ y i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        rw [hemp] at hi
        simp at hi
      rw [hzy]
    | succ d ih =>
      intro y hcard hy0 hpre
      by_cases hall : ∀ i, z i ≤ y i
      · exact N.gauge_mono b hz0 hall
      push Not at hall
      -- `l`: the least index where `y` drops below `z`.
      have hSne : (Finset.univ.filter fun i : Fin n => y i < z i).Nonempty :=
        hall.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      set l := (Finset.univ.filter fun i : Fin n => y i < z i).min' hSne
        with hldef
      have hlS : y l < z l :=
        (Finset.mem_filter.mp
          ((Finset.univ.filter fun i : Fin n => y i < z i).min'_mem hSne)).2
      have hlmin : ∀ i, i < l → z i ≤ y i := by
        intro i hil
        by_contra hzy
        push Not at hzy
        exact absurd
          (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy⟩))
          (not_le.mpr hil)
      -- Prefix domination at `l + 1` produces `j < l` with `z j < y j`.
      have hexj : ∃ j, j < l ∧ z j < y j := by
        by_contra h
        push Not at h
        have heq : ∀ i, i < l → z i = y i := fun i hi =>
          le_antisymm (hlmin i hi) (h i hi)
        have hp := hpre ((l : ℕ) + 1)
        have hset : (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) + 1)
            = insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ))
            := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert]
          constructor
          · intro hi
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
            · exact Or.inl (Fin.ext heq')
            · exact Or.inr hlt
          · rintro (rfl | hi)
            · omega
            · omega
        have hlnot :
            l ∉ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) := by
          simp
        rw [hset, Finset.sum_insert hlnot, Finset.sum_insert hlnot] at hp
        have hsum_eq :
            ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ), z i
              = ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ),
                  y i := by
          refine Finset.sum_congr rfl fun i hi => heq i ?_
          exact Fin.lt_def.mpr (Finset.mem_filter.mp hi).2
        rw [hsum_eq] at hp
        linarith
      obtain ⟨j, hjl, hzj⟩ := hexj
      have hjl_ne : j ≠ l := ne_of_lt hjl
      have hjl_nat : (j : ℕ) < (l : ℕ) := Fin.lt_def.mp hjl
      have hzlj : z l ≤ z j := hz_anti hjl.le
      have hylj : y l < y j := by linarith
      -- The transform: move `δ` from coordinate `j` to coordinate `l`.
      set δ : ℝ := min (y j - z j) (z l - y l) with hδdef
      have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
      have hδ₁ : δ ≤ y j - z j := min_le_left _ _
      have hδ₂ : δ ≤ z l - y l := min_le_right _ _
      have hδlt : δ < y j - y l := lt_of_le_of_lt hδ₁ (by linarith)
      have hyjl_pos : 0 < y j - y l := by linarith
      set c₂ : ℝ := δ / (y j - y l) with hc₂def
      have hc₂pos : 0 < c₂ := div_pos hδpos hyjl_pos
      have hc₂lt : c₂ < 1 := (div_lt_one hyjl_pos).mpr hδlt
      have hc₂mul : c₂ * (y j - y l) = δ :=
        div_mul_cancel₀ δ (ne_of_gt hyjl_pos)
      set y' : Fin n → ℝ :=
        Function.update (Function.update y j (y j - δ)) l (y l + δ)
        with hy'def
      have hy'j : y' j = y j - δ := by
        rw [hy'def, Function.update_of_ne hjl_ne, Function.update_self]
      have hy'l : y' l = y l + δ := by rw [hy'def, Function.update_self]
      have hy'i : ∀ i, i ≠ j → i ≠ l → y' i = y i := fun i hij hil => by
        rw [hy'def, Function.update_of_ne hil, Function.update_of_ne hij]
      -- (i) `y'` is a convex combination of `y` and its `(j l)`-swap.
      have hcomb : y' = (1 - c₂) • y + c₂ • (y ∘ Equiv.swap j l) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Function.comp_apply]
        rcases eq_or_ne i j with rfl | hij
        · rw [hy'j, Equiv.swap_apply_left]
          linear_combination hc₂mul
        rcases eq_or_ne i l with rfl | hil
        · rw [hy'l, Equiv.swap_apply_right]
          linear_combination -hc₂mul
        · rw [hy'i i hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
          ring
      -- (ii) `y'` stays nonnegative.
      have hy'0 : ∀ i, 0 ≤ y' i := by
        intro i
        rcases eq_or_ne i j with heq | hij
        · rw [heq, hy'j]
          linarith [hz0 j]
        rcases eq_or_ne i l with heq | hil
        · rw [heq, hy'l]
          linarith [hy0 l]
        · rw [hy'i i hij hil]
          exact hy0 i
      -- (iii) prefix domination survives the transform.
      have hpre' : ∀ m : ℕ,
          ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
            ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y' i := by
        intro m
        rcases le_or_gt m (j : ℕ) with hmj | hmj
        · -- Neither `j` nor `l` lies in the prefix: sums unchanged.
          have hcong : ∀ i ∈ (Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m), y' i = y i := by
            intro i hi
            have hivm : (i : ℕ) < m := (Finset.mem_filter.mp hi).2
            have hij : i ≠ j := fun h => by subst h; omega
            have hil : i ≠ l := fun h => by subst h; omega
            exact hy'i i hij hil
          rw [Finset.sum_congr rfl hcong]
          exact hpre m
        rcases le_or_gt m (l : ℕ) with hml | hml
        · -- `j` in, `l` out: the prefix of `y'` lost exactly `δ`, but the
          -- prefix gap was already at least `y j − z j ≥ δ`.
          have hcong : ∀ i ∈ (Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m),
              y' i = Function.update y j (y j - δ) i := by
            intro i hi
            have hivm : (i : ℕ) < m := (Finset.mem_filter.mp hi).2
            have hil : i ≠ l := fun h => by subst h; omega
            rw [hy'def, Function.update_of_ne hil]
          have hjmem : j ∈ Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmj⟩
          rw [Finset.sum_congr rfl hcong, Finset.sum_update_of_mem hjmem]
          have hysplit : ∑ i ∈ Finset.univ.filter
                fun i : Fin n => (i : ℕ) < m, y i
              = y j + ∑ i ∈ (Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m) \ {j}, y i := by
            rw [← Finset.erase_eq]
            exact (Finset.add_sum_erase _ y hjmem).symm
          have hterm : y j - z j ≤ ∑ i ∈ Finset.univ.filter
              (fun i : Fin n => (i : ℕ) < m), (y i - z i) := by
            refine Finset.single_le_sum (f := fun i => y i - z i) ?_ hjmem
            intro i hi
            have hivm : (i : ℕ) < m := (Finset.mem_filter.mp hi).2
            have hil : i < l := Fin.lt_def.mpr (by omega)
            linarith [hlmin i hil]
          rw [Finset.sum_sub_distrib] at hterm
          linarith [hpre m]
        · -- Both `j` and `l` in the prefix: the transform is sum-preserving.
          have hjmem : j ∈ Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          have hlmem : l ∈ Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hml⟩
          have hjmem' : j ∈ (Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m) \ {l} :=
            Finset.mem_sdiff.mpr ⟨hjmem, by simp [hjl_ne]⟩
          have hEq : ∑ i ∈ Finset.univ.filter
                fun i : Fin n => (i : ℕ) < m, y' i
              = ∑ i ∈ Finset.univ.filter
                fun i : Fin n => (i : ℕ) < m, y i := by
            have h1 : ∑ i ∈ Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m, y' i
                = (y l + δ) + ∑ i ∈ (Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l},
                    Function.update y j (y j - δ) i := by
              rw [hy'def]
              exact Finset.sum_update_of_mem hlmem _ _
            have h2 : ∑ i ∈ (Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m) \ {l},
                  Function.update y j (y j - δ) i
                = (y j - δ) + ∑ i ∈ ((Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l}) \ {j}, y i :=
              Finset.sum_update_of_mem hjmem' _ _
            have h3 : ∑ i ∈ Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m, y i
                = y l + ∑ i ∈ (Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l}, y i := by
              rw [← Finset.erase_eq]
              exact (Finset.add_sum_erase _ y hlmem).symm
            have h4 : ∑ i ∈ (Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m) \ {l}, y i
                = y j + ∑ i ∈ ((Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l}) \ {j}, y i := by
              rw [← Finset.erase_eq, ← Finset.erase_eq]
              exact (Finset.add_sum_erase _ y (by rwa [Finset.erase_eq])).symm
            rw [h1, h2, h3, h4]
            ring
          rw [hEq]
          exact hpre m
      -- (iv) the transform kills at least one disagreement.
      have hsub : (Finset.univ.filter fun i => z i ≠ y' i)
          ⊆ Finset.univ.filter fun i => z i ≠ y i := by
        intro i hi
        obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
        have hij : i ≠ j := by
          rintro rfl
          exact absurd heq hzj.ne
        have hil : i ≠ l := by
          rintro rfl
          exact absurd heq hlS.ne'
        exact hine (by rw [hy'i i hij hil]; exact heq)
      have hwitness : ∃ w ∈ Finset.univ.filter fun i => z i ≠ y i,
          w ∉ Finset.univ.filter fun i => z i ≠ y' i := by
        rcases min_choice (y j - z j) (z l - y l) with hmin | hmin
        · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
          have hj' : y' j = z j := by
            rw [hy'j, hδdef, hmin]
            ring
          simp [hj']
        · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
          have hl' : y' l = z l := by
            rw [hy'l, hδdef, hmin]
            ring
          simp [hl']
      have hcard' : (Finset.univ.filter fun i => z i ≠ y' i).card ≤ d := by
        have hlt := Finset.card_lt_card
          ((Finset.ssubset_iff_of_subset hsub).mpr hwitness)
        omega
      -- (v) one descent step does not increase the gauge; recurse.
      have hstep : N.gauge b y' ≤ N.gauge b y := by
        rw [hcomb]
        calc N.gauge b ((1 - c₂) • y + c₂ • (y ∘ Equiv.swap j l))
            ≤ N.gauge b ((1 - c₂) • y)
              + N.gauge b (c₂ • (y ∘ Equiv.swap j l)) :=
              N.gauge_add_le b _ _
          _ = (1 - c₂) * N.gauge b y + c₂ * N.gauge b y := by
              rw [N.gauge_real_smul, N.gauge_real_smul,
                abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - c₂),
                abs_of_nonneg hc₂pos.le, N.gauge_perm]
          _ = N.gauge b y := by ring
      exact le_trans (ih y' hcard' hy'0 hpre') hstep
  exact H _ y le_rfl hy0 hpre

/-! ### The Fan dominance principle -/

/-- **The Fan dominance principle** (Ky Fan; Bhatia IV.2.2): if every Ky Fan
sum of `A` is dominated by the corresponding Ky Fan sum of `B`, then
`N A ≤ N B` for *every* unitarily invariant norm `N`. -/
theorem apply_le_of_kyFanSum_le {A B : E →ₗ[𝕜] E}
    (h : ∀ k, kyFanSum k A ≤ kyFanSum k B) : N A ≤ N B := by
  have hanti : Antitone fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ) :=
    fun i j hij => A.singularValues_antitone (Fin.le_def.mp hij)
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) B]
  refine N.gauge_le_gauge_of_prefix_sums_le (stdOrthonormalBasis 𝕜 E) hanti
    (fun i => A.singularValues_nonneg _) (fun i => B.singularValues_nonneg _)
    fun m => ?_
  rcases le_or_gt m (finrank 𝕜 E) with hm | hm
  · rw [sum_filter_lt_eq_sum_fin hm fun k => A.singularValues k,
      sum_filter_lt_eq_sum_fin hm fun k => B.singularValues k,
      ← kyFanSum_eq_sum_fin, ← kyFanSum_eq_sum_fin]
    exact h m
  · have huniv : (Finset.univ.filter
        fun i : Fin (finrank 𝕜 E) => (i : ℕ) < m) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
    rw [huniv, ← kyFanSum_eq_sum_fin, ← kyFanSum_eq_sum_fin]
    exact h _

/-- Unitarily invariant norms are `star`-invariant: `N (A⋆) = N A`.  Via the
gauge representation and `σ(A⋆) = σ(A)`. -/
theorem apply_adjoint (A : E →ₗ[𝕜] E) : N A.adjoint = N A := by
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A.adjoint,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A]
  simp only [singularValues_adjoint]

/-! ### The operator-ideal property -/

/-- **The ideal property (left factor).**  If `‖C y‖ ≤ c ‖y‖` for `0 ≤ c`, then
`N (C ∘ₗ X) ≤ c * N X` for every unitarily invariant norm.  From Fan dominance
applied to the singular-value domination `σᵢ(C ∘ X) ≤ c σᵢ(X)`. -/
theorem apply_comp_le {C X : E →ₗ[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (C ∘ₗ X) ≤ c * N X :=
  calc N (C ∘ₗ X)
      ≤ N (((c : 𝕜)) • X) :=
        N.apply_le_of_kyFanSum_le fun k =>
          kyFanSum_le_of_singularValues_le (fun i => by
            rw [singularValues_real_smul X hc i]
            exact singularValues_comp_le hc hC X i) k
    _ = c * N X := by rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]

/-- **The ideal property (right factor).**  If `‖C y‖ ≤ c ‖y‖` for `0 ≤ c`, then
`N (X ∘ₗ C) ≤ N X * c`. -/
theorem apply_comp_le' {X C : E →ₗ[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (X ∘ₗ C) ≤ N X * c :=
  calc N (X ∘ₗ C)
      ≤ N (((c : 𝕜)) • X) :=
        N.apply_le_of_kyFanSum_le fun k =>
          kyFanSum_le_of_singularValues_le (fun i => by
            rw [singularValues_real_smul X hc i]
            exact singularValues_comp_le' hc hC i) k
    _ = N X * c := by rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc, mul_comm]

/-! ### The Frobenius (Hilbert–Schmidt) unitarily invariant norm

`‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)` over any orthonormal basis is a unitarily invariant
norm: subadditivity is the Minkowski inequality on `EuclideanSpace`, absolute
homogeneity is pointwise, and two-sided unitary invariance is
`sum_sq_norm_apply_unitary_comp` on the right and `LinearIsometryEquiv.norm_map`
on the left.  This is the norm the paper's `…_hilbertSchmidt` bounds use, and it
instantiates the every-UI-norm Davis–Kahan theorems to the Frobenius vocabulary
(plan step OP2). -/

/-- `√(∑ (fᵢ + gᵢ)²) ≤ √(∑ fᵢ²) + √(∑ gᵢ²)` for nonnegative real vectors: the
Minkowski inequality, obtained from `EuclideanSpace`'s triangle inequality by
transporting `f, g` across `WithLp.equiv`. -/
private theorem sqrt_sum_add_sq_le {m : ℕ} (f g : Fin m → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2)
      ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  let x : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm f
  let y : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm g
  have hnx : ‖x‖ = Real.sqrt (∑ i, f i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show x i = f i from rfl, Real.norm_eq_abs, sq_abs])
  have hny : ‖y‖ = Real.sqrt (∑ i, g i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show y i = g i from rfl, Real.norm_eq_abs, sq_abs])
  have hnxy : ‖x + y‖ = Real.sqrt (∑ i, (f i + g i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [PiLp.add_apply, show x i = f i from rfl, show y i = g i from rfl,
        Real.norm_eq_abs, sq_abs])
  rw [← hnx, ← hny, ← hnxy]
  exact norm_add_le x y

/-- **The Frobenius (Hilbert–Schmidt) norm as a unitarily invariant norm.**
`A ↦ √(∑ᵢ ‖A bᵢ‖²)` over the standard orthonormal basis. -/
noncomputable def frobenius (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : UnitarilyInvariantNorm 𝕜 E where
  toFun A := Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
  add_le' A B := by
    have hmono : Real.sqrt (∑ i, ‖(A + B) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        ≤ Real.sqrt (∑ i, (‖A (stdOrthonormalBasis 𝕜 E i)‖
            + ‖B (stdOrthonormalBasis 𝕜 E i)‖) ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [LinearMap.add_apply]; exact norm_add_le _ _
    exact hmono.trans (sqrt_sum_add_sq_le _ _)
  smul' a A := by
    have h : ∀ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2
        = ‖a‖ ^ 2 * ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := fun i => by
      rw [LinearMap.smul_apply, norm_smul, mul_pow]
    rw [show (∑ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        = ‖a‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => h i,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)]
  invariant' U V A := by
    have key : ∀ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2
        = ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 := fun i => by
      rw [show (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) (stdOrthonormalBasis 𝕜 E i)
          = U (A (V (stdOrthonormalBasis 𝕜 E i))) from rfl, U.norm_map]
    rw [show (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        = ∑ i, ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 from
        Finset.sum_congr rfl fun i _ => key i,
      sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)]

variable (𝕜 E) in
/-- **Basis independence of the Frobenius norm.**  `‖A‖_F = √(∑ₖ ‖A bₖ‖²)` for
*any* orthonormal basis `b`, not just the standard one — both sides equal
`√(∑ σₖ²)` by `sum_sq_singularValues`. -/
theorem frobenius_apply (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius 𝕜 E A = Real.sqrt (∑ k, ‖A (b k)‖ ^ 2) := by
  subst hn
  show Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) = _
  rw [← sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E),
    ← sum_sq_singularValues A rfl b]

variable (𝕜 E) in
/-- The squared Frobenius norm as a column-norm sum — the `‖A‖²_F` vocabulary of
the paper's Hilbert–Schmidt bounds. -/
theorem frobenius_sq (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius 𝕜 E A ^ 2 = ∑ k, ‖A (b k)‖ ^ 2 := by
  rw [frobenius_apply 𝕜 E A hn b,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

end UnitarilyInvariantNorm

end ForMathlib
