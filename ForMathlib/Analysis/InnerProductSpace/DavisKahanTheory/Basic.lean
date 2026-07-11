/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.PrincipalAngles
import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

/-!
# Canonical objects for the finite-dimensional Davis--Kahan theory

This file is the common statement layer for the complete finite-dimensional
Davis--Kahan programme.  The declarations are intentionally scaffolded with
`sorry`: they record the basis-independent objects and exact theorem shapes
that the completed development should expose.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 2--5 (spectral blocks, residuals, and angle operators).
* `ForMathlib/prose/Davis-1963-core-arguments.tex`,
  Sections "Canonical matching of subspaces" and
  "The sharp two-subspace estimate".
* `papers/DavisKahan-formalized-vs-literature.tex`,
  Sections "Setup and notation" and "Extensions formalized since the first version".

The principal design choice is to make subspaces, rather than chosen
orthonormal bases, the public API.  Family-level results in
`PrincipalAngles.lean` should become implementation lemmas for this layer.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- A subspace reduces an operator when it is invariant.  For a symmetric
operator, invariance of `U` implies invariance of `Uᗮ`, so this is the right
finite-dimensional public predicate. -/
def Reduces (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

/-- A nonzero eigenvector of a symmetric operator at a real eigenvalue. -/
def IsEigenvectorAt (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) : Prop :=
  x ≠ 0 ∧ A x = (lam : 𝕜) • x

/-- The finite-dimensional point spectrum of `A` carried by `U`.

For symmetric operators this is the spectrum of the restriction to `U` once
`U` reduces `A`.  The definition avoids exposing a choice of restricted
coordinate space in theorem statements. -/
def restrictedSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ IsEigenvectorAt A lam x}

/-- Every eigenvalue of `A` carried by `U` lies in `Ω`. -/
def SpectrumIn (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Ω : Set ℝ) : Prop :=
  restrictedSpectrum A U ⊆ Ω

/-- Two restricted spectra are separated by at least `δ`. -/
def SpectraSeparated (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedSpectrum A U → μ ∈ restrictedSpectrum B V →
    δ ≤ |lam - μ|

/-- The mixed separation used by the `sin Θ` theorem: the selected block of
`A` is separated from the complementary block of `B`. -/
def HybridGap (A B : E →ₗ[𝕜] E) (U V : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  SpectraSeparated A U B Vᗮ δ

/-- Absolute separation between the two diagonal blocks of `A`.

This is the internal-gap hypothesis used by the structured double-angle
Davis--Kahan theorems.  For a general unstructured Sylvester equation,
absolute separation alone instead leads to the separate `π/2` estimate. -/
def InternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  SpectraSeparated A U A Uᗮ δ

/-- The interval/exterior form of the mixed gap. -/
def IntervalExteriorGap (A B : E →ₗ[𝕜] E) (U V : Submodule 𝕜 E)
    (a b δ : ℝ) : Prop :=
  SpectrumIn A U (Set.Icc a b) ∧
    SpectrumIn B Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- The one-sided gap used by the tangent theorems. -/
def OrderedGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →ₗ[𝕜] F) (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ lam μ, lam ∈ restrictedSpectrum A U → μ ∈ restrictedSpectrum B V →
    lam + δ ≤ μ

/-- Ordered separation of the two diagonal blocks of `A`, in either
orientation.  This stronger predicate is useful when reducing a double-angle
argument to the elementary ordered Sylvester theorem. -/
def OrderedInternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  OrderedGap A U A Uᗮ δ ∨ OrderedGap A Uᗮ A U δ

/-- Ordered block separation implies absolute block separation.

Lean proof route for a weaker agent:

1. Unfold `OrderedInternalGap`, `InternalGap`, and `SpectraSeparated`, then split the disjunction into its two orientations.
2. In each branch specialize the ordered inequality to the chosen eigenvalues and derive the corresponding real order with `linarith`.
3. Rewrite the absolute value using `abs_of_nonpos` or `abs_of_nonneg`, and finish the remaining scalar inequality with `linarith`.
-/
theorem OrderedInternalGap.internalGap {A : E →ₗ[𝕜] E}
    {U : Submodule 𝕜 E} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : OrderedInternalGap A U δ) : InternalGap A U δ := by
  intro lam μ hlam hμ
  rcases h with hlow | hhigh
  · have hle := hlow lam μ hlam hμ
    have hlam_le : lam ≤ μ := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hlam_le)]
    linarith
  · have hle := hhigh μ lam hμ hlam
    have hμ_le : μ ≤ lam := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hμ_le)]
    linarith

/-- Canonical finite-dimensional spectral subspace selected by a real set.

The eventual implementation should be basis-independent, but may be proved by
choosing `LinearMap.IsSymmetric.eigenvectorBasis` and showing independence of
that choice. -/
noncomputable def spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 {x | ∃ lam ∈ Ω, IsEigenvectorAt A lam x}

/-- Canonical orthogonal spectral projector. -/
noncomputable def spectralProjection (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    E →ₗ[𝕜] E :=
  ((spectralSubspace A Ω).starProjection : E →L[𝕜] E)

/-- The orthogonal projector onto a finite-dimensional subspace, as a linear
map. -/
noncomputable def projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →ₗ[𝕜] E :=
  ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)

/-- The complementary projector. -/
noncomputable def complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection Uᗮ

/-- The cosine cross-projection `P_V P_U`. -/
noncomputable def cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection V ∘ₗ projection U

/-- The sine cross-projection `P_{Vᗮ} P_U`. -/
noncomputable def sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  complementaryProjection V ∘ₗ projection U

/-- The one-sided tangent cross-map.  On the transverse part it is
`P_{Vᗮ} P_U (P_V P_U)⁻¹`. -/
noncomputable def tanThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- The full-space canonical angle operator `Θ(U,V)` of Davis--Kahan.
Its nonzero eigenvalues are the principal angles, with the multiplicities
required by the two-projection decomposition. -/
noncomputable def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- `cos Θ` on the full ambient space. -/
noncomputable def cosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- `sin Θ` on the full ambient space. -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- `tan Θ` on the full ambient space.  In non-acute configurations this is
understood as the Moore--Penrose/graph-operator extension on the transverse
part, with the pole recorded separately by `IsTransverse`. -/
noncomputable def tanAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- The one-sided finite-dimensional `sin (2 Θ)` map supported on `U`.

This normalization matches the classic Davis--Kahan UI-norm theorem:
`2 P_{Uᗮ} P_V P_U`.  A separate full positive angle operator would duplicate
nonzero singular values and should not be conflated with this map. -/
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  (2 : 𝕜) • (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)

/-- `tan (2 Θ)` on the full ambient space. -/
noncomputable def tanTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- Principal angles as a sorted finitely supported sequence. -/
noncomputable def principalAngles (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ := by
  sorry

/-- Principal-angle cosines, padded by zeros beyond the relevant finite rank. -/
noncomputable def principalCosines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ := by
  sorry

/-- Principal-angle sines. -/
noncomputable def principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ := by
  sorry

/-- Principal-angle tangents. -/
noncomputable def principalTangents (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ := by
  sorry

/-- The pair has no angle `π/2`; equivalently, `P_V` is injective on `U`. -/
def IsTransverse (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection] : Prop :=
  ∀ x ∈ U, V.starProjection x = 0 → x = 0

/-- The pair is acute in the Davis--Kahan sense. -/
def IsAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  (∀ x ∈ U, V.starProjection x = 0 → x = 0) ∧
    (∀ y ∈ V, U.starProjection y = 0 → y = 0)

/-- No principal angle is a quarter turn.  This is the natural domain condition
for `tan (2 Θ)` before the canonical branch is selected.  The arbitrary
reducing subspace in the raw `tan 2Θ` theorem may have angles on either side
of `π/4`; the theorem itself excludes equality. -/
def AvoidsQuarterTurn (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  ∀ i, principalAngles U V i ≠ Real.pi / 4

omit [FiniteDimensional 𝕜 E] in
/-- Acuteness is symmetric.

Lean proof route for a weaker agent:

1. Unfold `IsAcute`; the two projection-kernel clauses are exchanged.
2. Keep this direct and independent of the Ext hierarchy.
-/
theorem IsAcute.symm {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : IsAcute U V) : IsAcute V U :=
  ⟨h.2, h.1⟩

/-- The diagonal part (pinch) of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def pinch (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  projection U ∘ₗ H ∘ₗ projection U +
    complementaryProjection U ∘ₗ H ∘ₗ complementaryProjection U

/-- The off-diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def offDiagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  H - pinch U H

/-- Davis--Kahan's vanishing-pinch hypothesis. -/
def IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : Prop :=
  pinch U H = 0

/-- The weaker one-block condition used by the `tan Θ` theorem. -/
def HasZeroCompression (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : Prop :=
  projection U ∘ₗ H ∘ₗ projection U = 0

omit [FiniteDimensional 𝕜 E] in
/-- A vanishing pinch has a vanishing selected diagonal block.

Lean proof route for a weaker agent:

1. Unfold `IsOffDiagonal`, `pinch`, and `HasZeroCompression`.
2. Apply `LinearMap.ext`; for each vector, compose the zero-pinch identity with `projection U` on the left and right.
3. Simplify projection idempotence and `projection U ∘ complementaryProjection U = 0` to isolate the selected diagonal block.
-/
theorem hasZeroCompression_of_isOffDiagonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hoff : IsOffDiagonal U H) : HasZeroCompression U H := by
  unfold IsOffDiagonal at hoff
  unfold HasZeroCompression
  apply LinearMap.ext
  intro x
  have hP_idem (y : E) : projection U (projection U y) = projection U y := by
    change U.starProjection (U.starProjection y) = U.starProjection y
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hP_comp (y : E) : projection U (complementaryProjection U y) = 0 := by
    change U.starProjection (Uᗮ.starProjection y) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Uᗮ.starProjection_apply_mem y
  have h := congrArg (projection U) (LinearMap.congr_fun hoff x)
  simpa [pinch, LinearMap.comp_apply, hP_idem, hP_comp] using h

omit [FiniteDimensional 𝕜 E] in
/-- A vanishing pinch is unchanged when the two summands of the orthogonal
splitting are exchanged.

Lean proof route for a weaker agent:

1. Unfold `pinch`; exchanging `U` and `Uᗮ` merely swaps the two summands.
2. The matching infinite lemma should live in `DavisKahanExt.Basic` and the finite proof can later specialize it.
-/
theorem isOffDiagonal_orthogonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hoff : IsOffDiagonal U H) : IsOffDiagonal Uᗮ H := by
  unfold IsOffDiagonal at hoff ⊢
  simpa [pinch, projection, complementaryProjection, add_comm] using hoff

omit [FiniteDimensional 𝕜 E] in
/-- Operator-form zero compression implies the corresponding sesquilinear
block vanishes.

Lean proof route for a weaker agent:

1. Apply the compression equality to `u′`, use self-adjointness of the orthogonal projection to move it across the inner product, and simplify `P_U u = u`.
2. Obtain the projected-vector equality with `LinearMap.congr_fun hzero u'` before entering the inner-product calculation.
3. Finish with `Submodule.inner_starProjection_left_eq_right` and `inner_zero_right`.
-/
theorem inner_map_eq_zero_of_hasZeroCompression
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hzero : HasZeroCompression U H)
    {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U) : ⟪u, H u'⟫_𝕜 = 0 := by
  have hblock := LinearMap.congr_fun hzero u'
  have hproj : U.starProjection (H u') = 0 := by
    simpa [HasZeroCompression, projection,
      Submodule.starProjection_eq_self_iff.mpr hu'] using hblock
  calc
    ⟪u, H u'⟫_𝕜 = ⟪U.starProjection u, H u'⟫_𝕜 := by
      rw [Submodule.starProjection_eq_self_iff.mpr hu]
    _ = ⟪u, U.starProjection (H u')⟫_𝕜 :=
      U.inner_starProjection_left_eq_right u (H u')
    _ = 0 := by rw [hproj, inner_zero_right]

/-- Both diagonal sesquilinear blocks vanish for an off-diagonal map.

Lean proof route for a weaker agent:

1. Apply `hasZeroCompression_of_isOffDiagonal` to `U` and `Uᗮ`, then invoke `inner_map_eq_zero_of_hasZeroCompression` on each block.
2. Use `isOffDiagonal_orthogonal` to obtain the complementary zero-compression premise.
3. Build the conjunction explicitly so elaboration failures remain localized to one block.
-/
theorem inner_blocks_eq_zero_of_isOffDiagonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hoff : IsOffDiagonal U H) :
    (∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0) ∧
      (∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0) := by
  constructor
  · intro u hu u' hu'
    exact inner_map_eq_zero_of_hasZeroCompression U H
      (hasZeroCompression_of_isOffDiagonal U H hoff) hu hu'
  · intro w hw w' hw'
    exact inner_map_eq_zero_of_hasZeroCompression Uᗮ H
      (hasZeroCompression_of_isOffDiagonal Uᗮ H
        (isOffDiagonal_orthogonal U H hoff)) hw hw'

/-! ## Basis independence and elementary geometry -/

omit [FiniteDimensional 𝕜 E] in
/-- A symmetric operator leaves the orthogonal complement of an invariant
subspace invariant.

Lean proof route for a weaker agent:

1. Preferred route: specialize `DavisKahanExt.reduces_orthogonalComplement` after converting the finite linear map to a continuous linear map.
2. Until that bridge exists, the direct inner-product proof is only a few lines.
-/
theorem reduces_orthogonal_of_isSymmetric {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} (hU : Reduces A U) :
    Reduces A Uᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

omit [FiniteDimensional 𝕜 E] in
/-- The canonical spectral subspace reduces its operator.  Symmetry is not
needed for this algebraic fact; it is needed later for orthogonal reduction and
for completeness of the real eigenvector decomposition.

Lean proof route for a weaker agent:

1. Unfold `spectralSubspace` and `Reduces`, and fix a vector in the generated span.
2. Apply `Submodule.span_induction`; for each generator unpack its eigenvalue/eigenvector witness and rewrite `A x` as a scalar multiple of `x`.
3. Close the zero, addition, and scalar cases by linearity and the submodule closure rules.
-/
theorem reduces_spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    Reduces A (spectralSubspace A Ω) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨lam, hlam, hy⟩
    rw [hy.2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨lam, hlam, hy⟩)
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using (spectralSubspace A Ω).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using (spectralSubspace A Ω).smul_mem c hx

/-- The canonical projector has the expected range.

Lean proof route for a weaker agent:

1. Unfold `spectralProjection` and use the standard theorem that the range of `Submodule.starProjection` is the submodule.
2. Check the coercion from continuous linear maps to linear maps before applying `Submodule.range_starProjection`.
3. Close by exact equality rather than extensionality.
-/
theorem range_spectralProjection (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    LinearMap.range (spectralProjection A Ω) = spectralSubspace A Ω := by
  exact Submodule.range_starProjection (spectralSubspace A Ω)

omit [FiniteDimensional 𝕜 E] in
/-- Spectral selection is independent of the chosen eigenbasis.

Lean proof route for a weaker agent:

1. Unfold `spectralSubspace` and `restrictedSpectrum` only enough to expose the defining eigenvector span.
2. Attempt `rfl`; if reducible wrappers block it, use `simp only` with those definitions rather than extensional set reasoning.
3. Keep this theorem as the API bridge if `spectralSubspace` is later reimplemented through an eigenbasis or projector.
-/
theorem spectralSubspace_eq_span_eigenvectors (A : E →ₗ[𝕜] E)
    (Ω : Set ℝ) :
    spectralSubspace A Ω =
      Submodule.span 𝕜 {x | ∃ lam ∈ Ω, IsEigenvectorAt A lam x} :=
  rfl

/-- Principal angles are symmetric in the two subspaces.

Lean proof route for a weaker agent:

1. Rewrite `cosThetaMap V U` as the adjoint of `cosThetaMap U V` using self-adjointness of orthogonal projections.
2. Apply the theorem that a map and its adjoint have the same ordered singular values.
3. Rewrite both sides with `singularValues_cosThetaMap` and then apply `Real.arccos` pointwise to obtain equality of `principalAngles`.
-/
theorem principalAngles_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    principalAngles U V = principalAngles V U := by
  sorry

/-- Principal-angle cosines are the singular values of `P_V P_U`.

Lean proof route for a weaker agent:

1. Choose orthonormal bases of `U` and `V`, identify the ambient cross projection with the overlap matrix plus zero blocks, and reuse `PrincipalAngles.singularValues_starProjection_comp_starProjection`.
2. Prove a unitary-equivalence lemma between the ambient cross projection and the zero-extended overlap operator.
3. Rewrite singular values with unitary invariance and the existing family-level cosine dictionary.
-/
theorem singularValues_cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (cosThetaMap U V).singularValues = principalCosines U V := by
  sorry

/-- Principal-angle sines are the singular values of `P_{Vᗮ} P_U`.

Lean proof route for a weaker agent:

1. Reduce to the Pythagorean relation between the cosine and complementary cross projections on each principal plane, then transfer the sorted singular-value list.
2. Prove the Gram identity `M⋆M = P_U - P_U P_V P_U` for the sine cross map.
3. Read the eigenvalues through the cosine dictionary and simplify `sqrt (1-c²)`.
-/
theorem singularValues_sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (sinThetaMap U V).singularValues = principalSines U V := by
  sorry

/-- The singular values of `P_U-P_V` are the full-space `sin Θ` values.

Lean proof route for a weaker agent:

1. Specialize the bounded Ext identity `sinAngleOperator = |P_U-P_V|` after converting finite linear maps to continuous linear maps.
2. Use the finite theorem that `T` and `|T|` have the same singular values, transporting across the coercions.
3. Rewrite the finite `sinAngleOperator` definition and verify that both singular-value sequences use the same ambient-dimension padding.
-/
theorem singularValues_projection_sub_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (projection U - projection V).singularValues =
      (sinAngleOperator U V).singularValues := by
  sorry

/-- The one-sided double-angle map is exactly twice the cross block.

Lean proof route for a weaker agent:

1. Unfold `sinTwoAngleOperator`.
2. Close the goal with `rfl`.
3. Keep this theorem as the normalization bridge used by the reflection and
   UI-norm files; do not replace it by a full positive angle operator without
   also changing every downstream multiplicity convention.

Signature audit: Valid after defining `sinTwoAngleOperator` as the one-sided
classic Davis--Kahan map rather than a full-space positive operator.
-/
theorem sinTwoAngleOperator_eq_two_smul_cross (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinTwoAngleOperator U V =
      (2 : 𝕜) • (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) := by
  rfl

/-- Equal-rank subspaces have the same largest sine whether measured by a
cross projection or by the difference of projectors.

Lean proof route for a weaker agent:

1. Split on whether the cross-projection norm is strictly below one.
2. In the acute branch, specialize the Ext identities relating the gap norm, `sinAngleOperator`, and the directed cross projection.
3. In the norm-one branch, use equal finite rank to show the reverse directed gap also has norm one, then bound both projector norms from above by one.
-/
theorem opNorm_projection_sub_eq_opNorm_sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    ‖(projection U - projection V).toContinuousLinearMap‖ =
      ‖(sinThetaMap U V).toContinuousLinearMap‖ := by
  sorry

/-- Orthogonal complements preserve the nontrivial principal angles.

Lean proof route for a weaker agent:

1. Choose the canonical two-projection decomposition into common, defect, and generic principal planes.
2. Show orthogonal complementation swaps the two defect blocks and leaves every generic angle unchanged.
3. Use `hrank` to identify the defect multiplicities; zero-padding then gives equality of the finitely supported principal-angle sequences.

Signature audit: The equal-rank hypothesis fixes the defect multiplicities.  With the
finitely-supported convention, additional zero angles disappear automatically, while the
nonzero and `π/2` multiplicities agree under orthogonal complementation.
-/
theorem principalAngles_orthogonal (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    principalAngles Uᗮ Vᗮ = principalAngles U V := by
  sorry

/-- Family-level principal angles agree with the canonical submodule API.

Lean proof route for a weaker agent:

1. Extend the two orthonormal families to ambient orthonormal bases, identify the overlap matrix with the restricted cross projection, and reuse the family-level theorem in `PrincipalAngles.lean`.
2. Rewrite both sides through `singularValues_cosThetaMap` and the overlap-operator theorem.
3. Verify that the finite-support padding agrees beyond the family dimension.
-/
theorem principalCosines_span_eq_cosPrincipalAngles {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    principalCosines (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) =
      cosPrincipalAngles hu hv := by
  sorry

end DavisKahanTheory
end ForMathlib
