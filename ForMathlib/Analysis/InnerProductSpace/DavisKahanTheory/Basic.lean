/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.PrincipalAngles
import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm
import ForMathlib.Analysis.InnerProductSpace.PolarDecomposition

/-!
# Canonical objects for the finite-dimensional Davis--Kahan theory

This file is the common statement layer for the complete finite-dimensional
Davis--Kahan programme.  Some declarations are intentionally scaffolded as open
obligations: they record the basis-independent objects and exact theorem shapes
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

/-- The modulus `|A| = (A⋆A)^{1/2}` has the same singular values as `A`: both
Gram operators coincide, `|A|⋆|A| = |A|² = A⋆A`.  This is the finite-dimensional
`σ(|A|) = σ(A)` used to identify difference-of-projector singular values with the
`sin Θ` operator's. -/
theorem singularValues_abs (A : E →ₗ[𝕜] E) :
    (ForMathlib.abs A).singularValues = A.singularValues := by
  refine ForMathlib.singularValues_eq_of_gram_eq ?_
  rw [(ForMathlib.isPositive_abs A).adjoint_eq, ForMathlib.abs_mul_self]

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

/-- `cos Θ` on the full ambient space, `|P_V P_U|`.  Its singular values are the
principal-angle cosines (`singularValues_abs` and `singularValues_cosThetaMap`). -/
noncomputable def cosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  ForMathlib.abs (cosThetaMap U V)

/-- `sin Θ` on the full ambient space, the modulus `|P_U - P_V|` of the projector
difference.  This is the symmetric full-space sine operator; its singular values
are those of `P_U - P_V` (`singularValues_projection_sub_projection`). -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  ForMathlib.abs (projection U - projection V)

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

/-- Principal-angle cosines: the singular values of the cross projection
`P_V P_U`, sorted decreasingly and padded by zeros beyond the finite rank.  These
are symmetric in `U, V` because `(P_V P_U)⋆ = P_U P_V` (`principalCosines_comm`). -/
noncomputable def principalCosines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (cosThetaMap U V).singularValues

/-- Principal-angle sines: the singular values of the directed cross projection
`P_{Vᗮ} P_U`.  In equal-dimension configurations these are the sines of the
principal angles; when `dim U ≠ dim V` the directed map also records the
`π/2` "defect" directions, so this is not symmetric in `U, V` in general. -/
noncomputable def principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (sinThetaMap U V).singularValues

/-- Principal angles as a sorted finitely supported sequence: `arcsin` applied to
the principal sines.  `arcsin 0 = 0` keeps the support finite. -/
noncomputable def principalAngles (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (principalSines U V).mapRange Real.arcsin Real.arcsin_zero

/-- Principal-angle tangents: `tan` applied to the principal angles.  `tan 0 = 0`
keeps the support finite (poles at `π/2` are only reached in the non-acute
configuration, excluded by the tangent theorems' hypotheses). -/
noncomputable def principalTangents (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (principalAngles U V).mapRange Real.tan Real.tan_zero

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

/-! ### Restriction to an invariant subspace and the restricted-spectrum bridge

These give the concrete restriction `A.restrict hU : U →ₗ[𝕜] U` of an operator to
an invariant subspace and identify its full point spectrum with the `U`-carried
point spectrum of `A`.  This is the bridge used to discharge the spectral
hypotheses of the residual/perturbation `sin Θ` theorems on the subtype. -/

/-- The restriction of a symmetric operator to an invariant subspace is
symmetric (mathlib's `LinearMap.IsSymmetric.restrict_invariant`, restated for the
`Reduces` predicate). -/
theorem isSymmetric_restrict {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : Reduces A U) :
    (A.restrict hU).IsSymmetric :=
  hA.restrict_invariant hU

/-- **The restricted-spectrum bridge.**  The point spectrum of the restriction
`A.restrict hU : U →ₗ[𝕜] U` (over the whole `⊤`) equals the `U`-carried point
spectrum of `A`.  Eigenvectors transport across the subtype coercion. -/
theorem restrictedSpectrum_restrict (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : Reduces A U) :
    restrictedSpectrum (A.restrict hU) ⊤ = restrictedSpectrum A U := by
  ext lam
  constructor
  · rintro ⟨x, -, hx0, hxEig⟩
    refine ⟨(x : E), x.2, fun hx => hx0 (Subtype.ext hx), ?_⟩
    have h := congrArg (Subtype.val) hxEig
    rwa [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h
  · rintro ⟨x, hxU, hx0, hxEig⟩
    refine ⟨⟨x, hxU⟩, Submodule.mem_top, fun hxu => hx0 (congrArg Subtype.val hxu), ?_⟩
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, Submodule.coe_smul]
    exact hxEig

/-- The containment form of the restricted-spectrum bridge: `A.restrict hU` has
spectrum in `s` iff `A` carries spectrum in `s` on `U`. -/
theorem spectrumIn_restrict_iff (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : Reduces A U) (s : Set ℝ) :
    SpectrumIn (A.restrict hU) ⊤ s ↔ SpectrumIn A U s := by
  unfold SpectrumIn
  rw [restrictedSpectrum_restrict]

/-- **A symmetric operator commutes with the projection onto a reducing
subspace.**  For `A` symmetric and `U` an `A`-invariant subspace (so `Uᗮ` is
invariant too), `P_U (A x) = A (P_U x)`. -/
theorem projection_apply_comm_of_reduces {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U) (x : E) :
    projection U (A x) = A (projection U x) := by
  have hUperp : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hApx : A (U.starProjection x) ∈ U := hU _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hUperp _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    rw [← map_add]; congr 1; abel
  show U.starProjection (A x) = A (U.starProjection x)
  rw [hsplit, map_add, U.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest, add_zero]

/-- The complementary projection onto `Uᗮ` also commutes with `A` when `A` is
symmetric and `U` reduces `A`. -/
theorem complementaryProjection_apply_comm_of_reduces {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (x : E) :
    complementaryProjection U (A x) = A (complementaryProjection U x) :=
  projection_apply_comm_of_reduces hA (reduces_orthogonal_of_isSymmetric hA hU) x

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

Design note (open obligation).  With the directed-sine convention
`principalAngles = arcsin ∘ principalSines`, this equality is *false without an
equal-dimension hypothesis*: when `dim U ≠ dim V` the directed sine map
`P_{Vᗮ} P_U` records the `π/2` "defect" directions of the larger subspace, which
have no counterpart in `P_{Uᗮ} P_V`.  Concretely, for `U = span{e₁, e₂}` and
`V = span{e₁}` in a 3-dimensional space, `principalAngles U V = {π/2, 0, …}` while
`principalAngles V U = {0, …}`.

The symmetric object is the *cosine* spectrum: `principalCosines_comm` proves
`principalCosines U V = principalCosines V U` unconditionally, since
`(P_V P_U)⋆ = P_U P_V`.  A fully symmetric `principalAngles` would have to be built
from those cosines with the min-dimension multiplicity convention (arccos on the
common `min (dim U) (dim V)` angles), not from the directed sine map.  Completing
this needs either that redesign of `principalAngles` or an added
`finrank 𝕜 U = finrank 𝕜 V` hypothesis; left as an open obligation for that
decision. -/
theorem principalAngles_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    principalAngles U V = principalAngles V U := by
  sorry

/-- Principal-angle cosines are the singular values of `P_V P_U` (definitional:
`principalCosines` is defined as those singular values). -/
theorem singularValues_cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (cosThetaMap U V).singularValues = principalCosines U V :=
  rfl

/-- Principal-angle sines are the singular values of `P_{Vᗮ} P_U` (definitional:
`principalSines` is defined as those singular values). -/
theorem singularValues_sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (sinThetaMap U V).singularValues = principalSines U V :=
  rfl

/-- Principal-angle cosines are symmetric in the two subspaces, since
`(P_V P_U)⋆ = P_U P_V` and adjoints share singular values.  (The sines are *not*
symmetric when `dim U ≠ dim V`; see `principalSines`.) -/
theorem principalCosines_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    principalCosines U V = principalCosines V U := by
  have hadj : (cosThetaMap V U).adjoint = cosThetaMap U V := by
    rw [eq_comm, LinearMap.eq_adjoint_iff]
    intro x y
    simp only [cosThetaMap, projection, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [V.inner_starProjection_left_eq_right, U.inner_starProjection_left_eq_right]
  rw [principalCosines, principalCosines, ← hadj, ForMathlib.singularValues_adjoint]

/-- The singular values of `P_U-P_V` are the full-space `sin Θ` values: with
`sinAngleOperator = |P_U - P_V|` and `σ(|T|) = σ(T)` (`singularValues_abs`). -/
theorem singularValues_projection_sub_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (projection U - projection V).singularValues =
      (sinAngleOperator U V).singularValues := by
  rw [sinAngleOperator, singularValues_abs]

/-- **A unitarily invariant norm depends only on the singular-value sequence.**
Via the gauge representation `apply_eq_gauge` of the operator SVD. -/
theorem _root_.ForMathlib.UnitarilyInvariantNorm.eq_of_singularValues_eq
    (N : UnitarilyInvariantNorm 𝕜 E) {A B : E →ₗ[𝕜] E}
    (h : A.singularValues = B.singularValues) : N A = N B := by
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) B, h]

/-- **The full projector-difference UI-norm bridge.**  Every unitarily invariant
norm of `P_U - P_V` equals that of the full `sin Θ` operator `|P_U - P_V|`, since
they share the singular-value sequence.  This is the only projection-geometry
rewrite the final UI-norm projector theorem needs. -/
theorem uiNorm_projection_sub_eq_sinAngleOperator (N : UnitarilyInvariantNorm 𝕜 E)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    N (projection U - projection V) = N (sinAngleOperator U V) :=
  N.eq_of_singularValues_eq (singularValues_projection_sub_projection U V)

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

Open obligation.  The clean route needs the two-projection (CS) decomposition
identity `‖P_U - P_V‖ = ‖P_{Vᗮ} P_U‖` at equal rank, which the flat
`SinThetaOpNorm` layer does not yet expose in this operator-equality form (it
provides the one-sided bound and the largest-angle identification, but not the
projector-difference/directed-map norm coincidence).  Left incomplete pending
that two-projection norm identity. -/
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

Open obligation.  With the directed-sine `principalAngles`, this reduces to
`singularValues (P_{Vᗮ} P_U) = singularValues (P_V P_{Uᗮ})` at equal rank, i.e.
the two-projection statement that complementation preserves the sine spectrum.
That decomposition lemma is not yet available in the flat layer; left incomplete
pending it (or a redesign of `principalAngles` through the symmetric cosine
spectrum, cf. `principalAngles_comm`). -/
theorem principalAngles_orthogonal (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    principalAngles Uᗮ Vᗮ = principalAngles U V := by
  sorry

/-- Family-level principal angles agree with the canonical submodule API: the
subspace cosine spectrum of `span u, span v` is the family-level
`cosPrincipalAngles`.  Both are singular values of the same cross projection
`P_{span v} P_{span u}`, via the flat cosine dictionary
`singularValues_starProjection_comp_starProjection`. -/
theorem principalCosines_span_eq_cosPrincipalAngles {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    principalCosines (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) =
      cosPrincipalAngles hu hv := by
  have hcomp : cosThetaMap (Submodule.span 𝕜 (Set.range u)) (Submodule.span 𝕜 (Set.range v))
      = (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
    rfl
  rw [principalCosines, hcomp,
    ForMathlib.singularValues_starProjection_comp_starProjection hu hv,
    cosPrincipalAngles_comm hv hu]

end DavisKahanTheory
end ForMathlib
