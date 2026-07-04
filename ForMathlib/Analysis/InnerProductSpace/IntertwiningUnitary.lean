/-
Staged for Mathlib: a new `Mathlib/Analysis/InnerProductSpace/IntertwiningUnitary.lean`.

SKELETON (`/develop` Phase 1e Step 2.5, Milestone 2): every declaration stated with `sorry`.
`lake build` must pass (sorries are warnings). Bodies are filled by `/beastmode` tickets PD-13..PD-17.
-/

import ForMathlib.Analysis.InnerProductSpace.PolarDecomposition
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # The canonical intertwining (matching) unitary (Milestone 2)

Given two complete orthogonal families of projections `{Pⱼ}`, `{P'ⱼ}` on a finite-dimensional inner
product space, with the non-degeneracy hypothesis "`Pⱼ x ≠ 0 ⟹ P'ⱼ Pⱼ x ≠ 0`", Davis constructs the
canonical unitary
`U Pⱼ = (P'ⱼ Pⱼ P'ⱼ)^{-1/2} P'ⱼ Pⱼ = P'ⱼ (Pⱼ P'ⱼ Pⱼ)^{-1/2} Pⱼ`,  with  `U Pⱼ = P'ⱼ U`,
the polar factor of `P'ⱼ Pⱼ` on each block. It measures the rotation of the spectral resolution.

Source: **Davis (1963)**, "The Rotation of Eigenvectors by a Perturbation", §2, lines 217–312
(`ForMathlib/prose/non-distributable/Davis-1963-...tex`); digest §2. This unblocks Davis Result B
(BL3/BL4) in `.mathlib-quality/decomposition-B.md`.

The block polar factors are the invertible-case polar decomposition
(`ForMathlib.polarUnitaryEquiv`) of `P'ⱼ Pⱼ` restricted to `range Pⱼ`.

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
  sorry

/-- A spectral projection is a projection (`IsStarProjection`). -/
theorem isStarProjection_spectralProjection (b : OrthonormalBasis (Fin n) 𝕜 E)
    (S : Finset (Fin n)) : IsStarProjection (spectralProjection b S) :=
  sorry

/-- Spectral projections onto disjoint index sets are orthogonal. -/
theorem spectralProjection_comp_of_disjoint (b : OrthonormalBasis (Fin n) 𝕜 E)
    {S T : Finset (Fin n)} (h : Disjoint S T) :
    spectralProjection b S ∘ₗ spectralProjection b T = 0 :=
  sorry

/-- The spectral projections over a partition of `Fin n` sum to `1`. -/
theorem spectralProjection_univ (b : OrthonormalBasis (Fin n) 𝕜 E) :
    spectralProjection b Finset.univ = 1 :=
  sorry

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

/-- **Non-degeneracy** (Davis's hypothesis): no nonzero vector in `range (P j)` is annihilated by
`P' j`. Equivalently `P'ⱼ Pⱼ` is injective on `range Pⱼ`. -/
def OrthoProjFamily.NonDegenerate (P P' : OrthoProjFamily 𝕜 E m) : Prop :=
  ∀ j, ∀ x, P.proj j x = x → x ≠ 0 → P'.proj j x ≠ 0

/-! ### The block polar factor (ticket PD-14, PD-15) -/

/-- **Block invertibility (PD-14):** under non-degeneracy, `P'ⱼ Pⱼ` is injective on `range Pⱼ`, so
`(P'ⱼ Pⱼ P'ⱼ)^{-1/2}` exists on `range P'ⱼ`. Davis §2 line 224. -/
theorem OrthoProjFamily.injOn_of_nonDegenerate {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') (j : Fin m) :
    Set.InjOn (P'.proj j ∘ₗ P.proj j) (range (P.proj j)) :=
  sorry

/-- **Block polar factor (PD-15):** the polar factor of `P'ⱼ Pⱼ` is a unitary
`range Pⱼ ≃ₗᵢ range P'ⱼ` — the invertible-case polar decomposition on the block. Davis §2 line 221. -/
noncomputable def OrthoProjFamily.blockPolar {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') (j : Fin m) :
    ↥(range (P.proj j)) ≃ₗᵢ[𝕜] ↥(range (P'.proj j)) :=
  sorry

/-! ### The intertwining unitary (ticket PD-16) -/

/-- **The canonical intertwining unitary** `U({Pⱼ},{P'ⱼ})`, assembled from the block polar factors.
`U Pⱼ = (P'ⱼ Pⱼ P'ⱼ)^{-1/2} P'ⱼ Pⱼ`. Davis §2, lines 217–229. -/
noncomputable def OrthoProjFamily.intertwiningUnitary {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') : E ≃ₗᵢ[𝕜] E :=
  sorry

/-- **The intertwining property** `U Pⱼ = P'ⱼ U`. Davis §2 line 229. -/
theorem OrthoProjFamily.intertwiningUnitary_comp_proj {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') (j : Fin m) :
    ((OrthoProjFamily.intertwiningUnitary hnd : E →ₗ[𝕜] E)) ∘ₗ P.proj j
      = P'.proj j ∘ₗ (OrthoProjFamily.intertwiningUnitary hnd : E →ₗ[𝕜] E) :=
  sorry

/-- `U` maps `range Pⱼ` into `range P'ⱼ` (it acts there as the block polar factor). -/
theorem OrthoProjFamily.intertwiningUnitary_mapsTo {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') (j : Fin m) {x : E} (hx : x ∈ range (P.proj j)) :
    OrthoProjFamily.intertwiningUnitary hnd x ∈ range (P'.proj j) :=
  sorry

/-! ### Rotation-angle interpretation (ticket PD-17) — needed by Davis Result B (BL4)

`θᵢ = arccos ⟨U xᵢ, xᵢ⟩` for `xᵢ` an orthonormal basis adapted to `{Pⱼ}`; the "sum of squared
sines" `∑ᵢ (1 - ‖⟨U xᵢ, xᵢ⟩‖²)` is the Frobenius off-diagonal size `‖𝒞⊥ U‖²_F`. Stated here at the
inner-product level (the pinching/Frobenius identification joins the parent Result-B infrastructure
in Milestone 3). Davis §2, lines 265–312. -/

/-- The squared sine of the `i`-th rotation angle, `sin²θᵢ = 1 - ‖⟨U xᵢ, xᵢ⟩‖²`. -/
noncomputable def OrthoProjFamily.sqSinAngle {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') (b : OrthonormalBasis (Fin n) 𝕜 E) (i : Fin n) : ℝ :=
  1 - ‖(⟪b i, OrthoProjFamily.intertwiningUnitary hnd (b i)⟫_𝕜 : 𝕜)‖ ^ 2

/-- **Angle interpretation (PD-17):** the total squared rotation `∑ᵢ sin²θᵢ` equals
`(finrank) - ∑ᵢ ‖⟨U xᵢ, xᵢ⟩‖²`, the pinch-off-diagonal Frobenius size of `U`. Davis §2 line 276.
(The `‖𝒞⊥ U‖²_F` identification is completed in Milestone 3 against the parent's Frobenius setup.) -/
theorem OrthoProjFamily.sum_sqSinAngle {P P' : OrthoProjFamily 𝕜 E m}
    (hnd : P.NonDegenerate P') (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ i, OrthoProjFamily.sqSinAngle hnd b i
      = (n : ℝ) - ∑ i, ‖(⟪b i, OrthoProjFamily.intertwiningUnitary hnd (b i)⟫_𝕜 : 𝕜)‖ ^ 2 :=
  sorry

end ForMathlib
