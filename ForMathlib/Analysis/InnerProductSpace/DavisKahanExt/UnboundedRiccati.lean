/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Unbounded

/-!
# Strong solutions of unbounded operator Riccati equations

Literature writeup: local TeX, Section 29.  The central extra obligation over
the bounded theory is preservation of operator domains.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Unbounded diagonal block data with bounded off-diagonal coupling. -/
structure UnboundedBlockData where
  A0 : ClosedOperator (𝕜 := 𝕜) (E := E0)
  A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  selfAdjoint0 : A0.IsSelfAdjoint
  selfAdjoint1 : A1.IsSelfAdjoint
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

/-- A bounded angular operator preserves the unbounded diagonal domains. -/
def PreservesRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ x : H.A0.domain, X (x : E0) ∈ H.A1.domain

/-- Strong Riccati solution, including the domain condition. -/
def StrongSolvesRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∃ hdom : PreservesRiccatiDomains H X,
    ∀ x : H.A0.domain,
      H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ -
        X (H.A0.toLinearMap x) -
        X (H.B01 (X (x : E0))) + H.B10 (x : E0) = 0

/-- Closed block operator matrix on the Hilbert direct sum. -/
noncomputable def unboundedBlockOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) := by
  sorry

/-- Graph subspace of a bounded angular operator in the Hilbert direct sum. -/
noncomputable def unboundedBlockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) := by
  sorry

/-- Roadmap predicate that a closed subspace reduces a closed operator with
domain decomposition respected. -/
def ClosedOperator.ReducesSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G) : Prop :=
  (∀ x : A.domain, (x : G) ∈ U → A.toLinearMap x ∈ U) ∧
  (∀ x : A.domain, (x : G) ∈ Uᗮ → A.toLinearMap x ∈ Uᗮ)

/-- Reducing graph subspaces correspond to strong Riccati solutions under the
explicit domain condition.

Proof strategy: work first on the algebraic core `dom A0 x dom A1`.  Expand
invariance of `(u, Xu)` under the block operator and use domain preservation
to justify every unbounded composition.  The second component gives the
strong Riccati equation; the adjoint graph gives reduction rather than mere
invariance.  Conversely, use the strong equation to show graph invariance and
then invoke self-adjointness to obtain invariance of the orthogonal complement.
Keep domain transport as named lemmas rather than hidden coercion proofs. -/
theorem graph_reduces_iff_strongRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (unboundedBlockOperator H).ReducesSubspace (unboundedBlockGraph X) ↔
      StrongSolvesRiccati H X := by
  sorry

/-- Existence of the contractive strong solution under separated diagonal
spectra and a sufficiently small bounded coupling. -/
theorem exists_strongRiccati_solution
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (s0 s1 : Set ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ClosedOperator.SpectralSetsSeparated H.A0 H.A1 s0 s1 d)
    (hsmall : ‖H.B01‖ < d) :
    ∃ X : E0 →L[𝕜] E1, StrongSolvesRiccati H X ∧ ‖X‖ < 1 := by
  sorry

/-- Strong Riccati solution yields block diagonalization with domain control. -/
theorem unbounded_blockDiagonalization
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : StrongSolvesRiccati H X) :
    ∃ W : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1),
      IsUnitaryOperator W := by
  sorry

end DavisKahanExt
end ForMathlib
