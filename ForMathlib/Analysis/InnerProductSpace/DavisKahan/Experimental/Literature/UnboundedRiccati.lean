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

noncomputable instance unboundedBlockGraph_hasOrthogonalProjection
    (X : E0 →L[𝕜] E1) :
    (unboundedBlockGraph X).HasOrthogonalProjection := by
  sorry

/-- Roadmap predicate that a closed subspace reduces a closed operator with
domain decomposition respected. -/
def ClosedOperator.InvariantSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G) : Prop :=
  ∀ x : A.domain, (x : G) ∈ U → A.toLinearMap x ∈ U

/-- A closed subspace reduces a closed operator and the domain splits under
the two orthogonal projections. -/
def ClosedOperator.ReducesSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G)
    [U.HasOrthogonalProjection] : Prop :=
  (∀ x : A.domain, U.starProjection (x : G) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : G) ∈ A.domain) ∧
  A.InvariantSubspace U ∧ A.InvariantSubspace Uᗮ


/-- Two closed operators on the same Hilbert space are unitarily equivalent
with explicit transport of domains and operator actions. -/
def ClosedOperator.UnitaryEquivalent
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A B : ClosedOperator (𝕜 := 𝕜) (E := G))
    (W Winv : G →L[𝕜] G) : Prop :=
  IsUnitaryOperator W ∧ IsUnitaryOperator Winv ∧
  Winv ∘L W = ContinuousLinearMap.id 𝕜 G ∧
  W ∘L Winv = ContinuousLinearMap.id 𝕜 G ∧
  ∃ hWdom : ∀ x : A.domain, W (x : G) ∈ B.domain,
  ∃ hWinvdom : ∀ y : B.domain, Winv (y : G) ∈ A.domain,
    (∀ x : A.domain,
      B.toLinearMap ⟨W (x : G), hWdom x⟩ = W (A.toLinearMap x)) ∧
    (∀ y : B.domain,
      A.toLinearMap ⟨Winv (y : G), hWinvdom y⟩ = Winv (B.toLinearMap y))

/-- Closed block-diagonal representative obtained from a reducing graph. -/
noncomputable def unboundedBlockDiagonalOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) := by
  sorry

/-- Reducing graph subspaces correspond to strong Riccati solutions under the
explicit domain condition.

Proof strategy: work first on the algebraic core `dom A0 x dom A1`.  Expand
invariance of `(u, Xu)` under the block operator and use domain preservation
to justify every unbounded composition.  The second component gives the
strong Riccati equation; the adjoint graph gives reduction rather than mere
invariance.  Conversely, use the strong equation to show graph invariance and
then invoke self-adjointness to obtain invariance of the orthogonal complement.
Keep domain transport as named lemmas rather than hidden coercion proofs. 

Lean proof route for a weaker agent:

1. Describe domain elements in the graph as `(u,Xu)` with `u∈dom A0`; use `PreservesRiccatiDomains` to place `Xu` in `dom A1`.
2. Expand the two block components of the unbounded operator.
3. Equate the second component with `X` applied to the first; this is exactly the strong Riccati equation.
4. Reverse the calculation to prove graph invariance.


Ext-agent signature audit (GPT 5.6 High): Correctly states invariance, not reduction.
Domain preservation must remain explicit because it is not implied by the formal
algebraic Riccati expression.

Preferred dependency route: Track domains in every block calculation. Establish graph
invariance first, reduction second, and only then construct a domain-transporting
unitary equivalence.
-/
theorem graph_invariant_iff_strongRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      (unboundedBlockOperator H).InvariantSubspace (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  sorry

/-- Existence of the contractive strong solution under separated diagonal
spectra and a sufficiently small bounded coupling. 

Lean proof route for a weaker agent:

1. Construct the separated spectral subspace of the unbounded block operator by a Riesz projection.
2. Prove it is a graph over the first coordinate and obtain a bounded contractive angular operator.
3. Establish preservation of `dom A0` into `dom A1` from the resolvent representation and graph invariance.
4. Expand invariance on the operator domain to obtain the strong Riccati identity.


Ext-agent signature audit (GPT 5.6 High): A conservative local existence target. The
reduction conclusion additionally requires the adjoint-graph/domain decomposition; this
must be proved, not inferred from one-sided domain preservation alone.

Preferred dependency route: Track domains in every block calculation. Establish graph
invariance first, reduction second, and only then construct a domain-transporting
unitary equivalence.
-/
theorem exists_strongRiccati_solution
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (s0 s1 : Set ℝ) {d : ℝ} (hd : 0 < d)
    (hcover0 : H.A0.realSpectrum ⊆ s0) (hcover1 : H.A1.realSpectrum ⊆ s1)
    (hsep : ClosedOperator.SpectralSetsSeparated H.A0 H.A1 s0 s1 d)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccati H X ∧ ‖X‖ < 1 ∧
      (unboundedBlockOperator H).ReducesSubspace (unboundedBlockGraph X) := by
  sorry

/-- Strong Riccati solution yields block diagonalization with domain control. 

Lean proof route for a weaker agent:

1. Construct the graph rotation from `X` and the zero graph using the bounded direct-rotation formula.
2. Prove the rotation intertwines the corresponding graph projections.
3. Use `hX` and `graph_invariant_iff_strongRiccati` to obtain invariance of the target graph.
4. Record domain transport separately; the current conclusion packages the unitary and projection intertwining rather than claiming a vacuous unitary existence.


Ext-agent signature audit (GPT 5.6 High): The corrected conclusion states actual unitary
equivalence with two-way domain transport. `hred` is needed in addition to the one-sided
strong Riccati equation.

Preferred dependency route: Track domains in every block calculation. Establish graph
invariance first, reduction second, and only then construct a domain-transporting
unitary equivalence.
-/
theorem unbounded_blockDiagonalization
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : StrongSolvesRiccati H X)
    (hred : (unboundedBlockOperator H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1),
      ClosedOperator.UnitaryEquivalent
        (unboundedBlockOperator H) (unboundedBlockDiagonalOperator H X)
        W Winv ∧
      W ∘L projection (unboundedBlockGraph 0) =
        projection (unboundedBlockGraph X) ∘L W := by
  sorry

end DavisKahanExt
end ForMathlib
