/-
Staged for Mathlib: addition to `Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # `LinearIsometryEquiv.ofEq` on subtype elements

`LinearIsometryEquiv.ofEq` is the identity on underlying elements.  The existing
`coe_ofEq_apply` says so after coercion to the ambient space; this `rfl` variant keeps
the result in subtype form, so `simp` can push `ofEq` through explicit `Subtype.mk`s.
That matters when the result is fed to another bundled map (as in the Gram-rigidity
composites in `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean`), where no
ambient coercion is available for `coe_ofEq_apply` to rewrite under.
-/

namespace ForMathlib

variable {E R' : Type*} [SeminormedAddCommGroup E] [Ring R'] [Module R' E]
  {p q : Submodule R' E}

@[simp]
theorem LinearIsometryEquiv.ofEq_apply_mk (h : p = q) (x : E) (hx : x ∈ p) :
    LinearIsometryEquiv.ofEq p q h ⟨x, hx⟩ = ⟨x, h ▸ hx⟩ :=
  rfl

end ForMathlib
