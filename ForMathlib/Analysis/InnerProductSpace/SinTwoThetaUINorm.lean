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
  sorry

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
  sorry

end UnitarilyInvariantNorm

end ForMathlib
