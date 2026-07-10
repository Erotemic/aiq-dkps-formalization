/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`TanTheta.lean`).

Statement gate by Claude Fable 5 (claude-fable-5[1m]), plan step G3.0 of
`dev/davis-kahan-expert-completion-plan.md`; proof pending (plan step G3).

The Davis–Kahan tan Θ theorem: one symmetric operator, one exact invariant
subspace `V` whose complementary spectrum sits in a strip `[α, β]`, one
arbitrary test subspace `Z` of the same dimension whose compression has
spectrum at distance `≥ (β−α)/2 + δ` from the strip's midpoint; conclusion
`tan ∠(Z, V) ≤ ‖residual‖ / δ`, stated per test vector so that the tangent's
pole never appears.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.PrincipalAngles

/-! # The Davis–Kahan tan Θ theorem (gated statement)

## Statement cross-check (statement-first gate, plan step G3.0)

The tan Θ theorem is recorded in finite-dimensional, matrix-precise form in
A. K. Motovilov, *Comment on 'The tan θ theorem with relaxed conditions', by
Y. Nakatsukasa* (arXiv:1204.4441), Propositions 1 and 4, which we quote:

*Proposition 1 (KMM 2005, Thm 2).*  Let the Hermitian `L = [[A₁, Bᴴ], [B, A₂]]`
be block-partitioned with `A₁ ∈ ℂᵏˣᵏ`.  Let `spec(A₁) ⊆ (−∞, α−δ] ∪ [β+δ, ∞)`
with `α ≤ β`, `δ > 0`.  Let `L₁, L₂` be complementary orthogonal reducing
subspaces of `L` with `dim L₁ = k` and `spec(L|_{L₂}) ⊆ [α, β]`, and let `𝒜₁`
be the first-`k`-coordinates subspace.  Then `tan ∠(𝒜₁, L₁) ≤ ‖B‖/δ`.

*Proposition 4 (Nakatsukasa's Theorem 1; residual form, equivalent).*  For a
Hermitian `A`, orthonormal `Q₁ ∈ ℂⁿˣᵏ`, `A₁ := Q₁ᴴAQ₁`,
`R := AQ₁ − Q₁A₁`; if `spec(A₁) ⊆ (−∞, α−δ] ∪ [β+δ, ∞)` and the complementary
exact spectrum `spec(Λ₂) ⊆ [α, β]`, then `tan ∠(ran Q₁, ran X₁) ≤ ‖R‖/δ`.

Points the gate had to settle, and how the sources settle them:

* **`cos Θ` invertibility (`∠ < π/2`) is a *conclusion*, not a hypothesis**:
  Motovilov's Lemma 3 shows `𝒜₁ ∩ L₂ = 𝒜₂ ∩ L₁ = {0}` follows from the
  spectral hypotheses in finite dimension (via
  `‖(L − c)y‖ ≥ ((β−α)/2 + δ)‖y‖` on `𝒜₁` against `≤ (β−α)/2 ‖y‖` on `L₂`).
  Our per-vector encoding absorbs this: `δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` for
  `x ∈ Z` forces `P_V x = 0 → x = 0`, so no inverse or tangent operator is
  ever formed and the pole never appears.
* **Two-sided outside condition**: the test compression's spectrum may sit on
  *both* sides of the strip (Nakatsukasa's relaxation); as Motovilov shows it
  is already contained in KMM 2005 for the spectral norm.  We adopt it: the
  hypothesis is coercivity of `A₁ − c` at distance `(β−α)/2 + δ` from the
  midpoint `c := (α+β)/2`, not a one-sided bound.
* **Which subspace is exact**: `V` (the `L₁`) is exactly invariant for `T`,
  with the *complementary* spectrum confined to the strip; the test subspace
  `Z` is arbitrary of the same finite rank.  `dim Z = dim V` is essential.
* **Norms**: spectral norm (the largest principal angle).  A
  unitarily-invariant-norm version is not part of the record checked here
  and is not asserted.
* The per-vector conclusion `∀ x ∈ Z, δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` is
  equivalent to `tan θ_max ≤ ρ/δ` (for equal dimensions,
  `sin θ_max = max_{x ∈ Z, unit} ‖(1 − P_V)x‖` and the vectorwise
  angle-to-`V` is maximized at `θ_max`); `ρ` bounds the residual columnwise,
  `‖T x − P_Z (T x)‖ ≤ ρ ‖x‖` on `Z`, which is `‖B‖ ≤ ρ` in Proposition 1's
  block notation and `‖R‖ ≤ ρ` in Proposition 4's.

## Main results

* `ForMathlib.tan_theta_le` (**stub**, plan step G3): the tan Θ theorem in the
  per-vector, pole-free form.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* V. Kostrykin, K. A. Makarov, A. K. Motovilov, *On the existence of solutions
  to the operator Riccati equation and the tan θ theorem*, Integr. Equ. Oper.
  Theory 51 (2005), 121–140.
* Y. Nakatsukasa, *The tan θ theorem with relaxed conditions*, Linear Algebra
  Appl. 436 (2012), 1528–1534.
* A. K. Motovilov, *Comment on 'The tan θ theorem with relaxed conditions'*,
  arXiv:1204.4441.
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] {T : E →ₗ[𝕜] E}

/-- **The Davis–Kahan tan Θ theorem (gated statement, plan step G3; proof
pending).**  `T` symmetric; `V` a `T`-invariant subspace whose complementary
form sits in the strip `[α, β]`; `Z` a test subspace with `dim Z = dim V`
whose compression `A₁ := P_Z T|_Z` is coercive at distance `(β−α)/2 + δ` from
the strip's midpoint; `ρ` a columnwise bound on the residual
`T x − P_Z (T x)` over `Z`.  Then every test vector satisfies
`δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` — the per-vector, pole-free form of
`tan ∠(Z, V) ≤ ρ/δ`, which in particular forces `Z ∩ Vᗮ = 0` (Motovilov's
Lemma 3).  See the module docstring for the literature cross-check. -/
theorem tan_theta_le (hT : T.IsSymmetric)
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V) (hdim : finrank 𝕜 Z = finrank 𝕜 V)
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZ : ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖
      ≤ ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : 𝕜) • x‖)
    (hVa : ∀ x ∈ Vᗮ, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hVb : ∀ x ∈ Vᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  sorry

end ForMathlib
