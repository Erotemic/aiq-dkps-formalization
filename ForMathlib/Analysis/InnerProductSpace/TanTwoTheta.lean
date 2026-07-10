/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`TanTwoTheta.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step G2.1 of
`dev/davis-kahan-expert-completion-plan.md`.

Groundwork for the subspace Davis–Kahan tan 2Θ theorem: the *vanishing-pinch*
hypothesis — the perturbation has no diagonal block with respect to a subspace
`U` and its orthogonal complement — expressed as an operator identity.  If
`⟪u, H u'⟫ = 0` for all `u, u' ∈ U`, then `P ∘ H ∘ P = 0` where `P` is the
orthogonal projection onto `U`; equivalently, the `U`-diagonal blocks of two
operators differing by such an `H` agree, `P S P = P T P`.  Applying the same
statement to `Uᗮ` gives the off-diagonal block identity `(1−P) S (1−P) =
(1−P) T (1−P)`.  These are the block hypotheses of `tan_two_theta_le_of_mem`
(`RotationSharp.lean`) promoted to the subspace level; the tan 2Θ headline that
consumes them is deferred to the G2 statement gate.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.RotationSharp

/-! # The subspace tan 2Θ theorem: block identities and the gated statement

## Statement cross-check (statement-first gate, plan step G2.0)

The classical subspace tan 2Θ theorem, as recorded verbatim in
Grubišić–Kostrykin–Makarov–Veselić, *The Tan 2Θ theorem for indefinite
quadratic forms* (arXiv:1006.3190, Introduction), quoting Davis–Kahan (1970):
let `A± ≻ 0` be strictly positive bounded operators on `H±`, `W` bounded from
`H₋` to `H₊`, and

`A = [[A₊, 0], [0, −A₋]]`, `B = A + V = [[A₊, W], [W⋆, −A₋]]`

with respect to `H = H₊ ⊕ H₋`.  Then

`‖tan 2Θ‖ ≤ 2 ‖V‖ / d`  **and**  `spec(Θ) ⊂ [0, π/4)`,

where `Θ` is the operator angle between `Ran E_A(ℝ₊)` and `Ran E_B(ℝ₊)` and
`d = dist(spec A₊, spec (−A₋))`.  Equivalently (their eq. (1.2)):
`‖P − Q‖ ≤ sin (½ arctan (2‖V‖/d))`, which implies `‖P − Q‖ < √2/2`.
Distinctive features, mirrored exactly here:

* **the perturbation is off-diagonal** (vanishing pinch) — this is what buys
  `tan` over `sin`: the angle stays *strictly below* `π/4` no matter how large
  `‖V‖` is, so `tan 2Θ` never meets its pole.  The pole question raised at the
  gate is thereby resolved: at the subspace level no `|cos 2Θ|`
  absolute-value bookkeeping is needed (unlike the per-vector
  `tan_two_theta_le`, where a single eigenvector from the *other* spectral
  component sits at angle `> π/4`);
* **subordinated spectra**: the two diagonal blocks sit on opposite sides of
  a gap (here: quadratic form of `T` is `≥ b` on `U`, `≤ a` on `Uᗮ`), the
  classical hypothesis — not the general two-component separation of the
  KMM-school generalizations;
* **both sides' spectral bounds**: the hypotheses on the perturbed pair
  `(S, V)` mirror those on `(T, U)` with the *same* `a, b`.  This is not a
  loss of faithfulness: off-diagonal perturbations repel spectrum away from
  the gap (GKMV Theorem 2.4(ii): the whole interval `(a, b)` stays in the
  resolvent of `S`), so the matching spectral subspace of `S` satisfies these
  bounds automatically.  That *spectral repulsion* step is filed separately
  (plan step G2.2a), keeping the headline conditional and clean;
* the classical statement is **operator-norm**; DK III state the sin 2Θ
  theorem in every unitarily invariant norm, but the tan 2Θ record here is
  op-norm — a UI-norm upgrade is not asserted by the sources we checked and
  is therefore not part of the gated statement;
* sharpness: for `T = diag(1, −1)`, `H = [[0, w], [w, 0]]` the bound is an
  equality (`tan 2θ = w = 2‖H‖/d`), and `θ → π/4` only as `w → ∞`.

The conclusion is encoded pole-free through `t := ‖P − P̂‖ = sin θ_max`:
`t² < 1/2` (the strict `π/4` bound) and
`(b − a) · 2t√(1−t²) ≤ 2ε · (1 − 2t²)` (i.e. `δ sin 2Θ ≤ 2ε cos 2Θ`), which
together are equivalent to `tan 2θ_max ≤ 2ε/(b − a)`.

## Main results

* `ForMathlib.starProjection_comp_comp_starProjection_eq_zero`: a perturbation
  with vanishing `U`-diagonal form compresses to zero, `P ∘ H ∘ P = 0`.
* `ForMathlib.starProjection_comp_comp_starProjection_congr`: two operators
  whose `U`-diagonal forms agree have equal `U`-diagonal blocks,
  `P ∘ S ∘ P = P ∘ T ∘ P`.
* `ForMathlib.tan_two_theta_norm_sub_le` (**stub**, plan step G2.2): the
  subspace tan 2Θ theorem, gated statement above.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* L. Grubišić, V. Kostrykin, K. A. Makarov, K. Veselić, *The Tan 2Θ theorem
  for indefinite quadratic forms*, J. Spectr. Theory 3 (2013); arXiv:1006.3190.
* A. Seelmann, *Notes on the sin 2Θ theorem*, Integr. Equ. Oper. Theory 79
  (2014); arXiv:1310.2036 (for the operator-angle formalism).
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **A perturbation with vanishing `U`-diagonal form compresses to zero.**  If
`⟪u, H u'⟫ = 0` for all `u, u' ∈ U`, then `P ∘ H ∘ P = 0`, `P` the orthogonal
projection onto `U`.  (Only the right-slot vanishing is used: `H (P x)` lands in
`Uᗮ`, which `P` then kills.) -/
theorem starProjection_comp_comp_starProjection_eq_zero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {H : E →ₗ[𝕜] E}
    (hH : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0) :
    (U.starProjection : E →ₗ[𝕜] E) ∘ₗ H ∘ₗ (U.starProjection : E →ₗ[𝕜] E) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  exact fun u hu => hH u hu _ (U.starProjection_apply_mem x)

/-- **Equal `U`-diagonal forms give equal `U`-diagonal blocks.**  If
`⟪u, S u'⟫ = ⟪u, T u'⟫` for all `u, u' ∈ U`, then `P ∘ S ∘ P = P ∘ T ∘ P`.
Applying this to `Uᗮ` yields the complementary block identity
`(1−P) ∘ S ∘ (1−P) = (1−P) ∘ T ∘ (1−P)` (`Submodule.starProjection_orthogonal`).
This is the operator form of the vanishing-pinch hypothesis of
`tan_two_theta_le_of_mem`. -/
theorem starProjection_comp_comp_starProjection_congr
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {S T : E →ₗ[𝕜] E}
    (h : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, S u'⟫_𝕜 = ⟪u, T u'⟫_𝕜) :
    (U.starProjection : E →ₗ[𝕜] E) ∘ₗ S ∘ₗ (U.starProjection : E →ₗ[𝕜] E)
      = (U.starProjection : E →ₗ[𝕜] E) ∘ₗ T ∘ₗ (U.starProjection : E →ₗ[𝕜] E) := by
  have hH : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, (S - T) u'⟫_𝕜 = 0 := fun u hu u' hu' => by
    rw [LinearMap.sub_apply, inner_sub_right, h u hu u' hu', sub_self]
  have hzero := starProjection_comp_comp_starProjection_eq_zero U hH
  rw [← sub_eq_zero]
  have hexp : (U.starProjection : E →ₗ[𝕜] E) ∘ₗ S ∘ₗ (U.starProjection : E →ₗ[𝕜] E)
      - (U.starProjection : E →ₗ[𝕜] E) ∘ₗ T ∘ₗ (U.starProjection : E →ₗ[𝕜] E)
      = (U.starProjection : E →ₗ[𝕜] E) ∘ₗ (S - T) ∘ₗ (U.starProjection : E →ₗ[𝕜] E) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [hexp, hzero]

section Headline

variable [FiniteDimensional 𝕜 E] [CompleteSpace E] {T S : E →ₗ[𝕜] E}

/-- **The subspace Davis–Kahan tan 2Θ theorem (gated statement, plan step
G2.2; proof pending).**  `T, S` symmetric; `U` a `T`-invariant subspace with
the form of `T` at least `b` on `U` and at most `a` on `Uᗮ`; `V` an
`S`-invariant subspace with the mirrored bounds for `S` (discharged for the
spectral choice of `V` by spectral repulsion, plan step G2.2a); the
perturbation `S − T` **off-diagonal** with respect to `U ⊕ Uᗮ` (vanishing
pinch) and of norm at most `ε`.  Conclusion, with
`t := ‖P − P̂‖ = sin θ_max`: the angle stays strictly below `π/4`
(`t² < 1/2`) and `(b − a) sin 2θ_max ≤ 2 ε cos 2θ_max` — together,
`tan 2θ_max ≤ 2ε/(b − a)`.  See the module docstring for the
literature cross-check. -/
theorem tan_two_theta_norm_sub_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b ε : ℝ} (hab : a < b) (hε0 : 0 ≤ ε)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hVb : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜)
    (hVa : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2 < 1 / 2 ∧
      (b - a) * (2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖
          * Real.sqrt (1 - ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2))
        ≤ 2 * ε * (1 - 2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2) := by
  sorry

end Headline

end ForMathlib
