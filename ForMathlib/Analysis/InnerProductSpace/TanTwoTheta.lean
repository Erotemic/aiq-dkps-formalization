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

/-! # Vanishing-pinch block identities for the subspace tan 2Θ theorem

## Main results

* `ForMathlib.starProjection_comp_comp_starProjection_eq_zero`: a perturbation
  with vanishing `U`-diagonal form compresses to zero, `P ∘ H ∘ P = 0`.
* `ForMathlib.starProjection_comp_comp_starProjection_congr`: two operators
  whose `U`-diagonal forms agree have equal `U`-diagonal blocks,
  `P ∘ S ∘ P = P ∘ T ∘ P`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
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

end ForMathlib
