/-
# AIQ DKPS ForMathlib inventory challenge: Matrix spectral functions and entrywise eigenvalue bounds

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/Analysis/Matrix/EntrywiseOpNorm.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/PiL2.lean`
(the `ℓ¹ ≤ √card · ℓ²` bound) and `Mathlib/Analysis/Matrix/Normed.lean` (the
entrywise → `ℓ²`-operator-norm bound).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # `ℓ¹`–`ℓ²` and entrywise–operator norm comparisons

Two elementary norm comparisons that are absent from Mathlib (which has the
`ℓ²`-operator-norm API in `Mathlib/Analysis/CStarAlgebra/Matrix.lean` but no
bound of it by the entrywise norm):

* on `EuclideanSpace 𝕜 ι`, `∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖` (Cauchy–Schwarz /
  Chebyshev);
* for a real `n × n` matrix with entries bounded by `ε`, the induced Euclidean
  operator `Matrix.toEuclideanLin A` has `‖A x‖ ≤ n ε ‖x‖`.

## Main results

* `ForMathlib.sum_norm_le_sqrt_card_mul_norm`
* `ForMathlib.norm_toEuclideanLin_le_of_entry_le`

The matrix bound's constant `n` is loose (the Frobenius bound gives `√(card)`);
it is the form produced by an entrywise sup bound and consumed by operator-norm
spectral-perturbation arguments. TODO(RCLike): the matrix bound is stated over
`ℝ`; the `RCLike` generalization is routine (`‖A i j‖`, `RCLike.norm_ofReal`).
-/

namespace ForMathlib

open scoped BigOperators
open Matrix

/--
**`ℓ¹ ≤ √card · ℓ²` on Euclidean space.** For `x : EuclideanSpace 𝕜 ι`,
`∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖`.
-/
theorem sum_norm_le_sqrt_card_mul_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  sorry
theorem norm_toEuclideanLin_le_of_entry_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {ε : ℝ} (hentry : ∀ i j, |A i j| ≤ ε) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  sorry
end ForMathlib
/-!
## Source: `ForMathlib/Analysis/Matrix/SpectralFunctionMeasurable.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(measurability of a continuous spectral function of a measurable Hermitian-matrix
family).

Formalized by Claude Fable 5 (claude-fable-5[1m]); relocated/staged and
self-contained-ized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Measurability of a continuous spectral function of a Hermitian matrix family

For a fixed continuous `h : ℝ → ℝ`, the *spectral `h`-transform*
`specTransform h B = Σₖ h(λₖ) uₖ uₖᵀ` of a measurable Hermitian-matrix family is
measurable.  Equivalently (for `h` continuous) this is the matrix continuous
functional calculus `h(B)`; the point is that it is measurable in the *entrywise*
σ-algebra with **no measurable selection of an eigenbasis** — `B ↦ uₖ(B)` is
discontinuous at eigenvalue crossings, yet `specTransform h B` is the entrywise
pointwise limit of matrix *polynomials* `p(B)` (Stone–Weierstrass on a spectral
interval), each of which is an entrywise polynomial in the entries of `B`.

## Main results

* `ForMathlib.Matrix.specTransform`
* `ForMathlib.Matrix.measurable_specTransform` (excluded from this inventory for now;
  this staged theorem still needs API alignment with Mathlib continuous functional
  calculus / spectral-transform conventions before it is part of the claim set.)
-/

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open MeasureTheory Filter Polynomial Set

namespace ForMathlib.Matrix

variable {n : ℕ}

/-- `Matrix` is a type-level def, so the pi `MeasurableSpace` instance does not
fire on it automatically; register the entrywise σ-algebra (matching the pi
topology used by `continuous_aeval`).  (To be reconciled with Mathlib's matrix
measurable structure at PR time.) -/
instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

instance : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

/-- The symmetric-operator structure of `toEuclideanLin B` for a Hermitian `B`. -/
noncomputable def opSym {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    (Matrix.toEuclideanLin B).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hB

/-- The sorted (decreasing) eigenvalues of `toEuclideanLin B` for Hermitian `B`. -/
noncomputable def sortedEig {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    Fin n → ℝ :=
  (opSym hB).eigenvalues finrank_euclideanSpace_fin

/-- For continuous `h` and any radius/tolerance, there is a polynomial
uniformly close to `h` on `[-R, R]`. -/
theorem exists_polynomial_uniform_close (h : ℝ → ℝ) (hh : Continuous h)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc (-R) R, |h x - p.eval x| ≤ ε := by
  sorry
theorem abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  sorry
theorem abs_sortedEig_le_of_entry_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {β : ℝ} (hβ : ∀ i j, |B i j| ≤ β) (k : Fin n) :
    |sortedEig hB k| ≤ (n : ℝ) * β := by
  sorry
theorem pow_mulVec_eigenvector {B : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : B *ᵥ v = μ • v) (t : ℕ) :
    (B ^ t) *ᵥ v = (μ ^ t) • v := by
  sorry
theorem aeval_mulVec_eigenvector {B : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : B *ᵥ v = μ • v) (p : Polynomial ℝ) :
    (aeval B p) *ᵥ v = (p.eval μ) • v := by
  sorry
theorem mulVec_eigenvectorBasis {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (k : Fin n) :
    B *ᵥ WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k)
      = sortedEig hB k
          • WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k) := by
  sorry
theorem aeval_entry_eq_sum {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (p : Polynomial ℝ) (i j : Fin n) :
    (aeval B p) i j
      = ∑ k : Fin n, p.eval (sortedEig hB k)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j) := by
  sorry
noncomputable def specTransform (h : ℝ → ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin n, h (sortedEig hB k)
      * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
      * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j)

/-- Uniform approximation of the spectral transform by matrix polynomials, on
an entrywise-bounded set of matrices. -/
theorem abs_specTransform_sub_aeval_le (h : ℝ → ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {β ε : ℝ} (hβ : ∀ a b, |B a b| ≤ β)
    {p : Polynomial ℝ}
    (hp : ∀ x ∈ Set.Icc (-((n : ℝ) * β)) ((n : ℝ) * β), |h x - p.eval x| ≤ ε)
    (i j : Fin n) :
    |specTransform h hB i j - (aeval B p) i j| ≤ (n : ℝ) * ε := by
  sorry
/-
`ForMathlib.Matrix.measurable_specTransform` is intentionally not part of this
inventory challenge yet.  It comes from the most recent spectral-transform / CFC
measurability staging work and still needs statement/API review before being
presented as a claim.  The comparator inventory therefore skips it, while keeping
its supporting definitions and helper lemmas visible above.
-/
end ForMathlib.Matrix
/-!
## Source: `ForMathlib/Analysis/Matrix/EntrywiseEigenvalue.lean`
-/
/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(eigenvalue perturbation from entrywise closeness).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Eigenvalue perturbation from entrywise closeness

Weyl's inequality bounds the eigenvalue perturbation by the *operator* norm of the
difference.  Combined with the entrywise→operator-norm comparison
`‖toEuclideanLin A‖ ≤ n · (entrywise sup of A)`, this gives a directly usable
**entrywise** eigenvalue-perturbation bound: if two real symmetric `n × n`
matrices are entrywise `ε`-close, their sorted eigenvalues differ by at most
`n · ε`.

## Main result

* `ForMathlib.Matrix.abs_sortedEig_sub_le_of_entry_le`
-/

open scoped Matrix
open Module

namespace ForMathlib.Matrix

variable {n : ℕ}

/-- **Entrywise eigenvalue perturbation.**  If two real symmetric matrices `A`,
`Ahat` are entrywise `ε`-close, their `k`-th sorted eigenvalues differ by at most
`n · ε` (Weyl's inequality through the entrywise → operator-norm comparison). -/
theorem abs_sortedEig_sub_le_of_entry_le {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, |Ahat i j - A i j| ≤ ε) (k : Fin n) :
    |sortedEig hAhat k - sortedEig hA k| ≤ (n : ℝ) * ε := by
  sorry
end ForMathlib.Matrix
