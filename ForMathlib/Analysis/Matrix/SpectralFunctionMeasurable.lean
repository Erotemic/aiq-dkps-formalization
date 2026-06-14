/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(measurability of a continuous spectral function of a measurable Hermitian-matrix
family).

Formalized by Claude Fable 5 (claude-fable-5[1m]); relocated/staged and
self-contained-ized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm
import ForMathlib.MeasureTheory.CfcMeasurable

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
* `ForMathlib.Matrix.measurable_specTransform`
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
  set s : Set ℝ := Set.Icc (-R) R with hs
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp isCompact_Icc
  set f : C(s, ℝ) := ContinuousMap.restrict s ⟨h, hh⟩ with hf
  have hmem : f ∈ (polynomialFunctions s).topologicalClosure := by
    rw [polynomialFunctions.topologicalClosure s]
    trivial
  have hmem' : f ∈ closure (polynomialFunctions s : Set C(s, ℝ)) := hmem
  obtain ⟨g, hgmem, hgdist⟩ := Metric.mem_closure_iff.mp hmem' ε hε
  rw [polynomialFunctions_coe] at hgmem
  obtain ⟨p, hp⟩ := hgmem
  refine ⟨p, fun x hx => ?_⟩
  have hgx : g ⟨x, hx⟩ = p.eval x := by
    rw [← hp]; rfl
  have hfx : f ⟨x, hx⟩ = h x := rfl
  have := ContinuousMap.dist_apply_le_dist (f := f) (g := g) ⟨x, hx⟩
  rw [Real.dist_eq, hgx, hfx] at this
  exact le_of_lt (lt_of_le_of_lt this hgdist)

/-! ### Coordinate and eigenvalue bounds -/

/-- A coordinate of a Euclidean vector is bounded by its norm. -/
theorem abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h := EuclideanSpace.norm_eq x
  have hsq : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 := by
    have hterm : ∀ j ∈ Finset.univ, (0:ℝ) ≤ (x j) ^ 2 := fun j _ => sq_nonneg _
    simpa using Finset.single_le_sum hterm (Finset.mem_univ i)
  calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (x j) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖x‖ := by
        rw [h]; congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Real.norm_eq_abs, sq_abs]

/-- Entrywise bound on a Hermitian matrix bounds all its sorted eigenvalues. -/
theorem abs_sortedEig_le_of_entry_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {β : ℝ} (hβ : ∀ i j, |B i j| ≤ β) (k : Fin n) :
    |sortedEig hB k| ≤ (n : ℝ) * β := by
  set u := (opSym hB).eigenvectorBasis finrank_euclideanSpace_fin with hu
  have hnorm1 : ‖u k‖ = 1 := u.orthonormal.1 k
  have happly : Matrix.toEuclideanLin B (u k) = sortedEig hB k • u k := by
    rw [hu]
    exact (opSym hB).apply_eigenvectorBasis finrank_euclideanSpace_fin k
  have hle : ‖Matrix.toEuclideanLin B (u k)‖ ≤ (n : ℝ) * β * ‖u k‖ :=
    ForMathlib.norm_toEuclideanLin_le_of_entry_le hβ (u k)
  rw [happly, norm_smul, Real.norm_eq_abs, hnorm1, mul_one] at hle
  rw [mul_one] at hle
  exact hle

/-! ### Polynomial spectral action -/

/-- Matrix powers act on an eigenvector by powers of the eigenvalue. -/
theorem pow_mulVec_eigenvector {B : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : B *ᵥ v = μ • v) (t : ℕ) :
    (B ^ t) *ᵥ v = (μ ^ t) • v := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      ring_nf

/-- A polynomial of a matrix acts on an eigenvector by the polynomial of the
eigenvalue. -/
theorem aeval_mulVec_eigenvector {B : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : B *ᵥ v = μ • v) (p : Polynomial ℝ) :
    (aeval B p) *ᵥ v = (p.eval μ) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial t a =>
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.smul_mulVec, pow_mulVec_eigenvector hv t, smul_smul]

/-- The eigen-equation for the sorted eigendata, in `mulVec` form. -/
theorem mulVec_eigenvectorBasis {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (k : Fin n) :
    B *ᵥ WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k)
      = sortedEig hB k
          • WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k) := by
  have happly := (opSym hB).apply_eigenvectorBasis finrank_euclideanSpace_fin k
  have h1 : WithLp.ofLp (Matrix.toEuclideanLin B
        ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k))
      = B *ᵥ WithLp.ofLp ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k) := rfl
  rw [← h1, happly]
  rfl

/-- Entrywise expansion of a matrix polynomial in the (sorted) eigendata:
`p(B)ᵢⱼ = Σₖ p(λₖ) uₖ(i) uₖ(j)`. -/
theorem aeval_entry_eq_sum {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (p : Polynomial ℝ) (i j : Fin n) :
    (aeval B p) i j
      = ∑ k : Fin n, p.eval (sortedEig hB k)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j) := by
  set u := (opSym hB).eigenvectorBasis finrank_euclideanSpace_fin with hu
  set v : Fin n → (Fin n → ℝ) := fun k => WithLp.ofLp (u k) with hv
  -- the single basis vector expands in the eigenbasis
  have hsingle : (Pi.single j 1 : Fin n → ℝ) = ∑ k, v k j • v k := by
    have hrepr := u.sum_repr' (EuclideanSpace.single j (1 : ℝ))
    have hinner : ∀ k, ⟪u k, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = v k j := by
      intro k
      rw [EuclideanSpace.inner_single_right]
      simp [hv]
    have := congrArg WithLp.ofLp hrepr
    rw [WithLp.ofLp_sum] at this
    have hofLp : WithLp.ofLp (EuclideanSpace.single j (1:ℝ)) = (Pi.single j 1 : Fin n → ℝ) := by
      simp [EuclideanSpace.single]
    rw [hofLp] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hinner k, WithLp.ofLp_smul]
  -- read the (i,j) entry through mulVec against the single vector
  have hentry : (aeval B p) i j = ((aeval B p) *ᵥ Pi.single j 1) i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hentry, hsingle, Matrix.mulVec_sum]
  have haction : ∀ k, (aeval B p) *ᵥ (v k j • v k)
      = (v k j * p.eval (sortedEig hB k)) • v k := by
    intro k
    rw [Matrix.mulVec_smul, aeval_mulVec_eigenvector (mulVec_eigenvectorBasis hB k) p,
      smul_smul]
  rw [show ∑ k, (aeval B p) *ᵥ (v k j • v k)
      = ∑ k, (v k j * p.eval (sortedEig hB k)) • v k from
    Finset.sum_congr rfl fun k _ => haction k]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have : v k i = u k i := rfl
  rw [this]
  have : v k j = u k j := rfl
  rw [this]
  ring

/-! ### The spectral `h`-transform and its measurability -/

/-- The spectral `h`-transform `Σₖ h(λₖ) uₖ(i) uₖ(j)` of a Hermitian matrix.
For `h = id` this is `B` itself (the spectral theorem); for the ramp `h` it is
the rank-`d` truncation that the Gram matrix of `spectralConfig` computes on
the spectral-split event. -/
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
  set u := (opSym hB).eigenvectorBasis finrank_euclideanSpace_fin with hu
  rw [specTransform, aeval_entry_eq_sum hB p i j, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : Fin n,
      |h (sortedEig hB k) * (u k i) * (u k j)
        - p.eval (sortedEig hB k) * (u k i) * (u k j)| ≤ ε := by
    intro k
    have hfactor : h (sortedEig hB k) * (u k i) * (u k j)
        - p.eval (sortedEig hB k) * (u k i) * (u k j)
        = (h (sortedEig hB k) - p.eval (sortedEig hB k))
            * (u k i) * (u k j) := by ring
    rw [hfactor, abs_mul, abs_mul]
    have hμ : sortedEig hB k ∈ Set.Icc (-((n : ℝ) * β)) ((n : ℝ) * β) := by
      have := abs_sortedEig_le_of_entry_le hB hβ k
      exact Set.mem_Icc.mpr (abs_le.mp this)
    have h1 : |h (sortedEig hB k) - p.eval (sortedEig hB k)| ≤ ε :=
      hp _ hμ
    have hui : |u k i| ≤ 1 := by
      have := abs_coord_le_norm (u k) i
      rwa [u.orthonormal.1 k] at this
    have huj : |u k j| ≤ 1 := by
      have := abs_coord_le_norm (u k) j
      rwa [u.orthonormal.1 k] at this
    have habs : (0:ℝ) ≤ |h (sortedEig hB k) - p.eval (sortedEig hB k)| :=
      abs_nonneg _
    have h2 : |h (sortedEig hB k) - p.eval (sortedEig hB k)| * |u k i|
        ≤ |h (sortedEig hB k) - p.eval (sortedEig hB k)| :=
      mul_le_of_le_one_right habs hui
    have h3 : |h (sortedEig hB k) - p.eval (sortedEig hB k)| * |u k i| * |u k j|
        ≤ |h (sortedEig hB k) - p.eval (sortedEig hB k)| * |u k i| :=
      mul_le_of_le_one_right (mul_nonneg habs (abs_nonneg _)) huj
    linarith
  calc |∑ k : Fin n, (h (sortedEig hB k) * (u k i) * (u k j)
          - p.eval (sortedEig hB k) * (u k i) * (u k j))|
      ≤ ∑ k : Fin n, |h (sortedEig hB k) * (u k i) * (u k j)
          - p.eval (sortedEig hB k) * (u k i) * (u k j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, ε := Finset.sum_le_sum fun k _ => hterm k
    _ = (n : ℝ) * ε := by simp [mul_comm]

/-- **Measurability of the spectral `h`-transform** for a fixed continuous `h`:
the entrywise pointwise limit of matrix polynomials `p(B̂)`, glued over a
countable entrywise-norm cover.  No eigenbasis selection, no functional
calculus. -/
theorem measurable_specTransform {Ω : Type*} [MeasurableSpace Ω]
    (h : ℝ → ℝ) (hh : Continuous h)
    {Bm : Ω → Matrix (Fin n) (Fin n) ℝ} (hBmeas : Measurable Bm)
    (hsym : ∀ ω, (Bm ω).IsHermitian) :
    Measurable fun ω => specTransform h (hsym ω) := by
  -- coordinate measurability of the matrix family
  have hentry : ∀ a b : Fin n, Measurable fun ω => Bm ω a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hBmeas)
  -- it suffices to prove each entry measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  -- the countable entrywise-bound cover
  set s : ℕ → Set Ω := fun R => {ω | ∀ a b : Fin n, |Bm ω a b| ≤ (R : ℝ)} with hs
  have hsmeas : ∀ R, MeasurableSet (s R) := by
    intro R
    have : s R = ⋂ (a : Fin n), ⋂ (b : Fin n), {ω | |Bm ω a b| ≤ (R : ℝ)} := by
      ext ω; simp [hs, Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
    exact (hentry a b) ((isClosed_le continuous_abs continuous_const).measurableSet)
  have hcover : (⋃ R, s R) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, hs, Set.mem_setOf_eq]
    obtain ⟨R, hR⟩ := exists_nat_ge (∑ a : Fin n, ∑ b : Fin n, |Bm ω a b|)
    refine ⟨R, fun a b => ?_⟩
    have h1 : |Bm ω a b| ≤ ∑ b' : Fin n, |Bm ω a b'| :=
      Finset.single_le_sum (f := fun b' => |Bm ω a b'|)
        (fun b' _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b' : Fin n, |Bm ω a b'| ≤ ∑ a' : Fin n, ∑ b' : Fin n, |Bm ω a' b'| :=
      Finset.single_le_sum (f := fun a' => ∑ b' : Fin n, |Bm ω a' b'|)
        (fun a' _ => Finset.sum_nonneg fun b' _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  -- glue measurability over the cover
  refine ForMathlib.measurable_of_iUnion_restrict hsmeas hcover (fun R => ?_)
  -- the polynomial approximants at radius n·R
  have hpos : ∀ m : ℕ, (0:ℝ) < 1 / (m + 1) := fun m => by positivity
  set pseq : ℕ → Polynomial ℝ := fun m =>
    (exists_polynomial_uniform_close h hh ((n : ℝ) * R) (hpos m)).choose with hpseq
  have hpspec : ∀ m, ∀ x ∈ Set.Icc (-((n : ℝ) * R)) ((n : ℝ) * R),
      |h x - (pseq m).eval x| ≤ 1 / (m + 1) := fun m =>
    (exists_polynomial_uniform_close h hh ((n : ℝ) * R) (hpos m)).choose_spec
  -- approximants are measurable on the piece
  have hAmeas : ∀ m : ℕ,
      Measurable fun ωs : (s R) => (aeval (Bm ωs) (pseq m)) i j := by
    intro m
    have hcont : Continuous fun M : Matrix (Fin n) (Fin n) ℝ => (aeval M (pseq m)) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp (pseq m).continuous_aeval)
    exact hcont.measurable.comp (hBmeas.comp measurable_subtype_coe)
  -- pointwise convergence on the piece
  have htend : ∀ ωs : (s R),
      Tendsto (fun m => (aeval (Bm ωs) (pseq m)) i j) atTop
        (𝓝 (specTransform h (hsym ωs) i j)) := by
    intro ωs
    have hbound : ∀ m : ℕ,
        ‖(aeval (Bm ωs) (pseq m)) i j - specTransform h (hsym ωs) i j‖
          ≤ (n : ℝ) * (1 / (m + 1)) := by
      intro m
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact abs_specTransform_sub_aeval_le h (hsym ωs) ωs.2 (hpspec m) i j
    have hlim : Tendsto (fun m : ℕ => (n : ℝ) * (1 / (m + 1))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun m : ℕ => (n : ℝ) * (1 / ((m : ℝ) + 1))) atTop
          (𝓝 ((n : ℝ) * (0 : ℝ))) := h0.const_mul (n : ℝ)
      simpa using h1
    have hsub : Tendsto
        (fun m => (aeval (Bm ωs) (pseq m)) i j - specTransform h (hsym ωs) i j)
        atTop (𝓝 0) :=
      squeeze_zero_norm hbound hlim
    have := hsub.add_const (specTransform h (hsym ωs) i j)
    simpa using this
  -- pass to the limit
  exact measurable_of_tendsto_metrizable' atTop hAmeas
    (tendsto_pi_nhds.mpr htend)


end ForMathlib.Matrix
