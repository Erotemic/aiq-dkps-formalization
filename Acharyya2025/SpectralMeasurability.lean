/-
Measurability of spectral / alignment events from measurability of the sample
dissimilarity matrix alone.

The raw spectral embedding `spectralConfig` is eigenvector-valued and genuinely
non-measurable in the sample matrix at eigenvalue crossings (the eigenbasis is a
`Classical.choice`).  This file develops the measurability needed to keep that
embedding out of the probability statements, in two layers.

## Used by the Quench `hmeas_spec` discharge

The bridge (`DkpsQuench.AcharyyaBridge`) uses only the lightweight route:

* `measurable_cmds_matrix` — the sample CMDS matrix is a measurable function of
  the sample (every entry is algebraic in the `Dhat` entries);
* `measurableSet_entrywiseClose_event` — hence the CMDS-entrywise-closeness
  event is Borel.

That event is *deterministically* contained in the alignment-existence event
(`AlignedPipeline.alignExists_of_entrywiseClose`), so it serves directly as the
measurable high-probability sub-event — no eigenvector measurability is ever
needed.  See `docs/planning/hmeas-spec-discharge.md`.

## General standalone development (more than the discharge needs)

A self-contained, more general result, kept as a reusable / Mathlib-candidate
measurability fact (it shows the alignment event is measurable for *any*
measurable spectral-split event, not just the entrywise one):

1. (`measurable_specTransform`) The spectral `h`-transform `Σₖ h(λₖ) uₖuₖᵀ` of a
   measurable Hermitian-matrix family is measurable for any fixed continuous
   `h` — the entrywise pointwise limit of matrix *polynomials* `p(B̂)`
   (Stone–Weierstrass on a spectral interval); no functional calculus, no
   eigenbasis selection.
2. (`inner_spectralConfig_eq_specTransform`) On the spectral-split event, the
   Gram matrix of `spectralConfig` equals `specTransform h`.
3. (`alignExists_iff_qProp`) `AlignExists` depends on the embedding only through
   its Gram matrix (Procrustes rigidity), via the matrix predicate `QProp`.
4. (`measurableSet_qProp`) `{M | QProp ψ c M}` is Borel (compactly quantified
   existential, no measurable selection, `ForMathlib.measurableSet_exists_mem_le`).
5. (`measurableSet_alignExists_inter`) Assembly: on any measurable spectral-split
   event the alignment-existence event is measurable from `Measurable Dhat`.

Layer 1's `measurable_specTransform` and the assembly are independent of the
Quench discharge; they record that the harder, fully-general route also goes
through.

Formalized by Claude Fable 5 (claude-fable-5[1m]); the entrywise-event layer and
this header by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/

import Acharyya2025.MatrixPerturbation
import Acharyya2025.AlignedPipeline
import Acharyya2025.Procrustes
import ForMathlib.MeasureTheory.CompactExists
import ForMathlib.MeasureTheory.CfcMeasurable
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open MeasureTheory Filter Polynomial

namespace Acharyya2025.SpectralMeasurability

open Acharyya2024
open Acharyya2025.MatrixPerturbation
open Acharyya2025.ConfigPerturbation

variable {n d : ℕ}

/-- `Matrix` is a type-level def, so the pi `MeasurableSpace` instance does not
fire on it; register it (entrywise σ-algebra, matching the pi topology). -/
instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

instance : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

/-! ### The ramp function

The fixed continuous spectral filter: identity above `b`, zero below `a`,
linear in between.  Applied to the sample eigenvalues it freezes the top-`d`
block and kills the tail, turning the discontinuous rank-`d` truncation into a
fixed continuous function of the matrix. -/

/-- Continuous ramp: `0` for `x ≤ a`, `x` for `x ≥ b` (when `0 ≤ a < b`),
linear in between. -/
noncomputable def ramp (a b : ℝ) : ℝ → ℝ :=
  fun x => max 0 (min x (b * (x - a) / (b - a)))

theorem ramp_continuous (a b : ℝ) : Continuous (ramp a b) := by
  unfold ramp
  fun_prop

theorem ramp_eq_zero {a b x : ℝ} (hb : 0 < b) (hab : a < b) (hx : x ≤ a) :
    ramp a b x = 0 := by
  unfold ramp
  have hline : b * (x - a) / (b - a) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith
    · linarith
  have : min x (b * (x - a) / (b - a)) ≤ 0 := le_trans (min_le_right _ _) hline
  exact max_eq_left this

theorem ramp_eq_self {a b x : ℝ} (ha : 0 ≤ a) (hab : a < b) (hx : b ≤ x) :
    ramp a b x = x := by
  unfold ramp
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hline : x ≤ b * (x - a) / (b - a) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < b - a)]
    nlinarith
  rw [min_eq_left hline]
  exact max_eq_right (by linarith)

/-! ### Stone–Weierstrass extraction -/

/-- For continuous `h` and any radius/tolerance, there is a polynomial
uniformly close to `h` on `[-R, R]`. -/
theorem exists_polynomial_uniform_close (h : ℝ → ℝ) (hh : Continuous h)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc (-R) R, |h x - p.eval x| ≤ ε := by
  classical
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
theorem abs_sortedEigenvalues_le_of_entry_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {β : ℝ} (hβ : ∀ i j, |B i j| ≤ β) (k : Fin n) :
    |sortedEigenvalues hB k| ≤ (n : ℝ) * β := by
  set u := (opSym hB).eigenvectorBasis finrank_euclideanSpace_fin with hu
  have hnorm1 : ‖u k‖ = 1 := u.orthonormal.1 k
  have happly : Matrix.toEuclideanLin B (u k) = sortedEigenvalues hB k • u k := by
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
      = sortedEigenvalues hB k
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
      = ∑ k : Fin n, p.eval (sortedEigenvalues hB k)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j) := by
  classical
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
      = (v k j * p.eval (sortedEigenvalues hB k)) • v k := by
    intro k
    rw [Matrix.mulVec_smul, aeval_mulVec_eigenvector (mulVec_eigenvectorBasis hB k) p,
      smul_smul]
  rw [show ∑ k, (aeval B p) *ᵥ (v k j • v k)
      = ∑ k, (v k j * p.eval (sortedEigenvalues hB k)) • v k from
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
  fun i j => ∑ k : Fin n, h (sortedEigenvalues hB k)
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
      |h (sortedEigenvalues hB k) * (u k i) * (u k j)
        - p.eval (sortedEigenvalues hB k) * (u k i) * (u k j)| ≤ ε := by
    intro k
    have hfactor : h (sortedEigenvalues hB k) * (u k i) * (u k j)
        - p.eval (sortedEigenvalues hB k) * (u k i) * (u k j)
        = (h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k))
            * (u k i) * (u k j) := by ring
    rw [hfactor, abs_mul, abs_mul]
    have hμ : sortedEigenvalues hB k ∈ Set.Icc (-((n : ℝ) * β)) ((n : ℝ) * β) := by
      have := abs_sortedEigenvalues_le_of_entry_le hB hβ k
      exact Set.mem_Icc.mpr (abs_le.mp this)
    have h1 : |h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k)| ≤ ε :=
      hp _ hμ
    have hui : |u k i| ≤ 1 := by
      have := abs_coord_le_norm (u k) i
      rwa [u.orthonormal.1 k] at this
    have huj : |u k j| ≤ 1 := by
      have := abs_coord_le_norm (u k) j
      rwa [u.orthonormal.1 k] at this
    have habs : (0:ℝ) ≤ |h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k)| :=
      abs_nonneg _
    have h2 : |h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k)| * |u k i|
        ≤ |h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k)| :=
      mul_le_of_le_one_right habs hui
    have h3 : |h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k)| * |u k i| * |u k j|
        ≤ |h (sortedEigenvalues hB k) - p.eval (sortedEigenvalues hB k)| * |u k i| :=
      mul_le_of_le_one_right (mul_nonneg habs (abs_nonneg _)) huj
    linarith
  calc |∑ k : Fin n, (h (sortedEigenvalues hB k) * (u k i) * (u k j)
          - p.eval (sortedEigenvalues hB k) * (u k i) * (u k j))|
      ≤ ∑ k : Fin n, |h (sortedEigenvalues hB k) * (u k i) * (u k j)
          - p.eval (sortedEigenvalues hB k) * (u k i) * (u k j)| :=
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
  classical
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

/-! ### The Gram bridge: on the spectral split, `Gram (spectralConfig) = specTransform` -/

/-- On the spectral-split event — `h` fixes the (nonnegative) top-`d` sorted
eigenvalues and kills the tail — the Gram matrix of the raw spectral embedding
equals the spectral `h`-transform.  This is what lets the (non-measurable)
eigenvector-valued embedding enter probability statements only through a
measurable matrix. -/
theorem inner_spectralConfig_eq_specTransform {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) (hd : d ≤ n) (h : ℝ → ℝ)
    (htop : ∀ k : Fin n, (k : ℕ) < d → 0 ≤ sortedEigenvalues hB k ∧
        h (sortedEigenvalues hB k) = sortedEigenvalues hB k)
    (htail : ∀ k : Fin n, d ≤ (k : ℕ) → h (sortedEigenvalues hB k) = 0)
    (i j : Fin n) :
    ⟪spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd i,
      spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd j⟫_ℝ
      = specTransform h hB i j := by
  classical
  set u := (opSym hB).eigenvectorBasis finrank_euclideanSpace_fin with hu
  set μ := sortedEigenvalues hB with hμdef
  -- coordinates of the spectral embedding
  have happ : ∀ (a : Fin n) (l : Fin d),
      spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd a l
        = Real.sqrt (μ (Fin.castLE hd l)) * u (Fin.castLE hd l) a := fun a l => rfl
  -- LHS: expand the real inner product and simplify the square roots
  have hLHS : ⟪spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd i,
      spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd j⟫_ℝ
      = ∑ l : Fin d, μ (Fin.castLE hd l) * u (Fin.castLE hd l) i * u (Fin.castLE hd l) j := by
    rw [show (⟪spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd i,
        spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd j⟫_ℝ : ℝ)
        = ∑ l : Fin d, spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd i l
            * spectralConfig (Matrix.toEuclideanLin B) (opSym hB) hd j l by
      simp [PiLp.inner_apply, mul_comm]]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [happ i l, happ j l]
    have hnn : 0 ≤ μ (Fin.castLE hd l) :=
      (htop (Fin.castLE hd l) (by simp)).1
    have hsqrt : Real.sqrt (μ (Fin.castLE hd l)) * Real.sqrt (μ (Fin.castLE hd l))
        = μ (Fin.castLE hd l) := Real.mul_self_sqrt hnn
    linear_combination (u (Fin.castLE hd l) i * u (Fin.castLE hd l) j) * hsqrt
  -- RHS: kill the tail and reindex over the castLE embedding
  have hRHS : specTransform h hB i j
      = ∑ l : Fin d, μ (Fin.castLE hd l) * u (Fin.castLE hd l) i * u (Fin.castLE hd l) j := by
    rw [specTransform]
    have hsub : (Finset.univ.map (Fin.castLEEmb hd)) ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.subset_univ _
    have hvanish : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        k ∉ Finset.univ.map (Fin.castLEEmb hd) →
        h (μ k) * u k i * u k j = 0 := by
      intro k _ hk
      have hge : d ≤ (k : ℕ) := by
        by_contra hlt
        push Not at hlt
        exact hk (Finset.mem_map.mpr ⟨⟨(k : ℕ), hlt⟩, Finset.mem_univ _, by
          simp [Fin.castLEEmb, Fin.castLE]⟩)
      rw [htail k hge, zero_mul, zero_mul]
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_map]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (Fin.castLEEmb hd l : Fin n) = Fin.castLE hd l from rfl,
      (htop (Fin.castLE hd l) (by simp)).2]
  rw [hLHS, hRHS]

/-! ### The matrix-level alignment predicate and Procrustes reduction -/

open Acharyya2025.AlignedPipeline Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- Matrix-level alignment predicate: `M` is realized as the Gram matrix of a
configuration within total distance `c` of `ψ`.  `AlignExists` is exactly this
predicate applied to the Gram matrix of the raw spectral embedding
(`alignExists_iff_qProp`). -/
def QProp (ψ : Config n d) (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ y : Config n d, (∀ i j, (⟪y i, y j⟫_ℝ : ℝ) = M i j) ∧ ∑ i, ‖y i - ψ i‖ ≤ c

open Acharyya2025.AlignedPipeline Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- **`AlignExists` depends on the raw spectral embedding only through its Gram
matrix** (Procrustes rigidity): the alignment-existence event equals the
matrix-level predicate `QProp` evaluated at the embedding's Gram matrix. -/
theorem alignExists_iff_qProp {Ω : Type} (hd : d ≤ n) (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (ψ : Config n d) (c : Nat → Real) (u : Nat) (ω : Ω) :
    AlignExists hd Dhat hsym ψ c u ω
      ↔ QProp ψ (c u) (fun i j =>
          ⟪spectralConfig
              (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
              (opSym (hsym u ω)) hd i,
            spectralConfig
              (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
              (opSym (hsym u ω)) hd j⟫_ℝ) := by
  set spec : Config n d := fun i =>
    spectralConfig (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
      (opSym (hsym u ω)) hd i with hspec
  constructor
  · rintro ⟨W, hWinner, hWerr⟩
    refine ⟨fun i => W (spec i), fun i j => hWinner _ _, ?_⟩
    simpa [ConfigError, hspec] using hWerr
  · rintro ⟨y, hgram, herr⟩
    obtain ⟨V, hV⟩ := Acharyya2025.Procrustes.exists_linearIsometryEquiv_of_inner_eq
      spec y (fun i j => (hgram i j).symm)
    refine ⟨V.toLinearEquiv.toLinearMap, fun x z => ?_, ?_⟩
    · simp [V.inner_map_map x z]
    · have hCE : ConfigError (fun i => V.toLinearEquiv.toLinearMap (spec i)) ψ
          = ∑ i, ‖y i - ψ i‖ := by
        rw [ConfigError]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hVi : V.toLinearEquiv.toLinearMap (spec i) = y i := by simpa using hV i
        rw [hVi]
      rw [hCE]
      exact herr

/-! ### The matrix-level predicate is Borel -/

/-- **`{M | QProp ψ c M}` is a Borel set of matrices.**  On each diagonal-bounded
piece the realizing configuration lives in a compact ball, so the existential is
compactly quantified (`ForMathlib.measurableSet_exists_mem_le`) with no
measurable selection; a countable union over the bound finishes. -/
theorem measurableSet_qProp (ψ : Config n d) (c : ℝ) :
    MeasurableSet {M : Matrix (Fin n) (Fin n) ℝ | QProp ψ c M} := by
  classical
  -- the compact configuration balls and the defect functional
  set K : ℕ → Set (Config n d) := fun R =>
    Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
      (Real.sqrt R)) with hK
  set F : Config n d → Matrix (Fin n) (Fin n) ℝ → ℝ := fun y M =>
    (∑ i : Fin n, ∑ j : Fin n, |(⟪y i, y j⟫_ℝ : ℝ) - M i j|)
      + max ((∑ i : Fin n, ‖y i - ψ i‖) - c) 0 with hF
  have hKcompact : ∀ R : ℕ, IsCompact (K R) := fun R =>
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  -- F is nonnegative, and ≤ 0 exactly at Gram realizations within distance c
  have hFnonneg : ∀ y M, 0 ≤ F y M := by
    intro y M
    refine add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (le_max_right _ _)
  have hFzero : ∀ y M, F y M ≤ 0 ↔
      ((∀ i j, (⟪y i, y j⟫_ℝ : ℝ) = M i j) ∧ ∑ i, ‖y i - ψ i‖ ≤ c) := by
    intro y M
    constructor
    · intro hle
      have h1 : (∑ i : Fin n, ∑ j : Fin n, |(⟪y i, y j⟫_ℝ : ℝ) - M i j|) = 0 := by
        have h2 : (0:ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, |(⟪y i, y j⟫_ℝ : ℝ) - M i j| :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
        have h3 : (0:ℝ) ≤ max ((∑ i : Fin n, ‖y i - ψ i‖) - c) 0 := le_max_right _ _
        rw [hF] at hle
        simp only at hle
        linarith
      have hmax : max ((∑ i : Fin n, ‖y i - ψ i‖) - c) 0 = 0 := by
        have h2 : (0:ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, |(⟪y i, y j⟫_ℝ : ℝ) - M i j| :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
        have h3 : (0:ℝ) ≤ max ((∑ i : Fin n, ‖y i - ψ i‖) - c) 0 := le_max_right _ _
        rw [hF] at hle
        simp only at hle
        linarith
      constructor
      · intro i j
        have houter := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg
            ((⟪y i, y j⟫_ℝ : ℝ) - M i j))).mp h1 i (Finset.mem_univ i)
        have hinner := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => abs_nonneg ((⟪y i, y j⟫_ℝ : ℝ) - M i j))).mp houter j (Finset.mem_univ j)
        have := abs_eq_zero.mp hinner
        linarith [this]
      · have : (∑ i : Fin n, ‖y i - ψ i‖) - c ≤ 0 := by
          calc (∑ i : Fin n, ‖y i - ψ i‖) - c
              ≤ max ((∑ i : Fin n, ‖y i - ψ i‖) - c) 0 := le_max_left _ _
            _ = 0 := hmax
        linarith
    · rintro ⟨hgram, herr⟩
      have h1 : (∑ i : Fin n, ∑ j : Fin n, |(⟪y i, y j⟫_ℝ : ℝ) - M i j|) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [hgram i j]; simp
      have h2 : max ((∑ i : Fin n, ‖y i - ψ i‖) - c) 0 = 0 :=
        max_eq_right (by linarith)
      rw [hF]; simp only; rw [h1, h2]; norm_num
  -- the piecewise decomposition by the diagonal bound
  have hpieces : {M : Matrix (Fin n) (Fin n) ℝ | QProp ψ c M}
      = ⋃ R : ℕ, ({M : Matrix (Fin n) (Fin n) ℝ | ∀ i, M i i ≤ (R : ℝ)}
          ∩ {M : Matrix (Fin n) (Fin n) ℝ | ∃ y ∈ K R, F y M ≤ 0}) := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, hgram, herr⟩
      obtain ⟨R, hR⟩ := exists_nat_ge (∑ i : Fin n, ‖y i‖ ^ 2)
      have hdiag : ∀ i, M i i ≤ (R : ℝ) := by
        intro i
        have h1 : M i i = ‖y i‖ ^ 2 := by
          rw [← hgram i i, real_inner_self_eq_norm_sq]
        have h2 : ‖y i‖ ^ 2 ≤ ∑ i' : Fin n, ‖y i'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ‖y i'‖ ^ 2)
            (fun i' _ => sq_nonneg _) (Finset.mem_univ i)
        linarith
      refine ⟨R, hdiag, y, ?_, (hFzero y M).mpr ⟨hgram, herr⟩⟩
      rw [hK]
      refine Set.mem_pi.mpr fun i _ => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖y i‖ ^ 2 ≤ (R : ℝ) := by
        have h2 : ‖y i‖ ^ 2 ≤ ∑ i' : Fin n, ‖y i'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ‖y i'‖ ^ 2)
            (fun i' _ => sq_nonneg _) (Finset.mem_univ i)
        linarith
      exact Real.le_sqrt_of_sq_le h1
    · rintro ⟨R, _, y, _, hFy⟩
      obtain ⟨hgram, herr⟩ := (hFzero y M).mp hFy
      exact ⟨y, hgram, herr⟩
  rw [hpieces]
  refine MeasurableSet.iUnion fun R => MeasurableSet.inter ?_ ?_
  · -- the diagonal-bound piece
    have : {M : Matrix (Fin n) (Fin n) ℝ | ∀ i, M i i ≤ (R : ℝ)}
        = ⋂ i : Fin n, {M : Matrix (Fin n) (Fin n) ℝ | M i i ≤ (R : ℝ)} := by
      ext M; simp [Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    have hcoord : Measurable fun M : Matrix (Fin n) (Fin n) ℝ => M i i :=
      (measurable_pi_apply i).comp (measurable_pi_apply i)
    exact hcoord measurableSet_Iic
  · -- the compactly quantified existential piece
    refine ForMathlib.measurableSet_exists_mem_le (hKcompact R) (fun M => ?_) (fun y _ => ?_) 0
    · -- continuity in the configuration
      refine Continuous.continuousOn ?_
      rw [hF]
      refine Continuous.add ?_ ?_
      · refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
        exact (Continuous.inner (continuous_apply i) (continuous_apply j)).sub
          continuous_const |>.abs
      · refine Continuous.max ?_ continuous_const
        refine Continuous.sub ?_ continuous_const
        exact continuous_finsetSum _ fun i _ =>
          ((continuous_apply i).sub continuous_const).norm
    · -- measurability in the matrix
      rw [hF]
      refine Measurable.add ?_ measurable_const
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      have hcoord : Measurable fun M : Matrix (Fin n) (Fin n) ℝ => M i j :=
        (measurable_pi_apply j).comp (measurable_pi_apply i)
      exact (measurable_const.sub hcoord).abs

/-! ### Assembly: measurability of the alignment event from `Measurable Dhat` -/

open Acharyya2025.AlignedPipeline Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- Glue: the sample CMDS matrix is a measurable function of the sample whenever
the dissimilarity matrix is — every entry is a finite algebraic expression in
the entries of `Dhat`. -/
theorem measurable_cmds_matrix {Ω : Type} [MeasurableSpace Ω]
    (Dhat : Nat → Ω → DisMat n) (u : Nat)
    (hD : Measurable fun ω => Dhat u ω) :
    Measurable fun ω => disMatToMatrix (classicalMDSMatrix (Dhat u ω)) := by
  have hentry : ∀ a b : Fin n, Measurable fun ω => Dhat u ω a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hD)
  have hsq : ∀ a b : Fin n, Measurable fun ω => (Dhat u ω a b) ^ 2 := fun a b =>
    (hentry a b).pow_const 2
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  show Measurable fun ω =>
    -(1 / 2 : ℝ) * doubleCenter (fun a b => (Dhat u ω a b) ^ 2) i j
  refine Measurable.const_mul ?_ _
  rw [show (fun ω => doubleCenter (fun a b => (Dhat u ω a b) ^ 2) i j)
      = fun ω => (Dhat u ω i j) ^ 2
          - rowMean (fun a b => (Dhat u ω a b) ^ 2) i
          - colMean (fun a b => (Dhat u ω a b) ^ 2) j
          + grandMean (fun a b => (Dhat u ω a b) ^ 2) from rfl]
  refine Measurable.add (Measurable.sub (Measurable.sub (hsq i j) ?_) ?_) ?_
  · -- rowMean
    rw [show (fun ω => rowMean (fun a b => (Dhat u ω a b) ^ 2) i)
        = fun ω => ((n : ℝ)⁻¹) * ∑ b : Fin n, (Dhat u ω i b) ^ 2 from rfl]
    exact (Finset.measurable_sum _ fun b _ => hsq i b).const_mul _
  · -- colMean
    rw [show (fun ω => colMean (fun a b => (Dhat u ω a b) ^ 2) j)
        = fun ω => ((n : ℝ)⁻¹) * ∑ a : Fin n, (Dhat u ω a j) ^ 2 from rfl]
    exact (Finset.measurable_sum _ fun a _ => hsq a j).const_mul _
  · -- grandMean
    rw [show (fun ω => grandMean (fun a b => (Dhat u ω a b) ^ 2))
        = fun ω => ((n : ℝ)⁻¹) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (Dhat u ω a b) ^ 2 from rfl]
    exact (Finset.measurable_sum _ fun a _ =>
      Finset.measurable_sum _ fun b _ => hsq a b).const_mul _

open Acharyya2025.AlignedPipeline Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- **Measurability of the alignment-existence event, with no raw-embedding
measurability primitive.**

On any measurable event `G` where the spectral split holds (the fixed continuous
filter `h` fixes the nonnegative top-`d` sorted eigenvalues of the sample CMDS
matrix and kills its tail — supplied downstream by Weyl from the
entrywise-closeness event), the alignment-existence event is measurable, from
measurability of the sample CMDS matrix alone.

This replaces `hmeas_spec` (measurability of the eigenvector-valued raw spectral
embedding — not provable as stated) with `hBmeas` (measurability of the sample
matrix — trivially dischargeable from `Measurable Dhat` via
`measurable_cmds_matrix`).

Route: `AlignExists = QProp ∘ Gram(spectralConfig)` (Procrustes), and on `G` the
Gram equals the measurable `specTransform h` (spectral split), so the event is a
measurable preimage of the Borel set `{M | QProp ψ c M}`. -/
theorem measurableSet_alignExists_inter {Ω : Type} [MeasurableSpace Ω]
    (hd : d ≤ n) (Dhat : Nat → Ω → DisMat n)
    (hsym : ∀ u ω, (disMatToMatrix (classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (ψ : Config n d) (c : Nat → Real) (u : Nat)
    (hBmeas : Measurable fun ω => disMatToMatrix (classicalMDSMatrix (Dhat u ω)))
    (h : ℝ → ℝ) (hh : Continuous h)
    {G : Set Ω} (hG : MeasurableSet G)
    (hsplit : ∀ ω ∈ G,
      (∀ k : Fin n, (k : ℕ) < d → 0 ≤ sortedEigenvalues (hsym u ω) k ∧
          h (sortedEigenvalues (hsym u ω) k) = sortedEigenvalues (hsym u ω) k) ∧
      (∀ k : Fin n, d ≤ (k : ℕ) → h (sortedEigenvalues (hsym u ω) k) = 0)) :
    MeasurableSet ({ω | AlignExists hd Dhat hsym ψ c u ω} ∩ G) := by
  have hT : Measurable fun ω => specTransform h (hsym u ω) :=
    measurable_specTransform h hh hBmeas (fun ω => hsym u ω)
  have hset : {ω | AlignExists hd Dhat hsym ψ c u ω} ∩ G
      = ((fun ω => specTransform h (hsym u ω)) ⁻¹' {M | QProp ψ (c u) M}) ∩ G := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    refine and_congr_left fun hGω => ?_
    rw [alignExists_iff_qProp hd Dhat hsym ψ c u ω]
    have hMeq : (fun i j =>
        (⟪spectralConfig
            (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
            (opSym (hsym u ω)) hd i,
          spectralConfig
            (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix (Dhat u ω))))
            (opSym (hsym u ω)) hd j⟫_ℝ : ℝ))
        = specTransform h (hsym u ω) := by
      funext i j
      exact inner_spectralConfig_eq_specTransform (hsym u ω) hd h
        (hsplit ω hGω).1 (hsplit ω hGω).2 i j
    rw [hMeq]
  rw [hset]
  exact (hT (measurableSet_qProp ψ (c u))).inter hG

open Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- **The CMDS-entrywise-closeness event is Borel**, from measurability of the
sample dissimilarity matrix alone — every CMDS entry is a finite algebraic
expression in the `Dhat` entries.  This is the measurable high-probability
sub-event the Quench bridge uses in place of `hmeas_spec`. -/
theorem measurableSet_entrywiseClose_event {Ω : Type} [MeasurableSpace Ω]
    (Dhat : Nat → Ω → DisMat n) (D : DisMat n) (rate : Nat → ℝ) (u : Nat)
    (hD : Measurable fun ω => Dhat u ω) :
    MeasurableSet {ω | Acharyya2025.Bridge.EntrywiseClose
      (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)} := by
  have hcmds : Measurable fun ω => disMatToMatrix (classicalMDSMatrix (Dhat u ω)) :=
    measurable_cmds_matrix Dhat u hD
  have hset : {ω | Acharyya2025.Bridge.EntrywiseClose
        (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)}
      = ⋂ (i : Fin n), ⋂ (j : Fin n),
          {ω | |classicalMDSMatrix (Dhat u ω) i j - classicalMDSMatrix D i j| ≤ rate u} := by
    ext ω; simp [Acharyya2025.Bridge.EntrywiseClose, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have hentry : Measurable fun ω => classicalMDSMatrix (Dhat u ω) i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hcmds)
  exact (hentry.sub measurable_const).abs measurableSet_Iic

end Acharyya2025.SpectralMeasurability
