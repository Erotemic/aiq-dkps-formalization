import Mathlib

open scoped BigOperators
open Filter

open MeasureTheory

namespace QuenchICML

set_option linter.unusedVariables false

universe u v

/-!
# DKPS / Quench ICML paper: statement-level Lean formalization

This file is meant to be **readable to people who are not familiar with Lean**.

Goals of this file:

1. Introduce Lean definitions that mirror the paper's notation (models, scores, DKPS stress, etc.).
2. State the key assumptions and theorems in (approximately) the same order as the paper.
3. Use `sorry` as a placeholder for proofs we haven't formalized yet.

**Important policy for this project**
- We avoid using `axiom` unless a result is explicitly taken from prior work.
- The **only** result treated as an external black box is `Theorem1` (Acharyya et al.),
  which is cited by the paper.

Throughout, we try to keep names close to the paper:

- `Q` = query set, `X` = response space
- `f : Model Q X` = a black-box model that maps each query to a distribution on responses
- `Qstar` = full benchmark query set (a finite set)
- `score f Qset` = benchmark score computed on a finite query set `Qset`
- `D` = pairwise distance matrix between models
- `dkpsStress` / `IsDKPS` = DKPS stress objective and minimizer property (paper Eq. (1))
- `psiHat` = estimated DKPS coordinates (defined via `Classical.choose`)

Many objects are intentionally `noncomputable`: they use integrals and minimizers.
Lean can still type-check and reason about these objects without executable code.
-/

/-!
## Basic objects: probability measures, models, vectors, matrices
-/

/-- Convenience wrapper: probability measures as a sigma-type. -/
abbrev ProbMeasure (X : Type u) [MeasurableSpace X] :=
  { μ : Measure X // IsProbabilityMeasure μ }

/-- Black-box generative model: `query ↦ distribution on responses`. -/
abbrev Model (Q : Type u) (X : Type v) [MeasurableSpace X] :=
  Q → ProbMeasure X

/-- Euclidean vectors `ℝ^p`. -/
abbrev Vec (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- Matrices `m × p` over `ℝ`. -/
abbrev Mat (m p : ℕ) := Matrix (Fin m) (Fin p) ℝ

/-- Frobenius norm (as used in the paper to build the distance matrix). -/
noncomputable def frobNorm {m p : ℕ} (A : Mat m p) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ (2 : ℕ))

/-!
## DKPS construction (paper Eq. (1))

The paper defines a matrix of *mean embedded responses* `X̄_i` for each model `f_i`,
computes pairwise Frobenius distances to form `D`, and then defines DKPS coordinates
as a (global) minimizer of a stress objective.

Here we formalize the *objects* and the *minimizer property*. We postpone proving that
a minimizer exists (this will require analysis), and instead record existence as a
`sorry` lemma from which we define `psiHat` by `Classical.choose`.
-/
section DKPS_Construction

variable {Q : Type u} {X : Type v} [MeasurableSpace X]

/-- Mean embedded response (integral abstraction of an empirical mean). -/
noncomputable def meanEmbed {p : ℕ} (μ : ProbMeasure X) (g : X → Vec p) : Vec p :=
  ∫ x, g x ∂ μ.1

/--
`X̄_i ∈ ℝ^{m×p}`: a matrix whose `i`-th row is the mean embedding of responses to query `Qset i`.

In the paper, this corresponds to the matrix formed by concatenating query-wise mean embeddings.
-/
noncomputable def XbarMat {m p : ℕ} (f : Model Q X) (Qset : Fin m → Q) (g : X → Vec p) :
    Mat m p :=
  fun i j => (meanEmbed (μ := f (Qset i)) g) j

/-- Pairwise distance matrix `D` via Frobenius distances between `X̄_i` matrices. -/
noncomputable def distMatrix {n m p : ℕ} (models : Fin n → Model Q X) (Qset : Fin m → Q)
    (g : X → Vec p) : Matrix (Fin n) (Fin n) ℝ :=
  fun i i' => frobNorm (XbarMat (f := models i) Qset g - XbarMat (f := models i') Qset g)

/-- DKPS stress objective (paper Eq. (1)). -/
noncomputable def dkpsStress {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → Vec d) : ℝ :=
  ∑ i, ∑ i', (‖z i - z i'‖ - D i i') ^ (2 : ℕ)

/-- `z` is a global minimizer of DKPS stress for `D`. -/
def IsDKPS {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → Vec d) : Prop :=
  ∀ z' : Fin n → Vec d, dkpsStress (D := D) z ≤ dkpsStress (D := D) z'

/-!
### Existence + definition of `psiHat`

The paper defines `ψ̂` as the stress minimizer. In Lean, we proceed in two steps:

1. State an existence theorem `exists_psiHat_isDKPS`. We will eventually prove it, but for now
   we use `sorry`.
2. Define `psiHat D` as an arbitrary choice of such a minimizer using `Classical.choose`, and
   prove `psiHat_isDKPS` from the choice specification (no additional `sorry` needed).
-/


/-!
### Existence + definition of `psiHat`

The DKPS paper defines `ψ̂` as a *solution* of the stress minimization problem (Eq. (1)).

Importantly, the cited works do **not** prove that a minimizer exists for an *arbitrary* real matrix
`D`. Instead, `D` is constructed from Euclidean data (pairwise distances of mean embeddings), i.e.
`D` is a Euclidean distance matrix (EDM). Under this realizability assumption, a minimizer exists
trivially: if `D i i' = ‖x i - x i'‖` for some configuration `x : Fin n → ℝ^d`, then the DKPS stress
at `x` is `0`, and stress is always nonnegative.

So we:
1. Define an EDM realizability predicate `IsEDM`.
2. Prove existence of a DKPS minimizer from `IsEDM` (no `sorry` needed).
3. Define `psiHat` by choosing one such minimizer (requires an `IsEDM` hypothesis).
-/

/-- `D` is realizable as Euclidean distances of some configuration in `ℝ^d`. -/
def IsEDM {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ x : Fin n → Vec d, ∀ i i', D i i' = ‖x i - x i'‖

/-- DKPS stress is always nonnegative (sum of squares). -/
lemma dkpsStress_nonneg {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → Vec d) :
    0 ≤ dkpsStress (D := D) z := by
  classical
  -- Each summand is a square, hence nonnegative.
  have hterm : ∀ i i' : Fin n, 0 ≤ (‖z i - z i'‖ - D i i') ^ (2 : ℕ) := by
    intro i i'
    -- `x^2 ≥ 0`
    simpa [pow_two] using (sq_nonneg (‖z i - z i'‖ - D i i'))
  -- Finite sums preserve nonnegativity.
  -- Finite sums preserve nonnegativity.
  unfold dkpsStress
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro i' hi'
  exact hterm i i'

/--
Existence of a DKPS minimizer under the EDM realizability assumption.

If `D` is an EDM realized by `x`, then `dkpsStress D x = 0`, hence `x` is a global minimizer.
-/
theorem exists_psiHat_isDKPS_of_IsEDM {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hEDM : IsEDM (n := n) (d := d) D) :
    ∃ z : Fin n → Vec d, IsDKPS (n := n) (d := d) D z := by
  classical
  rcases hEDM with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro z'
  -- `dkpsStress D x = 0`
  have h0 : dkpsStress (D := D) x = 0 := by
    simp [dkpsStress, hx]
  -- and `dkpsStress D z' ≥ 0`
  have hnonneg : 0 ≤ dkpsStress (D := D) z' := dkpsStress_nonneg (n := n) (d := d) D z'
  -- conclude `dkpsStress D x ≤ dkpsStress D z'`
  simpa [h0] using hnonneg

/--
The paper's `ψ̂`: an (arbitrary) DKPS minimizer, **defined only when** `D` is an EDM.

We choose a witness from `exists_psiHat_isDKPS_of_IsEDM` using `Classical.choose`.
-/
noncomputable def psiHat {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hEDM : IsEDM (n := n) (d := d) D) : Fin n → Vec d :=
  Classical.choose (exists_psiHat_isDKPS_of_IsEDM (n := n) (d := d) D hEDM)

/-- The chosen `psiHat` satisfies the DKPS minimizer predicate. -/
theorem psiHat_isDKPS {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hEDM : IsEDM (n := n) (d := d) D) :
    IsDKPS (n := n) (d := d) D (psiHat (n := n) (d := d) D hEDM) :=
  Classical.choose_spec (exists_psiHat_isDKPS_of_IsEDM (n := n) (d := d) D hEDM)

end DKPS_Construction


/-!
## Benchmark setup

The paper fixes a finite benchmark query set `Q⋆` and defines a benchmark score `y(f, Q)`
for any subset `Q ⊆ Q⋆`. We keep `score` abstract, since different applications may use
different scoring rules.

- `yFull f` corresponds to `y(f, Q⋆)`
- `ySubset Qsub f` corresponds to `y(f, Qsub)`
-/
section Benchmark_Setup

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

variable (Qstar : Finset Q)
variable (score : Model Q X → Finset Q → ℝ)

def yFull (f : Model Q X) : ℝ := score f Qstar
def ySubset (Qsub : Finset Q) (f : Model Q X) : ℝ := score f Qsub

end Benchmark_Setup

/-!
## Query efficiency (paper Definition 1 + Definition 2)

The paper defines "query efficiency" as: for large enough sample size `n`, a learned estimator
achieves no worse population risk than a baseline estimator, while using fewer benchmark queries.

We define the (population) risk as an integral over a probability measure `Pf` on models.

- `QQueryEfficient` matches paper Def. 1 (efficiency relative to a fixed query set `Q`)
- `mQueryEfficient` matches paper Def. 2 (uniformly over all subsets of size `m`)
-/
section QueryEfficiency

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- Population risk `E_f[ ℓ(h(f), y(f)) ]` under `Pf`. -/
noncomputable def Risk
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (y h : Model Q X → ℝ) : ℝ :=
  ∫ f, ℓ (h f) (y f) ∂ Pf

/--
`QQueryEfficient Pf ℓ y h h'`:
there exists `N` such that for all `n > N`, the risk of `h_n` is at most the risk of `h'_n`.

This mirrors paper Definition 1.
-/
def QQueryEfficient
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (y : Model Q X → ℝ)
    (h h' : ℕ → Model Q X → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n > N,
    Risk (Q := Q) (X := X) Pf ℓ y (h n) ≤ Risk (Q := Q) (X := X) Pf ℓ y (h' n)

/--
`mQueryEfficient` is the uniform variant from paper Definition 2:
the inequality must hold for every subset `Qsub` with `|Qsub| = m`.
-/
def mQueryEfficient
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (m : ℕ) (y : Model Q X → ℝ)
    (h h' : Finset Q → ℕ → Model Q X → ℝ) : Prop :=
  ∀ Qsub : Finset Q, Qsub.card = m →
    ∃ N : ℕ, ∀ n > N,
      Risk (Q := Q) (X := X) Pf ℓ y (h Qsub n) ≤ Risk (Q := Q) (X := X) Pf ℓ y (h' Qsub n)

end QueryEfficiency

/-!
## Assumptions and main theorems

### What does "with high probability" mean?

Acharyya et al. define "with high probability" for a sequence of events `Eₙ` as:
`P(Eₙᶜ) = o(1)` as `n → ∞`, i.e. `P(Eₙ) → 1`.

A convenient (and equivalent) reformulation is:

> For every failure tolerance `δ > 0`, there exists `N` such that for all `n > N`,
> `Pₙ(Eₙ) ≥ 1 - δ`.

We encode that as `HighProbAtTop μ E`, where:
- `μ n` is a probability measure describing the random experiment at sample size `n`,
- `E n` is the corresponding "good event".

This captures the asymptotic meaning used by the cited work, while remaining flexible about
the underlying probability space.
-/
section Assumptions_And_Theorems

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- Asymptotic "with high probability" along `n → ∞`. -/
def HighProbAtTop {Ω : Type} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n)) (E : ℕ → Set Ω) : Prop :=
  ∀ δ : ENNReal, 0 < δ → ∃ N : ℕ, ∀ n > N, (μ n) (E n) ≥ 1 - δ

/--
Asymptotic "with high probability" along `n → ∞` when the probability space may depend on `n`.

This is the same `∀ δ>0, ∃ N, ∀ n>N, Pₙ(Eₙ) ≥ 1-δ` notion,
but written for a *dependent* family of spaces `Ω n` and measures `μ n`.
-/
def HighProbAtTopDep (Ω : ℕ → Type) (instΩ : ∀ n, MeasurableSpace (Ω n))
    (μ : ∀ n, Measure (Ω n)) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (E : ∀ n, Set (Ω n)) : Prop :=
  ∀ δ : ENNReal, 0 < δ → ∃ N : ℕ, ∀ n > N, (μ n) (E n) ≥ 1 - δ

/-- Shorthand for "event holds with probability at least `1-δ`" under a fixed measure. -/
def HighProb {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (δ : ENNReal) : Prop :=
  μ E ≥ 1 - δ

/--
Assumption 1 (Lipschitz score function).
-/
def LipschitzScore {d : ℕ} (γ : ℝ)
    (Psi : Finset Q → Model Q X → Vec d)
    (y : Model Q X → ℝ) : Prop :=
  ∀ (Qsub : Finset Q) (f f' : Model Q X),
    |y f - y f'| ≤ γ * ‖Psi Qsub f - Psi Qsub f'‖

/--
Assumption 2 (Nontrivial support).
-/
def ModelSupportNontrivial
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    [PseudoMetricSpace (Model Q X)] : Prop :=
  ∀ (f : Model Q X) (δ : ℝ), 0 < δ →
    ∃ ε : ENNReal, 0 < ε ∧ Pf (Metric.ball f δ) ≥ ε

/-!
### Theorem 1 (DKPS concentration), stated as a Lean `Prop`

In the Quench paper, *Theorem 1 is cited from prior work* (Acharyya et al., with a later
restatement in Helm et al.). We will **not** reprove it here, but we do want a Lean statement
that mirrors the paper closely so later theorems can depend on it.

Informally, the cited theorem assumes (among other technical conditions):

* `r = ω(n^3)`  (replicates grow faster than `n^3`)
* `sup_{i,j} γ_{ij} = O(1)` where `γ_{ij} = trace(Cov(F_{ij}))`
* bounded support / moment conditions on the embedded response distributions `F_{ij}`

and concludes a uniform DKPS embedding error bound (up to an orthogonal alignment `W*`)
that holds "with high probability" as `n → ∞`.

Below we:
1. Define the asymptotic and measure-theoretic predicates used in the assumptions.
2. Package the cited theorem as a `Prop` (`Theorem1`).
3. Provide a lemma `theorem1_from_prior_work` with proof `by sorry` so the rest of the file
   can use Theorem 1 as a black box.

(When we later attempt to **prove** the Quench results, we may want to specialize this statement
to the exact DKPS objects defined earlier in this file; for now we keep it abstract but technically
well-typed.)
-/

open scoped Topology

/-- `r = ω(n^3)` in the sense used by the cited DKPS concentration results:
`(n^3 / r) → 0` along `n → ∞` (and `r n > 0` eventually so the ratio is meaningful). -/
def ReplicateGrowth (r : ℕ → ℕ) : Prop :=
  (∀ᶠ n in atTop, 0 < r n) ∧
  Tendsto (fun n : ℕ => ((n : ℝ)^3) / (r n : ℝ)) atTop (𝓝 (0 : ℝ))

/-- A uniform bounded-support condition for a probability measure on a normed space. -/
def BoundedSupport {V : Type} [Norm V] [MeasurableSpace V] (μ : Measure V) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ (∀ᵐ x ∂ μ, ‖x‖ ≤ R)

/-- Mean (Bochner integral) of a vector-valued random variable under `μ`. -/
noncomputable def meanVec {p : ℕ} (μ : Measure (Vec p)) : Vec p :=
  ∫ x, x ∂ μ

/--
A "trace-of-covariance" scalar for a vector-valued distribution.

For a random vector `X`, `trace(Cov(X)) = E[‖X - E[X]‖²]`. This avoids introducing covariance
matrices explicitly, but matches the quantity `γ_{ij} = trace(Cov(F_{ij}))` used in the paper.
-/
noncomputable def traceCov {p : ℕ} (μ : Measure (Vec p)) : ℝ :=
  ∫ x, ‖x - meanVec (μ := μ)‖ ^ (2 : ℕ) ∂ μ

/--
Uniform `O(1)` bound on the trace-of-covariance quantities `γ_{ij}`.

This corresponds to the paper's assumption `sup_{i,j} γ_{ij} = O(1)`, which is equivalent to
the existence of a constant `C` such that **all** `γ_{ij}` are eventually bounded by `C`.
-/
def CovTraceBounded {m p : ℕ}
    (F : ∀ n : ℕ, Fin n → Fin m → ProbMeasure (Vec p)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ n in atTop, ∀ (i : Fin n) (j : Fin m),
      traceCov (μ := (F n i j).1) ≤ C

/-!
### Prior work assumptions (Helm et al. 2025)

The Quench paper's Theorem 1 is cited from Helm et al. (2025, Theorem 2). Besides the growth
and bounded-variance conditions (`r = ω(n^3)` and `sup_{i,j} γ_{ij} = O(1)`), the cited theorem
assumes:

* **Assumption 1:** for all sufficiently large `n`, `rank(Bₙ) = d` for a fixed `d`.
* **Assumption 2:** there exist constants `C₁, C₂ > 0` such that (eventually in `n`)
  `λ_d(Bₙ) > C₁` and `λ₁(Bₙ) < C₂`, where `λ₁(Bₙ)` and `λ_d(Bₙ)` are the largest and smallest
  *positive* eigenvalues of `Bₙ` (equivalently, the largest and smallest nonzero eigenvalues under
  Assumption 1).

In Lean we keep the population matrix `Bₙ` abstract for now, but we can state these assumptions
in standard linear-algebra terms.
-/

namespace Helm2025

/-- `λ` is an eigenvalue of a real square matrix `A` (witnessed by a nonzero eigenvector). -/
def IsEigenvalueMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = lam • v

/-- `λ₁` is a (not-necessarily-unique) top eigenvalue of `A` in the usual order. -/
def IsTopEigenvalueMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lam1 : ℝ) : Prop :=
  IsEigenvalueMat A lam1 ∧ ∀ mu : ℝ, IsEigenvalueMat A mu → mu ≤ lam1

/-- `λ_d` is the smallest *positive* eigenvalue of `A`. -/
def IsBottomPositiveEigenvalueMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lamd : ℝ) : Prop :=
  IsEigenvalueMat A lamd ∧ 0 < lamd ∧ ∀ mu : ℝ, IsEigenvalueMat A mu → 0 < mu → lamd ≤ mu

/-- Rank of a real square matrix as the `finrank` of its range as a linear map. -/
noncomputable def matRank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.range (A.mulVecLin))


/--
Assumption 1 from Helm et al. (2025): eventually `rank(Bₙ) = d`.

The paper phrases this as: "for all sufficiently large `n`, `rank(B) = d`".
-/
def Assumption1_rank (B : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ) (d : ℕ) : Prop :=
  ∀ᶠ n in atTop, matRank (B n) = d

/--
Assumption 2 from Helm et al. (2025): stability of the extreme nonzero eigenvalues.

The paper states: there exist constants `C₁, C₂ > 0` such that
`lim inf λ_d > C₁` and `lim sup λ₁ < C₂`. For real sequences, this is equivalent to an
"eventually" bound, which is what we encode here.
-/
def Assumption2_eigs (B : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ) (d : ℕ) : Prop :=
  ∃ (lambda₁ lambda_d : ℕ → ℝ) (C₁ C₂ : ℝ),
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ n, IsTopEigenvalueMat (B n) (lambda₁ n)) ∧
    (∀ n, IsBottomPositiveEigenvalueMat (B n) (lambda_d n)) ∧
    ∀ᶠ n in atTop, C₁ < lambda_d n ∧ lambda₁ n < C₂


/-- `‖x‖_{2,∞}` for a finite family of vectors: `max_i ‖x_i‖₂`. -/
noncomputable def norm2inf {n d : ℕ} (x : Fin n → Vec d) : ℝ :=
  -- For `n = 0`, there are no rows, so we return `0`.
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    (Finset.univ.image (fun i : Fin n => ‖x i‖)).max' (by
      rcases h with ⟨i, hi⟩
      refine ⟨‖x i‖, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  else
    0

/-- Apply an orthogonal alignment (a linear isometry) pointwise. -/
noncomputable def applyIso {n d : ℕ} (W : (Vec d) ≃ₗᵢ[ℝ] (Vec d)) (x : Fin n → Vec d) : Fin n → Vec d :=
  fun i => W (x i)

/--
**Theorem 1 (prior work, DKPS concentration / embedding error).**

This is the *statement* we want to use later.  It matches the Quench paper's Theorem 1:
under growth + bounded-variance + Assumptions 1–2 (rank and eigenvalue stability), there exists an alignment `W*`
such that `‖ψ̂ W* - ψ‖_{2,∞}` is bounded by a cubic polynomial in `(n^3 / r)^(1/2 - δ)`
with high probability for every fixed `δ ∈ (0, 1/2)`.

Notes on parameters:
- `Ω n` is the sample space generating the random DKPS estimate for size `n`.
- `ψHat n ω` is the *random* estimated embedding, while `ψ n` is the population embedding.
- `F n i j` is the distribution of embedded responses for model `i` and query `j` at size `n`.

**Theorem 2 (Helm et al. 2025, DKPS concentration / embedding error).**

This is the statement the Quench paper uses as its Theorem 1.

Under the growth, bounded-variance, and spectral stability assumptions, there exists an
alignment `W*` such that

`‖ψ̂ W* - ψ‖_{2,∞} ≤ Poly₃( (n^3 / r)^(1/2 - δ) )`

with high probability (as `n → ∞`) for every fixed `δ ∈ (0, 1/2)`.

Notes on parameters:
- `Ω n` is the sample space generating the random DKPS estimate for size `n`.
- `ψHat n ω` is the *random* estimated embedding, while `ψ n` is the population embedding.
- `F n i j` is the distribution of embedded responses for model `i` and query `j` at size `n`.
- `B n` is the population (doubly centered) dissimilarity matrix whose MDS embedding is `ψ n`.
-/
def Theorem2 {m p d : ℕ}
  (Ω : ℕ → Type) (instΩ : ∀ n, MeasurableSpace (Ω n))
  (μ : ∀ n, Measure (Ω n)) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (F : ∀ n : ℕ, Fin n → Fin m → ProbMeasure (Vec p))
  (B : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ)
  (r : ℕ → ℕ)
  (ψHat : ∀ n : ℕ, Ω n → Fin n → Vec d)
  (ψ : ∀ n : ℕ, Fin n → Vec d)
  (Poly3 : ℝ → ℝ) : Prop :=
  ReplicateGrowth r →
  CovTraceBounded (F := F) →
  Assumption1_rank (B := B) d →
  Assumption2_eigs (B := B) d →
  ∃ Wstar : ∀ n : ℕ, (Vec d) ≃ₗᵢ[ℝ] (Vec d),
    ∀ δgeom : ℝ, δgeom ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ) →
      HighProbAtTopDep (Ω := Ω) (instΩ := instΩ) (μ := μ) (hμ := hμ)
        (E := fun n => {ω : Ω n |
          norm2inf (fun i : Fin n => (Wstar n) (ψHat n ω i) - (ψ n i))
            ≤ Poly3 (Real.rpow (((n : ℝ)^3) / (r n : ℝ)) (1/2 - δgeom))
        })

end Helm2025

/--
**Theorem 1 (Quench paper).**

This is exactly Helm et al. (2025) Theorem 2, restated with the numbering used in the Quench paper.
-/
abbrev Theorem1 {m p d : ℕ} := (Helm2025.Theorem2 (m := m) (p := p) (d := d))

/--
We assume the prior-work DKPS concentration theorem (Theorem 1) without reproving it.

Later, if we decide to formalize the cited paper as well, this `sorry` can be replaced
by an actual proof (or by importing a separate file that proves it).
-/
theorem theorem1_from_prior_work {m p d : ℕ}
  (Ω : ℕ → Type) (instΩ : ∀ n, MeasurableSpace (Ω n))
  (μ : ∀ n, Measure (Ω n)) (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (F : ∀ n : ℕ, Fin n → Fin m → ProbMeasure (Vec p))
  (B : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ)
  (r : ℕ → ℕ)
  (ψHat : ∀ n : ℕ, Ω n → Fin n → Vec d)
  (ψ : ∀ n : ℕ, Fin n → Vec d)
  (Poly3 : ℝ → ℝ) :
  Theorem1 (Ω := Ω) (instΩ := instΩ) (μ := μ) (hμ := hμ)
           (F := F) (B := B) (r := r) (ψHat := ψHat) (ψ := ψ) (Poly3 := Poly3) := by
  intro hGrow hVar hRank hEig
  -- Cited from Acharyya et al. / Helm et al.
  sorry

/-!
### Loss functions used in Theorem 2

The paper uses square loss / MSE.
-/

/-- Squared loss (the paper uses MSE / square loss). -/
def sqLoss (a b : ℝ) : ℝ := (a - b) ^ (2 : ℕ)

/-- Mean squared error `E_f[(ŷ(f) - y(f))²]` under `Pf`. -/
noncomputable def MSE
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (y yHat : Model Q X → ℝ) : ℝ :=
  ∫ f, sqLoss (yHat f) (y f) ∂ Pf

/-!
## Theorem 2, split into Part 1 and Part 2

The paper's Theorem 2 has two claims:

- **Part 1 (accuracy):** for any target error `ε > 0`, the DKPS+NN estimator can achieve
  `MSE ≤ ε` with high probability (as `n → ∞`).

- **Part 2 (query-efficiency):** if a baseline estimator that uses fewer queries has strictly
  positive MSE, then the DKPS+NN estimator is query-efficient relative to that baseline.

In the paper, Part 2 is derived from Part 1 by picking `ε` smaller than the baseline error
and using the definition of query-efficiency (eventual risk domination).
-/

/--
Theorem 2, Part 1 (accuracy), stated in an *eventual* high-probability form.

We model randomness explicitly:
- `Ω` is the probability space containing the experiment randomness (sampling reference models,
  sampling responses to build `ψ̂`, etc.).
- `μ n` is the distribution of the experiment at sample size `n`.
- `hNN n ω f` is the estimator output for target model `f`.

The theorem asserts: for every `ε > 0`, eventually in `n`, the event
`MSE(hNN n ω) ≤ ε` has probability ≥ `1-δ` for every failure tolerance `δ`.
-/
theorem Theorem2_part1
  {Ω : Type} [MeasurableSpace Ω]
  (Qstar : Finset Q)
  (score : Model Q X → Finset Q → ℝ)
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω)
  (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (hNN : ℕ → Ω → Model Q X → ℝ) :
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop (μ := μ) (hμ := hμ)
      (E := fun n => {ω : Ω |
        MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ ε
      }) := by
  intro ε hε
  -- This will be proved using Assumptions 1,2 and Theorem1 (plus additional technical lemmas).
  sorry

/--
Theorem 2, Part 2 (query-efficiency), in the form used by the paper's definition.

We compare two (random) estimators:
- `hNN n ω`  : DKPS+NN estimator using `m` queries (implicitly, via its construction)
- `hQ  n ω`  : baseline estimator using only `m` benchmark queries

The statement says that with high probability (as `n → ∞`), the risk of `hNN n ω`
is eventually no larger than the risk of `hQ n ω`.

For squared loss, "risk" is exactly MSE.
-/
theorem Theorem2_part2
  {Ω : Type} [MeasurableSpace Ω]
  (Qstar : Finset Q)
  (score : Model Q X → Finset Q → ℝ)
  (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
  (μ : ℕ → Measure Ω)
  (hμ : ∀ n, IsProbabilityMeasure (μ n))
  (hNN hQ : ℕ → Ω → Model Q X → ℝ)
  (hQ_pos : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n > N, ∀ ω : Ω,
      c ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)) :
  HighProbAtTop (μ := μ) (hμ := hμ)
    (E := fun n => {ω : Ω |
      MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f)
        ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)
    }) := by
  classical
  rcases hQ_pos with ⟨c, hc_pos, N0, hN0⟩
  -- Set `ε = c/2` and apply Part 1.
  have hε_pos : (0 : ℝ) < c / 2 := by linarith
  have hp :=
    Theorem2_part1 (Q := Q) (X := X) (Ω := Ω)
      (Qstar := Qstar) (score := score) (Pf := Pf)
      (μ := μ) (hμ := hμ) (hNN := hNN) (ε := c / 2) hε_pos
  -- Unfold the high-probability definition and transfer the guarantee from the `ε`-event
  -- to the desired domination event using monotonicity of measure.
  intro δ hδ_pos
  rcases hp δ hδ_pos with ⟨N1, hN1⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hn0 : n > N0 := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : n > N1 := lt_of_le_of_lt (le_max_right _ _) hn

  -- If `MSE(hNN) ≤ c/2` and `MSE(hQ) ≥ c`, then `MSE(hNN) ≤ MSE(hQ)`.
  have hsubset :
      {ω : Ω |
          MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ c / 2}
        ⊆
        {ω : Ω |
          MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f)
            ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)} := by
    intro ω hω
    have hc : c ≤
        MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f) :=
      hN0 n hn0 ω
    have hhalf : c / 2 ≤ c := by linarith
    exact le_trans (le_trans hω hhalf) hc

  -- Apply the high-probability bound for the `ε`-event and use `measure_mono`.
  have hE1_ge :
      (μ n)
          {ω : Ω |
              MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ c / 2}
        ≥ 1 - δ :=
    hN1 n hn1

  have hE1_leE2 :
      (μ n)
          {ω : Ω |
              MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ c / 2}
        ≤
        (μ n)
          {ω : Ω |
              MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f)
                ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)} :=
    measure_mono hsubset

  have hE2_ge : (1 - δ) ≤
      (μ n)
        {ω : Ω |
            MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f)
              ≤ MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hQ n ω f)} := by
    have hE1_ge' : (1 - δ) ≤
        (μ n)
          {ω : Ω |
              MSE (Q := Q) (X := X) Pf (fun f => score f Qstar) (fun f => hNN n ω f) ≤ c / 2} := by
      simpa [ge_iff_le] using hE1_ge
    exact le_trans hE1_ge' hE1_leE2

  simpa [ge_iff_le] using hE2_ge

end Assumptions_And_Theorems

end QuenchICML
