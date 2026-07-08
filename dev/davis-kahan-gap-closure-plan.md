# Davis–Kahan gap-closure plan

Plan for closing the gaps between the Lean formalization and the literature, as
catalogued in `papers/DavisKahan-formalized-vs-literature.tex` §"What is not
formalized". Written for an Opus-level agent; every step names its target file,
statement shape, proof route, Mathlib/ForMathlib assets, pitfalls, and a
difficulty grade.

## Revision log

- **v1 (2026-07-07, Fable):** initial plan.
- **v2 (2026-07-07, Opus review):** added `## Opus review notes` R1–R8;
  rerated W2.4 to 4/5; added statement-first gate to Definition of done.
- **v3 (2026-07-07, Fable):** every R-note folded into the step text it
  concerns (see per-note status markers in the review section). Major change:
  **W5.1 rerouted from the spectral-integral argument to a purely algebraic
  contraction argument** — no Bochner integrals, no measurability, no
  operator-valued `∫`; rerated 5/5 → 3/5, which dissolves Opus's R6 descope
  concern. Division of labor: **Fable implements W5.1** (hardest item,
  route-discovery-sensitive) and the W2.4 statement-first stubs (the R1 design
  content); **everything else is for Opus**, now unblocked by the corrected
  routes below. Follow the house rules in `dev/mathlib-quality-adapter.md`
(provenance headers, golf gates, `lake build` green after every step, axiom
check `propext, Classical.choice, Quot.sound` on headline declarations).

## The five gaps (from the paper)

| # | Gap | Workstream |
|---|-----|------------|
| G1 | Operator-norm `‖sinΘ‖_op ≤ ‖S−T‖_op/g` and general unitarily-invariant-norm sinΘ | W5, W7 |
| G2 | tanΘ, sin2Θ, tan2Θ theorems | W6 |
| G3 | YWS aligned-basis bound (`‖V̂O−V‖_F ≤ 2^{3/2}·min{…}/Δ`) | W3 |
| G4 | YWS singular-vector extension (rectangular `A, Â`) | W4 |
| G5 | General-interval spectral subspaces (two-sided gap) | W1 |

Plus two enabling workstreams the paper implies but does not list: a canonical
principal-angle API (W0) and Hoffman–Wielandt (W2 — required for the *exact*
YWS constant-2 Frobenius branch, which the current Weyl bridge cannot deliver;
see W2.4 for why).

## Existing assets (verified 2026-07-07, all sorry-free)

In `ForMathlib/Analysis/InnerProductSpace/` (namespace `ForMathlib` unless noted):

- **DavisKahan.lean** — the engine. Overlap encoded as
  `∑_{i∈s} ∑_{j∉s} ‖⟪uᵢ, v̂ⱼ⟫‖²` with `u = hT.eigenvectorBasis hn`,
  `v̂ = hS.eigenvectorBasis hn`; ladder rungs `…_le_offDiag`, `…_le_residual`,
  `…_le_hilbertSchmidt`, `…_le_opNorm`; Weyl bridges `gap_of_eigengap`,
  `gap_of_rank_floor`; projector identity
  `sum_norm_sub_starProjection_span_sq_eq` (`‖P̂−P‖²_F = 2·overlap`, already
  stated for an **arbitrary** `s : Finset (Fin m)`).
- **Spectrum.lean** — cross-term identity
  `inner_eigenvectorBasis_map_sub_eigenvectorBasis`:
  `⟪uᵢ,(S−T)v̂ⱼ⟫ = (μⱼ−λᵢ)⟪uᵢ,v̂ⱼ⟫`.
- **CourantFischer.lean** — Courant–Fischer both directions; Weyl
  `abs_eigenvalues_sub_le` (`|λₖ(T)−λₖ(S)| ≤ ε`).
- **SchurHorn.lean** — `schurWeight hT hn e i k = ‖⟪vᵢ, e k⟫‖²`, doubly
  stochastic (`schurWeight_row_sum`, `schurWeight_col_sum`); Karamata
  majorization `convexOn_sum_re_inner_orthonormalBasis_self_le`.
- **EigenvalueChange.lean** — Birkhoff bridge
  `diag_mem_convexHull_perm_spectrum` (uses
  `doublyStochastic_eq_convexHull_permMatrix`); Davis Thm 4.1.
- **PositiveSqrt.lean** (`namespace LinearMap.IsPositive`) — spectral PSD
  `sqrt` with uniqueness, `ker_sqrt`, `range_sqrt`, `sq_norm_sqrt_apply`.
- **PartialIsometry.lean** — `IsPartialIsometry` predicate + operator
  characterizations, constructor `isPartialIsometry_of_isometryOn`.
- **PolarDecomposition.lean** — `abs A`, `polarFactor A`,
  `polar_decomposition : A = polarFactor A ∘ₗ abs A`, `ker/range_polarFactor`,
  unitary case `polarUnitaryEquiv`, CFC bridge.
- **IntertwiningUnitary.lean** — `spectralProjection b S` (rank-one sums),
  `OrthoProjFamily`, Davis §2 `intertwiningUnitary`, `sqSinAngle`.
- **RotationBound.lean** — Davis Thm 3.2 + `rotation_le_two_mul_offDiag`.
- **NearIsometry.lean** — quantitative polar factor over ℝ (pattern for
  eigenbasis-defined operator functions; has a `TODO(RCLike)`).

Mathlib (pinned master `308db4b`, toolchain v4.32.0-rc1) **has**:
`LinearMap.singularValues : ℕ →₀ ℝ` (descending, `singularValues_antitone`,
`sq_singularValues_fin`, `card_support_singularValues`) in
`Analysis/InnerProductSpace/SingularValues.lean`; matrix Frobenius norm
(scoped `Matrix.Norms.Frobenius`); CFC `sqrt`/`abs`; Rayleigh quotients;
`LinearMap.IsSymmetric.eigenvalues/eigenvectorBasis` (sorted);
`Submodule.starProjection` API; `doublyStochastic_eq_convexHull_permMatrix`;
rearrangement inequality (`Algebra/Order/Rearrangement.lean`,
`MonovaryOn.sum_smul_comp_perm_le_sum_smul` family); Bochner integration.

Mathlib **lacks** (do not search for these upstream): matrix SVD
factorization, Schatten/Ky Fan/unitarily invariant norms, symmetric gauge
functions, principal angles, Hoffman–Wielandt, polar decomposition
(ForMathlib supplies it), Weyl eigenvalue perturbation (ForMathlib supplies
it), operator Hilbert–Schmidt norm as a bundled norm (the project encodes
`‖B‖²_F` as `∑ₖ ‖B(bₖ)‖²` over an orthonormal basis — keep that convention).

## Statement-shape conventions (apply to every step)

- Variables: `{𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}`,
  hypotheses `hT : T.IsSymmetric`, `hn : finrank 𝕜 E = n`, eigendata via
  Mathlib's `hT.eigenvalues hn` / `hT.eigenvectorBasis hn`.
- Frobenius quantities as explicit finite sums (`∑ⱼ ‖(S−T)v̂ⱼ‖²`), never a
  bundled HS norm; operator-norm hypotheses in the elementwise form
  `hε : ∀ x, ‖(S−T) x‖ ≤ ε * ‖x‖` (matches `gap_of_eigengap`).
- Gap hypotheses as explicit `∀ i j, … → … → g ≤ |…|` quantifications.
- **Boundary eigenvalue conventions (per Opus R2):** never encode YWS's
  `λ₀ = ∞`, `λ_{p+1} = −∞` sentinels. State edge-touching gaps as two guarded
  hypotheses — `hlow : r ≠ 0 → Δ ≤ λ_{r-1}(T) − λ_r(T)` and
  `hhigh : s + 1 ≠ n → Δ ≤ λ_s(T) − λ_{s+1}(T)` (vacuous at the spectrum
  edges) — and phrase complement sums over the actual `sᶜ`, so no fictitious
  index is ever referenced. Applies to W1.2, W2.4, W4.3.
- Names follow the existing `sum_cross_norm_inner_eigenvectorBasis_sq_le_*`
  pattern; `theorem` over `lemma` except for definitional glue; every public
  declaration gets a docstring citing the paper result it formalizes.
- Each new file: staging provenance header (`/- Staged for Mathlib: … -/`),
  added to `ForMathlib.lean` only when sorry-free.

---

## W0 — Canonical principal-angle API (foundation)

New file `ForMathlib/Analysis/InnerProductSpace/PrincipalAngles.lean`.
This is the "full canonical-angle API" the paper names as missing, and it is
the shared substrate for G1, G2, G3. Build it on Mathlib's
`LinearMap.singularValues`.

**W0.1 — Singular-value glue lemmas. Difficulty 3/5.**
For `A : E →ₗ[𝕜] F` between finite-dim spaces, prove:
(a) `∑ i, singularValues A i ^ 2 = ∑ₖ ‖A bₖ‖²` for any orthonormal basis `b`
    (Frobenius² = sum of squared singular values; route: diagonalize
    `A.adjoint ∘ₗ A`, use `sq_singularValues_fin` + Parseval);
(b) `singularValues A i ≤ ‖A‖` pointwise, and if `∀ x, ‖A x‖ ≤ ‖x‖`
    (contraction) then `singularValues A i ≤ 1`
    (route: `hasEigenvalue_adjoint_comp_self_sq_singularValues` + Rayleigh);
(c) `∑ i ∈ range d, singularValues A i = re (∑ₖ ⟪bₖ, (abs A) bₖ⟫)` — trace of
    `PolarDecomposition.abs A` equals the sum of singular values (route:
    `abs A` is diagonal in the eigenbasis of `A†A` with entries
    `√λᵢ = σᵢ` by `sqrt_apply_eigenvectorBasis` + `sqrt_unique`);
(d) **`singularValues_adjoint : (A.adjoint).singularValues = A.singularValues`
    — confirmed ABSENT from the pinned Mathlib (Opus R4), must be built here.**
    Route: `A†A` and `AA†` have equal nonzero spectra (if `A†A v = λv`, `λ≠0`,
    then `Av` is an `AA†`-eigenvector; the two multiplicity counts match by
    rank), hence equal sorted positive eigenvalue lists, hence equal singular
    values after the zero-padding that `ℕ →₀ ℝ` handles for free. This is
    independently Mathlib-attractive — file a `comparator/candidate-*.json`.
Pitfall: `singularValues` is a `ℕ →₀ ℝ` (finsupp) — write index bookkeeping
lemmas once (`singularValues_fin` mediates `Fin (finrank) → ℕ`).

**W0.2 — Principal angles between equal-dimensional subspaces. Difficulty 3.5/5.**
*(Rewritten per Opus R3 — the original mixed a subspace-compression definition
with flat-encoding lemmas; the flat encoding is now the definition itself.)*
Given orthonormal families `u : Fin d → E` and `v : Fin d' → E` (chosen bases
of the two subspaces), define the **flat overlap operator**
`overlapMap u v : EuclideanSpace 𝕜 (Fin d') →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)`
with `(overlapMap u v) eⱼ = ∑ᵢ ⟪u i, v j⟫ • eᵢ`, and set
`cosPrincipalAngles u v := LinearMap.singularValues (overlapMap u v)`.
Do **not** introduce `↥U →ₗ ↥V` compressions anywhere — all three consumers
(W3.3, W5.2 identification, W6 angle forms) want the flat operator. Prove
basis-independence at the level of singular values (conjugating `overlapMap`
by the unitary change-of-basis matrices of `u` and of `v` fixes
`singularValues`), so the notion descends to the subspace pair; a thin
`Submodule`-level wrapper choosing `stdOrthonormalBasis` bases comes last, if
at all. Prove:
(a) antitone, values in `[0,1]` (contraction, W0.1(b): `‖(overlapMap u v) x‖
    ≤ ‖x‖` is Bessel/Parseval);
(b) symmetry `cosPrincipalAngles u v = cosPrincipalAngles v u` via
    `singularValues_adjoint` (W0.1(d) — a required build, not an existing
    lemma; Opus R4) plus `adjoint (overlapMap u v) = overlapMap v u`;
(c) `∑ i, (1 - cosPrincipalAngles u v i ^ 2) = ∑ᵢ∑_{j∉block} ‖⟪uᵢ,wⱼ⟫‖²` when
    `u, v` are orthonormal-basis blocks (`v = w` restricted to the block) —
    the bridge to the DavisKahan.lean overlap encoding (route: W0.1(a) on
    `overlapMap` gives `∑cos² = ∑ᵢⱼ‖⟪uᵢ,vⱼ⟫‖²`; the complementary Parseval
    lemma `OrthonormalBasis.norm_sq_sub_starProjection_span_image` converts
    `d − ∑ᵢⱼ` into the cross-block sum);
(d) `∑ₖ ‖(P_U − P_V) bₖ‖² = 2 ∑ i, sin²θᵢ` (compose (c) with the existing
    projector identity `sum_norm_sub_starProjection_span_sq_eq`);
(e) bridge to `OrthoProjFamily.sqSinAngle` in the rank-one case (compose with
    `sqSinAngle_ofOrthonormalBasis`);
(f) *(for W5.2)* `‖Q̂ ∘ P‖ = max i, sin θᵢ`-form identification, or at minimum
    the inequality `sinθ_max ≤ ‖Q̂ ∘ P‖` needed there.
Define `sinThetaSq u v : ℝ := ∑ i, (1 - cos² …)` as the canonical `‖sinΘ‖²_F`
and restate the sharp DK rung as a thin wrapper over
`sum_cross_…_le_hilbertSchmidt`.

---

## W1 — General-interval spectral subspaces (G5)

Extend `DavisKahan.lean` (or new sibling `DavisKahanInterval.lean` if the file
would pass ~900 lines).

**W1.1 — Engine over an arbitrary index block. Difficulty 2/5. ✅ DONE
2026-07-07 (Opus).** Added `sum_cross_norm_inner_eigenvectorBasis_sq_le_{offDiag,residual,hilbertSchmidt}_block`
taking independent row/column finsets `s t : Finset (Fin n)` with membership gap
hypothesis `∀ i ∈ s, ∀ j ∈ t, gap ≤ |λᵢ(T) − λⱼ(S)|`; the three `d`-block
lemmas are now one-line corollaries (signatures unchanged, external Acharyya
consumer intact). Library build green.
The cross-term engine never uses that the block is `{i | i < d}`; the
projector section already takes `s : Finset (Fin m)`. Generalize
`sum_cross_norm_inner_eigenvectorBasis_sq_le_offDiag/_residual/_hilbertSchmidt`
from the `(·<d)/(d≤·)` split to `s : Finset (Fin n)` with gap hypothesis
`∀ i j, i ∈ s → j ∉ s → g ≤ |hT.eigenvalues hn i − hS.eigenvalues hn j|`.
Keep the current `d`-block statements as one-line corollaries
(`s := univ.filter (·<d)`) so no downstream statement drifts. Mechanical:
re-run the same proofs with `Finset.sum_filter`-style bookkeeping replaced by
`∈ s` / `∉ s`.

**W1.2 — Interval-selected subspaces and two-sided gap. Difficulty 2/5. ✅ DONE
2026-07-07 (Opus).** Added `sum_cross_interval_sq_le_hilbertSchmidt` (rows =
`{i | λᵢ(T) ∈ [a,b]}`, any column block avoiding the `g`-enlarged interval),
the two-sided Weyl bridge `notMem_Ioo_eigenvalues_of_notMem_Ioo`, and the
composed `sum_cross_interval_sq_le_hilbertSchmidt_of_eigengap` (population
interval gap `δ`, `ε`-close ⇒ sharp bound with gap `δ − ε`). Uses the W1.1
block engine with independent row/column finsets exactly as the pitfall note
anticipated. G5 closed.
Define the selected block by spectral membership:
`s := univ.filter (fun i => hT.eigenvalues hn i ∈ Set.Icc a b)` and state:
if every eigenvalue of `S` outside the enlarged interval
`Set.Icc (a−g) (b+g)`… — concretely, hypothesis
`∀ j, j ∉ s' → hS.eigenvalues hn j ∉ Set.Ioo (a−g) (b+g)` where `s'` is the
matching `S`-block — then the W1.1 gap hypothesis holds and the full ladder
applies to the interval subspaces. Also provide the Weyl bridge: a two-sided
population gap (`spec T ∩ (a−δ, a) = ∅ = spec T ∩ (b, b+δ)`) plus
`‖S−T‖_op ≤ ε < δ` yields `g = δ − ε` (same proof pattern as
`gap_of_eigengap`, done on both sides). Deliverable: the paper's
"general-interval subspaces" bullet closes with statements about
`span (eigenvectors with λ ∈ [a,b])`.
Pitfall: the two `Finset`s (`T`-selected and `S`-selected) may have different
cardinalities without extra hypotheses; state the ladder with independent
`s s' : Finset (Fin n)` and a cross-gap hypothesis `i ∈ s → j ∉ s' → …` —
the engine is already asymmetric, so this is free — and only tie the
cardinalities in the interval corollary where Weyl forces them equal.

---

## W2 — Hoffman–Wielandt and the exact YWS theorem

New file `ForMathlib/Analysis/InnerProductSpace/HoffmanWielandt.lean`, then
`YuWangSamworth.lean`.

Why needed: the current formalization recovers YWS only through the Weyl
bridge, which needs an *operator-norm* smallness case-split. For the
Frobenius branch of `‖sinΘ‖_F ≤ 2·min{√d‖E‖_op, ‖E‖_F}/Δ` the case
`‖E‖_op ≤ Δ/2 < ‖E‖_F` is fine (hybrid gap `Δ/2` + sharp rung), but when
`‖E‖_op > Δ/2` the Frobenius branch is not recoverable from the hybrid bound
(`2‖E‖_F/Δ` can be far below the trivial bound `√d`). YWS's own residual
sandwich with Hoffman–Wielandt closes it uniformly.

**W2.1 — Sorted rearrangement lemma. Difficulty 2/5. ✅ DONE 2026-07-07
(Opus).** `HoffmanWielandt.lean` (new file):
`sum_mul_comp_perm_le_sum_mul_of_antitone` —
`∑ i, f (σ i) * g i ≤ ∑ i, f i * g i` for antitone `f g : Fin n → ℝ`. One line
via `Antitone.monovary` + `Monovary.sum_comp_perm_smul_le_sum_smul`. Registered,
build green, axiom-clean. (Note: needs `import Mathlib.Data.Real.Basic` — the
abstract Rearrangement file does not pull in ℝ's order instances.)

**W2.2 — Trace inequality `tr(TS) ≤ ∑ λᵢ(T)·λᵢ(S)`. Difficulty 3/5. ✅ DONE
2026-07-07 (Opus).** `HoffmanWielandt.lean`:
`sum_mul_sum_mul_le_sum_mul_of_antitone` (abstract Birkhoff bilinear bound:
`∑ₖ aₖ ∑ⱼ Mₖⱼ bⱼ ≤ ∑ᵢ aᵢbᵢ` for antitone `a,b`, doubly-stochastic `M`, via
`doublyStochastic_eq_convexHull_permMatrix` + `permMatrix_mulVec` + W2.1 at each
vertex) and `sum_eigenvalues_mul_re_inner_self_le` (von Neumann trace
inequality, discharged from the bilinear bound with `M = schurWeight`). Axiom-clean.
Statement (basis-free trace avoided): `∑ₖ re ⟪T (vₖ), S? …⟫` — cleanest form:
`∑ k, hT.eigenvalues hn k * re ⟪uₖ, S uₖ⟫ ≤ ∑ i, λᵢ(T) * λᵢ(S)` where
`uₖ = hT.eigenvectorBasis`. Route: `re⟪uₖ, S uₖ⟫ = ∑ⱼ wⱼₖ λⱼ(S)` with
`w = schurWeight hS hn (hT.eigenvectorBasis hn)` (exists:
`re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul`); the double sum is a
doubly-stochastic image, bounded via Birkhoff
(`doublyStochastic_eq_convexHull_permMatrix`, pattern already worked out in
`diag_mem_convexHull_perm_spectrum`) + W2.1 on each permutation vertex.
The convex-combination argument: a linear functional on a convex hull is
maximized at a vertex — use `Finset.inner_le` style or just expand the convex
combination directly.

**W2.3 — Hoffman–Wielandt. Difficulty 3/5. ✅ DONE 2026-07-07 (Opus).**
`HoffmanWielandt.lean`: `sum_sq_eigenvalues_sub_le_sum_sq_norm_apply` —
`∑ᵢ(λᵢ(T)−λᵢ(S))² ≤ ∑ₖ‖(S−T)uₖ‖²`. Route exactly as planned: per-column
`norm_sub_sq` expansion, the helper `sum_sq_norm_apply_eq_sum_sq_eigenvalues`
(basis-independence `∑ₖ‖S eₖ‖² = ∑ᵢλᵢ(S)²`, double-Parseval swap), and W2.2 for
the cross term; `linarith` closes. Axiom-clean. **W2 (Hoffman–Wielandt) complete
— unblocks W2.4/W4.**
`∑ i, (hT.eigenvalues hn i − hS.eigenvalues hn i)² ≤ ∑ₖ ‖(S−T)(bₖ)‖²`
(any orthonormal basis `b`; instantiate at `hT.eigenvectorBasis`).
Route: expand `‖S−T‖²_F = ∑λᵢ(T)² + ∑λᵢ(S)² − 2·"tr(TS)"` where the trace
term is `∑ₖ re⟪T(bₖ),S(bₖ)⟫` evaluated in the `T`-eigenbasis
(`= ∑ₖ λₖ(T)·re⟪uₖ,S uₖ⟫`), then W2.2. The `‖·‖²_F` expansion needs a small
lemma `∑ₖ‖(S−T)bₖ‖² = ∑ₖ(‖T bₖ‖² + ‖S bₖ‖² − 2 re⟪T bₖ, S bₖ⟫)` plus
basis-independence of each trace-like sum (pattern:
`sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues` in SchurHorn.lean and
the Parseval lemmas in DavisKahan.lean).
Pitfall: keep everything real-part-explicit; `⟪T bₖ, S bₖ⟫` is not real
termwise-symmetric until summed — prove the summed symmetrization.

**W2.4 — YWS theorem, exact form. Difficulty 4/5 (rerated per Opus R1). ✅ DONE
2026-07-07 (Opus).** `YuWangSamworth.lean`: `residualColumn` +
`inner_eigenvectorBasis_residualColumn` (the R1 T-only cross-term identity),
`residualColumn_eq` (perturbation-column form), lower bound
`sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn` (population gap, Bessel),
upper bound `sum_sq_norm_residualColumn_le` (Hoffman–Wielandt + basis
independence), and the headline `sq_gap_mul_sum_cross_le_of_population_gap`
(`Δ²·overlap ≤ 4‖S−T‖²_F`) with the `‖sinΘ‖_F` form
`sqrt_sum_cross_le_of_population_gap` (`‖sinΘ‖_F ≤ 2‖S−T‖_F/Δ`). Verified via
`lake env lean` + axiom-clean. **Simplification vs plan:** the `(a+b)²≤2a²+2b²`
bound replaces the Minkowski step and preserves YWS's exact constant 2 (√ of 4).
**Frobenius branch; the √d operator-norm branch and d=1 corollary remain.**
*(Route rewritten per Opus R1 — the original text second-guessed the residual;
this version is re-derived against `prose/Yu-Wang-Samworth-2014…` and is the
committed design. Statement-first gate applies: land the `sorry` stubs below
before proving anything.)*

In `YuWangSamworth.lean`. Headline (commit to this statement first):
`‖sinΘ‖_F ≤ 2·min{√d·‖E‖_op, ‖E‖_F}/Δ` with `Δ` population-only, in the
squared sum-encoded form `Δ² · overlap ≤ (2·min{√d·ε_op, ε_F})²`, with the
gap given by the two guarded hypotheses of the R2 convention
(`hlow : r ≠ 0 → …`, `hhigh : s + 1 ≠ n → …`).

**Residual (the R1 correction).** Never form an operator `R`; work with the
columns
`Rⱼ := (λⱼ(T) : 𝕜) • v̂ⱼ − T v̂ⱼ` for `j` in the block — the **population
eigenvalue at the matched sorted index `j`** times the **sample eigenvector**.
The quantity `‖R‖²_F` is `∑_{j∈block} ‖Rⱼ‖²`.

**Stub 1 — T-only cross-term identity** (new lemma, trivial, goes next to
`Spectrum.lean`'s mixed identity):
`⟪uₖ, Rⱼ⟫ = ((λⱼ(T) − λₖ(T)) : 𝕜) * ⟪uₖ, v̂ⱼ⟫` — both multipliers are
`T`-eigenvalues; proof is `hT.apply_eigenvectorBasis` + `IsSymmetric`, and it
does **not** factor through `inner_eigenvectorBasis_map_sub_eigenvectorBasis`.

**Stub 2 — lower bound (population-gap engine):**
`Δ² · ∑_{j∈block}∑_{k∉block} ‖⟪uₖ, v̂ⱼ⟫‖² ≤ ∑_{j∈block} ‖Rⱼ‖²`.
Proof shape = the existing `offDiag → residual` enlargement: Stub 1 turns each
cross pair into `(λⱼ(T)−λₖ(T))²‖⟪uₖ,v̂ⱼ⟫‖² `, sortedness
(`eigenvalues_antitone`) plus the guarded `Δ`-hypotheses give
`|λⱼ(T)−λₖ(T)| ≥ Δ` for `j ∈ block ∌ k` (`k < r` uses `hlow`, `k > s` uses
`hhigh`), and row Parseval (`sum_sq_norm_inner_…_eq_row` pattern) enlarges
`∑_{k∉block}` to `‖Rⱼ‖²`.

**Stub 3 — upper bound, both branches.** Column identity (uses
`S v̂ⱼ = λⱼ(S)v̂ⱼ`):
`Rⱼ = (S−T) v̂ⱼ − ((λⱼ(S) − λⱼ(T)) : 𝕜) • v̂ⱼ`. Then
- Frobenius: `√(∑‖Rⱼ‖²) ≤ √(∑_{block}‖(S−T)v̂ⱼ‖²) + √(∑_{block}(λⱼ(S)−λⱼ(T))²)
  ≤ ‖E‖_F + ‖E‖_F` — first term by enlarging the block to all `j` (the
  existing residual→hilbertSchmidt enlargement), second by
  **Hoffman–Wielandt (W2.3)**;
- operator: `≤ √d·ε_op + √d·ε_op` — per-column `‖(S−T)v̂ⱼ‖ ≤ ε_op` and
  per-index Weyl `|λⱼ(S)−λⱼ(T)| ≤ ε_op` (`abs_eigenvalues_sub_le`).
*Pitfall:* the `√(∑‖aⱼ+bⱼ‖²)` triangle step is the `L²`-family Minkowski
inequality — do **not** expand squares and Cauchy–Schwarz by hand; package
the families as elements of `EuclideanSpace ℝ (Fin d)` (of norms) or
`PiLp 2 (fun _ : Fin d => E)` and use `norm_add_le`. State Stubs 2–3 squared
to keep `Real.sqrt` out of everything except the final assembly.

**Assembly:** `Δ·√overlap ≤ √(∑‖Rⱼ‖²) ≤ 2·min{√d ε_op, ε_F}`. Also derive the
`d = 1` eigenvector corollary (YWS Corollary 1, with sign-alignment
`re⟪v̂,v⟫ ≥ 0 → ‖v̂−v‖ ≤ √2 sinθ`).
Depends on: W1.1 (block-general engine vocabulary), W2.3.

---

## W3 — YWS aligned-basis bound (G3)

Same file `YuWangSamworth.lean` (or `AlignedBasis.lean` if it grows).
Operator-native statement of `∃ orthogonal O, ‖V̂O − V‖_F ≤ 2^{3/2}·min{…}/Δ`:

> There is an orthonormal family `w : Fin d → E` with
> `span w = span (v̂-block)` and
> `∑ i, ‖w i − u i‖² ≤ 2 · overlap(u-block, v̂-block)`,
> hence `√(∑‖wᵢ−uᵢ‖²) ≤ 2^{3/2}·min{√d ε_op, ε_F}/Δ`.

(`w = V̂O` in matrix language; spanning + orthonormality is the faithful
operator rendering of right-multiplication by orthogonal `O`.)

**W3.1 — Unitary polar decomposition in finite dimension. Difficulty 3/5.**
Extend `polarFactor` to a genuine unitary when `E = F` (square case):
`∃ U : E ≃ₗᵢ[𝕜] E, ∀ x, A x = U ((abs A) x)`. Route: `polarFactor A` is a
partial isometry with `ker = ker A`, `range = range A`;
`finrank (ker A) = finrank (range A)ᗮ` (rank-nullity + orthogonal complement
dims), so pick any linear isometry equiv between them
(`LinearIsometryEquiv` from two orthonormal bases of equal-dim subspaces —
`stdOrthonormalBasis`-based, or reuse the extension idiom from
`GramMatrix.lean`'s `LinearIsometry.extend`) and glue along
`(ker A) ⊕ (ker A)ᗮ`. This is an independently Mathlib-worthy lemma; put it
in `PolarDecomposition.lean`.
Pitfall: gluing two maps along an internal direct sum with isometry — use
`Submodule.isCompl_orthogonal` + `LinearMap.ofIsCompl`, prove isometry via
Pythagoras on the orthogonal decomposition, then
`LinearIsometryEquiv.ofSurjective` (pattern in `NearIsometry.lean`).

**W3.2 — `|tr(U A)| ≤ tr A` for positive `A`, unitary `U`. Difficulty 2/5.**
Statement: `hA : A.IsPositive` → `‖∑ₖ ⟪bₖ, (U ∘ₗ A) bₖ⟫‖ ≤ ∑ₖ re⟪bₖ, A bₖ⟫`.
Route: `tr(UA) = ⟨(√A)U†, √A⟩_HS`-style Cauchy–Schwarz:
`∑ₖ ⟪bₖ, U(A bₖ)⟫ = ∑ₖ ⟪√A(U† bₖ), √A bₖ⟫`, then Cauchy–Schwarz on the sum
and `∑ₖ‖√A(U†bₖ)‖² = ∑ₖ‖√A bₖ‖² = tr A` (unitary invariance of the basis
sum — a small lemma worth stating separately:
`∑ₖ ‖B (U bₖ)‖² = ∑ₖ ‖B bₖ‖²`, i.e. Frobenius sums are unitarily invariant
in the vector argument; also needed by W5/W7). Uses `sq_norm_sqrt_apply`.

**W3.3 — Trace–singular-value–angle chain. Difficulty 3/5.**
For the overlap compression `M : ↥(span v̂-block) →ₗ ↥(span u-block)` (or its
flat `d×d` matrix `Mᵢⱼ = ⟪uᵢ, v̂ⱼ⟫` — prefer the flat matrix on
`EuclideanSpace 𝕜 (Fin d)` to dodge subspace coercions):
(a) `tr (abs M) = ∑ σᵢ(M)` (W0.1(c));
(b) `σᵢ(M) ≤ 1` (W0.1(b): `M` is a compression of the identity);
(c) `∑ᵢ σᵢ(M) ≥ ∑ᵢ σᵢ(M)² = ∑ᵢⱼ ‖Mᵢⱼ‖² = d − overlap` (W0.1(a) +
    complementary Parseval).

**W3.4 — Assemble the aligned-basis theorem. Difficulty 4/5.**
*(Corrected per Opus R5, load-bearing:)* `O` **must** be the genuine
*kernel-completed unitary* from W3.1, **never** the bare `polarFactor M`
partial isometry. When a principal angle hits `π/2`, `M` is singular; with the
bare partial isometry `w` fails orthonormality and `tr(O†M) = tr|M|` breaks.
With W3.1's unitary, `O† ∘ M = |M|` holds as an **equality regardless of
`M`'s rank** — this equality (not an inequality via W3.2) is what the cross
term reduces to, and is the whole reason W3 avoids the SVD Mathlib lacks. Do
W3.1 first; W3.2 stays as the general von-Neumann-lite lemma (used to show the
chosen `O` is *optimal*, an optional remark, not on the critical path).

Set `w j := ∑ᵢ (O)ᵢⱼ • v̂ᵢ` where `O = ` the unitary polar factor of `M†`
(W3.1 at the `d`-dimensional level). Compute
`∑ⱼ ‖wⱼ − uⱼ‖² = 2d − 2 re tr(O† M) = 2d − 2 tr(abs M)` (polar decomposition
makes the cross term the trace of `abs M` exactly — no inequality needed on
this step), then by W3.3(c): `≤ 2d − 2(d − overlap) = 2·overlap`. Chain with
W2.4 for the `2^{3/2}` headline, and with the hybrid sharp rung for a
gap-hypothesis version (`√2·‖E‖_F·√2/g` form) so the theorem is usable
without the YWS `Δ` packaging.
Pitfalls: (i) orthonormality and spanning of `w` come from `O` unitary —
prove `Orthonormal 𝕜 w` via `∑ᵢ conj Oᵢⱼ Oᵢₖ = δⱼₖ`; (ii) mind conjugation
conventions in `⟪·,·⟫` (Mathlib inner is conjugate-linear in the *first*
argument) when identifying the cross term with `tr(O†M)`; over ℝ this
disappears — do **not** take the ℝ-only shortcut, state over `RCLike`
(YWS is real, but the proof is field-agnostic and the DK core is `RCLike`).
Depends on: W0.1, W3.1–W3.3; the headline constant additionally on W2.4.

---

## W4 — YWS singular-vector extension (G4)

New file `ForMathlib/Analysis/InnerProductSpace/SingularSubspace.lean`.
Setting: `A Â : E →ₗ[𝕜] F`, right-singular subspaces = spectral subspaces of
`A.adjoint ∘ₗ A` (self-adjoint, positive).

**W4.1 — Gram perturbation bound. Difficulty 2/5.**
`∀ x, ‖(Â†Â − A†A) x‖ ≤ (‖A‖ + ‖Â‖)·‖Â−A‖·‖x‖`, in the elementwise-ε form
used by the DK gap bridges. Route:
`Â†Â − A†A = Â†(Â−A) + (Â†−A†)A`, triangle inequality + `‖A†‖ = ‖A‖`
(Mathlib `LinearMap.adjoint` + opNorm lemmas; if the flat `∀ x` form is used
throughout, prove the adjoint step via
`‖A† y‖² = re⟪A A† y, y⟫ ≤ ‖A‖‖A†y‖‖y‖`).

**W4.2 — Singular-value Weyl + eigen/singular dictionary. Difficulty 3/5.**
(a) `λᵢ(A†A) = σᵢ(A)²` sorted-form dictionary between
    `(isSymmetric_adjoint_mul_self).eigenvalues hn` and
    `LinearMap.singularValues` (Mathlib's `sq_singularValues_fin` is close;
    align the sorting/indexing conventions once, as lemmas);
(b) Weyl for squared singular values:
    `|σᵢ(Â)² − σᵢ(A)²| ≤ ε_gram` via `abs_eigenvalues_sub_le` applied to the
    Gram operators with W4.1.

**W4.3 — YWS Theorem 3 (singular-subspace bound). Difficulty 3/5.**
Apply W2.4 (or, for the hybrid-gap version, the W1.1 ladder) to
`T := A†A`, `S := Â†Â`, gap `Γ = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})`.
The right-hand side unfolds to
`2·min{√d·(‖A‖+‖Â‖)‖Â−A‖, …_F}/Γ`; for the Frobenius branch of the numerator
YWS state `‖Â†Â−A†A‖_F` directly — provide both forms and a corollary
substituting the W4.1 product bound. Left-singular subspaces: state the
mirror via `A A†` (one-line corollary swapping `A ↔ A†`).
Depends on: W1.1/W2.4, W4.1, W4.2.

---

## W5 — Operator-norm sinΘ theorem (G1, op-norm case)

New files `ForMathlib/Analysis/InnerProductSpace/SylvesterBound.lean` and
extension of `DavisKahan.lean`.

**W5.1 — The Sylvester-solution bound. Difficulty 3/5 (was 5/5) — REROUTED
(v3, Fable). ✅ DONE 2026-07-07:** `SylvesterBound.lean` (helper
`norm_le_of_abs_re_inner_map_self_le` + coercive `opNorm_le_div_of_comp_add_comp_eq`
+ separated `opNorm_le_div_of_comp_sub_comp_eq`), registered in
`ForMathlib.lean`, `lake build` green (8709 jobs), all three headline
declarations axiom-clean. Bonus generality over the plan: **no
finite-dimensionality and no completeness** — the Rayleigh-quotient helper
made the eigenbasis unnecessary, so the bound holds for bounded symmetric
operators on arbitrary inner product spaces. The spectral-integral route and its
Bochner-integral risks (Opus R6) are **abandoned**. The replacement is a
purely algebraic one-inequality argument; no integrals, no measurability, no
fixed-point theorem, works verbatim over `RCLike` between two different
spaces.

*Headline lemma (coercive/Lyapunov form).* `A : E →L[𝕜] E`, `B : F →L[𝕜] F`
self-adjoint with `δ > 0` and
`hA : ∀ x, δ‖x‖² ≤ re⟪A x, x⟫`, `hB : ∀ v, δ‖v‖² ≤ re⟪B v, v⟫`.
If `A ∘L X + X ∘L B = Y` then `‖X‖ ≤ ‖Y‖ / (2δ)`.

*Proof (verified on paper, v3).* WLOG `X ≠ 0` (else trivial); then `E, F`
are nontrivial and evaluating the coercivity at a nonzero vector against
Cauchy–Schwarz gives `δ ≤ a := ‖A‖` and `δ ≤ b := ‖B‖`. Pure algebra from
the hypothesis:
`(a+b) • X = Y + (a•1 − A) ∘L X + X ∘L (b•1 − B)`.
The helper lemma below gives `‖(a•1−A)w‖ ≤ (a−δ)‖w‖` (the symmetric operator
`a•1−A` has quadratic form in `[0, (a−δ)‖·‖²]`) and likewise for `b•1−B`.
Pointwise for any `v`:
`(a+b)‖Xv‖ ≤ ‖Y‖‖v‖ + (a−δ)‖Xv‖ + (b−δ)‖X‖‖v‖`,
so `(b+δ)‖Xv‖ ≤ (‖Y‖ + (b−δ)‖X‖)‖v‖`; by `opNorm_le_bound`,
`(b+δ)‖X‖ ≤ ‖Y‖ + (b−δ)‖X‖`, i.e. `2δ‖X‖ ≤ ‖Y‖`. ∎
Note the asymmetry is harmless: the `(a−δ)‖Xv‖` term is absorbed pointwise,
the `(b−δ)` term after taking the sup — only one scalar solve.

*Helper lemma* (independently useful; symmetric-operator norm from the
quadratic form): `C.IsSymmetric`, `∀ x, |re⟪C x, x⟫| ≤ κ‖x‖²` ⟹
`∀ x, ‖C x‖ ≤ κ‖x‖`. Proof: eigen-expansion — each eigenvalue satisfies
`|λᵢ| ≤ κ` (plug the eigenvector), then
`‖Cx‖² = ∑ λᵢ²‖⟪bᵢ,x⟫‖² ≤ κ²‖x‖²` by Parseval; exactly the
`CourantFischer.lean` expansion pattern. Check first whether Mathlib's
Rayleigh file already has a usable form (`norm_eq_iSup_rayleighQuotient`
vicinity); if yes, use it, else stage this.

*DK-facing corollary (separated form).* `hA : ∀ x, (c+g)‖x‖² ≤ re⟪A x, x⟫`,
`hB : ∀ v, re⟪B v, v⟫ ≤ c‖v‖²`, `A ∘L X − X ∘L B = Y` ⟹ `‖X‖ ≤ ‖Y‖ / g`.
Shift `A' := A − (c+g/2)•1`, `B' := (c+g/2)•1 − B`, `δ := g/2`; then
`A'∘X + X∘B' = A∘X − X∘B = Y` and both coercivity hypotheses hold. Mind the
scalar casts: the shift is `((c+g/2 : ℝ) : 𝕜) • 1`, self-adjoint by
`RCLike.conj_ofReal`, with `re⟪(r:𝕜)•x, x⟫ = r‖x‖²`.

*Why quadratic-form hypotheses (not spectra):* they are exactly what the
compressions in W5.2 can discharge — the quadratic form of `S` on the
trailing span is `≤ c‖·‖²` by the (currently `private`) CourantFischer lemma
`re_inner_map_self_le_of_mem_specSubspace`; no compression-spectrum lemma
needed at all. Statements stay eigenvalue-index-free, the most
Mathlib-idiomatic form.
Do NOT attempt the general two-interval separation (constant π/2 territory);
half-line is what the DK hybrid gap needs.

**W5.2 — Operator-norm sinΘ. Difficulty 3.5/5 (was 4/5; simplified by the
W5.1 reroute).**
`‖Q̂ ∘ P‖ ≤ ε/g` where `P` = starProjection onto the `T`-leading block span,
`Q̂` = onto the `S`-trailing block span, hybrid gap `g` as in the ladder.
Route: compress to `X := (v ∈ ran P) ↦ Q̂ v` as a map `↥(ran P) →L ↥(ran Q̂)`;
the Sylvester relation
`(S compressed to ran Q̂) ∘ X − X ∘ (T compressed to ran P) = (compressed E)`
follows from invariance (`S`-spectral subspaces are `S`-invariant, `T`'s are
`T`-invariant; `Submodule`-restriction of a symmetric map to an invariant
subspace is symmetric — Mathlib `LinearMap.IsSymmetric.restrict_invariant`,
verify the exact name). Because W5.1's corollary takes **quadratic-form**
hypotheses, no compression-spectrum lemma is needed: coercivity of the
compressed `T` on the leading span (`(c+g)‖·‖² ≤ re⟪T·,·⟫`) and the upper
form bound for compressed `S` on the trailing span are exactly the
CourantFischer.lean private pair
`le_re_inner_map_self_of_mem_specSubspace` /
`re_inner_map_self_le_of_mem_specSubspace` — **un-`private` these two (and
`specSubspace` if needed) as part of this step** rather than re-deriving.
`‖compressed E‖ ≤ ‖S−T‖` since the inclusion is an isometry and `Q̂` is a
contraction; finally `‖Q̂ ∘ P‖ ≤ ‖X‖` by factoring through `P`.
Then identify `‖Q̂ P‖` with `sinΘ_op` (largest principal angle sine —
W0-level lemma: `‖Q̂P‖ = max singular value of the cross compression`) and
state the headline `‖sinΘ‖_op ≤ ‖S−T‖_op/g`, plus the projector corollary
`‖P̂ − P‖_op ≤ …` if wanted (`‖P̂−P‖ = max(‖Q̂P‖, ‖P̂Q‖)` — optional, rank
separately as a stretch lemma).
Depends on: W0.2, W5.1, W1.1 (for the general-block statement).

---

## W6 — sin2Θ / tan2Θ (G2)

New file `ForMathlib/Analysis/InnerProductSpace/RotationSharp.lean`.
Davis's 2×2-compression results (digest: `prose/Davis-1963-core-arguments.tex`
§"The sharp two-subspace estimate").

**W6.1 — Per-eigenvector sin2θ bound. Difficulty 4/5.**
Setting: `T` self-adjoint with `spec T ∩ (−1, 1) = ∅` (after rescaling — state
with explicit `a < b` half-spaces and a midpoint/radius normalization done in
the proof, not the statement: hypotheses `P := spectral proj of T on [b,∞)`,
`spec T ⊆ (−∞,a] ∪ [b,∞)`), `x` a unit eigenvector of `S = T + H` with
eigenvalue `≥ (a+b)/2`, `θ` the angle given by `cos θ = ‖P x‖`. Conclusion:
`sin 2θ ≤ 2‖H‖/(b−a)` (Davis's `sin 2θ ≤ δ` after scaling).
Route (Davis's compression): let `p = Px/‖Px‖`, `q = (1−P)x/‖(1−P)x‖`
(degenerate cases `Px = 0` / `(1−P)x = 0` handled first — they give `θ ∈
{0, π/2}` and the bound is direct), work entirely with the four scalars
`⟪p, T p⟫, ⟪q, T q⟫, ⟪p, H p⟫, ⟪q, H q⟫, ⟪p, H q⟫` — the "2×2 matrix" never
needs to exist as an object; the eigenvalue equation `⟪p, (S−λ̂)x⟫ = 0 =
⟪q, (S−λ̂)x⟫` yields the two scalar identities, subtract and bound.
`sin 2θ = 2 sinθ cosθ` via `Real.sin_two_mul`; define θ implicitly —
cleanest: avoid θ entirely and state the conclusion as
`2·‖Px‖·‖(1−P)x‖·(b−a) ≤ 2‖H‖` — i.e. a product-form inequality; provide the
`Real.arccos`-angle corollary separately for the literature-facing form.
Pitfalls: `⟪p, T q⟫ = 0` needs `P T = T P` and orthogonality of the spectral
split (spectralProjection API); phase alignment over ℂ (Davis chooses a phase
making `⟪p, H q⟫` effectively real — multiply `q` by the unimodular
`conj (⟪p,Hq⟫)/‖⟪p,Hq⟫‖`, the idiom used in RotationBound.lean's
intertwining lemma).

**W6.2 — Per-eigenvector tan2θ bound under vanishing pinch. Difficulty 3/5**
(given W6.1's scaffolding). Add hypothesis `P H P = 0` and
`(1−P) H (1−P) = 0` (diagonal blocks vanish); same scalar identities now give
`tan 2θ ≤ 2‖H‖/(b−a)` with **no smallness assumption**. Reuses everything
from W6.1; the only new content is the final scalar rearrangement.

**W6.3 — (Stretch) subspace-level sin2Θ theorem. Difficulty 5/5.**
The full DK-family subspace `sin2Θ`/`tan2Θ` theorems in unitarily invariant
norms are part-III material needing W7; the Frobenius-summed versions of
W6.1/W6.2 over an eigenbasis of `S` are reachable (sum the per-vector squares
— same pattern as the existing ladder) — do the Frobenius-summed version,
defer the op-norm version to post-W7. Mark as optional in the same PR.

---

## W7 — Unitarily invariant norms (G1, general case) — OPTIONAL / DEFER

A self-contained mini-library (symmetric gauge functions, Ky Fan k-norms,
majorization ⇒ norm domination, von Neumann trace inequality), prerequisite
for the *full* part-III statement and W6.3-op. Recommendation: **defer to a
separate project** — it is a Mathlib-sized contribution on its own
(`Analysis/UnitarilyInvariantNorm/…`), and the Frobenius + operator-norm pair
(W1–W6) already covers every application downstream in this repo (DKPS
pipeline consumes Frobenius bounds only). If undertaken:
W7.1 Ky Fan k-norms via `singularValues` partial sums + Ky Fan variational
principle (difficulty 4/5); W7.2 majorization ⇒ all-Ky-Fan domination ⇒
unitarily invariant norm domination (Fan dominance, 5/5); W7.3 extend the
Sylvester bound to any UI norm (note: W5.1's v3 algebraic route is op-norm
native; the UI-norm extension re-runs the same one-inequality argument using
submultiplicativity `|||CX||| ≤ ‖C‖·|||X|||` of UI norms against op-norm
factors, which W7.1–2 provide — no integrals needed here either; 3/5 given
W7.1–2); W7.4 part-III sinΘ for all UI norms (4/5).

---

## Execution order and dependency graph

```
W0.1 ──→ W0.2 ──→ (W3.3, W5.2 identification, W6 angle forms)
W1.1 ──→ W1.2                               [independent start]
W1.1 ──→ W2.4 ←── W2.1 → W2.2 → W2.3        [W2.1 independent start]
W2.4 ──→ W3.4 ←── W3.1, W3.2, W3.3 (←W0.1)
W2.4/W1.1 ──→ W4.3 ←── W4.1, W4.2
W5.1 ──→ W5.2 (←W0.2, W1.1)
W6.1 ──→ W6.2 → (W6.3 stretch)
W7: deferred
```

Recommended batches (each ends with `lake build` green, axiom check, golf
pass per `dev/mathlib-quality-adapter.md`, and a `papers/…-vs-literature.tex`
update including the permalink line):

1. **Batch A (warm-up, high leverage):** W1.1, W1.2, W2.1 — closes G5.
2. **Batch B (YWS exact):** W2.2, W2.3, W2.4 — Hoffman–Wielandt + YWS
   headline. Independently Mathlib-attractive (HW has repeatedly been
   requested upstream).
3. **Batch C (angles + alignment):** W0.1, W0.2, W3.1, W3.2, W3.3, W3.4 —
   closes G3, delivers the canonical-angle API.
4. **Batch D (singular vectors):** W4.1, W4.2, W4.3 — closes G4.
5. **Batch E (operator norm):** W5.1, W5.2 — closes the op-norm half of G1.
   **W5.1 is Fable's (in progress, v3 algebraic route); W5.2 is Opus's**, and
   with the reroute it no longer sits behind any integration machinery.
6. **Batch F (sharp rotations):** W6.1, W6.2 (+ W6.3 stretch) — closes G2's
   tractable core.
7. **Batch G (deferred):** W7 — full G1. Separate project decision.

## Difficulty ranking (all steps, hardest first)

*(v3: rows for W5.1/W5.2 rerated after the algebraic reroute; W2.4 rerated
per Opus R1. Historical ranks kept so the deltas are visible.)*

| Rank | Step | What | Difficulty | Why |
|------|------|------|-----------|-----|
| 1 | W6.3 | Subspace-level sin2Θ (stretch) | 5/5 | Needs W7 for op-norm form; Frobenius form still a heavy summation argument |
| 2 | W7.2 | Fan dominance theorem | 5/5 | Majorization theory from scratch (deferred) |
| 3 | W7.1 | Ky Fan norms + variational principle | 4/5 | New norm family + duality (deferred) |
| 4 | W7.4 | Part-III UI-norm sinΘ | 4/5 | Assembly over W7.1–3 (deferred) |
| 5 | W5.2 | Operator-norm sinΘ from Sylvester bound | **3.5/5 (was 4/5)** | Quadratic-form hypotheses kill the compression-spectrum lemma; remaining cost is subtype/restriction plumbing |
| — | W5.1 | Sylvester solution bound | **✅ DONE (was 5/5; rerouted v3, Fable)** | Landed in `SylvesterBound.lean`, axiom-clean, infinite-dim generality |
| 7 | W6.1 | Per-eigenvector sin2θ (Davis compression) | 4/5 | Delicate scalar geometry, degenerate cases, ℂ phase alignment |
| 8 | W3.4 | Aligned-basis theorem assembly | 4/5 | Long chain; conjugation bookkeeping; orthonormality of rotated family |
| 9 | W0.2 | Principal-angle definitions + bridges | 3.5/5 | Design-heavy (right def matters for three consumers); subspace coercions |
| 10 | W4.3 | YWS singular-subspace theorem | 3.5/5 | Mostly instantiation, but index/sorting bookkeeping across Gram dictionary |
| 11 | W2.2 | Trace inequality via Birkhoff | 3/5 | Machinery exists (schurWeight, Birkhoff); vertex-maximization plumbing |
| 12 | W2.3 | Hoffman–Wielandt | 3/5 | Frobenius expansion + basis-independence lemmas; W2.2 does the work |
| 13 | W2.4 | YWS exact theorem | **4/5 (was 3/5, per Opus R1)** | Residual is T-only + needs a new cross-term lemma; design content, not just assembly |
| 14 | W3.1 | Unitary polar decomposition (square case) | 3/5 | Direct-sum gluing of isometries; standard but fiddly |
| 15 | W3.3 | Trace/singular-value/angle chain | 3/5 | Three short lemmas over W0.1 |
| 16 | W0.1 | Singular-value glue (Frobenius², contraction, trace of abs) | 3/5 | Finsupp indexing friction; otherwise Parseval-level |
| 17 | W4.2 | Singular-value Weyl + dictionary | 3/5 | Sorting/indexing alignment, Weyl already local |
| 18 | W6.2 | tan2θ under vanishing pinch | 3/5 | Marginal cost over W6.1 |
| 19 | W3.2 | `|tr(UA)| ≤ tr A` for positive A | 2/5 | One Cauchy–Schwarz + existing `sq_norm_sqrt_apply` |
| 20 | W1.2 | Interval subspaces + two-sided Weyl bridge | 2/5 | Predicate plumbing over W1.1 |
| 21 | W4.1 | Gram perturbation bound | 2/5 | Triangle inequality + adjoint norm |
| 22 | W2.1 | Sorted rearrangement lemma | 2/5 | Mathlib rearrangement API plumbing |
| 23 | W1.1 | Engine over arbitrary Finset block | 2/5 | Mechanical generalization; projector section already does it |

## Opus review notes (2026-07-07)

**v3 disposition (Fable):** every note below is now folded into the plan body;
this section is kept as review history. Per-note status —
R1 → W2.4 rewritten with the corrected T-only residual + three statement-first
stubs (rerated 4/5). R2 → guarded-hypotheses convention added to the
statement-shape list. R3 → W0.2 redefined on the flat `overlapMap`
(compressions banned). R4 → `singularValues_adjoint` is now W0.1(d) with a
proof route. R5 → W3.4 rewritten around W3.1's kernel-completed unitary;
`tr(O†M)=tr|M|` recorded as an equality via `O†∘M = |M|`. R6 → **moot**: W5.1
rerouted to an integral-free algebraic argument (see W5.1 v3), so the Bochner
uncertainty and the descope path disappear; Fable is implementing W5.1
directly. R7 → division of labor set accordingly (W7, W6.3 stay deferred;
W5.2 now within Opus reach at 3.5/5). R8 → gate added to Definition of done.

Review by the executing (Opus) agent. I verified the load-bearing structural
claims against source: the ladder engine (`sum_cross_…` in `DavisKahan.lean`)
does extract the block only via `Finset.mem_filter.mp`, and the projector
section (`sum_norm_sub_starProjection_span_sq_eq` etc.) is already stated for
an arbitrary `s : Finset ι` — so **W1.1 is genuinely 2/5 as claimed**. Below
are the places that are underspecified, subtly wrong, or (for me) at the edge
of feasibility. Ordered by how much they'd cost if discovered mid-proof.

**R1 — W2.4 is the weakest-specified step; its residual is stated wrong.**
Fable's prose second-guesses which eigenvalues appear, and the version that
survives is not the one the current engine gives. The faithful YWS argument
(checked against `prose/Yu-Wang-Samworth-2014…` §"Lower/Upper bound"):
- *Residual:* `R` has columns `R v̂ⱼ = λⱼ(T-block)·v̂ⱼ − T v̂ⱼ`, `j` in the
  S-block. Here `λⱼ(T-block)` is a **T (population)** eigenvalue, *not* an
  `S`/sample one. This is **not** `(S−T)v̂ⱼ`, so the existing
  `…_le_residual` rung does **not** apply directly.
- *Lower bound (population gap, constant 1):* for `k` outside the T-block,
  `⟪uₖ, R v̂ⱼ⟫ = (λⱼ(T) − λₖ(T))·⟪uₖ, v̂ⱼ⟫`, and `|λⱼ(T) − λₖ(T)| ≥ Δ`.
  **Both multipliers are T-eigenvalues** ⇒ this needs a *new, simpler*
  cross-term identity `⟪uₖ, T v̂ⱼ⟫ = λₖ(T)·⟪uₖ, v̂ⱼ⟫` (just
  `hT.apply_eigenvectorBasis`), **not** `Spectrum.lean`'s mixed
  `inner_eigenvectorBasis_map_sub_eigenvectorBasis`. Then reuse the
  Parseval/`V₁ᵀV̂` counting to get `Δ‖sinΘ‖_F ≤ ‖R‖_F`. This is effectively a
  *second copy* of the engine specialized to `S = T` — plan for a small new
  lemma, do not expect to reuse the ladder verbatim.
- *Upper bound:* `R = E V̂ − V̂(Λ̂−Λ)` from `S v̂ⱼ = λ̂ⱼ v̂ⱼ` (this direction
  *is* the sample eigenvalues), giving `‖R‖_F ≤ ‖E‖_F + ‖Λ̂−Λ‖_F ≤ 2‖E‖_F`
  (HW, W2.3) and `≤ 2√d‖E‖_op` (Weyl, per-column).
- Fable's claim that the constant-2 population branch is *not* recoverable from
  the existing hybrid bound when `‖E‖_op > Δ/2` is **correct** — I checked:
  `gap_of_eigengap` yields hybrid gap `Δ − ‖E‖_op`, which degenerates exactly
  in that regime. So W2/W2.4 is genuinely necessary, not redundant.
- **Action for executor:** write the final `theorem` signature (population `Δ`,
  constant 2, both `min` branches) and the T-only cross-term lemma as `sorry`
  stubs *first*, confirm the constant on paper, then fill. Budget W2.4 at
  effectively 4/5, not 3/5, because of this design content.

**R2 — Boundary eigenvalue conventions (`λ₀=∞`, `λ_{p+1}=−∞`) are unspecified**
across W1.2, W2.4, W4.3. The cleanest faithful encoding I can commit to: state
the gap as **two hypotheses**
`hlow : r ≠ 0 → Δ ≤ λ_{r-1}(T) − λ_r(T)` and
`hhigh : s+1 ≠ n → Δ ≤ λ_s(T) − λ_{s+1}(T)` (vacuous at the spectrum edges),
and phrase the lower-bound counting over the *actual* complement `sᶜ` so no
fictitious `±∞` index is ever referenced. Add this as an explicit statement
convention to the header list. Without it, W2.4/W4.3 will churn on off-by-one
`Fin` boundary cases.

**R3 — W0.2's definition is self-contradictory as written.** It says define
`cosPrincipalAngles` via a subspace-compression map `↥U →ₗ ↥V` but "prove all
lemmas against the flat overlap-sum encoding." Those are different objects with
no stated bridge. Decision (unifying with W3.3, which already prefers the flat
matrix): **define `cosPrincipalAngles` as `LinearMap.singularValues` of the
flat overlap operator** `M : EuclideanSpace 𝕜 (Fin d') → EuclideanSpace 𝕜 (Fin d)`,
`M eⱼ = ∑ᵢ ⟪uᵢ, vⱼ⟫ • eᵢ`, and never introduce `↥U →ₗ ↥V`. All three
consumers (W3.3, W5.2, W6 angle-forms) want the flat matrix anyway. Rewrite
W0.2 to drop the compression-map phrasing.

**R4 — Missing dependency: `singularValues_adjoint` does not exist in Mathlib**
(I grepped — confirmed absent). W0.2(b) symmetry `cosPA U V = cosPA V U` rests
on `σ(M) = σ(M†)`, which must be built. It's a clean lemma
(`(M†M)` and `(MM†)` have equal nonzero spectra ⇒ equal singular values) and
independently Mathlib-attractive — **add it to W0.1 as an explicit sub-item**,
difficulty 3/5, and add a `comparator/candidate` entry. Do not assume it.

**R5 — W3.4 is subtly wrong about `O`, and the fix makes it depend hard on
W3.1.** Using `polarFactor M` (a *partial* isometry) fails when `M` is singular
(some `cosθ = 0`, i.e. a right angle): `w` is then not orthonormal and
`tr(O†M) = tr|M|` breaks. The correct `O` is the **kernel-completed unitary**
from W3.1, for which `O†M = |M|` holds with `O` unitary regardless of `M`'s
rank. So (i) W3.1 must produce a genuine `E ≃ₗᵢ E`, not just a partial
isometry (its current spec does — keep it); (ii) apply W3.1 at the flat
`d`-dimensional level to `M` (or `M†` — fix the side once and stay consistent);
(iii) `tr(O†M) = ∑σᵢ` becomes an *equality*, no SVD needed, sidestepping
Mathlib's missing matrix SVD. This is the crux that lets W3 avoid SVD at all —
call it out so no one reaches for `polarFactor` directly.

**R6 — W5.1 is at the edge of what I can land cleanly; timebox it.** I concur
with 5/5. Two specific under-specifications that will bite:
- The "commute inner product past the Bochner integral" step needs an
  operator-valued integral into `E₂ →L[𝕜] E₁` and a lemma of the shape
  `⟪u, (∫ f) v⟫ = ∫ ⟪u, f·v⟫`. Mathlib has `ContinuousLinearMap.integral_comp_comm`
  / `integral_clm` style lemmas but I am **not certain the exact form needed
  exists**; verify before committing, else the fallback (entrywise
  Schur-multiplier + Minkowski integral inequality, scalar integrals only) is
  safer and I'd start there.
- The spectrally-defined `expScaled(t)` needs measurability in `t` and
  integrability from the exponential bound; each is a small but real lemma.
- **Recommendation:** attempt W5.1 on a timebox. If the operator-integral
  infrastructure resists, deliver only the Frobenius operator-norm corollary
  the repo actually consumes and **defer the dimension-free op-norm sinΘ**,
  documenting the descope. Nothing downstream in the DKPS pipeline needs W5.2.

**R7 — Too difficult for me to commit to (flagging per instructions):**
- **W5.1 / W5.2 (op-norm sinΘ):** feasible but genuinely research-grade; treat
  as "attempt with descope option," not "will land." See R6.
- **W7 (unitarily invariant norms) in full:** agree with Fable — this is a
  standalone Mathlib-sized library (symmetric gauge functions + Fan dominance +
  von Neumann trace inequality). I would **not** take it on inside this effort;
  it deserves its own project. W7.1/W7.2 especially.
- **W6.3 (subspace-level op-norm sin2Θ):** defer; its op-norm form is downstream
  of W7. The Frobenius-summed W6.1/W6.2 are fine.
Everything else (W0, W1, W2.1–2.3, W3.1–3.3, W4) I assess as within reach at
Fable's stated difficulties, with W2.4 rerated up to 4/5 per R1.

**R8 — Process gap: no "statement-first" gate.** For every step whose *content*
is a derivation rather than a generalization (W2.4, W3.4, W4.3, W5.1, W6.1),
the plan should require writing the final `theorem … := sorry` with the exact
literature constant and a one-paragraph paper cross-check *before* proving, so a
wrong constant is caught in minutes not hours. Add this to Definition of done.

## Definition of done (per batch and overall)

- **Statement-first gate (per R8):** for every derivation-content step (W2.4,
  W3.4, W4.3, W5.1, W6.1) write the final `theorem … := sorry` with the exact
  literature constant and a one-paragraph paper cross-check *before* proving.
- `lake build` green (all ~8.6k jobs), zero `sorry`, `#print axioms` on each
  headline = `propext, Classical.choice, Quot.sound`.
- Every new file: staging provenance header, docstrings on public decls,
  registered in `ForMathlib.lean`.
- Golf pass per `dev/mathlib-quality-adapter.md` (`mathlib-quality:cleanup`
  with the provenance carve-out; decompose any proof > ~60 lines, > ~15 for
  headlines); statements never drift during golf.
- `papers/DavisKahan-formalized-vs-literature.tex`: move each closed item out
  of §"What is not formalized", extend the dictionary table, update the
  companion permalink, add the authoring model to the author list per the
  file's NOTE.
- Consider a `comparator/candidate-*.json` entry for independently
  Mathlib-attractive pieces (Hoffman–Wielandt W2.3, unitary polar W3.1,
  principal angles W0.2, Sylvester bound W5.1).
