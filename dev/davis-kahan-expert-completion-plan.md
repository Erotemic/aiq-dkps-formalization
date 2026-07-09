# Davis–Kahan expert-completion plan

Roadmap for taking the Davis–Kahan formalization from its current state —
`dev/davis-kahan-gap-closure-plan.md` (v6) fully executed, everything the DKPS
pipeline consumes formalized — to a state that would satisfy an expert asked
"is the Davis–Kahan *theory* formalized?", i.e. the Part III (1970) package:
the four theorems (sinΘ, sin2Θ, tanΘ, tan2Θ) at the subspace level, in every
unitarily invariant norm, with the principal-angle dictionary certified.

Written for an Opus-level agent; every step names its target file, statement
shape, proof route, existing assets, pitfalls, and a difficulty grade.  House
rules: `dev/mathlib-quality-adapter.md` (provenance headers, docstrings, golf
gates, `lake build` green after every step, `#print axioms` =
`propext, Classical.choice, Quot.sound` on headlines, paper sync per step,
`comparator/candidate-*.json` for Mathlib-attractive pieces).

## Revision log

- **v1 (2026-07-09, Fable):** initial plan, incorporating a review of Opus's
  2026-07-09 expert-gap diagnosis.
- **v3 (2026-07-09, Fable — F0–F2 executed; F3 rerouted, HLP eliminated):**
  **F0–F2 ✅ DONE** (`KyFan.lean`, commit `199390a`, all headlines
  axiom-clean): the full F0 singular-value API (gram-determined, unitary
  invariance both sides, real scaling, bounded-factor domination via new
  CourantFischer Loewner monotonicity + sorted-eigenvalue uniqueness
  `eigenvalues_eq_of_eigenbasis`), the knapsack lemma, the Ky Fan trace
  inequality, the variational principle (both directions), `kyFanSum`, and
  weak majorization `kyFanSum_add_le`.  **F3 reroute (major, verified on
  paper):** Fan dominance does *not* need F3.d (weak-majorization completion)
  or F3.e (Hardy–Littlewood–Pólya) — run the T-transform descent *directly on
  the gauge*: induct on the disagreement count of (sorted nonneg `z`,
  arbitrary nonneg `y`) under prefix-sum domination only (no total-equality);
  at each step the transformed `y' = c₁•y + c₂•(y∘swap j l)` costs one
  two-term triangle inequality + one swap-permutation invariance
  (`N(D_{y∘π}) = N(D_y)` via `OrthonormalBasis.equiv` conjugation), and the
  case "no index with `z_l > y_l`" gives `z ≤ y` pointwise, closed by
  coordinatewise gauge monotonicity (single-coordinate reflection step via
  `Submodule.reflection ((𝕜 ∙ b j)ᗮ)` + `Finset.induction` merge).  The key
  step inequalities: `j :=` least disagreement has `z_j < y_j` (prefix at
  `j+1`); `l :=` least index with `y_l < z_l`; `δ := min (y_j − z_j)
  (z_l − y_l)`; `y_j > y_l` from `z` sorted; prefix domination for `y'` needs
  `P_m(z) ≤ P_m(y) − δ` only for `j < m ≤ l`, which follows termwise.  So
  F3 = (a) `diagOp` + operator SVD, (b) the `UnitarilyInvariantNorm`
  structure + gauge representation `N A = N (diagOp b (σ A))`, (c)
  coordinatewise monotonicity, (e''') the descent above, (f) Fan dominance +
  `N(A⋆) = N(A)` + the ideal property (via (c) + `singularValues_comp_le`,
  no Fan dominance even needed for it).  F3.d/F3.e are **removed from the
  critical path**; HLP in weights form stays only as an optional
  Mathlib-attractive extra.  F4.b note: state the abstract Sylvester bound at
  the *LinearMap* level (elementwise bounds, finite dim) since
  `UnitarilyInvariantNorm` lives on `E →ₗ[𝕜] E`; F4.c ports the W5.2
  full-space construction to LinearMaps (mechanical; the CLM lemma
  `norm_le_of_abs_re_inner_map_self_le` bridges via `toContinuousLinearMap`).
- **v2 (2026-07-09, Fable — Phase E executed):** E1–E5 all ✅ DONE, library
  build green, all 12 new headlines axiom-clean.  Deviations from the v1
  routes, folded into the steps: (i) E2's coordinate pull-back uses the
  *adjoint of the coordinate isometry* (`Submodule.mem_span_range_iff_exists_fun`
  is hidden by the pinned Mathlib's module system) — cleaner anyway; (ii) all
  E3 spectral corollaries live in `SinThetaOpNorm.lean` (single import site);
  new public lemmas `map_mem_specSubspace` and `orthogonal_specSubspace` in
  `CourantFischer.lean`; (iii) **E4(e) re-scoped:** the `sqSinAngle` bridge is
  *dropped from E4* — `sqSinAngle` measures the direct-rotation angles of the
  intertwining unitary, whose identification with principal angles is
  G1-adjacent material; it is folded into G1's scope.  E4 delivers (c)
  (`sinThetaSq_blockFamily_eq_sum_cross`) and (d)
  (`sum_norm_sub_starProjection_sq_eq_two_mul_sinThetaSq`) plus the
  `blockFamily` API.

## Review of the Opus diagnosis (2026-07-09)

The diagnosis (three tiers: quartet + UI norms / dictionary + general
separation / breadth) is **structurally correct** and adopted below, with
these corrections and refinements, each folded into the step it concerns:

- **R-A (state):** "the operator-norm sinΘ just landed" was written while
  W5.2 was still in flight; it has since landed (`SinThetaOpNorm.lean`,
  commit `a855fd3`) via a *full-space scalar-extension* route (no subtype
  compressions) — the plan below reuses that construction verbatim for the
  UI-norm part-III headline (F4.c), which materially lowers its cost.
- **R-B (general separation is mostly done):** "fully general spectral
  separation" is *already covered in Frobenius form*: the W1.1 block engine
  takes arbitrary index sets `s, t` with the pointwise hypothesis
  `∀ i ∈ s, ∀ j ∉ t, g ≤ |λᵢ(T) − λⱼ(S)|`, which **is** general two-set
  separation for symmetric operators in finite dimension.  What is genuinely
  missing is only (i) the *operator-norm* sinΘ under general (interleaved,
  two-sided) separation — a genuinely different theorem carrying the optimal
  constant `π/2` (Bhatia–Davis–McIntosh), Fourier-analytic, deferred (Phase H)
  — and (ii) cosmetic `sep`-vocabulary wrappers (E5, trivial).
- **R-C (missing small items the diagnosis skipped):** the *spectral
  instantiations* of the new abstract theorems are not written: W5.2 and
  W6.1/W6.2 take abstract invariant subspaces + quadratic-form bounds; the
  literature-facing corollaries with eigenvalue hypotheses
  (`U = span of leading T-eigenvectors`, etc.) are a concrete gap (E3).
- **R-D (infinite dimension is closer than stated):** `SylvesterBound.lean`
  (no completeness, no finite dimension) and the per-vector sin2θ/tan2θ
  (`RotationSharp.lean`, orthogonal-projection-only) are *already*
  infinite-dimension-ready.  The genuinely finite-dimensional layer is the
  eigenbasis encoding.  A spectral-measure treatment remains out of scope
  (Phase H), but the frontier should be documented, not overstated.

## Current asset inventory (verified 2026-07-09, all sorry-free, axiom-clean)

Everything in `dev/davis-kahan-gap-closure-plan.md` §"Existing assets" plus,
since v4 of that plan:

- **RotationSharp.lean** — per-vector sin2θ (`sin_two_theta_le_of_mem`,
  `sin_two_theta_le`, `sin_two_arccos_le`; phase-free, projection-only) and
  tan2θ under vanishing pinch (`tan_two_theta_le_of_mem`, `tan_two_theta_le`);
  invariance helper `map_mem_orthogonal_of_forall_map_mem`; the μ-free
  `key_identity`.
- **SinThetaOpNorm.lean** — dimension-free op-norm sinΘ
  (`norm_starProjection_comp_starProjection_le`) via the full-space
  scalar-extension Sylvester argument; commutation helper
  `starProjection_comp_toContinuousLinearMap_comm`.
- **SingularSubspace.lean** additions — `singularValues_adjoint` (square),
  `eigenvalues_conj_unitary` (unitary conjugation preserves sorted
  eigenvalues), `eigenvalues_congr`, `comp_adjoint_eq_conj_adjoint_comp`.
- **PrincipalAngles.lean** — `cosPrincipalAngles` (= σ(overlapOp)),
  `sinThetaSq`, range/order/symmetry (`cosPrincipalAngles_comm`), bridge
  `sinThetaSq_eq_sub_overlap`, `sum_sq_norm_aligned_le_sinThetaSq`.
- **HoffmanWielandt.lean** — rearrangement, Birkhoff bilinear bound, von
  Neumann trace inequality for a *symmetric* pair
  (`sum_eigenvalues_mul_re_inner_self_le`), Hoffman–Wielandt.

Mathlib (pinned) **has**: `LinearMap.singularValues` + `sq_singularValues_fin`
etc.; Birkhoff (`doublyStochastic_eq_convexHull_permMatrix`); rearrangement
inequality; `LinearMap.IsSymmetric.eigenvalues/eigenvectorBasis`;
`Submodule.starProjection` API; CFC.

Mathlib **lacks** (verified by grep, do not search upstream): any majorization
theory (no Hardy–Littlewood–Pólya, no weak-majorization API), Ky Fan norms,
symmetric gauge functions, unitarily invariant norms, Loewner-order
monotonicity of sorted eigenvalues, operator SVD factorization, matrix/operator
`σ(A⋆) = σ(A)` (ForMathlib supplies the square case).

## Statement-shape conventions (inherit v5 conventions, plus)

- UI-norm phase: operators are square, `A : E →ₗ[𝕜] E`, `[FiniteDimensional 𝕜 E]`.
- Vectors of singular values enter lemmas as `Fin n → ℝ` obtained by
  `fun i => A.singularValues (i : ℕ)` with `hn : finrank 𝕜 E = n`; never as
  the raw finsupp except in definitional glue.
- A "unitarily invariant norm" is the structure of F3.b below; do **not**
  axiomatize symmetric gauge functions separately — derive the gauge from the
  norm (`Φ(x) := N(diagOp b x)`), which avoids a second primitive.
- **Statement-first gate** applies to every Phase G item and to F3.e: write
  the headline `theorem … := sorry` with the exact literature constant and a
  one-paragraph cross-check against DK III / Stewart–Sun / Bhatia *before*
  proving; commit the stub separately.

---

## Phase E — certify the dictionary and finish the spectral corollaries

Small, concrete, high value: after Phase E every bound already proved is
*certified* to be a statement about principal angles, in both norms, and every
theorem has its literature-facing eigenvalue-hypothesis form.  All items are
Opus-safe.

**E1 — Variational characterization of extreme singular values.
Difficulty 2/5.**  In `SingularSubspace.lean`.  For `A : E →ₗ[𝕜] F`,
`hn : finrank 𝕜 E = n`, `0 < n`:
(a) `∀ x, A.singularValues (n-1) * ‖x‖ ≤ ‖A x‖` and
(b) `∃ x, ‖x‖ = 1 ∧ ‖A x‖ = A.singularValues (n-1)`;
(c) `∀ x, ‖A x‖ ≤ A.singularValues 0 * ‖x‖` and
(d) `∃ x, ‖x‖ = 1 ∧ ‖A x‖ = A.singularValues 0`.
Route: `‖A x‖² = re ⟪(A⋆A) x, x⟫`; diagonalize with
`re_inner_map_self_eq_sum_eigenvalues_mul_sq` (CourantFischer.lean, public);
bound each eigenvalue by the first/last using `eigenvalues_antitone`; Parseval
(`sum_sq_norm_repr_eq_sq_norm` is private — reprove inline via
`OrthonormalBasis.sum_sq_norm_inner_right`, one line).  Witnesses: the first/
last eigenvector, with `sq_singularValues_fin` and `Real.sqrt_sq`.
Pitfall: `n − 1 : ℕ` vs `Fin n` — state with `(Fin.last _)`-style indices
`(⟨n-1, by omega⟩ : Fin n)` fixed once in a local abbreviation.

**E2 — Operator-norm principal-angle identification. Difficulty 3.5/5.**
In `PrincipalAngles.lean`.  For orthonormal families `u w : Fin d → E`
(`0 < d`), with `W := span 𝕜 (Set.range w)`:

> `‖Wᗮ.starProjection ∘L (span 𝕜 (Set.range u)).starProjection‖`
> `= Real.sqrt (1 - cosPrincipalAngles hw hu (d-1) ^ 2)`

i.e. `‖Q̂ ∘L P‖ = sin θ_max`.  This certifies that the W5.2 headline bounds
the largest principal-angle sine.  Route (two inequalities, `le_antisymm`):
- *Key identity:* for `y : EuclideanSpace 𝕜 (Fin d)` and `x := familyIsometry
  hu y ∈ U`: `‖W.starProjection x‖ = ‖overlapOp hw hu y‖` — Parseval on the
  `w`-family (`Orthonormal.norm_sq_starProjection_span_image`, DavisKahan.lean;
  mind `w '' ↑(Finset.univ)` vs `Set.range w` — add a `simp` bridge lemma
  `Set.image_univ`) plus `overlapOp_apply` coordinates
  (`(overlapOp hw hu y) i = ⟪w i, x⟫`, from `adjoint_inner_right`).
- *Pythagoras:* `‖Wᗮ.starProjection x‖² = ‖x‖² − ‖W.starProjection x‖²` (the
  two projections of `x` are orthogonal; `norm_add_sq` pattern as in
  RotationSharp.lean; also `Wᗮ.starProjection x = x − W.starProjection x` —
  `Submodule.starProjection_orthogonal_val` vicinity, check exact name).
- *≤:* for any `z`, `P z ∈ U` with `‖P z‖ ≤ ‖z‖`; write `P z = ι(y)`,
  apply E1(a) to `overlapOp hw hu`: `‖overlap y‖ ≥ σ_min ‖y‖`, so
  `‖Q̂ P z‖² = ‖y‖² − ‖overlap y‖² ≤ (1 − σ_min²)‖y‖² ≤ (1 − σ_min²)‖z‖²`.
- *≥:* the E1(b) witness `y₀` of `σ_min`, pushed to `x₀ := ι y₀`.
Then the corollary chaining with `norm_starProjection_comp_starProjection_le`:
in the W5.2 setting with `V = Wᗮ` (`d`-codimensional trailing span),
`sin θ_max ≤ ε / g`.  Pitfall: the sides of `cosPrincipalAngles` — the W5.2
`Q̂` projects onto `V`; the angle pair is `(w-family of Vᗮ, u-family of U)`;
use `cosPrincipalAngles_comm` to normalize.

**E3 — Spectral (eigenvalue-hypothesis) corollaries. Difficulty 2.5/5.**
New section in `SinThetaOpNorm.lean` and `RotationSharp.lean`.
(a) *Un-`private`* in `CourantFischer.lean`: `specSubspace`,
`finrank_specSubspace`, `re_inner_map_self_le_of_mem_specSubspace`,
`le_re_inner_map_self_of_mem_specSubspace` (update the header note: they now
have external consumers, the un-privatizing criterion it records).
(b) *Invariance lemma:* `T u ∈ specSubspace (hT.eigenvectorBasis hn) p` for
`u` in it — `Submodule.span_induction` + `apply_eigenvectorBasis`.
(c) *Complement lemma* (independently useful):
`(specSubspace b p)ᗮ = specSubspace b (¬ p ·)` — `⊇` from orthonormality,
equality by `finrank` count (`finrank_specSubspace` + orthogonal-complement
dimension).
(d) W5.2 spectral form: `s s' : Finset (Fin n)`,
`hs : ∀ i ∈ s, c + g ≤ hT.eigenvalues hn i`,
`hs' : ∀ j ∉ s', hS.eigenvalues hn j ≤ c` ⇒ op-norm bound between
`U := specSubspace (hT.eigenvectorBasis hn) (· ∈ s)` and the analogous
trailing `S`-span; quadratic forms discharged by (a), invariance by (b).
(e) sin2θ/tan2θ spectral forms: `U` = span of eigenvectors with
`b ≤ λᵢ(T)`; `ha` on `Uᗮ` via (c) then (a).
Deliverable: every abstract theorem has its sorted-eigenvalue corollary.

**E4 — Frobenius-encoding coherence bridges (deferred W0.2 (c)/(d)/(e)).
Difficulty 2.5/5.**  In `PrincipalAngles.lean`.  For eigenbasis *blocks*
(`u = hT.eigenvectorBasis hn` restricted to `s`, `v̂ = hS.eigenvectorBasis hn`
restricted to `s'`, `|s| = |s'| = d`, families via `Finset.orderIsoOfFin` or a
subtype enumeration — fix the indexing idiom once):
(c) `sinThetaSq hu hv = ∑_{j∈s'} ∑_{i∉s} ‖⟪uᵢ, v̂ⱼ⟫‖²` — from
`sinThetaSq_eq_sub_overlap` + full Parseval `∑_{all i}‖⟪uᵢ, v̂ⱼ⟫‖² = 1`;
(d) `∑ₖ ‖(P̂ − P) bₖ‖² = 2 · sinThetaSq hu hv` — compose (c) with
`sum_norm_sub_starProjection_span_sq_eq`;
(e) the `sqSinAngle` bridge in the nondegenerate rank-one case (compose with
`sum_sqSinAngle`, IntertwiningUnitary.lean).
Then restate the sharp DK rung as
`sinThetaSq hu hv ≤ (∑ⱼ ‖(S−T) v̂ⱼ‖²) / g²` — a thin wrapper over
`sum_cross_norm_inner_eigenvectorBasis_sq_le_hilbertSchmidt_block`.
Deliverable: all four sinΘ encodings in the repo (overlap sum, `sinThetaSq`,
projector distance, `sqSinAngle`) proved pairwise equal.

**E5 — `sep` vocabulary + general-separation documentation. Difficulty 1/5.**
Module-doc + thin wrappers only: restate the block-engine hypothesis as
`Set.Icc`-avoidance / `sep`-style phrasing where it reads better, and record
in `DavisKahan.lean`'s module doc that (i) the arbitrary-Finset block form
*is* general two-set separation in finite dimension (R-B), and (ii) the
op-norm analogue for interleaved spectra requires the `π/2` constant and is
deliberately out of scope (Phase H pointer).  Fold into the E3/E4 commit.

---

## Phase F — the unitarily-invariant-norm library (old W7, un-deferred)

The load-bearing phase: after F4 the part-III sinΘ theorem holds *for every
unitarily invariant norm*, with Frobenius and operator norm as instances.
Bricks ordered so each is independently landable and Mathlib-attractive.
New files under `ForMathlib/Analysis/InnerProductSpace/`:
`KyFan.lean` (F0–F2), `UnitarilyInvariantNorm.lean` (F3), extension of
`SylvesterBound.lean` + new `SinThetaUINorm.lean` (F4).

**F0 — Singular-value API strengthening. Difficulty 2.5/5.**  In
`SingularSubspace.lean` (or the new `KyFan.lean`):
(a) `singularValues_unitary_comp` : `σ(U ∘ A) = σ(A)` for `U : E ≃ₗᵢ[𝕜] E` —
`(U∘A)⋆(U∘A) = A⋆A` (`adjoint_toLinearMap_eq_symm`), then `eigenvalues_congr`;
(b) `singularValues_comp_unitary` : `σ(A ∘ U) = σ(A)` —
`(AU)⋆(AU) = U⁻¹(A⋆A)U`, then `eigenvalues_conj_unitary` (exists);
(c) `singularValues_smul` : `σ(a • A) = |a| • σ(A)` (via
`(a•A)⋆(a•A) = |a|²•A⋆A` and `√`);
(d) **Loewner monotonicity of sorted eigenvalues** (new, independently
Mathlib-attractive): if `M, N` symmetric and
`∀ x, re ⟪M x, x⟫ ≤ re ⟪N x, x⟫` then
`hM.eigenvalues hn k ≤ hN.eigenvalues hn k` — Courant–Fischer sandwich:
witness subspace for `M` (`forall_unit_vector_eigenvalue_le_re_inner`), test
vector for `N` (`exists_unit_vector_re_inner_le_eigenvalue`), exactly the
`eigenvalues_sub_le` proof pattern with the ε-term replaced by the form
inequality;
(e) corollary `singularValues_comp_le` / `_le_comp` :
`σᵢ(C ∘ A) ≤ c·σᵢ(A)` when `∀x, ‖Cx‖ ≤ c‖x‖` (and the mirrored
`σᵢ(A ∘ C) ≤ σᵢ(A)·c` via `singularValues_adjoint`) — from (d) applied to
`A⋆C⋆CA ≤ c²·A⋆A` (quadratic forms: `re⟪C⋆C(Ax), Ax⟫ = ‖C(Ax)‖²`), plus
`Real.sqrt` monotonicity.

**F1 — Ky Fan trace inequality and variational principle.**
(a) *Knapsack lemma. Difficulty 2/5.*  Pure real arithmetic, place first in
`KyFan.lean`: for `λ : Fin n → ℝ` antitone, `c : Fin n → ℝ`,
`h0 : ∀ j, 0 ≤ c j`, `h1 : ∀ j, c j ≤ 1`, `hk : ∑ j, c j ≤ k` (`k ≤ n`):
`∑ j, λ j * c j ≤ ∑ j ∈ Finset.range k …, λ j` (top-`k` sum; use a `Fin n`
filter `j < k`).  Proof: subtract, group by `j < k` vs `k ≤ j`, compare every
coefficient against `λ ⟨k-1⟩`-vs-`λ ⟨k⟩` — hmm, cleanest: prove
`∑ j, λ j * c j − ∑_{j<k} λ j = ∑_{j<k} (c j − 1)·λ j + ∑_{j≥k} c j·λ j
≤ λₖ·(∑ c − k) ≤ 0` termwise with `Finset.sum_le_sum`; guard `k = 0` and
`k = n` separately (empty/full top block).
(b) *Ky Fan trace inequality. Difficulty 3/5.*  For `T` symmetric,
`w : Fin k → E` orthonormal:
`∑ i, re ⟪T (w i), w i⟫ ≤ ∑ i ∈ (univ.filter (·.val < k)), hT.eigenvalues hn i`.
Route: diagonalize each term
(`re_inner_map_self_eq_sum_eigenvalues_mul_sq`), swap sums; column weights
`c j := ∑ i, ‖(b.repr (w i)) j‖²` satisfy `c j ≤ 1` (Bessel for the
orthonormal family `w` against the unit vector `b j` — Mathlib
`Orthonormal.sum_inner_mul_inner`-vicinity or `inner_products` Bessel; if the
exact Bessel form is missing, prove via
`Orthonormal.norm_sq_starProjection_span_image ≤ ‖bⱼ‖²`) and `∑ j c j = k`
(Parseval per `w i`); finish with (a).  Independently Mathlib-attractive
(implies the Schur–Horn partial-sum inequalities) — file a comparator
candidate.
(c) *Ky Fan variational principle. Difficulty 3.5/5.*
`∑_{i<k} σᵢ(A) = sup` — state as the two inequalities, never `iSup`:
  - *(achievability)* with `xᵢ := (A⋆A)-eigenvectorBasis i` and
    `uᵢ := polarUnitary A (xᵢ)`:
    `∑_{i<k} re ⟪u i, A (x i)⟫ = ∑_{i<k} σᵢ(A)` — from
    `polarUnitary_apply_abs_apply` + `inner_map_map` +
    `sqrt_apply_eigenvectorBasis` (the `sum_re_inner_abs_self_eq_…` proof
    pattern, SingularSubspace.lean);
  - *(bound)* for any orthonormal `u v : Fin k → E`:
    `re (∑ i, ⟪u i, A (v i)⟫) ≤ ∑_{i<k} σᵢ(A)`.  Route: `A = W ∘ |A|`
    (`polar_decomposition_unitary`), write `|A| = |A|^{1/2} ∘ |A|^{1/2}`
    (the positive square root of the positive `|A|` — `PositiveSqrt.lean`
    applies since `abs A` is positive; add glue lemma
    `(isPositive_abs A).sqrt_mul_self`… already exists as `sqrt_mul_self`),
    then AM–GM each term:
    `re ⟪uᵢ, W|A|vᵢ⟫ = re ⟪|A|^{1/2}(W⋆uᵢ), |A|^{1/2}vᵢ⟫
     ≤ ½‖|A|^{1/2}W⋆uᵢ‖² + ½‖|A|^{1/2}vᵢ‖²
     = ½ re⟪|A|(W⋆uᵢ), W⋆uᵢ⟫ + ½ re⟪|A|vᵢ, vᵢ⟫`,
    and both sums are `≤ ∑_{i<k} λᵢ(|A|) = ∑_{i<k} σᵢ(A)` by (b) — note
    `W⋆ ∘ u` is again orthonormal (unitary image).  Dictionary
    `λᵢ(|A|) = σᵢ(A)`: `|A|` is positive with `|A|² = A⋆A`, so
    `λᵢ(|A|)² = λᵢ(A⋆A)` — prove via `eigenvalues_congr`-style uniqueness on
    the shared eigenbasis (`sqrt_apply_eigenvectorBasis` gives the eigenbasis
    of `A⋆A` as an eigenbasis of `|A|` with eigenvalues `√λᵢ`, and sorted
    lists agree; this glue lemma `eigenvalues_abs` is its own small item —
    reuse the "same eigenbasis, same sorted values" argument from
    `sum_re_inner_abs_self_eq_sum_singularValues`).
    Pitfall: state everything with `re` outside the sum moved in
    (`map_sum`), and keep `k ≤ n` explicit; the `i < k` block as
    `Finset.univ.filter` per house convention.

**F2 — Ky Fan norms and the weak-majorization triangle inequality.
Difficulty 2/5 (given F1).**  In `KyFan.lean`:
- `def kyFanSum (k : ℕ) (A : E →ₗ[𝕜] E) : ℝ := ∑ i ∈ Finset.range k,
  A.singularValues i` (ℕ-indexed partial sum of the finsupp — no `Fin`
  gymnastics; `singularValues_of_finrank_le` makes over-length sums stable);
- **`kyFanSum_add_le`** (= weak majorization `σ(A+B) ≺_w σ(A)+σ(B)`, = the
  simultaneous triangle inequality for all Ky Fan norms):
  `kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B` — three lines from
  F1(c): achieve `kyFanSum k (A+B)` with a pair `(u, x)`, split
  `⟪uᵢ, (A+B)xᵢ⟫`, bound each half by its own variational bound.
  Independently Mathlib-attractive — comparator candidate;
- `kyFanSum_unitary_comp` / `_comp_unitary` / `_smul` from F0;
- monotone in `k`, and `kyFanSum n A = ∑ all σ` (trace norm),
  `kyFanSum 1 A = σ₀ = ‖A‖` (E1(c,d)).

**F3 — Unitarily invariant norms and Fan dominance.**
In new `UnitarilyInvariantNorm.lean`.
(a) *Operator SVD factorization. Difficulty 3.5/5.*  Fix
`b : OrthonormalBasis (Fin n) 𝕜 E`.  Define
`diagOp b (x : Fin n → ℝ) : E →ₗ[𝕜] E := ∑ i, (x i : 𝕜) • (⟪b i, ·⟫ • b i)`
(rank-one sums — the `spectralProjection` idiom of IntertwiningUnitary.lean).
Prove: **`∃ (Uu Vv : E ≃ₗᵢ[𝕜] E), A = Uu ∘ₗ diagOp b (σ(A)) ∘ₗ Vv`** —
route: `A = polarUnitary A ∘ₗ |A|` (exists); let `w :=` eigenbasis of `A⋆A`
(= eigenbasis of `|A|`, `sqrt_apply_eigenvectorBasis`); let
`K : E ≃ₗᵢ[𝕜] E` be the basis-exchange unitary `b i ↦ w i`
(`OrthonormalBasis.equiv`-vicinity — check name; else build via two
`repr` isometries composed); then `|A| = K ∘ diagOp b (λ(|A|)) ∘ K⁻¹`
(check on the basis `w`), and `λᵢ(|A|) = σᵢ(A)` (F1's `eigenvalues_abs`).
Also record `singularValues_diagOp` : `σ(diagOp b x) = sorted |x|`
(needed for (b); for *sorted nonneg* `x` it is `x` itself — restrict the
statement to antitone nonneg `x`, which is all (b) consumes).
(b) *The structure and the gauge. Difficulty 2.5/5.*
```
structure UnitarilyInvariantNorm (𝕜 E) [...] where
  toFun : (E →ₗ[𝕜] E) → ℝ
  nonneg, triangle (toFun (A+B) ≤ toFun A + toFun B),
  smul (toFun (a • A) = ‖a‖ * toFun A),
  invariant : ∀ (Uu Vv : E ≃ₗᵢ[𝕜] E) A, toFun (Uu ∘ₗ A ∘ₗ Vv) = toFun A
```
(seminorm axioms suffice for DK — positivity is never used; note this in the
docstring).  Define the gauge `Φ N x := N (diagOp b x)` and prove
**`N A = Φ N (σ(A))`** from (a) — basis-independence of `Φ` on sorted
nonneg vectors comes free (any two `diagOp`s of the same sorted vector are
unitarily equivalent via basis exchange).
(c) *Coordinatewise monotonicity of the gauge. Difficulty 3/5.*  For sorted
nonneg `x ≤ y` (coordinatewise): `Φ N x ≤ Φ N y`.  Route: one coordinate at
a time; `diagOp b (update y j t)` for `t ∈ [-yⱼ, yⱼ]` is a convex combination
of the two sign choices `t = ±yⱼ`, and the sign flip is conjugation by the
unitary `diagOp`-style reflection `b j ↦ −b j` (build once:
`reflectionUnitary b j : E ≃ₗᵢ[𝕜] E`); triangle + invariance give
`Φ(…t…) ≤ Φ(…yⱼ…)`.  Induct over coordinates (`Finset.sum_induction`-style
or `Fin n` recursion — pitfall: keep the intermediate vectors explicit,
`Function.update` chains, and do the induction as a `Finset.prod`-free
manual `Fin.induction` over positions).
(d) *Weak-majorization completion. Difficulty 2.5/5.*  Pure `Fin n → ℝ`
combinatorics: if `x ≺_w y` (partial-sum domination of the sorted nonneg
vectors) then `∃ z, (∀ i, x i ≤ z i) ∧ z ≺ y` (equal total sums) — add the
deficit `(∑y − ∑x)` to the last coordinate of `x` and re-sort… the classical
statement adds it so as to preserve domination; cleanest inductive route:
Bhatia II.3 (i): `x ≺_w y ⇒ x ≤ some z ≺ y` by increasing coordinates of `x`
greedily.  Timebox; if the greedy bookkeeping fights, an acceptable descope
is to prove Fan dominance only for *monotone* gauges directly from (c) +
(e)-for-`≺_w` via the substochastic Birkhoff padding trick — but try (d)
first, it is genuinely simpler.
(e) *Hardy–Littlewood–Pólya. Difficulty 4/5 — the crux brick; statement-first
gate.*  For sorted `z ≺ y` (equal sums, partial-sum domination):
`z ∈ convexHull ℝ {y ∘ π : π ∈ Equiv.Perm (Fin n)}`.  **Verified absent from
Mathlib** (no majorization theory upstream as of the pin).  Route (classical
T-transform induction, Bhatia II.1.10 / Marshall–Olkin 2.B.1): induct on the
number of indices where `z ≠ y`; find `i < j` with `yᵢ > zᵢ` and `yⱼ < zⱼ`
(exists by the majorization balance), apply the T-transform
`y' := y + t(eⱼ − eᵢ)(yᵢ − yⱼ)`-style two-point averaging with `t` chosen to
create one new agreement; `y'` is a convex combination of `y` and its
`(i j)`-transposition, and `z ≺ y'` still holds; recurse.  Pitfalls: work
with *sorted* vectors throughout and only introduce permutations at the very
end; make the induction measure explicit
(`(Finset.univ.filter (z · ≠ y ·)).card`); `convexHull` membership via
`segment` lemmas (`convexHull` of a finite set — use
`mem_convexHull_iff_exists_fintype`-vicinity or build as repeated
`convex_convexHull.segment_subset`).  Independently Mathlib-attractive at the
level of Birkhoff itself — definitely a comparator candidate.  This brick is
at the Opus/Fable boundary: attempt with the route above; if the T-transform
bookkeeping resists after a timebox, hand to Fable.
(f) *Fan dominance. Difficulty 2/5 given (b)–(e).*
`(∀ k, kyFanSum k A ≤ kyFanSum k B) → N A ≤ N B` for every
`N : UnitarilyInvariantNorm`:  σ(A) ≺_w σ(B) by hypothesis; complete to
`z ≺ σ(B)` (d); HLP (e) + convexity of `Φ N` (triangle + smul) + permutation
invariance give `Φ N z ≤ Φ N (σ(B))`; coordinate monotonicity (c) gives
`Φ N (σ(A)) ≤ Φ N z`; conclude via (b).  Comparator candidate (the package
(a)–(f) is a self-contained "UI norms via Fan dominance" Mathlib
contribution).

**F4 — UI-norm Sylvester bound and the part-III sinΘ theorem.**
(a) *Ideal property. Difficulty 2/5.*  `N (C ∘ₗ X) ≤ c * N X` when
`∀ x, ‖C x‖ ≤ c‖x‖` (and mirrored) — Fan dominance (F3.f) applied to the
singular-value domination F0(e) (`kyFanSum` is monotone in pointwise σ
domination — one `Finset.sum_le_sum`).
(b) *Abstract Sylvester bound. Difficulty 2.5/5.*  In `SylvesterBound.lean`
(new section; keep the op-norm originals untouched): for `N` with triangle +
smul + ideal property (state the hypotheses raw, so the lemma does not depend
on the F3 structure — `UnitarilyInvariantNorm` instantiates it), `A, B`
symmetric `δ`-coercive, `A∘X + X∘B = Y` ⇒ `N X ≤ N Y / (2δ)`.  The
absorption identity is verbatim W5.1's
`((‖A‖+‖B‖ : ℝ) : 𝕜) • X = Y + (‖A‖•1 − A)∘X + X∘(‖B‖•1 − B)`; unlike the
op-norm proof, no pointwise dance: apply `N`, use smul + triangle + ideal
property with the correction-operator bounds `norm_opNorm_smul_sub_apply_le`
(exists, private — un-private or duplicate its two-line statement), solve the
scalar inequality.  Separated form by the same midpoint shift.
(c) *Part-III sinΘ, every UI norm. Difficulty 3/5.*  New
`SinThetaUINorm.lean`:

> `N (V.starProjection ∘L U.starProjection) ≤ N (S − T) / g`

under exactly the W5.2 hypotheses.  Route: the W5.2 proof
(`SinThetaOpNorm.lean`) is already structured as: build `A, B, X, Y`
(full-space scalar extensions), prove symmetry + coercivity + the Sylvester
relation `A∘X − X∘B = Y` — **all of that is norm-free and reusable
verbatim**; extract it as a shared `private` "setup" lemma (or inline-copy;
prefer extraction, it also de-duplicates SinThetaOpNorm.lean), then finish
with F4(b) instead of the op-norm bound, plus `N Y ≤ N (S−T)` (ideal property
twice: `Y = P ∘L (T−S) ∘L Q`, contractions on both sides) and
`N (Q∘P) = N (star (P∘Q)) = N (P∘Q)` — *pitfall:* UI-norm invariance under
`star` is a lemma to add in F3 (`N (A⋆) = N A` via `singularValues_adjoint` +
(b)'s gauge representation), not an axiom.
Instantiating `N :=` Frobenius / op-norm recovers the existing theorems —
state both as `example`s or thin corollaries for the paper's dictionary.

---

## Phase G — the remaining subspace theorems (sin2Θ, tan2Θ, tanΘ)

Research-grade formalization; **statement-first gate mandatory** (commit the
`sorry` stub + a cross-check paragraph against the source before proving).
Consult `ForMathlib/prose/Davis-1963-core-arguments.tex` and DK III §§6–8
(Stewart–Sun V.3, Bhatia VII.1–2 as secondary) *before* writing each stub —
the hypothesis structure is exactly where these theorems are subtle, and no
route below should be trusted over the sources.  All three are
**Fable-grade**; Opus should attempt only after the F-phase, and only with
the descope options.

**G1 — Subspace sin2Θ. Difficulty 5/5.**  Target statement (Frobenius first;
UI-norm upgrade after F4): both `P` (spectral for `T`, block `[b, ∞)` vs
`(−∞, a]`) and `P̂` (the analogously-chosen spectral projection of
`S = T + H`), conclusion `‖sin 2Θ‖_F ≤ 2‖H‖_F / (b − a)`-shape.
Route candidates, in order of preference:
(i) *Commutator identity route:* for orthogonal projections `P, Q`:
`(P − Q)(P + Q − 1) = PQ − QP = [P, Q]`, and the singular values of `[P, Q]`
are `{sin θᵢ cos θᵢ}` (with multiplicity bookkeeping) — so
`‖sin 2Θ‖ = 2‖[P, P̂]‖` in any UI norm.  Then bound the commutator: `[P, P̂]`
satisfies a Sylvester-type relation obtained by compressing
`S P̂ = P̂ S` and `T P = P T` against the two block splittings; the diagonal
blocks of `H` drop out, which is where the factor-2-with-full-`H` (vs
`H_odd`) bookkeeping lives.  The commutator-singular-value lemma is
independently valuable and a good first sub-brick (3.5/5 alone).
(ii) *Davis's odd-part route:* `J := 2P − 1`; split `H` into `J`-commuting
and `J`-anticommuting parts; the per-vector W6.1 `key_identity` machinery
summed over an eigenbasis of `S` with the diagonal parts cancelled by
symmetry (this is what fails naively — the v5 W6.3 warning stands; the
cancellation must happen *before* the norm is taken).
Descopes if blocked: (α) the already-recorded dimension-carrying summed
corollary of W6.1 (trivial, explicitly-weaker docstring); (β) `‖sin 2Θ‖_op`
for the largest angle via W6.1 at a worst eigenvector.

**G2 — Subspace tan2Θ (vanishing pinch). Difficulty 4.5/5 (after G1).**
Same skeleton as G1 with the vanishing-diagonal-block hypotheses (state them
subspace-wise as in `tan_two_theta_le_of_mem`); the G1 machinery with the
diagonal blocks hypothesized away rather than cancelled.  Do not start before
G1's route is settled.

**G3 — Subspace tanΘ. Difficulty 5/5 — the single hardest remaining item;
highest statement-risk.**  DK III Thm 6.3 / Stewart–Sun V.3.6 shape: **one
operator** `A`, an exact spectral subspace, an arbitrary test subspace
`Z = ran ι_Z` with `M := ι_Z⋆ A ι_Z` and residual `R := A ι_Z − ι_Z M`;
hypotheses `σ(M) ⊆ [a, b]`, complementary exact spectrum `≤ a − δ` (one
side!); conclusion `‖tan Θ‖ ≤ ‖R‖/δ`.  Sub-bricks:
(i) statement stub + source cross-check (the tan operator needs
`cos Θ` invertible — determine from the source whether invertibility is a
hypothesis, a conclusion, or handled by convention, and mirror exactly);
(ii) the graph-operator formulation: `G := P_{Uᗮ} ι_Z (P_U ι_Z)⁻¹` with
`σᵢ(G) = tan θᵢ` (an E2-style identification, harder — needs the
`(P_U ι_Z)⁻¹` API);
(iii) the Sylvester relation `G` satisfies has a *similar-to-symmetric*
coefficient (`(P_U ι_Z) M (P_U ι_Z)⁻¹`), which the quadratic-form Sylvester
bound does **not** cover — either (α) prove the spectral-hypothesis Sylvester
variant for the special structure at hand (the coefficient is
`K M K⁻¹` with `K` the cos-compression — its quadratic form *after the
substitution `X ↦ X K`* becomes symmetric again; try the substitution trick
first: `A' (XK) − (XK) M = Y K` restores symmetric coefficients), or
(β) follow DK III's own §6 argument line-by-line from the prose digest.
Descopes: `d = 1` (single vector — easy, from the per-vector machinery);
Frobenius-only.

---

## Phase H — recorded as out of scope (documentation only)

- **H1 general-separation op-norm sinΘ (constant `π/2`)**: Fourier-analytic
  (Bhatia–Davis–McIntosh extremal function); genuinely a different proof
  technology.  Record in the paper as known-open in the formalization.
- **H2 infinite dimensions**: `SylvesterBound.lean` and `RotationSharp.lean`
  already hold without finite dimension; the eigenbasis-encoded layer is
  finite-dimensional by design.  A spectral-measure DK is a separate project;
  document the frontier precisely (which theorems are already
  dimension-free).
- **H3 generalized eigenproblems / relative perturbation** (definite pencils,
  Ipsen/Li): modern extensions, not part of "the DK theory"; out of scope.

---

## Execution order and dependency graph

```
E1 ─→ E2 ──────────────┐
E3, E4, E5 (parallel)  │  [Batch 1: dictionary — closes Tier-2 items]
                       ▼
F0 ─→ F1.a → F1.b → F1.c ─→ F2      [Batch 2: Ky Fan]
F3.a → F3.b → F3.c ─┐
F3.d, F3.e ─────────┴→ F3.f          [Batch 3: Fan dominance]
F0.e/F3.f → F4.a → F4.b → F4.c       [Batch 4: part-III sinΘ — the headline]
F4 ─→ G1 → G2;  G3 independent of G1/G2 but after F4   [Batches 5–6: Fable]
```

Each batch ends: `lake build` green, axiom check, golf pass, paper sync
(move items out of §"What remains", extend the dictionary tables, update the
permalink), comparator candidates filed (F1.b, F2 triangle, F3.e, F3 package,
F4.c; E2 and F0.d are also upstream-attractive).

## Difficulty ranking (hardest first)

| Rank | Step | What | Difficulty | Assignee |
|------|------|------|-----------|----------|
| 1 | G3 | Subspace tanΘ (graph operator, similar-to-symmetric Sylvester) | 5/5 | **Fable**; statement-risk |
| 2 | G1 | Subspace sin2Θ (commutator route) | 5/5 | **Fable** |
| 3 | G2 | Subspace tan2Θ | 4.5/5 | **Fable** (after G1) |
| 4 | F3.e | Hardy–Littlewood–Pólya via T-transforms | 4/5 | Opus, timeboxed; Fable fallback |
| 5 | F1.c | Ky Fan variational principle | 3.5/5 | Opus |
| 6 | F3.a | Operator SVD factorization | 3.5/5 | Opus |
| 7 | E2 | `‖Q̂P‖ = sin θ_max` identification | 3.5/5 | Opus |
| 8 | F1.b | Ky Fan trace inequality | 3/5 | Opus |
| 9 | F3.c | Gauge coordinatewise monotonicity | 3/5 | Opus |
| 10 | F4.c | Part-III sinΘ, every UI norm | 3/5 | Opus |
| 11 | F0 | Singular-value API (incl. Loewner monotonicity) | 2.5/5 | Opus |
| 12 | F3.b | UI-norm structure + gauge representation | 2.5/5 | Opus |
| 13 | F3.d | Weak-majorization completion | 2.5/5 | Opus |
| 14 | F4.b | Abstract-norm Sylvester bound | 2.5/5 | Opus |
| 15 | E3 | Spectral corollaries (+ un-private specSubspace) | 2.5/5 | Opus |
| 16 | E4 | Frobenius-encoding coherence bridges | 2.5/5 | Opus |
| 17 | E1 | Extreme-singular-value variational lemmas | 2/5 | Opus |
| 18 | F1.a | Knapsack lemma | 2/5 | Opus |
| 19 | F2 | Ky Fan norms + weak-majorization triangle | 2/5 | Opus |
| 20 | F4.a | Ideal property | 2/5 | Opus |
| 21 | F3.f | Fan dominance assembly | 2/5 | Opus |
| 22 | E5 | `sep` wrappers + separation documentation | 1/5 | Opus |

## Definition of done (overall)

- Phases E–F complete ⇒ the paper's §"What remains" reduces to the three
  Phase-G theorems and the Phase-H notes; part-III sinΘ (every UI norm,
  Frobenius and op-norm as instances) is the new headline.
- Phase G complete ⇒ the DK III quartet is formalized at the subspace level;
  the paper's gap list reduces to Phase H (documented as out of scope).
- Every batch: statement-first gates honored where mandated; new files carry
  provenance headers and are registered in `ForMathlib.lean`; difficulty
  re-rated in this file when reality disagrees with the estimate.
