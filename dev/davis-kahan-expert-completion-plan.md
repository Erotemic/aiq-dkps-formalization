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
- **v8 (2026-07-09, Fable — full remaining-work roadmap; Opus tasks promoted
  to routed step bodies):** the two Opus follow-ups filed in v7 as one-liners
  are now a full **Phase OP** (between Phase G and Phase H) with
  F4-grade step bodies: **OP1** G1 spectral corollaries (2/5), **OP2** the
  Frobenius `UnitarilyInvariantNorm` instance (2.5/5 — invariance is already
  stocked by `sum_sq_norm_apply_unitary_comp`, so cheaper than v7 estimated),
  and **OP3** the sin 2Θ dictionary certification
  `σᵢ(Q P̂ P) = cos θᵢ sin θᵢ` (3/5 — was the 3.5/5 "Fable-leaning
  dictionary" item; the gram-diagonalization route below is Fable-verified on
  paper, so it is now Opus-executable with a statement review).  **Ordering:
  OP1/OP2/OP3 are mutually independent and depend only on landed material
  (E-phase, F3, F4, G1); none of them waits on G2/G3, so Opus can execute
  Phase OP first, in any order, while G2/G3 remain with Fable.**  G2 and G3
  bodies restructured into gated stages (G2.0/G3.0 statement gates are
  Fable-checkpoints; post-gate sub-bricks graded and assigned).  Execution
  graph and difficulty table updated accordingly.
- **v7 (2026-07-09, Fable — Opus's F4 reviewed: correct; G1 ✅ DONE by a NEW
  route):** F4 review verdict: all four deliverables correct and idiomatic;
  the `Subsingleton`/`Nontrivial` case split in F4.b is the right fix for a
  genuine seminorm trap (`N X = 0 ↛ X = 0`, so the op-norm proof's case split
  does not transfer) — good catch.  **G1 landed** (`SinTwoThetaUINorm.lean`,
  gate `e38956e`, proof `c17998d`, both headlines axiom-clean) via **route
  (iii), the mirror reduction** — neither of the plan's two candidates:
  reflect `T` through the *perturbed* subspace (`J := V.reflection`,
  `T' := J T J`) and apply F4.c to the pair `(T, T')`; `J(Uᗮ)` is
  `T'`-invariant with the transported form bound, so the pair is separated by
  `T`'s own gap; the cross-projection is `J`-conjugate to `Q J P = 2 Q P̂ P`,
  and `N (T' − T) ≤ 2 N (S − T)` since `J` commutes with `S`.  This is DK
  III's own §8 argument and it collapses G1 from 5/5 to ~3/5-given-F4: no
  commutator dictionary, no odd-part cancellation, ~180 lines.  Landed:
  `sin_two_theta_reflection_le` (mirror-defect form, no second operator) and
  `sin_two_theta_starProjection_le` (headline; hypotheses: two-sided form
  separation on `T` alone, `V` merely `S`-invariant — strictly more general
  than the classical statement).  Lean notes: the reflection coercion normal
  form is `LinearEquiv.coe_coe` + `LinearIsometryEquiv.coe_toLinearEquiv`;
  `Submodule.starProjection_map_apply` needs a `show` to the `.map` form
  (dependent instance blocks `rw`); `reflection_apply`'s `2 •` is ℕ-smul
  (`Nat.cast_smul_eq_nsmul` bridges to `((2:ℝ):𝕜) •`).  **New Opus-tractable
  follow-ups filed:** (i) E3-style spectral corollaries of G1
  (`specSubspace` + sorted-eigenvalue hypotheses, mirroring
  `norm_starProjection_comp_starProjection_le_of_eigenvalues`) — 2/5;
  (ii) the Frobenius `UnitarilyInvariantNorm` instance (define via
  `√(∑ ‖A (b i)‖²)`; invariance from the gram machinery) — 2.5/5, makes the
  F4/G1 headlines instantiate to the paper's Frobenius vocabulary.
  **G2 note (route candidates revised):** the mirror route yields *sine-type
  absolute* bounds; the vanishing-pinch tan2Θ is a *relative* bound (angles
  past π/4 allowed), so it likely needs the per-vector `key_identity`
  machinery summed with the diagonal blocks hypothesized away (old route
  (ii)), or a mirror variant with the pinch killing the even part — fresh
  statement-first gate mandatory.  G3 unchanged.
- **v6 (2026-07-09, Opus — F4 ✅ DONE):** the part-III sinΘ theorem now holds in
  every unitarily invariant norm.  F4.a `apply_comp_le`/`apply_comp_le'`
  (ideal property, `UnitarilyInvariantNorm.lean`); F4.b
  `le_div_of_comp_add_comp_eq`/`le_div_of_comp_sub_comp_eq` (abstract Sylvester
  bound for any operator seminorm with the ideal property, `SylvesterBound.lean`
  — the absorption identity is applied at the *operator* level, so `N` acts
  directly with no pointwise estimate; DRY-refactored the op-norm helper via new
  `norm_opNorm_smul_one_sub_le`); F4.c: extracted the norm-free setup as
  `exists_isSymmetric_comp_sub_comp_eq` (`SinThetaOpNorm.lean`, op-norm theorem
  refactored to consume it — no regression) and the headline
  `apply_starProjection_comp_starProjection_le` in new `SinThetaUINorm.lean`,
  via the induced CLM seminorm `fun f => N ↑f` fed to F4.b (its ideal property is
  F4.a + `ContinuousLinearMap.le_opNorm`), plus `N Y ≤ N (S−T)` and
  star-invariance.  Also `opNorm 𝕜 E : UnitarilyInvariantNorm 𝕜 E` (the
  structure is inhabited — invariance is `opNorm_comp_linearIsometryEquiv`).
  Commits `b8de103` (F4.a/b/c) and `9d73132` (instance); all headlines
  axiom-clean, full library green.  Route deviations: `pow`/`le_or_lt`-style
  renames as in v5; the induced-norm bridge needed
  `ContinuousLinearMap.toLinearMap_add`/`_smul` (the `coe_add`/`coe_smul`
  aliases are deprecated).  **Next: Phase G (Fable) — subspace sin2Θ/tan2Θ/tanΘ.**
- **v5 (2026-07-09, Fable — F3 ✅ DONE):** the full v4-reroute F3 landed as
  `UnitarilyInvariantNorm.lean` (commit `7481732`), all headlines axiom-clean,
  full library build green, zero warnings in the new file: `diagOp` + algebra
  + `singularValues_diagOp`; operator SVD
  `exists_unitary_diagOp_factorization`; the `UnitarilyInvariantNorm`
  structure (standalone + `CoeFun`, per the v4.1 note) with
  nonneg/zero/neg/one-sided invariances derived; gauge on all vectors with
  `gauge_add_le` / `gauge_real_smul` / `gauge_perm` / `gauge_neg_single`;
  `gauge_update_le` + `gauge_mono`; the T-transform descent
  `gauge_le_gauge_of_prefix_sums_le` (disagreement-count induction, exactly
  the v4 route — `card ≤ d` plain induction replaced strong induction);
  Fan dominance `apply_le_of_kyFanSum_le`; star invariance `apply_adjoint`.
  `sum_filter_lt_eq_sum_fin` un-privatized in KyFan.lean as planned.
  Deviations from the v4 routes (minor, all Lean-level): `pow_le_pow_left` is
  `pow_le_pow_left₀` in this pin; `le_or_lt` is `le_or_gt`; `push_neg` is
  `push Not`; binder-position `Finset.univ.filter fun …` needs
  parentheses before the `,`; the c₁/c₂ convex-combination arithmetic under
  `set` must avoid `linear_combination` through division definitions (use
  `← add_mul` + the sum-to-one identity instead).  Paper synced (Phase E +
  F0–F2 + F3 paragraphs, dictionary rows, §remains item 2 re-scoped to F4,
  permalink → `7481732`).  **Next: F4 (Opus)** — a/b/c routes below are
  ready; then Phase G (Fable).
- **v4 (2026-07-09, Fable — Opus plan-review triaged; F3 body rewritten to the
  reroute):** disposition of the "Opus review of plan v3" below.  **Retracted**
  its two false negatives — Opus's greps ran in an FD-exhausted environment
  with `2>/dev/null`, so empty results were unreliable; re-verified in a
  healthy shell: **Birkhoff IS in the pin**
  (`Mathlib/Analysis/Convex/Birkhoff.lean`,
  `doublyStochastic_eq_convexHull_permMatrix` at line 165) and
  **`Submodule.reflection` IS in the pin**
  (`Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`,
  `K.reflection : E ≃ₗᵢ[𝕜] E`, `reflection_apply : K.reflection p =
  2 • K.starProjection p - p`) — so BLOCKING #2 is moot and the v1 asset
  inventory stands.  **Accepted** BLOCKING #1 (the F3 step body below is now
  the reroute, old F3.d/F3.e demoted to an optional annex), BLOCKING #3 (gauge
  convexity/permutation/sign-flip invariance are now named F3.b deliverables),
  the F1(c) cross-reference fix (the two KyFan.lean theorem names), the F4.c
  coercion-layer caveat (folded into F4.c), and the DONE-stamp suggestion.
  Descent argument re-verified on paper (δ/c₂ arithmetic checked; see F3.d).
  **Process rule added:** never trust a *negative* grep from a session with
  FD errors; re-run before acting on it.
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

## Opus review of plan v3 (2026-07-09)

I (Opus, the executing agent) read the whole plan and name-checked its concrete
asset claims against the repo and the pinned Mathlib.  The plan is executable
as written for the E-phase and F0–F2 (both already landed) and for F4.  Below
are the points that are **unclear or that I cannot execute from the description
alone**, ranked by how much they block me, plus the asset claims I verified so
future executors don't re-check.  Each is cross-referenced to the step it
concerns; I also left short inline `> **[Opus review]**` flags at those steps.

**Verified present (no action needed):**
- `OrthonormalBasis.equiv` — the F3.a basis-exchange unitary the plan flags
  with "check name; else build" **does exist** in pinned Mathlib
  (`Mathlib/Analysis/InnerProductSpace/PiL2.lean`, `protected def equiv :
  E ≃ₗᵢ[𝕜] E'`).  Use it directly.
- `sqrt_apply_eigenvectorBasis`, `polarUnitary`, `polar_decomposition_unitary`,
  `eigenvalues_conj_unitary`, `eigenvalues_abs` (KyFan.lean:183) — all present.
- F4's privates `norm_le_of_abs_re_inner_map_self_le` (a `→L[𝕜]` / CLM lemma,
  SylvesterBound.lean:78) and `norm_opNorm_smul_sub_apply_le`
  (SylvesterBound.lean:126) — present.
- Rearrangement inequality — present (`Mathlib/Algebra/Order/Rearrangement`).

**BLOCKING-clarity #1 — which F3 do I build?  (highest priority).**  The v3
reroute is described *only in the revision-log prose* (the F0–F2/F3-reroute
entry above), but the **Phase F → F3 step body below still describes the OLD
route** (F3.d weak-majorization completion + F3.e HLP + F3.f).  So the F3 I am
told to implement (reroute: T-transform descent directly on the gauge) and the
F3 that is actually *written out with target files and statement shapes*
disagree.  An executor does not know which to build.  **Please promote the
reroute to a proper numbered step body** (target file, headline
`theorem … := sorry` under the statement-first gate, the exact sub-lemmas) and
explicitly mark old F3.d/F3.e as "optional Mathlib-attractive extra, OFF the
critical path".  Until that is done I would either build the wrong thing or
stall.

> **[Fable v4] Accepted.**  The F3 step body below is now the reroute
> (steps a–f renumbered); the old completion+HLP route is the "optional
> annex" at the end of Phase F.

**BLOCKING-clarity #2 — `Submodule.reflection` does not exist (F3.c and the
v3-reroute closing step).**  Both the reroute prose ("single-coordinate
reflection step via `Submodule.reflection ((𝕜 ∙ b j)ᗮ)`") and F3.c ("the sign
flip … is conjugation by the unitary … `reflectionUnitary b j`") cite a
reflection API.  **There is no `reflection` definition in the pinned Mathlib**
(confirmed full-tree grep: nothing in `Analysis/InnerProductSpace` or
`Geometry/Euclidean`).  This must be *constructed*, not cited.  Concretely, the
single-coordinate sign flip `b j ↦ −b j` (fixing `b i` for `i ≠ j`) is cleanest
as `diagOp b (Function.update (fun _ => 1) j (-1))` **once `diagOp` (F3.a)
exists** — i.e. F3.c's reflection depends on F3.a, which the dependency graph
does not show — or, F3.a-independently, as `2 • (𝕜 ∙ b j)ᗮ.starProjection − 1`
(needs a two-line "this is an isometry" lemma).  Please pick one and name it as
a new construction with a difficulty bump (this is a small brick, ~0.5/5, but
it is a *new* one, not a lookup).

> **[Fable v4] Retracted — false negative.**  `Submodule.reflection` **does**
> exist in this pin (`Mathlib/Analysis/InnerProductSpace/Projection/
> Reflection.lean`; `K.reflection : E ≃ₗᵢ[𝕜] E`, `reflection_apply`,
> `reflection_symm`, `reflection_singleton_apply`).  The grep above ran in the
> FD-exhausted session with `2>/dev/null`, which silently dropped every file
> read.  Rule for future sessions: a negative grep from a session showing
> `Bad file descriptor` errors is evidence of nothing — re-run it.

**BLOCKING-clarity #3 — the reroute descent needs a gauge-convexity sub-lemma
that isn't stated.**  The reroute's per-step cost is "one two-term triangle
inequality" on `y' = c₁•y + c₂•(y∘swap)`.  For that I need `Φ N` defined on
*arbitrary* nonneg vectors (not just sorted σ-vectors) and its **subadditivity /
convexity in the vector argument** as an explicit lemma:
`Φ N (c₁•x + c₂•x') ≤ c₁·Φ N x + c₂·Φ N x'` for `c₁+c₂=1`, `cᵢ≥0`.  F3.b only
establishes the gauge *representation* `N A = Φ N (σ A)` on sorted σ-vectors;
convexity of `x ↦ Φ N x = N (diagOp b x)` follows from `diagOp` being ℝ-linear
in `x` plus `N`'s triangle+smul, but it should be a named F3 sub-lemma the
descent can cite, not left implicit.  Please add it.

> **[Fable v4] Accepted.**  The gauge is now defined on *all* of `Fin n → ℝ`
> and F3.b's deliverables include the named lemmas `gauge_add_le`,
> `gauge_real_smul`, `gauge_perm`, `gauge_neg_single` (sign flip) — see the
> rewritten F3.b below.

**Factual fix — asset inventory overstates Mathlib (affects F3.d fallback and
F3.e comparator framing).**  The inventory says "Mathlib (pinned) has … Birkhoff
(`doublyStochastic_eq_convexHull_permMatrix`)".  **It does not** — full-tree
grep finds no `doublyStochastic`, no Birkhoff, and (as the plan elsewhere
correctly states) no majorization theory at all in this pin.  Consequences: the
F3.d descope ("substochastic Birkhoff padding trick") is **not** available as a
lookup, and the F3.e comparator note "at the level of Birkhoff itself" should
read "would also require Birkhoff, likewise absent".  Since the reroute drops
F3.d/F3.e from the critical path this isn't fatal, but the inventory line is
wrong and the F3.d fallback must be treated as fully self-contained.

> **[Fable v4] Retracted — false negative** (same FD-broken-grep cause as #2).
> `doublyStochastic_eq_convexHull_permMatrix` **is** in the pin
> (`Mathlib/Analysis/Convex/Birkhoff.lean:165`, plus
> `DoublyStochasticMatrix.lean`).  The v1 inventory line stands.  What *is*
> correct: no majorization API upstream (only docstring mentions), so the
> annex HLP brick remains Mathlib-attractive.

**Minor — F4.c "reusable verbatim" is optimistic (a coercion layer, not a
math risk).**  The op-norm setup in `SinThetaOpNorm.lean`
(`norm_starProjection_comp_starProjection_le`) builds `A, B, X, Y` at the
**`→L[𝕜]` (ContinuousLinearMap)** level and finishes with the CLM Sylvester
bound.  F4.b / `UnitarilyInvariantNorm` live at the **`→ₗ[𝕜]` (LinearMap)**
level (the plan's own F4.b note).  So extracting the setup and "finishing with
F4(b)" needs an explicit `toLinearMap`/`toContinuousLinearMap` bridge (trivial
in finite dimension, but real bookkeeping).  Budget for it; "verbatim" undersells
the coercion glue.

**Minor — F1(c) cross-references.**  F1's variational principle landed in
KyFan.lean as *two* named theorems, `re_sum_inner_map_le_sum_singularValues`
(the bound) and `exists_orthonormal_re_sum_inner_map_eq` (achievability), not a
single `∑σ = sup`.  F3.a/F3.b/the reroute that cite "F1(c)" should cite these
two names.

> **[Fable v4] Accepted** — the rewritten Phase F below cites the two theorem
> names directly.  (The F4.c coercion-layer point and the DONE-stamp point are
> likewise accepted; stamps added to the E/F0–F2 headers and the coercion
> caveat folded into F4.c.)

**Clarity — mark completed sections done in the bodies, not only the log.**
The revision log records Phase E and F0–F2 as ✅ DONE, but the Phase E and
F0–F2 *section bodies* (and the execution-order graph and difficulty table)
still read as open TODOs.  I confirmed E2 is fully implemented in
`PrincipalAngles.lean` (the `familyIsometry`/`overlapOp` Pythagoras machinery,
both `le_antisymm` directions, the `y₀` witness).  A fresh executor could redo
landed work.  Suggest a `✅ DONE (commit …)` stamp on each completed step header.

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

> **[Opus review — retracted by Fable v4]** ~~`doublyStochastic`/Birkhoff is
> absent from the pinned Mathlib~~ — false negative from an FD-broken grep;
> it **is** present (`Analysis/Convex/Birkhoff.lean:165`).  The inventory
> line above is correct as written.
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
## ✅ DONE in full (v2; E1–E5 landed, see the v2 revision-log entry for deviations)

Small, concrete, high value: after Phase E every bound already proved is
*certified* to be a statement about principal angles, in both norms, and every
theorem has its literature-facing eigenvalue-hypothesis form.  All items are
Opus-safe.  **Do not re-execute: E1–E5 are all landed and axiom-clean**
(E2's `‖Q̂P‖ = sin θ_max` is in PrincipalAngles.lean, E3's spectral
corollaries in SinThetaOpNorm.lean, E4's coherence bridges in
PrincipalAngles.lean; step bodies kept below for provenance only).

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

**Status: F0–F2 ✅ DONE** (`KyFan.lean`, commit `199390a`, axiom-clean; the
F1(c) variational principle landed as the pair
`re_sum_inner_map_le_sum_singularValues` /
`exists_orthonormal_re_sum_inner_map_eq` — cite those names, not "F1(c)").
**F3 ✅ DONE** (`UnitarilyInvariantNorm.lean`, commit `7481732`, v5 log entry;
body below kept for provenance).  **F4 is the active step (Opus).**

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

**F3 — Unitarily invariant norms and Fan dominance.  ✅ DONE (commit
`7481732`; see the v5 revision-log entry for the landed names and the
Lean-level deviations).  [v4 body = the v3 reroute; HLP and weak-majorization
completion are NOT on this path — they live in the optional annex at the end
of Phase F.]**
In new `UnitarilyInvariantNorm.lean`.  All asset names below re-verified
against the pin in a healthy shell (2026-07-09, Fable).
(a) *`diagOp` and operator SVD factorization. Difficulty 3.5/5.*  Fix
`b : OrthonormalBasis (Fin n) 𝕜 E`, `hn : finrank 𝕜 E = n`.  Define
`diagOp b (x : Fin n → ℝ) : E →ₗ[𝕜] E := ∑ i, (x i : 𝕜) • (⟪b i, ·⟫ • b i)`
(rank-one sums — the `spectralProjection` idiom of IntertwiningUnitary.lean).
API: `diagOp_apply_basis : diagOp b x (b i) = (x i : 𝕜) • b i`; ℝ-linearity
in `x` (`diagOp_add`, `diagOp_real_smul`); `(diagOp b x).IsSymmetric`;
`diagOp b x ∘ₗ diagOp b y = diagOp b (x * y)`.
Prove: **`∃ (Uu Vv : E ≃ₗᵢ[𝕜] E), A = Uu ∘ₗ diagOp b (σ(A)) ∘ₗ Vv`** —
route: `A = polarUnitary A ∘ₗ |A|` (`polar_decomposition_unitary`); let
`w := (isSymmetric_adjoint_comp_self A).eigenvectorBasis hn` (also an
eigenbasis of `|A|` with eigenvalues `σᵢ(A)`, via
`sqrt_apply_eigenvectorBasis` + `eigenvalues_abs`, KyFan.lean:183); let
`K := b.equiv w (Equiv.refl _) : E ≃ₗᵢ[𝕜] E` (**verified**:
`OrthonormalBasis.equiv`, Mathlib PiL2.lean:840, maps `b i ↦ w i`); then
`|A| = K ∘ diagOp b (fun i => σᵢ(A)) ∘ K.symm` (check on the basis `w`), so
`Uu := polarUnitary A |>.trans` — careful with composition order —
`Uu := K.trans (polarUnitary A)`-shaped, `Vv := K.symm`.
Also record `singularValues_diagOp` : for *antitone nonneg* `x`,
`σᵢ(diagOp b x) = x i` — via `(diagOp b x)⋆ ∘ diagOp b x = diagOp b (x*x)`
(adjoint = itself by symmetry), `b` is an eigenbasis of `diagOp b (x*x)` with
antitone values `x i ^ 2`, so `eigenvalues_eq_of_eigenbasis`
(CourantFischer.lean, landed with F0) gives `λᵢ = xᵢ²`, then `Real.sqrt`.
(b) *The structure, the gauge on ALL vectors, and the invariance package.
Difficulty 2.5/5.*
```
structure UnitarilyInvariantNorm (𝕜 E) [...] where
  toFun : (E →ₗ[𝕜] E) → ℝ
  add_le' : toFun (A + B) ≤ toFun A + toFun B
  smul'   : toFun (a • A) = ‖a‖ * toFun A
  invariant' : ∀ (Uu Vv : E ≃ₗᵢ[𝕜] E) A, toFun (Uu ∘ₗ A ∘ₗ Vv) = toFun A
```
(seminorm axioms suffice for DK — positivity is never used; note this in the
docstring; derive `nonneg` and `map_zero` as lemmas.  Consider `extends
Seminorm 𝕜 (E →ₗ[𝕜] E)` if the API friction is low; otherwise standalone
with a `CoeFun`.)  Define the gauge **on all of `Fin n → ℝ`** (per the Opus
review, BLOCKING #3): `Φ N x := N (diagOp b x)`, with the named lemma
package the descent consumes:
  - `gauge_add_le : Φ N (x + y) ≤ Φ N x + Φ N y` (from `diagOp_add` +
    `add_le'`);
  - `gauge_real_smul : Φ N (c • x) = |c| * Φ N x` (from `diagOp_real_smul` +
    `smul'`, `‖(c : 𝕜)‖ = |c|`);
  - `gauge_perm : Φ N (x ∘ π) = Φ N x` for `π : Equiv.Perm (Fin n)` — with
    `P := b.equiv b π` (maps `b i ↦ b (π i)`):
    `diagOp b (x ∘ π) = P.symm ∘ₗ diagOp b x ∘ₗ P` (check on the basis:
    both sides send `b j ↦ x (π j) • b j`), then `invariant'`;
  - `gauge_neg_single : Φ N (Function.update x j (−(x j))) = Φ N x` — via the
    **one-sided** composition `diagOp b (update x j (−x j)) = diagOp b x ∘ₗ R`
    with `R := ((𝕜 ∙ b j)ᗮ).reflection` (**verified present**:
    `Submodule.reflection`, Mathlib
    `Analysis/InnerProductSpace/Projection/Reflection.lean`; `R (b j) = −b j`
    and `R (b i) = b i` for `i ≠ j` since `b i ∈ (𝕜 ∙ b j)ᗮ`); note the
    *conjugation* `R ∘ D ∘ R = D` is a trap — it does nothing (D preserves
    R's eigenspaces); the one-sided form is the correct one, and `invariant'`
    with `Uu := 1` covers it.
Then the representation **`N A = Φ N (σ(A))`** from (a) + `invariant'`.
(Basis-independence of `Φ` on antitone nonneg vectors is free via basis
exchange; record as a remark, no lemma needed.)
(c) *Update bound and coordinatewise monotonicity. Difficulty 2.5/5.*
  - `gauge_update_le : |t| ≤ y j → Φ N (Function.update y j t) ≤ Φ N y` —
    if `y j = 0` then `t = 0` and `update y j 0 = ` needs no step (rewrite);
    else write `update y j t = c₁ • y + c₂ • (update y j (−(y j)))` with
    `c₁ := (y j + t) / (2 * y j)`, `c₂ := (y j − t) / (2 * y j)`
    (both nonneg, `c₁ + c₂ = 1`; check the two cases `i = j`, `i ≠ j`
    pointwise), then `gauge_add_le` + `gauge_real_smul` + `gauge_neg_single`.
  - `gauge_mono : 0 ≤ x → x ≤ y (pointwise) → Φ N x ≤ Φ N y` — strong
    induction on `(Finset.univ.filter (fun i => x i ≠ y i)).card`; pick a
    disagreeing `j`, pass through `update y j (x j)` (apply
    `gauge_update_le` with `|x j| ≤ y j` from `0 ≤ x j ≤ y j`), disagreement
    count drops.
(d) ***The T-transform descent on the gauge — the crux. Difficulty 4/5.
Fable.***  Statement (`z` plays σ(A), `y` plays σ(B)):

> `gauge_le_of_prefix_sums_le` : for `z y : Fin n → ℝ` with `z` antitone,
> `0 ≤ z`, `0 ≤ y`, and
> `∀ m : ℕ, ∑ i ∈ univ.filter (·.val < m), z i ≤ ∑ i ∈ univ.filter (·.val < m), y i`:
> `Φ N z ≤ Φ N y`.

Route (re-verified on paper, v4): strong induction on
`d := (univ.filter (fun i => z i ≠ y i)).card`.
  - *Case `∀ i, z i ≤ y i`:* `gauge_mono`.  (Subsumes `d = 0`.)
  - *Else:* `l :=` least index with `y l < z l`; minimality gives
    `∀ i < l, z i ≤ y i`; `j :=` least index with `z j ≠ y j`.  If `j = l`,
    the prefix at `m = l + 1` reads `∑_{i<l} y + z l ≤ ∑_{i<l} y + y l`
    (using `z i = y i` for `i < l`), contradicting `y l < z l`; so `j < l`
    and `z j < y j`.  Sortedness: `y j > z j ≥ z l > y l`, so
    `y j − y l > 0`.  Set `δ := min (y j − z j) (z l − y l) > 0`;
    `2δ ≤ (y j − y l) − (z j − z l) ≤ y j − y l`, so
    `c₂ := δ / (y j − y l) ∈ (0, 1/2]`, `c₁ := 1 − c₂`.
    Define `y' := update (update y j (y j − δ)) l (y l + δ)`.  Then:
    (i) `y' = c₁ • y + c₂ • (y ∘ Equiv.swap j l)` — funext, three cases;
    (ii) `0 ≤ y'` (`y' j ≥ z j ≥ 0`, `y' l ≥ y l ≥ 0`);
    (iii) prefix domination for `(z, y')`: prefixes with `m ≤ j` or `m > l`
    unchanged; for `j < m ≤ l`:
    `P_m(y) − P_m(z) = ∑_{i<m} (y i − z i) ≥ y j − z j ≥ δ` termwise
    (every `i < m ≤ l` has `z i ≤ y i`, and `i = j` contributes
    `y j − z j`), so `P_m(z) ≤ P_m(y) − δ = P_m(y')`;
    (iv) at least one of `j, l` now agrees (`δ` attains one of its two
    arguments) and no agreement is destroyed, so the count drops;
    (v) `Φ N y' ≤ c₁ * Φ N y + c₂ * Φ N (y ∘ swap) = Φ N y`
    (`gauge_add_le` + `gauge_real_smul` + `gauge_perm`); recurse on
    `(z, y')`.
Lean pitfalls: keep `δ`, `c₂` abstract reals with the four inequalities as
`have`s; do the prefix bookkeeping with
`Finset.sum_update_of_mem`/`Finset.sum_ite_eq'`; the strong induction as
`Nat.strong_induction_on` on the card (not structural `Fin` recursion).
(e) *Fan dominance. Difficulty 2/5 given (b)–(d).*
`(∀ k, kyFanSum k A ≤ kyFanSum k B) → N A ≤ N B`:  by (b)'s representation
reduce to `Φ N (σ A) ≤ Φ N (σ B)`; `σ A` is antitone nonneg (singular values
are sorted — cite/derive `singularValues_antitone`; nonneg exists), and the
`kyFanSum` hypothesis (`kyFanSum_eq_sum_fin`) is exactly the prefix-sum
hypothesis of (d).  Comparator candidate (the package (a)–(e) is a
self-contained "UI norms via Fan dominance" Mathlib contribution).
(f) *`star` invariance. Difficulty 1/5.*  `N (A.adjoint) = N A` — from
`singularValues_adjoint` (SingularSubspace.lean, square case) + (b)'s
representation.  F4.c consumes this; it is a lemma, not an axiom.

**F3 implementation notes (v4.1, Fable — session ended before the Lean work;
all signatures below verified against the pin, ready to execute):**
- `sqrt_apply_eigenvectorBasis` (PositiveSqrt.lean:59) is **hard-coded to
  `hn := rfl`** (`Fin (finrank 𝕜 E)` indices) — start the F3.a SVD proof
  with `subst hn`, then every `rfl`-pinned lemma applies.
- Basis exchange: `OrthonormalBasis.equiv b w (Equiv.refl _)` with simp
  lemmas `equiv_apply_basis : b.equiv b' e (b i) = b' (e i)`, `equiv_symm`
  (PiL2.lean:840–856); permutation unitary for `gauge_perm` is
  `b.equiv b π`.
- Reflection: `Submodule.reflection_orthogonalComplement_singleton_eq_neg
  (v) : reflection (𝕜 ∙ v)ᗮ v = -v` and
  `reflection_mem_subspace_eq_self` for the fixed vectors; membership via
  `Submodule.mem_orthogonal_singleton_iff_inner_right` + orthonormality.
- Adjoint of a symmetric map: `LinearMap.IsSymmetric.adjoint_eq`
  (Adjoint.lean:598).
- Descent bookkeeping: `Finset.sum_update_of_mem` (additive of
  `prod_update_of_mem`, BigOperators/Group/Finset/Piecewise.lean:246;
  yields the `s \ {i}` form — `Finset.erase_eq` to convert),
  `Function.update_self` / `Function.update_of_ne` (note the argument order:
  `update_of_ne (h : a ≠ a')`), `Equiv.swap_apply_left/right/of_ne_of_ne`,
  least index via `Finset.min'` + `min'_le` / `min'_mem`, strong induction
  via `Nat.strong_induction_on` on the disagreement card.
- Fan dominance plumbing: un-`private` `sum_filter_lt_eq_sum_fin` in
  KyFan.lean (external consumer — same criterion as E3(a)); default basis
  `stdOrthonormalBasis 𝕜 E : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E`
  (PiL2.lean:1077).
- Structure: standalone + `CoeFun` (skip `extends Seminorm` for staging;
  reconsider at PR time).
- `diagOp` via the `InnerProductSpace.rankOne 𝕜 (b i) (b i)` idiom
  (IntertwiningUnitary.lean's `spectralProjection`); Gram identity
  `diagOp b x ∘ₗ diagOp b y = diagOp b (x * y)` by `b.toBasis.ext`, then
  `singularValues_diagOp` for antitone nonneg `x` via
  `eigenvalues_eq_of_eigenbasis` + `Real.sqrt_sq`.
- Descent-step arithmetic to keep abstract: `hδ₁ : δ ≤ y j − z j`,
  `hδ₂ : δ ≤ z l − y l`, `hδlt : δ < y j − y l` (from `y l < z j`),
  `c₂ * (y j − y l) = δ` via `div_mul_cancel₀`.

**F3-annex (OPTIONAL, off the critical path, Mathlib-attractive):** the
classical majorization bricks the reroute made unnecessary: (α)
weak-majorization completion (`x ≺_w y ⇒ ∃ z, x ≤ z ∧ z ≺ y`, Bhatia
II.3(i)); (β) Hardy–Littlewood–Pólya (`z ≺ y ⇒ z ∈ convexHull ℝ
{y ∘ π}`) by T-transform induction — same transform as (d) but tracking
convex-hull membership instead of a gauge, with the equal-sums balance
argument; note **Birkhoff IS in the pin** (`doublyStochastic_eq_convexHull_
permMatrix`, `Analysis/Convex/Birkhoff.lean:165`), so a doubly-stochastic
route is also open.  Since Mathlib has no majorization API at all, (α)+(β)
are a strong upstream candidate — file under `comparator/` if attempted.
Do not start before F4/G.

**F4 — UI-norm Sylvester bound and the part-III sinΘ theorem.  ✅ DONE (commits `b8de103`, `9d73132`; see the v6 revision-log entry).**
(a) *Ideal property. Difficulty 2/5.*  `N (C ∘ₗ X) ≤ c * N X` when
`∀ x, ‖C x‖ ≤ c‖x‖` (and mirrored) — Fan dominance (F3.e) applied to the
singular-value domination F0(e) (`kyFanSum_le_of_singularValues_le` exists,
KyFan.lean; mind the `c ≥ 0` side condition and the `c • B` massaging via
`kyFanSum_real_smul`).
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
relation `A∘X − X∘B = Y` — **all of that is norm-free and reusable**;
extract it as a shared `private` "setup" lemma (or inline-copy; prefer
extraction, it also de-duplicates SinThetaOpNorm.lean), then finish
with F4(b) instead of the op-norm bound, plus `N Y ≤ N (S−T)` (ideal property
twice: `Y = P ∘L (T−S) ∘L Q`, contractions on both sides) and
`N (Q∘P) = N ((P∘Q)⋆) = N (P∘Q)` — the `star` lemma is F3.f (landed).
*Coercion caveat (accepted from the Opus review):* the W5.2 setup lives at
the `→L[𝕜]` (CLM) level while `UnitarilyInvariantNorm` lives on `E →ₗ[𝕜] E`;
budget an explicit `toLinearMap`/`toContinuousLinearMap` bridging layer
(finite dimension makes it routine — `LinearMap.toContinuousLinearMap` is a
linear equiv — but it is real bookkeeping, not "verbatim" reuse).
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

**G1 — Subspace sin2Θ.  ✅ DONE (`c17998d`, route (iii) — mirror reduction; see the v7 revision-log entry).  Original difficulty 5/5; actual, given F4: ~3/5.**  Target statement (Frobenius first;
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

**G2 — Subspace tan2Θ (vanishing pinch). Difficulty 4.5/5.  Staged (v8);
G2.0 is a Fable checkpoint.**  The v7 route note stands: the G1 mirror gives
*absolute* (sine-type) bounds only; tan2Θ is *relative* — the per-vector form
already landed (`tan_two_theta_le`, spectral form
`tan_two_theta_le_of_eigenvalues`) reads
`(b−a) · cos θ(x) sin θ(x) ≤ |cos 2θ(x)| · ε` per unit `S`-eigenvector `x`,
and the `|cos 2θ|` weight does not pass through a UI norm naively.

- **G2.0 (statement gate — Fable, or Opus with a MANDATORY stop after the
  stub commit).**  Write the headline stub + cross-check paragraph from DK
  III §8 (tan 2Θ) with Stewart–Sun V.3 and Bhatia VII as secondaries, and
  `ForMathlib/prose/Davis-1963-core-arguments.tex` for the per-vector
  skeleton.  The one decision that must come from the sources: how the
  statement handles `2θᵢ ≥ π/2` (tan's pole).  Candidate shapes to weigh,
  in decreasing faithfulness-risk:
  (α) `‖tan 2Θ‖ ≤ 2‖H‖/δ` with the acute-angle convention (requires
  defining a tan2Θ diagonal operator and knowing `Θ < π/4` — determine
  whether the pinch hypotheses force it or the source assumes it);
  (β) the multiplied-out, pole-free per-angle form
  `(b−a) · 2 cᵢ sᵢ ≤ 2 ε · |cᵢ² − sᵢ²|` for each sorted principal angle
  (op-norm RHS), matching the landed per-vector shape — safest to state,
  still literature-recognizable;
  (γ) UI-norm form of (β) via majorization — only if the source actually
  states one (do not invent a UI-norm tan2Θ).
  If the sources are not reachable in-session, STOP and report.
- **G2.1 (post-gate; Opus-tractable, ~3/5).**  Block-transfer lemma: under
  the vanishing-pinch hypotheses (state subspace-wise, exactly as in
  `tan_two_theta_le_of_mem`), the diagonal blocks of `S` and `T` agree:
  `P S P = P T P` and `(1−P) S (1−P) = (1−P) T (1−P)` as operator
  identities, plus their form-level corollaries.  Independent of the gate's
  outcome; needed by every candidate.
- **G2.2 (post-gate; Fable).**  The aggregation: per-vector `key_identity`
  machinery (RotationSharp.lean) summed over an `S`-eigenbasis against the
  OP3 dictionary, or the shape the gate settles on.  Route to be written
  after G2.0 — do not pre-commit.

Descopes if blocked: (a) op-norm/largest-angle tan2Θ via the per-vector
theorem at a worst eigenvector (E2-style chaining, Opus 3/5, mirrors
`sqrt_one_sub_sq_cosPrincipalAngles_le`); (b) Frobenius-only via
eigenbasis summation.

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

*Staging protocol (v8):* G3.0 (= sub-brick (i), the statement gate) is
**Fable-only** — this is the highest statement-risk item in the plan and the
tan operator's very well-formedness is source-dependent.  After the gate:
(ii) and (iii) stay Fable (the `(P_U ι_Z)⁻¹` API and the
similar-to-symmetric Sylvester variant are both 4/5 on their own); the
`d = 1` descope is Opus-tractable now (2.5/5, per-vector machinery +
`sqrt_one_sub_sq_cosPrincipalAngles_le`-style chaining) and is a sensible
independent warm-up that de-risks the statement shape.

---

## Phase OP — Opus-ready follow-ups (v8; independent of G2/G3)

Three steps, **mutually independent**, each depending only on landed
material.  None waits on G2/G3: Opus can execute this phase first, in any
order, in parallel with Fable's Phase-G work.  House rules apply per step
(provenance header, `lake build` green, `#print axioms` on every new
headline, register any new file in `ForMathlib.lean`, paper sync, difficulty
re-rate here if reality disagrees).  No statement-first gate is needed for
OP1/OP2 (statements are determined by landed headlines); OP3 has a light
gate (commit the stub, then proceed — the route below is paper-verified).

**OP1 — Spectral (eigenvalue-hypothesis) corollaries of G1.
Difficulty 2/5.  Opus.**  In `SinTwoThetaUINorm.lean`, a `section Spectral`
at the end of the file, exactly mirroring the E3 pattern of
`SinThetaOpNorm.lean` (`norm_starProjection_comp_starProjection_le_of_eigenvalues`).
Two deliverables.

(a) Spectral form of the headline `sin_two_theta_starProjection_le`:

```lean
theorem sin_two_theta_starProjection_le_of_eigenvalues
    (N : UnitarilyInvariantNorm 𝕜 E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {s s' : Finset (Fin n)} {a b : ℝ} (hab : a < b)
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a) :
    N (((specSubspace (hT.eigenvectorBasis hn) (· ∈ s))ᗮ.starProjection ∘L
        (specSubspace (hS.eigenvectorBasis hn) (· ∈ s')).starProjection ∘L
        (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a)
```

Route: apply `sin_two_theta_starProjection_le` with
`U := specSubspace (hT.eigenvectorBasis hn) (· ∈ s)`,
`V := specSubspace (hS.eigenvectorBasis hn) (· ∈ s')`.  Discharge:
`hUinv`/`hVinv` by `map_mem_specSubspace` (CourantFischer.lean);
`hUb` by `le_re_inner_map_self_of_mem_specSubspace` fed `hb`;
`hUa`: given `x ∈ Uᗮ`, `rw [orthogonal_specSubspace] at hx` turns membership
into `specSubspace … (· ∉ s)`, then
`re_inner_map_self_le_of_mem_specSubspace` fed `ha`.  This is verbatim the
discharge pattern of `sin_two_theta_le_of_eigenvalues`
(SinThetaOpNorm.lean, `section Spectral`) — copy its `refine … fun w hw => ?_`
shape.  Note the G1 headline takes `hab : a < b` and a bare `N (S − T)` RHS
(no `ε`-form — UI norms consume the operator directly, unlike E3's op-norm
`hε` phrasing).

(b) Spectral form of `sin_two_theta_reflection_le` (mirror-defect version —
no second operator `S` at all): same `U`, arbitrary `W : Submodule 𝕜 E`,
conclusion
`2 * N ↑(…ᗮ.sP ∘L W.sP ∘L ….sP) ≤ N (W.reflection ∘ₗ T ∘ₗ W.reflection − T) / (b − a)`
with only `hb`/`ha` to discharge.  Trivial once (a) compiles.

Pitfalls: the `HasOrthogonalProjection` instances are found automatically
(finite dimension); the predicate produced by `orthogonal_specSubspace` is
`fun i => ¬ (i ∈ s)` — defeq to `(· ∉ s)`, no rewriting needed beyond the E3
precedent.  Keep the statement's coercion shape identical to the G1 headline
(`(… : E →L[𝕜] E) : E →ₗ[𝕜] E`) or `exact` will fail on coercion mismatch.

**OP2 — The Frobenius `UnitarilyInvariantNorm` instance.
Difficulty 2.5/5.  Opus.**  In `UnitarilyInvariantNorm.lean` (new final
section `section Frobenius`) or a small new file — prefer the former (single
import site, mirrors `opNorm`'s placement in SinThetaUINorm.lean only
because F4 needed it there; Frobenius needs nothing from F4).  Define via
the **basis sum, not singular values** (this makes `add_le'`/`smul'` easy
and avoids the complex-scalar trap in `smul'` — `singularValues_real_smul`
only covers `0 ≤ r : ℝ`, but `smul'` quantifies over all `a : 𝕜`):

```lean
noncomputable def frobenius (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    UnitarilyInvariantNorm 𝕜 E where
  toFun A := Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
  ...
```

Field routes:
- `smul'`: pointwise `norm_smul`, then
  `mul_pow`, `← Finset.mul_sum`, `Real.sqrt_mul (sq_nonneg ‖a‖)`,
  `Real.sqrt_sq (norm_nonneg a)`.
- `add_le'` (Minkowski): package the coordinate-norm vectors as
  `x y : EuclideanSpace ℝ (Fin m)` (`x i := ‖A (b i)‖` etc.) so that the
  goal is `‖z‖ ≤ ‖x‖ + ‖y‖`-shaped under `EuclideanSpace.norm_eq`
  (mind `‖x i‖ = |x i|`: bridge with `Real.norm_eq_abs`, `sq_abs`).
  Two steps: (i) a small monotonicity fact — for coordinatewise
  `0 ≤ v ≤ w`, `√(∑ v i²) ≤ √(∑ w i²)` by `Real.sqrt_le_sqrt`,
  `Finset.sum_le_sum`, `pow_le_pow_left₀` — applied to
  `‖(A+B)(b i)‖ ≤ ‖A (b i)‖ + ‖B (b i)‖`; (ii) `norm_add_le x y` in
  `EuclideanSpace ℝ (Fin m)`.  (Check first whether the pin already has a
  coordinatewise-monotonicity lemma for `EuclideanSpace` norms — grep from a
  healthy shell — else inline it; it is 5 lines.)
- `invariant'`: already fully stocked.  Left factor: `U` is a linear
  isometry equiv, so `‖U (A (V (b i)))‖ = ‖A (V (b i))‖` by
  `LinearIsometryEquiv.norm_map` under the sum.  Right factor: this is
  **exactly** `sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)`
  (SingularSubspace.lean:194).  Two rewrites total.

Deliverables beyond the instance:
(a) basis-independence bridge, stated for any orthonormal basis:

```lean
theorem frobenius_apply (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius 𝕜 E A = Real.sqrt (∑ k, ‖A (b k)‖ ^ 2)
```

via `sum_sq_singularValues A hn b` and `sum_sq_singularValues A rfl
(stdOrthonormalBasis 𝕜 E)` — the two sums share the singular-value middle
term.  (Mind the index bookkeeping: the `stdOrthonormalBasis` sum runs over
`Fin (finrank 𝕜 E)`; instantiate `sum_sq_singularValues` at `n := finrank 𝕜 E`,
`hn := rfl` for that side.)  Also state the squared form
(`(frobenius 𝕜 E A)^2 = ∑ …` via `Real.sq_sqrt` on a nonneg sum) — that is
the vocabulary the paper's `…_hilbertSchmidt` theorems use
(`DavisKahan.lean` measures `‖S−T‖²_F` as an eigenbasis column sum, which is
`frobenius_apply` at `b := hS.eigenvectorBasis hn`).
(b) Two named instantiation corollaries, in the files of their parents:
the Frobenius part-III sinΘ (`apply_starProjection_comp_starProjection_le`
at `N := frobenius 𝕜 E`, SinThetaUINorm.lean) and the Frobenius subspace
sin2Θ (`sin_two_theta_starProjection_le` at `N := frobenius 𝕜 E`,
SinTwoThetaUINorm.lean), each with the LHS/RHS unfolded through
`frobenius_apply` so the statements read `√(∑ ‖…(b k)‖²) ≤ √(∑ ‖(S−T)(b k)‖²) / gap`
— the literature-facing Frobenius vocabulary.  One-liners given (a).
Paper sync: the dictionary table gains the row "‖·‖_F is a
`UnitarilyInvariantNorm`; part-III sinΘ and sin2Θ instantiate to Frobenius".

**OP3 — sin 2Θ dictionary certification: `σᵢ(Q P̂ P) = cos θᵢ · sin θᵢ`.
Difficulty 3/5.  Opus (route is Fable-verified; light statement gate).**
This certifies that the G1 LHS *is* `½ sin 2Θ`: the E2-analogue at the
full singular-value (hence every-UI-norm) level rather than op-norm.  In
`PrincipalAngles.lean` (it consumes the aligned-basis machinery and
`cosPrincipalAngles`; import `UnitarilyInvariantNorm.lean` for `diagOp` —
check for an import cycle first; if one appears, the new lemmas go in
`SinTwoThetaUINorm.lean` instead, which already sees both).

Setting: orthonormal families `u v : Fin d → E`, `U := span (range u)`,
`V := span (range v)`, `P := U.starProjection`, `P̂ := V.starProjection`,
`Q := Uᗮ.starProjection`, `M := Q ∘L P̂ ∘L P` (the G1 LHS with these `U, V`),
`c i := cosPrincipalAngles hv hu i` (mind the argument order/`comm` lemma).
Target headline (state with `√(1 − c i ^2)` for the sine, per the E2
precedent `sqrt_one_sub_sq_cosPrincipalAngles_le` — no `arccos`):

```lean
theorem apply_orthogonal_starProjection_comp_le … :
    N ((M : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = N (diagOp bE fun i => if h : (i : ℕ) < d then
          c ⟨i, h⟩ * Real.sqrt (1 - c ⟨i, h⟩ ^ 2) else 0)
```

for every `N : UnitarilyInvariantNorm 𝕜 E`, where `bE` is an orthonormal
basis of `E` extending `u` (see (a)).  Corollary: `2 • M` version (the
literal `sin 2Θ` operator, `2 c s = sin 2θ`), chained with G1 into
`N (sin2Θ-diagonal) ≤ 2 N (S − T) / (b − a)`.

Paper-verified route (gram diagonalization — no sorting, no multiplicity
bookkeeping, that is why this dropped from 3.5/5 to 3/5):
(a) *Extended basis.* Extend `u` to an orthonormal basis `bE` of `E`
    (grep the pin from a healthy shell for
    `exists_orthonormalBasis_extension`-shaped lemmas; fallback: an
    orthonormal basis of `Uᗮ` plus `u` glued along
    `Fin d ⊕ Fin (n − d) ≃ Fin n` — the E-phase `blockFamily` idiom in
    reverse).  Only the properties `bE i = u i` for `i < d` and
    `bE j ∈ Uᗮ` for `j ≥ d` are consumed.
(b) *Aligned family.* Replace `v` by the aligned orthonormal family `ṽ` of
    `AlignedBasis.lean` (`inner_u_aligned_eq`: `⟪u i, ṽ j⟫ = δᵢⱼ c i`);
    pre-check that its span is all of `V` (`familyIsometry_mem_span` +
    dimension count; if the file only gives `⊆`, add the equality lemma —
    5 lines).  `P̂` expands over `ṽ` by
    `Orthonormal.starProjection_span_image_apply`.
(c) *Action formulas.* `M (u i) = c i • (ṽ i − c i • u i)` and `M x = 0`
    for `x ∈ Uᗮ`.  From the alignment: `P̂ (u i) = c i • ṽ i`,
    `P (ṽ i) = c i • u i`, and `ṽ i − c i • u i ∈ Uᗮ`
    (inner against every `u j` vanishes: `δᵢⱼ c i − c i δᵢⱼ`).
(d) *Gram is diagonal in `bE`.* `M.adjoint ∘ₗ M` fixes each `u i` up to the
    scalar `c i ^ 2 * (1 − c i ^ 2)` and kills `Uᗮ`: from (c),
    `Q (M (u i)) = M (u i)`, `P̂ (ṽ i − c i • u i) = (1 − c i ^2) • ṽ i`,
    `P ((1 − c i ^2) • ṽ i) = (1 − c i ^2) c i • u i`.  Meanwhile
    `gram (diagOp bE w) = diagOp bE (w ^ 2)` by `adjoint_diagOp` +
    `diagOp_comp`.  Conclude `M.adjoint ∘ₗ M = gram (diagOp bE w)` for
    `w i := if … then c i √(1 − c i²) else 0` by `LinearMap.ext` on `bE`
    (`OrthonormalBasis` spans; `sq_sqrt` needs `0 ≤ 1 − c i ^2`, i.e.
    `cosPrincipalAngles_le_one`).
(e) *Conclude.* `singularValues_eq_of_gram_eq` (KyFan.lean:58) gives
    `σ(M) = σ(diagOp bE w)`; then `apply_eq_gauge` twice (same `bE`) turns
    equal singular values into equal `N`-values — the headline.  The
    op-norm instance at `N := opNorm 𝕜 E` recovers (and strengthens) the
    E2 certification; cross-reference
    `norm_orthogonal_starProjection_comp_starProjection` in the docstring.

Light gate: commit the stub of the headline plus a two-sentence docstring
cross-check ("the CS-decomposition lower-left block is `S C`, singular
values `sin θᵢ cos θᵢ`" — Bhatia VII.1, DK III §8) before proving; no
pause needed after the stub since the route is verified.  Pitfalls: `M` is
`E →L[𝕜] E` but `adjoint`/`gram` live on `E →ₗ[𝕜] E` — do (c)/(d) entirely
at the LinearMap level (coerce once, at the start); `starProjection` of a
span expands only through the `Orthonormal.…span_image_apply` route seen in
`norm_orthogonal_starProjection_comp_starProjection`'s proof — do not
unfold `starProjection` itself.

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
E3, E4, E5 (parallel)  │  [Batch 1: dictionary ✅ DONE (v2)]
                       ▼
F0 ─→ F1.a → F1.b → F1.c ─→ F2      [Batch 2: Ky Fan ✅ DONE (199390a)]
F3.a → F3.b → F3.c → F3.d ─→ F3.e → F3.f   [Batch 3: Fan dominance ✅ DONE
                                            (7481732)]
F0.e/F3.e → F4.a → F4.b → F4.c       [Batch 4: part-III sinΘ ✅ DONE (b8de103)]
F4 ─→ G1 ✅ (c17998d)                    [Batch 5: sin2Θ ✅ DONE]

── remaining (v8) ──────────────────────────────────────────────
OP1, OP2, OP3 (parallel, Opus, no unmet deps — can start NOW)
G2.1 block-transfer (Opus, anytime — gate-independent)
G2.0 gate (Fable) ─→ G2.2 (Fable)
G3.0 gate (Fable) ─→ G3.(ii),(iii) (Fable);  G3 d=1 descope (Opus, anytime)
(F3-annex: optional, anytime)
```

The only cross-phase edges worth noting: OP2 before OP1 lets OP1's docstring
cite the Frobenius instantiation, and OP3's headline chains with G1 into the
certified `sin 2Θ` bound — but neither is a hard dependency.  All five
remaining Opus items (OP1, OP2, OP3, G2.1, G3-d=1) are independently
startable now; nothing Opus-assigned waits on any Fable item.

Each batch ends: `lake build` green, axiom check, golf pass, paper sync
(move items out of §"What remains", extend the dictionary tables, update the
permalink), comparator candidates filed (F1.b, F2 triangle, F3.e, F3 package,
F4.c; E2 and F0.d are also upstream-attractive).

## Difficulty ranking (hardest first)

Numbering per the v4 F3 body (descent = F3.d, dominance = F3.e, star = F3.f;
old completion/HLP rows moved to the annex).

| Rank | Step | What | Difficulty | Assignee |
|------|------|------|-----------|----------|
| 1 | G3 | Subspace tanΘ (graph operator, similar-to-symmetric Sylvester) | 5/5 | **Fable**; statement-risk; d=1 descope → Opus 2.5/5 |
| 2 | G1 | Subspace sin2Θ (mirror reduction to F4.c) | 5/5→3/5 | ✅ DONE (Fable, `c17998d`) |
| 3 | G2 | Subspace tan2Θ (staged: G2.0 gate + G2.2 Fable; G2.1 Opus 3/5) | 4.5/5 | **Fable** + Opus sub-brick |
| 4 | F3.d | T-transform descent on the gauge (v4 crux) | 4/5 | ✅ DONE (Fable, `7481732`) |
| 5 | F3.a | `diagOp` + operator SVD factorization | 3.5/5 | ✅ DONE (Fable, `7481732`) |
| 6 | F4.c | Part-III sinΘ, every UI norm (+ CLM↔LinearMap bridge) | 3/5 | ✅ DONE (Opus, `b8de103`) |
| 7 | F3.b | UI-norm structure + gauge + invariance package | 2.5/5 | ✅ DONE (Fable, `7481732`) |
| 8 | F3.c | Gauge update bound + coordinatewise monotonicity | 2.5/5 | ✅ DONE (Fable, `7481732`) |
| 9 | F4.b | Abstract-norm Sylvester bound | 2.5/5 | ✅ DONE (Opus, `b8de103`) |
| 10 | F4.a | Ideal property | 2/5 | ✅ DONE (Opus, `b8de103`) |
| 11 | F3.e | Fan dominance assembly | 2/5 | ✅ DONE (Fable, `7481732`) |
| 12 | F3.f | `star` invariance | 1/5 | ✅ DONE (Fable, `7481732`) |
| — | annex α | Weak-majorization completion (optional) | 2.5/5 | either, after F4 |
| — | annex β | Hardy–Littlewood–Pólya (optional) | 4/5 | Fable, after F4 |
| — | OP3 | sin 2Θ dictionary certification `σᵢ(QP̂P) = cᵢsᵢ` (routed v8) | 3.5/5→3/5 | Opus, start anytime |
| — | OP2 | Frobenius `UnitarilyInvariantNorm` instance (routed v8) | 2.5/5 | Opus, start anytime |
| — | OP1 | Spectral (eigenvalue-hypothesis) corollaries of G1 (routed v8) | 2/5 | Opus, start anytime |

Completed (for the record): E1 2/5, E2 3.5/5, E3 2.5/5, E4 2.5/5, E5 1/5
(v2); F0 2.5/5, F1.a 2/5, F1.b 3/5, F1.c 3.5/5, F2 2/5 (`199390a`).

## Definition of done (overall)

- Phases E–F complete ⇒ the paper's §"What remains" reduces to the three
  Phase-G theorems and the Phase-H notes; part-III sinΘ (every UI norm,
  Frobenius and op-norm as instances) is the new headline.
- Phase OP complete ⇒ every landed subspace theorem speaks the literature's
  language: eigenvalue-hypothesis forms for sin2Θ, the Frobenius norm as a
  first-class `UnitarilyInvariantNorm` instance, and the G1 LHS certified as
  `½ sin 2Θ` in every UI norm.
- Phase G complete ⇒ the DK III quartet is formalized at the subspace level;
  the paper's gap list reduces to Phase H (documented as out of scope).
- Every batch: statement-first gates honored where mandated; new files carry
  provenance headers and are registered in `ForMathlib.lean`; difficulty
  re-rated in this file when reality disagrees with the estimate.
awk: /tmp/claude-1285606669/-home-local-KHQ-edward-wang-code-aiq-eval-runner/3a364666-2629-4e42-a88e-f7263db90bc0/scratchpad/flags.awk:21: (FILENAME=dev/davis-kahan-expert-completion-plan.md FNR=696) warning: close of fd 3 (`dev/davis-kahan-expert-completion-plan.md') failed: Bad file descriptor
