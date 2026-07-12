# Lean proof-engineering lessons from the Davis–Kahan development

This is the durable troubleshooting reference for Lean-specific failures found
while building the finite-dimensional Davis–Kahan theory. Read it before a
substantial proof wave in `ForMathlib/Analysis/InnerProductSpace/`, and search it
when a mathematically straightforward proof fails for representation,
elaboration, or parser reasons.

The common theme is simple: first make the goal and the theorem agree
*syntactically*, then apply the mathematics. Bundled maps, coercions, semilinear
scalars, adjoints, and dependent branches often hide the expression that a
rewrite or theorem application expects.

## Fast diagnostic order

When a short proof unexpectedly fails:

1. inspect the exact goal and the exact theorem type;
2. identify the representation Lean is displaying;
3. use `change` to expose the intended expression;
4. prove a small bridge equality in that representation;
5. use `calc` or the exact theorem rather than a broad `simpa`;
6. normalize only the final coercion, scalar, or equality orientation;
7. if the goal contains an unexpected placeholder, inspect the elaboration of
   the earlier definition before debugging the downstream theorem.

Prefer the actual pinned Mathlib checkout under `.lake/packages/mathlib/Mathlib`
to remembered theorem names. Fully qualify fragile namespace-sensitive names.

## 1. Normalize bundled composition before rewriting pointwise identities

A target such as

```lean
(J ∘ₗ B ∘ₗ J) x = B x
```

does not syntactically contain `J (B (J x))` for `rw` to match. Expose the
pointwise expression first:

```lean
change J (B (J x)) = B x
```

Alternatively unfold composition application explicitly. Do not expect `rw` to
look through bundled `LinearMap.comp` on its own.

## 2. Match the projection representation in the goal

A reduction theorem may use a local `projection V`, while simplification exposes
`V.starProjection`. Even when they are definitionally related, rewriting can
fail because the displayed terms differ.

Prove a bridge in the representation appearing in the goal:

```lean
have hproj :
    V.starProjection (B x) = B (V.starProjection x) := by
  change projection V (B x) = B (projection V x)
  exact projection_apply_comm_of_reduces hB hV x
```

Then rewrite with `hproj`. The same technique applies whenever coercions or
bundled projection APIs disagree syntactically.

## 3. Normalize `RingHom.id` explicitly

Scalar-linearity goals may expose

```lean
(RingHom.id 𝕜) c
```

where ordinary linear notation suggests just `c`. `ring` and broad automation
need not remove it. Include

```lean
RingHom.id_apply
```

explicitly in the final normalization. Semilinear map fields often reveal the
ring homomorphism that ordinary notation hides.

## 4. Match `starRingEnd` exactly in semilinear arguments

Adjoint and semilinear APIs may produce the scalar

```lean
(starRingEnd 𝕜) a
```

rather than `star a`. Use the exact expression expected by the theorem:

```lean
N.smul_eq ((starRingEnd 𝕜) a) A.adjoint
```

Then prove the norm equality separately:

```lean
change ‖star a‖ = ‖a‖
exact norm_star a
```

Do not rely on one `simpa [norm_star]` to reconcile both the semilinear scalar
and its norm.

## 5. Check the direction of reassociation

For an expression such as

```lean
((V.symm ∘ₗ A.adjoint) ∘ₗ U.symm)
```

`LinearMap.comp_assoc` only rewrites when its chosen orientation matches the
actual association in the target. Inspect the target before choosing the rewrite
direction. A `change` or short `calc` is usually more robust than repeatedly
reversing associativity lemmas.

## 6. A noncomputable dependent `if` still needs decidability

A definition such as

```lean
if h : Function.Bijective (...) then ... else ...
```

still requires a `Decidable` instance for the proposition. Marking the
definition `noncomputable` is not sufficient. Without `classical`, elaboration
can leave an unintended placeholder in the definition body, and a later theorem
may appear to ask for an equality between that placeholder and the intended
inverse.

Use:

```lean
noncomputable def ... := by
  classical
  exact if h : Function.Bijective ... then ... else 0
```

Also introduce `classical` in lemmas that unfold or reduce this dependent branch.
If a downstream goal exposes an unexpected placeholder, inspect earlier
elaboration and typeclass errors first.

## 7. Qualify inner-product-space basis extensionality

The available theorem in the relevant import context was

```lean
InnerProductSpace.ext_inner_right_basis
```

not an unqualified `ext_inner_right_basis`. Prefer the fully qualified name for
namespace-sensitive basis APIs.

A failed tactic may also cause the next tactic to report `No goals to be solved`.
Treat that message as a likely cascade from the first failure rather than an
independent problem.

## 8. Check the orientation of Parseval equalities

For example,

```lean
OrthonormalBasis.sum_sq_norm_inner_right ...
```

returns an equality of the form

```lean
∑ i, ‖⟪e i, x⟫‖ ^ 2 = ‖x‖ ^ 2
```

while a proof may need the reverse orientation. Use `.symm` explicitly. Do not
expect `simpa` to reverse an equality merely because all other terms match.

## 9. Handle subsingleton vector spaces by substituting the vector

Broad simplification of zero maps in a `Subsingleton E` branch can leave goals
such as

```text
0 = 0 0
```

because zero is overloaded between maps, functions, and values. Substitute the
input instead:

```lean
have hx : x = 0 := Subsingleton.elim _ _
subst x
simp
```

To prove an entire map is zero, use extensionality and apply this argument to
each input instead of depending on global simplification.

## 10. Construct `NeZero` from a nonzero proof, not positivity directly

`NeZero n` expects `n ≠ 0`. `Module.finrank_pos` provides
`0 < Module.finrank 𝕜 E`, so convert it:

```lean
letI : NeZero (Module.finrank 𝕜 E) :=
  ⟨Nat.ne_of_gt Module.finrank_pos⟩
```

Install this instance before invoking APIs indexed by
`Fin (Module.finrank 𝕜 E)` that require nonzero dimension.

## 11. Taking adjoints does not automatically use self-adjointness

After

```lean
congrArg LinearMap.adjoint hEq
```

the result contains `A.adjoint` and `B.adjoint`, even when hypotheses say that
`A` and `B` are symmetric. Rewrite explicitly with facts such as

```lean
hA.adjoint_eq
hB.adjoint_eq
```

Do not expect simplification to discover and apply those hypotheses
unprompted.

## 12. Build reverse Sylvester equations from the exact adjointed form

Adjointing

```lean
A ∘ₗ X - X ∘ₗ B = C
```

naturally gives

```lean
X.adjoint ∘ₗ A.adjoint -
  B.adjoint ∘ₗ X.adjoint =
  C.adjoint
```

because adjoints reverse composition. Start from this exact equation, then
rewrite self-adjoint operators and arrange the desired reverse orientation.
Trying to force the original orientation through a single `simpa` is fragile.

## 13. Do not stack declaration doc comments

Two adjacent declaration comments

```lean
/-- First note. -/
/-- Second note. -/
lemma ...
```

can be a syntax error because the parser expects the declaration after the first
doc comment. Merge the notes into one `/-- ... -/` block, or make non-API
strategy notes ordinary block comments:

```lean
/- Implementation note. -/
```

## 14. Keep comments outside declaration syntax

Do not insert a strategy comment between a theorem header and its `:= by` body.
Place the comment before the declaration or fold it into the declaration's
single docstring.

For comment-only edits, a useful safety check is that stripping comments leaves
the same normalized token stream. Always compile or at least parse the touched
modules after moving declaration comments.

## 15. Prefer explicit representation bridges to broad `simpa`

One-line `simpa` proofs become fragile when they cross several of these at once:

- coercions between bundled maps and functions;
- semilinear scalar actions;
- adjoints;
- composition reassociation;
- projection implementations;
- equality orientation.

Use this order instead:

1. `change` the target to the intended representation;
2. state a small bridge equality;
3. use `calc` if more than one representation changes;
4. apply the exact mathematical theorem;
5. simplify only the remaining scalar or coercion detail.

A few explicit lines are preferable to a broad simplifier call whose success
depends on incidental simp lemmas.

## 16. Use precise language for coercion and lifting

Notation such as `↑A` usually forgets bundled structure:

```text
ContinuousLinearMap → LinearMap → function
```

Call this “coercing to the underlying linear map” or “forgetting the continuous
structure.” It is not a mathematical lift. Precise terminology helps identify
which representation Lean currently sees and which API should apply.

## 17. Design total inverse-like APIs before filling their definitions

Tangent embeddings, graph operators, resolvents, and related constructions may
only exist under invertibility or transversality hypotheses. Before implementing
a total definition, decide which API is intended:

- a proof-carrying construction;
- an `if`-totalized construction, often zero outside the valid branch;
- a generalized inverse;
- a partial structure.

Do not insert an arbitrary inverse just to close an implementation hole. For an
`if`-totalized construction, provide computation lemmas for the valid branch and
make the invalid branch explicit in the API.

## 18. Search for an abstraction-level reduction before coordinates

The ordered all-unitarily-invariant Sylvester estimate did not require full
rectangular Fan dominance. The successful route was to generalize an existing
square absorption theorem to rectangular maps, derive quadratic-form bounds from
spectral extremal information, and transport the reverse orientation by
adjoints.

Before starting an SVD, matrix-coordinate, or large basis expansion proof, check
whether the target follows from:

- an existing square theorem generalized to rectangular maps;
- adjoint transport;
- extremal spectral quadratic-form bounds;
- finite-dimensional injective/surjective equivalence;
- an existing left/right operator-ideal inequality.

Do not force an abstraction that does not fit its exact assumptions, but verify
these routes before committing to coordinates.


## 19. Normalize bundled-map goals before applying pointwise vector lemmas

A theorem about vectors will not rewrite a goal whose outer syntax is still a
bundled linear-map application.  For example, after rewriting an operator
identity, Lean may retain

```lean
‖(S + T) x‖ ^ 2
```

rather than exposing `‖S x + T x‖ ^ 2`.  Before applying Pythagoras or another
vector theorem, normalize only the application layer:

```lean
simp only [LinearMap.add_apply, LinearMap.comp_apply]
```

Then apply the theorem directly, preferably with `simpa [pow_two, ...] using`
rather than asking `rw` to discover a deeply nested norm pattern.  The same
principle applies to subtraction, scalar multiplication, and composition.

For algebraic operator decompositions, move to the pointwise identity first,
rewrite linearity explicitly (`map_sub`, `map_add`), and only then use `abel` or
`ring`.  Algebraic tactics do not automatically know that an opaque bundled map
preserves subtraction.

## 20. Read the target after rewriting `ker_eq_bot`

For linear maps, rewriting with `LinearMap.ker_eq_bot` commonly changes the
goal into `Function.Injective f`.  The next introduction therefore produces two
vectors and an equality, not one vector and a kernel-membership hypothesis.
A proof written as though the old kernel goal remained will fail in a confusing
way when an injectivity theorem is applied to the wrong target.

For subspace transversality, a robust route is:

1. introduce `x`, `y`, and `hxy : f x = f y`;
2. apply the geometric hypothesis to `x - y`;
3. express the projected-difference goal as `f (x - y) = 0` with `change`;
4. close it by linearity and `hxy`;
5. use injectivity of the coordinate isometry to conclude `x - y = 0`.

This avoids depending on the exact statement shape chosen by the kernel API.

## 21. Name adjoint and isometry inner-product bridges explicitly

Rewriting `X.inner_map_map` can fail when the target displays
`X.toLinearMap` rather than the isometry coercion `X`.  Similarly, a broad
rewrite with an adjoint identity may hit the wrong occurrence or orientation.
When a projection proof depends on both facts, state the scalar equalities
separately:

```lean
have hfirst : ⟪y, X z⟫ = ⟪X.toLinearMap.adjoint y, z⟫ :=
  (LinearMap.adjoint_inner_left X.toLinearMap z y).symm
have hsecond : ⟪X (X.toLinearMap.adjoint y), X z⟫ =
    ⟪X.toLinearMap.adjoint y, z⟫ :=
  X.inner_map_map _ _
```

Do not immediately `rw` by those facts if the goal still prints
`X.toLinearMap`: rewriting matches syntax before it performs the coercion
normalization one might expect.  Instead, use a typed `calc`, keep the target in
its displayed `X.toLinearMap` form, and use `change` only inside the step proved
by `X.inner_map_map`.  This makes the coercion crossing explicit and local.

The same rule applies to norms.  A Pythagorean theorem in the codomain yields a
term such as `‖X d‖ ^ 2`, whereas the desired Frobenius summand may be
`‖d‖ ^ 2`.  First apply Pythagoras without broad simplification, then rewrite
that one norm with `X.norm_map` in a separate `calc` step.  Asking `simpa` to do
both the square normalization and the isometry transport can leave universe-
indexed norm instances syntactically different even though the values are
mathematically equal.

## Toolchain and verification discipline

The repository currently targets approximately:

```text
Lean 4.32.0-rc1
Mathlib 4efb186f102ebfd2eea1545c151d6fbcfdff0e43
```

Before attempting to bootstrap anything, check whether the mounted repository
already has a usable toolchain and dependency cache:

```bash
which lake
which lean
lake --version
lean --version
ls -la .lake/packages/mathlib
```

If the pinned environment is available, use it. If it is not, do not spend a
proof wave on an uncertain installation unless toolchain setup is the task.
Source-audit a small coherent change and state clearly that local compilation
was unavailable. Never claim a local build without an actual successful log.

A mathematically plausible source edit is not complete until Lean accepts it.
Warnings about unfinished declarations or style are not the same as proof
failures, but never describe a theorem as complete based only on source review.

When the local pinned toolchain is available, inspect exact dependency source
under `.lake/packages/mathlib/Mathlib` and run the narrowest relevant build. If
it is unavailable, state that plainly and package small coherent waves for the
user's compiler loop.

After resolving a new non-obvious failure, add it here when it is a reusable
proof-engineering rule. Use `dev/journals/` instead when the value lies in the
specific debugging symptom and postmortem; promote only the durable rule into
this reference.

## 22. Audit every bundled-map occurrence, then verify the packaged file

A coercion failure fixed in one theorem is evidence that the same syntactic
pattern may recur earlier in the file.  In particular, lemmas stated for a
`LinearIsometry` such as

```lean
X.inner_map_map
X.norm_map
```

do not reliably rewrite expressions printed through `X.toLinearMap`.  After the
first such failure, search the whole authored diff for both forms and normalize
every theorem boundary deliberately:

```lean
change ⟪X x, X y⟫ = ⟪x, y⟫
exact X.inner_map_map x y
```

For residual and projection identities, prefer scalar equalities assembled by
`calc` or transitivity over a chain of broad rewrites.  For an isometric norm
transport, first prove the Pythagorean identity wholly in the codomain and only
then replace `‖X d‖` by `‖d‖`; do not ask one `simpa` to cross bundled coercions,
powers, and universe-indexed norm instances simultaneously.

A cumulative overlay is only trustworthy if the artifact contains the same
file that was reviewed.  Before delivery:

1. generate the patch from the clean committed baseline, not from a prior
   staging directory;
2. extract the ZIP and apply the patch independently to two clean copies;
3. compare every authored file byte-for-byte with the work tree;
4. inspect the exact formerly failing line ranges in both validation copies.

This catches the particularly costly failure mode where the work tree is fixed
but the packaged overlay still contains an older staged copy.

## 23. Put command modifiers before declaration documentation

Lean command modifiers such as

```lean
omit [FiniteDimensional 𝕜 E] in
```

must precede the declaration documentation as well as the declaration itself:

```lean
omit [FiniteDimensional 𝕜 E] in
/-- Documentation for the theorem. -/
theorem theorem_name ... := by
  ...
```

Do not place `omit ... in` between a docstring and its theorem. A documentation
comment is attached to the immediately following declaration command, so Lean
will parse the intervening `omit` where it is expecting `theorem`, `lemma`, or
another declaration and report an error such as `unexpected token 'omit';
expected 'lemma'`.

When cleaning unused-section-variable warnings, inspect the surrounding
comments before inserting a command modifier. Prefer leaving a harmless linter
warning over introducing an unparsed declaration header, and include the
modified file in the narrow compiler target whenever a toolchain is available.

## 24. Put the `sorry` at the weakest analytic seam, then close every transport layer

When a theorem family has one genuinely hard analytic ingredient and several
formal transport steps, do not leave a `sorry` in every public theorem. Isolate
the hard statement at the weakest reusable level and prove the rest from it.

For the arbitrary-disjoint-spectrum Davis--Kahan branch, first isolate the
simultaneous Ky Fan prefix estimate rather than postulating an arbitrary
unitarily invariant norm theorem.  Then push the root one step lower whenever
a common constructive certificate exists.  The final root is now:

```lean
sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
```

It constructs an exact finite unitary-orbit representation for `δ • X` with
coefficient mass at most `π / 2`.  The Ky Fan theorem

```lean
kyFan_sylvester_le_of_spectralDistance
```

is a proved finite-sum consequence, rectangular Fan dominance proves

```lean
uiNorm_sylvester_le_of_spectralDistance
```

and the residual and perturbation `sin Θ` theorems remain ordinary transport
proofs. This factoring has several benefits:

1. the remaining mathematics is visible in one constructive declaration;
2. a future Fourier, contour, or Schur-multiplier implementation can replace
   that declaration without changing downstream APIs;
3. Ky Fan subadditivity and the existing Fan-dominance theorem are exercised
   rather than duplicated;
4. the certificate simultaneously supports every rectangular UI seminorm;
5. documentation can state precisely which part is scaffolded and which part
   is formally proved.

Before opening the analytic proof, complete and name the deterministic
coordinate facts:

```lean
sylvesterReciprocalKernel
sylvester_eigenvalue_sub_ne_zero
sylvester_eigenbasis_coefficient_equation
```

Then prove all downstream scale, projection, restriction, and isometry
transports immediately. A scaffold is most useful when it reduces the future
agent's task to one theorem, not when it merely creates a longer list of
independent `sorry`s.

For positive scalar scaling under Fan dominance, compare the scaled operators
rather than manipulating the abstract norm inequality directly:

```lean
N ((δ : 𝕜) • X) ≤ N (((Real.pi / 2 : ℝ) : 𝕜) • C)
```

Prove every Ky Fan prefix inequality for those scaled maps, apply
`apply_le_of_kyFanSum_le`, and only then rewrite abstract homogeneity. This keeps
nonnegativity and absolute-value normalization local and avoids division in the
main proof.

Finally, keep status documents honest. A downstream theorem whose proof uses an
upstream declaration containing `sorry` is structurally wired but not a closed
formalization. Name the exact analytic root in the literature comparison and in
handoff documents until its `sorry` is removed.

## 25. Reduce integral norm estimates to exact finite orbit certificates

For finite-dimensional unitarily invariant norm arguments, an integral
representation is often not the best public theorem boundary.  Instead, isolate
an exact finite certificate:

```lean
X = ∑ i, a i • (U i ∘ C ∘ V i)
∑ i, ‖a i‖ ≤ mass
```

with unitary `U i` and `V i`.  Subadditivity, absolute homogeneity, and unitary
invariance then prove every UI-norm estimate by a short reusable theorem.  This
has three advantages:

1. the analytic proof no longer needs to know about Ky Fan norms or Fan
   dominance;
2. the norm layer no longer needs Bochner integration or measure theory;
3. the same certificate proves all rectangular UI seminorm bounds at once.

For the arbitrary-spectrum `π/2` Sylvester theorem, the intended analytic route
is:

1. represent `δ / s` on `|s| ≥ δ` by a Fourier measure of total variation at
   most `π / 2`;
2. integrate the two-sided unitary orbit of the defect;
3. absorb the phase of the measure into one unitary factor;
4. normalize the variation measure to obtain a barycenter;
5. use finite-dimensional Carathéodory to replace the barycenter by an exact
   finite convex combination.

This moves the sole `sorry` to the constructive certificate theorem while the
Ky Fan and arbitrary-UI-norm theorems become proved algebraic corollaries.

## 26. Every new analytic seam needs an executable proof-strategy comment

When adding a definition or theorem to a difficult formalization front, the
comment must do more than paraphrase the statement.  Include:

1. the mathematical construction or identity;
2. the intended Lean decomposition into named helper theorems;
3. the downstream theorem unlocked by the seam;
4. exceptional cases such as zero mass, zero-dimensional spaces, or real versus
   complex scalars.

For open theorems, the comment should be detailed enough that a weaker agent can
continue without reconstructing the literature argument.  For proved helper
theorems, state why the chosen theorem boundary avoids fragile coercions,
unnecessary integration APIs, or duplicated norm-specific reasoning.

Treat these comments as part of the formalization interface.  Whenever the
proof architecture changes, update the comments, the dedicated roadmap, and
the formalization-versus-literature document in the same overlay.

## 27. Treat parser failures as possible causes of later missing-declaration errors

A malformed notation occurrence can prevent Lean from registering the entire
following declaration.  Errors such as

```text
Invalid field `sum_le`: the environment does not contain ...sum_le
```

may therefore be cascading errors rather than independent API failures.  Fix
the first parser error and rebuild before replacing downstream field notation.

For finite-set sums in this codebase, use the supported binder spelling

```lean
∑ i ∈ s, f i
```

rather than the unsupported `∑ i in s, f i` form.  When introducing a helper
that will immediately be used by dot notation, inspect the exact source around
both the declaration and its first call so a parse failure is not mistaken for
a missing theorem.

## 28. Prefer typed `calc` chains for homogeneity bridges

When a certificate theorem controls a scaled map such as `((δ : 𝕜) • X)`, do
not rewrite a previously inferred inequality in place and hope coercion
normalization produces the desired scalar form.  State the bridge explicitly:

```lean
calc
  δ * K X = K (((δ : 𝕜)) • X) := (K_real_smul ...).symm
  _ ≤ mass * K C := certificate_bound ...
```

This keeps the real scalar, its `𝕜` coercion, and the map being scaled visible
in the expected types.  It also prevents semireducible unfolding from changing
the theorem shape while rewriting a local hypothesis.

Long namespace-qualified theorem names should remain syntactically contiguous.
Do not place a line break immediately after the namespace dot:

```lean
Namespace.theorem_name args
```

rather than `Namespace.` followed by the identifier on the next line.  A parser
error at that point can obscure the actual proof obligation that follows.

## 29. Separate barycentric analysis from finite certificate extraction

When an analytic argument produces an operator-valued average of a unitary
orbit, do not force measure theory, compactness, and `Fin n` bookkeeping into
one theorem.  Use three explicit layers:

```lean
Y ∈ convexHull ℝ (twoSidedUnitaryOrbit C)
X = ((m : 𝕜)) • Y
0 ≤ m ≤ mass
```

then

```lean
HasFiniteUnitaryOrbitCertificate mass X C
```

then the norm inequality.  The middle implication is finite algebra and should
be proved once with `mem_convexHull_iff_exists_fintype`.

A robust Lean implementation is:

1. extract a finite type `ι`, nonnegative weights `w : ι → ℝ`, orbit points
   `z : ι → E →ₗ[𝕜] F`, and the exact identity `Σ wᵢ • zᵢ = Y`;
2. use `choose` only after changing orbit membership into the explicit nested
   existential for left and right `LinearIsometryEquiv`s;
3. convert the restricted real action to coerced `𝕜` coefficients by
   unfolding the `Module.compHom` action; when the real action was introduced
   exactly through `algebraMap ℝ 𝕜`, this equality is definitional;
4. use coefficients `((m * w i : ℝ) : 𝕜)` so their norms simplify through
   `RCLike.norm_ofReal` and nonnegativity;
5. compute the coefficient mass as `m * Σ wᵢ = m` and apply `m ≤ mass`;
6. reindex an arbitrary `Fintype` by `Fin (Fintype.card ι)` only in a dedicated
   boundary lemma, using `Equiv.sum_comp` for both operator and mass sums.

This boundary is stronger than requiring the analytic theorem to construct a
certificate directly.  It allows the remaining Fourier proof to choose its
natural total variation `m`, rather than artificially padding the mass to
exactly `π / 2`, and it isolates the zero-mass case before normalization.

Do not call closed-convex-hull membership sufficient when the downstream API
requires an exact finite sum.  In finite dimensions, prove compactness or
closedness of the orbit convex hull, move the integral limit into the actual
convex hull, and only then invoke the finite extraction theorem.

## 30. Install restriction-of-scalars modules before stating real convex-hull goals

A type can be a module over `𝕜` without Lean automatically installing the
restricted `ℝ`-module structure needed by `convexHull ℝ`.  This matters for
spaces such as

```lean
E →ₗ[𝕜] F
```

when `𝕜` is only assumed to be `RCLike`.  If a theorem statement contains

```lean
Y ∈ convexHull ℝ s
```

Lean must synthesize `Module ℝ (E →ₗ[𝕜] F)` while elaborating the declaration
header, before the proof begins.  A `letI` inside the proof is therefore too
late.

Install a file-local restriction-of-scalars instance before the declaration:

```lean
local instance : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)
```

This composes the existing `𝕜` action with `algebraMap ℝ 𝕜`.  Do not add an
`IsScalarTower ℝ 𝕜 (E →ₗ[𝕜] F)` instance merely to convert notation: that is a
stronger compatibility obligation and may not synthesize for the chosen local
action.  At the finite sum where convex weights become `𝕜` coefficients,
prove the scalar identity by extensionality and discharge it pointwise in the
codomain.

Keep these instances local.  Exporting a second global module structure on a
widely used map type risks instance diamonds and changes elaboration far beyond
the convex-geometric proof.  Also audit every file that repeats the real
convex-hull theorem statement: imported local instances do not propagate to
importers.

### Restriction of scalars does not automatically justify a scalar tower

When a theorem needs `convexHull ℝ` on a type that is naturally a `𝕜`-module,
it is enough to install a local real module with
`Module.compHom _ (algebraMap ℝ 𝕜)`.  Do **not** also assert
`IsScalarTower ℝ 𝕜 M` unless the mixed scalar actions have actually been
proved compatible; the convex-hull API does not need that stronger instance.

At the finite-sum boundary, exploit the way the local action was defined.  For
an `RCLike` scalar, coercion from `ℝ` is definitionally the algebra map, so the
bundled-map scalar equality closes after exposing that definition:

```lean
have real_smul_map_eq (r : ℝ) (T : E →ₗ[𝕜] F) :
    r • T = ((r : 𝕜)) • T := by
  change (algebraMap ℝ 𝕜 r) • T = ((r : 𝕜)) • T
  rfl

have h' : ∑ i, (((w i : ℝ) : 𝕜)) • z i = Y := by
  calc
    ∑ i, (((w i : ℝ) : 𝕜)) • z i = ∑ i, w i • z i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (real_smul_map_eq (w i) (z i)).symm
    _ = Y := h
```

Do not descend pointwise to the codomain unless necessary: doing so asks Lean
for `Module ℝ F` and usually also `IsScalarTower ℝ 𝕜 F`, neither of which is
required for the map-level convex-hull argument.  Prefer the definitional
identity supplied by the exact restriction-of-scalars construction.

Finally, generic finite-certificate lemmas often do not use finite
dimensionality even when they live in a section that assumes it.  Put

```lean
omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
```

before the docstring and declaration so the public signature records the true
level of generality and the unused-section-variable linter stays quiet.
