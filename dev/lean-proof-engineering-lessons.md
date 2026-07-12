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
