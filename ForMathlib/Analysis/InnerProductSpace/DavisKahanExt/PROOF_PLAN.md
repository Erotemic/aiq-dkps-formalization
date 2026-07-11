# DavisKahanExt proof and reuse plan

> **Path migration:** supported bounded results now live under `DavisKahan/`; foundational and literature-facing targets live under `DavisKahan/Experimental/`. The old module paths remain compatibility imports.


This document records the intended proof order for the infinite-dimensional
Davis--Kahan scaffold and, in particular, which bounded Hilbert-space results
should become shared foundations for the finite-dimensional development.

The governing principle is:

> Prove basis-free projection and operator geometry once in complete Hilbert
> spaces, specialize it to finite dimensions, and keep singular-value lists,
> arbitrary finite unitarily invariant norms, Frobenius identities, and
> eigenvalue-index combinatorics in the finite theory.

The supported bounded theory is now imported by `ForMathlib.lean`.  Build the
sequestered foundational and literature developments explicitly with:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.All
```

A direct invocation such as

```bash
lake env lean ForMathlib/Analysis/InnerProductSpace/DavisKahanExt/All.lean
```

requires all imported local modules to have already been built into `.olean`
files.  It is therefore a post-build elaboration check, not the bootstrap
command.

## 1. Shared bounded core

The first proof wave should avoid Borel spectral projections, compact ideals,
unbounded operators, and Riccati equations.  Its output should be reusable by
both the finite and infinite theories.

### 1.1 Projection algebra

Target modules: `Basic.lean` and a future lightweight projection-geometry
module if `Basic.lean` becomes crowded.

Prove:

1. reducing subspaces have reducing orthogonal complements;
2. diagonal/off-diagonal decompositions and reflection identities;
3. elementary products and differences of orthogonal projections;
4. symmetry and triangle properties of the gap metric;
5. acute-pair criteria expressed by invertibility of projection restrictions.

These proofs should use only Hilbert-space orthogonal projections and bounded
operator algebra.  The finite theory should import or wrap them instead of
reproving them by eigenbasis sums.

### 1.2 Two-projection and operator-angle calculus

Target module: `OperatorAngle.lean`.

Prove:

1. `sinAngleOperator U V = |P_U - P_V|`;
2. `‖sinAngleOperator U V‖ = ‖P_U - P_V‖`;
3. orthogonal-complement invariance;
4. equivalence of acute pairs and bounded graph representations;
5. the relation between the angular-operator norm and the maximal angle.

This is the highest-value shared layer.  Once available, the finite theory can
specialize it to obtain projector-distance and largest-principal-angle
identities while retaining its separate finite singular-value dictionary.

### 1.3 Graph subspaces

Target module: `GraphSubspace.lean`.

Prove the bounded inverse theorem seam first: for an acute pair, the restricted
projection `P_U : V -> U` is a bounded bijection.  Its inverse produces the
unique angular operator

```text
X = P_{U^perp}|_V o (P_U|_V)^(-1).
```

Then prove the block formula for the graph projection and derive
`‖X‖ = tan(theta_max)`.  These results should feed both direct rotations and the
later Riccati theory.

### 1.4 Direct rotation

Target module: `DirectRotation.lean`.

Construct the direct rotation from the polar factor of

```text
P_V P_U + P_{V^perp} P_{U^perp}.
```

The acute hypothesis gives a spectral lower bound away from zero, allowing an
inverse square root through continuous functional calculus.  Prove unitarity,
intertwining, the reflection-square identity, and only then the correctly
qualified minimal-displacement statement.

### 1.5 Planar sharpness

Target module: `Sharpness.lean`.

Prove explicit `2 x 2` models early.  They certify optimal constants for both
finite and infinite theorems because a two-dimensional reducing block embeds
in every sufficiently large Hilbert space.  Infinite direct-sum ideal
extremizers can wait until symmetric ideals exist.

## 2. Ordered analytic core

The next wave should prove the easiest genuinely infinite-dimensional analytic
engine before constructing a full projection-valued Borel measure.

### 2.1 Ordered Sylvester estimate

Target module: `Sylvester.lean`, eventually split into an ordered core and a
general-separation extension.

For form bounds

```text
A >= a I,    B <= b I,    delta = a - b > 0,
```

use the semigroup formula

```text
X = integral_0^infinity exp(-t A) C exp(t B) dt.
```

The proof obligations are:

1. define the operator-valued Bochner integrand;
2. prove strong measurability and norm integrability from
   `‖exp(-t A)‖ <= exp(-a t)` and `‖exp(t B)‖ <= exp(b t)`;
3. show the integral has norm at most `‖C‖ / delta`;
4. differentiate finite-interval integrals to obtain `A X - X B = C`;
5. send the upper endpoint to infinity;
6. prove uniqueness by applying the same estimate to the homogeneous equation.

This yields the sharp constant-one operator-norm theorem without Borel
spectral projections.

### 2.2 Ordered residual and perturbation `sin Theta`

Target module: `SinTheta.lean`.

Derive the cross-block Sylvester equation for `P_{U^perp} X`.  Apply the ordered
Sylvester theorem, then use ideal/operator-norm contraction under composition
with an isometry.  The finite operator-norm theorem should become a thin
specialization of this result.

### 2.3 Reflection proof of `sin 2 Theta`

Target module: `DoubleAngle.lean`.

Conjugate by the reflection `J_U = 2 P_U - I`.  The reflected operator has the
same spectrum, while the reflection defect isolates twice the off-diagonal
perturbation.  Reduce the angle expression to a cross-block Sylvester equation
and bound the defect by `2 ‖A-B‖`.

## 3. Gap-selected spectral projections without full Borel calculus

Before the full `SpectralProjection.lean` programme, introduce a narrower
clopen-spectrum or contour-selected projection interface.

For a self-adjoint operator whose spectrum splits into two closed sets with
positive distance, the indicator of one component is continuous on the
spectrum.  Therefore the ordinary continuous functional calculus can define
the projection.  Alternatively, use a Riesz contour integral.

Prove:

1. the result is an orthogonal projection;
2. it commutes with the operator;
3. its range reduces the operator;
4. it agrees with a Riesz projection;
5. it varies norm-continuously while the gap remains open.

This is enough for most Davis--Kahan applications and avoids making strong
countable additivity a prerequisite for the basic perturbation theorem.

## 4. Finite specialization bridge

Add a bridge only after the bounded core is proved.  It should not import the
entire infinite scaffold.

The finite bridge should:

1. convert finite-dimensional linear maps to continuous linear maps;
2. identify finite star projections with the Hilbert-space projections used
   here;
3. specialize operator-angle and graph-subspace results;
4. recover operator-norm `sin Theta`, projector-difference, `sin 2 Theta`, and
   direct-rotation theorems;
5. leave finite principal-angle lists, singular values, Ky Fan/Frobenius
   estimates, Hoffman--Wielandt, and Yu--Wang--Samworth in the finite theory.

Do not make the finite UI-norm programme wait for infinite symmetric ideals.
The finite implementation is already much closer to closure.

## 5. Continuation, graph selection, and Riccati theory

After gap projections and the ordered core:

1. prove norm continuity of Riesz projections from the resolvent identity;
2. show projections at norm distance below one have isomorphic ranges;
3. select the continuation component born from the unperturbed spectral block;
4. turn the selected subspace into a graph;
5. prove the graph-reduces iff Riccati equation equivalence;
6. obtain existence from spectral continuation rather than starting with a
   nonlinear fixed-point argument;
7. prove uniqueness inside the contractive branch;
8. derive block diagonalization and the generalized `tan 2 Theta` theorem;
9. prove the sharp a priori `tan Theta` estimate by a scalar majorant argument
   on the Riccati solution norm.

A contraction mapping proof remains useful as a secondary local result, but
continuation better matches the spectral branch that applications need.

## 6. General separation and symmetric ideals

These are independent extensions and should not block operator-norm closure.

### 6.1 General `pi/2` Sylvester theorem

The constant-one theorem does not hold for arbitrary separated spectra.  The
general theorem should be proved separately using a Fourier multiplier,
double-operator-integral, or contour decomposition whose scalar kernel has
`L1` norm `pi/2`.  Formalization should isolate the scalar harmonic-analysis
lemma from the operator integral.

### 6.2 Symmetric ideals

Build compact operators and singular values first, then Schatten and trace
ideals, then general symmetric gauges.  Prove ideal multiplication and
pinching before ideal-valued Sylvester estimates.  These results can later
recover finite Schatten/Ky Fan corollaries, but they should not replace the
finite arbitrary-UI-norm development.

## 7. Unbounded and form perturbations

Treat these as later waves:

1. reconcile the local `ClosedOperator` scaffold with mathlib's partial-linear
   map and adjoint infrastructure;
2. prove graph-norm completeness;
3. prove Kato--Rellich through relative boundedness and closed graph norms;
4. establish unbounded resolvent identities;
5. define spectral projections for self-adjoint closed operators;
6. prove domain-preserving strong Riccati equivalences;
7. build closed semibounded forms and the representation theorem;
8. prove KLMN and only then formulate form-level Davis--Kahan estimates.

## 8. Suggested milestone sequence

1. projection algebra;
2. operator-angle identities;
3. graph representation;
4. planar sharpness;
5. ordered Sylvester operator-norm theorem;
6. ordered residual and perturbation `sin Theta`;
7. reflection `sin 2 Theta`;
8. finite bridge for those results;
9. clopen-spectrum/Riesz projections;
10. continuation and branch selection;
11. bounded Riccati and off-diagonal tangent theorems;
12. general `pi/2` separation;
13. symmetric ideals;
14. compact singular-subspace/Wedin theory;
15. unbounded operators and forms.

This order maximizes early reuse and prevents the Borel, ideal, and unbounded
frontiers from blocking the finite-dimensional programme.

## Per-theorem agent instructions

Every theorem declaration in this directory now has a `Lean proof route for a
weaker agent` in its docstring.  Before starting a proof, also read
`SIGNATURE_AUDIT.md`; it records which declarations were strengthened and
which foundational APIs still require redesign.  Cross-directory observations
for the finite agent are isolated in `NON_EXT_AGENT_HANDOFF.md`.
