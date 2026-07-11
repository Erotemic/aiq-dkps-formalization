# DavisKahanExt

A literature-indexed scaffold for extending the repository's finite-dimensional
Davis--Kahan development to complete Hilbert spaces.

The directory is intentionally self-contained and is **not** imported from
`ForMathlib.lean`. This lets the infinite-dimensional API evolve without
blocking the finite-dimensional build.

## Building the folder

Use Lake to build the module dependency graph:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All
```

Do not use a fresh direct Lean invocation as the bootstrap command:

```bash
lake env lean ForMathlib/Analysis/InnerProductSpace/DavisKahanExt/All.lean
```

Lean loads imports from compiled `.olean` files and does not recursively build
local source imports. The direct command works only after Lake has built the
imported modules.

`All.lean` imports the entire scaffold. Individual milestones can be built by
module name, for example:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.OperatorAngle
```

## Proof and reuse strategy

See [`PROOF_PLAN.md`](PROOF_PLAN.md) for the detailed roadmap. The central
strategy is to prove a lightweight, basis-free bounded Hilbert-space core and
specialize it to finite dimensions:

1. projection algebra and operator angles;
2. graph subspaces and direct rotations;
3. ordered operator-norm Sylvester bounds;
4. ordered `sin Theta` and reflection `sin 2 Theta`;
5. a finite bridge for operator-norm results;
6. gap-selected spectral projections and continuation;
7. Riccati/off-diagonal tangent theory;
8. only later, general `pi/2` separation, symmetric ideals, Borel calculus,
   unbounded operators, and forms.

Finite singular-value lists, arbitrary finite unitarily invariant norms,
Frobenius identities, eigenvalue combinatorics, and Yu--Wang--Samworth bounds
should remain in the finite theory rather than waiting for infinite-dimensional
operator-ideal infrastructure.

## Current module inventory

1. `Basic.lean`
2. `SpectralProjection.lean`
3. `Resolvent.lean`
4. `OperatorAngle.lean`
5. `SymmetricIdeals.lean`
6. `Sylvester.lean`
7. `SinTheta.lean`
8. `DoubleAngle.lean`
9. `Continuation.lean`
10. `GraphSubspace.lean`
11. `Riccati.lean`
12. `OffDiagonal.lean`
13. `DirectRotation.lean`
14. `Unbounded.lean`
15. `UnboundedRiccati.lean`
16. `Forms.lean`
17. `CompactAndSingular.lean`
18. `Sharpness.lean`

The current import graph is a scaffold, not the desired final proof order.
Early proof work should progressively decouple the lightweight bounded core
from `SpectralProjection`, `SymmetricIdeals`, and the unbounded layers.

## Major infrastructure frontiers

- clopen-spectrum and Riesz spectral projections;
- full Borel spectral projections and strong countable additivity;
- ordered and general-separated Sylvester solvers;
- graph subspaces and bounded/unbounded Riccati equations;
- symmetric/Schatten operator ideals;
- closed operators, graph norms, relative bounds, and form sums;
- Hermitian dilation and infinite-dimensional singular-subspace theory.

Every Lean module points to the local proof distillation in
`prose/InfiniteDimensionalDavisKahan.tex`.
