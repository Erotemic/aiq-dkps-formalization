# DavisKahanExt

A literature-indexed scaffold for extending the repository's finite-dimensional
Davis--Kahan development to Hilbert spaces.

The directory is intentionally self-contained and is **not** imported from
`ForMathlib.lean`.  This lets the infinite-dimensional API evolve without
blocking the established finite-dimensional build.

## Dependency order

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

`All.lean` imports the entire scaffold.

## Major infrastructure frontiers

- Borel spectral projections and strong countable additivity.
- Bounded Borel functional calculus for self-adjoint operators.
- Symmetric/Schatten operator ideals.
- Resolvent-integral Sylvester solvers.
- Graph subspaces and bounded/unbounded Riccati equations.
- Closed operators, graph norms, relative bounds, and form sums.
- Hermitian dilation and infinite-dimensional singular-subspace theory.

Every Lean module points to the local proof distillation in
`prose/InfiniteDimensionalDavisKahan.tex`.
