# Finite-dimensional Davis--Kahan theory scaffold

This directory is a theorem-level roadmap for a complete finite-dimensional
Davis--Kahan theory.  The declarations intentionally use `sorry`; they are
written at the intended final API boundary so proof work can proceed from the
foundational seams upward without repeatedly redesigning statements.

Model provenance for the scaffold: **GPT 5.6 High**.

## Dependency order

1. `Basic.lean`
2. `RectangularUINorm.lean`
3. `Residual.lean`
4. `Sylvester.lean`
5. `SinTheta.lean`
6. `TanTheta.lean`
7. `SinTwoTheta.lean`
8. `TanTwoTheta.lean`
9. `Generalized.lean`
10. `DirectRotation.lean`
11. `Davis1963.lean`
12. `Sharpness.lean`
13. `Statistics.lean`
14. `SingularSubspace.lean`

The mathematical proof roadmap and source mapping are in:

- `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`
- `ForMathlib/prose/Davis-1963-core-arguments.tex`
- `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`
- `papers/DavisKahan-formalized-vs-literature.tex`

The umbrella module is
`ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory`.
