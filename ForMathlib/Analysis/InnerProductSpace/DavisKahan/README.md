# Supported bounded Davis--Kahan theory

This directory contains the supported, dimension-free bounded theory.

The primary analytical API is generic over `RCLike` scalars.  It is stated in
terms of quadratic-form bounds and therefore does not depend on a
scalar-specific functional calculus:

- `SinTheta.lean`: the directed constant-one coercive `sin Θ` estimate;
- `Projector.lean`: the sharp factor-one projector theorem;
- `ReflectionDefect.lean`: reflection and double-angle perturbation algebra;
- `Spectral/Complex.lean`: a leaf specialization from actual complex spectra.

The reusable non-Davis--Kahan ingredients live one level higher:

- `ReducingSubspace.lean`;
- `QuadraticFormBounds.lean`;
- `ProjectionBlocks.lean`;
- `ProjectionGap.lean`;
- `SylvesterOperator.lean`;
- `SpectralOrder/Complex.lean`.

Build the supported slice with:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.All
```

The supported umbrella does not import any module under `Experimental/`.
