# DavisKahanExt compatibility tree

`DavisKahanExt` was the original workspace for the infinite-dimensional
formalization.  Its mature bounded results have been promoted into a supported
`RCLike` core, while its ambitious foundations and literature-indexed targets
have been moved under an explicit experimental tree.

## Build targets

Supported bounded theory:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.All
```

All retained foundations and literature targets:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.All
```

Compatibility targets:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.ExperimentalAll
```

`DavisKahanExt.All` intentionally imports only the supported theory.  It no
longer pulls Borel calculus, Riesz projections, operator ideals, graph
subspaces, Riccati theory, unbounded operators, or form perturbations into the
main dependency graph.

## New layout

General reusable infrastructure:

- `../ReducingSubspace.lean`;
- `../QuadraticFormBounds.lean`;
- `../ProjectionBlocks.lean`;
- `../ProjectionGap.lean`;
- `../SylvesterOperator.lean`;
- `../SpectralOrder/Complex.lean`.

Supported perturbation theory:

- `../DavisKahan/Basic.lean`;
- `../DavisKahan/SinTheta.lean`;
- `../DavisKahan/Projector.lean`;
- `../DavisKahan/ReflectionDefect.lean`;
- `../DavisKahan/Spectral/Complex.lean`.

Sequestered development:

- `../DavisKahan/Experimental/Foundation/`;
- `../DavisKahan/Experimental/Literature/`.

The old individual `.lean` files in this directory are compatibility imports.
New work should use the new paths.

## Scalar policy

The supported analytical core is generic over `RCLike`.  The complex spectral
module is a leaf bridge from actual restriction spectra to generic form-bound
hypotheses.  The corresponding real bridge is retained as a concrete
foundation target in
`DavisKahan/Experimental/Foundation/RealSpectralBridge.lean`.

## Roadmap documents

- `PROOF_PLAN.md` remains the literature proof roadmap;
- `SIGNATURE_AUDIT.md` records theorem-surface issues;
- `NON_EXT_AGENT_HANDOFF.md` records finite-tree specialization opportunities;
- `../DavisKahan/RESTRUCTURE_2026-07-11.md` records the new architecture.
