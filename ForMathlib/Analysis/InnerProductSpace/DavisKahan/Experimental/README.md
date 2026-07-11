# Experimental Davis--Kahan development

This tree retains ambitious foundational developments and theorem statements
that track the literature without making them dependencies of the supported
bounded theory.

## Foundation

`Foundation/` contains infrastructure that may eventually become general
`ForMathlib` material:

- provisional abstract spectral interfaces;
- Borel and Riesz spectral projections;
- operator-angle functional calculus;
- symmetric operator ideals;
- general Sylvester solvers;
- unbounded operators and closed forms;
- the missing real spectral-to-form bridge;
- complexification and real continuous-functional-calculus roadmaps.

Definitions in this directory are implementation seams, not frozen APIs.
The literature-facing statements that use them are retained so later work has
concrete targets.

## Literature

`Literature/` contains recognizable theorem families from Davis--Kahan,
Kato-style perturbation theory, graph-subspace and Riccati theory, direct
rotations, continuation, and sharpness constructions.

Build the complete retained development with:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.All
```

Experimental modules may import supported modules.  Supported modules must not
import this tree.
