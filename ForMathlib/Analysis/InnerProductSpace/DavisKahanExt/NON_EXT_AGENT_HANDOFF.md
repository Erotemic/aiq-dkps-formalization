# Handoff to the finite-dimensional Davis--Kahan agent

Author/provenance: Jon Crall and GPT 5.6 High.

This document is written by the `DavisKahanExt` agent. It records non-Ext
signatures that conflict with, or would be weakened by, the proof routes now
specified in the Ext theorem docstrings. No file outside `DavisKahanExt/` is
modified by this overlay.

## Boundary rule

Do not import `DavisKahanExt.All` into the finite theory. Once an Ext theorem is
proof-complete, import the smallest bounded module that contains it and write a
thin finite specialization. Keep finite singular-value lists, rectangular
unitarily invariant norms, Frobenius/Ky Fan identities, eigenvalue ordering,
and dimension-dependent results in the finite tree.

## Blocking finite signature issues

### 1. Sharp `sin 2Theta` needs finite-gap geometry

The following finite statements currently use only `InternalGap` while claiming
the sharp factor two for every unitarily invariant norm:

- `sinTwoTheta_residual_le`
- `sinTwoTheta_perturbation_le`
- `sinTwoTheta_cross_perturbation_le`
- `sinTwoTheta_reflectionDefect_le`
- `sinTwoTheta_spectralSubspace_le`
- `sinTwoTheta_perturbation_le_unequalFinrank`
- `opNorm_sinTwoTheta_le`
- `frobenius_sinTwoTheta_le`
- `kyFan_sinTwoTheta_le`

The Ext audit separates two results:

- finite-gap/interval-exterior geometry gives the sharp reflection theorem;
- arbitrary separated spectra route through the general Sylvester inverse and
  carry a larger universal constant.

The finite signatures should make the same split. Do not specialize
`DavisKahanExt.sinTwoTheta_perturbation` from a bare `InternalGap` theorem.

### 2. `reflectionDefect_le_two_mul_perturbation` is missing symmetry

`Reduces B V` in the finite scaffold records only invariance of `V`; it does not
by itself imply invariance of `Vᗮ`. The reflection commutes with `B` only after
adding `hB : B.IsSymmetric` or explicitly requiring both reducing blocks.

### 3. Generic `sin 2Theta` should remain operator-valued

Do not replace `‖sinTwoAngleOperator U V‖` by
`sin (2 * maximalAngle U V)` without a quarter-angle restriction. If the angle
spectrum contains values on both sides of `pi / 4`, the largest value of
`sin (2 theta)` need not occur at the maximal angle.

### 4. Tangent operators should expose their domains

Finite `tanAngleOperator` and `tanTwoAngleOperator` are total roadmap
constructions. Every theorem must carry, respectively:

- acuteness (`theta_max < pi/2`), and
- quarter-acuteness (`theta_max < pi/4`).

A cleaner final API should make these proof arguments part of the definitions,
as the Ext tree now does, or use a partial/functional-calculus object whose
boundedness theorem has those hypotheses.

### 5. Planar sharpness models are conflated

`DavisKahanTheory/Sharpness.lean` reuses `modelPerturbation` for the exact
`sin Theta`, `tan Theta`, and `sin 2Theta` equalities. These are not the same
model requirements.

- Exact `sin Theta` equality is realized by the difference between rotated and
  unrotated two-level operators.
- Tangent equality needs a residual/off-diagonal model satisfying the relevant
  zero-compression hypothesis.
- The factor two in `sin 2Theta` is generally asymptotic in the planar rotated
  model; the ratio tends to one as the angle tends to zero.
- The `sqrt 2` continuation threshold requires a higher-dimensional branch
  model; one planar off-diagonal block is insufficient.

Consequently, audit at least:

- `sinTheta_model_equality`
- `tanTheta_model_equality`
- `sinTwoTheta_model_equality`
- `tanTwoTheta_model_equality`
- `sinTwoTheta_constant_optimal`
- `directSum_models_simultaneous_equality`
- `four_bounds_first_order_equivalent`

before attempting their proofs.

### 6. Generalized compression must use the Gram metric

`generalizedTanTheta_residual_le` depends on a coordinate compression formed
from a nonorthonormal trial map. Ordinary symmetry is not preserved by
whitening unless the coordinate operator commutes with the Gram operator. Use
one of these mathematically equivalent interfaces:

1. a Gram-self-adjoint coordinate operator plus its whitened self-adjoint
   conjugate; or
2. formulate the Sylvester equation directly in the Gram inner product.

Do not route this theorem through a falsely ordinary-symmetric
`generalizedCompression`.

### 7. Finite continuation needs a uniform contour or gap

`spectralSubspace_path_continuous` currently assumes only that the chosen
spectral subspace's spectrum lies in `Omega`, which is essentially tautological
and does not isolate a branch. Replace it with a fixed separating contour, or a
positive uniform distance from the selected set to the complementary spectrum
for every `t in [0,1]`. The Ext specialization should then use
`continuous_continuedProjection`.

### 8. Canonical spectral projectors must carry the selected branch

Statements such as `sinTwoTheta_spectralSubspace_le` currently use the same set
`Omega` for both operators without asserting that it selects the continued or
corresponding perturbed component. For tangent and threshold results, an
arbitrary reducing eigenspace of the perturbed operator is not enough. State
continuation, index/rank preservation, or an explicit ordered eigenblock.

### 9. Full versus directed angle remains important

One mixed gap controls a cross projection/directed angle. A full projector
difference requires:

- the reverse mixed gap;
- an equal-defect/acute identity; or
- a self-adjoint off-diagonal block argument that preserves singular-value
  multiplicity.

Do not silently replace a directed theorem by a full `sinAngleOperator` theorem
when specializing Ext.

### 10. Preserve explicit dependencies in `sorry`-backed definitions

Lean omits section variables that do not occur in a declaration's result type.
This previously broke `adjointTransport`. Any finite definition whose intended
construction depends on a norm, gap witness, basis, or proof argument must put
that dependency explicitly in its signature.

### 11. Generic separated spectra carry `pi/2`, not constant one

When the finite tree specializes generic Ext statements, distinguish arbitrary
pairwise spectral separation from ordered or interval/exterior geometry. The
generic Sylvester inverse gives `pi/2`; constant one requires the stronger
geometry. This affects any future finite wrappers modeled after:

- unbounded spectral-set `sin Theta`;
- form perturbation `sin Theta`; and
- Hermitian-dilation statements underlying Wedin for arbitrary selected sets.

Do not erase this distinction merely because finite spectra can be enumerated.
Enumeration does not turn interlaced separated sets into ordered sets.

## Finite results that should specialize from Ext

Once the corresponding Ext declaration is proof-complete, prefer thin wrappers
for:

- reducing orthogonal complements;
- symmetry and directed/full projection-gap identities;
- acute graph representations and graph projection formulas;
- direct rotation and operator-norm extremality;
- ordered and general operator-norm Sylvester estimates;
- operator-norm residual and perturbation `sin Theta`;
- finite-gap operator-norm `sin 2Theta`;
- Riesz-projection continuation and branch selection;
- graph/Riccati equivalences and bounded block diagonalization;
- off-diagonal gap preservation and operator-norm tangent bounds.

## Finite-specific work that should remain local

Do not wait for Ext to prove:

- rectangular finite-dimensional unitarily invariant norms;
- singular-value majorization and Fan dominance;
- principal-angle lists, padding, and multiplicities;
- Frobenius/Hilbert--Schmidt and nuclear identities;
- finite eigenvalue ordering and block-index wrappers;
- Hoffman--Wielandt and Yu--Wang--Samworth bounds;
- exact matrix formulas and dimension factors.

## Acceptance test for every Ext specialization

Before replacing a finite proof:

1. the imported Ext theorem contains no `sorry`;
2. the finite wrapper proves that all Ext hypotheses follow from the finite
   data, including measurability and branch selection;
3. the constant and angle convention exactly match the finite statement;
4. the import is the smallest bounded module required; and
5. UI-norm or singular-value conclusions remain powered by finite machinery
   rather than being weakened to operator norm.

## Riesz/spectral projection measurability

Any finite wrapper that identifies a Riesz projection with a Borel spectral projection
should expose `MeasurableSet s` (or use an interval/half-line constructor whose
measurability is automatic).  Do not hide this obligation in a contour-separation
predicate: it belongs to the Borel functional-calculus side of the theorem.
