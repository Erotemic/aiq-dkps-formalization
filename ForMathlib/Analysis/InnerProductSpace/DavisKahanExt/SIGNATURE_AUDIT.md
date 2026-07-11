# DavisKahanExt theorem-signature audit

Author/provenance: Jon Crall and GPT 5.6 High.

This audit covers
`ForMathlib/Analysis/InnerProductSpace/DavisKahanExt/`. It accompanies the
proof-strategy docstrings attached to every theorem and lemma in the directory.
The declarations remain a roadmap: this document records why the signatures are
mathematically plausible, which ones were corrected, and which infrastructure
must exist before proof work begins.

## Audit result

The Ext tree contains 87 theorem/lemma declarations. Every declaration now has:

1. a local proof route;
2. an `Ext-agent signature audit (GPT 5.6 High)` paragraph; and
3. a preferred dependency route identifying the lower layer that should prove it.

The audit found several statements that were false, underdetermined, or stronger
than the hypotheses supported. Those signatures were changed rather than merely
annotated.

## Signature corrections made

### Bounded angle geometry

- `tanAngleOperator` now takes `IsAcute U V`. A bounded tangent operator is not
  canonical when the angle spectrum reaches `pi / 2`.
- `tanTwoAngleOperator` now takes `IsQuarterAcute U V`. This prevents a total
  bounded definition across the pole at `pi / 4`.
- `tanTwoTheta_offDiagonal` passes its quarter-angle proof to the operator.

### Generic and sharp double-angle theory

- `sinTwoTheta_generalSeparation` now bounds
  `d * ‖sinTwoAngleOperator U V‖`, rather than only
  `sin (2 * maximalAngle U V)`. The latter can miss intermediate angle spectrum
  when the spectrum crosses `pi / 4`.
- The sharp residual, perturbation, and ideal `sin 2Theta` statements use
  `FiniteGapConfiguration`; the separate `InternalGap` premise was redundant at
  positive `d`.
- Generic separated spectra remain separate from the finite-gap constant-one
  theorem and retain the larger universal constant.

### Continuation

- `continuous_continuedProjection` now assumes contour separation only on
  `[0,1]` and concludes `ContinuousOn` there.
- `SameProjectionComponent` likewise uses continuity on `[0,1]`, rather than
  demanding an irrelevant globally continuous extension.

### Symmetric ideals

- `kyFan` now requires `0 < k`.  The zero-th Ky Fan gauge is identically zero, so it cannot inhabit a structure whose gauge is definite.

`SymmetricNormIdeal` now explicitly records the properties used by the later
proofs:

- closure under adjoint;
- zero and definiteness laws for the gauge;
- adjoint invariance of the gauge; and
- sequential completeness in the gauge.

Every norm law is now restricted to operators satisfying `mem`.  This is
necessary: trace and Schatten norms are not finite real-valued norms on all
bounded operators.  The total `gauge` field is only a notational roadmap and
may be arbitrarily totalized away from the carrier.  Unitary conjugation now
returns ideal membership as well as equality of gauges.  A future
implementation should replace this roadmap structure with a bundled complete
normed space of ideal members.

### Riccati theory

- Local bounded and unbounded Riccati existence uses the conservative condition
  `2 * ‖B01‖ < d`. This is a contraction threshold, not the distinct sharp
  `sqrt 2 * d` continuation threshold for off-diagonal spectral branches.
- Bounded block diagonalization now returns unitary data, inverse identities,
  and the actual conjugation equality.
- The unbounded graph/Riccati equivalence explicitly includes domain
  preservation.
- Unbounded block diagonalization now states unitary equivalence with two-way
  transport of domains and actions, rather than only projection intertwining.

### Closed and unbounded operators

- `ClosedOperator.IsSelfAdjoint` is equality with the Hilbert-space adjoint.
  Maximal symmetry is not used as a substitute.
- `addRelative` now takes nonnegative relative-bound parameters and a relative
  bound below one. An arbitrary domain-linear perturbation need not define a
  closed operator.
- Kato--Rellich for relatively bounded perturbations carries symmetry,
  nonnegativity, and the bound-below-one assumptions.
- Unbounded `sin Theta` carries measurable spectral sets and both mixed gaps.
  Because those gaps are only arbitrary pairwise separation, the corrected
  theorem uses the universal `pi/2` constant; a later interval/exterior theorem
  should recover constant one.

### Forms

The original KLMN target did not assume that the reference form was actually
sesquilinear, closed, and lower semibounded: those fields were propositions,
not proofs bundled into the structure. The corrected `klmn` and form
`sin Theta` statements now take explicit validity hypotheses for the reference
and perturbing forms.

The form layer remains provisional until `ClosedForm.sesquilinear`,
`closedness`, and `lowerSemibounded` are replaced by mathematical predicates
with their required data.

### Spectral sets and compact/singular theory

- Spectral-projection laws and compact/Wedin wrappers carry measurable-set
  hypotheses.
- Off-diagonal positive spectral-distance conclusions carry nonempty initial
  block spectra.
- `hermitianDilation_spectralProjection_sinTheta` is explicitly a
  Hermitian-dilation spectral-projector bound. Its arbitrary separated-set form uses `pi/2`; a sharp
  constant-one version needs ordered or interval/exterior singular clusters.
  Separate left/right singular-subspace corollaries remain to be added.

### Sharpness

- The exact `sin Theta` equality model now uses the difference of rotated and
  unrotated two-level operators. It is not mislabeled as an off-diagonal
  perturbation.
- The factor two in `sin 2Theta` is stated as asymptotically sharp: the planar
  ratio tends to one as the angle tends to zero, rather than being falsely
  asserted as exact at every angle.
- The universal `sqrt 2` branch threshold is represented by a four-dimensional
  existential model. A single planar off-diagonal block cannot exhibit the
  required branch loss.
- Ideal sharpness is tied to an actual operator identity, not inferred from
  operator-norm sharpness.

## Remaining foundational design obligations

These are not currently theorem-signature defects, but proofs should not begin
above them until they are resolved.

1. **Spectral calculus.** Bundle a bounded self-adjoint operator with a Borel
   projection-valued measure, or first implement gap-selected Riesz projections
   and defer the full Borel layer.
2. **Restricted spectrum.** Define restriction only for reducing subspaces, or
   make the compression/restriction distinction explicit. Current theorem
   hypotheses consistently supply reduction, but the total definition remains
   semantically broad.
3. **Contours.** `ContourSeparatesSpectrum` must include a closed rectifiable or
   piecewise `C1` contour, resolvent-set inclusion, orientation, and winding
   numbers.
4. **Operator ideals.** Use a complete normed space of ideal members so
   ideal-valued Bochner integrals and limits are ordinary mathlib arguments.
5. **Partial operators.** Reconcile `ClosedOperator` with mathlib's partial
   linear-map infrastructure before implementing adjoints, resolvents, and
   Kato--Rellich.
6. **Form domains.** Bundle the form-domain Hilbert norm, inclusion into the
   ambient Hilbert space, and the representation theorem.
7. **Planar models.** Define the matrices explicitly and verify every reducing,
   gap, continuation, and equality hypothesis rather than allowing the model
   definitions to absorb the theorem.

## Recommended proof order

1. `Basic`
2. gap-selected `SpectralProjection` and `Resolvent`
3. `OperatorAngle` and `GraphSubspace`
4. ordered `Sylvester`
5. operator-norm `SinTheta`
6. finite-gap `DoubleAngle`
7. `Continuation`
8. bounded `Riccati` and `OffDiagonal`
9. `DirectRotation`
10. complete `SymmetricIdeals` and ideal corollaries
11. unbounded operators and unbounded Riccati
12. forms, compact/singular applications, and sharpness

Build the directory explicitly with:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All
```
