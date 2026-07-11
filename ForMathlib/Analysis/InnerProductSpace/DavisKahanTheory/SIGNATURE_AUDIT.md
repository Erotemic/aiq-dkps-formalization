# Finite Davis--Kahan signature audit and proof-wave status

Author/provenance: **Jon Crall and GPT 5.6 High**.

This document records the theorem-surface decisions made while closing the
finite-dimensional scaffold.  It is intentionally separate from the Ext audit:
finite singular-value lists, rectangular unitarily invariant norms, concrete
Frobenius/Ky Fan statements, eigenvalue indexing, and sharp finite models stay
in this directory even when an operator-norm core will eventually specialize a
proved Ext theorem.

## Current proof wave

Relative to source commit `52e2465`, this wave reduces the finite scaffold from
169 to 129 literal `sorry` placeholders.  The reduction is concentrated in
foundational seams rather than endpoint aliases:

- rectangular UI-seminorm algebra, operator norm, Frobenius norm, and square
  bridges;
- the Sylvester operator itself;
- compression symmetry, Galerkin orthogonality, vanishing-Ritz/invariance, and
  invariant-pair residual algebra;
- the sharp ordered half-line `sin Theta` specialization already available in
  `SinThetaUINorm`;
- the sharp square-UI `sin 2Theta` perturbation, cross-block, mirror-defect, and
  concrete operator/Frobenius forms;
- right/left Gram algebra and operator-norm perturbation bounds;
- explicit finite Hermitian dilation and its square identity;
- singular-subspace wrappers through Gram operators and Hermitian dilation.

The count is a source count, not a successful local elaboration claim.  The
execution environment used for this wave did not contain Lean or Lake.

## Signature decisions made in this wave

### 1. Sharp and generic double-angle theorems are distinct

`InternalGap` is absolute pairwise separation.  It is sufficient for the
general Sylvester estimate, but not for the constant-one ordered Sylvester
estimate used by the sharp factor-two `sin 2Theta` theorem.  The finite API now
uses:

- `TwoBlockFormGap A U a b` plus `a < b` for the sharp theorem family; and
- `InternalGap A U delta` for the general theorem with the resulting factor
  `pi` after the `sin 2Theta = 2 cross-block` normalization.

The same ordered block data is now used by the raw `tan 2Theta` scaffold.

### 2. Reflection reduction requires symmetry of the perturbed operator

`Reduces B V` means only invariance of `V`.  Commutation of the reflection in
`V` with `B` also needs invariance of `V-perp`; for the public finite API this is
obtained from `B.IsSymmetric`.  The mirror-defect-to-perturbation theorem now
exposes that hypothesis.

### 3. Generic Hermitian-dilation separation carries `pi / 2`

A `HybridGap` is generic separated-spectrum geometry.  The corresponding
dilation theorem therefore has the Bhatia--Davis--McIntosh `pi / 2` factor.
Constant one should be offered only in a separate ordered or
interval/exterior specialization.

### 4. The one-sided `sin Theta` theorem is the primitive square-UI statement

The directly proved finite core is
`sinTheta_perturbation_le_of_formBounds`.  It specializes the existing proved
`UnitarilyInvariantNorm.apply_starProjection_comp_starProjection_le` with
`V-perp` as the low spectral block.  Interval/exterior and spectral-distance
wrappers should reduce to residual/Sylvester machinery rather than duplicate
the analytic proof.

### 5. Gram and dilation objects are explicit, not opaque choices

`rightGram`, `leftGram`, `hermitianDilation`, `gramBlockDiagonal`, and
rectangular `zeroExtension` now have concrete block definitions.  This is
important for later norm equalities and Wedin-style specialization: these
objects should not remain arbitrary `sorry`-chosen maps whose intended block
semantics live only in prose.

## Signatures still requiring redesign or proof-time confirmation

### Tangent totalization

`tanThetaMap`, `tanAngleOperator`, `tanTwoAngleOperator`, and
`principalTangents` are currently total roadmap definitions.  A final API must
choose and document one of two conventions:

1. make the acute/quarter-acute proof an explicit argument to the operator; or
2. define a Moore--Penrose/zero-at-the-pole totalization and prove that it
   agrees with the genuine tangent functional calculus under the theorem's
   transversality hypothesis.

Do not prove a theorem by silently treating the current opaque totalization as
ordinary `tan` at a pole.

### Residual `sin 2Theta`

The rectangular theorem with arbitrary symmetric coordinate operator `M`
should be proved through the projected block equations or through the
reflection defect of `range X`.  During proof, verify that the chosen UI norm
has enough rectangular ideal/Fan-dominance infrastructure to compare the Ritz
residual with the supplied residual.  If that comparison fails for arbitrary
UI norms, specialize the theorem to the Ritz compression or add the exact
Galerkin hypothesis needed by the proof.

### Full versus directed sine operators

A single mixed gap controls `sinThetaMap U V`.  The full-space
`sinAngleOperator U V` duplicates or combines directed sine blocks depending
on the adopted multiplicity convention.  Full UI-norm statements must retain
both mixed gaps or prove the exact equal-defect identity that makes one side
sufficient.  Operator norm is a special case and should not be used to justify
an all-UI signature.

### Spectral branch selection

Using the same set `Omega` for two operators does not by itself select the
continued or corresponding perturbed branch.  Tangent, threshold, YWS, and
continuation results must expose one of:

- a fixed separating contour;
- a uniform interval/exterior gap and constant rank;
- ordered eigenvalue indices; or
- an explicit continued-projection hypothesis.

### Generalized trial maps

Nonorthonormal coordinates are self-adjoint in the Gram metric, not generally
in the original coordinate inner product.  Generalized tangent and Sylvester
statements must use the whitened compression or explicitly formulate
Gram-self-adjointness.

### Principal-angle multiplicities

Complement identities and full projector-difference UI norms are sensitive to
rank defects.  Equal-rank theorems may use the clean duplicated-angle
multiset.  Unequal-rank theorems must state the zero/one padding convention and
track unmatched directions explicitly.

### Sharpness

The exact planar models for `sin Theta`, tangent residual equality, and
reflection/double-angle asymptotics are different models.  The sharpness file
must not reuse one perturbation family for all four theorem families.  The
`sqrt 2` continuation threshold additionally needs a higher-dimensional branch
model.

## Preferred remaining proof order

1. Finish rectangular ideal inequalities and Fan dominance.
2. Prove ordered and interval/exterior rectangular Sylvester estimates.
3. Close residual `sin Theta` and derive perturbation wrappers.
4. Close the residual `sin 2Theta` reflection/Ritz comparison.
5. Implement proof-carrying or explicitly totalized tangent operators.
6. Close `tan Theta` and `tan 2Theta` from graph/Riccati seams.
7. Finish branch selection, YWS wrappers, direct rotation, and sharpness.

When an Ext theorem becomes proof-complete, import the smallest bounded Ext
module and use a thin specialization only if the constants, angle convention,
and branch hypotheses match exactly.  Do not route finite UI-norm claims
through an Ext theorem that proves only operator norm.
