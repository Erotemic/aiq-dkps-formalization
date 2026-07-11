# DavisKahanExt theorem-signature audit

Author/provenance: Jon Crall and GPT 5.6 High.

This audit covers only
`ForMathlib/Analysis/InnerProductSpace/DavisKahanExt/`.  It records the
signature corrections made while adding proof recipes to every theorem.  It
is not a claim that the declarations have already been proved or freshly
elaborated.

## Audit standard

Each theorem should satisfy four tests before proof work begins:

1. **Non-vacuity.**  The conclusion must express the advertised result rather
   than merely assert existence of an identity operator, a reducing `⊤`, or an
   arbitrary ideal member.
2. **Correct geometry.**  A full projector-difference or full `sin Θ` statement
   needs both directed gap hypotheses unless a separate equal-defect theorem
   supplies the missing direction.
3. **Analytic domain.**  Borel calculus requires self-adjointness,
   measurability, and boundedness on the spectrum; tangent operators require
   exclusion of their poles; unbounded compositions require explicit domain
   preservation.
4. **Ideal semantics.**  Schatten parameters must lie in the norm range and
   ideal-valued conclusions must include the relevant membership premise or
   conclusion.

## Corrections made in this overlay

### `Basic.lean`

- Added `BoundedOnSpectrum` so Borel-calculus laws do not quantify over
  unrestricted unbounded functions.
- Added `IsQuarterAcute`, expressed through the projection gap, as the domain
  condition for bounded `tan (2 Θ)` statements.

### `SpectralProjection.lean`

- Added self-adjointness assumptions to spectral-projection laws.
- Added `MeasurableSet` assumptions to set operations and indicator laws.
- Added measurability and spectral boundedness to multiplication and norm laws
  for the Borel calculus.
- Strengthened `StronglyCountablyAdditive` so it quantifies only over measurable
  disjoint families.

The definitions remain total roadmap placeholders.  An implementation may
encode invalid inputs as zero, but all public laws are now restricted to the
mathematically meaningful domain.

### `OperatorAngle.lean`

- Strengthened `norm_angularOperator_eq_tan_maximalAngle` so its witness is an
  actual angular operator whose graph is the target subspace.  The previous
  existential only prescribed a norm and was therefore too weak.

### `SymmetricIdeals.lean`

- Added absolute homogeneity and unitary invariance to the ideal structure.
- Restricted Schatten ideals to `1 ≤ p`.
- Added ideal-membership hypotheses and conclusions to pinching and
  off-diagonal extraction.
- Strengthened unitary conjugation with explicit unitary and inverse data.

A later implementation should replace the roadmap structure with a bundled
complete normed space of ideal members.  That is needed to justify
ideal-valued Bochner integrals without adding an ad hoc closure axiom.

### `Sylvester.lean`, `SinTheta.lean`, and `DoubleAngle.lean`

- Ideal statements now start from membership of the perturbation/right-hand
  side and return membership of the solution/angle operator together with the
  norm estimate.
- The canonical spectral-projector `sin Θ` theorem now has both mixed gap
  hypotheses.  One mixed gap controls only a directed angle.

### `Continuation.lean`

- `continuedProjection_same_component` now assumes continuity of the supplied
  projection path.  Projection-valuedness alone does not imply that two
  endpoints lie in the same norm-continuous component.

### `Riccati.lean`

- The existence theorem now returns the distinguished contractive solution and
  its quantitative norm bound.
- The standalone norm and uniqueness theorems now include the small-coupling
  and contractive-branch hypotheses needed to select that solution.
- Added `blockDiagonalOperator`.
- Replaced the vacuous “there exists an invertible operator” conclusion of
  `blockDiagonalization_of_riccati` with an actual conjugation to a block
  diagonal operator.

### `OffDiagonal.lean`

- Replaced the vacuous conclusion `∃ V, Reduces (A+H) V` with the continued
  spectral subspace, reduction, acuteness, and a positive perturbed spectral
  gap.
- Added the quarter-angle hypothesis to the raw `tan 2Θ` theorem.
- Removed the duplicate vacuous sharpness theorem; the explicit planar
  sharpness theorem lives in `Sharpness.lean`.
- Added positivity, finite-gap, and smallness assumptions to spectral
  repulsion so the selected branch is determined.

### `Unbounded.lean`

- Corrected `SpectralSetsSeparated`: selected spectral points now mean points
  in the intersection of the chosen set and the operator spectrum.  The old
  subset direction made complements such as `tᶜ` impossible in applications.
- Added symmetry and nonnegativity assumptions to Kato--Rellich for relatively
  bounded perturbations.
- Added both mixed gaps to the full projector-difference `sin Θ` theorem.

### `UnboundedRiccati.lean`

- Distinguished graph invariance from reduction.  A one-sided strong Riccati
  equation gives graph invariance; reduction additionally needs the adjoint
  graph/domain decomposition.
- Strengthened reduction to require preservation of the domain by both
  orthogonal projections.
- Added spectral-cover hypotheses to the strong-solution existence theorem.
- Replaced the vacuous unitary-existence conclusion with graph invariance and
  projection intertwining.

### `Forms.lean`

- Recorded sesquilinearity and lower semiboundedness in `ClosedForm`.
- Strengthened KLMN to return closedness and self-adjointness of the associated
  operator.
- Added `formPerturbationSize` and both mixed spectral gaps to the form-version
  `sin Θ` statement.  The earlier `(alpha+beta)/d` conclusion had neither the
  correct units nor sufficient spectral hypotheses.

### `CompactAndSingular.lean`

- Added reverse mixed gaps to full projection-difference statements.
- Restricted Schatten statements to `1 ≤ p` and added membership.
- Added the reverse gap to the Hermitian-dilation/Wedin theorem.

### `Sharpness.lean`

- Replaced the vacuous theorem asserting existence of any ideal member with an
  actual ideal-valued planar equality model.

## Remaining design decisions before proofs

These are not signature errors, but they determine implementation order.

1. Replace the total placeholder `spectralProjection` with either a Borel PVM
   package or a gap-selected continuous/Riesz projection core plus a later
   Borel extension.
2. Replace `SymmetricNormIdeal` with a bundled complete normed space of members
   before proving ideal-valued integral formulas.
3. Reconcile `ClosedOperator` with mathlib's partial-linear-map infrastructure
   before proving Kato--Rellich or unbounded Riccati results.
4. Decide whether `tanAngleOperator` and `tanTwoAngleOperator` should take proof
   arguments or remain total definitions whose theorems carry pole-avoidance
   assumptions.
5. Give `ContourSeparatesSpectrum` a concrete contour regularity and winding
   number package before implementing Riesz integrals.

## Recommended validation command

The folder is intentionally not imported by `ForMathlib.lean`.  Build it with:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All
```
