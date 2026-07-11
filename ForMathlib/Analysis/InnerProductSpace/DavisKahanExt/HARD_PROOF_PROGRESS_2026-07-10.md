# DavisKahanExt hard-proof wave — 2026-07-10

Author/provenance: Jon Crall and GPT 5.6 High.

This pass works only under
`ForMathlib/Analysis/InnerProductSpace/DavisKahanExt/`.  Its purpose is to
replace high-leverage `sorry` seams with actual bounded-Hilbert-space proofs,
and to correct theorem surfaces discovered to be misleading while doing so.

## Quantitative result

Relative to source archive
`aiq-dkps-formalization-source-2026-07-10T223102-5-52e2465706f5.tar.gz`:

- bare `sorry` count before: **139**;
- bare `sorry` count after: **131**;
- net proof debt removed: **8**;
- new scaffolding obligations introduced: **2**;
- pre-existing obligations actually closed: **10**.

The two added obligations are not cosmetic.  They split a previously
misnamed theorem into a genuine reflection-defect theorem and a genuine
approximate-invariant-pair residual theorem.

## Proofs completed

### Bounded projection geometry (`Basic.lean`)

- `reduces_orthogonalComplement`
- `projection_comp_comm_of_reduces`
- `projection_apply_comm_of_reduces`
- `subspaceGap_comm`
- `directedGap_le_subspaceGap`
- `reflectionOperator_apply`
- `reflectionOperator_involutive`
- `reflectionOperator_isUnitary`
- `norm_reflectionOperator_le_one`
- `reflectionOperator_comm_of_reduces`
- `complementaryProjection_apply`
- `two_smul_diagonalPart_eq_add_reflectionConjugate`
- `two_smul_offDiagonalPart_eq_sub_reflectionConjugate`

The projection-commutation proof follows the already established finite
argument in `ForMathlib.Analysis.InnerProductSpace.SinThetaOpNorm`: split a
vector into its projection and orthogonal remainder, use reduction of both
summands, and project the image.

The reflection layer now uses mathlib's bundled `Submodule.reflection` linear
isometry instead of rebuilding `2P-I` as an unrelated continuous linear map.
This makes involutivity, surjectivity, and norm preservation structural facts.

### Resolvent algebra (`Resolvent.lean`)

- `resolventOperator` is now a totalized chosen inverse, rather than an
  unconstrained `sorry` definition.
- `resolventOperator_comp_sub_smul_id`
- `sub_smul_id_comp_resolventOperator`
- `eq_resolventOperator_of_left_inverse`
- `eq_resolventOperator_of_right_inverse`
- `resolvent_identity`
- `resolvent_perturbation_identity`

The uniqueness API was corrected: one does not need to assume that an
arbitrary comparison map is already a two-sided inverse.  A left inverse is
unique because the chosen resolvent is a right inverse, and conversely.

### Symmetric ideals (`SymmetricIdeals.lean`)

- `neg_mem`
- `sub_mem`
- `gauge_neg`
- `gauge_unitary_conjugation`
- `gauge_diagonalPart_le`
- `gauge_offDiagonalPart_le`

The two contraction theorems are now proved from reflection averaging:

- `2 · diagonalPart U A = A + JAJ`;
- `2 · offDiagonalPart U A = A - JAJ`.

Unitary invariance of the gauge and the triangle inequality then give the
sharp constant one without an operator-ideal-specific singular-value proof.

### Double-angle reflection reduction (`DoubleAngle.lean`)

- `reflectionDefect_eq_zero_of_reduces`
- `reflectionDefect_eq_perturbationDefect`
- `norm_reflectionDefect_le_two_mul`
- `sinTwoTheta_perturbation`

The perturbation theorem is now a short corollary of the still-open sharp
reflection-defect theorem and the proved factor-two defect estimate.

## Signature corrections

### Reflection versus residual

The old theorem named `sinTwoTheta_residual` had conclusion

```text
d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖.
```

That is a **reflection-defect theorem**, not a residual theorem.  It is now
named `sinTwoTheta_reflectionDefect`.

A new theorem named `sinTwoTheta_residual` represents the actual
approximate-invariant-pair statement:

```text
d * ‖sinTwoThetaEmbedding U X‖ ≤ 2 * ‖residual A X M‖.
```

The required `sinTwoThetaEmbedding` is scaffolded in `Basic.lean`.  Its
implementation should wait for the isometric-embedding closed-range bridge,
so the range projection is canonical and basis-free.

### Resolvent uniqueness

The former internal uniqueness helper demanded both inverse equations.  It
has been replaced by separate left- and right-inverse uniqueness theorems,
each with the minimal hypothesis.

### Reflection operator

`reflectionOperator` is now definitionally backed by mathlib's
`Submodule.reflection`.  The earlier hand-built `2P-I` definition had the
right pointwise formula but discarded useful isometry and equivalence data.

## Next hard proofs

The next wave should proceed in this order:

1. **Operator-angle two-projection calculus**
   - `sinAngleOperator_eq_abs_projection_sub`;
   - `norm_sinAngleOperator`;
   - the full-gap/max-of-directed-gaps identity.
2. **Ordered Sylvester core**
   - construct the semigroup integral solver;
   - prove the Sylvester equation by differentiation under the integral;
   - prove the sharp constant-one norm bound.
3. **Sharp reflection-defect `sin 2Theta`**
   - show the reflected selected subspace reduces the reflected operator;
   - transfer the finite-gap geometry;
   - identify the angle between `U` and `J_V U` with `sin(2Theta(U,V))`.
4. **Isometric embedding range infrastructure**
   - closedness of `range X`;
   - orthogonal projection onto `range X`;
   - trial-space reflection defect in terms of `residual A X M`.
5. **Riesz/gap spectral projection**
   - avoid the full Borel PVM initially;
   - build clopen spectral projections from continuous functional calculus or
     a resolvent contour.

## Validation limitation

This sandbox does not contain Lean or Lake, and DNS access is disabled, so the
pinned Lean toolchain could not be installed.  The changes were checked
against proof patterns and declarations already used in this repository, and
with static syntax/import/comment checks, but they require the repository
build command:

```bash
lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All
```

Compiler feedback should be handled as a narrow elaboration follow-up rather
than by reverting the theorem-surface corrections above.
