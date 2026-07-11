# Handoff to the finite-dimensional Davis--Kahan agent

Author/provenance: Jon Crall and GPT 5.6 High.

This document is written by the `DavisKahanExt` agent.  It records issues and
specialization opportunities observed in the non-Ext finite-dimensional tree.
No file outside `DavisKahanExt/` is changed by this overlay.

## Boundary rule

Do not import `DavisKahanExt.All` into the finite theory.  When a shared theorem
is proved, import the smallest bounded-core module that contains it.  The
finite singular-value, Frobenius, Ky Fan, and dimension-dependent theories
should remain finite-specific.

## Results that should eventually specialize from Ext

The finite agent should plan to replace duplicate proofs with wrappers around
these Ext results once they are proof-complete:

- reducing orthogonal complements;
- symmetry and directed/full projection-gap identities;
- operator-angle and graph-subspace geometry;
- direct rotation and projection intertwining;
- ordered operator-norm Sylvester estimates;
- operator-norm residual and perturbation `sin Θ`;
- reflection-based operator-norm `sin 2Θ`;
- continuation of isolated spectral projections;
- Riccati/graph formulations of the off-diagonal tangent theorems;
- planar sharpness of universal constants.

A future finite bridge should live in the finite agent's directory and convert
finite linear maps to continuous linear maps.  It should import individual Ext
modules, not the umbrella module.

## Finite-only work that should not wait for Ext

Continue independently on:

- rectangular finite-dimensional unitarily invariant norms;
- singular-value majorization and Fan dominance;
- principal-angle lists and multiplicities;
- Frobenius/Hilbert--Schmidt identities;
- Hoffman--Wielandt and Yu--Wang--Samworth bounds;
- finite eigenvalue ordering, block dimensions, and matrix wrappers;
- all exact finite-rank and dimension-factor statements.

## Signature checks for the finite scaffold

The Ext audit suggests the finite agent should verify the following points in
`DavisKahanTheory/`.

1. **Full versus directed angles.**  A single mixed gap proves a directed
   cross-projection estimate.  A full `sinAngleOperator` or projector-
   difference estimate needs the reverse gap, an equal-defect theorem, or an
   operator-norm identity that supplies it.
2. **Tangent poles.**  Public `tan Θ` statements need acuteness; public
   `tan 2Θ` statements need exclusion of the quarter-angle pole.  Total
   definitions are acceptable only if every theorem states its domain.
3. **Schatten parameters.**  Norm statements require `1 ≤ p`.  Values below
   one belong to quasi-norm theory and should not inhabit a norm structure.
4. **Ideal/rectangular membership.**  Infinite ideals need membership, but
   finite rectangular norms are total.  Do not accidentally copy the Ext
   membership API into finite-dimensional norm statements.
5. **Riccati diagonalization.**  Any theorem called block diagonalization must
   state the conjugation equality, not merely existence of an invertible or
   unitary operator.
6. **Sharpness.**  Equality/optimality theorems must contain the equality or
   failed improved bound.  Existence of arbitrary operators or an ideal member
   is vacuous.
7. **Direct rotation extremality.**  Distinguish operator-norm minimality from
   stronger claims for every unitarily invariant norm; state any angle
   restriction required by the literature.
8. **Spectral subspaces.**  Keep basis-indexed finite constructions as
   implementation lemmas, but expose operator-and-spectral-set projectors in
   the public API once their basis independence is proved.
9. **Rectangular UI norms.**  Preserve explicit dependence on a norm parameter
   in `sorry`-backed definitions.  Lean drops unused section variables, which
   previously caused the `adjointTransport` constructor bug.
10. **Hilbert direct sums.**  Use `WithLp 2 (E × F)`, not the ordinary product
    norm, for zero extensions and Hermitian dilations.

## Proposed finite bridge acceptance tests

Before replacing a finite proof with an Ext specialization, require:

1. the Ext theorem is free of `sorry`;
2. the wrapper preserves the existing finite theorem's constant and exact
   hypotheses;
3. no Borel/unbounded/ideal module is pulled into a basic finite build;
4. the old finite proof is retained until the wrapper is build-green;
5. singular-value or UI-norm corollaries continue to use the finite machinery
   rather than being weakened to operator norm.
