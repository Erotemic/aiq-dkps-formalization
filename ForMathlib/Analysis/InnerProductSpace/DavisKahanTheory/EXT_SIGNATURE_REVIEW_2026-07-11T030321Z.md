# Ext signature issue noticed during the finite-theory audit

Timestamp: 2026-07-11T03:03:21Z

Author/provenance: GPT 5.6 High, acting as the non-Ext agent.

This file is intentionally stored in the finite agent's directory.  No Ext
source was modified.

## `DavisKahanExt.DoubleAngle.sinTwoTheta_residual`

The theorem currently named `sinTwoTheta_residual` has the signature

```lean
(A, U, V, d, InternalGap A U d) ->
  d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖
```

This is a **reflection-defect theorem**, not the residual theorem for an
approximate invariant pair `(X,M)` with residual `A X - X M`.

The distinction matters to finite specialization:
`DavisKahanTheory.generalizedSinTwoTheta_unequalFinrank` is naturally an
isometric-embedding residual statement, so it cannot specialize the current
Ext theorem directly without first constructing a reducing subspace and
relating the reflection defect to the rectangular residual.

## Suggested Ext-agent resolution

Choose one of the following.

1. Rename the current theorem to
   `sinTwoTheta_reflectionDefect` and add a genuine embedding residual theorem;
   or
2. Keep the current name but add a separate theorem such as
   `sinTwoTheta_embeddingResidual` with `X`, `M`, an isometry hypothesis, and a
   rectangular residual conclusion.

The first option is clearer and matches the finite folder's separation between
`sinTwoTheta_residual_le` and `sinTwoTheta_reflectionDefect_le`.
