# Mathlib review and readiness audit for headline candidates

Validation anchor for this audit:

- Repository archive: `aiq-dkps-formalization-source-2026-06-12T140903-5-b3b2569cd4ff.tar.gz`
- Git commit: `b3b2569cd4ffaab896d7ee183c673170a09773d8`
- Commit subject: `B2b: Berge value-function continuity + finite-family closeness modulus`
- Audited date: 2026-06-12

This document audits the current headline `ForMathlib` candidates for likely
Mathlib upstream readiness.  The goal is not to certify mathematical novelty or
correctness beyond Lean's kernel.  The goal is to identify what a Mathlib
reviewer is likely to object to before these results are proposed as PRs.

The headline candidates considered here are:

1. Gram rigidity.
2. Rank-controlled PSD Gram realization.
3. Spectral perturbation infrastructure: Courant--Fischer, Weyl, and
   Davis--Kahan-style projector/cross-block estimates.

The current files are proof-complete in the basic sense: the audited headline
files contain no `sorry`, no `admit`, no custom `axiom`, no `unsafe`, and no
lines longer than 100 characters.  However, proof-complete is not the same as
Mathlib-ready.  The main remaining issues are API design, statement shape,
decomposition into reviewable lemmas, proof maintainability, namespace and file
placement, and whether the statements fit existing Mathlib abstractions.

## Executive verdict

| Candidate | Current proof status | Mathlib readiness | Recommended action |
| --- | --- | --- | --- |
| Gram rigidity | Complete, clean, comparator-covered | **Closest to PR-ready** | Make this the first serious upstream target, after statement/API polishing. |
| Rank-controlled PSD Gram realization | Complete, valuable, comparator-covered | **Promising but needs API review** | Second big target; likely needs proof/API reshaping around existing PSD/rank APIs. |
| Courant--Fischer + Weyl | Complete and important | **High value, medium readiness** | Split into smaller PRs; do not bundle with Davis--Kahan initially. |
| Davis--Kahan projector/cross-block bounds | Complete and useful downstream | **Not PR-ready as-is** | Treat as staged infrastructure; needs API redesign and likely human spectral-analysis review. |

The first **big** result to target should be Gram rigidity.  It has
the best combination of mathematical value, statement clarity, proof locality,
and likely reviewer tractability.

## General Mathlib-readiness checklist

Before any PR, each candidate should be converted from a `ForMathlib` staging
file into a Mathlib-style contribution:

- Remove the `ForMathlib` namespace wrapper.
- Use a Mathlib copyright header and the module-system header style.
- Use `public import` / `import` grouping appropriate to the destination file.
- Minimize imports and confirm the target file is the right home.
- Re-check that Mathlib does not already contain the result under another name.
- Add or update module docstrings and declaration docstrings in Mathlib style.
- Replace AI provenance comments in Lean files with normal author/copyright
  metadata; AI provenance belongs in the PR description, not in Mathlib code.
- Confirm theorem names fit local naming conventions.
- Prefer reusable intermediate lemmas over large monolithic proofs.
- Decide whether constants/generalizations are intended API or merely sufficient
  for the downstream DKPS application.
- Verify with a dedicated comparator challenge for the exact theorem family.

## 1. Gram rigidity

Current file:

- `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean`

Current declarations:

- `ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq`
- `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`

### What the theorem says

The core theorem states that if two indexed families of vectors in a
finite-dimensional inner product space have the same pairwise inner products,
then a single linear isometry equivalence maps each vector in the first family
to the corresponding vector in the second family.  The matrix-facing theorem
packages this as equality of `Matrix.gram` matrices.

This is a strong and natural Mathlib candidate: finite configurations are
determined up to linear isometry by their Gram matrix.

### Strengths

- The statement is general over `RCLike 𝕜`.
- The index type `ι` is arbitrary; the proof uses finite-support linear
  combinations rather than assuming `Fintype ι`.
- The proof idea is mathematically appropriate: compare the kernels of the two
  linear-combination maps, build an isometry on the span, extend it, and use
  finite-dimensionality to upgrade to a linear isometry equivalence.
- The `Matrix.gram` theorem is easy to explain and likely useful outside DKPS.
- The file is small, readable, and has no obvious line-length or proof-hole
  style problems.

### Likely reviewer objections

1. **The statement may be less general than Mathlib wants.**

   The current theorem assumes both configurations live in the same ambient
   space `E` and concludes `E ≃ₗᵢ[𝕜] E`.  A more natural core statement may map
   between two possibly different inner product spaces `E` and `F`, at least at
   the level of the spans of the two configurations.  The current theorem can
   then be a corollary when the ambient spaces are the same finite-dimensional
   space.

2. **The useful core should probably be split out.**

   The proof internally constructs an isometry from `span (Set.range φ)` to
   `span (Set.range ψ)`.  That span-level theorem is arguably the fundamental
   result and does not need the same ambient-space assumptions.  A Mathlib PR
   may be better structured as:

   - span-level linear isometry from equality of Gram data;
   - ambient extension theorem as a corollary;
   - `Matrix.gram` iff statement as a final convenience theorem.

3. **The theorem name should be adjusted.**

   `exists_linearIsometryEquiv_map_eq_of_inner_eq` is understandable but very broad.
   A name such as
   `exists_linearIsometryEquiv_map_eq_of_inner_eq` or a `Matrix.gram`-scoped
   name may be easier to find and less likely to collide conceptually with other
   inner-product rigidity statements.

4. **Proof can be made more modular.**

   The current proof is readable, but large enough that reviewers may request
   named intermediate lemmas for:

   - equality of inner products of finite linear combinations;
   - kernel inclusion/equality induced by Gram equality;
   - construction of the induced isometry on quotient/range/span.

### Readiness rating

**A-/B+.**  This is the closest headline candidate to Mathlib quality.  It is
not necessarily PR-ready verbatim, but it is very plausibly one refactor away
from a strong first contribution.

### Recommended Fable task

Ask Fable to produce a Mathlib-shaped refactor, not a new proof from scratch:

- Extract the span-level theorem explicitly.
- Consider a version with two ambient spaces `E` and `F`.
- Keep the same-space finite-dimensional `LinearIsometryEquiv` theorem as a
  corollary.
- Keep the `Matrix.gram` theorem as the public-facing final result.
- Minimize imports and rename declarations according to likely Mathlib style.
- Preserve or improve the existing proof, but split long proof phases into
  reusable lemmas.

## 2. Rank-controlled PSD Gram realization

Current file:

- `ForMathlib/LinearAlgebra/Matrix/PosDef.lean`

Current declarations:

- `ForMathlib.Matrix.isHermitian_entry_eq_sum_eigenvalues`
- `ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`

### What the theorem says

For a square matrix `B : Matrix (Fin n) (Fin n) 𝕜`,

```lean
B.PosSemidef ∧ B.rank ≤ d ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A
```

over `RCLike 𝕜`.  Equivalently, a PSD matrix of rank at most `d` is the Gram
matrix of `n` vectors in `𝕜^d`.

### Strengths

- The statement is broadly useful: Gram matrices, PSD matrices, finite-rank
  realization, classical MDS, and finite-dimensional geometry all need this
  kind of result.
- The statement is already generalized to `RCLike 𝕜`.
- The reverse direction uses standard rank/PSD facts.
- The forward direction is mathematically direct and transparent: spectral
  decomposition plus packing nonzero eigen-directions into `Fin d`.
- The theorem is included in the passing headline comparator challenge.

### Likely reviewer objections

1. **This may duplicate or be derivable from existing factorization APIs.**

   Mathlib already has substantial PSD and matrix factorization infrastructure.
   Before opening a PR, re-check whether a square factorization theorem or a
   rank-factorization theorem can produce this result with less spectral
   machinery.  A reviewer may prefer a proof through existing API rather than a
   hand-rolled spectral reconstruction.

2. **The helper theorem may be too specialized or in the wrong file.**

   `isHermitian_entry_eq_sum_eigenvalues` is useful, but it may belong in
   `Mathlib/Analysis/Matrix/Spectrum.lean` rather than `PosDef.lean`.  The PSD
   factorization theorem may then import that helper or avoid it entirely.

3. **The proof uses low-level choice/embedding construction.**

   The proof embeds the subtype of nonzero eigenvalues into `Fin d` and then
   defines `A` using `Classical.choose`.  This is acceptable to Lean, but may be
   considered less maintainable than a construction through an existing
   equivalence, basis, or factorization API.

4. **The theorem name is verbose and conjunctive.**

   The current name mirrors the statement, but Mathlib may prefer one-direction
   names plus an iff theorem, for example:

   - `Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le`
   - `Matrix.rank_le_of_eq_conjTranspose_mul_self`
   - an iff theorem if both directions are genuinely desired.

5. **The destination is not obvious.**

   The theorem is about PSD matrices, rank, and Gram realization.  It could
   plausibly live near `Matrix.PosSemidef`, `Matrix.gram`, or matrix rank
   factorization material.  Ask on Zulip before choosing a final destination.

### Readiness rating

**B-/C+.**  The theorem is valuable and proof-complete, but the proof and API
shape probably need human review before a PR.  It is a good second big target,
not the first.

### Recommended Fable task

Ask Fable to explore alternative Mathlib-shaped proofs:

- Search existing Mathlib APIs for PSD square-root/factorization and rank
  factorization lemmas.
- Try to reprove the theorem using existing factorization lemmas before using
  spectral expansion.
- Split the two directions into separately named lemmas.
- Move spectral-entry helper material into a spectrum-focused location, or avoid
  needing it in the PSD PR.
- Produce a minimal-import version and a proposed destination-file diff.

## 3. Courant--Fischer and Weyl spectral perturbation

Current files:

- `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean`
- `ForMathlib/Analysis/InnerProductSpace/Spectrum.lean`

Current declarations most relevant to the headline result:

- `ForMathlib.re_inner_map_self_eq_sum_eigenvalues_mul_sq`
- `ForMathlib.exists_unit_vector_re_inner_le_eigenvalue`
- `ForMathlib.forall_unit_vector_eigenvalue_le_re_inner`
- `ForMathlib.abs_eigenvalues_sub_le`
- `ForMathlib.inner_eigenvectorBasis_map_sub_eigenvectorBasis`

### What the theorem stack says

This stack supplies the finite-dimensional spectral perturbation infrastructure
needed for DKPS: diagonalization of the quadratic form in the eigenbasis,
discrete Courant--Fischer bounds for sorted eigenvalues, Weyl's eigenvalue
perturbation inequality, and a cross-term identity used by Davis--Kahan-style
arguments.

### Strengths

- This is high-value mathematical infrastructure.  Mathlib users working with
  self-adjoint/symmetric operators, random matrices, PCA, MDS, or perturbation
  theory can plausibly reuse it.
- The code builds directly on Mathlib's `LinearMap.IsSymmetric.eigenvalues` and
  `eigenvectorBasis` APIs.
- The main Weyl theorem is cleanly stated in terms of sorted eigenvalues.
- The cross-term identity is small, elegant, and likely independently
  upstreamable.

### Likely reviewer objections

1. **This is too large for one PR.**

   Courant--Fischer, Weyl, and Davis--Kahan should not be bundled into a single
   first spectral PR.  The likely sequence is:

   1. cross-term identity;
   2. quadratic-form diagonalization;
   3. Courant--Fischer directional bounds;
   4. Weyl perturbation;
   5. Davis--Kahan-style corollaries.

2. **The statement may not use the preferred operator-norm API.**

   The current Weyl theorem assumes

   ```lean
   ∀ x, ‖(T - S) x‖ ≤ ε * ‖x‖
   ```

   This is convenient and avoids additional continuity/API issues, but a
   reviewer may prefer a theorem phrased using an operator norm of a continuous
   linear map, or at least a corollary in that form.

3. **The `finrank = n` / `Fin n` indexing style may need discussion.**

   The current statement fits Mathlib's existing sorted-eigenvalue API, but it
   is still somewhat heavy.  Confirm with reviewers whether this is the desired
   public shape.

4. **`specSubspace` may be local scaffolding, not public API.**

   The helper `specSubspace` is a convenient proof device.  It may be better as
   a private/local definition unless reviewers want a public spectral-subspace
   API.

5. **The constants are sufficient but not necessarily canonical.**

   The Weyl theorem itself is canonical.  Some downstream bounds are deliberately
   conservative.  Separate canonical theorems from application-sufficient
   estimates.

### Readiness rating

**B for Courant--Fischer/Weyl after splitting; C for the whole spectral stack.**
The material is very valuable, but should be decomposed before PR.  The
cross-term identity may be a small early spectral PR.  The full stack should
wait until reviewers agree on statement shape and destination files.

### Recommended Fable task

Ask Fable for a PR decomposition rather than a monolithic patch:

- Isolate `inner_eigenvectorBasis_map_sub_eigenvectorBasis` as a tiny PR.
- Isolate `re_inner_map_self_eq_sum_eigenvalues_mul_sq` as a quadratic-form
  diagonalization theorem.
- Refactor Courant--Fischer into minimal public theorem statements plus private
  proof helpers.
- Provide a Weyl theorem in the current hypothesis form and, if feasible, a
  corollary using Mathlib's preferred normed-operator API.
- Prepare comparator challenges for each stage separately.

## 4. Davis--Kahan projector/cross-block bounds

Current file:

- `ForMathlib/Analysis/InnerProductSpace/DavisKahan.lean`

Relevant declarations:

- `ForMathlib.sum_norm_inner_eigenvectorBasis_map_sub_sq_le`
- `ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le`
- `ForMathlib.gap_of_rank_floor`
- `ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor`
- `ForMathlib.Orthonormal.starProjection_span_image_apply`
- `ForMathlib.sum_norm_sub_starProjection_span_sq_eq`
- `ForMathlib.sum_norm_sub_starProjection_span_sq_le`

### What this material says

This file proves cross-block and projector-form Davis--Kahan-style bounds.  It
controls overlap between spectral subspaces of two close symmetric operators
under a spectral gap condition, and converts that into a projector-distance
bound in the real case.

### Strengths

- This is genuinely substantial formalization-resistant material.
- It is downstream-important: this is one of the bridges from matrix
  perturbation to embedding alignment.
- The proofs are explicit and rely on the staged Weyl/Courant--Fischer stack.
- The projector identity is mathematically meaningful and likely useful.

### Likely reviewer objections

1. **The API is not yet Mathlib-shaped.**

   Mathlib may prefer spectral projections expressed using existing projection,
   submodule, or continuous-linear-map APIs rather than a bespoke finite-sum
   `spectralProjection` definition.

2. **The statement is too application-shaped.**

   The gap hypothesis is written as a pairwise bound over indices split by a
   cutoff `d`.  This is exactly what the DKPS proof needs, but not necessarily
   the most reusable Davis--Kahan theorem statement.  Reviewers may prefer a
   formulation in terms of separated spectral sets, invariant subspaces, or
   projection operators.

3. **The real-only projector form needs justification.**

   The cross-block material is more general, but the projector-form theorem is
   currently in a real namespace.  That may be fine for a first result, but a
   Mathlib API discussion should decide whether the correct target is real only
   or `RCLike`.

4. **This depends on earlier spectral infrastructure.**

   It should not be upstreamed before the cross-term identity, Courant--Fischer,
   and Weyl pieces are accepted or at least reviewed.

### Readiness rating

**C.**  This is an impressive formalization result, but not a first Mathlib PR
in its current form.  Treat it as a major staged result and a downstream
validation of the spectral stack.  Do not lead with it as the first upstreaming
attempt.

### Recommended Fable task

Ask Fable to produce a design note and alternative statement shapes:

- Formulate a reusable Davis--Kahan theorem independent of DKPS cutoffs.
- Explore whether existing Mathlib projection APIs can replace the custom
  `spectralProjection` definition.
- Separate cross-block energy lemmas from projector-distance corollaries.
- Produce a minimal dependency graph showing exactly which spectral PRs must
  land first.
- Do not optimize constants until the API shape is accepted.

## Challenge status and trust model

The comparator challenges are useful for review, but they do not establish that
a theorem is Mathlib-quality.  They establish that the solution proves exactly
the public challenge statement using only permitted axioms.

Current trusted headline coverage:

- Gram rigidity: covered by the headline challenge.
- Rank-controlled PSD Gram realization: covered by the headline challenge.
- Weyl perturbation: covered by the headline challenge.

The broad inventory challenge is useful as an audit artifact, not as a PR plan.
It should remain clearly labeled as an inventory.  Recent/provisional staged
items, especially spectral-transform/CFC measurability, should not be presented
as headline claims until their statement shape has been reviewed.

## Recommended upstreaming sequence

### First serious PR track: Gram rigidity

1. Ask on Zulip whether the community prefers a same-ambient-space theorem or a
   span-level theorem between two spaces.
2. Refactor the proof around the preferred core theorem.
3. Add a dedicated comparator challenge for this family.
4. Prepare a small PR with only the Gram-rigidity theorem family.

### Second serious PR track: PSD Gram realization

1. Re-check existing PSD factorization and rank APIs.
2. Decide destination file with reviewer input.
3. Split forward/backward directions if useful.
4. Avoid bundling spectral-entry helper material unless necessary.

### Third serious PR track: spectral perturbation

1. Cross-term identity.
2. Quadratic-form diagonalization.
3. Courant--Fischer bounds.
4. Weyl perturbation.
5. Davis--Kahan-style corollaries after API discussion.

## Concrete next tasks for Fable

Use Fable for targeted cleanup rather than broad theorem proving:

1. **Gram PR refactor.**
   Produce a Mathlib-shaped patch for Gram rigidity with a span-level theorem,
   same-ambient corollary, and `Matrix.gram` iff theorem.

2. **PSD API search and alternate proof.**
   Search existing Mathlib APIs and attempt a proof of rank-controlled PSD
   factorization using existing factorization/rank lemmas rather than explicit
   spectral expansion.  If not possible, justify the spectral proof and split
   helpers.

3. **Spectral PR decomposition.**
   Split the spectral perturbation stack into PR-sized files and produce a
   dependency plan.  Include candidate theorem names and destination files.

4. **Davis--Kahan redesign note.**
   Produce alternative theorem statements for Davis--Kahan in terms of spectral
   subspaces/projections rather than DKPS cutoffs, and identify which form is
   most compatible with existing Mathlib APIs.

5. **Comparator cleanup.**
   Keep dedicated challenge files for each headline family.  Do not use the
   inventory challenge as evidence of Mathlib readiness without human review of
   each statement.

## Bottom line

The current headline proofs are real and substantial, but they are not all
Mathlib-quality as-is.  Gram rigidity is the best first big target.
PSD Gram realization is the best second target after API review.  The spectral
stack is probably the highest-value long-term contribution, but it must be
split carefully.  Davis--Kahan is the most impressive downstream result, but it
needs API redesign before it should be proposed upstream.
