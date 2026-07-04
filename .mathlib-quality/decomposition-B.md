# Decomposition — Result B: Davis's sharper total-rotation estimate (Thm 3.2)

Source of truth: **Davis (1963)**, §3 "The Total Amount of Rotation", Theorem 3.2 (eq. 3.1),
transcribed from `ForMathlib/prose/non-distributable/Davis-1963-...tex` lines 510–640, plus
§2 (canonical matching unitary, lines 217–320). Companion digest `Davis-1963-core-arguments.tex`
§4–5.

Status: **decomposition only.** Surfaces a large Mathlib API gap (operator polar decomposition)
that gates the whole result. Result A (`sum_sq_eigenvalues_sub_ge`) is complete and feeds the
final combination step.

## Target

**Theorem 3.2 (Davis, eq. 3.1).** `A` self-adjoint with simple spectrum, gaps ≥ `γ`,
`‖H‖_op < γ/2`. Then `(γ')² ‖𝒞⊥U‖²_F ≤ ‖H‖²_F − ∑ᵢ(λᵢ − λ'ᵢ)²`, where `U` is the canonical
matching unitary and `γ'² = minᵢ{γᵢ² − (λ'ᵢ − λᵢ)²}`, `γᵢ = min_{j≠i}|λᵢ − λ'ⱼ|`.

**Corollary (the payoff, digest §5).** Combining with Result A (Thm 4.1):
`(γ')² ‖𝒞⊥U‖²_F ≤ 2‖𝒞⊥H‖²_F` — eigenvector rotation controlled by the *off-diagonal* part of `H`.

## Proof structure (transcribed from Davis §3, lines 577–640)

`‖𝒞⊥U‖²_F = ∑ᵢ sin²θᵢ` where `θᵢ = arccos⟨Uxᵢ, xᵢ⟩` are the rotation angles of the canonical
unitary `U` (polar factor of `PⱼP̂ⱼPⱼ`, §2). The estimate comes from running the Thm-2.1
Rayleigh-quotient comparison on `⟨(A + 𝒞H − λ'ᵢ)² xᵢ, xᵢ⟩`, computed two ways (the cross-term
with `𝒞⊥H` vanishes because `𝒞H` is diagonal in the old eigenbasis), and retaining the
eigenvalue-displacement term `∑(λᵢ − λ'ᵢ)²`.

## Decomposition tree

- **BL1** (leaf, cross-term): the identity `⟨(A + 𝒞H − λ'ᵢ)² xᵢ, xᵢ⟩ = (λᵢ − λ'ᵢ)² + ⟨(𝒞⊥H)² xᵢ, xᵢ⟩`.
  - Discharge: extends this project's `inner_eigenvectorBasis_map_sub_eigenvectorBasis`
    (Spectrum.lean) + the pinching split `H = 𝒞H + 𝒞⊥H`. Feasible from existing infra.

- **BL2** (leaf, Rayleigh lower bound): `⟨(A + 𝒞H − λ'ᵢ)² xᵢ, xᵢ⟩ ≥ (λᵢ − λ'ᵢ)² + (γ')² sin²θᵢ`.
  - Discharge: the two-sided Rayleigh comparison, cf. `CourantFischer.lean`
    `re_inner_map_self_le/ge_of_mem_specSubspace`. Feasible.

- **BL3** ⚠️ **API GAP (large): the canonical matching unitary `U`.**
  - `U` is defined (Davis §2, lines 217–320) by `U Pⱼ = (P'ⱼPⱼP'ⱼ)^{-1/2} P'ⱼPⱼ`, the **polar
    factor** of `P'ⱼPⱼ` on each spectral block, satisfying `U Pⱼ = P'ⱼ U` and minimising the
    Frobenius displacement among intertwining unitaries.
  - **Mathlib has NO polar decomposition and NO partial-isometry API** (grep-confirmed 2026-07-04:
    empty for `polarDecomposition`, `PartialIsometry` across all of Mathlib). It has the CFC
    building blocks (`CFC.sqrt`, `abs`, `rpow` on the CStar/positive-operator side), but not
    `A = U|A|`, not the inverse square root on a range, not the intertwining-unitary construction.
  - This is a **substantial standalone development** (operator polar decomposition in
    finite-dim inner product spaces + its API), of a scale worth its own project and a
    plausible Mathlib contribution in its own right. It is the gating blocker for BL4/BL5.

- **BL4** (leaf): `‖𝒞⊥U‖²_F = ∑ᵢ sin²θᵢ` (rotation-angle interpretation of the off-diagonal
  Frobenius norm of `U`). Depends on BL3 (needs `U` and its angles `θᵢ`).

- **BL5** (top-level): assemble BL1+BL2 over all blocks, retain the displacement term, get eq. 3.1.
  Depends on BL1–BL4.

- **BL6** (corollary): combine BL5 with Result A (`sum_sq_eigenvalues_sub_ge`) and
  `‖H‖²_F = ‖𝒞H‖²_F + ‖𝒞⊥H‖²_F` to get `(γ')²‖𝒞⊥U‖²_F ≤ 2‖𝒞⊥H‖²_F`. Depends on BL5 + Result A.

## Feasibility assessment

BL1, BL2, BL5, BL6 are feasible from existing project + Mathlib infrastructure (cross-term
identity, Rayleigh comparison, Result A). **The whole result is gated on BL3 — operator polar
decomposition — which Mathlib entirely lacks.** This is not a small leaf; it is a real
sub-development (the abstract polar decomposition `A = U|A|` with `|A| = √(A*A)` via CFC, the
partial isometry `U`, and the specialisation to the intertwining unitary of two projection
families). Recommended: scope BL3 as its own `/develop` project (operator polar decomposition
→ Mathlib), and only then resume Result B's BL1–BL6.

This is the expected, correct outcome of the decomposition pass: Result B's headline is a short
combination, but its foundation (the matching unitary) is a genuine API gap, and surfacing that
— rather than inventing a convenient leaf — is the deliverable.
