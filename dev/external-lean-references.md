# External Lean references — spectral perturbation / Davis–Kahan

A registry of external Lean formalizations that **inspired or informed** results in this
repo, kept for **credit and recognition**. Where a `ForMathlib` proof was derived by reading
one of these, the derived file's header names the source (repo + permalink + retrieval date)
and the correspondence is recorded below.

Our policy here is **distill-and-re-derive, not vendor**: we read the external proof for its
mathematical strategy and write an independent proof in Mathlib idiom against our pinned
toolchain. This sidesteps licensing questions and produces master-compatible code, while the
credit below ensures the original authors are recognized. A local (git-ignored) clone of the
relevant files lives under `dev/reference-repos/` for convenient reference; it is a cache, not
a vendored dependency, and is not committed.

---

## `rjwalters/lean-genius`

- **Repo:** <https://github.com/rjwalters/lean-genius>
- **Referenced commit:** `3e09c97392dc68d068becb89e2068b1830234661` (retrieved 2026-07-04)
- **Nature:** large AI-generated proof corpus (Aristotle-style; `*OQ*` naming). The files are
  standalone research files (`import Mathlib`), pinned to `leanprover/lean4:v4.26.0` + mathlib
  `v4.26.0`. This project is on `v4.31.0-rc2` + mathlib master, so nothing lifts out verbatim;
  we port strategies by hand.
- **License:** none declared (GitHub reports no license; no `LICENSE` in tree as of the commit
  above). We therefore do **not** copy or build against it — only read it and re-derive.
  If the author adds an OSI license later, verbatim reuse could be reconsidered.

### Files referenced (local cache: `dev/reference-repos/lean-genius/proofs/Proofs/`)

| File | Content | Status in source | Used for |
|---|---|---|---|
| `SchurHornMajorization.lean` | Forward Schur–Horn in convex/Karamata form: `diag(T) ≺ spec(T)` via a doubly-stochastic weight matrix `‖⟪vⱼ,eᵢ⟫‖²`, Parseval, row-wise Jensen. Also `schur_trace_eq`, `schur_sum_sq_le`. | sorry-free, axiom-free | Strategy for our forward Schur–Horn (`ForMathlib/…/SchurHorn.lean`) — foundation of Davis's eigenvalue-change bound |
| `CauchyInterlacingKyFan.lean` | Ky Fan partial-sum interlacing / trace-of-compression | sorry-free | Reference for the Ky Fan / partial-sum majorization API |
| `CauchyInterlacingWeyl.lean` | Weyl monotonicity (`weyl_monotone`) and subadditive Weyl (`weyl_add_le`) | 2 sorries (in source) | Reference for Weyl inequalities (we already have `abs_eigenvalues_sub_le_opNorm` in `CourantFischer.lean`) |
| `CauchyInterlacingWeylDual.lean`, `…MajorizationPositivity.lean`, `…Compression/Keystone/Poincare/Assembly.lean` | Cauchy interlacing infrastructure (max–min characterization, compression positivity) | sorry-free (except Weyl) | Reference for the interlacing route to majorization |

### Correspondence to our `ForMathlib`

| Our declaration (`ForMathlib/…/SchurHorn.lean`) | Source declaration read | Relationship |
|---|---|---|
| `convexOn_sum_re_inner_orthonormalBasis_self_le` | `SchurHorn.schur_majorization_convexOn` | same doubly-stochastic-weights + row-Jensen + column-collapse strategy; independently re-derived, reusing this project's `re_inner_map_self_eq_sum_eigenvalues_mul_sq` for the diagonal decomposition. Builds clean on `v4.31.0-rc2`/master, axiom-clean (`propext, Classical.choice, Quot.sound`). |
| `sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues` | `SchurHorn.schur_trace_eq` | trace / equality case |
| `sum_sq_re_inner_orthonormalBasis_self_le_sum_sq_eigenvalues` | `SchurHorn.schur_sum_sq_le` | `φ = (·)²` instance |
| `schurWeight`, `schurWeight_row_sum`, `schurWeight_col_sum` | `SchurHorn.dsWeight`, `dsWeight_row_sum`, `dsWeight_col_sum` | doubly-stochastic weight matrix (indexed eigen×basis) |

---

## `NetRxn/SK_EFT_Hawking`

- **File:** `lean/SKEFTHawking/QuantumNetwork/VectorMajorization.lean`
- **Permalink:** <https://github.com/NetRxn/SK_EFT_Hawking/blob/a55226f613c54b4a272dafa7f2bf8bb2bcca3921/lean/SKEFTHawking/QuantumNetwork/VectorMajorization.lean>
- **Retrieved:** 2026-07-04
- **Nature:** defines `topkSum` / `sortDesc` and proves `topkSum_doublyStochastic_mulVec_le`
  (weak majorization under a doubly-stochastic map). Sorry-free, kernel-pure
  (`{propext, Classical.choice, Quot.sound}`). No majorization *predicate* (defers to Mathlib's
  TODO).
- **Used for:** design reference for a sorted-prefix `topkSum` API — the explicit
  `∀k, ∑_{i<k} d↓ ≤ ∑_{i<k} λ↓` formulation, complementary to lean-genius's convex-function form.

---

## Upstream Mathlib state (as of 2026-07-04, master)

- **No** majorization predicate, **no** `topkSum`, **no** Schur–Horn theorem — only a comment
  motivating it in `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.
- Available ingredients: spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis` /
  `eigenvalues`), Birkhoff / doubly-stochastic (`Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`,
  `exists_eq_sum_perm_of_mem_doublyStochastic`), and Jensen (`ConvexOn.map_sum_le`).
- Consequence: a clean forward Schur–Horn + a `topkSum` majorization API are themselves
  independently PR-able to Mathlib.
