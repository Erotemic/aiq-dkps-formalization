# Decomposition — Davis's eigenvalue-change lower bound + sharper total-rotation

Source of truth for the statements below: **Davis (1963), Theorem 4.1** ("A Lower
Bound for the Change in Eigenvalues"), transcribed from
`ForMathlib/prose/non-distributable/Davis-1963-Rotation-of-Eigenvecvtors-by-Perturbation.tex`,
lines 641–754. Companion digest: `ForMathlib/prose/Davis-1963-core-arguments.tex` §5.

Status: **skeleton built, L1 proven.** `ForMathlib/Analysis/InnerProductSpace/EigenvalueChange.lean`
compiles clean (4 sorries: L2/L3/L4/L5). L1 (`two_mul_sq_le_sum_sq_sub_perm`) is proven and
axiom-clean. Ticket board: `.mathlib-quality/tickets.md`. Forward Schur–Horn (`SchurHorn.lean`)
is built and feeds L3 (its doubly-stochastic weights), but is *not* itself the direction this
proof needs — the bound runs on the convex-hull/Birkhoff direction (§1, L3).

---

## §0. Central modelling decision (needs approval before skeleton)

Davis runs the whole proof "in the real Hilbert space 𝓕 of Hermitian matrices under
Frobenius norm" (line 667). But **every matrix that appears — `B`, `C`, `Bπ` — is
diagonal in `A`'s eigenbasis** (`B` = eigenvectors of `A`, eigenvalues `λ'`; `C = A + 𝒞H`
is `A` plus the diagonal part of `H`; `Bπ` = `B` with eigenvalues permuted). The pinching
subspace `𝒞𝓕` is exactly the diagonal matrices ≅ ℝⁿ, and the Frobenius inner product on
them is the Euclidean inner product on the diagonals.

**Decision: prove the geometric core as a standalone statement about vectors in
`EuclideanSpace ℝ (Fin n)`** (the diagonal-of-`A`'s-eigenbasis coordinates), then wrap it
in an operator-level statement (`T`, `S` self-adjoint on `E`, using `hT.eigenvalues`)
matching the existing `DavisKahan.lean` / `SchurHorn.lean` API for downstream use. This
avoids formalising a matrix Hilbert space `𝓕` and the pinching projector as objects, which
would be large overhead for no mathematical content Davis actually uses.

Correspondence (`w := λ'` the eigenvalues of `A+H`, `c :=` diagonal of `A+H` in `A`'s
eigenbasis `= λ + diag H`):
- `B ↔ w`, `Bπ ↔ w ∘ π`, `C ↔ c`, `A ↔ λ` (eigenvalues of `A`)
- `‖B−C‖²_F = ‖w − c‖²`, `⟨B−C, B⟩_F = ⟪w − c, w⟫`
- `Δ = B − A ↔ w − λ`, so `‖Δ‖²_F = ∑ᵢ(λ'ᵢ − λᵢ)²`
- `‖𝒞H‖²_F = ∑ᵢ (diag H)ᵢ² = ‖c − λ‖²`; `‖𝒞⊥H‖²_F = ‖H‖²_F − ‖𝒞H‖²_F`

---

## §1. Result A — eigenvalue-change lower bound (Davis Thm 4.1)

### Plain-English proof (transcribed from Davis, lines 666–753)

Work in ℝⁿ via §0. Normalise `‖w‖² = ∑λ'ᵢ² = 1`. Set `c =` diagonal of `A+H`, `Δ = w − λ`.

**Part 1 (geometric, eq. 4.2).** Prove `⟪w − c, w⟫ / ‖w − c‖ ≥ γ/√2`, where
`γ = minᵢ≠ⱼ |wᵢ − wⱼ| > 0` is the eigen-separation of `A+H`.

- `c` is the diagonal of `A+H`, and `A+H` is unitarily conjugate to `diag w`. Hence
  `c = D · w` with `D` the doubly-stochastic matrix `Dᵢⱼ = |Uᵢⱼ|²`. By **Birkhoff**,
  `D ∈ convexHull {permutation matrices}`, so `c ∈ convexHull {w ∘ π : π ∈ Sₙ}` — a convex
  polytope whose vertices `w ∘ π` all lie on the sphere `‖w ∘ π‖ = ‖w‖ = 1` (line 689–696).
- The function `g(c) = γ‖w − c‖ − √2⟪w − c, w⟫` is **convex** in `c` (norm term convex,
  inner term affine). A convex function on a convex hull attains its max at a generating
  point, so it suffices to show `g(w ∘ π) ≤ 0` for every `π` (line 700–702).
- For `π = id`, `g(w) = 0`. For `π ≠ id`: using `‖w‖=1`,
  `⟪w − w∘π, w⟫ = 1 − ⟪w∘π, w⟫ = ½‖w − w∘π‖²`, so
  `g(w∘π) = ‖w−w∘π‖·(γ − ‖w−w∘π‖/√2) ≤ 0 ⟺ ‖w − w∘π‖² ≥ 2γ²`.
- **Combinatorial core:** for distinct `w` with min-gap `γ` and `π ≠ id`,
  `∑ᵢ(w_{π(i)} − wᵢ)² ≥ 2γ²`, with equality for the transposition of a closest pair
  (line 705–708). This gives `g(w∘π) ≤ 0` at every vertex, hence (4.2).

**Part 2 (algebra, lines 716–753).** Fix `w`, `c`. From `Δ + (c − w) = c − λ = diag H`
(the pinching), `‖Δ‖² − ‖diag H‖² = −2⟪c − w, diag H⟫ + ‖w − c‖²`. Over `diag H` of norm
`≤ γ/√2`, the RHS is minimised at `diag H = γ(c−w)/(√2‖w−c‖)`, giving
`‖Δ‖² − ‖diag H‖² ≥ −√2 γ‖w−c‖ + ‖w−c‖²`. Add `‖𝒞⊥H‖² = ‖A+H‖² − ‖c‖² = 1 − ‖c‖²`;
the target `‖Δ‖² ≥ ‖diag H‖² − ‖𝒞⊥H‖²` reduces to
`−√2γ‖w−c‖ + ‖w−c‖² + 1 − ‖c‖² ≥ 0`. Since `‖w−c‖² + 1 − ‖c‖² = 2⟪w−c, w⟫`, this is
exactly `⟪w−c,w⟫/‖w−c‖ ≥ γ/√2`, i.e. (4.2). ∎

### Ordered lemmas

- **L1** (leaf, combinatorial — the crux): `two_mul_sq_le_sum_sq_sub_perm`
  - Statement (ℝⁿ): for `w : Fin n → ℝ` injective, `γ` with `∀ i≠j, γ ≤ |w i − w j|`,
    `π : Equiv.Perm (Fin n)`, `π ≠ 1`: `2 * γ^2 ≤ ∑ i, (w (π i) − w i)^2`.
  - Source (verbatim, lines 705–708):
    > "To maximize the angle between −B and Bπ−B, both vertices being on the unit sphere,
    > is the same as to minimize ‖Bπ−B‖² = ∑ᵢ(λ'_{π(i)}−λ'ᵢ)². It is known exactly what π
    > accomplishes this: π must exchange two λ'ᵢ which differ by exactly γ, and leave every
    > other i fixed. For this π, ‖Bπ−B‖ = √2γ, clearly."
  - Discharge: **no mathlib lemma** — genuinely new but elementary and finite. Proof: a
    non-identity `π` moves some pair; reduce `∑(w_{π i} − w_i)²` to `2(‖w‖² − ⟪w∘π,w⟫)` and
    bound `⟪w∘π,w⟫ ≤ ‖w‖² − γ²` via a rearrangement / exchange argument. Self-contained.
  - This is the one real leaf that needs a from-scratch proof; ~40–80 LOC estimated.

- **L2** (leaf, mathlib): `perm_vertex_convex_bound` — the vertex inequality at a fixed `π`
  and its convex-hull promotion.
  - Uses `ConvexOn.le_sup_of_mem_convexHull` (Mathlib/Analysis/Convex/Jensen.lean:341,
    verified) to reduce `g(c) ≤ 0` for `c ∈ convexHull V` to `g(v) ≤ 0` for `v ∈ V`, plus
    convexity of `x ↦ ‖w − x‖` (`convexOn_norm` / `ConvexOn.comp_affineMap`) and L1.
  - Source: lines 700–702 (the convexity-⟹-vertex argument), verbatim:
    > "Now γ‖B−C‖ − √2⟨B−C,B⟩ is a convex function of C, so if it is ever positive for C in
    > the polytope it must be so at some vertex; at C=B it is not; so consider C=Bπ≠B."

- **L3** (internal, Birkhoff bridge): `mem_convexHull_perm_orbit_of_diag_conj`
  - Statement: the diagonal (in `A`'s eigenbasis) of a self-adjoint operator with spectrum
    `w` lies in `convexHull {w ∘ π}`.
  - Sub-decomposition:
    - **L3.1** (leaf, project): the weight matrix `Dᵢⱼ = ‖⟪vⱼ, e i⟫‖²` is doubly stochastic
      — already have `schurWeight_row_sum` / `schurWeight_col_sum` in `SchurHorn.lean`.
    - **L3.2** (leaf, mathlib): `doublyStochastic_eq_convexHull_permMatrix`
      (Mathlib/Analysis/Convex/Birkhoff.lean:165, verified) + `permMatrix_mulVec`
      (Mathlib/LinearAlgebra/Matrix/Permutation.lean:74, verified): a doubly-stochastic
      `D` has `D · w ∈ convexHull {P_π · w} = convexHull {w ∘ π}`.
    - **L3.3** (leaf, project): the diagonal `c = D · w` — this is exactly
      `re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul` (SchurHorn.lean) read as a
      matrix–vector product.
  - Source: lines 689–696, verbatim:
    > "C is the pinching to 𝒞𝓕 of a hermitian matrix (namely A+H) which is
    > unitary-equivalent to B∈𝒞𝓕. This is known [Horn1954,Davis1959] to imply that
    > C = ∑_π a_π Bπ; here π runs over the permutations … a_π ≥ 0 and ∑ a_π = 1."
  - NOTE: this is the **convex-hull / Rado direction** of Schur–Horn, distinct from the
    Karamata/majorization direction in `SchurHorn.lean`. Mathlib has no
    majorization↔convexHull bridge, but we get convexHull membership *directly* from
    Birkhoff, sidestepping any majorization predicate.

- **L4** (leaf, algebra): `sq_norm_delta_ge` — Part 2, the pure inner-product manipulation
  in ℝⁿ deriving the target from (4.2). Discharge: `inner_sub_left`/`inner_sub_right`,
  `norm_sub_sq_real`, `real_inner_self_eq_norm_sq`, and the "minimise over `diag H`" step
  (Cauchy–Schwarz `⟪c−w, diag H⟫ ≤ ‖c−w‖·‖diag H‖`). ~50 LOC.

- **L5** (top-level, operator wrapper): `sum_sq_eigenvalues_sub_ge` — restate for `T, S`
  self-adjoint on `E`, `‖𝒞(S−T)‖_F` etc. in the existing `hT.eigenvalues` idiom, applying
  L1–L4 to `w = hS.eigenvalues`, `c = diag of S in T's eigenbasis`.

## §2. Result B — sharper total-rotation estimate (Davis Thm 3.2 + 3.3)

Combines Result A with Davis's Thm 3.2 cross-term/Rayleigh estimate
`(γ')²‖𝒞⊥U‖²_F ≤ ‖H‖²_F − ∑(λᵢ−λ'ᵢ)²`. The `‖H‖²_F = ‖𝒞H‖²_F + ‖𝒞⊥H‖²_F` split
(line 608) plus Result A gives `(γ')²‖𝒞⊥U‖²_F ≤ 2‖𝒞⊥H‖²_F` (digest §5, line 293–297).
Depends on the **canonical matching unitary** `U` (polar factor of `Pⱼ P̂ⱼ Pⱼ`) — a
separate sub-development, decompose after Result A is built.

---

## §3. Feasibility assessment

**Feasible, bounded, no multi-week Mathlib gap.** The proof reduces cleanly to
`EuclideanSpace ℝ (Fin n)`; the only external ingredients are Birkhoff (present:
`doublyStochastic_eq_convexHull_permMatrix`), convex-max-on-hull (present:
`ConvexOn.le_sup_of_mem_convexHull`), and Jensen (present). No majorization predicate is
needed. The single genuinely-new leaf is the elementary combinatorial bound **L1**
(`2γ² ≤ ∑(w_{πi}−wᵢ)²` for `π≠id`), which is finite and self-contained.

Result A is the priority (the stated target). Result B additionally needs the matching
unitary, which is best scoped as its own decomposition once A lands.
