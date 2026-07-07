# Development Plan: Operator polar decomposition `A = U|A|` + the intertwining unitary

Spun off from the Davis Result-B API gap **BL3** (`decomposition-B.md`). Planning artifacts:
this file, `decomposition-polar.md` (full decomposition + source quotes + adversarial pass),
and the "Polar decomposition" section of `tickets.md`.

## Goal
For `A` an operator on a finite-dimensional inner product space:
1. **Headline (via CFC, ℂ):** `∃ U : H →L[ℂ] H`, `U` a partial isometry, `A = U ∘L CFC.abs A`.
2. **RCLike route (ℝ+ℂ, for Davis):** `A = polarUnitary A ∘ₗ abs A` with `abs A = (A⋆A)^{1/2}` the
   spectral square root; `U` a partial isometry, unitary when `A` is invertible.
3. **Intertwining unitary (Davis §2):** for close projection families `{Pⱼ},{P'ⱼ}`, the canonical
   unitary `W = (P'ⱼPⱼP'ⱼ)^{-1/2}P'ⱼPⱼ` on blocks, with `W Pⱼ = P'ⱼ W`, and `‖𝒞⊥W‖²=∑sin²θᵢ`.
4. **Unblock Davis BL3/BL4** in the parent Result-B project.

## Scope decision (user, 2026-07-04)
Carrier = **hybrid** (CFC-ℂ headline + LinearMap/RCLike route). End-point = **full chain to BL3**.

## References
| Reference | Role |
|-----------|------|
| Horn–Johnson, *Matrix Analysis* 2nd ed., Thm **7.2.6** (p.440), **7.2.7(b)**, **7.3.1** (p.449) | Statements: PSD sqrt, `ker(A⋆A)=ker A`, polar `A=UQ`. PDF present. |
| Conway, *A Course in Functional Analysis* 2nd ed., **VI.3.9** | Route-(ii) isometry proof of `A=U\|A\|`, `ker U=ker A`, partial isometries. |
| Reed–Simon I, **Thm VI.10**; Riesz–Sz.-Nagy **§110/§136** | Corroborating polar-decomposition sources (Davis cites §136). |
| Davis (1963) **§2** (lines 217–312) | The intertwining unitary + angle interpretation. `.tex` present. |
| Davis (1958) §7 | Minimality of `W` — **unavailable → deferred, off critical path.** |

## ★ Proof-route pivot ★
HJ proves 7.3.1 via the **SVD** (`A=VΣW*`), which **mathlib lacks** (SingularValues.lean = singular
*numbers* only). We use the **operator/isometry route (ii)** (Conway VI.3.9): no SVD needed.

## Mathlib Inventory
| Concept | Mathlib status | Action |
|---------|---------------|--------|
| `\|A\| = √(A⋆A)` via CFC | `CFC.abs` (Abs.lean:46), full API, **ℂ / `E →L[ℂ] E` only** | USE (headline) |
| Positive-operator `sqrt` (LinearMap/RCLike) | **ABSENT** (inline only, Positive.lean:544) | BUILD (Sub-dev I) |
| Polar decomposition `A=U\|A\|` | **ABSENT** (all of mathlib) | BUILD (Sub-dev III) |
| Partial isometry | **ABSENT** (no predicate/API) | BUILD (Sub-dev II) |
| SVD factorization | **ABSENT** (only singular values) | AVOID (route ii) |
| Intertwining unitary | **ABSENT** | BUILD (Milestone 2) |
| Spectral projection *operator* | **ABSENT** (eigenbasis exists) | BUILD (prereq I.5) |
| `LinearMap↔CLM` adjoint bridge | `adjoint_toContinuousLinearMap` = **`rfl`** (Adjoint.lean:541) | USE (CFC bridge) |
| `star = adjoint`, `IsStarProjection`, `rankOne`, `eigenvectorBasis`, `isCompl_orthogonal`, `Unitary.linearIsometryEquiv`, `isPositive_adjoint_comp_self` | present (verified names/lines in decomposition-polar.md) | USE |

## File Structure (new — does NOT touch the Davis files)
- `ForMathlib/Analysis/InnerProductSpace/PositiveSqrt.lean` — Sub-dev I (positive sqrt). *skeleton ✓*
- `ForMathlib/Analysis/InnerProductSpace/PartialIsometry.lean` — Sub-dev II. *skeleton ✓*
- `ForMathlib/Analysis/InnerProductSpace/PolarDecomposition.lean` — Sub-dev III + CFC bridge. *skeleton ✓*
- `ForMathlib/Analysis/InnerProductSpace/IntertwiningUnitary.lean` — Milestone 2 (+ spectral proj). *skeleton ✓*

Add each to `ForMathlib.lean` once sorry-free. **Full M1+M2 skeleton `lake build` green** (sorries
only, ~35 sorries across 4 files), verified 2026-07-04.

## Dependency Graph
```
Sub-dev I  (PositiveSqrt) ─┬─────────────→ Sub-dev III (PolarDecomposition, RCLike) ─┬→ CFC bridge (ℂ headline)
Sub-dev II (PartialIsom)  ─┘                                                          └→ invertible unitary ─┐
Sub-dev I.7 (inverse sqrt) ───────────────────────────────────────────────┐                                 │
Spectral projection (I.5, API gap) ────────────────────────────────────────┴→ Milestone 2 (Intertwining) ───┤
                                                                                       Milestone 3 (wire BL3/BL4) ←┘
```
Milestone 1 = {I, II, III, CFC bridge} lands first (self-contained). M2 = {I.5, intertwining}. M3 = wire.

## Generality Decisions
- **`𝕜 : RCLike`** for the LinearMap route (ℝ and ℂ) — Davis's real case is direct, no
  complexification bridge. The CFC headline is necessarily **ℂ** (mathlib's C⋆ instance on CLM).
- **`E →ₗ[𝕜] E`** primary carrier (project-native, matches `EigenvalueChange.lean`), with the CFC
  headline in `E →L[ℂ] E` joined by the definitional adjoint bridge.
- **`IsPartialIsometry`** defined abstractly for `[Monoid R] [StarMul R]` (max generality; serves
  both carriers and any C⋆-algebra).
- **Finite-dimensional** — the polar factor is a genuine (non-closure) construction; Davis is
  finite-dim; matches the whole project. (Infinite-dim `B(H)` is future work.)

## Milestone acceptance
- **M1 done** when PolarDecomposition.lean is sorry-free, `lake build` green, `#print axioms
  ForMathlib.continuousLinearMap_polar_decomposition` clean (`propext, Classical.choice, Quot.sound`).
  ✅ **DONE 2026-07-07** (axiom check verified on all five M1 headline declarations).
- **M2 done** when `intertwiningUnitary` + `WPⱼ=P'ⱼW` + angle interpretation are sorry-free.
  ✅ **DONE 2026-07-07.** Route note: `blockPolar` is derived by *restricting* the assembled
  unitary — surjectivity of each block comes from the intertwining relation, so no
  rank-equality/dimension-count lemma was needed.
- **M3 done** when Davis BL3/BL4 consume `W` (parent Result B unblocked).
  ✅ **DONE 2026-07-07** — `RotationBound.lean` discharges BL1–BL6 (Davis Thm 3.2 + the
  `(γ')²‖𝒞⊥U‖² ≤ 2‖𝒞⊥H‖²` corollary). Result B complete.

## Deferred / flagged
- Davis Thm 2.1/2.3 **minimality** of `W`: source (Davis1958 §7) unavailable, off the BL3 path →
  **not ticketed**; revisit via `/expert-review` only if the user wants the minimality theorems.
