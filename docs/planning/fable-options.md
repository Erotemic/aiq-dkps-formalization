# Fable work options — value to the Mathlib contribution

Written 2026-06-12 (Opus). The old Fable list (`historical/for-fable.md`, F1–F6)
is fully done. These are the *remaining* candidate Fable tasks, each rated by how
much it **strengthens the contribution** under the standing priority: spend effort
on things Mathlib reviewers care about and that strengthen what we have — not
net-new content reviewers won't converge on.

Ranking is by *strengthening per Fable effort*, not raw difficulty.

| # | Task | Effort | Strengthens | Clears the "reviewers care" filter? |
|---|---|---|---|---|
| 1 | **Rank factorization** `Matrix.exists_mul_eq_of_rank_le` | M–L | **High** | ✅ yes |
| 2 | **Davis–Kahan** redesign onto `orthogonalProjection` (R4) | L | **High** (but gated) | ⚠ after Zulip |
| 3 | Courant–Fischer full min-max (R5) | L | Low | ➖ marginal |
| 4 | Two-space Gram **equivalence** (R1b leftover) | M | Low | ➖ marginal |
| 5 | B1 matrix-Bernstein sharp constants | XL | Medium | ✅ but huge effort |

---

## 1. Rank factorization — `Matrix.exists_mul_eq_of_rank_le` (TOP PICK)

**What.** "Any matrix of rank `≤ r` factors as `M = L · R` with `L : m×r`,
`R : r×n`." Discovered as a genuine gap during the R2b recon: Mathlib has the PSD
square root but **no rank factorization at all**.

**How it strengthens.** Two-for-one:
- **A new standalone PR** — rank factorization is textbook-foundational and
  *entirely absent* upstream; exactly the kind of net-new content reviewers *do*
  want (unlike a bespoke redesign).
- **Strengthens the PSD candidate** — it lets the rank-controlled PSD proof drop
  its hand-rolled `Classical.choose`/embedding step (the audit's §2.3 objection)
  in favour of `B = (√B)·(√B)` then rank-factor `√B = L·R`. The PSD proof becomes
  ~5 clean lines instead of the current ~90.

**Why Fable.** A real new construction (basis of the column space / range; express
columns in it), ~M–L. Standard math, but not mechanical.

**Verdict.** Best use of a Fable session under the stated priority: net-new *and*
reviewer-valued *and* it improves an existing candidate. Recommend first.

## 2. Davis–Kahan redesign (R4) — high value but gated on an API decision

**What.** Restate the DK cross-block / projector bounds in terms of Mathlib's
`orthogonalProjection` / spectral-subspace API instead of the bespoke
`spectralProjection` finite sum and DKPS index-cutoffs.

**How it strengthens.** DK is currently staged but **"not PR-ready as-is"** (audit
§4). Without this redesign the DK candidate likely never becomes a PR. R4 is what
turns it from staged infrastructure into a real contribution — and DK is *entirely
absent* from Mathlib, so a clean version is genuinely valuable.

**The catch.** The right statement shape is a *design decision* the audit says
needs human spectral-analysis review (separated spectral sets? invariant
subspaces? projector distance?). Spending Fable before that shape is settled risks
producing a form reviewers won't accept. **Gate on a Zulip decision (D-8) first.**

**Opus warm-start available (cheap, design-neutral):** a bridge lemma proving
`spectralProjection b d = orthogonalProjection (span of the first d eigenvectors)`
would de-risk the redesign with a verified foundation without making the design
call. Worth doing *before* the Fable session if R4 is greenlit.

## 3. Courant–Fischer full min-max (R5) — marginal

**What.** The canonical `λ_k = min over (k+1)-dim subspaces, max Rayleigh`
variational form. Mathlib has only the extremal (largest/smallest) case.

**How it strengthens.** Doesn't strengthen any existing PR — our directional bounds
already suffice for Weyl (the headline). It's a standalone nice-to-have that fills
a Mathlib gap. Pursue only if a reviewer explicitly asks. Low priority.

## 4. Two-space Gram equivalence — marginal

**What.** `E ≃ₗᵢ F` under `finrank E = finrank F`, via a cross-space isometry
extension of orthogonal complements (Mathlib's `LinearIsometry.extend` is
same-space only).

**How it strengthens.** The span-level core already gives the general two-space
result; this is a niche corollary, and the same-space equivalence covers the main
use. Marginal. Needs a small new extension construction.

## 5. B1 matrix-Bernstein sharp constants — high effort

**What.** Replace the loose `n`/`n²` constants in the sample-covariance
eigenvalue-concentration (elementary Chebyshev + union-bound route) with sharp
constants via a matrix Bernstein/Hoeffding inequality.

**How it strengthens.** Sharper constants make the B1 candidate more attractive.
**But** matrix Bernstein is itself a major absent piece — proving it is its own
large contribution (XL). Not worth it unless matrix concentration becomes a
deliberate target.

---

## Bottom line

Under the stated priority, **only #1 (rank factorization) clearly clears the bar**
right now: net-new, reviewer-valued, and it strengthens our PSD candidate. **#2
(Davis–Kahan)** is high-value but should wait for the D-8 Zulip API decision (with
an optional Opus bridge-lemma warm-start). **#3–#5 are marginal or disproportionate
effort** and are not recommended under the current priority.

If the goal stays "get what we have pristine and PR-droppable" rather than adding
scope, a reasonable answer is **no Fable yet** — do #1 only if you want to both
strengthen PSD and add the rank-factorization PR.
