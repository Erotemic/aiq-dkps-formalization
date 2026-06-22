# Lessons learned

Effortful-debug postmortems, **newest first**. Each entry is written so its
symptom keywords match what you'd grep for from *inside* the bug. Standalone
per-incident files are preferred for focused lessons (link them from
[`index.md`](index.md)); short or cross-cutting lessons accumulate here.

Canonical entry shape: **Symptom / What it was NOT / Root cause / Fix /
Takeaway**.

---

## 2026-06-14 — Theorem placement: by dependencies, not theme or first use (we got this wrong ≥3×)

@wwylele on PR #40567: *"This theorem doesn't involve `Orthonormal`, which is what
this file is about. Can this be moved to an earlier file?"* —
`inner_linearCombination_linearCombination` had moved `GramMatrix.lean` →
`Orthonormal.lean` → (finally) `Basic.lean`. **Three homes for one lemma.** Jon
flagged that we've gotten placement wrong in many cases and asked to preempt it.

### Root cause of every wrong placement
We located the lemma by the wrong signal each time:
- in `GramMatrix.lean` because that's where it was **first used** (usage ≠ home);
- in `Orthonormal.lean` because it **resembled** `Orthonormal.inner_finsupp_eq_sum_left`
  (superficial similarity ≠ shared dependencies; that lemma is specialized, ours
  is general);
- the right home, `Basic.lean`, is where its **dependencies** live
  (`Finsupp.sum_inner`, `inner_smul_left`) and which already `open`s
  `Finsupp`/`ComplexConjugate` — so the move was even import-free.

### The rule (full operational version in `../mathlib-proof-polishing.md`)
Place by **dependencies**, in order: (1) dependency floor — at/after the latest
decl the statement+proof use; (2) **concept test** — does it *involve* the file's
central concept? a `Foo.lean` is a promise its public contents are about `Foo`;
(3) earliest viable file with the needed opens and **no new heavy import**;
(4) import-cost veto — a heavy new import into a foundational file means it belongs
later/more-specialized (the `…→ LinearMap.lean?` question, answered "no" by the
`Finsupp`/`Isomorphisms` import delta). For a NEW file you author: every *public*
decl must belong to the file's concept — else `private` it or move it (we just
`private`d `CourantFischer`'s `specSubspace`, a general orthonormal-span helper).

### Takeaway
"What is this about / where did I first use it / what does it look like" are all
**non-locators**. The locator is "what is it built from, and what's the earliest
file that already has those without a new heavy import."

---

## 2026-06-14 — Terminal `simp`: collapse the explicit list, don't pin it (corrects my own golf)

@wwylele on PR #40567 replaced what I had golfed to
`simpa only [LinearEquiv.trans_apply, …six @[simp] bookkeeping lemmas…]
using (inner_linearCombination_eq_of_inner_eq h c c').symm`
with simply
`simp [inner_linearCombination_eq_of_inner_eq h c c']`.

### What I got wrong
My golf had turned `simp only [list]; exact fact.symm` into `simpa only [list]
using fact.symm` — a *half* step. I kept (a) the explicit six-lemma list and (b)
the `.symm`. Both were removable:
- The six lemmas (`trans_apply`, `quotKerEquivRange_symm_apply_image`,
  `mkQ_apply`, `quotEquivOfEq_mk`, `quotKerEquivRange_apply_mk`, `coe_inner`)
  are **all `@[simp]`** — the default simp set already contains them; listing
  them is noise that hides the one thing that matters (the math fact).
- `simp` **orients equalities**, so `.symm` is unneeded.
- This is a **terminal** simp (it closes the goal) → vendored golfing rule **1.15**
  ("terminal `simp only` → `simp`") already said to unsqueeze it. I had the rule
  in `mathlib-quality-adapter.md` and didn't apply it.

### The rule (and the correction)
**Terminal simp closing with one fact ⇒ `simp [fact]`** — drop the reconstructed
`@[simp]` list *and* the `.symm`. This **corrects** the "pin a stable explicit
`simp only` set; don't ship a bare `simp`" guidance I'd written: that applies only
to **non-terminal** simps, where a later `rw`/`refine`/`simp` depends on the exact
normal form. For a terminal goal there is no downstream fragility — the short
`simp [fact]` is preferred and is the Mathlib house style.

### Scope check (don't over-apply)
The other `simp only […]` blocks in the polished files (NearIsometry,
SpectralFunctionMeasurable) are **non-terminal** — a subsequent tactic consumes
the normalized form — so they correctly stay explicit. `simpa only [gram_apply]
using congrFun₂ hg i j` keeps its single *deliberately-named* unfold (it reads
"unfold `gram`, then it's the hypothesis", not redundant bookkeeping). Only the
one genuine instance changed. Recorded in
[`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md).

---

## 2026-06-14 — Maintainer follow-up on the `def`: drop the wrapper, keep only the strongest object

The second review pass (@wwylele, PR #40567) trimmed the freshly-landed `def`
further, and the lessons mostly **correct** what the first pass taught.

- **A `def` + `@[simp]` apply lemma makes the `exists_…` wrapper dead weight.**
  This *reverses* the "keep `exists_` as a one-line corollary so downstream is
  untouched" advice I'd written in
  [`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md). Once the named
  object exists, `∃ L, ∀ i, L (φ i) = ψ i` is `⟨theDef …, theDef_apply …⟩` inline;
  a standing wrapper is bloat. (I went back and corrected the doc — flagged the
  reversal in place rather than silently rewriting.)
- **Forgetful-derivation test before keeping/“pending”-ing a corollary.** Two
  corollaries that read like "more API" were just `(equiv).toLinearIsometry` and
  `(span ψ).subtypeₗᵢ.comp (equiv).toLinearIsometry` — a cast and a
  post-composition, no new math. The proof that consumed them now inlines the same
  expressions. Ask *"new fact, or trivial restatement of the strongest object?"*
  If restatement: drop it, and it is **not** MathlibPending material either (a
  named one-liner won't survive upstream review).
- **Terminology precision.** Don't name-drop a field's signature problem
  ("Procrustes") unless the statement *is* that problem; this is the exact /
  zero-residual case, not the least-squares optimization. Keep the citation, drop
  the editorial claim. (Resolved 2026-06-22: the file/namespace were renamed
  `Procrustes` → `GramRigidity`, and "Procrustes" was demoted to a one-line
  *motivation* note; the polar-factor "optimal `W*`" overclaims were softened too.)
- **Placement = import-cost, not theme.** "Move it to `LinearMap.lean`?" → it
  needs `Finsupp.linearCombination` + `Isomorphisms`, which that file lacks;
  answer with the dependency delta first.
- **Sync discipline.** "Stay in sync with the fork" meant mirroring the fork
  *exactly*, including dropping decls the fork had already dropped (staging had
  drifted by two corollaries). And: amend dated decision logs with a **dated
  supersession note**, don't rewrite the history.

Details + the `variable (φ ψ)` placement gotcha in
[`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md) §"Maintainer
follow-up".

---

## 2026-06-14 — Debugging the apply-lemma when `∃`-theorem → `def` (Mathlib structural polish)

Turning `exists_linearIsometryEquiv_span_map_eq_of_inner_eq` into a `def`
(`linearIsometryEquivSpanOfInnerEq`, via `LinearEquiv.isometryOfInner`) per
reviewer request. The construction was easy; proving the `@[simp]` apply lemma
was the time-sink. Symptom → cause → fix, so you grep these from inside the bug:

- **`unknown identifier 'h'`** in a helper whose *statement* doesn't mention `h`
  → `variable (h)` isn't auto-included there → add `include h`.
- **`simp` leaves a goal that looks already-true / `unsolved goals` at a `simp`**
  → `sorry` it, reproduce in a scratch, `extract_goal` to read the *real*
  residual (twice it turned out a *different* decl was failing, not the one I was
  staring at).
- **A `simp only [structural_lemma, compute_lemma]` won't fire the structural
  lemma** → the compute lemma rewrote the pattern first (`linearCombination_single`
  turned `Tφ (single i 1)` back into `φ i`, killing `quotKerEquivRange_symm_apply_image`'s
  `⟨f x, _⟩` match). Split: structural `simp only` first, compute `simp` second.
- **Two canonical forms won't unify** (`(ker f).mkQ x` vs `Submodule.Quotient.mk x`)
  → add the bridge lemma (`Submodule.mkQ_apply`).
- **`rw [someDef]` errors** → can't `rw` a def; use `simp only [someDef]`.
- **`unknown constant …_apply`** mid-`simp` → invented lemma name; grep Mathlib
  for the real one (`coe_isometryOfInner`, `coe_ofEq_apply`).

Full write-up + the convention (copy `Orthonormal.equiv`'s API; no uniqueness
lemma; keep `exists_` as a corollary) in
[`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md) §"Structural
polish".

---

## 2026-06-14 — Over-relying on a ChatGPT *rephrasing* of reviewer feedback (invented meta-structure → wrong scope + over-build)

**Not a Lean bug — a process failure when consuming reviewer feedback.**

### Symptom
Asked to apply a Mathlib reviewer's proof-"folding" feedback, the agent: (1) built
an elaborate `dev/` framework of "principles" and a benchmark question, (2) ran a
*repo-wide* mechanical sweep (folding/classical-removal across ForMathlib **and**
the DKPS papers), and (3) repeatedly mis-scoped — until the user said *"I don't
like how you are interpreting it… focus on the content of what the demonstrated
changes were."*

### Root cause
The feedback the agent received was **not the reviewer's message** — it was a
**ChatGPT rephrasing** that added structure the reviewer never wrote: a "what the
reviewer is *really* asking for" section, a numbered argument breakdown, a long
"how `simp` works" appendix. The agent treated that invented scaffolding as the
reviewer's intent and generalized from it. The reviewer's *actual* message was
just the worked before→after diffs + *"this shows you how to fold; this might not
be optimal yet; do another pass."* — i.e. a **scoped** ask: fold the remaining
non-optimal proofs **in this PR**.

### Fix
Re-anchor on the **demonstrated diffs**, drop the invented meta. The real second
pass was small and concrete: fold the PR's still-verbose rigidity proofs
(`gram_eq_gram_iff` both directions; `obtain ⟨_, c, rfl⟩` to drop reconstruction
`have`s in `hf_isom`/`hf_mem`/`hsurj`). Added a provenance caveat to
[`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md).

### Takeaway
- **Distinguish the reviewer's actual words from any LLM rephrasing of them.** A
  rephrasing optimizes for fluent structure and will *invent* intent, scope, and
  rationale the reviewer never expressed. When the input is "here's the feedback
  (paraphrased)", treat the **concrete examples/diffs as the only hard signal**
  and the surrounding narrative as a hypothesis, not instructions.
- **Don't generalize a few worked examples into a framework or a sweep.** "Here
  are 8 folds on one proof + 'do another pass'" means *fold the other proofs like
  these*, scoped to the same artifact — not "derive a meta-theory" or "apply
  mechanically everywhere." Match the scope the examples were drawn from.
- **When unsure of scope, the examples define it.** They were all from one PR's
  rigidity proofs → the work is that PR's rigidity proofs.

(The repo-wide `classical` removal that came out of this *was* separately
user-directed and is fine; the failure was the interpretation/scope, not that
specific edit.)

---

## 2026-06-14 — Comparator `statement do not match` on conformances that build green + are axiom-clean

Full postmortem:
[`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md).

**One-line root cause:** the comparator's `lean4export` compares **universe
parameters and the instance telescope without alpha-normalizing**, so a
Mathlib-only conformance must mirror the source's `variable` context *exactly* —
dropping an unused `variable {F}` shifted `ι`'s universe from `u_4` to `u_3`
(`statement do not match`), and omitting an accumulated section instance
(`[FirstCountableTopology X]`) dropped an entry from the instance list.

**Durable rules:**
1. **"Slim a conformance" = delete other *theorems*, never the *context*.** Copy
   the source's `variable` lines verbatim, including unused type vars (they
   reserve universe slots) and every instance in declaration order.
2. **`#print <name>` first when chasing `statement do not match`** — it shows the
   leading `.{u_…}` universe signature; `#check` hides it in the body.
3. **The export is a trust boundary below `lake build`.** Build-green +
   axiom-clean + pp.all-identical is *not* export-match. Verify each leaf with a
   `#print` universe diff + `pp.all #check` type diff before paying for the
   comparator; the comparator is ground truth.
4. **Adjacent slips from the same "didn't mirror the source" family:** a dropped
   `[MeasurableSpace E] [BorelSpace E]` → `failed to synthesize`; a leaderboard
   importing the wrong ForMathlib module for a declaration → `Unknown constant`
   (a decl can live in a different file than its "natural" home —
   `eigenvalues₀_eq_zero_of_le` is in `Analysis/Matrix/Spectrum.lean`, not
   `PosDef.lean`).

### Meta-takeaway (the one that would have saved the most time)
**For any semantic property the Lean toolchain can decide, ask the toolchain —
never a textual grep, and never `lake build` alone.** Three precise tools sit one
keystroke away and each answers a different question crisply:
- `#print axioms <name>` → sorry/axiom-freeness (clean = `[propext,
  Classical.choice, Quot.sound]`). A `grep sorry` over source matched docstring
  prose (`` no `sorry` remains ``) and produced a *false* "the papers have
  sorries" alarm that nearly triggered pointless recovery work.
- `#print <name>` / `pp.all #check @<name>` → exact statement, universes,
  instances. The thing that decides comparator match.
- the comparator itself → the real export comparison.

And guard the diagnostic: a comparison over captured command output is a false
pass if the capture was empty — assert non-empty before trusting "identical."
