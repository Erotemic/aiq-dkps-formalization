# Benchmark-candidate strategy

This formalization is both a Mathlib-upstreaming effort and a useful source of
small, realistic Lean/Mathlib engineering benchmark problems. Every time a
patch fails in a way that required project context to diagnose — and especially
when it *built green but a downstream check rejected it* — capture a benchmark
candidate before the details fade.

The goal is not to record trivia. A good candidate tests whether another model
can preserve an engineering invariant while doing the original task, ideally
*before* seeing the error that exposed the mistake. This domain is unusually
good for it: Lean's kernel, `#print axioms`, and the comparator give crisp,
mechanical pass/fail, so a candidate's "expected answer" is checkable, not a
matter of taste.

## Workflow

1. **Fix the project first.** Ground the candidate in a real repair, not a
   speculative lesson.
2. **Save the failure evidence.** Keep the exact error — comparator output
   (`statement do not match`), kernel error (`motive is not type correct`),
   elaboration error (`failed to synthesize`), or `#print axioms` showing
   `sorryAx`. The repair must be auditable.
3. **Reconstruct the pre-error context.** What did the agent *have* when it made
   the mistake? Usually the benchmark should start there — e.g. "the source
   theorem + the task to restate it," not "here is the comparator error."
4. **Distill the invariant.** Convert the mistake into a compact rule, e.g.
   "a Mathlib-only conformance must reproduce the source's *exact* `variable`
   context, including unused variables that shift universe numbering," or "a
   `#print axioms` on a leaf transitively certifies its whole proof tree."
5. **Write a hard question.** Include enough Lean code-shape that a model must
   reason about elaboration, universes, instances, the module system, or the
   comparator's matching semantics — without giving away the answer.
6. **Write the expected answer and validation.** Include the minimal fix and the
   command that catches the bug (`lake build`, `lake env lean … Leaderboard`,
   `#print name`, the comparator config).
7. **Tag by failure class** (see taxonomy below).

## Candidate quality bar

Keep a candidate only when it has all of these:

- **Realistic:** it came from an actual task in this repo.
- **Contextual:** a generic Lean/Mathlib StackOverflow answer is not enough; the
  model must preserve a project-specific invariant (comparator export matching,
  leaf-only exposure, Mathlib-overlap awareness, import direction…).
- **Minimal but tempting:** trimmed, but the prompt still has enough context that
  the original mistake is the *natural* one to make.
- **Checkable:** there is a `lake`/`#print`/comparator command, or a precise
  expected patch shape.
- **Non-leaky:** askable without quoting the final error, unless the candidate is
  explicitly an error-repair task.

The best candidates in this repo share a signature: **the code built green and
the type looked right, but a downstream check still rejected it.** Universe-
parameter export mismatch, defeq-but-not-syntactic-equality, an axiom leak — a
model that only trusts `lake build` walks straight into them.

## Prompt levels

For each significant issue, prefer the highest level that still feels fair:

- **Level A — pre-error operation.** "Slim this conformance to its single leaf
  theorem while keeping the comparator's statement-match." The hardest and most
  predictive test: it measures whether the model anticipates the trap.
- **Level B — error repair.** Give the failure (`statement do not match`) and ask
  for the fix. Tests debugging ability; less predictive of avoidance.
- **Level C — distilled micro-question.** A tiny Lean snippet capturing the rule
  ("does dropping an unused `variable {F}` change the declaration's universe
  signature? why does that matter to a name-sensitive exporter?"). Good for
  focused unit benchmarks.

`lean-questions.md` should favour Level A/B candidates with an "Expected answer"
section.

## Tag taxonomy

Tag by the *invariant* tested, not the surface API. Stable clusters (extend as
new categories appear):

- **Comparator / export invariants** — `comparator-statement-match`,
  `universe-parameters`, `instance-arg-order`, `lean4export`,
  `conformance-mirrors-source`, `leaf-selection`, `mathlib-only-restatement`.
- **Proof / kernel invariants** — `defeq-vs-syntactic`, `motive-not-type-correct`,
  `rw-motive`, `sorry-hygiene`, `axiom-footprint`, `print-axioms`.
- **Mathlib API** — `mathlib-overlap` (does it already exist?),
  `lemma-naming`, `dot-notation`, `gap-verification`, `wrong-import-for-decl`.
- **Module system** — `public-import`, `expose-section`, `import-direction`,
  `import-cycle`, `minimal-imports`.
- **Process / provenance** — `comment-grep-false-positive`, `fork-staging-sync`,
  `ai-authorship-strip`, `silent-truncation`.

When in doubt, tag with both the invariant and the surface (e.g.
`universe-parameters`, `comparator-statement-match`). The invariant tag makes
the corpus searchable for "what does this model fail at"; the surface tag for
"what part of the project this concerns."
