# Developer notes — `dev/`

Long-running engineering memory for the AIQ DKPS Lean formalization. Anything
that **isn't** the formalization itself (`ForMathlib/`, the paper libraries
`Acharyya2024/` … `Helm2025/`), the comparator challenge package (`Challenge/`,
`comparator/`), or planning/status docs (`docs/`) lives here. The contents are
deliberately agent-readable: an agent arriving cold should be able to read this
folder, understand the project's pattern of past mistakes, and take fewer of
them.

The search entry point is [`SEARCH.md`](SEARCH.md). It gives grep patterns and
routing rules so agents search this memory instead of reading it all.

The two subtrees:

```text
dev/
  SEARCH.md                   # How to search engineering memory
  mathlib-proof-polishing.md  # Reference: "folding" proofs to Mathlib style (read before a polishing pass)
  benchmark-candidates/       # Distilled hard questions from real formalization/comparator mistakes
  journals/                   # Postmortems of bugs that took real effort to diagnose
```

`dev/` is **not** a planning tracker (use `docs/planning/`), **not** the
comparator/challenge how-to (use `docs/challenge/`), and **not** a place for WIP
scratch (gitignore those).

---

## `dev/benchmark-candidates/`

**What it is.** A growing corpus of self-contained Lean 4 / Mathlib /
comparator questions distilled from real mistakes made while building and
upstreaming this project. Each question captures a *pre-error* setup — the
context an agent had at the moment of the mistake — so a different model facing
the same setup can be tested for the same failure mode.

This domain has an unusually rich supply of these: a Lean proof either checks or
it doesn't, the comparator either matches or it doesn't, and `#print axioms`
gives a crisp pass/fail. That makes the traps **mechanically checkable**, which
is exactly what a benchmark needs.

**Why an agent should care.**

- **Read** these before a task that resembles one catalogued here (slimming a
  conformance, restating a theorem, choosing a leaf, minimizing imports,
  matching a comparator export). The "Why this was easy to miss" section names
  the cognitive trap so you can recognise it in your own reasoning.
- **Write** here when you cause (or watch the user cause, or resolve) a mistake
  whose root cause is a transferable invariant. The bar is: *another model in
  the same situation could plausibly make the same mistake without this question
  written down.*

**Layout.**

```text
benchmark-candidates/
  README.md          # Workflow, quality bar, prompt Levels A/B/C, tag taxonomy
  index.md           # Router by failure-class invariant
  lean-questions.md  # Main corpus (most entries land here)
```

Spin off a standalone `topic-YYYY-MM-DD.md` file (and link it from `index.md`)
when a question is substantial and focused, or when parallel agents are editing
`lean-questions.md` concurrently. When in doubt, add to `lean-questions.md`.

[`benchmark-candidates/README.md`](benchmark-candidates/README.md) is required
reading before adding a question (write the failure evidence first, then distil;
pick the right Level A/B/C prompt; tag by *failure-class invariant*, not by
surface API).

---

## `dev/journals/`

**What it is.** Postmortem journal of bugs that took real effort to diagnose.
Newest-first, written in the moment so the symptom language matches what a
future debugger would search for.

**Why an agent should care.**

- **Read** here first when you hit a confusing symptom in the same area as a
  past entry. The grep target is the *symptom* (e.g. "statement do not match",
  "motive is not type correct", "failed to synthesize", "no sorry remains"),
  written the way you'd search for it from *inside* the bug — before you know
  the technically-correct vocabulary.
- **Write** here after a fix that took effort. Skip the narrative; the canonical
  shape is **Symptom / What it was NOT / Root cause / Fix / Takeaway**.

**Layout.**

```text
journals/
  index.md             # Symptom router
  lessons_learned.md   # Aggregate entries, newest first
```

---

## `dev/mathlib-proof-polishing.md`

A standalone **reference** (not a postmortem, not a test question) distilling how
to "fold" a proof to Mathlib reviewer standard: replace low-level tactic traces
with rewrite-friendly local lemmas and delegate bookkeeping to `simp`/`simpa`.
Read it before a polishing pass on any upstream-bound proof (ForMathlib
candidates first; the DKPS paper proofs later). It pairs with benchmark question
Q4 (the fold-this-proof capability test). Distilled from real reviewer feedback,
so it reflects what an actual Mathlib maintainer asked for.

---

## How `dev/` relates to the rest of the repo

```text
docs/planning/   -> what's in flight, PR decisions, candidate dossiers
docs/challenge/  -> how the comparator challenge package works
Challenge/       -> the comparator challenges (MathlibCandidate / MathlibPending) + manifest
comparator/      -> per-PR comparator configs
ForMathlib/      -> the upstreamable, paper-agnostic Mathlib candidates
Acharyya*/ …     -> the four DKPS paper theorem layers (end states)
dev/             -> long-running engineering memory (you are here)
  benchmark-candidates/  -> distilled "hard question" corpus from real mistakes
  journals/              -> effortful-debug postmortems
```

The auto-memory at
`/home/agent/.claude/projects/-home-joncrall-code-aiq-dkps-formalization/memory/`
is a parallel layer for **per-conversation** continuity (user preferences,
recent project state, feedback rules). It cross-references `dev/` when relevant;
the two don't duplicate. If a fact is true across many sessions → auto-memory.
If it's a *question* or a *postmortem* → `dev/`.

When unsure *where* to write: would a brand-new agent landing in this repo
benefit from reading it cold, without conversation context? If yes → `dev/`. If
it's only useful with the user in the loop → auto-memory.

---

## Quality bar (one paragraph)

Don't record trivia. Both subtrees are curated; an over-long file is a worse
signal than a short one, because future readers won't believe the important
entries hidden between filler. The strongest entries here are the ones where the
code *built green and looked correct* but a downstream check (comparator,
`#print axioms`, kernel) still rejected it — those are the non-obvious,
transferable traps. If unsure whether something belongs, write it in scratch
first; if a week later you still think the lesson is durable, move it in.
