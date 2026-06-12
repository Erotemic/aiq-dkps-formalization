# Venue notes for formalization_draft1

This draft is deliberately venue-neutral.  The technical story can be shaped in
at least three ways.

## ITP-style submission

Likely emphasis:

- formalization of nontrivial mathematics in Lean 4;
- theorem-statement repair caused by kernel-level verification;
- reusable Mathlib-style infrastructure;
- artifact availability and build reproducibility;
- difficult proof-engineering tasks carried out by a model-assisted workflow.

Likely changes:

- convert to the current ITP format;
- shorten background and related work;
- move parts of the DKPS statistical context to an appendix;
- add a compact theorem crosswalk table and artifact-evaluation section.

## Journal of Automated Reasoning submission

Likely emphasis:

- deeper account of the formal interfaces;
- more detail on false or underspecified theorem shapes;
- substantial discussion of measurability, alignment, spectral perturbation,
  and MDS minimizer stability;
- extended comparison with prior formalizations of probability, linear algebra,
  and spectral methods.

Likely changes:

- expand the deterministic CMDS perturbation section;
- include more Lean snippets;
- describe the `ForMathlib` staging design in more detail;
- add an appendix with theorem names and proof dependencies.

## Artifact or experience-paper direction

Likely emphasis:

- reproducibility of the Lean artifact;
- model-assisted workflow and human validation;
- what kinds of tasks were successfully delegated to Fable 5;
- what tasks remained as honest seams.

Likely changes:

- add a chronological account of work packages;
- include exact commit hashes, build logs, and session provenance;
- keep mathematical exposition high-level but precise.
