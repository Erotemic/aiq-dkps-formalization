# formalization_draft1

This directory contains a first venue-neutral draft for a paper about the
Lean 4 formalization of the DKPS theorem stack, with emphasis on the difficult
formalization tasks: spectral perturbation, MDS stability, alignment,
measurability, probability-to-rate composition, and theorem-interface repair.
DKPS is treated as the motivating application and integration test rather than
the main contribution.

The draft is intentionally not committed to a final venue format yet.  It uses a
plain `article` class so it can later be converted to:

- an ITP/LIPIcs-style conference submission,
- a Springer LNCS-style conference/workshop version,
- a Journal of Automated Reasoning article, or
- an artifact-description companion paper.

## Files

- `paper.tex` -- main LaTeX draft.
- `references.bib` -- provisional BibTeX bibliography for later venue conversion; the current draft uses an inline `thebibliography` so it can build without BibTeX.
- `claims_to_files.md` -- working map from paper claims to repository files.
- `venue_notes.md` -- notes about likely venue directions and formatting choices.
- `model_provenance.md` -- current evidence for the multi-model assistance statement.
- `Makefile` -- convenience targets for local builds.
- `.latexmkrc` -- local latexmk configuration.

## Build

If `latexmk` is installed:

```bash
make -C papers/formalization_draft1
```

Otherwise:

```bash
cd papers/formalization_draft1
pdflatex paper
pdflatex paper
```

## Suggested next editing pass

1. Decide whether the paper is primarily an ITP-style formalization paper or a
   JAR-style artifact/account paper.
2. Replace the placeholder author block.
3. Audit `model_provenance.md` against session transcripts, especially GPT 5.2
   attribution, before finalizing the assistance statement.
4. Add line-accurate citations to Lean declarations if desired.
5. Decide how much of the remaining `hmeas_spec` seam belongs in the main text
   versus an appendix.
