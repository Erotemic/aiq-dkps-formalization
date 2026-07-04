# Lean dependency tracing tools

These tools generate dependency graphs for the AIQ DKPS formalization, with a
focus on the path into:

```lean
DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_second_moment
```

The intended workflow is to generate an auditable dependency map, then edit
`milestones.toml` until the milestone diagram matches the story you want to put
on a slide.

## Quick start: Python-only lexical graph

From the repository root:

```bash
python -m pip install networkx
python tools/lean_dep_trace/trace_deps.py . \
    --outdir build/lean-dep-trace \
    --target DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_second_moment
```

Outputs:

- `build/lean-dep-trace/summary.json`
- `build/lean-dep-trace/lean_user_decl_deps.graphml`
- `build/lean-dep-trace/lean_user_decl_deps.dot`
- `build/lean-dep-trace/focused_ancestors.graphml`
- `build/lean-dep-trace/focused_ancestors.{dot,svg,png}` if Graphviz is installed
- `build/lean-dep-trace/module_backbone.{dot,svg,png}` if Graphviz is installed
- `build/lean-dep-trace/milestone_backbone.{dot,svg,png}` if Graphviz is installed
- `build/lean-dep-trace/milestone_evidence.md`
- `build/lean-dep-trace/milestone_matches.json`

By default, the full declaration graph is written as DOT/GraphML but only the focused, module, and milestone graphs are rendered. Add `--render-full` if you also want `lean_user_decl_deps.svg/png`; it can be slow.

The Python-only mode is intentionally lightweight. It strips Lean comments,
extracts top-level declarations, and scans each declaration span for explicit
references to other user declarations. It is good for recovering the
human-readable formalization pipeline, but it is not Lean's kernel/elaborator
view of dependencies.

## More exact mode: elaborated dependency export

For a closer-to-real theorem dependency graph, first export elaborated
constant dependencies from Lean:

```bash
lake build
mkdir -p build/lean-dep-trace
lake env lean --run tools/lean_dep_trace/ExportDeclDeps.lean \
    > build/lean-dep-trace/elab_deps.jsonl
```

Then render graphs from that JSONL:

```bash
python tools/lean_dep_trace/trace_deps.py . \
    --lean-jsonl build/lean-dep-trace/elab_deps.jsonl \
    --outdir build/lean-dep-trace-elab \
    --target DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_second_moment
```

`ExportDeclDeps.lean` uses Lean's compiled environment and `Expr.getUsedConstants`
on theorem types and proof terms. This sees elaborated constants that are not
visible as plain text. It still filters to project roots (`ForMathlib`,
`Acharyya2024`, `Acharyya2025`, `DkpsQuench`) so the output is useful for slide
planning instead of being dominated by Mathlib internals.

If the Lean helper breaks after a Lean version bump, the most likely API points
are `env.constants.toList`, `ConstantInfo.value?`, or `Expr.getUsedConstants`.
The Python lexical tracer is independent of those APIs.

## Editing the slide-level dependency story

Edit:

```text
tools/lean_dep_trace/milestones.toml
```

Each `[[milestone]]` has:

- `id`: stable identifier used by edges.
- `label`: diagram label.
- `subtitle`: second line in the diagram.
- `color`: Graphviz fill color.
- `patterns`: substrings matched against declaration names, module names, and docstrings.

Each `[[edge]]` declares a slide-level edge between milestones. The generated
`milestone_evidence.md` records whether the matched declarations have a path in
the focused dependency graph and gives a shortest matched path when found.

This makes it easy to tune the map around questions like:

- Should `GramRealization` be shown as load-bearing or as related background?
- Should `Helm2025` be included or intentionally omitted?
- Should the slide collapse `Courant-Fischer`, `Weyl`, and `Davis-Kahan` into one
  spectral perturbation box?

## Tree-sitter note

Tree-sitter can be useful for syntax-aware source segmentation, but it is not the
right authority for theorem dependencies in Lean. The Lean elaborator resolves
names, typeclasses, notations, tactics, and implicit terms. For real theorem
links, prefer the Lean JSONL export plus the Python renderer. Use the lexical
mode when you want a fast, editable, high-recall draft.
