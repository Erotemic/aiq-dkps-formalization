#!/usr/bin/env python3
"""Trace Lean declaration dependencies for the AIQ DKPS formalization.

This tool has two modes:

1. Default lexical mode: strip Lean comments, find user declarations, and scan
   declaration bodies for explicit references to other user declarations. This is
   fast, Python-only, and good for human-readable pipeline maps.

2. Elaborated mode: pass --lean-jsonl from ExportDeclDeps.lean to use dependencies
   extracted from Lean's compiled environment/proof expressions. This is closer to
   the real theorem dependency graph, but requires a working Lean/lake build.

The output is intended for slide planning and audit handoffs: GraphML/JSON for
analysis, DOT/SVG/PNG for diagrams, and a milestone backbone controlled by an
editable TOML file.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from collections import defaultdict, deque
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Mapping

try:
    import networkx as nx
except ImportError as ex:  # pragma: no cover
    raise SystemExit(
        "This tool requires networkx. Install with: python -m pip install networkx"
    ) from ex

DECL_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "inductive",
    "axiom",
)
DECL_RE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)"
    r"(?:(?:@\[[^\n]*\]\s*)?)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local|opaque)\s+)*"
    r"(?P<kind>" + "|".join(DECL_KINDS) + r")\s+"
    r"(?P<name>`[^`]+`|[A-Za-z_][A-Za-z0-9_'.₀-₉]*)"
)
NAMESPACE_RE = re.compile(r"(?m)^\s*namespace\s+([A-Za-z0-9_'.]+)")
END_RE = re.compile(r"(?m)^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*(?:--.*)?$")
WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*")
QUALIFIED_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'.₀-₉]*)+")

DEFAULT_INCLUDE_ROOTS = ["ForMathlib", "Acharyya2024", "Acharyya2025", "DkpsQuench"]
DEFAULT_TARGET = "DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_second_moment"


@dataclass
class Decl:
    id: str
    name: str
    full_name: str
    kind: str
    module: str
    relpath: str
    line: int
    end_line: int
    doc: str = ""
    source: str = "lexical"


def strip_comments(text: str) -> str:
    """Strip nested Lean block comments and line comments while preserving lines."""
    out: list[str] = []
    i = 0
    depth = 0
    in_str = False
    escaped = False
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_str:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
            out.append(ch)
            i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            out.extend("  ")
            i += 2
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def line_of_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def module_name(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def namespace_at(clean: str, offset: int) -> str:
    prefix = clean[:offset]
    stack: list[str] = []
    events: list[tuple[int, str, str | None]] = []
    for m in NAMESPACE_RE.finditer(prefix):
        events.append((m.start(), "ns", m.group(1)))
    for m in END_RE.finditer(prefix):
        events.append((m.start(), "end", m.group(1)))
    for _, typ, name in sorted(events):
        if typ == "ns":
            assert name is not None
            stack.append(name)
        elif name:
            if stack and stack[-1] == name:
                stack.pop()
            elif name in stack:
                stack = stack[: stack.index(name)]
        elif stack:
            stack.pop()
    return ".".join(stack)


def extract_doc(original: str, decl_offset: int) -> str:
    before = original[:decl_offset]
    m = re.search(r"/--(?P<doc>.*?)-/\s*$", before, flags=re.S)
    if not m:
        return ""
    doc = m.group("doc")
    doc = re.sub(r"\s*\n\s*", " ", doc).strip()
    doc = re.sub(r"\s+", " ", doc)
    return doc[:500]


def iter_lean_files(root: Path, include_roots: list[str]) -> Iterable[Path]:
    for stem in include_roots:
        p_file = root / f"{stem}.lean"
        if p_file.exists():
            yield p_file
        p_dir = root / stem
        if p_dir.exists():
            yield from sorted(p_dir.rglob("*.lean"))


def collect_decls(root: Path, files: list[Path]) -> tuple[dict[str, Decl], dict[str, str], dict[str, str]]:
    decls: dict[str, Decl] = {}
    texts_clean: dict[str, str] = {}
    texts_orig: dict[str, str] = {}
    for path in files:
        original = path.read_text(encoding="utf8")
        clean = strip_comments(original)
        rel = str(path.relative_to(root))
        texts_clean[rel] = clean
        texts_orig[rel] = original
        matches = list(DECL_RE.finditer(clean))
        for idx, m in enumerate(matches):
            # Skip nested declarations unless they start at column 0. This avoids
            # most local declarations inside tactic blocks while keeping all files
            # in this repo. Remove this guard if you want locals too.
            if m.group("indent"):
                continue
            kind = m.group("kind")
            name = m.group("name").strip("`")
            ns = namespace_at(clean, m.start())
            full = f"{ns}.{name}" if ns else name
            end = matches[idx + 1].start() if idx + 1 < len(matches) else len(clean)
            decl_id = full
            if decl_id in decls:
                decl_id = f"{full}@@{rel}:{line_of_offset(clean, m.start())}"
            decls[decl_id] = Decl(
                id=decl_id,
                name=name,
                full_name=full,
                kind=kind,
                module=module_name(root, path),
                relpath=rel,
                line=line_of_offset(clean, m.start()),
                end_line=line_of_offset(clean, end),
                doc=extract_doc(original, m.start()),
            )
    return decls, texts_clean, texts_orig


def collect_lexical_deps(root: Path, decls: dict[str, Decl], texts_clean: Mapping[str, str]) -> nx.DiGraph:
    full_to_id = {d.full_name: did for did, d in decls.items()}
    bare_to_ids: dict[str, list[str]] = defaultdict(list)
    for did, d in decls.items():
        bare_to_ids[d.name].append(did)

    g = nx.DiGraph(mode="lexical")
    for did, d in decls.items():
        g.add_node(did, **asdict(d))

    decl_ids_by_rel: dict[str, list[str]] = defaultdict(list)
    for did, d in decls.items():
        decl_ids_by_rel[d.relpath].append(did)
    for rel in decl_ids_by_rel:
        decl_ids_by_rel[rel].sort(key=lambda did: decls[did].line)

    for rel, clean in texts_clean.items():
        line_offsets = [0]
        for m in re.finditer("\n", clean):
            line_offsets.append(m.end())

        def off_for_line(line: int) -> int:
            return line_offsets[max(0, min(line - 1, len(line_offsets) - 1))]

        for did in decl_ids_by_rel.get(rel, []):
            d = decls[did]
            body = clean[off_for_line(d.line) : off_for_line(d.end_line)]
            refs: set[str] = set()

            for tok in QUALIFIED_RE.findall(body):
                if tok in full_to_id:
                    refs.add(full_to_id[tok])
                    continue
                suffix_hits = [rid for full, rid in full_to_id.items() if full.endswith("." + tok)]
                if len(suffix_hits) == 1:
                    refs.add(suffix_hits[0])
                    continue
                parts = tok.split(".")
                for i in range(1, len(parts)):
                    suf = ".".join(parts[i:])
                    if suf in full_to_id:
                        refs.add(full_to_id[suf])
                        break
                    suffix_hits = [rid for full, rid in full_to_id.items() if full.endswith("." + suf)]
                    if len(suffix_hits) == 1:
                        refs.add(suffix_hits[0])
                        break

            current_ns = ".".join(d.full_name.split(".")[:-1])
            ns_parts = current_ns.split(".") if current_ns else []
            for tok in WORD_RE.findall(body):
                resolved = None
                for k in range(len(ns_parts), -1, -1):
                    prefix = ".".join(ns_parts[:k])
                    cand = f"{prefix}.{tok}" if prefix else tok
                    if cand in full_to_id:
                        resolved = full_to_id[cand]
                        break
                if resolved is None and tok in bare_to_ids and len(bare_to_ids[tok]) == 1:
                    resolved = bare_to_ids[tok][0]
                if resolved is not None:
                    refs.add(resolved)

            for rid in refs:
                if rid != did:
                    g.add_edge(rid, did, source="lexical")
    return g


def load_elaborated_deps(path: Path, decls: dict[str, Decl], include_roots: list[str]) -> nx.DiGraph:
    """Build graph from ExportDeclDeps.lean JSONL and annotate with lexical metadata."""
    roots = tuple(include_roots)

    def wanted(name: str) -> bool:
        return any(name == r or name.startswith(r + ".") for r in roots)

    g = nx.DiGraph(mode="elaborated")
    lexical_by_full = {d.full_name: d for d in decls.values()}
    rows = []
    for raw in path.read_text(encoding="utf8").splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            row = json.loads(raw)
        except json.JSONDecodeError:
            continue
        name = row.get("name")
        if not isinstance(name, str) or not wanted(name):
            continue
        rows.append(row)

    for row in rows:
        name = row["name"]
        d = lexical_by_full.get(name)
        if d is None:
            g.add_node(
                name,
                id=name,
                name=name.split(".")[-1],
                full_name=name,
                kind=row.get("kind", "constant"),
                module=".".join(name.split(".")[:-1]),
                relpath="",
                line=0,
                end_line=0,
                doc="",
                source="elaborated",
            )
        else:
            data = asdict(d)
            data["source"] = "elaborated"
            data["kind"] = row.get("kind", data["kind"])
            g.add_node(name, **data)

    user_names = set(g.nodes)
    for row in rows:
        name = row["name"]
        for dep in row.get("deps", []):
            if dep in user_names and dep != name:
                g.add_edge(dep, name, source="elaborated")
    return g


def resolve_targets(g: nx.DiGraph, targets: list[str]) -> list[str]:
    resolved: list[str] = []
    for t in targets:
        if t in g:
            resolved.append(t)
            continue
        hits = [n for n in g.nodes if n.endswith("." + t) or n == t]
        if hits:
            resolved.append(sorted(hits, key=len)[0])
        else:
            sys.stderr.write(f"warning: target not found: {t}\n")
    return resolved


def ancestors_subgraph(g: nx.DiGraph, targets: list[str]) -> nx.DiGraph:
    nodes: set[str] = set()
    for t in targets:
        if t not in g:
            continue
        nodes.add(t)
        nodes.update(nx.ancestors(g, t))
    return g.subgraph(nodes).copy()


def module_color(module: str, *, focus: bool = False) -> str:
    if focus:
        return "#fff2cc"
    if module.startswith("DkpsQuench"):
        return "#d9ead3"
    if module.startswith("Acharyya2025"):
        return "#cfe2f3"
    if module.startswith("Acharyya2024"):
        return "#eadcf8"
    if module.startswith("ForMathlib"):
        return "#fce5cd"
    return "#f7f7f7"


def dot_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', r'\"').replace("\n", r"\n")


def write_dot(g: nx.DiGraph, path: Path, focus_targets: set[str] | None = None) -> None:
    focus_targets = focus_targets or set()
    lines = [
        "digraph LeanDeps {",
        "  graph [rankdir=LR, overlap=false, splines=true];",
        "  node [shape=box, fontsize=10, fontname=Helvetica];",
        "  edge [fontsize=8, fontname=Helvetica];",
    ]
    for n, data in g.nodes(data=True):
        name = data.get("name", n)
        module = data.get("module", "")
        rel = data.get("relpath", "")
        line = data.get("line", "")
        label = f"{name}\n{module}"
        if rel and line:
            label += f"\n{rel}:{line}"
        color = module_color(module, focus=n in focus_targets)
        penwidth = "2" if n in focus_targets else "1"
        lines.append(
            f'  "{dot_escape(n)}" [label="{dot_escape(label)}", '
            f'style=filled, fillcolor="{color}", penwidth={penwidth}];'
        )
    for u, v in g.edges():
        lines.append(f'  "{dot_escape(u)}" -> "{dot_escape(v)}";')
    lines.append("}")
    path.write_text("\n".join(lines), encoding="utf8")


def render_dot(dot: Path) -> None:
    for fmt in ["svg", "png"]:
        out = dot.with_suffix(f".{fmt}")
        try:
            subprocess.run(["dot", f"-T{fmt}", str(dot), "-o", str(out)], check=False)
        except FileNotFoundError:
            return


def write_module_backbone(g: nx.DiGraph, path: Path) -> None:
    mg = nx.DiGraph()
    for n, data in g.nodes(data=True):
        mg.add_node(data.get("module", "unknown"))
    for u, v in g.edges():
        mu = g.nodes[u].get("module", "unknown")
        mv = g.nodes[v].get("module", "unknown")
        if mu != mv:
            mg.add_edge(mu, mv, weight=mg.get_edge_data(mu, mv, {}).get("weight", 0) + 1)
    lines = [
        "digraph ModuleDeps {",
        "  graph [rankdir=LR, overlap=false, splines=true];",
        "  node [shape=box, fontsize=11, fontname=Helvetica];",
        "  edge [fontsize=9, fontname=Helvetica];",
    ]
    for m in sorted(mg.nodes):
        lines.append(f'  "{dot_escape(m)}" [style=filled, fillcolor="{module_color(m)}"];')
    for u, v, data in sorted(mg.edges(data=True)):
        lines.append(f'  "{dot_escape(u)}" -> "{dot_escape(v)}" [label="{data.get("weight", 1)}"];')
    lines.append("}")
    path.write_text("\n".join(lines), encoding="utf8")


def node_matches_patterns(node: str, data: Mapping[str, object], patterns: list[str]) -> bool:
    text = "\n".join(str(x) for x in [node, data.get("name", ""), data.get("full_name", ""), data.get("module", ""), data.get("doc", "")])
    return any(p in text for p in patterns)


def shortest_path_between_sets(g: nx.DiGraph, sources: list[str], targets: list[str]) -> list[str] | None:
    target_set = set(targets)
    best: list[str] | None = None
    for s in sources:
        if s not in g:
            continue
        q = deque([(s, [s])])
        seen = {s}
        while q:
            cur, path = q.popleft()
            if cur in target_set:
                if best is None or len(path) < len(best):
                    best = path
                break
            if best is not None and len(path) >= len(best):
                continue
            for nxt in g.successors(cur):
                if nxt not in seen:
                    seen.add(nxt)
                    q.append((nxt, path + [nxt]))
    return best


def write_milestone_backbone(g: nx.DiGraph, config_path: Path, outdir: Path) -> None:
    if not config_path.exists():
        return
    config = tomllib.loads(config_path.read_text(encoding="utf8"))
    milestones = config.get("milestone", [])
    edges = config.get("edge", [])
    if isinstance(milestones, dict):
        milestones = [milestones]
    if isinstance(edges, dict):
        edges = [edges]

    matches: dict[str, list[str]] = {}
    for m in milestones:
        mid = m["id"]
        pats = list(m.get("patterns", []))
        matches[mid] = [n for n, data in g.nodes(data=True) if node_matches_patterns(n, data, pats)]

    dot = outdir / "milestone_backbone.dot"
    lines = [
        "digraph Milestones {",
        "  graph [rankdir=LR, overlap=false, splines=true];",
        "  node [shape=box, style=rounded, fontsize=13, fontname=Helvetica];",
        "  edge [fontsize=10, fontname=Helvetica];",
    ]
    for m in milestones:
        mid = m["id"]
        label = m.get("label", mid)
        subtitle = m.get("subtitle", "")
        label_text = f"{label}\n{subtitle}" if subtitle else label
        color = m.get("color", "#f7f7f7")
        count = len(matches.get(mid, []))
        lines.append(
            f'  "{dot_escape(mid)}" [label="{dot_escape(label_text)}\n({count} matched decls)", '
            f'fillcolor="{color}", style="rounded,filled"];'
        )
    evidence_lines = ["# Milestone dependency evidence", ""]
    for e in edges:
        src = e["source"]
        dst = e["target"]
        label = e.get("label", "")
        path = shortest_path_between_sets(g, matches.get(src, []), matches.get(dst, []))
        style = "solid" if path else "dashed"
        color = "#444444" if path else "#999999"
        lines.append(
            f'  "{dot_escape(src)}" -> "{dot_escape(dst)}" '
            f'[label="{dot_escape(label)}", style={style}, color="{color}"];'
        )
        evidence_lines.append(f"## {src} -> {dst}")
        evidence_lines.append("")
        if path:
            evidence_lines.append("Shortest matched path:")
            evidence_lines.append("")
            for node in path:
                d = g.nodes[node]
                evidence_lines.append(
                    f"- `{node}` ({d.get('relpath', '')}:{d.get('line', '')})"
                )
        else:
            evidence_lines.append("No path found between matched declarations in this graph.")
        evidence_lines.append("")
    lines.append("}")
    dot.write_text("\n".join(lines), encoding="utf8")
    (outdir / "milestone_evidence.md").write_text("\n".join(evidence_lines), encoding="utf8")
    (outdir / "milestone_matches.json").write_text(json.dumps(matches, indent=2), encoding="utf8")
    render_dot(dot)


def write_focus_json(g: nx.DiGraph, targets: list[str], outdir: Path) -> None:
    payload: dict[str, list[dict[str, object]]] = {}
    for target in targets:
        sg = ancestors_subgraph(g, [target])
        try:
            order = list(nx.topological_sort(sg))
        except nx.NetworkXUnfeasible:
            order = list(sg.nodes)
        rows = []
        for n in order:
            d = sg.nodes[n]
            rows.append(
                {
                    "id": n,
                    "name": d.get("name"),
                    "kind": d.get("kind"),
                    "module": d.get("module"),
                    "file": d.get("relpath"),
                    "line": d.get("line"),
                    "deps_in_focus": len([p for p in sg.predecessors(n)]),
                    "used_by_in_focus": len([s for s in sg.successors(n)]),
                    "doc": d.get("doc", ""),
                }
            )
        payload[target] = rows
    (outdir / "focused_ancestors.json").write_text(json.dumps(payload, indent=2), encoding="utf8")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("root", type=Path, help="Lean project root")
    ap.add_argument("--include", nargs="*", default=DEFAULT_INCLUDE_ROOTS, help="root modules/directories to scan")
    ap.add_argument("--target", action="append", default=[], help="target declaration; can be repeated")
    ap.add_argument("--outdir", type=Path, default=Path("build/lean-dep-trace"), help="output directory")
    ap.add_argument("--milestones", type=Path, default=None, help="TOML milestone config")
    ap.add_argument("--lean-jsonl", type=Path, default=None, help="JSONL from ExportDeclDeps.lean for elaborated dependencies")
    ap.add_argument("--no-render", action="store_true", help="do not call graphviz dot")
    ap.add_argument("--render-full", action="store_true", help="also render the full declaration graph; this can be slow")
    args = ap.parse_args()

    root = args.root.resolve()
    files = list(iter_lean_files(root, args.include))
    decls, clean, _orig = collect_decls(root, files)

    if args.lean_jsonl:
        g = load_elaborated_deps(args.lean_jsonl, decls, args.include)
        mode = "elaborated"
    else:
        g = collect_lexical_deps(root, decls, clean)
        mode = "lexical"

    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    targets = resolve_targets(g, args.target or [DEFAULT_TARGET])

    nx.write_graphml(g, outdir / "lean_user_decl_deps.graphml")
    write_dot(g, outdir / "lean_user_decl_deps.dot")
    if args.render_full and not args.no_render:
        render_dot(outdir / "lean_user_decl_deps.dot")

    summary = {
        "mode": mode,
        "decl_count": g.number_of_nodes(),
        "edge_count": g.number_of_edges(),
        "targets_requested": args.target or [DEFAULT_TARGET],
        "targets_resolved": targets,
        "include_roots": args.include,
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf8")

    if targets:
        sg = ancestors_subgraph(g, targets)
        nx.write_graphml(sg, outdir / "focused_ancestors.graphml")
        write_dot(sg, outdir / "focused_ancestors.dot", set(targets))
        if not args.no_render:
            render_dot(outdir / "focused_ancestors.dot")
        write_focus_json(g, targets, outdir)
        write_module_backbone(sg, outdir / "module_backbone.dot")
        if not args.no_render:
            render_dot(outdir / "module_backbone.dot")

        config_path = args.milestones or (Path(__file__).with_name("milestones.toml"))
        write_milestone_backbone(sg, config_path, outdir)

    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
