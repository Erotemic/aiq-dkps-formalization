/-
Export elaborated Lean declaration dependencies as JSONL.

Run from the repository root after the project has been built:

  mkdir -p build/lean-dep-trace
  lake env lean --run tools/lean_dep_trace/ExportDeclDeps.lean \
    > build/lean-dep-trace/elab_deps.jsonl

Then consume with:

  python tools/lean_dep_trace/trace_deps.py . \
    --lean-jsonl build/lean-dep-trace/elab_deps.jsonl \
    --outdir build/lean-dep-trace-elab

This uses Lean's compiled environment and Expr.getUsedConstants, so it sees
elaborated constants in theorem types and proof terms rather than only textual
references. It intentionally filters to the project roots below and omits
Mathlib/internal constants to keep the graph slide-sized.
-/

import Lean
import Lean.Util.FoldConsts

open Lean

namespace Tools.LeanDepTrace

/-- Project root modules to import and keep in the exported graph. -/
def projectRoots : List String := [
  "ForMathlib",
  "Acharyya2024",
  "Acharyya2025",
  "DkpsQuench"
]

/-- Root modules to load into the environment. -/
def projectImports : Array Import := #[
  { module := `ForMathlib },
  { module := `Acharyya2024 },
  { module := `Acharyya2025 },
  { module := `DkpsQuench }
]

private def hasPrefixRoot (name : Name) : Bool :=
  let s := name.toString
  projectRoots.any (fun r => s == r || s.startsWith (r ++ "."))

private def constKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def usedConstantsOf? (expr? : Option Expr) : List Name :=
  match expr? with
  | none => []
  | some e => e.getUsedConstants.toList

private def dedupNames (xs : List Name) : List Name :=
  xs.foldl
    (fun acc x => if acc.contains x then acc else acc ++ [x])
    []

private def userDepsOfConst (ci : ConstantInfo) : List Name :=
  let deps := ci.type.getUsedConstants.toList ++ usedConstantsOf? ci.value?
  dedupNames <| deps.filter (fun n => hasPrefixRoot n && n != ci.name)

private def jsonLine (name : Name) (ci : ConstantInfo) (deps : List Name) : String :=
  let depJson := Json.arr <| deps.toArray.map (fun n => Json.str n.toString)
  let obj := Json.mkObj [
    ("name", Json.str name.toString),
    ("kind", Json.str (constKind ci)),
    ("deps", depJson)
  ]
  obj.compress

end Tools.LeanDepTrace

open Tools.LeanDepTrace

/-- Entry point for `lake env lean --run`. -/
def main : IO Unit := do
  let env ← importModules projectImports {} 0
  let mut rows : Array (Name × ConstantInfo) := #[]
  for (name, ci) in env.constants.toList do
    if hasPrefixRoot name then
      rows := rows.push (name, ci)
  let rows := rows.qsort (fun a b => a.fst.toString < b.fst.toString)
  for (name, ci) in rows do
    IO.println <| jsonLine name ci (userDepsOfConst ci)
