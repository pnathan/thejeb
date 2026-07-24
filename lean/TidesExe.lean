/-
`tides` — the executable end of the pipeline.

Reads a `frames.json` (whatever the Haiku extraction wrote) *at runtime*,
parses it, and evaluates the **verified** computable STE layer of
`Ste.FiniteInstance` on the loaded data:

  * `STE.Consistent`        — is the corpus jointly satisfiable?
  * `STE.disagreementDegree`— distinct values per variable
  * the conflict sites and the feasibility verdict

The frames are data, not source: nothing about this corpus is hard-coded.
The authors index as `Fin nA`, the variables as `Fin nV`, values as
`String`; `STE.Consistent`/`STE.disagreementDegree` are exactly the
definitions proved correct in `Ste.FiniteInstance`
(`feasibilitySet_eq_empty_iff`, `agree_iff_degree_le_one`), here *run* on
the parsed frames. The trust boundary is the JSON parser and Lean's
evaluator; the aggregation logic itself is the verified one.

Usage:  lake exe tides [path/to/frames.json]
        (defaults to sources/tides/extraction/frames.json)
-/
import Ste.FiniteInstance
import Lean.Data.Json

open Lean

namespace Tides

/-- A parsed corpus: author names, variable names, and the frame matrix
`fr[author][var] = some value | none` (silence). -/
structure Corpus where
  authors : Array String
  vars : Array String
  fr : Array (Array (Option String))

/-- Pull `frames.json` into a `Corpus`. Variable order is the union of keys
across authors (JSON-object order); `"silent"` or a missing cell is `none`. -/
def parse (s : String) : Except String Corpus := do
  let j ← Json.parse s
  let framesObj ← j.getObjVal? "frames"
  let authorNode ← framesObj.getObj?
  let authorPairs : Array (String × Json) := authorNode.toArray
  -- collect the union of variable names, first-seen order
  let mut vars : Array String := #[]
  for (_, avObj) in authorPairs do
    match avObj.getObj? with
    | .ok node =>
      for (k, _) in node.toArray do
        if !vars.contains k then vars := vars.push k
    | .error _ => pure ()
  -- build the frame matrix
  let mut authors : Array String := #[]
  let mut fr : Array (Array (Option String)) := #[]
  for (a, avObj) in authorPairs do
    authors := authors.push a
    let mut row : Array (Option String) := #[]
    for v in vars do
      let cell : Option String :=
        match avObj.getObjVal? v with
        | .ok cellJson =>
          match cellJson.getObjVal? "value" with
          | .ok valJson =>
            match valJson.getStr? with
            | .ok "silent" => none
            | .ok val => some val
            | .error _ => none
          | .error _ => none
        | .error _ => none
      row := row.push cell
    fr := fr.push row
  return { authors, vars, fr }

/-- The runtime frame function, indexing authors/variables by `Fin`. -/
def frameOf (c : Corpus) : Fin c.authors.size → Fin c.vars.size → Option String :=
  fun a v => (c.fr[a.val]!)[v.val]!

/-- Report line: variable name with its (verified-definition) disagreement
degree. -/
def degrees (c : Corpus) : Array (String × Nat) :=
  (Array.finRange c.vars.size).map
    (fun v => (c.vars[v.val]!, STE.disagreementDegree (frameOf c) v))

def isConsistent (c : Corpus) : Bool :=
  decide (STE.Consistent (frameOf c))

end Tides

open Tides in
def main (args : List String) : IO Unit := do
  let path := args.headD "sources/tides/extraction/frames.json"
  let s ← IO.FS.readFile path
  match parse s with
  | .error e => IO.eprintln s!"parse error: {e}"; IO.Process.exit 1
  | .ok c =>
    IO.println s!"corpus: {c.authors.size} authors, {c.vars.size} variables  ({path})"
    IO.println s!"authors: {c.authors.toList}"
    let ds := degrees c
    let consistent := isConsistent c
    let conflicts := (ds.filter (fun p => p.2 ≥ 2)).map (·.1)
    IO.println ""
    IO.println "disagreement degree per variable (STE.disagreementDegree):"
    for (v, d) in ds do
      IO.println s!"  {v} = {d}"
    IO.println ""
    IO.println s!"consistent (STE.Consistent): {consistent}"
    if consistent then
      IO.println "verdict: feasibility set NONEMPTY — a joint reading exists"
    else
      IO.println "verdict: feasibility set EMPTY — no reading satisfies every voice"
    IO.println s!"conflict sites ({conflicts.size}): {conflicts.toList}"
