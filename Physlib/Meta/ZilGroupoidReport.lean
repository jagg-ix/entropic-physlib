/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public meta import Physlib.Meta.ZilUnifyDiagram
public meta import Physlib.Meta.ZilBridgeGroupoid
public meta import Physlib.Meta.ZilDatalogFast

/-!
# `#zil_groupoid_report` and `#zil_assert_edge_defect` — the groupoid, run on real carriers

Two commands completing `Physlib.Meta.ZilBridgeGroupoid`:

* `#zil_groupoid_report c₁, c₂, … [with "typing"]` feeds the *real* diagram data — homogeneous
  bridge constraints as `bridgeEdge` facts, connecting-theorem coverage as `bridgeProven`
  facts — through the certified groupoid rules and reports the `underivedComposite` closure.
  Where `#zil_unify_diagram`'s composite check looks through **one** intermediate object, the
  Datalog closure composes proven bridges along paths of **any** length: an edge whose flanks
  are themselves only reachable through further proven hops is still surfaced. The rules are
  the `decide`-certified ones; the evaluation is `deriveProgramFast`, pinned to the certified
  reference engine by `Physlib.Meta.ZilDatalogFastCheck`.

* `#zil_assert_edge_defect A B "dim" [with "typing"]` is the **signed dimensional defect**
  assertion: the two sides of the bridge constraint between `A` and `B` must differ by exactly
  the stated dimension (`"1"` for homogeneous). This promotes readouts like the temperature
  pentagon's Verlinde edges — inhomogeneous by exactly `I⁻¹` under the information-extended
  typing of `G` — from documentation to build-enforced fact: the defect *is* the
  Brillouin/Landauer bookkeeping, and this command fails the build if it drifts.
-/

open Lean Elab Command Meta
open Physlib.Meta.ZilDimension
open Physlib.Meta.ZilAnalogyUnify
open Physlib.Meta.ZilUnifyDiagram
open Physlib.Meta.ZilBridgeGroupoid
open Physlib.Meta.ZilDatalogFast
open Zil.Datalog

namespace Physlib.Meta.ZilGroupoidReport

/-- Run the certified groupoid rules over the real diagram data for `carriers`. -/
meta def runGroupoid (carriers : Array Name)
    (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) : CommandElabM Unit := do
  if carriers.size < 2 then
    throwError "zil_groupoid_report: need at least two carriers"
  let env ← getEnv
  let lookup := lookupOf overrides
  -- pairwise edges from the unifier, coverage from the environment pass
  let mut edges : Array (Name × Name × Bool) := #[]   -- (a, b, homogeneous?)
  for i in [0:carriers.size] do
    for j in [i+1:carriers.size] do
      let r ← unifyPair carriers[i]! carriers[j]!
      edges := edges.push (carriers[i]!, carriers[j]!, verdictPasses (r.verdict lookup))
  let conn := connectingTheorems env carriers
  let provenPair (a b : Name) : Bool :=
    !(conn.getD (a, b) []).isEmpty || !(conn.getD (b, a) []).isEmpty
  -- facts for the groupoid program
  let mut facts : List Atom := []
  let mut nEdge := 0
  let mut nProven := 0
  for (a, b, homog) in edges do
    if homog then
      facts := ZilBridgeGroupoid.edge "bridgeEdge" a.toString b.toString :: facts
      nEdge := nEdge + 1
    if provenPair a b then
      facts := ZilBridgeGroupoid.edge "bridgeProven" a.toString b.toString :: facts
      nProven := nProven + 1
  let closure := deriveProgramFast { facts := facts, rules := bridgeGroupoidRules } 8
  -- report, deduplicating the symmetric closure to unordered pairs
  let renderV : Value → String | .symbol s => s | .string s => s | v => toString (repr v)
  let mut seen : List (String × String) := []
  let mut findings : Array String := #[]
  for a in closure do
    if a.relation == "underivedComposite" then
      let x := renderV a.object; let y := renderV a.subject
      let key := if x ≤ y then (x, y) else (y, x)
      unless seen.contains key do
        seen := key :: seen
        findings := findings.push s!"{key.1} ⟷ {key.2}"
  let mut out := s!"zil_groupoid_report: {carriers.size} objects, {nEdge} homogeneous edges, \
{nProven} proven, closure {closure.length} atoms\n"
  if findings.isEmpty then
    out := out ++ "  underived composites (any path length): NONE — the groupoid is closed\n"
  else
    out := out ++ s!"  underived composites (any path length): {findings.size}\n"
    for f in findings do
      out := out ++ s!"    · {f}\n"
  logInfo out

/-- Compute the signed dimensional defect of the bridge constraint between `a` and `b`:
`1` for a homogeneous or identical edge, `dl · dr⁻¹` for an inhomogeneous one. -/
meta def edgeDefect (a b : Name)
    (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) :
    CommandElabM (Dimension LTMCTIDimensionBase) := do
  let r ← unifyPair a b
  match r.verdict (lookupOf overrides) with
  | .identical => pure 1
  | .homogeneous _ => pure 1
  | .inhomogeneous dl dr => pure (dl * dr⁻¹)
  | .undetermined why =>
    throwError "zil_assert_edge_defect: verdict UNDETERMINED for {a} ⟶ {b} ({why})"

meta def runAssertDefect (a b : Name) (expected : String)
    (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) : CommandElabM Unit := do
  let some want := parseDim expected
    | throwError "zil_assert_edge_defect: cannot parse expected dimension '{expected}'"
  let defect ← edgeDefect a b overrides
  if dimEq defect want then
    logInfo s!"zil_assert_edge_defect: {a} ⟶ {b} defect [{renderDim defect}] = expected — OK"
  else
    throwError "zil_assert_edge_defect FAILED: {a} ⟶ {b} has defect \
[{renderDim defect}], expected [{renderDim want}]"

syntax (name := zilGroupoidReportCmd) "#zil_groupoid_report " ident,+ : command
syntax (name := zilGroupoidReportWithCmd) "#zil_groupoid_report " ident,+ " with " str : command
syntax (name := zilAssertEdgeDefectCmd) "#zil_assert_edge_defect " ident ident str : command
syntax (name := zilAssertEdgeDefectWithCmd)
  "#zil_assert_edge_defect " ident ident str " with " str : command

elab_rules : command
  | `(#zil_groupoid_report $cs:ident,*) => do
    runGroupoid (cs.getElems.map (·.getId)) {}
  | `(#zil_groupoid_report $cs:ident,* with $s:str) => do
    runGroupoid (cs.getElems.map (·.getId)) (← parseOverrides s.getString)
  | `(#zil_assert_edge_defect $a:ident $b:ident $d:str) => do
    runAssertDefect a.getId b.getId d.getString {}
  | `(#zil_assert_edge_defect $a:ident $b:ident $d:str with $s:str) => do
    runAssertDefect a.getId b.getId d.getString (← parseOverrides s.getString)

end Physlib.Meta.ZilGroupoidReport
