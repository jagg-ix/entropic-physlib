/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilConceptLookup

meta import Zil.Datalog.Attach

/-!
# `#zil_assert_*` — graph-structural claims as build-time facts

`#zil_query` retrieves; these commands **enforce**.  A statement like *"this premise has no
derivation anywhere in the graph"* is a graph-structural fact — checkable mechanically, and liable
to silently change as the repository grows.  Reporting it in prose leaves it a snapshot; asserting
it in a gate makes the build fail the day it stops being true.

* `#zil_assert_primitive "token"…` — the token is **load-bearing** (some `requires` edge references
  it) **and** no `formalizes`/`derives` edge establishes it.  The load-bearing check is essential:
  without it, a misspelled token trivially "has no establisher", which is precisely the
  asserting-absence-with-wrong-vocabulary failure this session kept hitting.
* `#zil_assert_established "token"…` — some `formalizes`/`derives` edge establishes it.
* `#zil_assert_edge decl "relation" "token"` — that exact edge exists on that declaration.

Import alongside the modules whose graph is being asserted — `import Physlib` for whole-repository
facts.  Pure string scans over `declarationAttachments`; no `whnf`, no `maxHeartbeats`.
-/

@[expose] public section

namespace Physlib.Meta.ZilAssert

open Lean Elab Command Zil.Datalog

/-- Relations that establish a token. -/
meta def establishRelations : List String := ["formalizes", "derives"]

/-- The symbol subject of an edge, if any. -/
meta def subjectStr : Value → Option String
  | .symbol s => some s
  | _ => none

meta def runAssertPrimitive (toks : List String) : CommandElabM Unit := do
  let env ← getEnv
  let atts := (declarationAttachments env).toList
  for tok in toks do
    let referenced := atts.any fun a =>
      a.atom.relation == "requires" && subjectStr a.atom.subject == some tok
    unless referenced do
      throwError "zil_assert_primitive: token is not referenced by any `requires` edge — \
        asserting primitivity of an unused token is vacuous (possible typo): {tok}"
    match atts.find? (fun a =>
        establishRelations.contains a.atom.relation && subjectStr a.atom.subject == some tok) with
    | some a =>
      throwError "zil_assert_primitive FAILED: `{tok}` is established by `{a.declaration}` \
        via `{a.atom.relation}` — the premise is no longer primitive; update the gate"
    | none => pure ()
  logInfo m!"zil_assert_primitive: {toks.length} token(s) load-bearing with no establisher"

meta def runAssertEstablished (toks : List String) : CommandElabM Unit := do
  let env ← getEnv
  let atts := (declarationAttachments env).toList
  for tok in toks do
    unless atts.any (fun a =>
        establishRelations.contains a.atom.relation && subjectStr a.atom.subject == some tok) do
      throwError "zil_assert_established FAILED: no formalizes/derives edge establishes: {tok}"
  logInfo m!"zil_assert_established: {toks.length} token(s) established"

meta def runAssertEdge (decl : Name) (rel tok : String) : CommandElabM Unit := do
  let env ← getEnv
  let atts := (declarationAttachments env).toList
  unless atts.any (fun a =>
      a.declaration == decl && a.atom.relation == rel && subjectStr a.atom.subject == some tok) do
    throwError "zil_assert_edge FAILED: no edge `{decl}` —[{rel}]→ `{tok}`"
  logInfo m!"zil_assert_edge: {decl} —[{rel}]→ token present"

syntax (name := zilAssertPrimitiveCmd) "#zil_assert_primitive " str,+ : command
syntax (name := zilAssertEstablishedCmd) "#zil_assert_established " str,+ : command
syntax (name := zilAssertEdgeCmd) "#zil_assert_edge " ident str str : command

elab_rules : command
  | `(#zil_assert_primitive $ts:str,*) =>
    runAssertPrimitive (ts.getElems.toList.map (·.getString))
  | `(#zil_assert_established $ts:str,*) =>
    runAssertEstablished (ts.getElems.toList.map (·.getString))
  | `(#zil_assert_edge $d:ident $r:str $t:str) =>
    runAssertEdge d.getId r.getString t.getString

end Physlib.Meta.ZilAssert
