/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public meta import Physlib.Meta.ZilTypedRef
public import Physlib
meta import Zil.Datalog.Attach

/-!
# Typed-reference coverage report over the real physlib graph

`#zil_typed_graph_report` extracts every ZIL graph edge from the current environment, parses both
endpoints with the typed-reference layer of `Physlib.Meta.ZilTypedRef`, and logs per-namespace
coverage plus any value carrying an unknown prefix. This is the build-time demonstration that the graph
prefixes (`claim`, `lean`, `paper`, `assumption`, `constant`, `model`, `definition`, `object`,
`epistemic`, `scope`, `premise`, `value`, `input`, `theorem`, `mathlib`, `law`, `measurement`, `book`)
type cleanly into the Zanzibar-style object namespaces over the whole graph, and a standing detector for
any new prefix that slips in untyped.
-/

@[expose] public section

namespace Physlib.Meta.ZilTypedRefReport

open Lean
open Zil.Datalog
open Physlib.Meta.ZilTypedRef

/-- Extract the physlib graph atoms from an environment. -/
meta def graphAtoms (env : Environment) : List Atom :=
  (Zil.Datalog.declarationAttachments env).toList.map fun a => a.atom

/-- The display name of a namespace (its canonical graph prefix). -/
meta def nsName (τ : ObjType) : String := τ.nsPrefix

/-- Count, per namespace, how many of the parsed references landed in it. -/
meta def histogram (refs : List (Option Ref)) : List (ObjType × Nat) :=
  ObjType.all.map fun τ =>
    (τ, (refs.filter fun r => match r with | some ⟨τ', _⟩ => τ' == τ | none => false).length)

meta def reportMessage (env : Environment) : MessageData := Id.run do
  let atoms := graphAtoms env
  let objs := atoms.map fun a => Ref.ofValue? a.object
  let subs := atoms.map fun a => Ref.ofValue? a.subject
  let objTyped := (objs.filter (·.isSome)).length
  let subTyped := (subs.filter (·.isSome)).length
  let unknown := (atoms.filterMap fun a =>
      match a.subject with
      | .symbol s =>
          if (Ref.ofValue? a.subject).isNone && (s.splitOn ":").length ≥ 2 then some s else none
      | _ => none).eraseDups
  let objHist := histogram objs
  let subHist := histogram subs
  let objLine := String.intercalate "  " (objHist.map fun p => s!"{nsName p.1}={p.2}")
  let subLine := String.intercalate "  " (subHist.map fun p => s!"{nsName p.1}={p.2}")
  let unknownLine :=
    if unknown.isEmpty then
      "none (every prefixed value maps to a known namespace)"
    else
      s!"({unknown.length}) " ++ String.intercalate ", " (unknown.take 12)
  return m!"zil typed-ref coverage: {atoms.length} edges | objects typed {objTyped}/{atoms.length} | subjects typed {subTyped}/{atoms.length}\n  objects  by namespace: {objLine}\n  subjects by namespace: {subLine}\n  unknown-prefix subjects: {unknownLine}"

/-- **`#zil_typed_graph_report`** — parse every extracted graph value with the typed-reference layer
and log per-namespace coverage plus any unknown-prefix values. -/
syntax (name := zilTypedGraphReportCmd) "#zil_typed_graph_report" : command

@[command_elab zilTypedGraphReportCmd]
meta def elabZilTypedGraphReport : Elab.Command.CommandElab := fun _ => do
  logInfo (reportMessage (← getEnv))

end Physlib.Meta.ZilTypedRefReport

end

#zil_typed_graph_report
