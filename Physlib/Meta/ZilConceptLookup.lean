/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.AxiomWhitelistCheck

meta import Zil.Datalog.Attach

/-!
# `#zil_concept_lookup` — retrieval over the ZIL graph, not audit

Every prior ZIL command is an auditor (`#zil_graph_report`, `#zil_intent_audit`,
`#zil_definitional_overclaim_report`, …): they answer *"is what we claimed sound?"*.  None answers
*"what does the repository already have about X?"* — and that gap caused repeated failures to find
existing material: the kinematic route to the Schmidt number, the Cauchy-development modules, the
two Verlinde halves of the weak equivalence principle.  In each case the claims were **in the
graph**, attached and searchable in principle, and nothing could query them by concept.

This command closes the gap.  `#zil_concept_lookup "kw1 kw2"` scans every graph edge of the current
environment and prints the declarations whose attached token (claim, assumption, paper, lean
reference, caveat — any symbol subject) contains **all** the given keywords, case-insensitively.
Claim tokens are descriptive kebab-case sentences, so keyword conjunction over them is an effective
concept index that costs nothing to maintain.

Import this module *alongside the modules to search* — typically `import Physlib` for the whole
repository — and invoke with space-separated keywords.  Pure string matching over the attachment
array: no `whnf`, no `maxHeartbeats` concerns, output capped at 40 edges.
-/

@[expose] public section

namespace Physlib.Meta.ZilConceptLookup

open Lean Elab Command Zil.Datalog

/-- The searchable token of a graph value: any symbol subject, verbatim. -/
meta def tokenOf : Value → Option String
  | .symbol s => some s
  | _ => none

/-- All keywords occur in the token (case-insensitive substring conjunction). -/
meta def matchesAll (kws : List String) (s : String) : Bool :=
  let l := s.toLower
  kws.all fun kw => decide (1 < (l.splitOn kw).length)

syntax (name := zilConceptLookupCmd) "#zil_concept_lookup " str : command

elab_rules : command
  | `(#zil_concept_lookup $s:str) => do
    let kws := ((s.getString.splitOn " ").filter (fun k => k ≠ "")).map String.toLower
    if kws.isEmpty then
      logWarning "no keywords given"
      return
    let env ← getEnv
    let mut hits : Nat := 0
    let mut shown : Nat := 0
    let mut out : String := ""
    for att in (declarationAttachments env).toList do
      match tokenOf att.atom.subject with
      | some tok =>
        if matchesAll kws tok then
          hits := hits + 1
          if shown < 40 then
            out := out ++ s!"  · {att.declaration}\n      [{att.atom.relation}] {tok}\n"
            shown := shown + 1
      | none => pure ()
    logInfo m!"zil concept lookup {kws}: {hits} matching edges (showing {shown})\n{out}"

end Physlib.Meta.ZilConceptLookup
