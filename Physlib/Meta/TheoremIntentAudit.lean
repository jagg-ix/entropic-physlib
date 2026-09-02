/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
meta import Zil.Datalog.FormalizationContract
meta import Zil.Datalog.Attach

/-!
# Theorem-intent contract audit

physlib carries two independent ZIL subsystems that have never been cross-checked. The `@[zil_level …]`
attribute stamps each theorem with a native `Zil.Datalog.TheoremIntent` — its declared abstraction level
(`physicalTheorem`, `bridgeTheorem`, …), read back by `Zil.Datalog.theoremIntents`. Separately, the
`zil attach` blocks build the knowledge graph of `formalizes` / `supported_by` / `caveat` edges. The
intent says what a theorem *claims to be*; the graph says what it *has*.

This audit joins them. A theorem that declares an abstraction level but carries no `formalizes` edge is
declared-but-ungraphed; a `physicalTheorem`/`bridgeTheorem` with no `supported_by` edge cites no support
for the level it claims. Both are contract gaps no single subsystem can see.

Leaf module: it imports the whole `Physlib` library and logs the audit at build time via
`#zil_intent_audit`. Not part of the default build — run on demand:

```
lake build Physlib.Meta.TheoremIntentAudit
```
-/

open Lean

namespace Physlib.Meta.TheoremIntentAudit

@[expose] public section

/-- Read the native theorem-intents, cross-reference each against the `zil attach` graph, and format the
contract audit. -/
meta def audit (env : Environment) : MessageData := Id.run do
  let intents := Zil.Datalog.theoremIntents env
  let attachments := Zil.Datalog.declarationAttachments env
  let hasRel (d : Name) (rel : String) : Bool :=
    attachments.any fun a => a.declaration == d && a.atom.relation == rel
  let byLevel := intents.foldl (init := (∅ : Std.HashMap String Nat)) fun m i =>
    let k := i.level.label; m.insert k (m.getD k 0 + 1)
  let unformalized := intents.filter fun i => !hasRel i.declaration "formalizes"
  let unsupported := intents.filter fun i => !hasRel i.declaration "supported_by"
  let mut s := s!"physlib theorem-intent (@[zil_level]) contract audit\n"
  s := s ++ s!"  intents: {intents.size}\n"
  s := s ++ s!"  by level: {byLevel.toList.toArray.qsort (·.2 > ·.2) |>.map (fun (l, n) => s!"{l}={n}")}\n"
  s := s ++ s!"  [gap] declared but not in the graph (no `formalizes` edge): {unformalized.size}\n"
  for i in unformalized.toList.take 12 do
    s := s ++ s!"        · {i.level.label}  {i.declaration}\n"
  s := s ++ s!"  [gap] level claimed with no cited support (no `supported_by` edge): {unsupported.size}\n"
  for i in unsupported.toList.take 8 do
    s := s ++ s!"        · {i.level.label}  {i.declaration}\n"
  return m!"{s}"

/-- **`#zil_intent_audit`** — cross-reference the native theorem-intents with the knowledge graph and log
the contract gaps. -/
syntax (name := zilIntentAuditCmd) "#zil_intent_audit" : command

@[command_elab zilIntentAuditCmd]
meta def elabZilIntentAudit : Elab.Command.CommandElab := fun _ => do
  logInfo (audit (← getEnv))

end

end Physlib.Meta.TheoremIntentAudit

#zil_intent_audit
