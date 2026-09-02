/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.DerivedPredictions
meta import Zil.Datalog.FormalizationContract
meta import Zil.Datalog.Attach

/-!
# Program-health synthesis

One dashboard over the whole knowledge graph and the native `@[zil_level]` theorem-intents. The individual
audits each answer one question; the value is in crossing them. `#physlib_program_health` reports:

* **Rigor tiers** — the `epistemic_status` distribution (how much rests on exact identities vs loaded
  ansätze vs risky steps).
* **Rigor-weighted gaps** — predictions that are *both* risky/ansatz-loaded *and* untested (no
  `experimental_bound`): the highest-priority weaknesses, which no single count reveals.
* **Foundational spine and risk** — the load-bearing assumptions and papers, and specifically the
  assumptions that underwrite risky claims (where one fix has the most leverage).
* **Cross-consistency** — theorem-intents with no graph anchor, and `physical`/`bridge`-level theorems
  supported only by internal lemmas (a physics claim resting on no external result).

Leaf module: imports the whole library and logs the dashboard at build time. Not in the default build —
run on demand or via `scripts/physlib-program-health.sh`.
-/

open Lean

namespace Physlib.Meta.ProgramHealth

@[expose] public section

meta def valStr : Zil.Datalog.Value → String
  | .symbol s => s | .string s => s | .integer i => toString i | .boolean b => toString b

/-- Whether a status names a not-yet-rigorous tier. -/
meta def isLoaded (s : String) : Bool := s == "risky" || s == "ansatz-loaded"

meta def topN (m : Std.HashMap String Nat) (n : Nat) : List (String × Nat) :=
  (m.toList.toArray.qsort (·.2 > ·.2)).toList.take n

/-- Compute the program-health dashboard from the environment. -/
meta def programHealth (env : Environment) : MessageData := Id.run do
  let atts := Zil.Datalog.declarationAttachments env
  let intents := Zil.Datalog.theoremIntents env
  let hasRel (d : Name) (rel : String) : Bool :=
    atts.any fun a => a.declaration == d && a.atom.relation == rel
  let subjectsOf (d : Name) (rel : String) : Array String :=
    (atts.filter fun a => a.declaration == d && a.atom.relation == rel).map fun a => valStr a.atom.subject
  let statusOf (d : Name) : Option String :=
    (atts.find? fun a => a.declaration == d && a.atom.relation == "epistemic_status").map
      fun a => valStr a.atom.subject
  let declsWith (rel : String) : List Name :=
    ((atts.filter (·.atom.relation == rel)).map (·.declaration)).toList.eraseDups

  -- §1 rigor tiers
  let statusHist : Std.HashMap String Nat :=
    (atts.filter (·.atom.relation == "epistemic_status")).foldl (init := {}) fun m a =>
      let k := valStr a.atom.subject; m.insert k (m.getD k 0 + 1)
  let allowedStatuses := ["inversion", "consistency-identity", "ansatz-loaded", "risky", "conditional-model"]
  let outOfVocab := (declsWith "epistemic_status").filter fun d =>
    match statusOf d with | some st => !allowedStatuses.contains st | none => false

  -- §2 rigor-weighted gaps. A missing experimental_bound is a real gap only for a numerical prediction
  -- (derives → constant); a derived claim or law (derives → claim/law) is a formal result, not a
  -- falsifiable numeric, so it is reported separately rather than as "untested".
  let derivesToPrefix (pfx : String) : List Name :=
    ((atts.filter fun a => a.atom.relation == "derives" && (valStr a.atom.subject).startsWith pfx).map
      (·.declaration)).toList.eraseDups
  let numericalPreds := derivesToPrefix "constant:"
  let untestedNumerical := numericalPreds.filter fun d => !hasRel d "experimental_bound"
  let riskyUntestedNum := untestedNumerical.filter fun d => (statusOf d).any isLoaded
  let formalDerivs := (derivesToPrefix "claim:" ++ derivesToPrefix "law:").eraseDups
  let loadedDecls := declsWith "epistemic_status" |>.filter fun d => (statusOf d).any isLoaded
  let loadedUnsupported := loadedDecls.filter fun d => hasRel d "formalizes" && !hasRel d "supported_by"
  let loadedUncaveated := loadedUnsupported.filter fun d => !hasRel d "caveat"

  -- §3 foundational spine and risk
  let requiresHist : Std.HashMap String Nat :=
    (atts.filter (·.atom.relation == "requires")).foldl (init := {}) fun m a =>
      let k := valStr a.atom.subject; m.insert k (m.getD k 0 + 1)
  let paperHist : Std.HashMap String Nat :=
    (atts.filter fun a => a.atom.relation == "supported_by" && (valStr a.atom.subject).startsWith "paper:").foldl
      (init := {}) fun m a => let k := valStr a.atom.subject; m.insert k (m.getD k 0 + 1)
  let riskBearing : Std.HashMap String Nat :=
    loadedDecls.foldl (init := {}) fun m d =>
      (subjectsOf d "requires").foldl (fun m2 s => m2.insert s (m2.getD s 0 + 1)) m

  -- §4 cross-consistency. Internal-only support is a concern for a physical claim, but often expected
  -- for a bridge theorem (which by design rests on internal formalisms), so keep them separate.
  let internalOnly : Zil.Datalog.TheoremIntent → Bool := fun i =>
    let sups := subjectsOf i.declaration "supported_by"
    sups.size > 0 && sups.all (·.startsWith "lean:")
  let ungraphed := intents.filter fun i => !hasRel i.declaration "formalizes"
  let selfRefPhysical := (intents.filter (·.level == .physicalTheorem)).filter internalOnly
  let selfRefBridge := (intents.filter (·.level == .bridgeTheorem)).filter internalOnly

  -- §5 solid core: the positive complement of the gaps
  let exactCore := (declsWith "epistemic_status").filter fun d =>
    match statusOf d with | some st => st == "consistency-identity" || st == "inversion" | none => false
  let anchoredPreds := numericalPreds.filter fun d => hasRel d "experimental_bound"
  let externallyGrounded :=
    ((atts.filter fun a => a.atom.relation == "supported_by" && (valStr a.atom.subject).startsWith "paper:").map
      (·.declaration)).toList.eraseDups

  -- §6 hidden epistemic debt: a claim with no caveat of its own that transitively requires (via
  -- requires ⋈ formalizes) a claim some *caveated* theorem formalizes — it looks clean but rests on a
  -- hedged foundation. Computed as a bounded least-fixpoint over the direct-dependency map.
  let provesClaim : Std.HashMap String (Array Name) :=
    (atts.filter (·.atom.relation == "formalizes")).foldl (init := {}) fun m a =>
      let k := valStr a.atom.subject; m.insert k ((m.getD k #[]).push a.declaration)
  let formalizers := declsWith "formalizes"
  let depsMap : Std.HashMap Name (Array Name) :=
    formalizers.foldl (init := {}) fun m d =>
      m.insert d ((subjectsOf d "requires").foldl (init := #[]) fun acc rc => acc ++ provesClaim.getD rc #[])
  let mut reaches : Std.HashSet Name := {}
  for d in formalizers do
    if (depsMap.getD d #[]).any (hasRel · "caveat") then reaches := reaches.insert d
  for _ in [0:32] do
    for d in formalizers do
      if !reaches.contains d && (depsMap.getD d #[]).any reaches.contains then reaches := reaches.insert d
  let hiddenDebtDirect := formalizers.filter fun d =>
    !hasRel d "caveat" && (depsMap.getD d #[]).any (hasRel · "caveat")
  let hiddenDebt := formalizers.filter fun d => !hasRel d "caveat" && reaches.contains d

  let mut s := s!"# physlib program-health synthesis\n\n"
  s := s ++ s!"graph: {atts.size} edges;  theorem-intents: {intents.size}\n\n"
  s := s ++ s!"## 1. Rigor tiers (epistemic_status)\n"
  for (k, n) in topN statusHist 8 do s := s ++ s!"  {k}: {n}\n"
  s := s ++ s!"\n## 2. Rigor-weighted gaps\n"
  s := s ++ s!"  numerical predictions (derives→constant): {numericalPreds.length};  \
    untested (no experimental_bound): {untestedNumerical.length}\n"
  s := s ++ s!"  ** risky/ansatz-loaded numerical predictions that are untested (top priority): \
    {riskyUntestedNum.length} **\n"
  for d in riskyUntestedNum.take 8 do s := s ++ s!"      · {d}\n"
  s := s ++ s!"  formal derivations (derives→claim/law, not falsifiable numerics): {formalDerivs.length}\n"
  s := s ++ s!"  ** loaded claims (risky/ansatz) with no supporting source: {loadedUnsupported.length} \
    (of these {loadedUncaveated.length} carry no caveat either — undisclosed, the sharpest concern) **\n"
  s := s ++ s!"    undisclosed (no source, no caveat):\n"
  for d in loadedUncaveated do s := s ++ s!"      · {d}\n"
  s := s ++ s!"\n## 3. Foundational spine and risk\n"
  s := s ++ s!"  most load-bearing assumptions:\n"
  for (k, n) in topN requiresHist 6 do s := s ++ s!"      {n}×  {k}\n"
  s := s ++ s!"  most-cited external papers:\n"
  for (k, n) in topN paperHist 6 do s := s ++ s!"      {n}×  {k}\n"
  s := s ++ s!"  ** assumptions underwriting risky/ansatz claims (highest leverage): **\n"
  for (k, n) in topN riskBearing 8 do s := s ++ s!"      {n} risky claims ←  {k}\n"
  s := s ++ s!"\n## 4. Cross-consistency\n"
  s := s ++ s!"  theorem-intents with no `formalizes` anchor: {ungraphed.size}\n"
  s := s ++ s!"  ** physical-theorem claims supported only by internal lemmas (the real concern): \
    {selfRefPhysical.size} **\n"
  for i in selfRefPhysical.toList.take 8 do s := s ++ s!"      · {i.declaration}\n"
  s := s ++ s!"  bridge-theorem claims supported only by internal lemmas: {selfRefBridge.size} \
    (usually expected — a bridge rests on internal formalisms)\n"
  s := s ++ s!"\n## 5. Solid core (positive complement)\n"
  s := s ++ s!"  exact identities (consistency-identity / inversion status): {exactCore.length}\n"
  s := s ++ s!"  anchored numerical predictions (derives→constant with an experimental_bound): \
    {anchoredPreds.length} of {numericalPreds.length}\n"
  s := s ++ s!"  claims with external (paper) support: {externallyGrounded.length}\n"
  s := s ++ s!"\n## 6. Hidden epistemic debt\n"
  s := s ++ s!"  ** uncaveated claims that transitively rest on a caveated foundation (look clean, but a \
    dependency is hedged): {hiddenDebt.length} ({hiddenDebtDirect.length} directly) **\n"
  for d in hiddenDebt.take 8 do s := s ++ s!"      · {d}\n"
  let json := "{" ++ s!"\"edges\":{atts.size}, \"exact_identities\":{exactCore.length}, \
    \"untested_numerical\":{untestedNumerical.length}, \"loaded_uncited\":{loadedUnsupported.length}, \
    \"undisclosed\":{loadedUncaveated.length}, \"out_of_vocab\":{outOfVocab.length}, \
    \"physics_internal_only\":{selfRefPhysical.size}, \"hidden_debt\":{hiddenDebt.length}" ++ "}"
  s := s ++ s!"\n## metrics (diffable)\n{json}\n"
  return m!"{s}"

/-- **`#physlib_program_health`** — log the program-health dashboard for the current environment. -/
syntax (name := programHealthCmd) "#physlib_program_health" : command

@[command_elab programHealthCmd]
meta def elabProgramHealth : Elab.Command.CommandElab := fun _ => do
  logInfo (programHealth (← getEnv))

end

end Physlib.Meta.ProgramHealth

#physlib_program_health
