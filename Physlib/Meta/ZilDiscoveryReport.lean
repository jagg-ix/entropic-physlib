/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.DerivedPredictions
public import Physlib.Meta.ZilGraphReport
public meta import Physlib.Meta.ZilDiscovery
meta import Zil.Datalog.Attach

/-!
# Discovery report — offensive opportunities over the physlib knowledge graph

`#zil_discovery_report` is the offensive twin of `#zil_graph_report`. It rebuilds the weakest-link closure
(the assumption ledger's `transitivePrimitivePremise` edges) unioned with the base graph, then folds the
feature and opportunity registries of `Physlib.Meta.ZilDiscovery` over it: for each opportunity it composes
the required features and ranks the top nodes. The audit report finds what is *wrong*; this one ranks the
highest-leverage *next* targets — the postulate whose derivation would discharge the most, and the citation
hubs whose cross-arc citers are bridge candidates.

The report is a generic fold: it names no feature and no opportunity. A new signal is added as a `Feature`
in `ZilDiscovery.featureRegistry` (and, if it needs a new derived relation, a Datalog rule in `ZilGraph`),
and every opportunity that requires it gains reach with no change here.
-/

@[expose] public section

namespace Physlib.Meta.ZilDiscoveryReport

open Lean
open Zil.Datalog
open Physlib.Meta.ZilGraph
open Physlib.Meta.ZilDatalogFast
open Physlib.Meta.ZilGraphReport
open Physlib.Meta.ZilDiscovery

/-- The derived-atom context the features read: the weakest-link closure (for premise reach) unioned with
the base graph (for citations). Mirrors the `wlClosed` construction in `ZilGraphReport`. -/
meta def discoveryContext (env : Environment) : List Atom :=
  let facts := extractFacts env
  let wlFacts := facts.filter fun a =>
    a.relation == "requires" || a.relation == "formalizes" || a.relation == "derives"
      || a.relation == "epistemic_status"
      || (a.relation == "supported_by" && (renderValue a.subject).startsWith "lean:")
  let wlClosed := deriveProgramFast
    { facts := wlFacts ++ statusStrictlyStronger ++ premiseAliases, rules := weakestLinkRules } 3
  -- keep only the relations the features read: shrinks every feature's filter and `eraseDups`
  (wlClosed ++ facts).filter fun a =>
    a.relation == "transitivePrimitivePremise" || a.relation == "epistemic_status"
      || a.relation == "supported_by" || a.relation == "experimental_bound"

/-- Fold the opportunity registry over the graph, composing each from the feature registry. -/
meta def discoveryMessage (env : Environment) : MessageData := Id.run do
  let ctx := discoveryContext env
  -- compute each feature ONCE; the O(n²) premise projections are shared across every opportunity
  let cache : List (String × List (Value × Nat)) := featureRegistry.map fun f => (f.name, f.compute ctx)
  let lookup (nm : String) : List (Value × Nat) := ((cache.find? (·.1 == nm)).map (·.2)).getD []
  let mut s := s!"physlib ZIL discovery report — {opportunityRegistry.length} opportunities composed from \
    {featureRegistry.length} features (offensive read; the highest-leverage next targets)\n"
  for spec in opportunityRegistry do
    let rankRows := lookup spec.rankBy
    let qualified := rankRows.filterMap fun nr =>
      if spec.require.all fun nm => rowScore (lookup nm) nr.1 > 0 then some nr else none
    let ranked := (qualified.toArray.qsort fun a b => decide (a.2 > b.2)).toList
    s := s ++ s!"  [{spec.name}] over {spec.kind.label}, rank by {spec.rankBy} — {ranked.length} candidates:\n"
    for r in ranked.take 8 do
      let vec := String.intercalate " "
        ((spec.rankBy :: spec.require).eraseDups.map fun nm => s!"{nm}={rowScore (lookup nm) r.1}")
      s := s ++ s!"        · {renderValue r.1}   [{vec}]\n"
  return m!"{s}"

/-- **`#zil_discovery_report`** — extract the physlib knowledge graph, build the derived context, and log
the ranked opportunities composed from the feature registry. -/
syntax (name := zilDiscoveryReportCmd) "#zil_discovery_report" : command

@[command_elab zilDiscoveryReportCmd]
meta def elabZilDiscoveryReport : Elab.Command.CommandElab := fun _ => do
  logInfo (discoveryMessage (← getEnv))

end Physlib.Meta.ZilDiscoveryReport

end

#zil_discovery_report
