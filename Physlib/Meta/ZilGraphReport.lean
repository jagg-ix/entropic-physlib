/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public meta import Physlib.Meta.ZilGraph
public meta import Physlib.Meta.ZilDatalogFast
public import Physlib.Meta.DerivedPredictions
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE
meta import Zil.Datalog.Attach

/-!
# Repo-wide ZIL knowledge-graph audit

The report surface for `Physlib.Meta.ZilGraph`: it extracts every `zil attach` edge reachable from this
module's imports (`declarationAttachments`, a `meta` extension), runs the verified improvement rules
through the ZIL Datalog engine, and logs the CAT/EPT gap audit at build time via `#zil_graph_report`.

This is a leaf tool, not a proof — the machine-checked content (that the gap rules fire exactly on the
untested/unsupported edges) lives in `Physlib.Meta.ZilGraph`. Import more physlib content above to widen
the audit; import the full `Physlib` root for the complete repo-wide picture.
-/

open Lean
open Zil.Datalog
open Physlib.Meta.ZilGraph
open Physlib.Meta.ZilDatalogFast

namespace Physlib.Meta.ZilGraphReport

@[expose] public section

/-- The base relations the improvement rules read; the rest of the graph is irrelevant to gap detection
and is filtered out before the (list-based) engine runs. -/
meta def relevantRelations : List String :=
  ["derives", "experimental_bound", "formalizes", "supported_by", "prediction_class", "epistemic_status",
   "requires", "caveat", "assumes_primitive", "open_problem_scope"]

/-- Extract the physlib knowledge graph from an environment as ground atoms (attributes dropped so
structurally equal edges deduplicate). -/
meta def extractFacts (env : Environment) : List Atom :=
  (Zil.Datalog.declarationAttachments env).toList.map fun a =>
    { object := a.atom.object, relation := a.atom.relation, subject := a.atom.subject }

/-- Render a ground value for the audit log. -/
meta def renderValue : Value → String
  | .symbol s => s
  | .string s => s
  | .integer i => toString i
  | .boolean b => toString b

/-- Count atoms carrying a given relation. -/
meta def countRel (relation : String) (atoms : List Atom) : Nat :=
  (atoms.filter (·.relation == relation)).length

/-- Run the improvement rules over the graph in `env` and format the CAT/EPT gap audit. -/
meta def runReportMessage (env : Environment) : MessageData := Id.run do
  let facts := extractFacts env
  let relevant := facts.filter fun a => relevantRelations.contains a.relation
  -- inject the reference vocabulary (invalidStatusRule), the canonical-alias table (the primitive-vs-derived
  -- cross-module guard) and the conformance policy (the scenario-adaptive nonconformant check)
  let closed := deriveProgramFast
    { facts := relevant ++ allowedStatusFacts ++ canonicalAliases ++ conformancePolicy
        ++ premiseKinds ++ exactIdentityStatusFacts ++ premiseAliases
      rules := improvementRules } 8
  let decls (relation : String) : List Value :=
    (closed.filter (·.relation == relation) |>.map (·.object)).eraseDups
  let untestedDecls := decls "untestedPrediction"
  let unclassifiedDecls := decls "unclassifiedPrediction"
  let unstatusedDecls := decls "unstatusedPrediction"
  let unsupportedDecls := decls "unsupportedClaim"
  let openScoped := (relevant.filter (·.relation == "open_problem_scope") |>.map (·.object)).eraseDups
  let invalidStatusDecls := decls "invalidEpistemicStatus"
  -- dependency cycles: bounded transitive closure over `requires`, run separately from the gap rules
  let requiresFacts := facts.filter (·.relation == "requires")
  let depClosed := deriveProgramFast { facts := requiresFacts, rules := dependencyRules } 8
  let cycleDecls := (depClosed.filter (·.relation == "circularDependency") |>.map (·.object)).eraseDups
  -- weakest-link: the declaration-dependency closure (`requires`∘`establishes`) + buried-conditionality,
  -- run separately (the closure is O(n²)) like the cycle check, and depth-bounded (fuel 6)
  let wlFacts := facts.filter fun a =>
    a.relation == "requires" || a.relation == "formalizes" || a.relation == "derives"
      || a.relation == "epistemic_status" || a.relation == "discloses"
      || (a.relation == "supported_by" && (renderValue a.subject).startsWith "lean:")
  let wlClosed := deriveProgramFast
    { facts := wlFacts ++ statusStrictlyStronger ++ premiseAliases, rules := weakestLinkRules } 3
  let buriedDecls := (wlClosed.filter (·.relation == "buriedConditionality") |>.map (·.object)).eraseDups
  -- assumption ledger: the transitive primitive-premise footprint (grounding-tree leaves) + the size of
  -- the declaration-dependency graph (op3.md's PR-4 assumption engine)
  let primitivePremises :=
    (wlClosed.filter (·.relation == "transitivePrimitivePremise") |>.map (·.subject)).eraseDups
  let declDeps := (wlClosed.filter (·.relation == "dependsOnDecl")).length
  let mut s := s!"physlib ZIL knowledge-graph audit\n"
  s := s ++ s!"  edges: {facts.length} total; {relevant.length} feed the gap rules\n"
  s := s ++ s!"    formalizes={countRel "formalizes" facts} supported_by={countRel "supported_by" facts} \
    caveat={countRel "caveat" facts} requires={countRel "requires" facts} \
    epistemic_status={countRel "epistemic_status" facts} \
    prediction_class={countRel "prediction_class" facts} derives={countRel "derives" facts}\n"
  s := s ++ s!"  [derives coverage] declarations deriving a prediction that lacks:\n"
  s := s ++ s!"    · experimental_bound (untested): {untestedDecls.length}\n"
  s := s ++ s!"    · prediction_class (unclassified): {unclassifiedDecls.length}\n"
  s := s ++ s!"    · epistemic_status (unstatused): {unstatusedDecls.length}\n"
  s := s ++ s!"  [value] declarations whose epistemic_status is out of vocabulary: \
    {invalidStatusDecls.length}\n"
  for d in invalidStatusDecls.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  s := s ++ s!"  [source] declarations formalizing an unsupported claim (no supported_by): \
    {unsupportedDecls.length}\n"
  for d in unsupportedDecls.take 12 do
    s := s ++ s!"        · {renderValue d}\n"
  s := s ++ s!"  [source] declarations exempt as declared open-program entries \
    (open_problem_scope): {openScoped.length}\n"
  s := s ++ s!"  [dependency] circular requires-chains (transitive, up to depth 8): {cycleDecls.length}\n"
  for d in cycleDecls.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  s := s ++ s!"  [coverage] fully documented predictions (derives + bound + class + status): \
    {(decls "wellDocumentedPrediction").length}\n"
  let primitiveGap := (decls "assumedPrimitiveButDerived" ++ decls "assumedPrimitiveButCanonicallyDerived").eraseDups
  s := s ++ s!"  [consistency] quantities declared primitive that the graph derives \
    (assumes_primitive vs derives, direct + canonical): {primitiveGap.length}\n"
  for d in primitiveGap.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  let evidenceGap := decls "undisclosedEvidenceGap"
  s := s ++ s!"  [evidence-scope] experimentally-anchored claims whose required premise no evidence \
    reaches, undisclosed: {evidenceGap.length}\n"
  for d in evidenceGap.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  let nonconformantDecls := decls "nonconformant"
  s := s ++ s!"  [adaptive conformance] claims not meeting the standard their epistemic_status demands \
    (policy-driven): {nonconformantDecls.length}\n"
  for d in nonconformantDecls.take 12 do
    s := s ++ s!"        · {renderValue d}\n"
  let statusOverclaimDecls := decls "statusOverclaim"
  s := s ++ s!"  [honesty] exact `consistency-identity` claims resting on an undischarged physical \
    postulate (status over-claim; honest status = conditional-model): {statusOverclaimDecls.length}\n"
  for d in statusOverclaimDecls.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  let unclassifiedExactPremises :=
    (closed.filter (·.relation == "unclassifiedExactPremise") |>.map (·.subject)).eraseDups
  s := s ++ s!"  [honesty:triage] undischarged premises of exact identities awaiting physical/math \
    classification in `premiseKinds`: {unclassifiedExactPremises.length}\n"
  for d in unclassifiedExactPremises.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  let premiseMislabels :=
    (closed.filter (·.relation == "premiseAssumedButDerived") |>.map (·.subject)).eraseDups
  s := s ++ s!"  [premise-hygiene] `assumption:`-labelled premises whose content the graph derives under \
    another token (cross-name; discharged, so no honesty flag): {premiseMislabels.length}\n"
  for d in premiseMislabels.take 10 do
    s := s ++ s!"        · {renderValue d}\n"
  s := s ++ s!"  [weakest-link] exact `consistency-identity` claims that transitively rest on a \
    weaker-status (ansatz/conditional/risky) declaration — buried conditionality (depth-bounded): \
    {buriedDecls.length}\n"
  for d in buriedDecls.take 12 do
    s := s ++ s!"        · {renderValue d}\n"
  s := s ++ s!"  [assumption-ledger] distinct primitive premises (bare postulates nothing establishes) the \
    program transitively rests on: {primitivePremises.length}\n"
  -- foundational risk: for each primitive premise, its reach (declarations transitively resting on it) and
  -- exact-reach (how many of those are `consistency-identity` — exact claims silently resting on a bare
  -- postulate, which `buriedConditionality` misses because a bare postulate carries no status). Ranked by
  -- exact-reach: the postulate whose failure would break the most EXACT results. Raw reach ≠ risk — a cited
  -- theorem with wide reach is firm, whereas a bare postulate underwriting exact claims is not.
  let ppAtoms := wlClosed.filter (·.relation == "transitivePrimitivePremise")
  let exactDecls := (wlClosed.filter (fun a =>
    a.relation == "epistemic_status" && renderValue a.subject == "consistency-identity")
    |>.map (·.object)).eraseDups
  let profile := primitivePremises.map fun p =>
    let deps := (ppAtoms.filter (fun a => a.subject == p) |>.map (·.object)).eraseDups
    (p, deps.length, (deps.filter (fun d => exactDecls.contains d)).length)
  let ranked := (profile.toArray.qsort (fun a b =>
    decide (a.2.2 > b.2.2 ∨ (a.2.2 = b.2.2 ∧ a.2.1 > b.2.1)))).toList
  s := s ++ s!"  [assumption-ledger:foundational-risk] primitive premises by exact-claim reach \
    (reach = all dependents; exact = consistency-identity dependents resting on this bare postulate):\n"
  for pne in ranked.take 10 do
    s := s ++ s!"        · reach={pne.2.1} exact={pne.2.2}  ← {renderValue pne.1}\n"
  let maxBlast := profile.foldl (fun m x => Nat.max m x.2.1) 0
  let maxExact := profile.foldl (fun m x => Nat.max m x.2.2) 0
  s := s ++ "  [assumption-ledger:metrics] {" ++ s!"\"decl_dependencies\":{declDeps}, \
    \"primitive_premises\":{primitivePremises.length}, \"max_blast_radius\":{maxBlast}, \
    \"max_exact_reach\":{maxExact}, \"buried_conditionality\":{buriedDecls.length}" ++ "}\n"
  return m!"{s}"

/-- **`#zil_graph_report`** — extract the physlib knowledge graph from the current environment, run the
improvement rules through the ZIL Datalog engine, and log the gap audit. -/
syntax (name := zilGraphReportCmd) "#zil_graph_report" : command

@[command_elab zilGraphReportCmd]
meta def elabZilGraphReport : Elab.Command.CommandElab := fun _ => do
  logInfo (runReportMessage (← getEnv))

end

end Physlib.Meta.ZilGraphReport

#zil_graph_report
