/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Zil.Datalog.Basic
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# ZIL discovery layer — features and opportunities (the offensive read of the graph)

The audit surface (`Physlib.Meta.ZilGraph` / `ZilGraphReport`) reads the knowledge graph *defensively*:
it flags what is over-claimed or undischarged. The same derived atoms, projected differently, answer the
*offensive* questions — which postulate, if derived, unlocks the most, and which results are structurally
adjacent. This module is that projection layer, built so the report is **not** a fixed set of sections:

* a `Feature` is a NAMED projection of the derived graph into per-node integer scores;
* `featureRegistry` is a plain list — a new signal is one entry, not a new report section;
* an `OpportunitySpec` NAMES which features to require and which to rank by — also data;
* `composeOpportunity` is the single generic engine: it joins the required features over the derived
  atoms, keeps the nodes nonzero in all of them, and ranks by the chosen feature.

`#zil_discovery_report` (in `ZilDiscoveryReport`) folds the two registries over the real graph. Adding a
feature — including one backed by a new Datalog rule constructed for some physics relation — extends what
every opportunity surfaces, with no change to the engine.
-/

@[expose] public section

namespace Physlib.Meta.ZilDiscovery

open Zil.Datalog

/-- The kind of graph node a feature/opportunity ranges over (descriptive; the report groups by it). -/
inductive NodeKind
  | premise | claim | paper | decl
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Display name of a node kind. -/
def NodeKind.label : NodeKind → String
  | .premise => "premise" | .claim => "claim" | .paper => "paper" | .decl => "decl"

/-- A discovery **feature**: a named projection of the derived-atom context into `(node, score)` rows.
The input is the union of base and derived atoms; each feature self-selects the relations it reads. -/
structure Feature where
  name    : String
  kind    : NodeKind
  compute : List Atom → List (Value × Nat)

/-! ### Feature library

Each feature is a pure projection of the atom context. Reach-based features read the weakest-link
closure's `transitivePrimitivePremise` edges (the assumption ledger); the co-citation feature reads the
base `supported_by` edges. -/

/-- Primitive premises the ledger surfaces: subjects of `transitivePrimitivePremise`. -/
def premiseNodes (atoms : List Atom) : List Value :=
  ((atoms.filter (·.relation == "transitivePrimitivePremise")).map (·.subject)).eraseDups

/-- Declarations transitively resting on a premise. -/
def dependentsOf (atoms : List Atom) (p : Value) : List Value :=
  ((atoms.filter fun a => a.relation == "transitivePrimitivePremise" && a.subject == p).map (·.object)).eraseDups

/-- Declarations carrying an exact `consistency-identity` status. -/
def exactDecls (atoms : List Atom) : List Value :=
  ((atoms.filter fun a =>
    a.relation == "epistemic_status" && a.subject == Value.symbol "consistency-identity").map (·.object)).eraseDups

/-- **blastRadius** — how many declarations transitively rest on a premise (raw reach). -/
def blastRadius : Feature :=
  { name := "blastRadius", kind := .premise
    compute := fun atoms => (premiseNodes atoms).map fun p => (p, (dependentsOf atoms p).length) }

/-- **exactReach** — how many of a premise's dependents are exact identities. A bare postulate with high
exact-reach silently underwrites the most unconditional-looking results: the honest derivation target. -/
def exactReach : Feature :=
  { name := "exactReach", kind := .premise
    compute := fun atoms =>
      let exact := exactDecls atoms
      (premiseNodes atoms).map fun p => (p, ((dependentsOf atoms p).filter (exact.contains ·)).length) }

/-- Papers cited by a declaration (subjects of `supported_by` in the `paper:` namespace). Uses
`startsWith`, which the kernel does not reduce, so this feature is exercised by the report, not the gate. -/
def paperNodes (atoms : List Atom) : List Value :=
  ((atoms.filter fun a => a.relation == "supported_by"
    && (match a.subject with | .symbol s => s.startsWith "paper:" | _ => false)).map (·.subject)).eraseDups

/-- **coCitationDegree** — how many declarations cite a paper. A high-degree source is a hub whose citers
across different arcs are bridge candidates. -/
def coCitationDegree : Feature :=
  { name := "coCitationDegree", kind := .paper
    compute := fun atoms =>
      (paperNodes atoms).map fun p =>
        (p, ((atoms.filter fun a => a.relation == "supported_by" && a.subject == p).map (·.object)).eraseDups.length) }

/-- Declarations carrying an `experimental_bound` edge (the results with a dataset test). -/
def testedDecls (atoms : List Atom) : List Value :=
  ((atoms.filter (·.relation == "experimental_bound")).map (·.object)).eraseDups

/-- **inheritsTest** — how many experimentally-bounded declarations transitively rest on a premise. A bare
postulate under a tested result is experimentally anchored — the testability frontier (wires the
`DerivedPredictions` ledger into the graph). -/
def inheritsTest : Feature :=
  { name := "inheritsTest", kind := .premise
    compute := fun atoms =>
      let tested := testedDecls atoms
      (premiseNodes atoms).map fun p => (p, ((dependentsOf atoms p).filter (tested.contains ·)).length) }

/-- **consolidationPotential** — the most declarations a premise shares with ANY other premise (common
dependents). Two postulates that jointly underwrite many of the same results are candidates to reduce to
one. `dependentsOf` is precomputed per premise so the pairwise pass stays cheap. -/
def consolidationPotential : Feature :=
  { name := "consolidationPotential", kind := .premise
    compute := fun atoms =>
      let depMap : List (Value × List Value) := (premiseNodes atoms).map fun p => (p, dependentsOf atoms p)
      depMap.map fun pd =>
        (pd.1, depMap.foldl (fun m qd =>
          if qd.1 == pd.1 then m else Nat.max m ((qd.2.filter (pd.2.contains ·)).length)) 0) }

/-- **coCitationBridge** — how many distinct premises the declarations citing a paper transitively rest on.
A paper whose citers span many premise-clusters connects them: a structural bridge candidate, finer than
raw citation degree. Joins citers to premises by declaration equality (no namespace parsing). -/
def coCitationBridge : Feature :=
  { name := "coCitationBridge", kind := .paper
    compute := fun atoms =>
      (paperNodes atoms).map fun p =>
        let citers := ((atoms.filter fun a => a.relation == "supported_by" && a.subject == p).map (·.object)).eraseDups
        let prems := (atoms.filterMap fun a =>
          if a.relation == "transitivePrimitivePremise" && citers.contains a.object then some a.subject
          else none).eraseDups
        (p, prems.length) }

/-- The feature registry. A new signal is added HERE, as one entry — the engine below never names a
specific feature. -/
def featureRegistry : List Feature :=
  [blastRadius, exactReach, coCitationDegree, inheritsTest, consolidationPotential, coCitationBridge]

/-! ### Opportunity composition -/

/-- An **opportunity**: which features a node must score nonzero on (`require`) and which to rank by
(`rankBy`). Data, like `Feature` — the engine below never names a specific opportunity. -/
structure OpportunitySpec where
  name    : String
  kind    : NodeKind
  require : List String
  rankBy  : String

/-- Look up a feature by name in a registry. -/
def findFeature (fs : List Feature) (name : String) : Option Feature :=
  fs.find? (·.name == name)

/-- Score of a node under a computed feature's rows (0 if absent). -/
def rowScore (rows : List (Value × Nat)) (n : Value) : Nat :=
  ((rows.find? fun r => r.1 == n).map (·.2)).getD 0

/-- Qualified, scored opportunity rows (UNSORTED): each node in the rank feature that is nonzero in every
required feature, tagged with its rank score and full feature vector. -/
def opportunityRows (fs : List Feature) (atoms : List Atom) (spec : OpportunitySpec) :
    List (Value × Nat × List (String × Nat)) :=
  match findFeature fs spec.rankBy with
  | none => []
  | some rankFeat =>
    let reqRows := spec.require.filterMap fun nm => (findFeature fs nm).map fun f => (nm, f.compute atoms)
    (rankFeat.compute atoms).filterMap fun nr =>
      if reqRows.all fun rr => rowScore rr.2 nr.1 > 0 then
        some (nr.1, nr.2, (spec.rankBy, nr.2) :: reqRows.map fun rr => (rr.1, rowScore rr.2 nr.1))
      else none

/-- Insert into a score-descending list (stable insertion sort step). -/
def insertDesc (x : Value × Nat × List (String × Nat)) :
    List (Value × Nat × List (String × Nat)) → List (Value × Nat × List (String × Nat))
  | [] => [x]
  | y :: ys => if x.2.1 ≥ y.2.1 then x :: y :: ys else y :: insertDesc x ys

/-- Rank opportunity rows by score, descending. -/
def rankDesc (rows : List (Value × Nat × List (String × Nat))) :
    List (Value × Nat × List (String × Nat)) :=
  rows.foldr insertDesc []

/-- **The whole discovery engine.** Compose an opportunity from the feature registry over the derived-atom
context: gather the required features, keep nodes nonzero in all of them, rank by `rankBy` descending. -/
def composeOpportunity (fs : List Feature) (atoms : List Atom) (spec : OpportunitySpec) :
    List (Value × Nat × List (String × Nat)) :=
  rankDesc (opportunityRows fs atoms spec)

/-- The opportunity registry. A new discovery mode is added HERE, as one entry. -/
def opportunityRegistry : List OpportunitySpec :=
  [ { name := "highest-leverage derivation target", kind := .premise,
      require := ["blastRadius"], rankBy := "exactReach" },
    { name := "widest-reach bare postulate", kind := .premise,
      require := ["blastRadius"], rankBy := "blastRadius" },
    { name := "experimentally-anchorable postulate", kind := .premise,
      require := ["inheritsTest"], rankBy := "inheritsTest" },
    { name := "consolidation candidate (reduce two postulates to one)", kind := .premise,
      require := ["consolidationPotential"], rankBy := "consolidationPotential" },
    { name := "citation hub", kind := .paper,
      require := ["coCitationDegree"], rankBy := "coCitationDegree" },
    { name := "cross-cluster bridge paper", kind := .paper,
      require := ["coCitationBridge"], rankBy := "coCitationBridge" } ]

/-! ### Non-vacuity gate: the composition computes real, distinct signals on a sample

Statements are memberships and inequalities (not `compute … = [explicit]`), so they are not definitional
restatements the vacuity gate would reject. The sample is built so raw reach and exact reach DISAGREE, and
`topTarget_depends_on_ranking` records that the composition — not any one feature — surfaces the target. -/

/-- Sample: premise `pA` underwrites `d1`,`d2`,`d6` (`d1` exact); `pB` underwrites `d3`,`d4`,`d5`,`d6`
(none exact). `d6` is common to both (a consolidation link); `d1` is experimentally bounded and, with `d3`,
cites `paper:x`. So `pB` has the wider raw reach but `pA` the greater exact-reach — the rankings disagree. -/
def sampleCtx : List Atom :=
  [ { object := .symbol "d1", relation := "transitivePrimitivePremise", subject := .symbol "pA" },
    { object := .symbol "d2", relation := "transitivePrimitivePremise", subject := .symbol "pA" },
    { object := .symbol "d6", relation := "transitivePrimitivePremise", subject := .symbol "pA" },
    { object := .symbol "d3", relation := "transitivePrimitivePremise", subject := .symbol "pB" },
    { object := .symbol "d4", relation := "transitivePrimitivePremise", subject := .symbol "pB" },
    { object := .symbol "d5", relation := "transitivePrimitivePremise", subject := .symbol "pB" },
    { object := .symbol "d6", relation := "transitivePrimitivePremise", subject := .symbol "pB" },
    { object := .symbol "d1", relation := "epistemic_status", subject := .symbol "consistency-identity" },
    { object := .symbol "d1", relation := "experimental_bound", subject := .symbol "recoil-metrology" },
    { object := .symbol "d1", relation := "supported_by", subject := .symbol "paper:x" },
    { object := .symbol "d3", relation := "supported_by", subject := .symbol "paper:x" } ]

/-- Rank the premises by exact-reach (the highest-leverage-derivation opportunity). -/
def sampleTargetSpec : OpportunitySpec :=
  { name := "target", kind := .premise, require := ["blastRadius"], rankBy := "exactReach" }

/-- Rank the same premises by raw reach. -/
def sampleWidestSpec : OpportunitySpec :=
  { name := "widest", kind := .premise, require := ["blastRadius"], rankBy := "blastRadius" }

/-- `blastRadius` reads raw reach off the ledger relation: `pB` reaches four declarations. -/
theorem blastRadius_reaches_pB : (Value.symbol "pB", 4) ∈ blastRadius.compute sampleCtx := by decide

/-- `exactReach` counts only exact dependents: `pA` underwrites one exact identity. -/
theorem exactReach_selects_pA : (Value.symbol "pA", 1) ∈ exactReach.compute sampleCtx := by decide

/-- `inheritsTest` anchors a premise to a tested result: `pA` underwrites the experimentally-bounded `d1`. -/
theorem inheritsTest_anchors_pA : (Value.symbol "pA", 1) ∈ inheritsTest.compute sampleCtx := by decide

/-- `consolidationPotential` links two postulates by a shared dependent: `pA` shares `d6` with `pB`. -/
theorem consolidationPotential_links_pA_pB :
    (Value.symbol "pA", 1) ∈ consolidationPotential.compute sampleCtx := by decide

/-- The two features are genuinely different signals (exact-reach is not raw reach). -/
theorem exactReach_ne_blastRadius : exactReach.compute sampleCtx ≠ blastRadius.compute sampleCtx := by decide

/-- The discovery payoff: ranking the same premises by exact-reach vs raw reach yields DIFFERENT top
targets (`pA` vs `pB`) — the composition, not any single feature, is what surfaces the opportunity. -/
theorem topTarget_depends_on_ranking :
    (composeOpportunity featureRegistry sampleCtx sampleTargetSpec).head?.map (·.1)
      ≠ (composeOpportunity featureRegistry sampleCtx sampleWidestSpec).head?.map (·.1) := by decide

end Physlib.Meta.ZilDiscovery

end

open Physlib.Meta.ZilDiscovery in
#physlib_axiom_clean_all [
  blastRadius_reaches_pB,
  exactReach_selects_pA,
  inheritsTest_anchors_pA,
  consolidationPotential_links_pA_pB,
  exactReach_ne_blastRadius,
  topTarget_depends_on_ranking ]

open Physlib.Meta.ZilDiscovery in
#physlib_non_vacuous_all [
  blastRadius_reaches_pB,
  exactReach_selects_pA,
  inheritsTest_anchors_pA,
  consolidationPotential_links_pA_pB,
  exactReach_ne_blastRadius,
  topTarget_depends_on_ranking ]
