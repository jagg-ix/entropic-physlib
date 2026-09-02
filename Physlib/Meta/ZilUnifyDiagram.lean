/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilAnalogyUnify

/-!
# `#zil_unify_diagram` — the constraint diagram on a set of carriers

The unifier's pairwise output is a morphism: for definitions `A`, `B` the bridge constraint is
the difference `nf A − nf B` in the free abelian group on canonical binder names, so a set of
carriers spans a diagram — objects the definitions, edges the constraints.  In that
representation **composition is exact by construction**: normal forms are computed once per
definition, so differences telescope and every triangle commutes at the syntactic level.  The
command therefore does not pretend to "check" commutativity; it audits the two things that are
*not* automatic:

* **homogeneity per edge** — each constraint is dimension-checked under the given typing, the
  same kill test as `#zil_analogy_unify`;
* **proof coverage per edge** — which edges have a *connecting theorem* in the corpus: a
  Physlib theorem whose statement mentions both carriers.  The constraint is a candidate; the
  connecting theorem is the content.

From those two it derives the actionable report: **underived composites** — edges with no
connecting theorem, both of whose flanks through a third object are proven.  This is exactly
the shape in which the temperature triangle's third side was found by hand
(`comptonTemperature ≐ gibbonsHawkingTemperatureSI` had proven flanks through
`unruhTemperature` and no direct theorem, until `comptonTemperature_eq_gibbonsHawkingSI_iff`).
The command mechanizes that discovery pattern.

`#zil_assert_diagram` is the build-enforced form: it **fails** unless every edge is homogeneous
(or identical) under the given typing and every edge has a connecting theorem.  Fail-closed: an
undetermined verdict (opaque residues, unknown binders) fails the assert rather than passing it.

Honest limits: "connecting theorem" is by constant-occurrence in the statement — it certifies
that *some* proven statement ties the two carriers together, not that it is the `iff` form of
this particular constraint; and the diagram inherits every limit of the multiplicative normal
form (binder-name matching, opaque additive composites).

First run (temperature sector): the {Unruh, Compton, Gibbons–Hawking-SI} triangle reports every
edge homogeneous with a connecting theorem and `#zil_assert_diagram` passes; adding
`hawkingTemperature` as a fourth object surfaces two underived composites, both flanks proven
through the Unruh carrier: `comptonTemperature ⟶ hawkingTemperature` with constraint
`m·c³ ≐ κ·ℏ` (the surface gravity at which a horizon is as hot as the particle's rest-energy
scale), and `gibbonsHawkingTemperatureSI ⟶ hawkingTemperature` with constraint `H·c ≐ κ` (the
de Sitter horizon's surface gravity).  Two weld candidates, found by the tool.
-/

@[expose] public section

namespace Physlib.Meta.ZilUnifyDiagram

open Lean Elab Command Meta
open Physlib.Meta.ZilDimension
open Physlib.Meta.ZilAnalogyUnify

/-- Is `n` declared in a `Physlib` module? -/
meta def inPhyslibModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => m.toString.startsWith "Physlib"
    | none => false
  | none => false

/-- One environment pass: for every unordered pair of carriers, the Physlib theorems whose
statement mentions both.  Pairs are keyed in input order of the carrier array. -/
meta def connectingTheorems (env : Environment) (carriers : Array Name) :
    Std.HashMap (Name × Name) (List Name) := Id.run do
  let carrierSet : NameSet := carriers.foldl (·.insert ·) {}
  let mut conn : Std.HashMap (Name × Name) (List Name) := {}
  for (n, ci) in env.constants.toList do
    -- Imported theorems present as `.thmInfo` under classic imports but as `.axiomInfo`
    -- in module context (the module system strips proofs at the boundary).  Physlib's
    -- no-axioms policy means a Physlib-module `.axiomInfo` IS an imported theorem.
    let type? : Option Expr := match ci with
      | .thmInfo v => some v.type
      | .axiomInfo v => some v.type
      | _ => none
    if let some ty := type? then
      if inPhyslibModule env n && !ZilAnalogy.isMachineName n then
        let hits := ty.foldConsts ({} : NameSet) fun c acc =>
          if carrierSet.contains c then acc.insert c else acc
        if hits.size ≥ 2 then
          let hitList := carriers.filter hits.contains
          for i in [0:hitList.size] do
            for j in [i+1:hitList.size] do
              let key := (hitList[i]!, hitList[j]!)
              conn := conn.insert key (n :: conn.getD key [])
  return conn

meta def renderEdgeVerdict : EdgeVerdict → String
  | .identical => "IDENTICAL up to coefficient"
  | .homogeneous d => s!"HOMOGENEOUS [{renderDim d}]"
  | .inhomogeneous dl dr => s!"INHOMOGENEOUS [{renderDim dl}] ≐ [{renderDim dr}]"
  | .undetermined why => s!"UNDETERMINED ({why})"

meta def verdictPasses : EdgeVerdict → Bool
  | .identical | .homogeneous _ => true
  | _ => false

meta def runDiagram (carriers : Array Name) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase))
    (assert : Bool) : CommandElabM Unit := do
  if carriers.size < 2 then
    throwError "zil_unify_diagram: need at least two carriers"
  if carriers.toList.eraseDups.length ≠ carriers.size then
    throwError "zil_unify_diagram: duplicate carriers in the diagram"
  let env ← getEnv
  let lookup := lookupOf overrides
  let cmd := if assert then "zil_assert_diagram" else "zil_unify_diagram"
  -- pairwise unification, in input order
  let mut results : Array UnifyResult := #[]
  for i in [0:carriers.size] do
    for j in [i+1:carriers.size] do
      results := results.push (← unifyPair carriers[i]! carriers[j]!)
  let conn := connectingTheorems env carriers
  let edgeThms (a b : Name) : List Name :=
    (conn.getD (a, b) []).reverse
  -- report
  let nEdges := results.size
  let mut out := s!"{cmd}: {carriers.size} objects, {nEdges} edges\n"
  let mut failures : Array String := #[]
  for r in results do
    let v := r.verdict lookup
    let thms := edgeThms r.a r.b
    let constraint :=
      if r.diff.isEmpty && r.opaques.isEmpty then s!"(identical, × {r.ratio})"
      else s!"{renderFactors r.lhs} ≐ {renderFactors r.rhs}" ++
        (if r.ratio == 1 then "" else s!"   (× {r.ratio})")
    out := out ++ s!"  edge {r.a} ⟶ {r.b}:\n"
    out := out ++ s!"    constraint: {constraint} — {renderEdgeVerdict v}\n"
    match thms with
    | [] => out := out ++ "    connecting theorems: NONE\n"
    | ts =>
      let shown := ts.take 4
      let more := if ts.length > 4 then s!" (+{ts.length - 4} more)" else ""
      out := out ++ s!"    connecting theorems: {String.intercalate ", "
        (shown.map (·.toString))}{more}\n"
    unless verdictPasses v do
      failures := failures.push
        s!"edge {r.a} ⟶ {r.b}: {renderEdgeVerdict v}"
    if thms.isEmpty then
      failures := failures.push s!"edge {r.a} ⟶ {r.b}: no connecting theorem"
  -- underived composites: unproven edge with a fully proven flank pair through a third object
  let proven (a b : Name) : Bool :=
    !(edgeThms a b).isEmpty || !(edgeThms b a).isEmpty
  let mut composites : Array String := #[]
  for r in results do
    unless proven r.a r.b do
      for x in carriers do
        if x != r.a && x != r.b && proven r.a x && proven x r.b then
          composites := composites.push
            s!"{r.a} ⟶ {r.b} via {x}: both flanks proven, composite underived"
  out := out ++ "  composition: exact by construction (per-definition normal forms telescope)\n"
  if !composites.isEmpty then
    out := out ++ "  underived composites:\n"
    for c in composites do
      out := out ++ s!"    · {c}\n"
  if assert then
    if failures.isEmpty then
      logInfo (out ++ s!"  ⟹ diagram PROVEN: every edge homogeneous with a connecting theorem")
    else
      throwError "{cmd} FAILED:\n{String.intercalate "\n" failures.toList}\n\n{out}"
  else
    logInfo out

syntax (name := zilUnifyDiagramCmd) "#zil_unify_diagram " ident,+ : command
syntax (name := zilUnifyDiagramWithCmd) "#zil_unify_diagram " ident,+ " with " str : command
syntax (name := zilAssertDiagramCmd) "#zil_assert_diagram " ident,+ : command
syntax (name := zilAssertDiagramWithCmd) "#zil_assert_diagram " ident,+ " with " str : command

elab_rules : command
  | `(#zil_unify_diagram $cs:ident,*) =>
    runDiagram (cs.getElems.map (·.getId)) {} false
  | `(#zil_unify_diagram $cs:ident,* with $o:str) => do
    runDiagram (cs.getElems.map (·.getId)) (← parseOverrides o.getString) false
  | `(#zil_assert_diagram $cs:ident,*) =>
    runDiagram (cs.getElems.map (·.getId)) {} true
  | `(#zil_assert_diagram $cs:ident,* with $o:str) => do
    runDiagram (cs.getElems.map (·.getId)) (← parseOverrides o.getString) true

end Physlib.Meta.ZilUnifyDiagram
