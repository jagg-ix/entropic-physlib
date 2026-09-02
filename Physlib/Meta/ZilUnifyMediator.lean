/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilUnifyDiagram

/-!
# `#zil_unify_mediator` — the missing object between two carriers

The diagram audit hunts missing *edges*; this command hunts missing *objects*.  Both §10 gaps
had the same shape: two carriers whose unification is **inhomogeneous by exactly a product of
interface constants** — `comptonFrequency ≐ unruhTemperature` off by exactly `k_B/ℏ`, the
energy-convention `gibbonsHawkingTemperature ≐ unruhTemperature` off by exactly `k_B` — and the
fix was in both cases a *mediating definition* (`comptonTemperature`,
`gibbonsHawkingTemperatureSI`) converting the one carrier into the other's sector.  This
command mechanizes that discovery:

1. compute the dimensions of both definitions' bodies and their **defect** `dim A / dim B`;
2. solve the defect *exactly* over the interface basis `{ℏ, k_B, c, G}` (Gaussian elimination
   in the dimension group `ℚ⁶`; dimensions of the basis come from the same binder table and
   `with` overrides as every other command, so the typing flows through);
3. if the defect is a product of interface constants, form the **candidate mediator**
   `M = A · ℏ^{-x} k_B^{-y} c^{-z} G^{-w}` — same normal form as `A`, conversion factors
   applied, dimension equal to `B`'s;
4. sweep the ℝ-valued Physlib definitions for one whose normal form matches the candidate's
   factor map (`π` exponent and numeric coefficient free — they are reported as the
   *prescription*, e.g. the ubiquitous `1/(2π)`), and report matches, or **MISSING MEDIATOR**
   with the form a new definition would need.

`#zil_assert_mediator A B finds M` is the build-enforced form: it fails unless the search for
the pair finds exactly the named mediator.  Fail-closed: undetermined dimensions, a defect
outside the interface span, or a missing/renamed mediator all fail the assert.

Honest limits: multiplicative normal forms only, so additive composites never match; the
candidate keeps `A`'s opaque residues verbatim; matching is by binder-name factor map, so a
mediator built from renamed-but-equal parameters is invisible; the corpus is the ℝ-valued
Physlib definitions (curried `ℝ` codomain), nothing else; and a *found* mediator certifies a
definition of the right multiplicative shape exists — the welds through it still have to be
proven (`#zil_unify_diagram` then audits those edges).

Validation (the two §10 gaps as positive controls, run against the closed corpus):
`comptonFrequency ≐ unruhTemperature` → defect `[T⁻¹Θ⁻¹I⁻¹]` = `k_B/ℏ`, candidate
`m·c²·k_B⁻¹`, found `comptonTemperature` with prescription `× 1/(2π)`;
`gibbonsHawkingTemperature ≐ unruhTemperature` → defect = `k_B`, candidate `ℏ·H·k_B⁻¹`, found
`gibbonsHawkingTemperatureSI` **exact**.  Negative control: a homogeneous pair refuses the
search.  Both positives are held as build facts in the WEP depth gate §14 — delete or rename a
mediator and the gate fails.

First hunt (temperature/rate/energy sectors, gate §15 holds the closures):
* `unruhTemperature` → rate sector: **found `CausalDiamond.QIFEquilibrium.qifEntropicRate`
  exact** — a cross-arc hit; welded as `unruhTemperature_eq_qifEntropicRate_scaled`
  (`T_U = (ℏ/k_B)·λ`), with the `κ`-face recorded as an instantiation (the search reported the
  `κ`-carrier image "missing", but it is `qifEntropicRate` under the renaming `a ↦ κ` — the
  binder-name limit in action, resolved by a theorem, not a duplicate definition; the
  `GM/R²`-carrier report is the same renaming).
* `deBroglieFrequency` → temperature sector: **missing**, closed by defining
  `deBroglieTemperature = E/(2πk_B)` with the weld `unruh_eq_deBroglieTemperature_iff`
  (`a = Ec/ℏ`) and `deBroglie_eq_comptonTemperature_iff` (`E = mc²` — the §9 rest-energy
  residue as a temperature-sector theorem).
* Tool limits the hunt surfaced: `Constants.kB`-style framework constants are *defs*, opaque
  to the binder table, so Landauer-sector carriers come back undetermined (teaching `dimOf`
  the framework constants is the fix); binder `T` reads `Θ`, not the framework's `Θ·I`, so
  temperature-*binder* carriers show a spurious `I`-defect against temperature-*valued*
  carriers.  Also surfaced, and since consolidated: of the four `unruhTemperature` definitions the hunt
  found across arcs, two survive — the SI carrier (`Physlib.Thermodynamics.unruhTemperature`,
  canonical) and the geometric-convention carrier
  (`Lorentz.JacobsonUnruhRindlerClock.unruhTemperature = κ/2π`, related by the recorded
  conversion `si_unruhTemperature_eq_scaled`).  The `CausalDiamond.EquivalencePrinciple` alias
  (`:= hawkingTemperature`) and the `GaussCodazzi.ScreenThermodynamics` duplicate of the
  geometric form were deleted, their use sites rewired onto the canonical carrier through the
  `unruhTemperature_eq_hawkingTemperature` weld.
-/

@[expose] public section

namespace Physlib.Meta.ZilUnifyMediator

open Lean Elab Command Meta
open Dimension.LTMCTI
open Physlib.Meta.ZilDimension
open Physlib.Meta.ZilAnalogyUnify

meta def dimVec (d : (Dimension LTMCTIDimensionBase)) : Array ℚ :=
  #[(d.exponent .length), (d.exponent .time), (d.exponent .mass), (d.exponent .charge), (d.exponent .temperature), (d.exponent .information)]

/-- Exact solve of `target = Π basisᵢ ^ eᵢ` in the dimension group, by Gaussian elimination
over `ℚ`.  `none` if the target is outside the basis span or the basis is dependent under the
given typing (no unique solution). -/
meta def solveConversion (basis : Array (String × (Dimension LTMCTIDimensionBase))) (target : (Dimension LTMCTIDimensionBase)) :
    Option (Array (String × ℚ)) := Id.run do
  let k := basis.size
  let names := basis.map (·.1)
  let tv := dimVec target
  let mut rows : Array (Array ℚ × ℚ) := #[]
  for i in [0:6] do
    rows := rows.push (basis.map (fun p => (dimVec p.2)[i]!), tv[i]!)
  let mut pivotRow := 0
  let mut pivots : Array (Nat × Nat) := #[]
  for col in [0:k] do
    let mut found := false
    for rIdx in [pivotRow:rows.size] do
      if !found && rows[rIdx]!.1[col]! != 0 then
        let tmp := rows[pivotRow]!
        rows := rows.set! pivotRow rows[rIdx]!
        rows := rows.set! rIdx tmp
        found := true
    if found then
      let (pr, prb) := rows[pivotRow]!
      let p := pr[col]!
      let prN := pr.map (· / p)
      let prbN := prb / p
      rows := rows.set! pivotRow (prN, prbN)
      for rIdx in [0:rows.size] do
        if rIdx != pivotRow then
          let (rr, rb) := rows[rIdx]!
          let f := rr[col]!
          if f != 0 then
            rows := rows.set! rIdx (rr.mapIdx (fun i a => a - f * prN[i]!), rb - f * prbN)
      pivots := pivots.push (pivotRow, col)
      pivotRow := pivotRow + 1
  for rIdx in [pivotRow:rows.size] do
    if rows[rIdx]!.2 != 0 then return none
  if pivots.size != k then return none
  let mut out : Array (String × ℚ) := #[]
  for (r, c) in pivots do
    if rows[r]!.2 != 0 then
      out := out.push (names[c]!, rows[r]!.2)
  return some out

/-- Session cache of the ℝ-valued Physlib definitions' normal forms, keyed by the imported
module count (same pattern as `physlibDefSetCache`). -/
meta initialize mediatorNFCache : IO.Ref (Option (Nat × Array (Name × MulNF))) ← IO.mkRef none

meta def realValuedNFs (env : Environment) (defSet : NameSet) :
    CommandElabM (Array (Name × MulNF)) := do
  let key := env.header.moduleNames.size
  if let some (k, arr) ← mediatorNFCache.get then
    if k == key then return arr
  let arr ← liftTermElabM do
    let mut out : Array (Name × MulNF) := #[]
    for n in defSet.toList do
      if let some (.defnInfo v) := env.find? n then
        try
          let isReal ← forallTelescope v.type fun _ cod => return cod.isConstOf ``Real
          if isReal then
            out := out.push (n, ← nfOfDef defSet v)
        catch _ => pure ()
    return out
  mediatorNFCache.set (some (key, arr))
  return arr

meta def sansPi (fs : Std.HashMap String ℚ) : List (String × ℚ) :=
  ((fs.toList.filter fun (n, q) => n != "π" && q != 0).toArray.qsort
    (fun x y => x.1 < y.1)).toList

meta def sortedOpaques (l : List (String × ℚ)) : List (String × ℚ) :=
  ((l.filter fun (_, q) => q != 0).toArray.qsort (fun x y => x.1 < y.1)).toList

meta structure MediatorMatch where
  name : Name
  coeffRatio : ℚ
  piDelta : ℚ

meta def renderPrescription (m : MediatorMatch) : String :=
  if m.coeffRatio == 1 && m.piDelta == 0 then "(exact)"
  else
    let pi := if m.piDelta == 0 then "" else s!" · π^{renderExp m.piDelta}"
    s!"(× {m.coeffRatio}{pi})"

meta def runMediator (a b : Name) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase))
    (expect : Option Name) : CommandElabM Unit := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  let cmd := if expect.isSome then "zil_assert_mediator" else "zil_unify_mediator"
  let getV (n : Name) : CommandElabM DefinitionVal := do
    match env.find? n with
    | some (.defnInfo v) => return v
    | _ => throwError "{cmd}: {n} is not a definition"
  let va ← getV a
  let vb ← getV b
  let dimOfDef (v : DefinitionVal) : CommandElabM DimR :=
    liftTermElabM <| lambdaTelescope v.value fun _ body => dimOf lookup defSet 8 body
  let da ← dimOfDef va
  let db ← dimOfDef vb
  let fail (msg : String) : CommandElabM Unit := do
    if expect.isSome then throwError "{cmd} FAILED: {msg}"
    else logInfo s!"{cmd}: {a} ≐ {b}\n  {msg}"
  match da, db with
  | .known dA, .known dB =>
    if dimEq dA dB then
      fail s!"already homogeneous ([{renderDim dA}]) — no conversion needed; \
        use #zil_analogy_unify for duplicate detection"
    else
      let defect := dA * dB⁻¹
      let basis : Array (String × (Dimension LTMCTIDimensionBase)) :=
        #["ℏ", "kB", "c", "G"].filterMap fun n => (lookup n).map (n, ·)
      match solveConversion basis defect with
      | none =>
        fail s!"defect [{renderDim defect}] is not a product of interface constants \
          {basis.toList.map (·.1)} under this typing"
      | some conv =>
        let nfa ← liftTermElabM <| nfOfDef defSet va
        let mut candidate := nfa.factors
        for (n, e) in conv do
          candidate := candidate.insert n (candidate.getD n 0 - e)
        let candKey := sansPi candidate
        let candOpq := sortedOpaques nfa.opaques
        let sweep ← realValuedNFs env defSet
        let mut found : Array MediatorMatch := #[]
        for (n, nf) in sweep do
          if n != a && n != b then
            if sansPi nf.factors == candKey && sortedOpaques nf.opaques == candOpq then
              found := found.push
                { name := n
                  coeffRatio := nf.coeff / nfa.coeff
                  piDelta := nf.factors.getD "π" 0 - candidate.getD "π" 0 }
        let convStr := renderFactors (conv.toList.filter fun (_, q) => q != 0)
        let mut out := s!"{cmd}: {a} ≐ {b}\n"
        out := out ++ s!"  dim A: [{renderDim dA}]   dim B: [{renderDim dB}]   \
          defect A/B: [{renderDim defect}]\n"
        out := out ++ s!"  conversion: defect = {convStr}  (A over the conversion has \
          the dimension of B)\n"
        out := out ++ s!"  candidate mediator: {renderFactors candKey}  \
          (π and coefficient free)\n"
        if found.isEmpty then
          out := out ++ "  ⟹ MISSING MEDIATOR — no ℝ-valued Physlib definition has this \
            normal form; defining it closes the pair (the §10 pattern)\n"
        else
          for m in found do
            out := out ++ s!"  found in corpus: {m.name}  {renderPrescription m}\n"
        match expect with
        | none => logInfo out
        | some want =>
          if found.any (·.name == want) then
            logInfo (out ++ s!"  ⟹ mediator held: {want}")
          else
            throwError "{cmd} FAILED: expected mediator {want} not found\n\n{out}"
  | _, _ =>
    fail "dimension of a body not determined (unknown binders — add `with` overrides)"

syntax (name := zilUnifyMediatorCmd) "#zil_unify_mediator " ident ident : command
syntax (name := zilUnifyMediatorWithCmd) "#zil_unify_mediator " ident ident " with " str : command
syntax (name := zilAssertMediatorCmd) "#zil_assert_mediator " ident ident " finds " ident : command
syntax (name := zilAssertMediatorWithCmd)
  "#zil_assert_mediator " ident ident " finds " ident " with " str : command

elab_rules : command
  | `(#zil_unify_mediator $a:ident $b:ident) =>
    runMediator a.getId b.getId {} none
  | `(#zil_unify_mediator $a:ident $b:ident with $o:str) => do
    runMediator a.getId b.getId (← parseOverrides o.getString) none
  | `(#zil_assert_mediator $a:ident $b:ident finds $m:ident) =>
    runMediator a.getId b.getId {} (some m.getId)
  | `(#zil_assert_mediator $a:ident $b:ident finds $m:ident with $o:str) => do
    runMediator a.getId b.getId (← parseOverrides o.getString) (some m.getId)

end Physlib.Meta.ZilUnifyMediator
