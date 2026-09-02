/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilUnifyMediator

meta import Zil.Datalog.Attach

/-!
# `#zil_link` — find the existing definition your term already is

The linking layer: given a definition, find corpus definitions that are the *same
multiplicative form up to a renaming of variables and a product of interface constants* — the
case the name-bound matchers cannot see (the mediator search reported the `κ`-carrier rate
"missing" when it was exactly `qifEntropicRate` under `a ↦ κ`; four `unruhTemperature`
duplicates sat undetected across arcs for the same reason).

Method, per candidate from the cached ℝ-valued sweep:

1. split each normal form into **variables** and **interface constants**
   (`ℏ, k_B, c, G, π` map to themselves; everything else is a variable);
2. prefilter: the variables' exponent multisets must agree;
3. enumerate substitutions `σ` (variable bijections preserving exponents), filtered by
   **dimensional consistency** from the binder table and `with` overrides — a rename `κ ↦ a`
   survives (both accelerations), `m ↦ E` dies (mass against energy), which is what keeps the
   rest-energy *specialization* `E = mc²` honestly out of scope (it is a composite
   substitution, not a renaming);
4. an exact normal-form check under `σ` decides the match; the interface-constant exponent
   difference is reported as the **conversion**, coefficient ratio and `π` power as the
   **prescription**, and the ready-to-prove weld shape (`unfold both; ring`) is emitted.

`#zil_link_module Mod` surveys every ℝ-valued definition a module declares.
`#zil_island_report [limit n]` is the inverse: Physlib ℝ-valued definitions with **no ZIL
attachment and no reference from any other module** (neither in a theorem statement nor in
another definition's body) — the islands, listed.

Honest limits: multiplicative normal forms only; candidates with opaque residues are skipped
(fail-closed — renaming inside rendered strings is not attempted); the match is decided at the
normal-form level (both sides come from the same normalizer), and the emitted weld is the
kernel-checked form the caller adds; specializations (variable ↦ composite) and additive
bodies are out of scope.  Finding a link certifies a definition of the same shape exists —
whether to consolidate is a judgment the caller makes.

Validation battery (run against the consolidated corpus):
* `hawkingTemperature` finds exactly the true convention family — `qifEntropicRate`
  (`κ ↦ a`, conversion `ℏ/k_B`, exact: the proven cross-arc weld), the canonical SI Unruh
  carrier (`κ ↦ a`, conversion 1: the proven `κ = a` weld), the geometric carrier
  (conversion `ℏ/k_Bc`: the proven `si_unruhTemperature_eq_scaled`), `diamondTemperature`
  (`× −1`: the proven inverted diamond temperature) — plus one **new** unwelded candidate,
  `QFT.PathIntegral.modularHamEigenvalue` (conversion `ℏ²/k_Bc`, prescription `1/(4π²)`).
* `comptonTemperature` finds `comptonFrequency` (the proven `comptonTemperature_eq_clock`
  prescription `ℏ/k_B · 1/(2π)`), `massEnergyEquivalence` (`m ↦ M`), and the one-mass
  `schwarzschildRadius` family (conversion carrying `G` — fault-line flavored) — while
  `deBroglieTemperature` is correctly **absent**: `E = mc²` is a specialization, not a
  renaming, and the dimension filter keeps it out.
* Before the fail-closed dimension rule, one-variable forms matched everything
  (`κ ↦ ωe`, `× 1/360` noise); with it, every reported hit above is a true relation.
* First `#zil_island_report` over the working closure: **738** ℝ-valued definitions
  unattached and unreferenced outside their module.
-/

@[expose] public section

namespace Physlib.Meta.ZilLink

open Lean Elab Command Meta
open Physlib.Meta.ZilDimension
open Physlib.Meta.ZilAnalogyUnify
open Physlib.Meta.ZilUnifyMediator
open Zil.Datalog

meta def interfaceConsts : List String := ["ℏ", "kB", "c", "G", "π"]

/-- Split a normal form's nonzero factors into (variables, interface constants). -/
meta def splitVars (nf : MulNF) : List (String × ℚ) × List (String × ℚ) :=
  let live := nf.factors.toList.filter fun (_, q) => q != 0
  (live.filter (fun (n, _) => !interfaceConsts.contains n),
   live.filter (fun (n, _) => interfaceConsts.contains n))

meta def sortedExponents (l : List (String × ℚ)) : List ℚ :=
  ((l.map (·.2)).toArray.qsort (· < ·)).toList

/-- (Dimension LTMCTIDimensionBase)-compatible rename, fail-closed: an *identity* pair (same name) is always
allowed; a genuine rename requires **both** dimensions known and equal.  An unknown dimension
on either side kills the candidate — without this, every one-variable multiplicative form
links to every other up to interface constants, which is mathematically true and physically
vacuous. -/
meta def dimCompatible (lookup : String → Option (Dimension LTMCTIDimensionBase)) (f g : String) : Bool :=
  f == g ||
    match lookup f, lookup g with
    | some df, some dg => dimEq df dg
    | _, _ => false

/-- All exponent-preserving, dimension-consistent variable bijections, capped. -/
meta partial def bijections (lookup : String → Option (Dimension LTMCTIDimensionBase)) :
    List String → List String → List (List (String × String))
  | [], gs => if gs.isEmpty then [[]] else []
  | f :: fs', gs =>
    gs.foldr (fun g acc =>
      if dimCompatible lookup f g then
        ((bijections lookup fs' (gs.erase g)).map ((f, g) :: ·)) ++ acc
      else acc) []

meta def sigmaCandidates (lookup : String → Option (Dimension LTMCTIDimensionBase))
    (fvars gvars : List (String × ℚ)) : List (List (String × String)) := Id.run do
  -- group by exponent (association list; ℚ is BEq)
  let mut groups : List (ℚ × List String × List String) := []
  for (n, q) in fvars do
    match groups.find? (fun (e, _, _) => e == q) with
    | some _ => groups := groups.map fun (e, fs, gs) =>
        if e == q then (e, n :: fs, gs) else (e, fs, gs)
    | none => groups := (q, [n], []) :: groups
  for (n, q) in gvars do
    match groups.find? (fun (e, _, _) => e == q) with
    | some _ => groups := groups.map fun (e, fs, gs) =>
        if e == q then (e, fs, n :: gs) else (e, fs, gs)
    | none => groups := (q, [], [n]) :: groups
  -- per-group bijections, product across groups
  let mut acc : List (List (String × String)) := [[]]
  for (_, fs, gs) in groups do
    if fs.length != gs.length then
      return []
    let bs := bijections lookup fs gs
    acc := acc.flatMap fun partial_ => bs.map fun b => partial_ ++ b
    if acc.length > 24 then
      acc := acc.take 24
  return acc

meta structure LinkHit where
  candidate : Name
  sigma : List (String × String)
  conversion : List (String × ℚ)
  coeffRatio : ℚ
  piDelta : ℚ

meta def renderSigma (σ : List (String × String)) : String :=
  if σ.isEmpty then "(none — same names)"
  else String.intercalate ", " (σ.map fun (f, g) => s!"{f} ↦ {g}")

meta def renderHit (h : LinkHit) : String := Id.run do
  let conv := if h.conversion.isEmpty then "1"
    else renderFactors h.conversion
  let presc :=
    if h.coeffRatio == 1 && h.piDelta == 0 then "exact"
    else s!"× {h.coeffRatio}" ++ (if h.piDelta == 0 then "" else s!" · π^{renderExp h.piDelta}")
  let mut out := s!"    ↦ {h.candidate}\n"
  out := out ++ s!"      σ: {renderSigma h.sigma}   conversion: {conv}   prescription: {presc}\n"
  out := out ++ s!"      weld shape: <target> = (conversion·prescription) · {h.candidate} ∘ σ, \
    by unfold both; ring\n"
  return out

/-- Try to link `nfF` against candidate `(n, nfG)`.  Requires opaque-free sides. -/
meta def tryLink (lookup : String → Option (Dimension LTMCTIDimensionBase)) (nfF : MulNF) (n : Name) (nfG : MulNF) :
    Option LinkHit := Id.run do
  unless (nfF.opaques.filter fun (_, q) => q != 0).isEmpty do return none
  unless (nfG.opaques.filter fun (_, q) => q != 0).isEmpty do return none
  let (fv, fc) := splitVars nfF
  let (gv, gc) := splitVars nfG
  if sortedExponents fv != sortedExponents gv then return none
  for σ in sigmaCandidates lookup fv gv do
    -- exact check: every f-variable maps to a g-variable of the same exponent
    let ok := fv.all fun (fn, fq) =>
      match σ.find? (fun (a, _) => a == fn) with
      | some (_, gn) => gv.any fun (n', q') => n' == gn && q' == fq
      | none => false
    if ok then
      -- conversion: interface exponents f − g (π separately)
      let mut conv : List (String × ℚ) := []
      let mut piΔ : ℚ := 0
      for cname in interfaceConsts do
        let fq := (fc.find? (fun (a, _) => a == cname)).map (·.2) |>.getD 0
        let gq := (gc.find? (fun (a, _) => a == cname)).map (·.2) |>.getD 0
        if cname == "π" then
          piΔ := fq - gq
        else if fq - gq != 0 then
          conv := conv ++ [(cname, fq - gq)]
      return some { candidate := n, sigma := σ.filter (fun (a, b) => a != b)
                    conversion := conv
                    coeffRatio := nfF.coeff / nfG.coeff
                    piDelta := piΔ }
  return none

meta def linkOne (env : Environment) (defSet : NameSet)
    (lookup : String → Option (Dimension LTMCTIDimensionBase)) (d : Name) :
    CommandElabM (Option (Array LinkHit)) := do
  let some (.defnInfo v) := env.find? d | return none
  let nfF ← liftTermElabM <| nfOfDef defSet v
  let sweep ← realValuedNFs env defSet
  let mut hits : Array LinkHit := #[]
  for (n, nfG) in sweep do
    if n != d then
      if let some h := tryLink lookup nfF n nfG then
        hits := hits.push h
  return some hits

meta def runLinkCmd (d : Name) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) :
    CommandElabM Unit := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  match ← linkOne env defSet lookup d with
  | none => throwError "zil_link: {d} is not a definition"
  | some hits =>
    let mut out := s!"zil link: {d}\n"
    if hits.isEmpty then
      out := out ++ "  no link found (up to renaming and interface constants) — either a \
        genuine original or outside the multiplicative fragment\n"
    else
      for h in hits do
        out := out ++ renderHit h
    logInfo out

meta def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

meta def runLinkModule (mod : Name) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) :
    CommandElabM Unit := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  let mut out := s!"zil link module: {mod}\n"
  let mut linked := 0
  let mut total := 0
  for d in defSet.toList do
    if moduleOf env d == some mod then
      if let some hits ← linkOne env defSet lookup d then
        let isReal ← liftTermElabM do
          let some (.defnInfo v) := env.find? d | return false
          forallTelescope v.type fun _ cod => return cod.isConstOf ``Real
        if isReal then
          total := total + 1
          if !hits.isEmpty then
            linked := linked + 1
            out := out ++ s!"  {d}:\n"
            for h in hits do
              out := out ++ renderHit h
  out := out ++ s!"  ⟹ {linked} of {total} ℝ-valued definitions have links; \
    {total - linked} unlinked in this module\n"
  logInfo out

/-- Physlib ℝ-valued definitions with no ZIL attachment and no reference from any other
module — neither in a theorem statement nor in another definition's body. -/
meta def runIslandReport (lim : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  -- referenced-from-other-module set: one pass over Physlib constants
  let mut referenced : NameSet := {}
  for (n, ci) in env.constants.toList do
    let inPhyslib := (moduleOf env n).any fun m => m.toString.startsWith "Physlib"
    if inPhyslib then
      let exprs : List Expr := match ci with
        | .thmInfo v => [v.type]
        | .axiomInfo v => [v.type]
        | .defnInfo v => [v.type, v.value]
        | _ => []
      let home := moduleOf env n
      for e in exprs do
        referenced := e.foldConsts referenced fun c acc =>
          if defSet.contains c && moduleOf env c != home then acc.insert c else acc
  let attached : NameSet :=
    (declarationAttachments env).foldl (fun s a => s.insert a.declaration) {}
  let mut out := s!"zil island report (ℝ-valued Physlib definitions, unattached and \
    unreferenced outside their module):\n"
  let mut count := 0
  let mut shown := 0
  for d in defSet.toList do
    if !referenced.contains d && !attached.contains d then
      let isReal ← liftTermElabM do
        let some (.defnInfo v) := env.find? d | return false
        forallTelescope v.type fun _ cod => return cod.isConstOf ``Real
      if isReal then
        count := count + 1
        if shown < lim then
          shown := shown + 1
          out := out ++ s!"  · {d}   [{(moduleOf env d).getD Name.anonymous}]\n"
  out := out ++ s!"  ⟹ {count} islands ({shown} shown)\n"
  logInfo out

syntax (name := zilLinkCmd) "#zil_link " ident : command
syntax (name := zilLinkWithCmd) "#zil_link " ident " with " str : command
syntax (name := zilLinkModuleCmd) "#zil_link_module " ident : command
syntax (name := zilLinkModuleWithCmd) "#zil_link_module " ident " with " str : command
syntax (name := zilIslandReportCmd) "#zil_island_report" : command
syntax (name := zilIslandReportLimCmd) "#zil_island_report " " limit " num : command

elab_rules : command
  | `(#zil_link $d:ident) => runLinkCmd d.getId {}
  | `(#zil_link $d:ident with $o:str) => do
    runLinkCmd d.getId (← parseOverrides o.getString)
  | `(#zil_link_module $m:ident) => runLinkModule m.getId {}
  | `(#zil_link_module $m:ident with $o:str) => do
    runLinkModule m.getId (← parseOverrides o.getString)
  | `(#zil_island_report) => runIslandReport 25
  | `(#zil_island_report limit $n:num) => runIslandReport n.getNat

end Physlib.Meta.ZilLink
