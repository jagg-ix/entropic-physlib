/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilDimension

/-!
# `#zil_analogy_unify` — the bridge constraint between two same-shaped definitions

Einstein's equivalence-principle move, mechanized at the step that matters: two definitions from
different sectors are matched factor-by-factor, and what does **not** cancel is emitted as the
**bridge constraint** — the parameter identification under which the two quantities are literally
equal.  For `unruhTemperature` against `verlindeGravityTemperature` the constraint is
`a ≐ G·M·R⁻²`: the residue of the match *is* the equivalence principle.  The command finds the
constraint; whether it deserves promotion to a principle is decided by the kill tests
(dimensional homogeneity, printed inline; typing invariance via `#zil_dimension_*` overrides) and
by proving the corresponding `iff` theorem.

Method: both bodies are delta-unfolded (bounded), then reduced to a **multiplicative normal
form** — a numeric coefficient, named factors with rational exponents (binder names; `π`), and
opaque residues (sums, transcendentals, anything non-multiplicative) rendered verbatim.  Factors
matching by *binder name* cancel (both `ℏ` mean Planck's constant — physics notation is the
shared vocabulary), the coefficient ratio is reported separately (per C7 it carries no evidential
weight but must be visible), and the residual products on the two sides form the constraint.
Both sides of the constraint are dimension-checked with the same table/overrides as
`#zil_dimension_*`.

Reading the output: an **empty constraint** means the definitions are identical up to
coefficient — the duplicate/prescription-gap case, with the exact ratio printed.  A
**homogeneous constraint** is an equivalence-principle candidate: prove the `iff`, test typing
invariance, then gate it.  An **inhomogeneous constraint** usually means the two definitions use
different unit conventions (a `kB = c = 1` body against an SI body) — re-run with overrides
modelling the convention before concluding anything.

Honest limits: multiplicative structure only — additive composites travel as opaque residues and
never cancel; matching is by binder name, so `m` vs `M` stay distinct and renamed-but-equal
parameters do not cancel; opaque residues make the dimensional verdict undetermined.  The
constraint is a **candidate**, not a theorem — the `iff` still has to be proven.

First battery (the CAT/EPT test), with three results cross-validated against theorems already in
the repository:

* `unruhTemperature` ≐ `verlindeGravityTemperature` → `R²·a ≐ G·M`, homogeneous — re-derives the
  proven `unruh_eq_gravityTemperature_iff` (the equivalence principle, entropic form);
* `unruhTemperature` ≐ `hawkingTemperature` → `a ≐ κ`, homogeneous, coefficient 1 — re-derives the
  proven weld `unruhTemperature_eq_hawkingTemperature`; with the third pairing
  `G·M ≐ R²·κ` the temperature sector closes as a *consistent constraint triangle*;
* `schwarzschildRadius` ≐ `comptonWavelength` → `G·m·M ≐ ħ·c` (×2), homogeneous under SI `G` and
  exactly `I⁻¹` off under holographic `G` — the entropic `G`-derivation keystone
  (`entropicNewtonConstant_converges`) is dimensionally sound and is a one-nat conversion, the
  same signature as the WEP identity;
* `erEprOneBitMass` ≐ `entropicOneBitMass` → identical in every named factor, residue `√(2π)` —
  re-derives the proven `oneBitMass_ratio_eq_sqrt_two_pi` prescription gap;
* `unruhTemperature` ≐ `gibbonsHawkingTemperature` → INHOMOGENEOUS (`a ≐ H·kB·c`): honest
  convention finding — the FLRW definition is in the energy convention (`kB = c = 1` absorbed),
  so the de Sitter pairing `a ≐ c·H` cannot be recorded until that definition carries its
  constants.  A repository improvement surfaced by the kill test, not a tool failure.
  **Closed**: `gibbonsHawkingTemperatureSI` restores the constants; the re-run emits `a ≐ H·c`,
  homogeneous, coefficient 1, and the weld is proven (`unruh_eq_gibbonsHawkingSI_iff`).

Clock battery (binder spellings canonicalized: `ħ`/`hbar` ↦ `ℏ`, `k_B` ↦ `kB`, so factors cancel
across modules that chose different glyphs):

* `deBroglieFrequency` ≐ `comptonFrequency` → **`E ≐ m·c²`**, homogeneous — the rest-energy
  identification itself is the residue of the match (cross-validating
  `deBroglie_eq_gamma_compton`: the de Broglie clock is the boosted Compton clock);
* `zitterbewegungFrequency` ≐ `comptonFrequency` → coefficient 2 with the mass-shell residue
  `√(p²c² + m²c⁴)` opaque — at rest it collapses to the proven doubling
  (`zitterbewegung_rest_eq_two_compton`); the mass shell is genuinely non-multiplicative;
* `comptonFrequency` ≐ `unruhTemperature` → INHOMOGENEOUS by exactly the `k_B` interface: no
  Compton-temperature definition (`m·c²/(2π·k_B)`) exists to mediate frequency ↔ temperature —
  recorded as a gap, not padded over.  The clock sector itself is information-neutral under both
  `G`-typings (`EntropicWepDepthGate` §9): the nat enters only at the `G`-construction.
  **Closed**: `comptonTemperature` is that mediator (`comptonTemperature_eq_clock`); the re-run
  `unruhTemperature ≐ comptonTemperature` emits `a·ℏ ≐ m·c³`, homogeneous, coefficient 1, and the
  weld is proven (`unruh_eq_comptonTemperature_iff`).

Triangle closure (found by the tool on the closed carriers): the remaining pairing
`comptonTemperature` ≐ `gibbonsHawkingTemperatureSI` emits `m·c² ≐ ℏ·H`, homogeneous,
coefficient 1 — exactly the composition of the two welds through the shared Unruh carrier, so
the three constraints are a *consistent* triangle, not independent claims; proven as
`comptonTemperature_eq_gibbonsHawkingSI_iff` (the constraint mass `m = ℏH/c²` is de Sitter's
own mass scale, Wesson's minimum mass quantum).
-/

@[expose] public section

namespace Physlib.Meta.ZilAnalogyUnify

open Lean Elab Command Meta
open Dimension.LTMCTI
open Physlib.Meta.ZilDimension
open Physlib.Meta.ZilAnalogy

/-- Multiplicative normal form: coefficient × Π nameᵢ^qᵢ × Π opaqueⱼ^qⱼ. -/
meta structure MulNF where
  coeff : ℚ := 1
  factors : Std.HashMap String ℚ := {}
  opaques : List (String × ℚ) := []

meta def ratZPow (q : ℚ) (n : ℤ) : ℚ :=
  if n ≥ 0 then q ^ n.toNat else (q ^ (-n).toNat)⁻¹

/-- Physically identical binder spellings collapse to one name, so factors cancel across
modules that chose different glyphs. -/
meta def canonName (n : String) : String :=
  if n == "ħ" || n == "hbar" then "ℏ" else if n == "k_B" then "kB" else n

meta def MulNF.addFactor (nf : MulNF) (name : String) (ex : ℚ) : MulNF :=
  let name := canonName name
  { nf with factors := nf.factors.insert name (nf.factors.getD name 0 + ex) }

/-- Reduce an expression to multiplicative normal form, at exponent `ex`. -/
meta partial def mulNF (e : Expr) (ex : ℚ) (acc : MulNF) : MetaM MulNF := do
  match e with
  | .fvar id =>
    return acc.addFactor (← id.getDecl).userName.toString ex
  | .mdata _ b => mulNF b ex acc
  | .letE _ _ v b _ => mulNF (b.instantiate1 v) ex acc
  | _ =>
    match numLit? e with
    | some q =>
      if ex.den == 1 then return { acc with coeff := acc.coeff * ratZPow q ex.num }
      else return { acc with opaques := (s!"{q}", ex) :: acc.opaques }
    | none =>
      let args := e.getAppArgs
      match e.getAppFn with
      | .const n _ =>
        if (n == ``HMul.hMul || n == ``HSMul.hSMul) && args.size ≥ 2 then
          let acc ← mulNF args[args.size - 2]! ex acc
          mulNF args[args.size - 1]! ex acc
        else if n == ``HDiv.hDiv && args.size ≥ 2 then
          let acc ← mulNF args[args.size - 2]! ex acc
          mulNF args[args.size - 1]! (-ex) acc
        else if n == ``Inv.inv && args.size ≥ 1 then
          mulNF args[args.size - 1]! (-ex) acc
        else if n == ``HPow.hPow && args.size ≥ 2 then
          match numLit? args[args.size - 1]! with
          | some k => mulNF args[args.size - 2]! (ex * k) acc
          | none => return { acc with opaques := (toString (← Meta.ppExpr e), ex) :: acc.opaques }
        else if n == ``Real.sqrt && args.size ≥ 1 then
          mulNF args[args.size - 1]! (ex / 2) acc
        else if n == ``Neg.neg && args.size ≥ 1 then
          let acc :=
            if ex.den == 1 then { acc with coeff := acc.coeff * ratZPow (-1) ex.num } else acc
          mulNF args[args.size - 1]! ex acc
        else if n == ``Real.pi then
          return acc.addFactor "π" ex
        else if n == ``Constants.kB then
          -- the framework constant contributes the canonical `kB` factor, so the
          -- link/mediator sweeps see it as interface vocabulary, not an opaque
          return acc.addFactor "kB" ex
        else if transparentCasts.contains n && args.size ≥ 1 then
          mulNF args[args.size - 1]! ex acc
        else
          return { acc with opaques := (toString (← Meta.ppExpr e), ex) :: acc.opaques }
      | _ => return { acc with opaques := (toString (← Meta.ppExpr e), ex) :: acc.opaques }

meta def renderFactors (fs : List (String × ℚ)) : String :=
  let piece (n : String) (q : ℚ) : String :=
    if q == 1 then n else s!"{n}^{renderExp q}"
  match fs with
  | [] => "1"
  | l => String.intercalate " · " (l.map fun (n, q) => piece n q)

/-- (Dimension LTMCTIDimensionBase) of a factor product, if every name resolves. -/
meta def dimOfFactors (lookup : String → Option (Dimension LTMCTIDimensionBase)) (fs : List (String × ℚ)) :
    Option (Dimension LTMCTIDimensionBase) :=
  fs.foldl (fun acc (n, q) => do
    let d ← acc
    let dn ← if n == "π" then some (1 : (Dimension LTMCTIDimensionBase)) else lookup n
    pure (d * dn ^ q)) (some 1)

meta def nfOfDef (defSet : NameSet) (v : DefinitionVal) : MetaM MulNF :=
  lambdaTelescope v.value fun _ body => do
    let body ← unfoldBounded defSet.contains 64 body
    mulNF body 1 {}

/-- Structured result of one pairwise unification — the morphism `a ⟶ b` of the constraint
diagram.  `diff` is `nf a − nf b` in the free abelian group on canonical binder names (nonzero
entries only); `opaques` the signed non-multiplicative residues; `ratio` the coefficient ratio
`A/B`.  Normal forms are computed once per definition, so differences telescope:
`(nf a − nf b) + (nf b − nf c) = nf a − nf c` — composition of these morphisms is exact by
construction, which is why a diagram audit (`#zil_unify_diagram`) checks homogeneity and proof
coverage, not commutativity. -/
meta structure UnifyResult where
  a : Name
  b : Name
  matched : List String
  diff : List (String × ℚ)
  opaques : List (String × ℚ)
  ratio : ℚ

/-- Positive part of the difference: the left side of the bridge constraint. -/
meta def UnifyResult.lhs (r : UnifyResult) : List (String × ℚ) :=
  r.diff.filter fun (_, q) => q > 0

/-- Negated negative part of the difference: the right side of the bridge constraint. -/
meta def UnifyResult.rhs (r : UnifyResult) : List (String × ℚ) :=
  (r.diff.filter fun (_, q) => q < 0).map fun (n, q) => (n, -q)

/-- The dimensional verdict on one edge, under a given typing. -/
meta inductive EdgeVerdict where
  | identical
  | homogeneous (d : (Dimension LTMCTIDimensionBase))
  | inhomogeneous (dl dr : (Dimension LTMCTIDimensionBase))
  | undetermined (why : String)

meta def UnifyResult.verdict (lookup : String → Option (Dimension LTMCTIDimensionBase)) (r : UnifyResult) :
    EdgeVerdict :=
  if r.diff.isEmpty && r.opaques.isEmpty then .identical
  else match dimOfFactors lookup r.lhs, dimOfFactors lookup r.rhs with
  | some dl, some dr =>
    if !r.opaques.isEmpty then .undetermined "opaque residues present"
    else if dimEq dl dr then .homogeneous dl
    else .inhomogeneous dl dr
  | _, _ => .undetermined "unknown binder — add `with` overrides"

/-- Compute the unification of two definitions, without rendering. -/
meta def unifyPair (a b : Name) : CommandElabM UnifyResult := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  let getDef (n : Name) : CommandElabM DefinitionVal := do
    match env.find? n with
    | some (.defnInfo v) => return v
    | _ => throwError "zil_analogy_unify: {n} is not a definition"
  let va ← getDef a
  let vb ← getDef b
  let (nfa, nfb) ← liftTermElabM do
    return (← nfOfDef defSet va, ← nfOfDef defSet vb)
  -- difference A − B over the union of named factors
  let mut diff : Std.HashMap String ℚ := nfa.factors
  for (n, q) in nfb.factors.toList do
    diff := diff.insert n (diff.getD n 0 - q)
  -- opaque residues: cancel identical renderings
  let mut opq : Std.HashMap String ℚ := {}
  for (s, q) in nfa.opaques do
    opq := opq.insert s (opq.getD s 0 + q)
  for (s, q) in nfb.opaques do
    opq := opq.insert s (opq.getD s 0 - q)
  let matched := (nfa.factors.toList.filterMap fun (n, _) =>
    if nfb.factors.contains n then some n else none)
  return { a, b, matched
           diff := diff.toList.filter fun (_, q) => q ≠ 0
           opaques := opq.toList.filter fun (_, q) => q ≠ 0
           ratio := nfa.coeff / nfb.coeff }

meta def renderUnify (lookup : String → Option (Dimension LTMCTIDimensionBase)) (r : UnifyResult) : String := Id.run do
  let lhs := r.lhs
  let rhs := r.rhs
  let mut out := s!"zil analogy unify: {r.a} ≐ {r.b}\n"
  out := out ++ s!"  matched factors: {String.intercalate ", " r.matched}\n"
  out := out ++ s!"  coefficient ratio (A/B): {r.ratio}\n"
  if !r.opaques.isEmpty then
    out := out ++ "  unmatched non-multiplicative residues:\n"
    for (s, q) in r.opaques do
      out := out ++ s!"    · ({s})^{renderExp q}\n"
  if lhs.isEmpty && rhs.isEmpty && r.opaques.isEmpty then
    out := out ++ s!"  ⟹ IDENTICAL up to coefficient {r.ratio} — duplicate or prescription gap\n"
  else
    out := out ++ s!"  bridge constraint: {renderFactors lhs} ≐ {renderFactors rhs}"
    out := out ++ (if r.ratio == 1 then "\n" else s!"   (× {r.ratio})\n")
    match dimOfFactors lookup lhs, dimOfFactors lookup rhs with
    | some dl, some dr =>
      if r.opaques.isEmpty then
        let verdict := if dimEq dl dr then "HOMOGENEOUS — equivalence-principle candidate"
          else "INHOMOGENEOUS — unit-convention mismatch or false pairing"
        out := out ++ s!"  dimension: [{renderDim dl}] ≐ [{renderDim dr}] — {verdict}\n"
      else
        out := out ++ "  dimension: undetermined (opaque residues present)\n"
    | _, _ =>
      out := out ++ "  dimension: undetermined (unknown binder — add `with` overrides)\n"
  return out

meta def runUnify (a b : Name) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) :
    CommandElabM Unit := do
  let r ← unifyPair a b
  logInfo (renderUnify (lookupOf overrides) r)

syntax (name := zilUnifyCmd) "#zil_analogy_unify " ident ident : command
syntax (name := zilUnifyWithCmd) "#zil_analogy_unify " ident ident " with " str : command

elab_rules : command
  | `(#zil_analogy_unify $a:ident $b:ident) => runUnify a.getId b.getId {}
  | `(#zil_analogy_unify $a:ident $b:ident with $o:str) => do
    runUnify a.getId b.getId (← parseOverrides o.getString)

end Physlib.Meta.ZilAnalogyUnify
