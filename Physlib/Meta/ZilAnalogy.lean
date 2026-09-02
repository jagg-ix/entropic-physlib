/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilAssert

meta import Zil.Datalog.Attach

/-!
# `#zil_analogy` — same equation form, different physics

Ideas travel between domains when equations share a *form*: the harmonic oscillator, exponential
relaxation, inverse-square laws, the `κ/2π` temperatures, the `M² = ħc·k/G` mass conditions.  This
session met several by hand — `Δτ_ent = τ₁ − τ₂` re-appearing as the differential channel and the
log-likelihood increment; `unruhTemperature` and `hawkingTemperature` as one formula; the one-bit
mass family.  Each was noticed late, by luck.

This command finds them mechanically, in two passes:

1. **Theorem pass** — for every declaration carrying a ZIL attachment, the conclusion's structural
   fingerprint, both as stated and with every Physlib definition **unfolded in place** (`(unf …)`
   classes; bounded delta-expansion with beta and zeta cleanup).  The fingerprint is re-gated
   after unfolding, so a definitional predicate abbreviating an equation joins the equation's
   family, and two modules that packaged one identity behind different defined symbols meet.
2. **Definition pass** — for every definition compiled from a `Physlib.*` module, the fingerprint
   of its *body* (reported as `(def …)` classes).  This is where families hidden behind defined
   symbols live: `ħa/(2πc·k_B)` and `ħc³/(8πGM·k_B)` are different theorems but the *same shape of
   definition*.

The fingerprint keeps the logical structure (`=`, `↔`, `≤`, `<`, `≠`, `∧`, `∨`, `¬`, `∃`),
arithmetic (`+ − × / ^`, `⁻¹`, negation), and transcendental structure (`exp log sqrt sin cos
sinh cosh tanh`, `π`, `I`, `normSq`); it erases every numeric literal to `#` (so `2` vs `4π` do
**not** split a family — same form at different coefficient *is* the analogy class, per C7) and
every domain-specific constant to `C` (casts are transparent; `let`-bindings are inlined).
Variables are erased to `x` — except that a variable occurring **more than once** in the rendered
statement is erased to `z`, so `a/a` and `a/b` do not merge: repetition is the one bit of variable
identity that changes what an equation says.  A conclusion qualifies whenever a relation appears
anywhere inside it, so `∃`-shaped and conjunctive statements are in scope.  Three
canonicalizations make the match modulo algebra rather than spelling:

* `+` and `·` are flattened and their operands sorted (associativity/commutativity blind);
* repeated `x`/`z`/`#` factors are absorbed, and `x^n` counts as `x` — so `ħ·a` and `ħ·c³` are one
  numerator shape, which is exactly what merges the `κ/2π` temperature family;
* `=`, `↔`, `≠`, `∧`, `∨` are orientation-blind (operand skeletons sorted).

Every declaration is keyed up to four ways: **exact**, **unfolded** (`(unf …)`), and
**coefficient-blind** versions of both (`≈`-prefixed, numeric factors dropped from products — what
lets `√(ħc·ln2/2G)` and a capillary length `√(σ/ρg)` meet).  A processed class that groups exactly
the declaration set of a less-processed one is suppressed.  Classes spanning **different
namespaces** are ranked by structural specificity × cross-area spread, damped by class size (a
100-member class is a category, not a family): a family confined to one module is boilerplate, a
contentless form (`C = C·C`) scores zero however widely it spreads, and one carrying `π`, `exp`,
or a division across a handful of areas is a candidate law.

Honest limits (v4): unfolding is delta+beta+zeta (64-step budget per conclusion; no iota, so a
`match` on a symbolic argument still stops at `C`); variable identity is tracked only as
unique-vs-repeated, so permutation patterns finer than repetition can over-merge, and inside an
`∃`-binder the bound variable renders `x` without repetition tracking; higher-order conclusions
(quantification over functions) are out of scope.  On the first v4 run no cross-area `∃`-shaped
class appeared — the machinery is exercised (`∀c, 0<c → ∃t, t·t = c+c` fingerprints as
`(Ex (Eq x z))`) but the graph's existential conclusions carry no matching rendered arithmetic
yet.  A hit is a **candidate**, to be verified by reading the statements — the command finds
rhymes, not theorems.

First full-graph run (v1) rediscovered the `‖weight‖ = e^(−entropic time)` family (8 declarations,
EntropyProductionDecay / TotalCorrelationEntropicClock / IKKT–OVV / Regge), the `S = bits/4`
horizon family (Schwarzschild / Kerr–Newman / Nariai / `bekensteinTauEnt`), the self-calibrating
`rate · t* = log(a/b)` readout (Zeno stripe ↔ Mpemba crossing), and the TFD-halfweight² = Unruh
family; surfaced unnoticed rhymes — `planet_ratio_gravimeter` ↔ `mass_ratio_eq_frequency_ratio`
(both the calibration-free ratio-equals-ratio observable shape) and the KMS `e^(−β·ω)` ↔
Compton-anchor `e^(−Γ·t)` weight pair — and caught the `sin²θ_W = 3/8` fact stated in two modules.
The definition pass and the canonicalizations were added precisely because v1 confirmed the
`κ/2π` and `M² = ħc·k/G` families do not surface from theorem statements alone.

The v2 run then found both validation targets — the `κ/2π` class merges `unruhTemperature`,
`verlindeGravityTemperature`, `hawkingTemperature` and `gibbonsHawkingTemperature`;
`entropicOneBitMass` lands in the cross-scale `√(scale/scale)` crossover class with the SU(3)
`crossoverRadius`, the Caldeira–Leggett critical temperature and the capillary length — plus new
finds: the Minkowski quadratic form as a three-area class (`minkowskiMassShell` /
`poincareRestMassSq` / `minkowskiSq`), Kerr and Reissner–Nordström outer horizons as one
`M + √(M²−a²)` shape, the surface-gravity form recurring in the van der Waals `sigmaOverlap`, and
a `2π·count/scale` quantization class joining `verlindeDisplacementEntropy` with Matsubara
frequencies, flux quantization and the Sagnac phase.

The v3 run added 29 classes that exist only under unfolding, headed by:
`entropicDefect_eq_muon_g2` ↔ `anomaly_eq_schmidt_sq_sub_one` — the WMassAnomaly and
MuonAnomaly arcs formalized the muon `g−2` identity `1/sinh²η = coth²η − 1` independently and the
unfolder proves they are one statement; the Gibbs–Bogoliubov free-energy gap stated in both
IpekCaticha and AlgebraicQFT vocabulary (equality *and* inequality forms); three boost-invariance
theorems (electrogravitic residual / Bell no-signaling / Clifford-fiber action) sharing the
interval-preservation shape; curvature-two-form ↔ gluon-field-strength antisymmetry; and the
interval clock-gain cocycle equation recurring across detector, Araki-production and
measure-kernel semigroup modules.
-/

@[expose] public section

namespace Physlib.Meta.ZilAnalogy

open Lean Elab Command Meta Zil.Datalog

/-- Relation heads: a fingerprint qualifies when one of these appears anywhere inside it. -/
meta def relHeads : List Name := [``Eq, ``Iff, ``Ne, ``LE.le, ``LT.lt]

/-- Heads that are orientation-blind: operand skeletons are sorted. -/
meta def symHeads : List Name := [``Eq, ``Iff, ``Ne, ``And, ``Or]

/-- Associative-commutative heads: operands flattened, sorted, multiplicities absorbed. -/
meta def acHeads : List Name := [``HAdd.hAdd, ``HMul.hMul]

/-- Non-AC binary heads kept in the fingerprint (last two explicit arguments recursed). -/
meta def binHeads : List Name :=
  relHeads ++ [``And, ``Or, ``HSub.hSub, ``HDiv.hDiv, ``HPow.hPow]

/-- Unary heads kept (last argument recursed). -/
meta def keptUn : List Name :=
  [``Not, ``Neg.neg, ``Inv.inv, ``Real.exp, ``Real.log, ``Real.sqrt, ``Real.cos, ``Real.sin,
   ``Real.cosh, ``Real.sinh, ``Real.tanh, ``Complex.normSq]

/-- Nullary heads kept verbatim. -/
meta def keptNullary : List Name := [``Real.pi, ``Complex.I]

/-- Cast-like heads treated as transparent. -/
meta def transparentCasts : List Name :=
  [``Nat.cast, ``Int.cast, ``RatCast.ratCast, ``NNReal.toReal]

meta def shortName (n : Name) : String :=
  match n.components.getLast? with
  | some c => c.toString
  | none => n.toString

/-- Flatten nested applications of one AC head into an operand list. -/
meta partial def acOperands (h : Name) (e : Expr) : List Expr :=
  let args := e.getAppArgs
  match e.getAppFn with
  | .const n _ =>
    if n == h && args.size ≥ 2 then
      acOperands h args[args.size - 2]! ++ acOperands h args[args.size - 1]!
    else [e]
  | _ => [e]

/-- Absorb adjacent duplicate `x`/`z`/`#` operands of a sorted list (multiplicity blindness). -/
meta def squashDups : List String → List String
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    if a == b && (a == "x" || a == "z" || a == "#") then squashDups (b :: t)
    else a :: squashDups (b :: t)

/-- Free variables at positions the fingerprint actually renders, with occurrence counts.  This
mirrors `skel`'s traversal exactly, so occurrences buried in implicit or instance arguments —
which render as part of an opaque `C` — do not count. -/
meta partial def visibleFVars (e : Expr) (acc : Std.HashMap FVarId Nat := {}) :
    Std.HashMap FVarId Nat :=
  match e with
  | .fvar id => acc.insert id (acc.getD id 0 + 1)
  | .mdata _ b => visibleFVars b acc
  | .letE _ _ v b _ => visibleFVars (b.instantiate1 v) acc
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const n _ =>
      if n == ``OfNat.ofNat || n == ``OfScientific.ofScientific then acc
      else if n == ``Exists && args.size ≥ 1 then
        match args[args.size - 1]! with
        | .lam _ _ b _ => visibleFVars b acc
        | p => visibleFVars p acc
      else if transparentCasts.contains n && args.size ≥ 1 then
        visibleFVars args[args.size - 1]! acc
      else if (acHeads.contains n || binHeads.contains n) && args.size ≥ 2 then
        visibleFVars args[args.size - 1]! (visibleFVars args[args.size - 2]! acc)
      else if keptUn.contains n && args.size ≥ 1 then
        visibleFVars args[args.size - 1]! acc
      else acc
    | _ => acc

/-- The variables that occur more than once in the rendered statement. -/
meta def repeatedFVars (e : Expr) : Std.HashSet FVarId :=
  (visibleFVars e).fold (init := {}) fun acc id k => if k ≥ 2 then acc.insert id else acc

/-- The structural fingerprint of an expression.  `blind := true` additionally drops numeric
factors from products (per C7: `2G` vs `4πG` differ only by coefficient), so the blind key
matches a family modulo its prefactor.  Variables in `rep` render `z` (repeated), others `x`. -/
meta partial def skel (blind : Bool) (rep : Std.HashSet FVarId) (e : Expr) : String :=
  match e with
  | .fvar id => if rep.contains id then "z" else "x"
  | .bvar _ => "x"
  | .mvar _ => "x"
  | .lit _ => "#"
  | .mdata _ b => skel blind rep b
  | .letE _ _ v b _ => skel blind rep (b.instantiate1 v)
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
      if n == ``OfNat.ofNat || n == ``OfScientific.ofScientific then "#"
      else if n == ``Exists && args.size ≥ 1 then
        match args[args.size - 1]! with
        | .lam _ _ b _ => s!"(Ex {skel blind rep b})"
        | p => s!"(Ex {skel blind rep p})"
      else if transparentCasts.contains n && args.size ≥ 1 then
        skel blind rep args[args.size - 1]!
      else if acHeads.contains n && args.size ≥ 2 then
        let ops := (acOperands n e).map (skel blind rep)
        let ops := ops.map fun s =>
          if s == "(hPow x #)" then "x" else if s == "(hPow z #)" then "z" else s
        let ops := if blind && n == ``HMul.hMul then ops.filter (· != "#") else ops
        let sorted := (ops.toArray.qsort (· < ·)).toList
        match squashDups sorted with
        | [] => "#"
        | [s] => s
        | ss => s!"({shortName n} {String.intercalate " " ss})"
      else if binHeads.contains n && args.size ≥ 2 then
        let l := skel blind rep args[args.size - 2]!
        let r := skel blind rep args[args.size - 1]!
        if n == ``HPow.hPow && l == "#" && r == "#" then "#"
        else
          let (l, r) := if symHeads.contains n && decide (r < l) then (r, l) else (l, r)
          s!"({shortName n} {l} {r})"
      else if keptUn.contains n && args.size ≥ 1 then
        let inner := skel blind rep args[args.size - 1]!
        -- a transcendental of a pure number is a pure number (log 2 is a coefficient)
        if inner == "#" && n != ``Not then "#" else s!"({shortName n} {inner})"
      else if keptNullary.contains n then shortName n
      else "C"
    | .fvar id => if rep.contains id then "z" else "x"
    | _ => "C"

/-- A fingerprint is interesting if it carries algebraic structure beyond a bare head. -/
meta def interesting (s : String) : Bool :=
  ["hAdd", "hSub", "hMul", "hDiv", "hPow", "exp", "log", "sqrt", "cosh", "sinh", "tanh",
   "neg", "inv", "pi"].any fun kw => decide (1 < (s.splitOn kw).length)

/-- A fingerprint expresses a relation somewhere inside (the qualification gate for theorem
conclusions — `∃`-shaped and conjunctive statements qualify through their inner relation). -/
meta def containsRel (s : String) : Bool :=
  ["Eq", "Iff", "Ne", "le", "lt"].any fun kw => decide (1 < (s.splitOn kw).length)

/-- Area key: the leading namespace components, for cross-domain spread. -/
meta def areaOf (n : Name) : String :=
  let cs := n.components
  String.intercalate "." ((cs.take (min 4 (cs.length - 1))).map toString)

/-- Structural specificity of a fingerprint: transcendentals weigh double; division, powers,
subtraction, negation, inversion, literals and variables weigh one.  A form like `C = C·C` scores
zero — spread alone cannot promote it over a genuinely shaped family. -/
meta def specificity (s : String) : Nat :=
  let cnt (kw : String) : Nat := (s.splitOn kw).length - 1
  2 * (cnt "exp" + cnt "log" + cnt "sqrt" + cnt "sinh" + cnt "cosh" + cnt "tanh"
       + cnt "pi" + cnt "normSq")
    + cnt "hDiv" + cnt "hPow" + cnt "hSub" + cnt "neg" + cnt "inv" + cnt "#" + cnt "x" + cnt "z"

/-- Compiler-generated and elaboration-internal names, excluded from the definition pass. -/
meta def isMachineName (n : Name) : Bool :=
  n.isInternal || n.components.any fun c =>
    let s := c.toString
    s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || s.startsWith "_"

/-- Unfold occurrences of target definitions anywhere inside `e`, recursively, spending at most
`budget` unfold steps — the bound guards against pathological definition chains.  Beta-redexes
left by unfolding are reduced along the way; `let`-bindings are inlined by `skel` itself. -/
meta def unfoldBounded (isTarget : Name → Bool) (budget : Nat) (e : Expr) : MetaM Expr := do
  let ref ← IO.mkRef budget
  Meta.transform e (pre := fun e => do
    if e.isHeadBetaTarget then
      return .visit e.headBeta
    if let .const n _ := e.getAppFn then
      if isTarget n then
        if (← ref.get) > 0 then
          if let some e' ← Meta.unfoldDefinition? e then
            ref.modify (· - 1)
            return .visit e'
    return .continue)

/-- Processing rank of a fingerprint key, for duplicate suppression: an exact match outranks an
unfolded one, which outranks a coefficient-blind one.  Derived from the key's prefix. -/
meta def keyRank (fp : String) : Nat :=
  if fp.startsWith "≈(unf" then 3
  else if fp.startsWith "≈" then 2
  else if fp.startsWith "(unf" then 1
  else 0

meta def runAnalogy (lim : Nat) : CommandElabM Unit := do
  let env ← getEnv
  -- unique attached declarations: the curated physics layer
  let mut attached : NameSet := {}
  for att in (declarationAttachments env).toList do
    attached := attached.insert att.declaration
  let attachedList := attached.toList
  let allGroups ← liftTermElabM do
    let mut allGroups : Std.HashMap String (List Name) := {}
    let addKey (g : Std.HashMap String (List Name)) (fp : String) (d : Name) :
        Std.HashMap String (List Name) := g.insert fp (d :: g.getD fp [])
    -- pass 0: the Physlib definition set (feeds both the definition pass and the unfolder),
    -- fingerprinting each definition body along the way
    let mut physlibDefs : NameSet := {}
    for (n, ci) in env.constants.toList do
      if let .defnInfo v := ci then
        unless isMachineName n do
          let inPhyslib :=
            match env.getModuleIdxFor? n with
            | some idx =>
              match env.header.moduleNames[idx.toNat]? with
              | some m => m.toString.startsWith "Physlib"
              | none => false
            | none => false
          if inPhyslib then
            physlibDefs := physlibDefs.insert n
            let fps? ← try
                lambdaTelescope v.value fun _ body => do
                  let rep := repeatedFVars body
                  let s := skel false rep body
                  return if interesting s then
                    some (s!"(def {s})", s!"≈(def {skel true rep body})") else none
              catch _ => pure (none : Option (String × String))
            if let some (fp, bfp) := fps? then
              allGroups := addKey allGroups fp n
              allGroups := addKey allGroups bfp n
    let defSet := physlibDefs
    -- pass 1: attached theorem conclusions — exact, blind, and with Physlib definitions
    -- unfolded in place (the fingerprint is re-gated after unfolding, so definitional
    -- predicates that abbreviate an equation join the equation's family)
    for d in attachedList do
      if let some info := env.find? d then
        let keys ← try
            forallTelescope info.type fun _ concl => do
              let rep := repeatedFVars concl
              let s := skel false rep concl
              let b := skel true rep concl
              let sOk := interesting s && containsRel s
              let bOk := interesting b && containsRel b
              let concl' ← unfoldBounded defSet.contains 64 concl
              let unf ← forallTelescope concl' fun _ c => do
                let rep' := repeatedFVars c
                return (skel false rep' c, skel true rep' c)
              let mut acc : List String := []
              if sOk then acc := s :: acc
              let (u, ub) := unf
              if interesting u && containsRel u && (!sOk || u != s) then
                acc := s!"(unf {u})" :: acc
              if interesting ub && containsRel ub && (!bOk || ub != b) && u != ub then
                acc := s!"≈(unf {ub})" :: acc
              if bOk && b != s then acc := s!"≈{b}" :: acc
              return acc
          catch _ => pure ([] : List String)
        for fp in keys do
          allGroups := addKey allGroups fp d
    return allGroups
  -- duplicate suppression: a processed key (unfolded/blind) earns its place only by grouping a
  -- declaration set no less-processed key already groups
  let mut bySig : Std.HashMap String (String × List Name) := {}
  for (fp, ds) in allGroups.toList do
    let sig := String.intercalate "," ((ds.map toString).toArray.qsort (· < ·)).toList
    match bySig.get? sig with
    | some (fp₀, _) => if keyRank fp < keyRank fp₀ then bySig := bySig.insert sig (fp, ds)
    | none => bySig := bySig.insert sig (fp, ds)
  -- rank: specificity × cross-area spread, damped by class size (a 100-member class is a
  -- category, not a family) — shaped, surprising families first
  let scored := bySig.toList.filterMap fun (_, fp, ds) =>
    let areas := (ds.map areaOf).eraseDups
    if areas.length ≥ 2 && ds.length ≥ 2 then
      some (fp, ds, areas.length, specificity fp * areas.length * 8 / (8 + ds.length))
    else none
  let sorted := scored.toArray.qsort fun a b =>
    a.2.2.2 > b.2.2.2
    || (a.2.2.2 == b.2.2.2 && a.2.2.1 > b.2.2.1)
    || (a.2.2.2 == b.2.2.2 && a.2.2.1 == b.2.2.1 && a.2.1.length > b.2.1.length)
  let mut out := ""
  let mut shown := 0
  for (fp, ds, nAreas, score) in sorted.toList do
    if shown < lim then
      out := out ++ s!"◆ score {score}: {nAreas} areas, {ds.length} declarations — form {fp}\n"
      for d in ds.reverse.take 8 do
        out := out ++ s!"    · {d}\n"
      if ds.length > 8 then out := out ++ s!"    … {ds.length - 8} more\n"
      shown := shown + 1
  logInfo m!"zil analogy: {scored.length} cross-area form classes (showing {shown})\n{out}"

syntax (name := zilAnalogyCmd) "#zil_analogy" : command
syntax (name := zilAnalogyLimitCmd) "#zil_analogy " " limit " num : command

elab_rules : command
  | `(#zil_analogy) => runAnalogy 10
  | `(#zil_analogy limit $n:num) => runAnalogy n.getNat

end Physlib.Meta.ZilAnalogy
