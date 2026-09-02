/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilAnalogy
public import Physlib.Units.PlanckUnitsInformation

public meta import Physlib.Units.Dimension
public meta import Physlib.Units.InformationDimensionCollision
public meta import Physlib.Units.GravitationalCouplingDimensions
meta import Zil.Datalog.Attach

/-!
# `#zil_dimension_*` — dimensional analysis over the declaration graph

`Physlib.Units` carries the object-level dimension algebra: `Dimension LTMCTIDimensionBase` is the rational-exponent
group over ⟨length, time, mass, charge, temperature, information⟩, with the framework convention
`[k_B] = E·Θ⁻¹·I⁻¹` (the Brillouin/Landauer information slot — see
`Units.InformationDimensionCollision`).  This module puts that algebra to work *on the code*: it
infers the dimension of definition bodies and theorem conclusions from the names of their binders,
using the **same `Dimension LTMCTIDimensionBase` values** (`action_dim`, `boltzmann_dim`, `newtonConstant_dim`, …) —
no parallel dimension system.

* `#zil_dimension_of decl` — infer and print the dimension of a definition's body (or, for a
  theorem, the dimension of each side of its concluding relation and the homogeneity verdict).
  `#zil_dimension_of decl with "a : L T^-2, S : L^2 T^-2 M Θ^-1"` supplies binder dimensions the
  conventional table does not know.
* `#zil_dimension_audit [limit n]` — sweep every Physlib definition and every ZIL-attached theorem
  conclusion: report **inhomogeneities** (a sum of unequal known dimensions, a relation between
  unequal known dimensions, a dimensionful argument to `exp`/`log`/trig) and print the
  **dimensional census** — all inferred quantities grouped by dimension, which is retrieval by
  physical kind: every temperature in the repository, every action, every rate.
* `#zil_assert_dimension decl "L^2 T^-1 M"` — the build-enforced form: fails when the inferred
  dimension is unknown or differs from the declared one, so a definition's dimensional identity
  becomes part of the build the way `#zil_assert_primitive` makes graph facts part of the build.
* `#zil_assert_relation_defect decl "I^-1" [with …]` — the theorem-level form: in the
  conclusion (descending through `∧ ∨ ↔ ¬ ∃`), every relation with determinable sides must
  carry defect `[rhs]/[lhs]` trivial or exactly the declared one (either sign), at least one
  relation must be determinable, and for a nontrivial declaration at least one must actually
  carry it — "one defect threads the statement", per theorem, vacuity-guarded.

Inference: binder names are read against a **conventional table** (`ℏ c G kB m M t τ T r R ℓ Δx
Δt ω Ω ν E v q`, angles/counts dimensionless), trailing indices stripped (`m₁`, `R'`).  Unknown
names stay unknown and poison to unknown rather than guess; `with`-overrides resolve ambiguity
per call.  Dimensions propagate through `+ − × / ^ √ ⁻¹ ‖·‖ normSq`, casts and `let`; a Physlib
definition applied inside a body is unfolded (bounded) so `planckMass`-style compounds resolve.
Sums adopt the known side's dimension when the other is unknown — the standard homogeneity
assumption; the *check* only fires when both sides are known and disagree.

Honest limits: findings are candidates — a flagged sum may be a genuine bug, a geometric-units
module (`c = G = 1` collapses L/T/M on purpose), or an unconventional binder name; the table
deliberately omits ambiguous letters (`a`, `p`, `S`, `k`, `λ`, `β`, `g`, `x`) so absence of a
finding under unknown binders is no certificate.  Under the framework `k_B`, temperatures read
`Θ·I` — that is the information-slot convention, not an error (override `kB : L^2 T^-2 M Θ^-1`
for SI-style reading).  Nonliteral exponents on dimensionful bases and `match` on symbolic
arguments stay unknown.

First full-repository audit: 2609 definitions dimensioned, 294 findings.  Verified positives of
the design: `verlindeDisplacementEntropy` infers `[L² T⁻² M Θ⁻¹ I⁻¹]` (entropy per nat, the
framework convention) and `eotvos_null` checks homogeneous at `[L T⁻²]` on both sides — the WEP
observable is dimensionally an acceleration.  Observed collision classes, confirming the
candidate-not-verdict stance: CFT modules bind `c` as the *central charge* (their entropies
census as velocity), Thomas-BMT binds `G` as the *anomaly factor*, module-theory support code
binds `m` as a *module element*; Euclidean-action modules flag `exp` of `[M²]` because the
saddle exponent is written in `G = c = ℏ = 1` units.  Each is readable from the finding itself.

**The `exp(M²)` findings under holographic `G`** (re-evaluation, machine-checked in
`EntropicWepDepthGate` §6): restoring constants, the Schwarzschild saddle exponent is
`4πGM²/(ħc)`.  Under SI `G` it is dimensionless — the finding is a geometric-units artifact.
But the framework *forces* `[G] = L³M⁻¹T⁻²·I⁻¹` once the bit count carries `I`
(`GravitationalCouplingDimensions.holographicBits_forces_newton_perBit`: Newton's constant is
area-per-bit), and under holographic `G` the same number splits by route: the area route
`A·c³/(4Gℏ)` carries `I` (a nat count — the canonical dissipative exponent,
`imaginaryAction_dim = I𝓭`), while the mass route `4πGM²/(ħc)` carries `I⁻¹` — the **one-nat
defect** of `oneNat_threads_system`, with sign set by which side of the holographic identity
`G` enters.  The two readings differ by `I²`, are numerically identical, and are
indistinguishable to the 5-base projection (`forgetInfo`) — the geometric-units modules are
exactly where that fault line hides.  Accordingly `exp` accepts a pure-`I` argument as
framework-canonical; the `I⁻¹` side keeps being flagged, because it genuinely is the
defect-carrying form.
-/

@[expose] public section

namespace Physlib.Meta.ZilDimension

open Lean Elab Command Meta
open Dimension.LTMCTI
open Physlib.Units.InformationDimensionCollision
open Physlib.Units.GravitationalCouplingDimensions

/-! ### The dimension value layer (object-level `Dimension LTMCTIDimensionBase`, reused) -/

meta def dimEq (d₁ d₂ : Dimension LTMCTIDimensionBase) : Bool :=
  d₁.exponent .length == d₂.exponent .length && d₁.exponent .time == d₂.exponent .time && d₁.exponent .mass == d₂.exponent .mass
    && d₁.exponent .charge == d₂.exponent .charge && d₁.exponent .temperature == d₂.exponent .temperature
    && d₁.exponent .information == d₂.exponent .information

meta def dimIsOne (d : Dimension LTMCTIDimensionBase) : Bool := dimEq d 1

meta def renderExp (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-- Render in the basis order of `Units.Dimension`: `L T M C Θ I`; dimensionless renders `1`. -/
meta def renderDim (d : Dimension LTMCTIDimensionBase) : String :=
  let piece (b : String) (q : ℚ) : Option String :=
    if q == 0 then none else if q == 1 then some b else some s!"{b}^{renderExp q}"
  let ps := [piece "L" (d.exponent .length), piece "T" (d.exponent .time), piece "M" (d.exponent .mass),
             piece "C" (d.exponent .charge), piece "Θ" (d.exponent .temperature), piece "I" (d.exponent .information)]
  match ps.filterMap id with
  | [] => "1"
  | l => String.intercalate " " l

meta def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [a] => (a.toInt?).map fun n => (n : ℚ)
  | [a, b] => do
    let n ← a.toInt?
    let d ← b.toNat?
    if d == 0 then none else pure ((n : ℚ) / (d : ℚ))
  | _ => none

/-- Parse `"L^2 T^-2 M Θ^-1 I^-1"`-style dimension strings (`1` = dimensionless). -/
meta def parseDim (s : String) : Option (Dimension LTMCTIDimensionBase) := do
  let mut acc : Dimension LTMCTIDimensionBase := 1
  for tok in (s.splitOn " ").filter (· ≠ "") do
    if tok == "1" then
      continue
    let (base, expStr) :=
      match tok.splitOn "^" with
      | [b] => (b, "1")
      | [b, e] => (b, e)
      | _ => ("", "")
    let q ← parseRat expStr
    let b : Dimension LTMCTIDimensionBase ←
      match base with
      | "L" => some L𝓭 | "T" => some T𝓭 | "M" => some M𝓭
      | "C" => some C𝓭 | "Θ" => some Θ𝓭 | "I" => some I𝓭
      | _ => none
    acc := acc * b ^ q
  return acc

/-! ### The conventional binder table -/

/-- Conventional physics binder names.  Ambiguous letters are deliberately absent — resolve them
with `with "name : DIM"` overrides. -/
meta def binderTable : List (String × (Dimension LTMCTIDimensionBase)) :=
  [("ℏ", action_dim), ("ħ", action_dim), ("hbar", action_dim),
   ("c", velocity_dim), ("v", velocity_dim),
   ("G", newtonConstant_dim),
   ("kB", boltzmann_dim), ("k_B", boltzmann_dim),
   ("m", M𝓭), ("M", M𝓭),
   ("t", T𝓭), ("τ", T𝓭), ("Δt", T𝓭), ("Δτ", T𝓭),
   ("T", Θ𝓭),
   ("r", L𝓭), ("R", L𝓭), ("ℓ", L𝓭), ("Δx", L𝓭),
   ("ω", frequency_dim), ("Ω", frequency_dim), ("ν", frequency_dim),
   ("E", energy_dim), ("q", C𝓭),
   ("θ", 1), ("φ", 1), ("α", 1), ("n", 1), ("N", 1), ("K", 1)]

/-- Strip trailing indices and primes: `m₁ → m`, `R' → R`, `t2 → t`. -/
meta def stripIndex (s : String) : String :=
  String.mk ((s.toList.reverse.dropWhile fun ch =>
    "₀₁₂₃₄₅₆₇₈₉0123456789'".toList.contains ch).reverse)

meta def lookupBinder (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) (name : String) :
    Option (Dimension LTMCTIDimensionBase) :=
  match overrides.get? name with
  | some d => some d
  | none =>
    match overrides.get? (stripIndex name) with
    | some d => some d
    | none =>
      match binderTable.find? (·.1 == name) with
      | some (_, d) => some d
      | none => (binderTable.find? (·.1 == stripIndex name)).map (·.2)

/-- Parse `"a : L T^-2, S : L^2 T^-2 M Θ^-1"` override strings. -/
meta def parseOverrides (s : String) : CommandElabM (Std.HashMap String (Dimension LTMCTIDimensionBase)) := do
  let mut acc : Std.HashMap String (Dimension LTMCTIDimensionBase) := {}
  for entry in (s.splitOn ",").filter (fun e => e.trimAscii.toString ≠ "") do
    match entry.splitOn ":" with
    | [name, dimStr] =>
      match parseDim dimStr.trimAscii.toString with
      | some d => acc := acc.insert name.trimAscii.toString d
      | none => throwError "zil_dimension: cannot parse dimension `{dimStr.trimAscii.toString}`"
    | _ => throwError "zil_dimension: override entry `{entry}` is not `name : DIM`"
  return acc

/-! ### The evaluator -/

/-- Inference result: a known dimension, unknown (insufficient information — never a finding), or
an inconsistency (the finding). -/
meta inductive DimR where
  | known (d : Dimension LTMCTIDimensionBase)
  | unknown
  | bad (msg : String)

meta partial def numLit? : Expr → Option ℚ
  | .lit (.natVal n) => some (n : ℚ)
  | .mdata _ b => numLit? b
  | e =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const n _ =>
      if n == ``OfNat.ofNat && args.size ≥ 2 then numLit? args[1]!
      else if n == ``OfScientific.ofScientific && args.size ≥ 5 then do
        let m ← numLit? args[2]!
        let e10 ← numLit? args[4]!
        match args[3]! with
        | .const ``Bool.true _ => some (m / (10 : ℚ) ^ (e10.num.toNat))
        | .const ``Bool.false _ => some (m * (10 : ℚ) ^ (e10.num.toNat))
        | _ => none
      else if n == ``Neg.neg && args.size ≥ 1 then (numLit? args[args.size - 1]!).map (- ·)
      else if ZilAnalogy.transparentCasts.contains n && args.size ≥ 1 then
        numLit? args[args.size - 1]!
      else none
    | _ => none

meta def strictTranscendentals : List Name :=
  [``Real.exp, ``Real.log, ``Real.cos, ``Real.sin, ``Real.cosh, ``Real.sinh, ``Real.tanh,
   ``Complex.exp, ``Complex.log, ``Complex.cos, ``Complex.sin]

meta def relLike : List Name := [``Eq, ``Ne, ``LE.le, ``LT.lt]

/-- Infer the dimension of `e`.  Binder dimensions come from `lookup`; Physlib definitions
applied inside are unfolded with `fuel`.  Unknowns poison to unknown; the homogeneity checks
fire only between *known* dimensions. -/
meta partial def dimOf (lookup : String → Option (Dimension LTMCTIDimensionBase)) (defSet : NameSet) (depth : Nat)
    (e : Expr) : MetaM DimR := do
  let combineMul (op : ℚ → ℚ) (l r : DimR) : DimR :=
    match l, r with
    | .bad m, _ => .bad m
    | _, .bad m => .bad m
    | .known a, .known b => .known (a * b ^ op 1)
    | _, _ => .unknown
  let combineSum (l r : DimR) (ctx : String) : DimR :=
    match l, r with
    | .bad m, _ => .bad m
    | _, .bad m => .bad m
    | .known a, .known b =>
      if dimEq a b then .known a
      else .bad s!"inhomogeneous {ctx}: [{renderDim a}] vs [{renderDim b}]"
    | .known a, .unknown => .known a
    | .unknown, .known b => .known b
    | _, _ => .unknown
  let propPair (l r : DimR) (ctx : String) : DimR :=
    match l, r with
    | .bad m, _ => .bad m
    | _, .bad m => .bad m
    | .known a, .known b =>
      if dimEq a b then .known 1
      else .bad s!"{ctx} compares [{renderDim a}] with [{renderDim b}]"
    | _, _ => .known 1
  match e with
  | .fvar id =>
    let decl ← id.getDecl
    let name := decl.userName.toString
    -- Fail closed on non-scalar binders.  The binder-name table lists *scalar* physical
    -- quantities, so applying it to a binder purely by name silently misattributes any
    -- tensor-valued argument that happens to share a letter with a constant: in the complex
    -- Einstein equation `G` is the Einstein tensor, `T` the stress-energy tensor and `S` the
    -- entropic stress, and typing them as Newton's constant, a temperature and an entropy
    -- produced a confident, wrong homogeneity verdict.  Anything that is not a real number
    -- is reported unknown, which surfaces as `not determined` rather than as a false result.
    let ty ← whnf decl.type
    if !ty.isConstOf ``Real then return .unknown
    return match lookup name with
    | some d => .known d
    | none => .unknown
  | .bvar _ => return .unknown
  | .mvar _ => return .unknown
  | .lit (.natVal 0) => return .unknown   -- zero is dimensionally polymorphic
  | .lit _ => return .known 1
  | .mdata _ b => dimOf lookup defSet depth b
  | .letE _ _ v b _ => dimOf lookup defSet depth (b.instantiate1 v)
  | _ =>
    let args := e.getAppArgs
    let recArg (i : Nat) : MetaM DimR := dimOf lookup defSet depth args[args.size - i]!
    match e.getAppFn with
    | .const n _ =>
      if n == ``OfNat.ofNat || n == ``OfScientific.ofScientific then
        -- zero is dimensionally polymorphic: `x = 0` must not force dimensionlessness
        return if numLit? e == some 0 then .unknown else .known 1
      else if ZilAnalogy.transparentCasts.contains n && args.size ≥ 1 then recArg 1
      else if n == ``Complex.ofReal && args.size ≥ 1 then recArg 1
      else if ZilAnalogy.keptNullary.contains n then return .known 1
      else if (n == ``HMul.hMul || n == ``HSMul.hSMul) && args.size ≥ 2 then
        return combineMul id (← recArg 2) (← recArg 1)
      else if n == ``HDiv.hDiv && args.size ≥ 2 then
        return combineMul Neg.neg (← recArg 2) (← recArg 1)
      else if (n == ``HAdd.hAdd || n == ``HSub.hSub) && args.size ≥ 2 then
        return combineSum (← recArg 2) (← recArg 1) "sum"
      else if n == ``HPow.hPow && args.size ≥ 2 then
        match ← recArg 2 with
        | .bad m => return .bad m
        | .unknown => return .unknown
        | .known b =>
          if dimIsOne b then return .known 1
          else
            match numLit? args[args.size - 1]! with
            | some k => return .known (b ^ k)
            | none => return .unknown
      else if n == ``Neg.neg && args.size ≥ 1 then recArg 1
      else if n == ``Inv.inv && args.size ≥ 1 then
        return match ← recArg 1 with
        | .known d => .known (d ^ (-1 : ℚ))
        | r => r
      else if n == ``Real.sqrt && args.size ≥ 1 then
        return match ← recArg 1 with
        | .known d => .known (d ^ ((1 : ℚ)/2))
        | r => r
      else if n == ``Norm.norm && args.size ≥ 1 then recArg 1
      else if n == ``Complex.normSq && args.size ≥ 1 then
        return match ← recArg 1 with
        | .known d => .known (d ^ (2 : ℚ))
        | r => r
      else if strictTranscendentals.contains n && args.size ≥ 1 then
        return match ← recArg 1 with
        | .bad m => .bad m
        | .known d =>
          if dimIsOne d then .known 1
          -- pure information is framework-canonical here: the dissipative exponent is a nat
          -- count (`ComplexActionDimension.imaginaryAction_dim = I𝓭`; a Boltzmann exponent
          -- `E/(k_B T)` carries `I` under the framework `k_B`)
          else if dimEq d I𝓭 then .known 1
          else .bad s!"dimensionful argument [{renderDim d}] to {ZilAnalogy.shortName n}"
        | .unknown => .known 1
      else if relLike.contains n && args.size ≥ 2 then
        return propPair (← recArg 2) (← recArg 1) "relation"
      else if (n == ``And || n == ``Or || n == ``Iff) && args.size ≥ 2 then
        return match ← recArg 2, ← recArg 1 with
        | .bad m, _ => .bad m
        | _, .bad m => .bad m
        | _, _ => .known 1
      else if n == ``Not && args.size ≥ 1 then
        return match ← recArg 1 with
        | .bad m => .bad m
        | _ => .known 1
      else if n == ``Exists && args.size ≥ 1 then
        match args[args.size - 1]! with
        | .lam _ _ b _ =>
          return match ← dimOf lookup defSet depth b with
          | .bad m => .bad m
          | _ => .known 1
        | _ => return .known 1
      else if n == ``Constants.kB then
        -- Framework constant as a *def*, not a binder (`Constants.kB := kBAx.1`, a numeric
        -- subtype projection with no dimensional structure to unfold into).  Defer to the
        -- binder table under the same name, so `with` overrides and typing experiments flow
        -- through the constant exactly as through the binder.
        return match lookup "kB" with
        | some d => .known d
        | none => .unknown
      else if defSet.contains n && depth > 0 then
        match ← Meta.unfoldDefinition? e with
        | some e' => dimOf lookup defSet (depth - 1) e'
        | none => return .unknown
      else return .unknown
    | _ => return .unknown

/-! ### Shared sweep -/

meta def physlibDefSetCore (env : Environment) : NameSet := Id.run do
  let mut acc : NameSet := {}
  for (n, ci) in env.constants.toList do
    if let .defnInfo _ := ci then
      unless ZilAnalogy.isMachineName n do
        let inPhyslib :=
          match env.getModuleIdxFor? n with
          | some idx =>
            match env.header.moduleNames[idx.toNat]? with
            | some m => m.toString.startsWith "Physlib"
            | none => false
          | none => false
        if inPhyslib then acc := acc.insert n
  return acc

/-- Session cache for the definition set, keyed by the imported-constant count — a file running
many `#zil_assert_dimension`/`#zil_assert_relation_defect` commands sweeps the environment once,
not once per command. -/
meta initialize physlibDefSetCache : IO.Ref (Option (Nat × NameSet)) ← IO.mkRef none

meta def physlibDefSet (env : Environment) : IO NameSet := do
  let key := env.header.moduleNames.size
  if let some (k, s) ← physlibDefSetCache.get then
    if k == key then return s
  let s := physlibDefSetCore env
  physlibDefSetCache.set (some (key, s))
  return s

meta def lookupOf (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) : String → Option (Dimension LTMCTIDimensionBase) :=
  lookupBinder overrides

/-! ### Commands -/

meta def runDimensionOf (d : Name) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) :
    CommandElabM Unit := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  match env.find? d with
  | none => throwError "zil_dimension_of: unknown declaration {d}"
  | some (.defnInfo v) =>
    let (binderLines, result) ← liftTermElabM <|
      lambdaTelescope v.value fun xs body => do
        let mut lines := ""
        for x in xs do
          let xdecl ← x.fvarId!.getDecl
          let name := xdecl.userName.toString
          -- same fail-closed rule as `dimOf`: only real-valued binders may be typed from
          -- the name table, so a tensor-valued `G`/`T`/`S` is shown as unknown rather than
          -- as Newton's constant, a temperature or an entropy
          let xty ← whnf xdecl.type
          let tag :=
            if !xty.isConstOf ``Real then "? (non-scalar)"
            else match lookup name with
              | some dm => renderDim dm
              | none => "?"
          lines := lines ++ s!"  {name} : {tag}\n"
        let r ← dimOf lookup defSet 8 body
        return (lines, r)
    let verdict := match result with
      | .known dm => s!"[{renderDim dm}]"
      | .unknown => "not determined (unknown binder dimensions — add `with` overrides)"
      | .bad m => s!"INCONSISTENT — {m}"
    logInfo m!"zil dimension of {d}:\n{binderLines}  ⟹ {verdict}"
  | some info =>
    let verdict ← liftTermElabM <|
      forallTelescope info.type fun _ concl => do
        let args := concl.getAppArgs
        match concl.getAppFn with
        | .const n _ =>
          if relLike.contains n && args.size ≥ 2 then
            let l ← dimOf lookup defSet 8 args[args.size - 2]!
            let r ← dimOf lookup defSet 8 args[args.size - 1]!
            let show' : DimR → String
              | .known dm => s!"[{renderDim dm}]"
              | .unknown => "?"
              | .bad m => s!"INCONSISTENT ({m})"
            let verdict := match l, r with
              | .known a, .known b =>
                if dimEq a b then "homogeneous" else "INHOMOGENEOUS"
              | _, _ => "not fully determined"
            return s!"lhs {show' l}  rhs {show' r}  — {verdict}"
          else return "conclusion is not a relation — nothing to compare"
        | _ => return "conclusion is not a relation — nothing to compare"
    logInfo m!"zil dimension of {d} (theorem):\n  {verdict}"

meta def runDimensionAudit (lim : Nat) (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) :
    CommandElabM Unit := do
  let env ← getEnv
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  let (findings, census, nKnown, nUnknown) ← liftTermElabM do
    let mut findings : List (Name × String) := []
    let mut census : Std.HashMap String (List Name) := {}
    let mut nKnown := 0
    let mut nUnknown := 0
    for n in defSet.toList do
      if let some (.defnInfo v) := env.find? n then
        let r ← try
            lambdaTelescope v.value fun _ body => dimOf lookup defSet 8 body
          catch _ => pure DimR.unknown
        match r with
        | .bad m => findings := (n, m) :: findings
        | .known d =>
          if !dimIsOne d then
            let key := renderDim d
            census := census.insert key (n :: census.getD key [])
          nKnown := nKnown + 1
        | .unknown => nUnknown := nUnknown + 1
    -- attached theorem conclusions: relation homogeneity
    let mut attached : NameSet := {}
    for att in (Zil.Datalog.declarationAttachments env).toList do
      attached := attached.insert att.declaration
    for d in attached.toList do
      if let some info := env.find? d then
        let bad? ← try
            forallTelescope info.type fun _ concl => do
              match ← dimOf lookup defSet 8 concl with
              | .bad m => return some m
              | _ => return none
          catch _ => pure none
        if let some m := bad? then
          findings := (d, m) :: findings
    return (findings, census, nKnown, nUnknown)
  -- information-charge histogram: how many nats each dimensioned formula converts
  let mut charge : Std.HashMap String Nat := {}
  for (dim, ds) in census.toList do
    match parseDim dim with
    | some d =>
      let key := renderExp (d.exponent .information)
      charge := charge.insert key (charge.getD key 0 + ds.length)
    | none => pure ()
  let mut out := s!"zil dimension audit: {nKnown} definitions dimensioned, {nUnknown} unknown, \
{findings.length} findings\n"
  let chargeRanked := charge.toList.toArray.qsort fun a b => a.2 > b.2
  out := out ++ "── information charge (I exponent) over dimensioned, non-dimensionless defs ──\n"
  for (k, cnt) in chargeRanked.toList do
    out := out ++ s!"  I^{k}: {cnt}\n"
  out := out ++ "── findings (candidates: bug, geometric units, or binder convention) ──\n"
  for (n, m) in findings.take lim do
    out := out ++ s!"  ✗ {n}\n      {m}\n"
  if findings.length > lim then out := out ++ s!"  … {findings.length - lim} more\n"
  out := out ++ "── census (top dimensions across areas) ──\n"
  let ranked := census.toList.toArray.qsort fun a b => a.2.length > b.2.length
  let mut shown := 0
  for (dim, ds) in ranked.toList do
    if shown < lim then
      out := out ++ s!"  [{dim}] — {ds.length} quantities\n"
      for n in ds.reverse.take 6 do
        out := out ++ s!"      · {n}\n"
      if ds.length > 6 then out := out ++ s!"      … {ds.length - 6} more\n"
      shown := shown + 1
  logInfo out

meta def runAssertDimension (d : Name) (target : String)
    (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) : CommandElabM Unit := do
  let env ← getEnv
  let some expected := parseDim target
    | throwError "zil_assert_dimension: cannot parse dimension `{target}`"
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  match env.find? d with
  | some (.defnInfo v) =>
    let r ← liftTermElabM <| lambdaTelescope v.value fun _ body => dimOf lookup defSet 8 body
    match r with
    | .known dm =>
      if dimEq dm expected then
        logInfo m!"zil_assert_dimension: {d} has dimension [{renderDim dm}]"
      else
        throwError "zil_assert_dimension FAILED: {d} has dimension [{renderDim dm}], \
          asserted [{renderDim expected}]"
    | .unknown =>
      throwError "zil_assert_dimension FAILED: dimension of {d} is not determined — \
        certifying it would be vacuous; supply `with` overrides"
    | .bad m => throwError "zil_assert_dimension FAILED: {d} is inconsistent — {m}"
  | _ => throwError "zil_assert_dimension: {d} is not a definition"

/-- Collect every relation (`= ≠ ≤ <`) inside a conclusion — descending through `∧ ∨ ↔ ¬ ∃ ∀` —
whose two sides both have determinable dimensions. -/
meta partial def collectRelDefects (lookup : String → Option (Dimension LTMCTIDimensionBase)) (defSet : NameSet)
    (e : Expr) : MetaM (List (Dimension LTMCTIDimensionBase × (Dimension LTMCTIDimensionBase))) := do
  match e with
  | .mdata _ b => collectRelDefects lookup defSet b
  | .letE _ _ v b _ => collectRelDefects lookup defSet (b.instantiate1 v)
  | .forallE _ _ b _ => collectRelDefects lookup defSet b
  | .lam _ _ b _ => collectRelDefects lookup defSet b
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const n _ =>
      if relLike.contains n && args.size ≥ 2 then
        let l ← dimOf lookup defSet 8 args[args.size - 2]!
        let r ← dimOf lookup defSet 8 args[args.size - 1]!
        match l, r with
        | .known a, .known b => return [(a, b)]
        | _, _ => return []
      else if (n == ``And || n == ``Or || n == ``Iff) && args.size ≥ 2 then
        return (← collectRelDefects lookup defSet args[args.size - 2]!)
          ++ (← collectRelDefects lookup defSet args[args.size - 1]!)
      else if (n == ``Not || n == ``Exists) && args.size ≥ 1 then
        collectRelDefects lookup defSet args[args.size - 1]!
      else return []
    | _ => return []

/-- `#zil_assert_relation_defect decl "D" [with overrides]` — build-enforce that in the theorem's
conclusion, every relation with determinable sides carries defect `[rhs]/[lhs] ∈ {1, D, D⁻¹}`,
at least one relation is determinable, and (for `D ≠ 1`) at least one actually carries `D` or
`D⁻¹`.  This is the machine form of "one defect threads the statement" applied per theorem. -/
meta def runAssertRelationDefect (d : Name) (target : String)
    (overrides : Std.HashMap String (Dimension LTMCTIDimensionBase)) : CommandElabM Unit := do
  let env ← getEnv
  let some expected := parseDim target
    | throwError "zil_assert_relation_defect: cannot parse dimension `{target}`"
  let defSet ← physlibDefSet env
  let lookup := lookupOf overrides
  match env.find? d with
  | none => throwError "zil_assert_relation_defect: unknown declaration {d}"
  | some info =>
    let defects ← liftTermElabM <|
      forallTelescope info.type fun _ concl => collectRelDefects lookup defSet concl
    if defects.isEmpty then
      throwError "zil_assert_relation_defect FAILED: no relation in {d} has both sides \
        determinable — the assertion would be vacuous; supply `with` overrides"
    let expectedInv := expected ^ (-1 : ℚ)
    let mut carried : Nat := 0
    for (l, r) in defects do
      let q := r * l ^ (-1 : ℚ)
      if dimEq q 1 then pure ()
      else if dimEq q expected || dimEq q expectedInv then carried := carried + 1
      else
        throwError "zil_assert_relation_defect FAILED: a relation in {d} has defect \
          [{renderDim q}] (lhs [{renderDim l}], rhs [{renderDim r}]) — not trivial, not \
          [{renderDim expected}], not [{renderDim expectedInv}]"
    if !dimEq expected 1 && carried == 0 then
      throwError "zil_assert_relation_defect FAILED: every determinable relation in {d} is \
        homogeneous — asserting defect [{renderDim expected}] would be vacuous"
    logInfo m!"zil_assert_relation_defect: {d} — {defects.length} relation(s) determinable, \
{carried} carrying [{renderDim expected}]±¹, rest homogeneous"

syntax (name := zilDimOfCmd) "#zil_dimension_of " ident : command
syntax (name := zilDimOfWithCmd) "#zil_dimension_of " ident " with " str : command
syntax (name := zilDimAuditCmd) "#zil_dimension_audit" : command
syntax (name := zilDimAuditLimitCmd) "#zil_dimension_audit " " limit " num : command
syntax (name := zilDimAuditWithCmd) "#zil_dimension_audit " " with " str : command
syntax (name := zilDimAuditLimitWithCmd) "#zil_dimension_audit " " limit " num " with " str : command
syntax (name := zilDimAssertCmd) "#zil_assert_dimension " ident str : command
syntax (name := zilDimAssertWithCmd) "#zil_assert_dimension " ident str " with " str : command
syntax (name := zilRelDefectCmd) "#zil_assert_relation_defect " ident str : command
syntax (name := zilRelDefectWithCmd) "#zil_assert_relation_defect " ident str " with " str : command

elab_rules : command
  | `(#zil_dimension_of $d:ident) => runDimensionOf d.getId {}
  | `(#zil_dimension_of $d:ident with $o:str) => do
    runDimensionOf d.getId (← parseOverrides o.getString)
  | `(#zil_dimension_audit) => runDimensionAudit 15 {}
  | `(#zil_dimension_audit limit $n:num) => runDimensionAudit n.getNat {}
  | `(#zil_dimension_audit with $o:str) => do
    runDimensionAudit 15 (← parseOverrides o.getString)
  | `(#zil_dimension_audit limit $n:num with $o:str) => do
    runDimensionAudit n.getNat (← parseOverrides o.getString)
  | `(#zil_assert_dimension $d:ident $t:str) => runAssertDimension d.getId t.getString {}
  | `(#zil_assert_dimension $d:ident $t:str with $o:str) => do
    runAssertDimension d.getId t.getString (← parseOverrides o.getString)
  | `(#zil_assert_relation_defect $d:ident $t:str) => runAssertRelationDefect d.getId t.getString {}
  | `(#zil_assert_relation_defect $d:ident $t:str with $o:str) => do
    runAssertRelationDefect d.getId t.getString (← parseOverrides o.getString)

end Physlib.Meta.ZilDimension
