/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil.Datalog.Attach

/-!
# Standing detector for definitional-unfold over-claims

The reference defect (fixed): `gMuMu_is_gaussian_fisher_info` / `madelung_born_rule` — a theorem whose proof
is a pure definitional unfolding (`rfl` / `rw [only-defs]`, so the statement's two sides are already defeq)
yet whose ZIL `formalizes @ "claim:…"` asserts a substantive *conceptual identification* the tautology does
not establish. It slipped through because the non-vacuity check (`#physlib_non_vacuous`,
`AxiomWhitelistCheck.isDefinitionalRestatement`) only runs on explicitly-listed declarations.

`#zil_definitional_overclaim_report` closes that: it runs the same `isDefinitionalRestatement` primitive
over **every** ZIL-formalized theorem, and reports those whose statement is definitionally trivial — flagging
the subset whose claim reads as a conceptual identification (the triage set).

This is a **surfacing report for triage, not an auto-gate**: whether a trivial-statement claim *over-states*
its content is a judgment (an honest value identity like `…equals-the-squared-amplitude` is fine; a
conceptual `…is-the-born-rule-modulus-squared` is the defect). And recall is partial — defeq-equality
catches `rfl`-with-defeq-sides cases but misses normalization-bridged ones (e.g. `1/σ²` vs `(σ²)⁻¹`, which
need `one_div`); a proof-text grep complements it. It reuses the tested `isDefinitionalRestatement` and
`Zil.Datalog.declarationAttachments`.
-/

@[expose] public section

namespace Physlib.Meta.ZilDefinitionalOverclaimReport

open Lean Elab Command Meta Zil.Datalog

/-- Keywords marking a claim as a conceptual identification rather than a bare value/definitional identity —
the higher-risk shape when the proof is a definitional restatement. -/
meta def conceptualKeywords : List String :=
  ["is-the", "is-exactly", "is-precisely", "coincides", "born", "fisher", "quantum-potential",
   "modular", "spinor", "reconstructs", "is-a-", "hamiltonian"]

/-- A claim token reads as a conceptual identification (heuristic infix match). -/
meta def isConceptualClaim (claim : String) : Bool :=
  conceptualKeywords.any fun kw => decide (1 < (claim.splitOn kw).length)

/-- The claim token of a `claim:…` graph value, else `none`. -/
meta def claimToken? : Value → Option String
  | .symbol s => if "claim:".isPrefixOf s then some (s.stripPrefix "claim:") else none
  | _ => none

/-- Whether a declaration's statement is a definitional restatement — the two sides of the concluding
`=`/`↔` are already defeq (provable by `rfl`). Same test as `AxiomWhitelistCheck.isDefinitionalRestatement`,
inlined to avoid a cross-module meta reference. -/
meta def isDefRestatement (declType : Expr) : MetaM Bool :=
  forallTelescope declType fun _ concl => do
    match concl.eq? with
    | some (_, lhs, rhs) => isDefEq lhs rhs
    | none =>
      match concl.iff? with
      | some (lhs, rhs) => isDefEq lhs rhs
      | none => return false

/-- Run the definitional-restatement test over every ZIL-formalized theorem; count the trivial ones and
list the subset carrying a conceptual claim (the triage set). -/
meta def reportMessage : CommandElabM MessageData := do
  let env ← getEnv
  let mut processed : NameSet := {}
  let mut trivialCount := 0
  let mut flagged : List (Name × String) := []
  for att in (declarationAttachments env).toList do
    if att.atom.relation == "formalizes" && att.declarationKind == "theorem"
        && !processed.contains att.declaration then
      match claimToken? att.atom.subject, env.find? att.declaration with
      | some claim, some info =>
        processed := processed.insert att.declaration
        let isTrivial ← liftTermElabM (isDefRestatement info.type)
        if isTrivial then
          trivialCount := trivialCount + 1
          if isConceptualClaim claim then
            flagged := (att.declaration, claim) :: flagged
      | _, _ => pure ()
  let mut s := s!"zil definitional-overclaim report: {trivialCount} ZIL-formalized theorems have a \
    definitionally-trivial statement (rfl-provable); {flagged.length} of those carry a conceptual claim \
    (triage — verify the claim against what the proof establishes):\n"
  for (d, c) in flagged.reverse do
    s := s ++ s!"        · {d}\n            claim= {c}\n"
  return m!"{s}"

/-- **`#zil_definitional_overclaim_report`** — surface every ZIL-formalized theorem with a definitionally
trivial statement, flagging the conceptual-claim subset for over-claim triage. -/
syntax (name := zilDefOverclaimCmd) "#zil_definitional_overclaim_report" : command

@[command_elab zilDefOverclaimCmd]
meta def elabZilDefOverclaim : CommandElab := fun _ => do
  logInfo (← reportMessage)

end Physlib.Meta.ZilDefinitionalOverclaimReport

end

/- Demonstration on the fixed Madelung pair: the value lemma is a (now honestly-labelled) definitional
restatement; the genuine Born-rule theorem `ρ = ‖ψ‖²` is substantive. -/
#physlib_vacuity_report Physlib.QuantumMechanics.Schrodinger.madelung_born_rule
#physlib_vacuity_report Physlib.QuantumMechanics.Schrodinger.madelungDensity_eq_wavefunctionNormSq

#zil_definitional_overclaim_report
