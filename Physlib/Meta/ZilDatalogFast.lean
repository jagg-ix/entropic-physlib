/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Zil.Datalog.Basic
public import Zil.Datalog.Eval

/-!
# An indexed, saturating evaluator for the ZIL Datalog core

`Zil.Datalog.deriveProgram` is the reference evaluator: small, obviously correct, and quadratic in
several places at once. On the repo-wide graph (~11800 edges) it no longer finishes — a full
`Physlib.Meta.ZilGraphAuditFull` build was killed after 5h32m without emitting the audit.

Three costs compound in the reference engine:

* **No saturation check.** `deriveRuleSet` recurses on `fuel` unconditionally, so a rule set that
  reaches its fixpoint after two rounds still pays for all eight, each a full pass over every fact.
* **Quadratic dedup.** Every round rebuilds the whole accumulated set with `List.eraseDups`,
  which is `O(n²)` structural comparisons over atoms containing strings — and it re-dedups facts
  that were already unique in the previous round.
* **Unindexed joins.** `matchPattern` scans *every* fact for every pattern and every candidate
  substitution. For a self-join like `dependsOnDecl(D,F) :- dependsOnDecl(D,E), dependsOnDecl(E,F)`
  that is `O(m²)` per round in the size of the derived relation, which is where the audit actually
  disappears.

This module keeps the reference semantics and removes all three costs:

* stop as soon as a round adds nothing;
* deduplicate through a `Std.HashSet`, preserving first-occurrence order so results stay *equal as
  lists* to the reference engine, not merely equal as sets;
* index facts by relation, and by (relation, object) / (relation, subject), so a join probes only
  the atoms that can possibly unify.

The indexing is exactly semantics-preserving because `Zil.Datalog.unify` rejects immediately when
`pattern.relation != atom.relation`, and because each index bucket preserves the insertion order
of the fact list — so probing a bucket yields the same subsequence, in the same order, that
scanning every fact would have yielded.

The agreement is proved in general — same atoms, same order, for every program and fuel — by
`deriveProgramFast_eq` in `Physlib.Meta.ZilDatalogFastEquiv`; `Physlib.Meta.ZilDatalogFastCheck`
keeps evaluated `#guard` instances as smoke tests of the compiled code paths.
-/

@[expose] public section

open Zil.Datalog

namespace Physlib.Meta.ZilDatalogFast

/-! ### Hashing for the atom vocabulary -/

instance : Hashable Value where
  hash
    | .symbol v => mixHash 17 (hash v)
    | .string v => mixHash 19 (hash v)
    | .integer v => mixHash 23 (hash v)
    | .boolean v => mixHash 29 (hash v)

instance : Hashable Atom where
  hash a :=
    mixHash (hash a.object) (mixHash (hash a.relation) (mixHash (hash a.subject) (hash a.attrs)))

/-! ### Order-preserving deduplication

`List.eraseDups` keeps the first occurrence of each element and preserves order. This does the
same in one pass through a hash set, so every downstream result is *equal as a list* to the
reference engine's.
-/

/-- `List.eraseDups` for atoms, in `O(n)` expected time. -/
def dedupAtoms (as : List Atom) : List Atom :=
  (as.foldl (init := ((#[] : Array Atom), (∅ : Std.HashSet Atom))) fun acc a =>
      if acc.2.contains a then acc else (acc.1.push a, acc.2.insert a)).1.toList

/-! ### The fact index -/

/-- Facts grouped by relation, and by relation paired with a bound endpoint. Buckets keep the
order in which facts appear in the underlying list. -/
structure FactIndex where
  byRel : Std.HashMap String (Array Atom)
  byRelObject : Std.HashMap (String × Value) (Array Atom)
  byRelSubject : Std.HashMap (String × Value) (Array Atom)

def pushAt {κ : Type} [BEq κ] [Hashable κ]
    (m : Std.HashMap κ (Array Atom)) (key : κ) (a : Atom) : Std.HashMap κ (Array Atom) :=
  m.insert key ((m.getD key #[]).push a)

/-- Build the three indexes in a single pass. -/
def buildIndex (facts : List Atom) : FactIndex :=
  facts.foldl (init := { byRel := ∅, byRelObject := ∅, byRelSubject := ∅ }) fun idx a =>
    { byRel := pushAt idx.byRel a.relation a
      byRelObject := pushAt idx.byRelObject (a.relation, a.object) a
      byRelSubject := pushAt idx.byRelSubject (a.relation, a.subject) a }

/-- The value a pattern term already denotes under `substitution`, if any. -/
def resolveTerm (substitution : Substitution) : Term → Option Value
  | .value v => some v
  | .variable name => lookup name substitution

/-- The facts that could possibly unify with `pattern` under `substitution`: the narrowest index
bucket whose key is already determined. Falls back to the whole relation when both endpoints are
still free. -/
def candidates (index : FactIndex) (pattern : Pattern) (substitution : Substitution) : Array Atom :=
  match resolveTerm substitution pattern.object with
  | some v => index.byRelObject.getD (pattern.relation, v) #[]
  | none =>
    match resolveTerm substitution pattern.subject with
    | some v => index.byRelSubject.getD (pattern.relation, v) #[]
    | none => index.byRel.getD pattern.relation #[]

/-! ### The rule application pipeline, mirroring `Zil.Datalog` -/

/-- Indexed counterpart of `Zil.Datalog.matchPattern`. -/
def matchPatternIndexed (index : FactIndex) (pattern : Pattern)
    (substitution : Substitution) : List Substitution :=
  (candidates index pattern substitution).toList.filterMap fun atom =>
    unify pattern atom substitution

/-- Indexed counterpart of `Zil.Datalog.satisfyBody`. -/
def satisfyBodyIndexed (index : FactIndex) (body : List Pattern) : List Substitution :=
  body.foldl (init := [[]]) fun substitutions pattern =>
    substitutions.flatMap (matchPatternIndexed index pattern)

/-- Indexed counterpart of `Zil.Datalog.excludesPattern`. -/
def excludesPatternIndexed (index : FactIndex) (pattern : Pattern)
    (substitution : Substitution) : Bool :=
  !((candidates index pattern substitution).any fun atom =>
      (unify pattern atom substitution).isSome)

/-- Indexed counterpart of `Zil.Datalog.satisfyNegativeBody`. -/
def satisfyNegativeBodyIndexed (index : FactIndex) (body : List Pattern)
    (substitutions : List Substitution) : List Substitution :=
  body.foldl (init := substitutions) fun remaining pattern =>
    remaining.filter (excludesPatternIndexed index pattern)

/-- Indexed counterpart of `Zil.Datalog.applyRule`. -/
def applyRuleIndexed (index : FactIndex) (rule : Rule) : List Atom :=
  (satisfyNegativeBodyIndexed index rule.negativePatterns
    (satisfyBodyIndexed index rule.positiveBody)).filterMap (instantiate rule.head)

/-- One round of rule application over an already-deduplicated fact list. -/
def stepIndexed (rules : List Rule) (facts : List Atom) : List Atom :=
  let index := buildIndex facts
  dedupAtoms (facts ++ rules.flatMap (applyRuleIndexed index))

/-! ### Saturating drivers

The reference `deriveRuleSet`/`derive` burn their whole fuel budget even after reaching a fixpoint.
Because facts only ever grow and every intermediate list is deduplicated, "this round added
nothing" is exactly "the length did not change", so the fixpoint test is a length comparison.
-/

def saturate (rules : List Rule) : Nat → List Atom → List Atom
  | 0, facts => facts
  | fuel + 1, facts =>
    let next := stepIndexed rules facts
    if next.length == facts.length then next else saturate rules fuel next

/-- Indexed, early-exiting counterpart of `Zil.Datalog.deriveRuleSet`. -/
def deriveRuleSetFast (rules : List Rule) (fuel : Nat) (facts : List Atom) : List Atom :=
  saturate rules fuel (dedupAtoms facts)

/-- Indexed, early-exiting counterpart of `Zil.Datalog.derive`. -/
def deriveFast (program : Program) (fuel : Nat) : List Atom :=
  saturate program.rules fuel (dedupAtoms program.facts)

/-- Indexed, early-exiting counterpart of `Zil.Datalog.deriveStratified`. -/
def deriveStratifiedFast (program : Program) (fuel : Nat := 32) : List Atom :=
  (List.range (program.maxStratum + 1)).foldl (init := program.facts) fun facts stratum =>
    let rules := program.rules.filter fun rule => program.stratumOf rule.head.relation == stratum
    deriveRuleSetFast rules fuel facts

/-- Drop-in replacement for `Zil.Datalog.deriveProgram`.

Same stratification, same fuel semantics, same result list — including order — but indexed joins,
hash-set deduplication and an early exit on saturation. -/
def deriveProgramFast (program : Program) (fuel : Nat := 32) : List Atom :=
  if program.hasNegation then deriveStratifiedFast program fuel else deriveFast program fuel

end Physlib.Meta.ZilDatalogFast
