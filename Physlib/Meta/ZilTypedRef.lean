/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Zil.Datalog.Basic
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil.Datalog.Attach

/-!
# Typed object references for the physlib knowledge graph (Zanzibar-style)

The ZIL graph edges physlib emits are already Zanzibar tuples `object#relation@subject`
(`Zil.Datalog.Atom`). But the object/subject are flat `Value.symbol "claim:…"` / `"lean:…"` strings,
and downstream code dispatches on them by `String.startsWith "lean:"` — the object *type* is a `:`-prefix
baked into a string, not a symbol.

This module is the first cut of the typed-reference layer: it replaces the string prefix with an actual
namespace symbol. An object reference is `Ref = ⟨τ : ObjType, id : String⟩` — the Zanzibar `type:id`
shape as structured data — with `ObjType` an explicit enum over the namespaces the repo actually uses:
reference targets (`claim`, `decl` = Lean declaration, `source`/`theorem`/`mathlib`/`book` = citations),
physics objects (`assumption`, `constant`, `model`, `definition`, `object`, `value`, `input`, `law`,
`measurement`), and epistemic-caveat kinds (`epistemic`, `scope`, `premise`).

`Ref.ofValue?` parses a raw graph value into a typed ref (matching the prefix against a known
namespace); `Ref.render` / `Ref.toValue` render it back. Type dispatch becomes a pattern match on `τ`
rather than a `startsWith`, and an unknown prefix becomes a definite `none` rather than a silent miss.

`#zil_typed_graph_report` runs the parser over the whole extracted graph and reports coverage: how many
object/subject values type into each namespace, and which values carry an unknown prefix — the
build-time demonstration on the real ~7300-object graph.
-/

@[expose] public section

namespace Physlib.Meta.ZilTypedRef

open Zil.Datalog

/-- The object namespaces of the physlib knowledge graph — the Zanzibar object types.

Three families: reference targets (`claim`, `decl` = a Lean declaration, `source`/`theorem`/`mathlib`/
`book` = external citations), physics objects (`assumption`, `constant`, `model`, `definition`,
`object`, `value` = a measured/experimental number, `input` = a standard-physics postulate, `law`,
`measurement`), and epistemic-caveat kinds (`epistemic`, `scope`, `premise`). -/
inductive ObjType
  | claim
  | decl
  | source
  | assumption
  | constant
  | model
  | definition
  | object
  | epistemic
  | scope
  | premise
  | value
  | input
  | «theorem»
  | mathlib
  | law
  | measurement
  | book
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The canonical string prefix of each namespace as it appears in the raw graph values. -/
def ObjType.nsPrefix : ObjType → String
  | .claim => "claim"
  | .decl => "lean"
  | .source => "paper"
  | .assumption => "assumption"
  | .constant => "constant"
  | .model => "model"
  | .definition => "definition"
  | .object => "object"
  | .epistemic => "epistemic"
  | .scope => "scope"
  | .premise => "premise"
  | .value => "value"
  | .input => "input"
  | .«theorem» => "theorem"
  | .mathlib => "mathlib"
  | .law => "law"
  | .measurement => "measurement"
  | .book => "book"

/-- The full list of namespaces, for exhaustiveness and lookup. -/
def ObjType.all : List ObjType :=
  [.claim, .decl, .source, .assumption, .constant, .model, .definition, .object,
   .epistemic, .scope, .premise, .value, .input, .«theorem», .mathlib, .law, .measurement, .book]

theorem ObjType.mem_all (τ : ObjType) : τ ∈ ObjType.all := by
  cases τ <;> simp [ObjType.all]

/-- The namespace prefixes are pairwise distinct, so the prefix determines the type. -/
theorem ObjType.nsPrefix_injective {a b : ObjType} (h : a.nsPrefix = b.nsPrefix) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-- Recover a namespace from its prefix string. -/
def ObjType.ofPrefix? (p : String) : Option ObjType :=
  ObjType.all.find? (fun τ => τ.nsPrefix == p)

/-- Every namespace is recovered from its own prefix. -/
theorem ObjType.ofPrefix?_nsPrefix (τ : ObjType) : ObjType.ofPrefix? τ.nsPrefix = some τ := by
  cases τ <;> decide

/-- An unrecognised prefix maps to no namespace. -/
theorem ObjType.ofPrefix?_unknown : ObjType.ofPrefix? "widget" = none := by decide

/-- A **typed object reference** `⟨τ, id⟩` — the Zanzibar `type:id` shape as structured data,
replacing the flat `Value.symbol "type:id"` string. -/
structure Ref where
  τ : ObjType
  id : String
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Render a typed ref to its canonical `"type:id"` string form. -/
def Ref.render (r : Ref) : String := r.τ.nsPrefix ++ ":" ++ r.id

/-- Render a typed ref back to a raw graph `Value`. -/
def Ref.toValue (r : Ref) : Value := .symbol r.render

/-- Parse a raw `"type:id"` string into a typed ref: split off the prefix before the first colon,
match it against a known namespace, and keep the remainder (rejoined) as the id. An unknown prefix or
a colon-free string yields `none`. -/
def parseRef? (s : String) : Option Ref :=
  match s.splitOn ":" with
  | pre :: rest@(_ :: _) => (ObjType.ofPrefix? pre).map (fun τ => ⟨τ, ":".intercalate rest⟩)
  | _ => none

/-- Parse a raw graph value into a typed ref (symbols and strings only). -/
def Ref.ofValue? : Value → Option Ref
  | .symbol s => parseRef? s
  | .string s => parseRef? s
  | _ => none

/-! ## Parser structure

Whole-string parses (`splitOn` over long claim ids) are not kernel-reducible, so they are exercised on
the real graph by `#zil_typed_graph_report` rather than proved by `decide`. What is proved here is the
correctness core the parser rests on: prefixes are distinct and each recovers its namespace
(`ObjType.ofPrefix?_nsPrefix`), an unknown prefix is rejected (`ObjType.ofPrefix?_unknown`), and only
symbol/string values can be references. -/

/-- Integer values are not typed references. -/
theorem parse_integer_rejected (i : Int) : Ref.ofValue? (.integer i) = none := rfl

/-- Boolean values are not typed references. -/
theorem parse_boolean_rejected (b : Bool) : Ref.ofValue? (.boolean b) = none := rfl

/-- `render` is a left inverse of the projection to the namespace prefix: the rendered string starts
with the namespace's prefix followed by a colon. -/
theorem Ref.render_eq (r : Ref) : r.render = r.τ.nsPrefix ++ ":" ++ r.id := rfl

/-- A fully-typed graph edge: both endpoints resolved to typed references where possible. The
relation stays a string (relations are the next layer to type). -/
structure TypedEdge where
  object : Option Ref
  relation : String
  subject : Option Ref

/-- Type both endpoints of a raw atom into the typed-reference layer. -/
def TypedEdge.ofAtom (a : Atom) : TypedEdge :=
  { object := Ref.ofValue? a.object, relation := a.relation, subject := Ref.ofValue? a.subject }

end Physlib.Meta.ZilTypedRef

end

open Physlib.Meta.ZilTypedRef in
#physlib_axiom_clean_all [
  ObjType.mem_all,
  ObjType.nsPrefix_injective,
  ObjType.ofPrefix?_nsPrefix ]

open Physlib.Meta.ZilTypedRef in
#physlib_non_vacuous_all [
  ObjType.mem_all,
  ObjType.nsPrefix_injective,
  ObjType.ofPrefix?_nsPrefix ]
