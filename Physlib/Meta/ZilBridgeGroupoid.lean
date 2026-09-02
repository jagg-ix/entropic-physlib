/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.ZilGraph
public import Physlib.Meta.ZilDatalogFast

/-!
# The bridge groupoid — composition and discovery as certified Datalog rules

`#zil_unify_diagram` computes, for a set of carrier definitions, the pairwise **bridge
constraints**: differences of multiplicative normal forms, valued in the free abelian group on
canonical binder names. Because the constraints are differences, every morphism is invertible and
composition telescopes exactly — the carriers and constraints form a **groupoid**, not merely a
directed graph. The diagram command exploits this operationally; this module states it as
*rules* over two relations and certifies the rules the way every other detector in
`Physlib.Meta.ZilGraph` is certified — by `decide` on samples that encode the real discovery
story.

The relations:

* `bridgeEdge(A, B)` — a dimensionally homogeneous bridge constraint exists between carriers
  `A` and `B` (the `#zil_unify_diagram` edge);
* `bridgeProven(A, B)` — some Physlib theorem connects `A` and `B` (the diagram's
  "connecting theorem" coverage).

The rules:

* **symmetry** (`bridgeProven.symm`, `bridgeEdge.symm`) — invertibility of the groupoid's
  morphisms: a constraint read right-to-left is the negated group element, and a connecting
  theorem connects both ways;
* **composition** (`provenPath.base`, `provenPath.trans`) — the transitive closure of proven
  connections: `provenPath(A, C)` says the constraint `A ⟶ C` is *derivable by composing
  proven bridges*, even when no direct theorem states it;
* **discovery** (`underivedComposite`) — the offensive read: an edge that exists
  (`bridgeEdge`), is reachable through proven flanks (`provenPath`), but has no direct
  connecting theorem. This is precisely the shape in which
  `hawking_eq_comptonTemperature_iff` was found: both flanks through the Unruh carrier were
  proven before the direct edge was.

The samples below encode that very history: the open triangle (Hawking edge unproven) makes
`underivedComposite` fire on exactly the Hawking–Compton edge, and the closed triangle — the
repository's current state — suppresses it. The negative discipline (`no bridgeEdge(A, A)`
facts are ever asserted) keeps the reflexive paths `provenPath(A, A)` harmless: the discovery
rule joins against `bridgeEdge`, so identity loops never surface as findings.

The standing, build-enforced form for the real five-carrier temperature diagram lives in
`Physlib.Meta.TemperaturePentagonGate`.
-/

open Zil.Datalog
open Physlib.Meta.ZilGraph
open Physlib.Meta.ZilDatalogFast

@[expose] public section

namespace Physlib.Meta.ZilBridgeGroupoid

/-! ### The rules -/

/-- Symmetry of proven connections: the groupoid's morphisms are invertible, and a connecting
theorem mentioning both carriers connects them in either direction. -/
def bridgeProvenSymmRule : Rule :=
  { name := "bridgeProven.symm"
    head := pat (.variable "b") "bridgeProven" (.variable "a")
    literals := [.positive (pat (.variable "a") "bridgeProven" (.variable "b"))] }

/-- Symmetry of edges: a bridge constraint read right-to-left is the negated group element,
still a homogeneous constraint. -/
def bridgeEdgeSymmRule : Rule :=
  { name := "bridgeEdge.symm"
    head := pat (.variable "b") "bridgeEdge" (.variable "a")
    literals := [.positive (pat (.variable "a") "bridgeEdge" (.variable "b"))] }

/-- Base of the composition closure: a proven bridge is a proven path. -/
def provenPathBaseRule : Rule :=
  { name := "provenPath.base"
    head := pat (.variable "a") "provenPath" (.variable "b")
    literals := [.positive (pat (.variable "a") "bridgeProven" (.variable "b"))] }

/-- Composition: proven paths compose. In the free abelian group the composite constraint is
the telescoping sum, so derivability is inherited along the path. -/
def provenPathTransRule : Rule :=
  { name := "provenPath.trans"
    head := pat (.variable "a") "provenPath" (.variable "c")
    literals := [.positive (pat (.variable "a") "provenPath" (.variable "b")),
                 .positive (pat (.variable "b") "provenPath" (.variable "c"))] }

/-- **The discovery rule.** An edge that exists, is reachable by composing proven bridges, and
has no direct connecting theorem — the underived composite, the mechanized form of the pattern
that found the Hawking–Compton identity. Stratified negation against `bridgeProven`. -/
def underivedCompositeRule : Rule :=
  { name := "underivedComposite"
    head := pat (.variable "a") "underivedComposite" (.variable "b")
    literals := [.positive (pat (.variable "a") "bridgeEdge" (.variable "b")),
                 .positive (pat (.variable "a") "provenPath" (.variable "b")),
                 .negative (pat (.variable "a") "bridgeProven" (.variable "b"))] }

/-- The groupoid rule set, in evaluation order. -/
def bridgeGroupoidRules : List Rule :=
  [bridgeProvenSymmRule, bridgeEdgeSymmRule, provenPathBaseRule, provenPathTransRule,
   underivedCompositeRule]

/-! ### Certification samples — the temperature-triangle history

Objects `U` (Unruh), `K` (Compton), `H` (Hawking). Historically: `U–K` and `U–H` were proven,
the `K–H` edge existed as a homogeneous constraint (`m·c³ ≐ κ·ℏ`) with no direct theorem —
until the diagram tool surfaced it and `hawking_eq_comptonTemperature_iff` closed it. -/

/-- An undirected pair of groupoid facts for relation `rel` between `a` and `b`. -/
def edge (rel a b : String) : Atom :=
  { object := .symbol a, relation := rel, subject := .symbol b }

/-- The open triangle: both flanks through `U` proven, the `K–H` edge present but unproven. -/
def openTriangle : Program :=
  { facts := [edge "bridgeEdge" "U" "K", edge "bridgeEdge" "U" "H", edge "bridgeEdge" "K" "H",
              edge "bridgeProven" "U" "K", edge "bridgeProven" "U" "H"]
    rules := bridgeGroupoidRules }

/-- The closed triangle — the repository's current state: all three edges proven. -/
def closedTriangle : Program :=
  { facts := openTriangle.facts ++ [edge "bridgeProven" "K" "H"]
    rules := bridgeGroupoidRules }

-- The sample certifications run through the List-based reference engine `deriveProgram` —
-- the kernel reduces it directly, which is exactly what it exists for; the indexed
-- `deriveProgramFast` (used at repo scale) is pinned to it by the `#guard`s in
-- `Physlib.Meta.ZilDatalogFastCheck`.
set_option maxRecDepth 16000

/-- **The discovery rule fires on the open triangle**, on exactly the historically missing
edge: `K–H` is reachable through the proven flanks but not directly proven. -/
theorem underivedComposite_fires_on_open_triangle :
    edge "underivedComposite" "K" "H" ∈ deriveProgram openTriangle 6 := by decide

/-- **Proven flanks alone are not flagged** — the `U–K` edge is directly proven, so it is not
an underived composite, in the open triangle where the rule does fire elsewhere. -/
theorem underivedComposite_suppressed_on_proven_edge :
    edge "underivedComposite" "U" "K" ∉ deriveProgram openTriangle 6 := by decide

/-- **Closing the diagram silences the rule**: once `hawking_eq_comptonTemperature_iff` exists,
the `K–H` finding disappears. -/
theorem underivedComposite_suppressed_on_closed_triangle :
    edge "underivedComposite" "K" "H" ∉ deriveProgram closedTriangle 6 := by decide

/-- **Identity loops never surface**: `provenPath(U, U)` is derivable by symmetry and
composition, but no `bridgeEdge(U, U)` fact exists, so the discovery join stays empty on the
diagonal. -/
theorem underivedComposite_ignores_identity_loops :
    edge "underivedComposite" "U" "U" ∉ deriveProgram openTriangle 6 := by decide

/-- **Invertibility is real**: the reversed flank `K ⟶ U` is derivable although only
`U ⟶ K` was asserted — the groupoid symmetry rule at work. -/
theorem provenPath_symm_derivable :
    edge "provenPath" "K" "U" ∈ deriveProgram openTriangle 6 := by decide

end Physlib.Meta.ZilBridgeGroupoid
