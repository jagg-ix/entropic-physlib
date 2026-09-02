/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Zil.Horn
public meta import Zil.Horn
public meta import Zil.Datalog.HornGrounding
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics

/-!
# Certified grounding of a ZIL formalization contract (Horn proof of concept)

The `#zil_formalization_lint` on a `zil_file_contract` reports a *coverage
percentage*: how many of the promised objects carry a classified witness.  It
counts; it does not prove that the transitive support of a `contract_status
satisfied` claim actually bottoms out.  This module is a proof of concept that
the new `Zil.Horn` (HORC) definite-Horn layer supplies the missing piece: a
kernel-checkable **grounding certificate**.

We take the real dependency graph of the contract
`physlib.einsteinEntanglementDynamics` (in
`QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics`) — its four
attached theorems, the claims they `formalize`, the source each claim is
`supported_by`, and the single object the contract `requires` — and encode it as
a definite-Horn program.  A single SLD query, `groundedContract(...)`, resolves
exactly when every witnessed claim reaches an established source and the required
object is provided.  `horn_certify` accepts the answer only after independent
proof-tree replay, and `solveCertifiedDepth_entails` turns that answer into a
`Zil.Horn.Entails` derivation of the grounding goal.

The check has teeth: the same program with the required-object fact removed
yields no certified solution (`broken_grounding_fails`), so grounding is a real
obligation and not a tautology.

**Trust note.**  `horn_certify` discharges the bounded `HasCertifiedSolution`
proposition by `native_decide`, so this module depends on the compiler-reduction
axiom `Lean.ofReduceBool` — the documented trust boundary of the executable Horn
tactics.  The *semantic* content (`solveCertifiedDepth_entails`) is an ordinary
kernel-checked theorem; only the "there exists a certified answer" step is
evaluated natively.
-/

@[expose] public section

namespace Physlib.Meta.EinsteinEntanglementDynamicsGrounding

open Zil.Horn

/-- The dependency graph of `physlib.einsteinEntanglementDynamics`, written in the
HORC surface language.  Uppercase names are variables; the lowercase names mirror
the contract's theorems (`witnesses`), its `supported_by` sources (`cites`), its
established base source and provided `requires_object` (`established`/`provides`),
and the two grounding rules. -/
def contractGraphSource : String :=
  "% witnesses(Theorem, Claim): each attached theorem formalizes a claim\n" ++
  "witnesses(ads3LeadingEntropy_firstLaw, fgFirstLaw).\n" ++
  "witnesses(rtAreaEntropy_firstOrderVariation, rtFirstOrder).\n" ++
  "witnesses(ads3EntropyFourierKernel_radialEquation, radialEquation).\n" ++
  "witnesses(ads3EinsteinMode_induces_entropyDynamics, einsteinInduces).\n" ++
  "% cites(Claim, Source): the supported_by edge\n" ++
  "cites(fgFirstLaw, nozaki1304).\n" ++
  "cites(rtFirstOrder, nozaki1304).\n" ++
  "cites(radialEquation, nozaki1304).\n" ++
  "cites(einsteinInduces, nozaki1304).\n" ++
  "% established base sources and provided required objects\n" ++
  "established(nozaki1304).\n" ++
  "provides(rtAreaEntropy).\n" ++
  "% a claim is grounded when a theorem witnesses it and its cited source is established\n" ++
  "groundedClaim(C) :- witnesses(T, C), cites(C, S), established(S).\n" ++
  "% the contract is grounded when its required object is provided and every claim is grounded\n" ++
  "groundedContract(einsteinEntanglementDynamics) :- provides(rtAreaEntropy), " ++
    "groundedClaim(fgFirstLaw), groundedClaim(rtFirstOrder), " ++
    "groundedClaim(radialEquation), groundedClaim(einsteinInduces).\n"

/-- The parsed contract-graph program (empty on a parse error, which the query
would then fail to ground). -/
def contractGraph : Program :=
  (Zil.Horn.Parser.parseText contractGraphSource).toOption.getD []

/-- The grounding query: is the contract grounded? -/
def groundingQuery : List Atom :=
  (Zil.Horn.Parser.parseGoalsText "groundedContract(einsteinEntanglementDynamics).").toOption.getD []

/-- The HORC source parses (the encoding is well-formed). -/
theorem contractGraph_parses :
    (Zil.Horn.Parser.parseText contractGraphSource).toOption.isSome = true := by
  native_decide

/-- **The grounding certificate.**  Bounded SLD search, followed by independent
proof-tree replay, finds and certifies a derivation of
`groundedContract(einsteinEntanglementDynamics)`: every witnessed claim reaches
the established source and the required object is provided. -/
theorem einstein_contract_grounded :
    HasCertifiedSolution contractGraph groundingQuery 64 := by
  horn_certify

/-- **Semantic grounding.**  Any certified answer entails the grounding goal as a
definite-clause consequence of the graph — an ordinary kernel-checked theorem,
independent of the native search. -/
theorem einstein_grounding_entails {sol : Solution}
    (member : sol ∈ (solveCertifiedDepth contractGraph groundingQuery 64).solutions) :
    ∀ goal ∈ groundingQuery, Entails contractGraph (goal.substitute sol.substitution) :=
  solveCertifiedDepth_entails member

/-- The contract graph with the `provides(rtAreaEntropy)` fact deleted: the
`requires_object` obligation is now unmet. -/
def brokenGraph : Program :=
  contractGraph.filter fun clause => clause.head.predicate ≠ "provides"

/-- **Teeth.**  With the required object no longer provided, no certified
grounding exists — the check is a real obligation, not a tautology. -/
theorem broken_grounding_fails :
    ¬ HasCertifiedSolution brokenGraph groundingQuery 64 := by
  unfold HasCertifiedSolution
  native_decide

-- Number of certified grounding answers (positive graph): expect at least one.
#eval (solveCertifiedDepth contractGraph groundingQuery 64).solutions.length

-- Certified answers after deleting the required-object fact: expect zero.
#eval (solveCertifiedDepth brokenGraph groundingQuery 64).solutions.length

end Physlib.Meta.EinsteinEntanglementDynamicsGrounding

/-! ## The same grounding, extracted from the live contract (no hand transcription)

`#zil_horn_grounding` reads the `physlib.einsteinEntanglementDynamics` file
contract straight from the `Zil.Datalog` environment extension, builds the Horn
graph from its actual `requires_objects` / `witnessed_by` fields, and certifies
`grounded(...)` by replay — so this verdict tracks the real contract, not the
`contractGraphSource` copy above. -/

#zil_horn_grounding physlib.einsteinEntanglementDynamics
