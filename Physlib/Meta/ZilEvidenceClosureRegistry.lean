/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE
meta import Zil

/-!
# ZIL evidence closure registry

This module gives the CAT/EPT formalization a Lean-native registry for evidence
lifecycle state. It prevents three recurrent errors:

* treating a named Lean declaration as if it had already been kernel checked;
* leaving an omission marked open after a stronger theorem has replaced it; and
* hiding remaining analytic work inside free-form caveat text.

The registry is declarative. Lean remains proof authority; standalone ZIL graphs
consume the same identifiers for orchestration and queries.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Meta.ZilEvidenceClosureRegistry

inductive ClaimState where
  | implemented
  | conditional
  | rejected
  | open
  deriving DecidableEq, BEq, Repr

inductive VerificationState where
  | sourceDeclared
  | pendingKernelCheck
  | kernelChecked
  | notApplicable
  deriving DecidableEq, BEq, Repr

structure EvidenceRecord where
  id : String
  state : ClaimState
  verification : VerificationState
  witness : Option String
  requires : List String
  dischargedBy : List String
  supersedes : List String
  deriving DecidableEq, Repr

def implemented (id witness : String)
    (requires : List String := []) : EvidenceRecord where
  id := id
  state := .implemented
  verification := .pendingKernelCheck
  witness := some witness
  requires := requires
  dischargedBy := []
  supersedes := []

def rejected (id resolution : String)
    (supersedes : List String := []) : EvidenceRecord where
  id := id
  state := .rejected
  verification := .notApplicable
  witness := none
  requires := []
  dischargedBy := [resolution]
  supersedes := supersedes

def obligation (id : String) (requires : List String := []) : EvidenceRecord where
  id := id
  state := .open
  verification := .notApplicable
  witness := none
  requires := requires
  dischargedBy := []
  supersedes := []

/-- Canonical CAT/EPT closure records already present on
`entropic-physlib-linear-full`, followed by the genuinely remaining analytic
obligations. -/
def catEptClosureRegistry : List EvidenceRecord := [
  implemented
    "claim:hartree-self-energy-continuity-from-lsix-fifths"
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianSelfEnergy_tendsto_of_lsixFifths"
    ["obligation:localized-strong-lsix-fifths-born-convergence"],
  implemented
    "claim:h-one-hartree-interaction-continuity"
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths"
    ["claim:hartree-self-energy-continuity-from-lsix-fifths"],
  implemented
    "claim:energy-split-no-loss-and-strong-h-one-closure"
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit"
    ["claim:h-one-hartree-interaction-continuity"],
  implemented
    "claim:born-normalization-closes-after-strong-h-one-convergence"
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneLTwoNormalized_of_tendsto"
    ["claim:energy-split-no-loss-and-strong-h-one-closure"],
  implemented
    "claim:born-first-moment-energy-minimizer"
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_energyMinimizer"
    ["obligation:recentered-first-moment-bound",
      "obligation:localized-strong-lsix-fifths-born-convergence"],
  implemented
    "claim:compact-complete-minimizing-orbit"
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure"
    ["claim:born-first-moment-energy-minimizer"],
  implemented
    "claim:born-law-minimizing-orbit-stability"
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_minimizingOrbit_uniformlyStable"
    ["claim:compact-complete-minimizing-orbit",
      "obligation:global-mass-energy-preserving-flow"],
  rejected
    "omission:unit-mass-sphere-is-globally-weakly-closed"
    "counterexample:orthonormal-unit-mass-sequence-weakly-converges-to-zero"
    ["claim:normalized-mass-weak-closure-remains-open"],
  rejected
    "omission:attractive-translation-invariant-energy-is-unconditionally-weakly-lsc"
    "counterexample:negative-energy-translates-weakly-converge-to-zero"
    ["claim:target-energy-unconditional-weak-lower-semicontinuity"],
  rejected
    "omission:spatial-schrodinger-generator-is-bounded-h-one-to-h-one"
    "fourier-audit:laplacian-h-one-to-h-one-ratio-grows-like-frequency-squared"
    ["claim:concrete-generator-h-one-to-h-one-c-one"],
  obligation
    "obligation:localized-strong-lsix-fifths-born-convergence",
  obligation
    "obligation:recentered-first-moment-bound",
  obligation
    "obligation:concrete-energy-critical-duhamel-strichartz-flow"
    ["interface:weak-generator-h-one-to-h-minus-one"],
  obligation
    "obligation:global-mass-energy-preserving-flow"
    ["obligation:concrete-energy-critical-duhamel-strichartz-flow"],
  obligation
    "obligation:analytic-identification-of-m9-69-with-minimizing-orbit"
    ["claim:compact-complete-minimizing-orbit"]
]

def registryIds : List String := catEptClosureRegistry.map (·.id)

def implementedWitnessesPresent : Bool :=
  catEptClosureRegistry.all fun record =>
    if record.state == .implemented then record.witness.isSome else true

def rejectedClaimsHaveResolution : Bool :=
  catEptClosureRegistry.all fun record =>
    if record.state == .rejected then !record.dischargedBy.isEmpty else true

def openObligationsHaveNoProofWitness : Bool :=
  catEptClosureRegistry.all fun record =>
    if record.state == .open then record.witness.isNone else true

def requiredClosureIds : List String := [
  "claim:hartree-self-energy-continuity-from-lsix-fifths",
  "claim:energy-split-no-loss-and-strong-h-one-closure",
  "claim:born-normalization-closes-after-strong-h-one-convergence",
  "claim:born-first-moment-energy-minimizer",
  "claim:compact-complete-minimizing-orbit",
  "claim:born-law-minimizing-orbit-stability"
]

def requiredClosureCoverage : Bool :=
  requiredClosureIds.all fun id => registryIds.contains id

theorem registry_ids_nodup : registryIds.Nodup := by
  decide

theorem implemented_records_have_witness : implementedWitnessesPresent = true := by
  decide

theorem rejected_claims_have_resolution : rejectedClaimsHaveResolution = true := by
  decide

theorem open_obligations_have_no_proof_witness :
    openObligationsHaveNoProofWitness = true := by
  decide

theorem required_closure_coverage : requiredClosureCoverage = true := by
  decide

end Physlib.Meta.ZilEvidenceClosureRegistry

/- ZIL-BEGIN -/

zil attach Physlib.Meta.ZilEvidenceClosureRegistry.registry_ids_nodup where
  formalizes @ "claim:the-cat-ept-zil-evidence-registry-has-no-duplicate-identifiers"

zil attach Physlib.Meta.ZilEvidenceClosureRegistry.implemented_records_have_witness where
  formalizes @ "claim:every-registry-record-marked-implemented-names-a-lean-witness",
  caveat @ "claim:a-named-witness-remains-pending-kernel-check-until-the-lean-audit-builds"

zil attach Physlib.Meta.ZilEvidenceClosureRegistry.rejected_claims_have_resolution where
  formalizes @ "claim:every-rejected-omission-has-a-structured-counterexample-or-resolution-edge"

zil attach Physlib.Meta.ZilEvidenceClosureRegistry.open_obligations_have_no_proof_witness where
  formalizes @ "claim:open-analytic-obligations-cannot-be-misreported-as-implemented-by-the-registry"

zil attach Physlib.Meta.ZilEvidenceClosureRegistry.required_closure_coverage where
  formalizes @ "claim:the-registry-covers-the-live-hartree-no-loss-normalization-minimizer-compactness-and-orbital-stability-chain"

zil_file_contract physlib.meta.zilEvidenceClosureRegistry where
  promises "A Lean-native evidence lifecycle registry with unique identifiers, structured theorem witnesses, explicit rejected omissions, discharge links, and non-promotable open analytic obligations."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Meta.ZilEvidenceClosureRegistry.catEptClosureRegistry"]
  forbids_substitutes ["promoting pending-kernel-check witnesses to verified evidence",
    "burying open analytic obligations in prose caveats"]
  witnessed_by [
    Physlib.Meta.ZilEvidenceClosureRegistry.registry_ids_nodup,
    Physlib.Meta.ZilEvidenceClosureRegistry.implemented_records_have_witness,
    Physlib.Meta.ZilEvidenceClosureRegistry.rejected_claims_have_resolution,
    Physlib.Meta.ZilEvidenceClosureRegistry.open_obligations_have_no_proof_witness,
    Physlib.Meta.ZilEvidenceClosureRegistry.required_closure_coverage ]

/- ZIL-END -/
