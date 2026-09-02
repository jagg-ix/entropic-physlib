/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow
public import Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
meta import Zil

/-!
# Constructed flow and identified-branch adapters

The live repository already contains the complete `H¹(ℝ³)` Bessel-energy
carrier, the genuine infinite-dimensional free Schrödinger group, the corrected
weak/mild cubic--quintic interfaces, the conservative-flow stability theorem,
and the identified-branch structure. This module supplies the small adapters
needed to use those results together rather than reporting them as unavailable.

* `freeHOneFlow` is the exact free Schrödinger group on the complete `H¹`
  energy coordinate. It has identity, composition, norm conservation, and
  strong recovery at zero time.
* `identifiedTargetBranchCertificateOfMinimizer` turns an actual member of the
  minimizing orbit into the repository's identified-branch certificate.
* `exists_identifiedStableMinimizingBranch` selects such a branch from every
  global conservative Born mild-flow certificate and retains compactness and
  uniform orbital stability.

The construction does not silently manufacture a concrete nonlinear target
flow. The global conservative certificate still records the target flow and its
invariants explicitly. The point here is that the free group, stability
composition, and branch-identification constructors are already available.
-/

set_option autoImplicit false

open Filter Topology
open Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates

structure HOneStrongUnitaryGroupCertificate where
  flow : ℝ → EuclideanHOneThree → EuclideanHOneThree
  flow_zero : ∀ u, flow 0 u = u
  flow_add : ∀ s t u, flow (s + t) u = flow s (flow t u)
  flow_norm : ∀ t u, ‖flow t u‖ = ‖u‖
  flow_tendsto_zero : ∀ u, Tendsto (fun t => flow t u) (𝓝 0) (𝓝 u)

noncomputable def freeHOneFlow
    (t : ℝ) (u : EuclideanHOneThree) : EuclideanHOneThree :=
  freeSchrodingerMultiplier t u

@[simp] lemma freeHOneFlow_zero (u : EuclideanHOneThree) :
    freeHOneFlow 0 u = u := by
  exact freeSchrodingerMultiplier_zero_time u

lemma freeHOneFlow_add (s t : ℝ) (u : EuclideanHOneThree) :
    freeHOneFlow (s + t) u = freeHOneFlow s (freeHOneFlow t u) := by
  exact freeSchrodingerMultiplier_add s t u

@[simp] lemma norm_freeHOneFlow (t : ℝ) (u : EuclideanHOneThree) :
    ‖freeHOneFlow t u‖ = ‖u‖ := by
  exact norm_freeSchrodingerMultiplier t u

lemma freeHOneFlow_tendsto_zero (u : EuclideanHOneThree) :
    Tendsto (fun t : ℝ => freeHOneFlow t u) (𝓝 0) (𝓝 u) := by
  exact freeSchrodingerMultiplier_tendsto_zero u

noncomputable def freeHOneStrongUnitaryGroupCertificate :
    HOneStrongUnitaryGroupCertificate where
  flow := freeHOneFlow
  flow_zero := freeHOneFlow_zero
  flow_add := freeHOneFlow_add
  flow_norm := norm_freeHOneFlow
  flow_tendsto_zero := freeHOneFlow_tendsto_zero

noncomputable def identifiedTargetBranchCertificateOfMinimizer
    (C : GlobalConservativeBornMildFlowCertificate)
    (branch : EuclideanHOneThree)
    (hbranch :
      branch ∈ HOneConstrainedEnergyMinimizers C.admissible C.energy) :
    IdentifiedTargetBranchCertificate where
  toGlobalConservativeBornMildFlowCertificate := C
  branch := branch
  branch_mem := hbranch.1
  branch_minimizes := hbranch.2

@[simp] lemma identifiedTargetBranchCertificateOfMinimizer_branch
    (C : GlobalConservativeBornMildFlowCertificate)
    (branch : EuclideanHOneThree)
    (hbranch :
      branch ∈ HOneConstrainedEnergyMinimizers C.admissible C.energy) :
    (identifiedTargetBranchCertificateOfMinimizer C branch hbranch).branch = branch :=
  rfl

theorem exists_identifiedTargetBranchCertificate
    (C : GlobalConservativeBornMildFlowCertificate) :
    ∃ B : IdentifiedTargetBranchCertificate,
      B.branch ∈ HOneConstrainedEnergyMinimizers B.admissible B.energy := by
  obtain ⟨_groundEnergy, hnonempty, _hcompact, _hchar, _hlower, _hstable⟩ :=
    exists_minimizingOrbit_uniformlyStable C
  obtain ⟨branch, hbranch⟩ := hnonempty
  let B := identifiedTargetBranchCertificateOfMinimizer C branch hbranch
  exact ⟨B, identifiedBranch_mem_minimizingOrbit B⟩

theorem exists_identifiedStableMinimizingBranch
    (C : GlobalConservativeBornMildFlowCertificate) :
    ∃ B : IdentifiedTargetBranchCertificate,
      B.branch ∈ HOneConstrainedEnergyMinimizers B.admissible B.energy ∧
      IsCompact (HOneConstrainedEnergyMinimizers B.admissible B.energy) ∧
      IsUniformlyOrbitallyStableOn B.weakFlow.flow B.admissible
        (HOneConstrainedEnergyMinimizers B.admissible B.energy) := by
  obtain ⟨_groundEnergy, hnonempty, hcompact, _hchar, _hlower, hstable⟩ :=
    exists_minimizingOrbit_uniformlyStable C
  obtain ⟨branch, hbranch⟩ := hnonempty
  let B := identifiedTargetBranchCertificateOfMinimizer C branch hbranch
  refine ⟨B, identifiedBranch_mem_minimizingOrbit B, ?_, ?_⟩
  · simpa [B, identifiedTargetBranchCertificateOfMinimizer] using hcompact
  · simpa [B, identifiedTargetBranchCertificateOfMinimizer] using hstable

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.freeHOneStrongUnitaryGroupCertificate where
  formalizes @ "claim:the-live-euclidean-free-schrodinger-evolution-is-an-exact-strongly-continuous-unitary-group-on-the-complete-h-one-bessel-energy-carrier"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.exists_identifiedTargetBranchCertificate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow.exists_minimizingOrbit_uniformlyStable",
  formalizes @ "claim:every-global-conservative-born-mild-flow-certificate-admits-a-selected-identified-minimizing-branch"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.exists_identifiedStableMinimizingBranch where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow.exists_minimizingOrbit_uniformlyStable",
  formalizes @ "claim:the-selected-identified-branch-belongs-to-a-compact-minimizing-orbit-that-is-uniformly-stable-under-the-supplied-global-conservative-flow",
  caveat @ "claim:the-theorem-consumes-the-explicit-global-conservative-target-flow-certificate-and-does-not-replace-its-construction"

zil_file_contract physlib.cubicQuinticConstructedCertificates where
  promises "The exact free H1 Schrödinger group, a named minimizing-branch constructor, and selection of an identified branch inside the compact uniformly stable minimizing orbit of every supplied global conservative Born mild-flow certificate."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.freeHOneFlow",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.identifiedTargetBranchCertificateOfMinimizer"]
  forbids_substitutes ["a concrete nonlinear target flow, which must still supply its explicit weak equation, admissibility, and conservation laws",
    "physical particle identity, calibration, or external validation claims"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.freeHOneStrongUnitaryGroupCertificate,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.exists_identifiedTargetBranchCertificate,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates.exists_identifiedStableMinimizingBranch ]

/- ZIL-END -/