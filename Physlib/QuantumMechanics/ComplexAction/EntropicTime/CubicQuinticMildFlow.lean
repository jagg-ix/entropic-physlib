/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability
meta import Zil

/-!
# Corrected weak/mild H¹ closure for the cubic--quintic target

The spatial Schrödinger generator is not modeled here as a bounded `H¹ → H¹`
vector field. Its Laplacian and energy-critical quintic term naturally live in
the dual/weak formulation, while an `H¹` evolution is supplied as a weak or
mild flow. The module therefore formalizes only mathematically valid bridges:

* a weak-generator flow interface tested against `H¹` vectors;
* Hartree plus local-interaction convergence;
* strong `H¹` no-loss and normalization closure from the live energy-split theorem;
* constrained minimizer and compact minimizing-orbit wrappers using the live
  Born first-moment machinery; and
* a global conservative flow certificate that instantiates the existing
  Cazenave--Lions minimizing-orbit theorem.

The concrete Duhamel/Strichartz construction, recentered first-moment estimate,
and model-specific interaction convergence remain explicit analytic inputs.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow

abbrev HOneWeakGenerator :=
  EuclideanHOneThree → EuclideanHOneThree →L[ℂ] ℂ

/-- Weak formulation of a global `H¹` evolution. The generator is evaluated
against an `H¹` test vector and therefore represents an `H⁻¹`-valued spatial
operator without falsely asserting a bounded `H¹ → H¹` Laplacian. -/
structure HOneWeakMildFlowCertificate where
  weakGenerator : HOneWeakGenerator
  flow : ℝ → EuclideanHOneThree → EuclideanHOneThree
  flow_zero : ∀ u, flow 0 u = u
  flow_add : ∀ s t u, flow (s + t) u = flow s (flow t u)
  orbit_continuous : ∀ u, Continuous (fun t => flow t u)
  weak_equation : ∀ u w t,
    HasDerivAt (fun s => inner ℂ (flow s u) w)
      (weakGenerator (flow t u) w) t

/-- The complete target interaction is the actual attractive Newton/Hartree
term plus a supplied local cubic--quintic interaction functional. -/
noncomputable def targetInteraction
    (G : ℝ) (localInteraction : EuclideanHOneThree → ℝ)
    (u : EuclideanHOneThree) : ℝ :=
  hOneAttractiveNewtonInteraction G u + localInteraction u

/-- Model-specific localized convergence required for the target interaction.
The Hartree component uses the repository's exact `L^(6/5)` closure theorem;
the local cubic--quintic contribution remains a separate explicit premise. -/
structure TargetInteractionConvergence
    (G : ℝ) (localInteraction : EuclideanHOneThree → ℝ)
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree) : Prop where
  hartree : HOneBornLSixFifthsConverges u v
  «local» : Tendsto (fun n => localInteraction (u n)) atTop
    (𝓝 (localInteraction v))

lemma targetInteraction_tendsto
    (G : ℝ) (localInteraction : EuclideanHOneThree → ℝ)
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (h : TargetInteractionConvergence G localInteraction u v) :
    Tendsto (fun n => targetInteraction G localInteraction (u n)) atTop
      (𝓝 (targetInteraction G localInteraction v)) := by
  exact
    (hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths
      G u v h.hartree).add h.«local»

/-- **Corrected M9.75 closure.** Weak `H¹` convergence, convergence of the
localized target interaction, and convergence of a positive kinetic-plus-
interaction energy force no loss of `H¹` norm. The sequence converges strongly,
the limit attains the level, and physical `L²` normalization closes. -/
theorem target_tendsto_and_normalized_of_minimizing_energySplit
    (G : ℝ) (localInteraction energy : EuclideanHOneThree → ℝ)
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (kineticWeight level : ℝ) (hkinetic : 0 < kineticWeight)
    (hnormalized : ∀ n, HOneLTwoNormalized (u n))
    (hweak : ∀ w : EuclideanHOneThree,
      Tendsto (fun n => inner ℂ (u n) w) atTop
        (𝓝 (inner ℂ v w)))
    (hsplit_u : ∀ n,
      energy (u n) = kineticWeight * ‖u n‖ ^ 2 +
        targetInteraction G localInteraction (u n))
    (hsplit_v :
      energy v = kineticWeight * ‖v‖ ^ 2 +
        targetInteraction G localInteraction v)
    (henergy : Tendsto (fun n => energy (u n)) atTop (𝓝 level))
    (hinteraction :
      TargetInteractionConvergence G localInteraction u v)
    (hlower : level ≤ energy v) :
    energy v = level ∧ Tendsto u atTop (𝓝 v) ∧ HOneLTwoNormalized v := by
  have hclosure :=
    hOne_tendsto_of_minimizing_energySplit
      u v energy (targetInteraction G localInteraction)
      kineticWeight level hkinetic hweak hsplit_u hsplit_v henergy
      (targetInteraction_tendsto G localInteraction u v hinteraction)
      hlower
  exact ⟨hclosure.1, hclosure.2,
    hOneLTwoNormalized_of_tendsto hnormalized hclosure.2⟩

/-- **Corrected M9.76 minimizer bridge.** Born first-moment localization and
target-interaction convergence instantiate the live direct method. No global
weak closure of the unit sphere and no unconditional weak lower semicontinuity
of the attractive energy are assumed. -/
theorem exists_target_energyMinimizer
    (G : ℝ) (localInteraction energy : EuclideanHOneThree → ℝ)
    (u : ℕ → EuclideanHOneThree) (B : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (hnormalized : ∀ n, HOneLTwoNormalized (u n))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ n,
      ∫⁻ x, hOneBornDensity (u n) x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (admissible : Set EuclideanHOneThree)
    (kineticWeight level : ℝ) (hkinetic : 0 < kineticWeight)
    (hu_admissible : ∀ n, u n ∈ admissible)
    (hweakClosed :
      ∀ (v : EuclideanHOneThree) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        v ∈ admissible)
    (hsplit : ∀ z ∈ admissible,
      energy z = kineticWeight * ‖z‖ ^ 2 +
        targetInteraction G localInteraction z)
    (henergy : Tendsto (fun n => energy (u n)) atTop (𝓝 level))
    (hlower : ∀ z ∈ admissible, level ≤ energy z)
    (hinteractionClosure :
      ∀ (v : EuclideanHOneThree) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        TargetInteractionConvergence G localInteraction (u ∘ φ) v) :
    ∃ v : EuclideanHOneThree,
      v ∈ admissible ∧ ‖v‖ ≤ B ∧ energy v = level ∧
      ∃ hvNormalized : HOneLTwoNormalized v,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (u ∘ φ) atTop (𝓝 v) ∧
          Tendsto
            (fun n => hOneBornProbability (u (φ n))
              (hnormalized (φ n)))
            atTop (𝓝 (hOneBornProbability v hvNormalized)) := by
  apply bounded_normalized_hOne_firstMoment_has_energyMinimizer
    u B hu hnormalized C hC hmoment admissible energy
    (targetInteraction G localInteraction) kineticWeight level hkinetic
    hu_admissible hweakClosed hsplit henergy hlower
  intro v φ hφ hweak
  exact targetInteraction_tendsto G localInteraction (u ∘ φ) v
    (hinteractionClosure v φ hφ hweak)

/-- Compactness of the complete constrained minimizing orbit follows from the
actual Born moment and target-interaction closure; no separate norm-closure
certificate is accepted. -/
theorem isCompact_target_energyMinimizers
    (G : ℝ) (localInteraction energy : EuclideanHOneThree → ℝ)
    (admissible : Set EuclideanHOneThree)
    (kineticWeight level B : ℝ) (hkinetic : 0 < kineticWeight)
    (hbounded : ∀ z,
      z ∈ {z | z ∈ admissible ∧ energy z = level} → ‖z‖ ≤ B)
    (hnormalized : ∀ z,
      z ∈ {z | z ∈ admissible ∧ energy z = level} →
        HOneLTwoNormalized z)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ z,
      z ∈ {z | z ∈ admissible ∧ energy z = level} →
        ∫⁻ x, hOneBornDensity z x * ENNReal.ofReal ‖x‖
          ∂volume ≤ C)
    (hweakClosed :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n, u n ∈ {z | z ∈ admissible ∧ energy z = level}) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        v ∈ admissible)
    (hsplit : ∀ z ∈ admissible,
      energy z = kineticWeight * ‖z‖ ^ 2 +
        targetInteraction G localInteraction z)
    (hlower : ∀ z ∈ admissible, level ≤ energy z)
    (hinteractionClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n, u n ∈ {z | z ∈ admissible ∧ energy z = level}) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        TargetInteractionConvergence G localInteraction (u ∘ φ) v) :
    IsCompact {z | z ∈ admissible ∧ energy z = level} := by
  apply isCompact_hOneBorn_energyMinimizers_of_interactionClosure
    admissible energy (targetInteraction G localInteraction)
    kineticWeight level B hkinetic hbounded hnormalized C hC hmoment
    hweakClosed hsplit hlower
  intro u v φ hu hφ hweak
  exact targetInteraction_tendsto G localInteraction (u ∘ φ) v
    (hinteractionClosure u v φ hu hφ hweak)

/-- Global weak/mild flow together with the exact conservation data consumed by
the live orbital-stability theorem. Analytic construction of these fields is
not hidden in the structure. -/
structure GlobalConservativeBornMildFlowCertificate where
  weakFlow : HOneWeakMildFlowCertificate
  admissible : Set EuclideanHOneThree
  energy : EuclideanHOneThree → ℝ
  admissible_closed : IsClosed admissible
  admissible_nonempty : admissible.Nonempty
  bound : ℝ
  admissible_bounded : ∀ u ∈ admissible, ‖u‖ ≤ bound
  admissible_normalized : ∀ u ∈ admissible, HOneLTwoNormalized u
  momentBound : ℝ≥0∞
  momentBound_ne_top : momentBound ≠ ∞
  admissible_moment : ∀ u ∈ admissible,
    ∫⁻ x, hOneBornDensity u x * ENNReal.ofReal ‖x‖
      ∂volume ≤ momentBound
  normClosure :
    ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
      (φ : ℕ → ℕ),
      (∀ n, u n ∈ admissible) → StrictMono φ →
      (∀ w : EuclideanHOneThree,
        Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
          (𝓝 (inner ℂ v w))) →
      Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖)
  energy_continuous : Continuous energy
  flow_admissible : ∀ t u,
    u ∈ admissible → weakFlow.flow t u ∈ admissible
  flow_energy : ∀ t u, energy (weakFlow.flow t u) = energy u

/-- **Corrected M9.77 closure.** The actual Born-law compactness theorem
constructs a ground state and its full minimizing orbit. The global
conservative weak/mild flow then makes that orbit uniformly stable. -/
theorem exists_minimizingOrbit_uniformlyStable
    (C : GlobalConservativeBornMildFlowCertificate) :
    ∃ groundEnergy : ℝ,
      (HOneConstrainedEnergyMinimizers C.admissible C.energy).Nonempty ∧
      IsCompact (HOneConstrainedEnergyMinimizers C.admissible C.energy) ∧
      (∀ u, u ∈ HOneConstrainedEnergyMinimizers C.admissible C.energy ↔
        u ∈ C.admissible ∧ C.energy u = groundEnergy) ∧
      (∀ u ∈ C.admissible, groundEnergy ≤ C.energy u) ∧
      IsUniformlyOrbitallyStableOn C.weakFlow.flow C.admissible
        (HOneConstrainedEnergyMinimizers C.admissible C.energy) := by
  exact exists_hOneBorn_minimizingOrbit_uniformlyStable
    C.weakFlow.flow C.admissible C.energy C.admissible_closed
    C.admissible_nonempty C.bound C.admissible_bounded
    C.admissible_normalized C.momentBound C.momentBound_ne_top
    C.admissible_moment C.normClosure C.energy_continuous
    C.flow_admissible C.flow_energy

/-- Optional identification of a distinguished numerical/analytic branch with
the order-defined minimizing orbit. The minimizing property is explicit data,
not inferred from a finite-grid stationary residual. -/
structure IdentifiedTargetBranchCertificate
    extends GlobalConservativeBornMildFlowCertificate where
  branch : EuclideanHOneThree
  branch_mem : branch ∈ admissible
  branch_minimizes : ∀ v ∈ admissible, energy branch ≤ energy v

lemma identifiedBranch_mem_minimizingOrbit
    (C : IdentifiedTargetBranchCertificate) :
    C.branch ∈ HOneConstrainedEnergyMinimizers C.admissible C.energy :=
  ⟨C.branch_mem, C.branch_minimizes⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow.target_tendsto_and_normalized_of_minimizing_energySplit where
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneLTwoNormalized_of_tendsto",
  formalizes @ "claim:localized-hartree-and-local-interaction-convergence-plus-the-positive-h-one-energy-split-force-strong-h-one-no-loss-and-close-the-normalized-born-mass",
  caveat @ "claim:the-unit-l-two-sphere-is-not-claimed-globally-weakly-closed-and-the-attractive-energy-is-not-claimed-unconditionally-weakly-lower-semicontinuous"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow.isCompact_target_energyMinimizers where
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure",
  supported_by @ "lean:WignerSergiSystem.live",
  formalizes @ "claim:born-first-moment-localization-and-target-interaction-convergence-make-the-complete-constrained-minimizing-orbit-strongly-compact-in-h-one",
  caveat @ "claim:recentered-first-moment-control-and-local-cubic-quintic-interaction-convergence-remain-model-specific-analytic-inputs"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow.exists_minimizingOrbit_uniformlyStable where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_minimizingOrbit_uniformlyStable",
  formalizes @ "claim:a-global-conservative-weak-or-mild-h-one-flow-with-the-actual-born-compactness-data-has-a-nonempty-compact-minimizing-orbit-that-is-uniformly-orbitally-stable",
  caveat @ "claim:the-certificate-does-not-construct-the-energy-critical-duhamel-flow-or-prove-its-conservation-laws"

zil_file_contract physlib.cubicQuinticMildFlow where
  promises "Correct weak/mild H1 interfaces for the spatial cubic-quintic target, strong no-loss and normalization closure from localized interaction convergence, compact minimizing-orbit closure from the actual Born law, and uniform orbital stability from an explicit global conservative flow certificate."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.schrodingerNewton_compactModuloTranslations_of_trichotomy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.exists_constrained_hOne_minimizer_of_bounded_minimizingSequence",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.cubicQuinticDensity_coercive"]
  forbids_substitutes ["claiming construction of the energy-critical Duhamel flow or its conservation laws from the orbital-stability certificate"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow.exists_minimizingOrbit_uniformlyStable]

/- ZIL-END -/