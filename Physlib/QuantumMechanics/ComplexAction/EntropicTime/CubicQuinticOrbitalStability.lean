/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE
meta import Zil

/-!
# Cubic--quintic coercivity and live continuum H¹ closure

This module builds only the bridges still missing after the current
`entropic-physlib-linear-full` branch established:

* a complete continuum `H¹(ℝ³)` Bessel-energy carrier;
* weak sequential compactness with retention of the energy bound;
* weak-plus-norm strong convergence;
* Prokhorov compactness for tight probability sequences and a joint field/density
  subsequence theorem;
* a direct-method engine;
* negative-level exclusion of vanishing and positive-binding-gap exclusion of
  dichotomy;
* local existence/uniqueness for every `C¹` generator on the complete H¹ carrier;
* Cazenave--Lions orbital stability from compact energy sublevels and conserved
  flow.

The new results below add predicate-carrier bridges, constrained attainment, and
the composition of the already-proved variational exclusions with an explicit
concentration--compactness trichotomy.

## Honest scope

The remaining model-specific work is to prove the normalized mass constraint is
weakly closed, promote the target energy with weak lower semicontinuity, derive
tightness modulo translations from the binding functional, prove the concrete
Hartree/cubic--quintic generator is `C¹` on H¹, and construct its global
mass/energy-preserving flow.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory SchwartzMap
open scoped ENNReal Space Topology
open Space
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability

/-! ## A. Exact cubic--quintic density coercivity -/

lemma cubicQuinticDensity_slack_eq
    (α β ρ : ℝ) (hβ : β ≠ 0) :
    (-α / 2) * ρ ^ 2 + (β / 3) * ρ ^ 3 +
        (3 * α ^ 2 / (16 * β)) * ρ =
      (β / 3) * ρ * (ρ - 3 * α / (4 * β)) ^ 2 := by
  field_simp [hβ]
  ring

lemma cubicQuinticDensity_coercive
    (α β ρ : ℝ) (hβ : 0 < β) (hρ : 0 ≤ ρ) :
    -(3 * α ^ 2 / (16 * β)) * ρ ≤
      (-α / 2) * ρ ^ 2 + (β / 3) * ρ ^ 3 := by
  have hslack :
      0 ≤ (β / 3) * ρ * (ρ - 3 * α / (4 * β)) ^ 2 := by
    positivity
  rw [← cubicQuinticDensity_slack_eq α β ρ hβ.ne'] at hslack
  linarith

/-! ## B. Predicate-carrier H¹ compactness bridges -/

/-- Sequential weak closure of a constraint set in the repository's exact
predicate-defined `H¹(ℝ³)` carrier. -/
def HOneSequentiallyWeaklyClosed
    (S : Set (EuclideanHs 3 1)) : Prop :=
  ∀ (u : ℕ → EuclideanHs 3 1) (f : EuclideanHs 3 1),
    (∀ n, u n ∈ S) → HOneWeaklyConverges u f → f ∈ S

/-- Weak predicate-carrier convergence plus convergence of the exact Sobolev
norm upgrades to strong convergence of the complete H¹ energy coordinates. -/
theorem hOneEnergyCoordinate_tendsto_of_weak_of_sobolevNorm
    (u : ℕ → EuclideanHs 3 1) (f : EuclideanHs 3 1)
    (hweak : HOneWeaklyConverges u f)
    (hnorm : Tendsto (fun n => sobolevNorm 1 (u n).1 (u n).2)
      atTop (𝓝 (sobolevNorm 1 f.1 f.2))) :
    Tendsto (fun n => hOneEnergyCoordinate (u n)) atTop
      (𝓝 (hOneEnergyCoordinate f)) := by
  apply hOne_tendsto_of_weak_of_norm
  · intro w
    simpa using hweak (hOneFromEnergyCoordinate w)
  · simpa using hnorm

/-- A Sobolev-bounded predicate-carrier sequence whose associated probability
measures are tight has one common subsequence with weak H¹ field convergence,
retained energy bound, and distributional density convergence. -/
theorem bounded_sobolevNorm_and_tightProbability_has_joint_subsequence
    (u : ℕ → EuclideanHs 3 1) (C : ℝ)
    (hu : ∀ n, sobolevNorm 1 (u n).1 (u n).2 ≤ C)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) |
        ν ∈ Set.range μ}) :
    ∃ f : EuclideanHs 3 1,
      sobolevNorm 1 f.1 f.2 ≤ C ∧
        ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)),
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            HOneWeaklyConverges (u ∘ φ) f ∧
            Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨v, hv, ν, φ, hφ, hweak, hμ⟩ :=
    bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence
      (fun n => hOneEnergyCoordinate (u n)) C
      (fun n => by simpa using hu n) μ htight
  refine ⟨hOneFromEnergyCoordinate v, ?_, ν, φ, hφ, ?_, hμ⟩
  · rw [← norm_hOneEnergyCoordinate, hOneEnergyCoordinate_fromEnergyCoordinate]
    exact hv
  · intro w
    simpa [HOneWeaklyConverges, Function.comp_def] using
      hweak (hOneEnergyCoordinate w)

/-! ## C. Constrained direct method on the complete continuum carrier -/

/-- A Sobolev-bounded minimizing sequence in a sequentially weakly closed
constraint set attains its level when the functional is sequentially weakly
lower semicontinuous. -/
theorem exists_constrained_hOne_minimizer_of_bounded_minimizingSequence
    (J : EuclideanHs 3 1 → ℝ) (S : Set (EuclideanHs 3 1))
    (level C : ℝ) (u : ℕ → EuclideanHs 3 1)
    (huS : ∀ n, u n ∈ S)
    (hu : ∀ n, sobolevNorm 1 (u n).1 (u n).2 ≤ C)
    (hJ : Tendsto (fun n => J (u n)) atTop (𝓝 level))
    (hlower : ∀ f, f ∈ S → level ≤ J f)
    (hclosed : HOneSequentiallyWeaklyClosed S)
    (hlsc : HOneSequentiallyWeaklyLowerSemicontinuous J) :
    ∃ f : EuclideanHs 3 1, f ∈ S ∧ J f = level := by
  obtain ⟨f, φ, hφ, hf⟩ :=
    bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence u C hu
  have hfS : f ∈ S :=
    hclosed (u ∘ φ) f (fun n => huS (φ n)) hf
  have hJφ : Tendsto (fun n => J (u (φ n))) atTop (𝓝 level) :=
    hJ.comp hφ.tendsto_atTop
  have hupper : J f ≤ level :=
    hlsc (u ∘ φ) f level hf (by
      simpa [Function.comp_def] using hJφ)
  exact ⟨f, hfS, le_antisymm hupper (hlower f hfS)⟩

structure HOneGroundStateCertificate where
  functional : EuclideanHs 3 1 → ℝ
  constraint : Set (EuclideanHs 3 1)
  level : ℝ
  bound : ℝ
  minimizingSequence : ℕ → EuclideanHs 3 1
  sequence_mem : ∀ n, minimizingSequence n ∈ constraint
  sequence_bound : ∀ n,
    sobolevNorm 1 (minimizingSequence n).1 (minimizingSequence n).2 ≤ bound
  sequence_minimizes :
    Tendsto (fun n => functional (minimizingSequence n)) atTop (𝓝 level)
  level_lower : ∀ f, f ∈ constraint → level ≤ functional f
  constraint_weaklyClosed : HOneSequentiallyWeaklyClosed constraint
  functional_weaklyLowerSemicontinuous :
    HOneSequentiallyWeaklyLowerSemicontinuous functional

namespace HOneGroundStateCertificate

theorem exists_groundState (C : HOneGroundStateCertificate) :
    ∃ f : EuclideanHs 3 1,
      f ∈ C.constraint ∧ C.functional f = C.level :=
  exists_constrained_hOne_minimizer_of_bounded_minimizingSequence
    C.functional C.constraint C.level C.bound C.minimizingSequence
    C.sequence_mem C.sequence_bound C.sequence_minimizes C.level_lower
    C.constraint_weaklyClosed C.functional_weaklyLowerSemicontinuous

end HOneGroundStateCertificate

/-! ## D. Concentration--compactness branch elimination -/

def ConcentrationCompactnessTrichotomy
    (Vanishing Dichotomy CompactModuloTranslations : Prop) : Prop :=
  Vanishing ∨ Dichotomy ∨ CompactModuloTranslations

/-- The current branch's negative normalized level excludes vanishing, and its
positive cluster binding gap excludes dichotomy. Hence any explicit
concentration--compactness trichotomy reduces to compactness modulo translations. -/
theorem schrodingerNewton_compactModuloTranslations_of_trichotomy
    (G M a : ℝ) (hG : 0 < G) (ha : 0 < a) (haM : a < M)
    (seed : 𝓢(Space 3, ℝ))
    (hseedNorm : ∫⁻ x, ‖seed x‖ₑ ^ (2 : ℝ) = 1)
    (hseedCompact : HasCompactSupport (seed : Space 3 → ℝ))
    (hseedHartree :
      0 < newtonianSelfEnergy (fun x => seed x ^ 2))
    (Vanishing Dichotomy CompactModuloTranslations : Prop)
    (htrichotomy : ConcentrationCompactnessTrichotomy
      Vanishing Dichotomy CompactModuloTranslations)
    (hvanishing : Vanishing → 0 ≤ normalizedCoreGroundEnergy G)
    (hdichotomy : Dichotomy → compactCoreBindingGap G M a ≤ 0) :
    CompactModuloTranslations := by
  rcases htrichotomy with hvan | hdich | hcompact
  · exact False.elim ((not_le_of_gt
      (normalizedCoreGroundEnergy_neg G hG seed
        hseedNorm hseedCompact hseedHartree)) (hvanishing hvan))
  · exact False.elim ((not_le_of_gt
      (compactCoreBindingGap_pos G M a hG ha haM seed
        hseedNorm hseedCompact hseedHartree)) (hdichotomy hdich))
  · exact hcompact

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.cubicQuinticDensity_coercive where
  formalizes @ "claim:positive-quintic-saturation-gives-the-exact-local-density-lower-bound-v-rho-greater-than-or-equal-to-minus-three-alpha-squared-over-sixteen-beta-times-rho"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.bounded_sobolevNorm_and_tightProbability_has_joint_subsequence where
  formalizes @ "claim:a-sobolev-bounded-predicate-h-one-sequence-with-tight-probability-densities-has-one-common-subsequence-realizing-weak-field-convergence-with-retained-bound-and-distributional-density-convergence",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence",
  caveat @ "claim:tightness-must-still-be-derived-from-the-binding-functional-after-recentering"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.hOneEnergyCoordinate_tendsto_of_weak_of_sobolevNorm where
  formalizes @ "claim:predicate-carrier-weak-h-one-convergence-plus-sobolev-norm-convergence-implies-strong-convergence-of-the-complete-h-one-energy-coordinates",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.exists_constrained_hOne_minimizer_of_bounded_minimizingSequence where
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence",
  formalizes @ "claim:on-the-complete-continuum-h-one-r-three-carrier-a-sobolev-bounded-minimizing-sequence-in-a-sequentially-weakly-closed-constraint-attains-its-level-for-a-sequentially-weakly-lower-semicontinuous-functional",
  caveat @ "claim:constraint-closure-and-target-functional-lower-semicontinuity-remain-model-specific-obligations"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.schrodingerNewton_compactModuloTranslations_of_trichotomy where
  formalizes @ "claim:negative-ground-energy-excludes-vanishing-and-a-positive-cluster-binding-gap-excludes-dichotomy-so-an-explicit-concentration-compactness-trichotomy-leaves-only-compactness-modulo-translations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalizedCoreGroundEnergy_neg",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_pos",
  caveat @ "claim:derivation-of-tightness-modulo-translations-and-the-trichotomy-remains-open"

zil_file_contract physlib.cubicQuinticOrbitalStability where
  promises "Exact cubic-quintic density coercivity, predicate-carrier joint field/density compactness from tightness, weak-plus-norm strong H1 closure, constrained direct-method attainment, and elimination of vanishing and dichotomy from the live Schrodinger-Newton variational theorems."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalizedCoreGroundEnergy_neg",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_pos"]
  forbids_substitutes ["claiming tightness modulo translations or the concentration-compactness trichotomy is derived rather than assumed as a model obligation"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability.schrodingerNewton_compactModuloTranslations_of_trichotomy]

/- ZIL-END -/
