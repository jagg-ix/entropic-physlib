/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelGibbsModular
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelCrossObservable
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ContinuumWeakCouplingReduction
public import Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction
meta import Zil

/-!
# The unified constrained system–clock–bath carrier

Page–Wootters conditioning, GKSL dissipation, a Gibbs/modular equilibrium, and
strict entropic relaxation have existed in this repository as *separate* carriers.
This module supplies the single structure that holds them together and proves
that one constrained system–clock–bath model **reduces to both experimentally
anchored limits**:

* the reversible **Page–Wootters photon-clock** limit (`𝓛 = 0`), where the
  conditional generator is the von Neumann generator and the conditional channel
  is entropy-preserving; and
* the irreversible **quantum-dot / driven-lead** limit, where the conditional
  channel strictly contracts relative entropy toward a faithful Gibbs
  equilibrium, which is therefore its **unique** thermal steady state.

The bundled pieces are all pre-existing proved carriers:

* `HamiltonianConstraint` / `IsPhysical` — the global constraint
  `(H_C + H_S + H_int)|Ψ⟩ = 0`;
* `DissipativeConditionalClock.gksLGen` — the conditional generator
  `−(i/ℏ)[H_S, ρ] + 𝓛(ρ)`, with `gksLGen_eq_vonNeumannGen_of_lindblad_zero` the
  `𝓛 → 0` (Moreva) reduction and `conditionalEntropicRate_nonneg` the pointwise
  Spohn `dτ_ent/dτ ≥ 0`;
* `oneLevelChannel` with its Gibbs stationary state (`stationaryState_gibbs_form`),
  modular generator `K = β·H_S + log Z·𝟙` (`modularHamiltonian_stationaryState`),
  and strict arrow (`oneLevelChannel_qRelativeEnt_strictLt_of_ne`); and
* `fixedPoint_unique_of_strict_qRelativeEnt` — a strictly-contracting channel has a
  unique fixed point, and `cptp_qRelativeEnt_le` — data processing.

The final section composes the later continuum work back into this carrier.  It
uses the nonzero one-level Page--Wootters constraint and correlated history,
the explicit one-level `C₀` CPTP semigroup, and the Gaussian collision-reservoir
Davies-scale realization.  Thus the earlier certificate obligation is closed for
that concrete reservoir, while the stronger fixed-Hamiltonian
`H₀ + λV` thermodynamic Davies theorem remains explicitly out of scope.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open QuantumMechanics.LindbladDrivenLeads
open Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction

namespace Physlib.QuantumMechanics.RelationalTime

/-- **One constrained system–clock–bath carrier.**  It bundles the Page–Wootters
global constraint, the conditional GKSL generator on the system, and a faithful
Gibbs equilibrium realized by a stationary conditional channel. -/
structure UnifiedRelationalDissipativeCarrier
    (Glob Sys : Type*)
    [NormedAddCommGroup Glob] [InnerProductSpace ℂ Glob]
    [NormedAddCommGroup Sys] [InnerProductSpace ℂ Sys]
    [CompleteSpace Sys] [FiniteDimensional ℂ Sys]
    (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The Page–Wootters global constraint `(H_C + H_S + H_int)|Ψ⟩ = 0`. -/
  constraint : HamiltonianConstraint Glob
  /-- A physical (constraint-annihilated) global state. -/
  physicalState : Glob
  /-- The global state is annihilated by the constraint. -/
  physical : constraint.IsPhysical physicalState
  /-- The conditional GKSL generator `dρ_S/dτ = −(i/ℏ)[H_S, ρ] + 𝓛(ρ)`. -/
  clock : DissipativeConditionalClock Sys
  /-- The discrete CPTP realization of one conditional step. -/
  channel : CPTPMap d d
  /-- The faithful Gibbs / thermal equilibrium. -/
  gibbs : MState d
  /-- The equilibrium is stationary under the conditional channel. -/
  gibbs_stationary : channel gibbs = gibbs

namespace UnifiedRelationalDissipativeCarrier

variable {Glob Sys : Type*}
  [NormedAddCommGroup Glob] [InnerProductSpace ℂ Glob]
  [NormedAddCommGroup Sys] [InnerProductSpace ℂ Sys]
  [CompleteSpace Sys] [FiniteDimensional ℂ Sys]
  {d : Type*} [Fintype d] [DecidableEq d]
variable (C : UnifiedRelationalDissipativeCarrier Glob Sys d)

/-- The conditional generator of the carrier: `−(i/ℏ)[H_S, ρ] + 𝓛(ρ)`. -/
def conditionalGenerator (ρ : Sys →L[ℂ] Sys) : Sys →L[ℂ] Sys :=
  C.clock.gksLGen ρ

/-- **The Page–Wootters (Moreva photon-clock) limit `𝓛 = 0`**: the conditional
generator is exactly the von Neumann generator — reversible unitary conditional
evolution is the dissipationless limit of the carrier. -/
@[zil_level physical_theorem]
theorem morevaLimit_unitaryConditional (ρ : Sys →L[ℂ] Sys)
    (hL : C.clock.lindblad = 0) :
    C.conditionalGenerator ρ = C.clock.vonNeumannGen ρ :=
  C.clock.gksLGen_eq_vonNeumannGen_of_lindblad_zero ρ hL

/-- **The reversible limit is entropy-preserving**: when the conditional channel is
a genuinely unitary channel it produces no von Neumann entropy — the reversible
Page–Wootters sector. -/
@[zil_level physical_theorem]
theorem morevaLimit_entropyPreserving (h : C.channel.IsUnitary) :
    IsEntropyPreserving C.channel :=
  isUnitary_isEntropyPreserving C.channel h

/-- **Data processing toward equilibrium**: the conditional channel never
increases the relative entropy to the Gibbs equilibrium — the shared
irreversibility law, with the reversible case the equality boundary. -/
@[zil_level physical_theorem]
theorem kl_contracts_to_gibbs (ρ : MState d) :
    qRelativeEnt (C.channel ρ) C.gibbs ≤ qRelativeEnt ρ C.gibbs := by
  have h := cptp_qRelativeEnt_le C.channel ρ C.gibbs
  rwa [C.gibbs_stationary] at h

/-- **The quantum-dot / driven-lead limit**: if the conditional channel strictly
contracts the relative entropy toward the Gibbs equilibrium on every other state,
then that equilibrium is its **unique** fixed point — a unique thermal steady state
reached by strict irreversible relaxation. -/
@[zil_level bridge_theorem]
theorem quantumDotLimit_uniqueEquilibrium
    (hstrict : ∀ ρ, ρ ≠ C.gibbs →
      qRelativeEnt (C.channel ρ) C.gibbs < qRelativeEnt ρ C.gibbs)
    {ρ : MState d} (hρfix : C.channel ρ = ρ) : ρ = C.gibbs := by
  refine fixedPoint_unique_of_strict_qRelativeEnt C.channel C.gibbs C.gibbs_stationary
    (fun σ hσ => ?_) hρfix
  rw [C.gibbs_stationary]
  exact hstrict σ hσ

/-- **Non-negative entropic production (pointwise Spohn)**: the conditional
dissipation rate is non-negative, so the accumulated entropic time `τ_ent` is
non-decreasing along the worldline. -/
@[zil_level physical_theorem]
theorem entropicProduction_nonneg {ι : Type*} [Fintype ι]
    (L : ι → (Sys →L[ℂ] Sys)) (ψ : Sys) :
    0 ≤ C.clock.conditionalEntropicRate L ψ :=
  C.clock.conditionalEntropicRate_nonneg L ψ

/-- **One carrier, both experimental limits.**  A single constrained
system–clock–bath carrier simultaneously exposes:

* the reversible Page–Wootters conditional evolution as the `𝓛 = 0` limit;
* a unique thermal Gibbs steady state under strict relative-entropy contraction;
* relative-entropy data processing toward that equilibrium.

This is the joint reduction the separate carriers could not state together. -/
@[zil_level bridge_theorem]
theorem reduces_to_both_limits
    (hstrict : ∀ ρ, ρ ≠ C.gibbs →
      qRelativeEnt (C.channel ρ) C.gibbs < qRelativeEnt ρ C.gibbs) :
    (∀ ρ : Sys →L[ℂ] Sys, C.clock.lindblad = 0 →
        C.conditionalGenerator ρ = C.clock.vonNeumannGen ρ)
      ∧ (∀ ρ : MState d, C.channel ρ = ρ → ρ = C.gibbs)
      ∧ (∀ ρ : MState d,
          qRelativeEnt (C.channel ρ) C.gibbs ≤ qRelativeEnt ρ C.gibbs) :=
  ⟨fun ρ hL => C.morevaLimit_unitaryConditional ρ hL,
   fun _ hρfix => C.quantumDotLimit_uniqueEquilibrium hstrict hρfix,
   fun ρ => C.kl_contracts_to_gibbs ρ⟩

end UnifiedRelationalDissipativeCarrier

/-! ## The carrier is inhabited by the one-level driven-lead channel -/

/-- **The one-level driven-lead channel is a unified carrier.**  Its conditional
channel is `oneLevelChannel`, its equilibrium the one-level stationary state (the
qubit Gibbs state at the Fermi occupation), the constraint and conditional clock
the dissipationless free clock.  This witnesses that the unified structure is not
vacuous. -/
noncomputable def unifiedCarrierOfOneLevel (d0 : OneLevelChannelData)
    (ℏ : ℝ) (hℏ : 0 < ℏ) :
    UnifiedRelationalDissipativeCarrier
      (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 1)) Qubit where
  constraint := HamiltonianConstraint.trivial _
  physicalState := 0
  physical := HamiltonianConstraint.isPhysical_zero _
  clock := DissipativeConditionalClock.trivial ℏ hℏ
  channel := oneLevelChannel d0
  gibbs := d0.stationaryState
  gibbs_stationary := oneLevelChannel_stationaryState_fixed d0

/-- **The quantum-dot limit fires on the one-level witness**: on interior, non-half,
non-stationary occupations the one-level channel strictly contracts relative
entropy toward the Gibbs equilibrium, so `quantumDotLimit_uniqueEquilibrium`
applies to the concrete carrier. -/
@[zil_level physical_theorem]
theorem unifiedCarrierOfOneLevel_strictArrow (d0 : OneLevelChannelData)
    (ℏ : ℝ) (hℏ : 0 < ℏ) (hf0 : 0 < d0.occupation) (hf1 : d0.occupation < 1)
    (hhalf : d0.occupation ≠ 1 / 2) (hd0 : 0 < d0.damping) (ρ : MState Qubit)
    (hN0 : 0 < excitedOccupation ρ) (hN1 : excitedOccupation ρ < 1)
    (hne : ρ ≠ d0.stationaryState) :
    qRelativeEnt ((unifiedCarrierOfOneLevel d0 ℏ hℏ).channel ρ)
        (unifiedCarrierOfOneLevel d0 ℏ hℏ).gibbs
      < qRelativeEnt ρ (unifiedCarrierOfOneLevel d0 ℏ hℏ).gibbs :=
  oneLevelChannel_qRelativeEnt_strictLt_of_ne d0 hf0 hf1 hhalf hd0 ρ hN0 hN1 hne

/-! ## Nontrivial constrained carrier and continuum-bath closure -/

/-- The actual one-level dissipative Page--Wootters system, embedded in the
unified carrier at a selected nonnegative macroscopic time.  Unlike the minimal
inhabitant above, this uses the nonzero clock--system Hamiltonian constraint,
the nonzero correlated history, the explicit loss/gain conditional generator,
and the genuine one-level `C₀` CPTP semigroup. -/
noncomputable def unifiedCarrierOfDissipativeOneLevel
    (P : OneLevelDissipativePageWoottersCarrier) (t : NNReal) :
    UnifiedRelationalDissipativeCarrier
      (EuclideanSpace ℂ (Qubit × Qubit)) (EuclideanSpace ℂ Qubit) Qubit where
  constraint := P.constraint
  physicalState := oneLevelCorrelatedHistory
  physical := oneLevelCorrelatedHistory_isPhysical P.energy
  clock := P.clock
  channel := P.rate.oneLevelCPTPC0Semigroup.channel t
  gibbs := P.rate.continuousStationaryState
  gibbs_stationary := by
    exact P.rate.oneLevelPositiveTimeSemigroup_stationary_fixed t

/-- **The unified carrier is genuinely constrained and dissipative.**  Its
history and total constraint are nonzero, the history satisfies that constraint,
and its conditional generator is exactly the concrete one-level GKSL matrix
operator on every density matrix. -/
@[zil_level bridge_theorem]
theorem unifiedCarrierOfDissipativeOneLevel_nontrivial_gksl
    (P : OneLevelDissipativePageWoottersCarrier) (t : NNReal)
    (ρ : Matrix Qubit Qubit ℂ) :
    let C := unifiedCarrierOfDissipativeOneLevel P t;
      C.constraint.IsPhysical C.physicalState ∧
      C.physicalState ≠ 0 ∧ C.constraint.H_total ≠ 0 ∧
      C.conditionalGenerator
          (Matrix.toEuclideanCLM (n := Qubit) (𝕜 := ℂ) ρ) =
        Matrix.toEuclideanCLM (n := Qubit) (𝕜 := ℂ)
          (oneLevelGKSLMatrix P.rate ρ) := by
  dsimp [unifiedCarrierOfDissipativeOneLevel,
    UnifiedRelationalDissipativeCarrier.conditionalGenerator]
  exact ⟨oneLevelCorrelatedHistory_isPhysical P.energy,
    oneLevelCorrelatedHistory_ne_zero,
    oneLevelHamiltonianConstraint_nonzero P.energy P.energy_ne_zero,
    oneLevelExplicitDissipativeClock_gksLGen P.rate P.ℏ P.ℏ_pos ρ⟩

/-- A Gaussian continuum spectral bath selects the rate of a nontrivial
one-level Page--Wootters carrier. -/
noncomputable def gaussianOneLevelPageWoottersCarrier
    (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1)
    (ℏ : ℝ) (hℏ : 0 < ℏ) (energy : ℝ) (henergy : energy ≠ 0) :
    OneLevelDissipativePageWoottersCarrier where
  rate := b.toRateData couplingStrengthSq occupation hc hf0 hf1
  ℏ := ℏ
  ℏ_pos := hℏ
  energy := energy
  energy_ne_zero := henergy

/-- The continuum-bath-selected, nontrivially constrained unified carrier. -/
noncomputable def unifiedCarrierOfGaussianBath
    (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1)
    (ℏ : ℝ) (hℏ : 0 < ℏ) (energy : ℝ) (henergy : energy ≠ 0)
    (t : NNReal) :
    UnifiedRelationalDissipativeCarrier
      (EuclideanSpace ℂ (Qubit × Qubit)) (EuclideanSpace ℂ Qubit) Qubit :=
  unifiedCarrierOfDissipativeOneLevel
    (gaussianOneLevelPageWoottersCarrier b couplingStrengthSq occupation hc
      hf0 hf1 ℏ hℏ energy henergy) t

/-- **Continuum Davies--relational--cross-observable capstone.**  One Gaussian
continuum bath fixes a single golden-rule rate.  That same rate:

* is the right generator coefficient of the reduced `C₀` CPTP semigroup;
* is obtained as the Davies-scale reduction of unitary collision dynamics;
* drives the nonzero constrained Page--Wootters conditional GKSL clock;
* is the Lorentzian HWHM and fixes the population relaxation time; and
* occurs in the exact derivative of the held-out binary relative entropy.

This is a model-level cross-observable theorem.  It does not identify a
laboratory bath or replace the collision dilation by a fixed
`H₀ + λV` thermodynamic-limit theorem. -/
@[zil_level bridge_theorem]
theorem gaussianBath_davies_relational_linewidth_KL_capstone
    (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 < occupation) (hf1 : occupation < 1)
    (ℏ : ℝ) (hℏ : 0 < ℏ) (energy : ℝ) (henergy : energy ≠ 0)
    (macroTime : NNReal) (epsilon N₀ τ : ℝ)
    (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1) (hτ : 0 ≤ τ) :
    let r := b.toRateData couplingStrengthSq occupation hc hf0.le hf1.le;
    let C := unifiedCarrierOfGaussianBath b couplingStrengthSq occupation hc
      hf0.le hf1.le ℏ hℏ energy henergy macroTime;
    C.constraint.IsPhysical C.physicalState ∧
      C.physicalState ≠ 0 ∧ C.constraint.H_total ≠ 0 ∧
      (∀ ρ : Matrix Qubit Qubit ℂ,
        C.conditionalGenerator
            (Matrix.toEuclideanCLM (n := Qubit) (𝕜 := ℂ) ρ) =
          Matrix.toEuclideanCLM (n := Qubit) (𝕜 := ℂ)
            (oneLevelGKSLMatrix r ρ)) ∧
      r.gamma = 2 * Real.pi * couplingStrengthSq * b.spectralWeight ∧
      r.oneLevelCPTPC0Semigroup.HasInfinitesimalGenerator
        (oneLevelGKSLMatrix r) ∧
      (∀ s, Filter.Tendsto (fun lambda : NNReal =>
          daviesReducedUnitaryBathChannel r lambda (s / lambda ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (r.oneLevelCPTPC0Semigroup.channel s))) ∧
      lorentzHWHM r epsilon = r.gamma ∧
      r.populationRelaxationTime = (2 * r.gamma)⁻¹ ∧
      HasDerivAt (fun s => binaryKL (r.predictedOccupation N₀ s) r.occupation)
        (-(entropyProductionRate r.gamma
          (r.predictedOccupation N₀ τ) r.occupation)) τ := by
  dsimp [unifiedCarrierOfGaussianBath,
    unifiedCarrierOfDissipativeOneLevel,
    gaussianOneLevelPageWoottersCarrier]
  let r := b.toRateData couplingStrengthSq occupation hc hf0.le hf1.le
  exact ⟨oneLevelCorrelatedHistory_isPhysical energy,
    oneLevelCorrelatedHistory_ne_zero,
    oneLevelHamiltonianConstraint_nonzero energy henergy,
    fun ρ => oneLevelExplicitDissipativeClock_gksLGen
      r ℏ hℏ ρ,
    rfl,
    r.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator,
    daviesReducedUnitaryBathChannel_tendsto r,
    lorentzHWHM_eq_gamma r epsilon,
    rfl,
    binaryKL_predictedOccupation_hasDerivAt r hN₀0 hN₀1 hf0 hf1 hτ⟩

end Physlib.QuantumMechanics.RelationalTime

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier

zil attach reduces_to_both_limits where
  formalizes @ "claim:one-constrained-system-clock-bath-carrier-reduces-to-both-the-reversible-page-wootters-unitary-limit-and-the-strict-relaxation-to-a-unique-gibbs-equilibrium",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.gksLGen_eq_vonNeumannGen_of_lindblad_zero",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-generic-two-limit-theorem-does-not-by-itself-identify-a-microscopic-bath-the-concrete-Gaussian-collision-Davies-realization-is-supplied-by-gaussianBath_davies_relational_linewidth_KL_capstone"

zil attach morevaLimit_unitaryConditional where
  formalizes @ "claim:the-dissipationless-limit-of-the-unified-carrier-is-the-reversible-page-wootters-von-neumann-conditional-evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.gksLGen_eq_vonNeumannGen_of_lindblad_zero"

zil attach quantumDotLimit_uniqueEquilibrium where
  formalizes @ "claim:the-dissipative-limit-of-the-unified-carrier-relaxes-strictly-to-a-unique-gibbs-thermal-equilibrium",
  unique_up_to @ "lean:QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt"

zil attach unifiedCarrierOfOneLevel_strictArrow where
  formalizes @ "claim:the-one-level-driven-lead-channel-inhabits-the-unified-carrier-and-realizes-its-strict-thermal-relaxation-limit",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_ne"

zil attach unifiedCarrierOfDissipativeOneLevel_nontrivial_gksl where
  formalizes @ "claim:the-unified-relational-dissipative-carrier-has-a-nonzero-correlated-history-in-the-kernel-of-a-nonzero-page-wootters-constraint-and-its-conditional-generator-is-the-explicit-one-level-GKSL-operator",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.OneLevelDissipativePageWoottersCarrier.constrained_gksl_history",
  epistemic_status @ "conditional-model"

zil attach gaussianBath_davies_relational_linewidth_KL_capstone where
  formalizes @ "claim:one-Gaussian-continuum-bath-rate-simultaneously-fixes-the-unitary-Davies-scale-reduction-the-C0-GKSL-generator-the-constrained-relational-clock-the-Lorentzian-linewidth-the-population-relaxation-time-and-the-exact-KL-production-derivative",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.gaussianContinuumBath_davies_cptp_gksl_capstone",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.calibrated_rate_linewidth_relaxation_KL_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfDissipativeOneLevel_nontrivial_gksl",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-selected-physical-reservoir-is-the-Gaussian-continuum-collision-model-and-its-occupation-and-coupling-data-are-independently-fixed",
  caveat @ "scope:proved-for-the-explicit-collision-dilation-not-a-universal-fixed-H-zero-plus-lambda-V-thermodynamic-Davies-limit-or-an-external-laboratory-identification"

zil_file_contract physlib.unifiedRelationalDissipativeCarrier where
  promises "One constrained system-clock-bath carrier bundles the Page-Wootters global constraint, the conditional GKSL generator, and a faithful Gibbs equilibrium, and reduces to both experimentally anchored limits. The concrete one-level inhabitant is strengthened from the minimal zero-constraint witness to a nonzero correlated history in the kernel of a nonzero clock-system constraint with the explicit GKSL clock. A Gaussian continuum collision reservoir then selects the same rate appearing in its unitary Davies-scale reduction, the C0 CPTP infinitesimal generator, the Lorentzian half-width, the population relaxation time, and the exact binary-KL derivative."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint",
    "lean:Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock",
    "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel",
    "lean:QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt",
    "lean:QuantumMechanics.LindbladDrivenLeads.OneLevelDissipativePageWoottersCarrier",
    "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath"
  ]
  forbids_substitutes [
    "promoting the explicit Gaussian collision dilation to the universal fixed-H-zero-plus-lambda-V thermodynamic Davies theorem",
    "identifying the mathematical Gaussian bath with a laboratory reservoir without an independent physical-identity package",
    "asserting strict relaxation without the strict relative-entropy contraction hypothesis"
  ]
  witnessed_by [
    morevaLimit_unitaryConditional,
    quantumDotLimit_uniqueEquilibrium,
    reduces_to_both_limits,
    unifiedCarrierOfOneLevel_strictArrow,
    unifiedCarrierOfDissipativeOneLevel_nontrivial_gksl,
    gaussianBath_davies_relational_linewidth_KL_capstone
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.unifiedRelationalDissipativeCarrier
