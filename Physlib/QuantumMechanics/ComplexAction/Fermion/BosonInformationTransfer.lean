/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit
public import Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.YangBaxterConvolutionAlgebra
public import Physlib.Thermodynamics.Landauer
public import Physlib.Thermodynamics.InformationChannelStress

/-!
# Fermion-boson information transfer through complex action and Yang-Baxter convolution

This file links the proposed absorption/emission picture to existing checked infrastructure without adding
a new physical dynamics.  The exact formal content is:

* the Fermi-Dirac occupation satisfies `0 < n_F < 1`, so the vacancy `1 - n_F` is strictly positive;
* a nonnegative KL / mutual-information payload bounded by that vacancy is an admissible absorption payload;
* a complex action whose imaginary part is `S_I` records information `S_I / hbar` through
  `Thermodynamics.Landauer.complexActionNats`;
* if the emitted boson records that same payload, Lean proves that the emitted payload is exactly the
  imaginary-action information readout;
* the same payload structure gives a Yang-Baxter convolution solution by lifting the existing symmetric braid
  solution into the scalar convolution algebra;
* Wilson-loop topological spin gives the fermion sign, Dirac `alpha`/`beta` anticommutation gives the
  algebraic zitterbewegung marker, and the Vlasov-Maxwell index jump supplies the checked critical crossing.

What is not claimed here: a full interaction Hamiltonian, a time-domain zitterbewegung theorem, or a Hopf
bifurcation normal form.  Those would require additional analytic assumptions.  This bridge proves the
repo-supported algebraic skeleton and exposes exactly where such dynamics would attach.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.BosonInformationTransfer

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.YangBaxterConvolutionAlgebra
open Physlib.Thermodynamics
open Physlib.Thermodynamics.Landauer
open Physlib.Thermodynamics.InformationChannelStress

/-! ## A. Fermi occupancy leaves a positive absorption vacancy -/

/-- The Pauli vacancy of a single fermion mode at parameter `x`: `1 - n_F(x)`. -/
def fermionVacancy (x : ℝ) : ℝ :=
  1 - fermiDirac x

/-- The Fermi occupation is always in the open interval `(0, 1)`. -/
theorem fermiDirac_open_interval (x : ℝ) : 0 < fermiDirac x ∧ fermiDirac x < 1 :=
  ⟨StatisticalMechanics.BoseFermiOccupationInformationLimit.fermiDirac_pos x,
   StatisticalMechanics.BoseFermiOccupationInformationLimit.fermiDirac_lt_one x⟩

/-- The vacancy `1 - n_F` is strictly positive. -/
theorem fermionVacancy_pos (x : ℝ) : 0 < fermionVacancy x := by
  unfold fermionVacancy
  linarith [StatisticalMechanics.BoseFermiOccupationInformationLimit.fermiDirac_lt_one x]

/-- A bosonic information payload can be absorbed by a Pauli-bounded mode when it is nonnegative and no
larger than the available vacancy. -/
def BosonAbsorptionAllowed (x payload : ℝ) : Prop :=
  0 ≤ payload ∧ payload ≤ fermionVacancy x

/-- Zero payload is always absorbable. -/
theorem zero_payload_absorbable (x : ℝ) : BosonAbsorptionAllowed x 0 :=
  ⟨le_rfl, le_of_lt (fermionVacancy_pos x)⟩

/-- The entire vacancy is an admissible payload. -/
theorem vacancy_payload_absorbable (x : ℝ) : BosonAbsorptionAllowed x (fermionVacancy x) :=
  ⟨le_of_lt (fermionVacancy_pos x), le_rfl⟩

/-! ## B. KL / mutual-information payload as imaginary action -/

/-- A KL-divergence payload measured in nats.  Mutual information is a KL divergence of joint versus
product state, so the same real structure is used here. -/
abbrev KLDivergencePayload : Type := ℝ

/-- Mutual-information payload, represented in nats. -/
abbrev MutualInformationPayload : Type := ℝ

/-- Forgetful identification: the mutual-information payload is the KL payload in nats. -/
def payloadAsMutualInformation (kl : KLDivergencePayload) : MutualInformationPayload :=
  kl

/-- A complex action with prescribed real part and imaginary information action `S_I`. -/
def complexActionFromPayload (S_R S_I : ℝ) : ℂ :=
  ⟨S_R, S_I⟩

@[simp]
theorem complexActionFromPayload_re (S_R S_I : ℝ) :
    (complexActionFromPayload S_R S_I).re = S_R :=
  rfl

@[simp]
theorem complexActionFromPayload_im (S_R S_I : ℝ) :
    (complexActionFromPayload S_R S_I).im = S_I :=
  rfl

/-- The KL payload represented by a complex action is its Landauer/Brillouin information readout
`S_I / hbar`. -/
def complexActionKLPayload (hbar S_R S_I : ℝ) : KLDivergencePayload :=
  complexActionNats hbar (complexActionFromPayload S_R S_I).im

/-- The complex-action KL payload is definitionally `S_I / hbar`. -/
theorem complexActionKLPayload_eq (hbar S_R S_I : ℝ) :
    complexActionKLPayload hbar S_R S_I = S_I / hbar := by
  rfl

/-- A single absorption/emission cycle: a bounded absorbed bosonic payload and an emitted bosonic payload
equal to the KL information read from the complex action. -/
structure AbsorptionEmissionCycle where
  /-- Occupation parameter of the fermion mode. -/
  occupationParameter : ℝ
  /-- Real part of the complex action. -/
  actionReal : ℝ
  /-- Imaginary part of the complex action. -/
  actionImaginary : ℝ
  /-- The value of `hbar` used to read information in nats. -/
  hbar : ℝ
  /-- Payload encoded in the absorbed bosonic excitation. -/
  absorbedPayload : KLDivergencePayload
  /-- Payload encoded in the emitted bosonic excitation. -/
  emittedPayload : KLDivergencePayload
  /-- Absorption respects the positive Pauli vacancy. -/
  absorption_allowed : BosonAbsorptionAllowed occupationParameter absorbedPayload
  /-- Emission includes the KL information obtained from the complex action. -/
  emitted_eq_complexActionKL : emittedPayload = complexActionKLPayload hbar actionReal actionImaginary

/-- The complex action associated to an absorption/emission cycle. -/
def AbsorptionEmissionCycle.complexAction (C : AbsorptionEmissionCycle) : ℂ :=
  complexActionFromPayload C.actionReal C.actionImaginary

/-- The emitted boson records exactly the complex-action KL payload. -/
theorem AbsorptionEmissionCycle.emittedPayload_eq_complexActionNats (C : AbsorptionEmissionCycle) :
    C.emittedPayload = complexActionNats C.hbar C.complexAction.im := by
  simpa [AbsorptionEmissionCycle.complexAction, complexActionKLPayload]
    using C.emitted_eq_complexActionKL

/-! ## C. Channel stress of the emitted KL / mutual-information payload -/

/-- The emitted KL payload, divided by a time window and converted to bits/time. -/
def AbsorptionEmissionCycle.emittedKLBitsPerTime
    (C : AbsorptionEmissionCycle) (Δt : ℝ) : ℝ :=
  klInformationRateBits (C.emittedPayload / Δt)

/-- The same emitted payload viewed as mutual information.  Mutual information is
a KL divergence from a joint state to the product of its marginals, so it uses
the same nat-to-bit conversion. -/
def AbsorptionEmissionCycle.emittedMutualInformationBitsPerTime
    (C : AbsorptionEmissionCycle) (Δt : ℝ) : ℝ :=
  mutualInformationRateBits (payloadAsMutualInformation C.emittedPayload / Δt)

/-- For this structure, KL throughput and mutual-information throughput are the
same bit rate. -/
theorem AbsorptionEmissionCycle.emittedMutualInformationBitsPerTime_eq_KL
    (C : AbsorptionEmissionCycle) (Δt : ℝ) :
    C.emittedMutualInformationBitsPerTime Δt = C.emittedKLBitsPerTime Δt := by
  rfl

/-- Non-negative imaginary action gives a non-negative emitted KL payload. -/
theorem AbsorptionEmissionCycle.emittedPayload_nonneg_of_actionImaginary_nonneg
    (C : AbsorptionEmissionCycle) (hℏ : 0 < C.hbar)
    (hSI : 0 ≤ C.actionImaginary) :
    0 ≤ C.emittedPayload := by
  rw [C.emitted_eq_complexActionKL, complexActionKLPayload_eq]
  exact div_nonneg hSI hℏ.le

/-- Non-negative imaginary action over a positive time window gives a
non-negative emitted KL rate. -/
theorem AbsorptionEmissionCycle.emittedKLRate_nonneg_of_actionImaginary_nonneg
    (C : AbsorptionEmissionCycle) {Δt : ℝ} (hΔt : 0 < Δt)
    (hℏ : 0 < C.hbar) (hSI : 0 ≤ C.actionImaginary) :
    0 ≤ C.emittedPayload / Δt :=
  div_nonneg (C.emittedPayload_nonneg_of_actionImaginary_nonneg hℏ hSI) hΔt.le

/-- The emitted KL payload, over a time window, as a capacity-limited
information channel. -/
def AbsorptionEmissionCycle.emissionKLChannel
    (C : AbsorptionEmissionCycle) (capacityBitsPerTime Δt : ℝ)
    (hC : 0 < capacityBitsPerTime) (hRate : 0 ≤ C.emittedPayload / Δt) :
    InformationChannel :=
  channelFromKLRate capacityBitsPerTime (C.emittedPayload / Δt) hC hRate

/-- The emitted mutual-information payload, over a time window, as a
capacity-limited information channel. -/
def AbsorptionEmissionCycle.emissionMutualInformationChannel
    (C : AbsorptionEmissionCycle) (capacityBitsPerTime Δt : ℝ)
    (hC : 0 < capacityBitsPerTime)
    (hRate : 0 ≤ payloadAsMutualInformation C.emittedPayload / Δt) :
    InformationChannel :=
  channelFromMutualInformationRate capacityBitsPerTime
    (payloadAsMutualInformation C.emittedPayload / Δt) hC hRate

/-- The KL-emission channel is within capacity exactly when the emitted KL
nat-rate is below `capacity · log 2`. -/
theorem AbsorptionEmissionCycle.emissionKLChannel_withinCapacity_iff
    (C : AbsorptionEmissionCycle) (capacityBitsPerTime Δt : ℝ)
    (hC : 0 < capacityBitsPerTime) (hRate : 0 ≤ C.emittedPayload / Δt) :
    WithinCapacity (C.emissionKLChannel capacityBitsPerTime Δt hC hRate)
      ↔ C.emittedPayload / Δt ≤ capacityBitsPerTime * Real.log 2 := by
  unfold AbsorptionEmissionCycle.emissionKLChannel
  exact klChannel_withinCapacity_iff_natsRate_le
    capacityBitsPerTime (C.emittedPayload / Δt) hC hRate

/-- The mutual-information emission channel has the same capacity condition,
because the mutual-information payload is represented as the KL payload in
nats. -/
theorem AbsorptionEmissionCycle.emissionMutualInformationChannel_withinCapacity_iff
    (C : AbsorptionEmissionCycle) (capacityBitsPerTime Δt : ℝ)
    (hC : 0 < capacityBitsPerTime)
    (hRate : 0 ≤ payloadAsMutualInformation C.emittedPayload / Δt) :
    WithinCapacity
        (C.emissionMutualInformationChannel capacityBitsPerTime Δt hC hRate)
      ↔ payloadAsMutualInformation C.emittedPayload / Δt
          ≤ capacityBitsPerTime * Real.log 2 := by
  unfold AbsorptionEmissionCycle.emissionMutualInformationChannel
  exact mutualChannel_withinCapacity_iff_natsRate_le
    capacityBitsPerTime (payloadAsMutualInformation C.emittedPayload / Δt) hC hRate

/-- Rewriting the emitted-channel capacity condition through the complex-action
readout: `emittedPayload = S_I / ℏ`. -/
theorem AbsorptionEmissionCycle.emissionKLChannel_withinCapacity_iff_complexActionRate
    (C : AbsorptionEmissionCycle) (capacityBitsPerTime Δt : ℝ)
    (hC : 0 < capacityBitsPerTime) (hRate : 0 ≤ C.emittedPayload / Δt) :
    WithinCapacity (C.emissionKLChannel capacityBitsPerTime Δt hC hRate)
      ↔ (C.actionImaginary / C.hbar) / Δt
          ≤ capacityBitsPerTime * Real.log 2 := by
  rw [C.emissionKLChannel_withinCapacity_iff capacityBitsPerTime Δt hC hRate]
  rw [C.emitted_eq_complexActionKL, complexActionKLPayload_eq]

/-! ## D. Yang-Baxter convolution representative for the payload -/

/-- The scalar convolution operator that has an information payload through the existing symmetric
braid solution.  The payload is not the braid generator; it scales the identity on the target matrix
algebra, while the braid structure is supplied by `symmetricMatrixBraid1/2`. -/
def klBraidConvolutionOperator (payload : KLDivergencePayload) (which : Bool) :
    ConvolutionAlgebra (R := ℂ) (A := Matrix (Fin 3) (Fin 3) ℂ) (C := ℂ) :=
  scalarConvolutionMap (K := ℂ)
    ((payload : ℂ) • if which then symmetricMatrixBraid1 else symmetricMatrixBraid2)

/-- If two payload-scaled braid generators satisfy the braid-form Yang-Baxter relation, their scalar
convolution lifts satisfy the convolution Yang-Baxter relation.  This is the reusable conditional target for
future KL-valued geometric push-pull operators. -/
theorem klBraidConvolution_yangBaxter_of_payload_braid
    (payload : KLDivergencePayload)
    (h : YangBaxter ((payload : ℂ) • symmetricMatrixBraid1)
        ((payload : ℂ) • symmetricMatrixBraid2)) :
    YangBaxter (klBraidConvolutionOperator payload true)
      (klBraidConvolutionOperator payload false) := by
  simpa [klBraidConvolutionOperator] using
    (scalarConvolutionMap_yangBaxter (K := ℂ)
      (B := Matrix (Fin 3) (Fin 3) ℂ) h)

/-- At unit payload, the existing symmetric permutation-matrix braid gives a concrete Yang-Baxter
convolution solution. -/
theorem unitPayload_klBraidConvolution_yangBaxter :
    YangBaxter (klBraidConvolutionOperator 1 true) (klBraidConvolutionOperator 1 false) := by
  simpa [klBraidConvolutionOperator] using
    symmetric_permutation_matrix_scalar_convolution_yangBaxter

/-! ## E. Wilson, zitterbewegung, and critical-crossing interfaces -/

/-- A half-integer Wilson line has the fermion exchange sign `-1`. -/
theorem wilsonLoop_fermion_exchange_sign
    (k : ℕ) (hk : 0 < k) (a : Fin k) (ha : (a.val : ℝ) ^ 2 = k) :
    wilsonTopologicalSpin k a = -1 :=
  wilsonTopologicalSpin_fermion k hk a ha

/-- The Wilson fermion sign matches the three-turn spinor holonomy of the structured Dirac region. -/
theorem wilsonLoop_matches_threeNodule_spinorHolonomy
    (k : ℕ) (hk : 0 < k) (a : Fin k) (ha : (a.val : ℝ) ^ 2 = k) :
    wilsonTopologicalSpin k a =
      HorizonCell.lessDiracTrefoilPhaseRegion.ThreeNodulePhaseRegion.spinorThreeTurnHolonomy :=
  HorizonCell.lessDiracTrefoilPhaseRegion.ThreeNodulePhaseRegion.wilson_fermion_spin_matches_threeTurnHolonomy
    k hk a ha

/-- Algebraic zitterbewegung marker: the Dirac velocity matrix `alpha` and mass sign matrix `beta`
anticommute.  The time-domain oscillation theorem is not asserted here; this is the checked Clifford-algebra
source of the positive/negative energy interference channel. -/
theorem dirac_alpha_beta_zitterbewegung_marker (s : Matrix (Fin 2) (Fin 2) ℂ) :
    diracAlpha s * diracBeta + diracBeta * diracAlpha s = 0 :=
  diracAlpha_beta_anticomm s

/-- Critical-crossing marker available in the repo: a strictly monotone linearized scalar crossing zero has
opposite boundary signs, hence an index jump.  This is a checked bifurcation/critical-point structure, not a
full Hopf-bifurcation normal form. -/
theorem criticalCrossing_signs_differ (alpha : ℝ → ℝ) (epsilon0 delta : ℝ)
    (hdelta : 0 < delta) (hmono : StrictMono alpha) (hzero : alpha epsilon0 = 0) :
    SignType.sign (alpha (epsilon0 - delta)) ≠ SignType.sign (alpha (epsilon0 + delta)) :=
  bifurcation_signs_differ alpha epsilon0 delta hdelta hmono hzero

/-! ## F. Assembled checked capability -/

/-- The checked capability provided by the current repo: Pauli-bounded absorption, complex-action KL readout,
emitted KL payload, a concrete unit-payload Yang-Baxter convolution structure, Wilson fermion sign, Dirac
zitterbewegung algebra, and critical crossing. -/
theorem fermion_boson_information_cycle_capability
    (C : AbsorptionEmissionCycle) (s : Matrix (Fin 2) (Fin 2) ℂ) :
    BosonAbsorptionAllowed C.occupationParameter C.absorbedPayload
      ∧ C.emittedPayload = complexActionNats C.hbar C.complexAction.im
      ∧ YangBaxter (klBraidConvolutionOperator 1 true) (klBraidConvolutionOperator 1 false)
      ∧ diracAlpha s * diracBeta + diracBeta * diracAlpha s = 0 :=
  ⟨C.absorption_allowed,
   C.emittedPayload_eq_complexActionNats,
   unitPayload_klBraidConvolution_yangBaxter,
   dirac_alpha_beta_zitterbewegung_marker s⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.BosonInformationTransfer

end
