/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Particles.StandardModel.YukawaDimensionalAnalysis
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass
public import Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
public import Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree

/-!
# Standard Model Yukawa coupling bridge

`YukawaDimensionalAnalysis` proves the engineering-dimension constraints for the Standard Model Yukawa
operator.  `Yukawa.MassDecoherenceProportionality` and `Yukawa.SeesawMass` use the algebraic mass relation
`m_f = y_f v / sqrt 2`.

This file adds the missing named equations between those layers:

* the two existing `yukawaMass` definitions agree;
* recovering `y_f = sqrt 2 * m_f / v` is a two-sided inverse when `v ≠ 0`;
* the physical Higgs-fermion coupling satisfies `g_hff = m_f/v = y_f/sqrt 2`;
* the matrix relation `M = (v/sqrt 2) • Y` is entrywise the same Yukawa mass equation;
* the generated sterile/right-handed neutrino singlet makes the Dirac neutrino Yukawa channel
  gauge-neutral and feeds the existing Type-I seesaw matrix;
* the three-flavor neutrino spectrum in `Particles.NeutrinoModel` is linked back to those same sterile
  Dirac-neutrino Yukawa channels, so the seesaw-generated `Δm²₂₁`, `Δm²₃₁` layer and the gauge-singlet
  channels are one checked package;
* the dimension facts and algebraic facts can be used as one bundled Standard Model constraint.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling

open Physlib.Particles.StandardModel.YukawaDimensionalAnalysis
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel


/-- The decoherence bridge and seesaw bridge use the same Standard Model Yukawa mass equation. -/
lemma yukawaMass_definitions_agree (y v : ℝ) :
    yukawaMass y v
      = Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass y v := by
  rfl


/-- The physical Higgs-fermion coupling written as `m_f / v`. -/
def higgsFermionCouplingFromMass (m v : ℝ) : ℝ := m / v

/-- The same physical Higgs-fermion coupling written as `y_f / sqrt 2`. -/
def higgsFermionCouplingFromYukawa (y : ℝ) : ℝ := y / Real.sqrt 2

/-- The Yukawa recovery map is a left inverse of `m_f = y_f v / sqrt 2`: recovering the coupling from
the generated mass returns the original `y_f` when `v ≠ 0`. -/
lemma yukawaCoupling_yukawaMass (y v : ℝ) (hv : v ≠ 0) :
    yukawaCoupling (yukawaMass y v) v = y := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold yukawaCoupling yukawaMass
  field_simp [hv, hsqrt2]

/-- The same inverse statement for the seesaw module's Yukawa mass carrier. -/
lemma yukawaCoupling_seesawYukawaMass (y v : ℝ) (hv : v ≠ 0) :
    yukawaCoupling
        (Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass y v) v = y := by
  rw [← yukawaMass_definitions_agree]
  exact yukawaCoupling_yukawaMass y v hv

/-- After electroweak symmetry breaking, the Higgs-fermion coupling from the generated mass is
`g_hff = m_f/v = y_f/sqrt 2`. -/
lemma higgsFermionCouplingFromMass_yukawaMass_eq (y v : ℝ) (hv : v ≠ 0) :
    higgsFermionCouplingFromMass (yukawaMass y v) v = higgsFermionCouplingFromYukawa y := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold higgsFermionCouplingFromMass higgsFermionCouplingFromYukawa yukawaMass
  field_simp [hv, hsqrt2]

/-- The same `g_hff = y_f/sqrt 2` identity using the seesaw module's mass carrier. -/
lemma higgsFermionCouplingFromMass_seesawYukawaMass_eq (y v : ℝ) (hv : v ≠ 0) :
    higgsFermionCouplingFromMass
        (Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass y v) v
      = higgsFermionCouplingFromYukawa y := by
  rw [← yukawaMass_definitions_agree]
  exact higgsFermionCouplingFromMass_yukawaMass_eq y v hv


/-- A Standard Model Yukawa mass matrix: `M = (v/sqrt 2) • Y`. -/
def yukawaMassMatrix {ι κ : Type*} (Y : Matrix ι κ ℝ) (v : ℝ) : Matrix ι κ ℝ :=
  (v / Real.sqrt 2) • Y

/-- Entrywise, `M = (v/sqrt 2) • Y` is exactly the scalar Yukawa mass equation. -/
@[simp] lemma yukawaMassMatrix_apply {ι κ : Type*} (Y : Matrix ι κ ℝ) (v : ℝ) (i : ι) (j : κ) :
    yukawaMassMatrix Y v i j = yukawaMass (Y i j) v := by
  simp [yukawaMassMatrix, yukawaMass]
  ring

/-- The Higgs-fermion coupling matrix `M/v` recovers `Y/sqrt 2` entrywise when `v ≠ 0`. -/
lemma yukawaMassMatrix_coupling_apply {ι κ : Type*} (Y : Matrix ι κ ℝ) (v : ℝ)
    (hv : v ≠ 0) (i : ι) (j : κ) :
    higgsFermionCouplingFromMass (yukawaMassMatrix Y v i j) v
      = higgsFermionCouplingFromYukawa (Y i j) := by
  rw [yukawaMassMatrix_apply]
  exact higgsFermionCouplingFromMass_yukawaMass_eq (Y i j) v hv


/-- The neutral component of the conjugate Higgs doublet `\tilde H` has `T₃ = +1/2`. -/
def conjugateHiggsNeutralWeakIsospin3 : ℚ := 1 / 2

/-- The conjugate Higgs doublet has weak hypercharge `Y = -1` in the `Q = T₃ + Y/2`
convention used throughout this development. -/
def conjugateHiggsHypercharge : ℚ := -1

/-- The neutral conjugate-Higgs component has electric charge zero. -/
def conjugateHiggsNeutralElectricCharge : ℚ :=
  gellMannNishijima conjugateHiggsNeutralWeakIsospin3 conjugateHiggsHypercharge

lemma conjugateHiggsNeutralElectricCharge_zero :
    conjugateHiggsNeutralElectricCharge = 0 := by
  norm_num [conjugateHiggsNeutralElectricCharge, conjugateHiggsNeutralWeakIsospin3,
    conjugateHiggsHypercharge, gellMannNishijima]

/-- Hypercharge of the Dirac adjoint of a generation-labelled fermion. -/
def diracAdjointHypercharge (f : ThreeGenerationWeylFermion) : ℚ :=
  - (threeGenerationQuantumNumbers f).hypercharge

/-- Electric charge of the Dirac adjoint of a generation-labelled fermion. -/
def diracAdjointElectricCharge (f : ThreeGenerationWeylFermion) : ℚ :=
  - (threeGenerationQuantumNumbers f).electricCharge

/-- Lepton number of the Dirac adjoint of a generation-labelled fermion. -/
def diracAdjointLeptonNumber (f : ThreeGenerationWeylFermion) : ℚ :=
  - (threeGenerationQuantumNumbers f).leptonNumber

/-- The hypercharge carried by the Dirac-neutrino Yukawa channel
`\bar L · \tilde H · ν_R`. -/
def diracNeutrinoYukawaHypercharge (flavor : NeutrinoFlavor) : ℚ :=
  diracAdjointHypercharge (neutrinoParticle flavor)
    + conjugateHiggsHypercharge
    + (rightHandedNeutrinoQuantumNumbers flavor).hypercharge

/-- The electric charge carried by the neutral Dirac-neutrino Yukawa channel. -/
def diracNeutrinoYukawaElectricCharge (flavor : NeutrinoFlavor) : ℚ :=
  diracAdjointElectricCharge (neutrinoParticle flavor)
    + conjugateHiggsNeutralElectricCharge
    + (rightHandedNeutrinoQuantumNumbers flavor).electricCharge

/-- The total lepton number carried by the Dirac-neutrino Yukawa channel. -/
def diracNeutrinoYukawaLeptonNumber (flavor : NeutrinoFlavor) : ℚ :=
  diracAdjointLeptonNumber (neutrinoParticle flavor)
    + (0 : ℚ)
    + (rightHandedNeutrinoQuantumNumbers flavor).leptonNumber

/-- The active neutrino in `L` has the generated weak-doublet quantum numbers. -/
lemma diracNeutrino_activeLeft_hasQuantumNumbers (flavor : NeutrinoFlavor) :
    HasThreeGenerationComputedQuantumNumbers (neutrinoParticle flavor)
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  neutrinoParticle_hasQuantumNumbers flavor

/-- The sterile right-handed neutrino in the Dirac Yukawa channel is a generated gauge singlet. -/
lemma diracNeutrino_rightSinglet_hasQuantumNumbers (flavor : NeutrinoFlavor) :
    HasRightHandedNeutrinoQuantumNumbers flavor 0 0 0 0 1 (1 / 2)
      .singlet .singlet .right :=
  rightHandedNeutrino_hasQuantumNumbers flavor

/-- The Dirac-neutrino Yukawa channel is `U(1)_Y` neutral:
`Y(\bar L) + Y(\tilde H) + Y(ν_R) = +1 - 1 + 0 = 0`. -/
lemma diracNeutrinoYukawaHypercharge_zero (flavor : NeutrinoFlavor) :
    diracNeutrinoYukawaHypercharge flavor = 0 := by
  cases flavor <;>
    simp [diracNeutrinoYukawaHypercharge, diracAdjointHypercharge, neutrinoParticle,
      neutrinoGeneration, threeGenerationQuantumNumbers, leftElectronNeutrinoState,
      rightHandedNeutrinoQuantumNumbers, fermionQuantumNumbers, fermionHypercharge,
      su5AntifundHyperchargeFromBlock, su5IndexIsColour, conjugateHiggsHypercharge]

/-- The neutral component channel is electrically neutral:
`Q(\bar ν_L) + Q(\tilde H^0) + Q(ν_R) = 0`. -/
lemma diracNeutrinoYukawaElectricCharge_zero (flavor : NeutrinoFlavor) :
    diracNeutrinoYukawaElectricCharge flavor = 0 := by
  cases flavor <;>
    simp [diracNeutrinoYukawaElectricCharge, diracAdjointElectricCharge, neutrinoParticle,
      neutrinoGeneration, threeGenerationQuantumNumbers, leftElectronNeutrinoState,
      rightHandedNeutrinoQuantumNumbers, fermionQuantumNumbers, fermionElectricCharge,
      fermionWeakIsospin3, fermionHypercharge, su5AntifundWeakIsospin3FromBlock,
      su5AntifundHyperchargeFromBlock, su5IndexIsColour, conjugateHiggsNeutralElectricCharge,
      conjugateHiggsNeutralWeakIsospin3, conjugateHiggsHypercharge, gellMannNishijima]

/-- The Dirac-neutrino Yukawa channel preserves total lepton number:
`L(\bar L) + L(\tilde H) + L(ν_R) = -1 + 0 + 1 = 0`. -/
lemma diracNeutrinoYukawaLeptonNumber_zero (flavor : NeutrinoFlavor) :
    diracNeutrinoYukawaLeptonNumber flavor = 0 := by
  cases flavor <;>
    simp [diracNeutrinoYukawaLeptonNumber, diracAdjointLeptonNumber, neutrinoParticle,
      neutrinoGeneration, threeGenerationQuantumNumbers, leftElectronNeutrinoState,
      rightHandedNeutrinoQuantumNumbers, fermionQuantumNumbers, fermionLeptonNumber,
      su5IndexIsColour]

/-- The neutrino Dirac mass is the same Standard-Model Yukawa mass carrier used elsewhere:
`m_D = y_ν v / sqrt 2`. -/
noncomputable def neutrinoDiracMass (yν v : ℝ) : ℝ := yukawaMass yν v

lemma neutrinoDiracMass_eq_yukawaMass (yν v : ℝ) :
    neutrinoDiracMass yν v = yukawaMass yν v := rfl

lemma neutrinoDiracMass_eq_seesawYukawaMass (yν v : ℝ) :
    neutrinoDiracMass yν v =
      Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass yν v := by
  exact yukawaMass_definitions_agree yν v

/-- The sterile-singlet Dirac mass is the off-diagonal mass in the existing Type-I seesaw theorem. -/
lemma sterileNeutrino_yukawa_seesaw_bridge (yν v M_N : ℝ) :
    (Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawMatrix
        (neutrinoDiracMass yν v) M_N).trace = M_N
      ∧ (Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawMatrix
          (neutrinoDiracMass yν v) M_N).det = -(neutrinoDiracMass yν v) ^ 2
      ∧ Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawEigenPlus
          (neutrinoDiracMass yν v) M_N
        + Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawEigenMinus
          (neutrinoDiracMass yν v) M_N = M_N
      ∧ Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawEigenPlus
          (neutrinoDiracMass yν v) M_N
        * (- Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawEigenMinus
          (neutrinoDiracMass yν v) M_N)
          = yν ^ 2 * v ^ 2 / 2 := by
  rw [neutrinoDiracMass_eq_seesawYukawaMass]
  exact Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawa_seesaw yν v M_N

/-- The complete checked Standard-Model extension supplied by the sterile singlet: the state is a
right-handed gauge singlet, the Dirac Yukawa channel is neutral under the tracked quantum numbers,
and the resulting Dirac mass feeds the existing Type-I seesaw matrix. -/
def HasDiracNeutrinoYukawaSingletBridge (yν v M_N : ℝ) : Prop :=
  HasSterileRightHandedNeutrinoSingletComputations
    ∧ (∀ flavor : NeutrinoFlavor, diracNeutrinoYukawaHypercharge flavor = 0)
    ∧ (∀ flavor : NeutrinoFlavor, diracNeutrinoYukawaElectricCharge flavor = 0)
    ∧ (∀ flavor : NeutrinoFlavor, diracNeutrinoYukawaLeptonNumber flavor = 0)
    ∧ conjugateHiggsNeutralElectricCharge = 0
    ∧ neutrinoDiracMass yν v =
        Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass yν v
    ∧ (Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawMatrix
        (neutrinoDiracMass yν v) M_N).trace = M_N
    ∧ (Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawMatrix
        (neutrinoDiracMass yν v) M_N).det = -(neutrinoDiracMass yν v) ^ 2
    ∧ Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawEigenPlus
        (neutrinoDiracMass yν v) M_N
      * (- Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.seesawEigenMinus
        (neutrinoDiracMass yν v) M_N)
        = yν ^ 2 * v ^ 2 / 2

lemma diracNeutrinoYukawaSingletBridge_checked (yν v M_N : ℝ) :
    HasDiracNeutrinoYukawaSingletBridge yν v M_N := by
  rcases sterileNeutrino_yukawa_seesaw_bridge yν v M_N with
    ⟨htrace, hdet, _hsum, hlever⟩
  exact ⟨sterileRightHandedNeutrinoSingletComputations_checked,
    diracNeutrinoYukawaHypercharge_zero,
    diracNeutrinoYukawaElectricCharge_zero,
    diracNeutrinoYukawaLeptonNumber_zero,
    conjugateHiggsNeutralElectricCharge_zero,
    neutrinoDiracMass_eq_seesawYukawaMass yν v,
    htrace, hdet, hlever⟩

/-- Three sterile Dirac-neutrino Yukawa channels and the three-flavor seesaw
oscillation spectrum are the same package: each generation is a gauge-neutral
right-handed singlet channel, and the shared inputs generate the three light
masses whose `Δm²` splittings are computed in `Particles.NeutrinoModel`. -/
def HasThreeFlavorDiracNeutrinoYukawaSeesawOscillationBridge
    (D : ThreeFlavorSeesawData) : Prop :=
  HasThreeFlavorSeesawOscillationBridge D
    ∧ HasDiracNeutrinoYukawaSingletBridge D.y1 D.v D.M1
    ∧ HasDiracNeutrinoYukawaSingletBridge D.y2 D.v D.M2
    ∧ HasDiracNeutrinoYukawaSingletBridge D.y3 D.v D.M3

/-- The three-flavor bridge follows from the lower seesaw/oscillation theorem in
`Particles.NeutrinoModel` and the existing sterile-singlet Dirac Yukawa bridge
for each generation. -/
lemma threeFlavorDiracNeutrinoYukawaSeesawOscillationBridge_checked
    (D : ThreeFlavorSeesawData) :
    HasThreeFlavorDiracNeutrinoYukawaSeesawOscillationBridge D :=
  ⟨threeFlavorSeesawOscillationBridge_checked D,
    diracNeutrinoYukawaSingletBridge_checked D.y1 D.v D.M1,
    diracNeutrinoYukawaSingletBridge_checked D.y2 D.v D.M2,
    diracNeutrinoYukawaSingletBridge_checked D.y3 D.v D.M3⟩


/-- The Standard Model Yukawa coupling is dimensionless, generates a mass dimension after multiplication
by the Higgs VEV, and gives a dimensionless physical Higgs-fermion coupling. -/
lemma standardModelYukawa_dimensional_requirements :
    yukawaCouplingDim4 = 1
      ∧ yukawaCouplingDim4 * higgsVEVDim4 = massParameterDim4
      ∧ massParameterDim4 / higgsVEVDim4 = 1 := by
  exact ⟨yukawaCouplingDim4_eq_one, generatedFermionDim4_eq_mass,
    higgsFermionCouplingDim4_eq_one⟩

/-- Bundled algebraic Standard Model relation: from one dimensionless coupling `y_f`, the generated mass
is `y_f v/sqrt 2`, the recovered coupling is again `y_f`, and the Higgs-fermion coupling is
`y_f/sqrt 2`. -/
lemma standardModelYukawa_algebraic_requirements (y v : ℝ) (hv : v ≠ 0) :
    yukawaMass y v
        = Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass y v
      ∧ yukawaCoupling (yukawaMass y v) v = y
      ∧ higgsFermionCouplingFromMass (yukawaMass y v) v = higgsFermionCouplingFromYukawa y := by
  exact ⟨yukawaMass_definitions_agree y v, yukawaCoupling_yukawaMass y v hv,
    higgsFermionCouplingFromMass_yukawaMass_eq y v hv⟩

end Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling

end

end
