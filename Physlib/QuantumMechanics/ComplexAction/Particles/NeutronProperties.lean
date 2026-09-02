/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
public import Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
meta import Zil

/-!
# Neutron particle model: udd flavor, neutral baryon, magnetic moment, beta decay

This file packages the neutron as a named hadron model, reusing the existing
repository infrastructure instead of redefining the hadron equations:

* `HadronFlavorModel.neutron = [up, down, down]` supplies the quark content.
  From it, `listCharge neutron = 0`, `I3 = -1/2`, `Y = 1`, and strong
  Gell-Mann--Nishijima are computed.
* `HadronSpinStatistics.baryon_is_fermion` supplies the three-quark fermion
  exchange phase.
* `BaryonLeptonNumberConservation.beta_decay_conserves` supplies the exact
  additive quantum-number equation `n = p + e^- + anti-nu_e`.
* `ProtonProperties.chargeRadiusSqFromSlope` supplies the form-factor radius
  convention, reused for the neutron's negative charge radius squared.
* `Yukawa.StandardModelYukawaCoupling` supplies the current-quark mass relation
  `m_q = y_q v / sqrt 2`; the neutron mass then decomposes into the two down
  current masses, one up current mass, and a residual strong-sector mass.
* `StrongInteractionColorOctet` supplies the `Z/3` colour-centre confinement
  signature; the neutron's total `udd` winding is zero, hence colour-centre
  trivial.

The numeric constants are measured particle data. The formal content is the
checked compatibility: the same neutron object is a neutral `udd` baryon, a
fermion, has nonzero negative magnetic moment, has a positive beta-decay mass
window, and satisfies the existing conservation-law equation.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
open Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties

/-! ## A. Neutron constants and the standard neutron instance -/

/-- Neutron mass `m_n approx 939.565 MeV/c^2`. -/
noncomputable def neutronMass : ℝ := 939.565

/-- Neutron-proton mass splitting `m_n - m_p`. -/
noncomputable def neutronProtonMassDifference : ℝ := neutronMass - protonMass

/-- Neutron g-factor in nuclear magneton normalization, `g_n approx -3.8263`. -/
noncomputable def neutronGFactor : ℝ := -3.8263

/-- Neutron magnetic dipole moment `mu_n = g_n/2 approx -1.91315 mu_N`. -/
noncomputable def neutronMagneticMoment : ℝ := neutronGFactor / 2

/-- The neutron's magnetic response in the same `g = 2(1+a)` normalization used
for the anomalous-moment API. For a neutral composite baryon this is a compact
normalization of the internal quark-current response, not a point-charge Dirac
prediction. -/
noncomputable def neutronMagneticAnomalyScale : ℝ := neutronGFactor / 2 - 1

/-- Neutron mean life, in seconds, `tau_n approx 879.4 s`. -/
noncomputable def neutronMeanLife : ℝ := 879.4

/-- Neutron electric dipole moment experimental upper-bound scale, in `e cm`. -/
noncomputable def neutronEDMupperBound : ℝ := 1.8e-26

/-- Neutron mean-square charge radius, in `fm^2`. The neutron is neutral, but
its internal charge distribution has a nonzero slope. -/
noncomputable def neutronChargeRadiusSq : ℝ := -0.1161

/-- The standard neutron particle object: quark model, additive quantum numbers,
mass, magnetic moment, and lifetime in one record. -/
noncomputable def standardNeutron : HadronParticleModel where
  quarkContent := neutron
  quantumNumbers :=
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron
  massMeV := neutronMass
  magneticMomentNuclearMagnetons := neutronMagneticMoment
  meanLifeSeconds := neutronMeanLife

/-! ## B. Flavor, spin-statistics, and Gell-Mann--Nishijima checks -/

/-- The neutron quark content is `udd`. -/
lemma neutron_quarkContent : neutron = [QuarkFlavor.up, QuarkFlavor.down, QuarkFlavor.down] := rfl

/-- The neutron is electrically neutral, derived from `udd`. -/
lemma neutron_charge_zero : listCharge neutron = 0 := neutron_charge

/-- The neutron's baryon number is one: three quarks, each with `B = 1/3`. -/
lemma neutron_baryonNumber_one :
    QuarkFlavor.baryonNumber QuarkFlavor.up
      + QuarkFlavor.baryonNumber QuarkFlavor.down
      + QuarkFlavor.baryonNumber QuarkFlavor.down = 1 :=
  baryon_baryonNumber QuarkFlavor.up QuarkFlavor.down QuarkFlavor.down

/-- The neutron has `I3 = -1/2` and strong hypercharge `Y = 1`. -/
lemma neutron_isospin_hypercharge :
    listIsospinT3 neutron = -1 / 2 ∧ listHypercharge neutron = 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [listIsospinT3, neutron, QuarkFlavor.isospinT3]
  · norm_num [listHypercharge, neutron, QuarkFlavor.hypercharge, QuarkFlavor.baryonNumber,
      QuarkFlavor.strangeness, QuarkFlavor.charmness, QuarkFlavor.bottomness,
      QuarkFlavor.topness, quarkBaryonNumber]

/-- Strong Gell-Mann--Nishijima for the neutron, inherited from the composite
hadron theorem. -/
lemma neutron_gellMannNishijima :
    listCharge neutron = listIsospinT3 neutron + listHypercharge neutron / 2 :=
  gmn_strong_baryon neutron

/-- The neutron is a three-quark fermion. -/
lemma neutron_is_fermion : compositeTwist 3 = -1 := baryon_is_fermion

/-- The record's additive electric charge agrees with the computed flavor
charge. -/
lemma standardNeutron_charge_matches_flavor :
    listCharge standardNeutron.quarkContent = standardNeutron.quantumNumbers.electric := by
  simp [standardNeutron, neutron_charge_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron]

/-- The record's additive baryon number is the baryon value `1`. -/
lemma standardNeutron_baryon_number : standardNeutron.quantumNumbers.baryon = 1 := by
  simp [standardNeutron,
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron]

/-! ## C. Magnetic structure, finite charge distribution, and beta decay -/

/-- The neutron g-factor is twice its magnetic moment in nuclear magnetons. -/
lemma neutronGFactor_eq_two_mul_moment : neutronGFactor = 2 * neutronMagneticMoment := by
  unfold neutronMagneticMoment; ring

/-- The same g-factor normalization used by the anomalous-moment module recovers
the neutron g-factor from `neutronMagneticAnomalyScale`. -/
lemma neutronGFactor_eq_gFactor_anomalyScale :
    gFactor neutronMagneticAnomalyScale = neutronGFactor := by
  unfold gFactor neutronMagneticAnomalyScale; ring

/-- The neutron magnetic moment is nonzero. -/
lemma neutronMagneticMoment_nonzero : neutronMagneticMoment ≠ 0 := by
  unfold neutronMagneticMoment neutronGFactor; norm_num

/-- The neutron magnetic moment is negative in nuclear magnetons. -/
lemma neutronMagneticMoment_negative : neutronMagneticMoment < 0 := by
  unfold neutronMagneticMoment neutronGFactor; norm_num

/-- The neutron is neutral but magnetic: zero flavor charge, nonzero magnetic
moment. -/
lemma neutron_neutral_but_magnetic : listCharge neutron = 0 ∧ neutronMagneticMoment ≠ 0 :=
  ⟨neutron_charge_zero, neutronMagneticMoment_nonzero⟩

/-- The neutron charge-radius squared is negative. -/
lemma neutronChargeRadiusSq_negative : neutronChargeRadiusSq < 0 := by
  unfold neutronChargeRadiusSq; norm_num

/-- The neutron charge-radius squared is expressed using the existing
form-factor slope convention `r^2 = -6 G'(0)`. -/
lemma neutronChargeRadiusSq_from_formFactorSlope :
    chargeRadiusSqFromSlope (0.1161 / 6) = neutronChargeRadiusSq := by
  unfold chargeRadiusSqFromSlope neutronChargeRadiusSq; norm_num

/-- The neutron EDM bound is a positive experimental upper-bound scale. -/
lemma neutronEDM_bound_positive : (0 : ℝ) < neutronEDMupperBound := by
  unfold neutronEDMupperBound; norm_num

/-- The neutron mean life is positive. -/
lemma neutronMeanLife_positive : 0 < neutronMeanLife := by
  unfold neutronMeanLife; norm_num

/-- The neutron mean life is in the expected hundred-second beta-decay window. -/
lemma neutronMeanLife_window : 870 < neutronMeanLife ∧ neutronMeanLife < 890 := by
  unfold neutronMeanLife; refine ⟨?_, ?_⟩ <;> norm_num

/-- Beta decay conserves all additive `(Q,B,L)` quantum numbers. -/
lemma neutron_beta_decay_conserves :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron =
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.proton
        + Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.electron
        + Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.antiNeutrino :=
  Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.beta_decay_conserves

/-- The standard-neutron record carries the beta-decay quantum numbers. -/
lemma standardNeutron_beta_decay_conserves :
    standardNeutron.quantumNumbers =
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.proton
        + Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.electron
        + Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.antiNeutrino := by
  simpa [standardNeutron] using neutron_beta_decay_conserves

/-- The neutron is heavier than the proton. -/
lemma neutronMass_gt_protonMass : protonMass < neutronMass := by
  unfold protonMass neutronMass; norm_num

/-- The neutron-proton mass splitting is about `1.293 MeV`. -/
lemma neutronProtonMassDifference_window :
    1.29 < neutronProtonMassDifference ∧ neutronProtonMassDifference < 1.30 := by
  unfold neutronProtonMassDifference neutronMass protonMass
  refine ⟨?_, ?_⟩ <;> norm_num

/-- The neutron has enough rest-mass energy for beta decay into `p + e^-` at
the level of rest masses; the neutrino mass is not included in this low-energy
bookkeeping model. -/
lemma neutron_beta_decay_mass_window : protonMass + electronMass < neutronMass := by
  unfold protonMass electronMass neutronMass; norm_num

/-! ## D. Neutron mass decomposition: Yukawa current masses plus strong residual -/

/-- The neutron's current-quark mass contribution: one up current mass and two
down current masses. -/
noncomputable def neutronCurrentQuarkMass (yUp yDown v : ℝ) : ℝ :=
  currentQuarkMass yUp v + 2 * currentQuarkMass yDown v

/-- The residual strong-sector contribution to the neutron mass after the
Yukawa current-quark masses have been accounted for. This is the QCD/confinement
piece; the file does not pretend to derive it numerically from first-principles
Yang-Mills dynamics. -/
noncomputable def neutronStrongResidualMass (yUp yDown v : ℝ) : ℝ :=
  neutronMass - neutronCurrentQuarkMass yUp yDown v

/-- The neutron's current-quark contribution is exactly the sum of the existing
Yukawa mass equations for `u,d,d`. -/
lemma neutronCurrentQuarkMass_eq_yukawa_sum (yUp yDown v : ℝ) :
    neutronCurrentQuarkMass yUp yDown v =
      Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass yUp v
        + 2 * Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass yDown v :=
  rfl

/-- The neutron mass decomposes exactly into its Yukawa current-quark part plus
the residual strong-sector part. -/
lemma neutronMass_eq_currentQuarkMass_plus_strongResidual (yUp yDown v : ℝ) :
    neutronMass = neutronCurrentQuarkMass yUp yDown v + neutronStrongResidualMass yUp yDown v := by
  unfold neutronStrongResidualMass; ring

/-- If the residual strong-sector mass is positive, then the neutron is heavier
than the sum of its Higgs/Yukawa current-quark masses. This isolates the exact
assumption needed for the physical claim that most neutron mass is strong/QCD
energy. -/
lemma neutronMass_gt_currentQuarkMass_of_residual_pos
    (yUp yDown v : ℝ) (hres : 0 < neutronStrongResidualMass yUp yDown v) :
    neutronCurrentQuarkMass yUp yDown v < neutronMass := by
  rw [neutronMass_eq_currentQuarkMass_plus_strongResidual yUp yDown v]
  exact lt_add_of_pos_right _ hres

/-- The total winding of the neutron's `udd` quark content is zero:
`2 + (-1) + (-1) = 0`. -/
def neutronTotalWinding : ℤ :=
  QuarkFlavor.windingNumber QuarkFlavor.up
    + QuarkFlavor.windingNumber QuarkFlavor.down
    + QuarkFlavor.windingNumber QuarkFlavor.down

/-- The neutron's total winding is zero. -/
lemma neutronTotalWinding_zero : neutronTotalWinding = 0 := by
  norm_num [neutronTotalWinding, QuarkFlavor.windingNumber]

/-- The neutron is colour-centre trivial in the existing `Z/3` confinement
signature: its total triality/winding is divisible by three. -/
lemma neutron_colourCentre_trivial :
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.cubeRoot ^ neutronTotalWinding = 1 := by
  rw [colourCentre_triality, neutronTotalWinding_zero]
  exact dvd_zero 3

/-- Checked neutron mass-derivation package supported by existing infra:
current quark masses come from the Standard Model Yukawa relation; the neutron
mass is current `udd` mass plus the strong residual; and the `udd` winding is
colour-centre trivial, placing that residual on the colour/Yang-Mills side. -/
def HasNeutronMassDecomposition (yUp yDown v : ℝ) : Prop :=
  neutronCurrentQuarkMass yUp yDown v =
      currentQuarkMass yUp v + 2 * currentQuarkMass yDown v
    ∧ neutronMass = neutronCurrentQuarkMass yUp yDown v + neutronStrongResidualMass yUp yDown v
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.cubeRoot ^ neutronTotalWinding = 1
    ∧ listCharge neutron = 0

/-- The neutron mass decomposition is checked without introducing a duplicate
Yukawa equation, duplicate confinement signature, or false numeric derivation of
the QCD residual. -/
lemma neutronMassDecomposition_checked (yUp yDown v : ℝ) :
    HasNeutronMassDecomposition yUp yDown v :=
  ⟨rfl,
    neutronMass_eq_currentQuarkMass_plus_strongResidual yUp yDown v,
    neutron_colourCentre_trivial,
    neutron_charge_zero⟩

/-! ## E. Antineutron and hadron-sector capability package -/

/-- The antineutron additive quantum numbers: charge neutral, antibaryon number
`-1`, lepton number zero. -/
def antiNeutron :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.QuantumNumbers :=
  ⟨0, -1, 0⟩

/-- The antineutron reverses the neutron's baryon number while keeping charge
zero. -/
lemma antiNeutron_charge_baryon_conjugate :
    antiNeutron.electric =
        -Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron.electric
      ∧ antiNeutron.baryon =
        -Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron.baryon := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [antiNeutron,
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron]

/-- Neutron plus antineutron has vacuum additive quantum numbers. -/
lemma neutron_antineutron_to_vacuum :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron + antiNeutron =
      ⟨0, 0, 0⟩ := by
  ext <;>
    simp [antiNeutron,
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.neutron]

/-- The checked neutron particle model: the neutron is the neutral `udd`
fermionic baryon satisfying strong GMN, beta-decay conservation, nonzero
negative magnetic moment, finite internal charge distribution, and the positive
beta-decay rest-mass window. -/
def HasNeutronParticleModel : Prop :=
  listCharge neutron = 0
    ∧ QuarkFlavor.baryonNumber QuarkFlavor.up
      + QuarkFlavor.baryonNumber QuarkFlavor.down
      + QuarkFlavor.baryonNumber QuarkFlavor.down = 1
    ∧ listIsospinT3 neutron = -1 / 2
    ∧ listHypercharge neutron = 1
    ∧ listCharge neutron = listIsospinT3 neutron + listHypercharge neutron / 2
    ∧ compositeTwist 3 = -1
    ∧ standardNeutron.quantumNumbers =
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.proton
        + Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.electron
        + Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.antiNeutrino
    ∧ neutronMagneticMoment ≠ 0
    ∧ neutronMagneticMoment < 0
    ∧ neutronChargeRadiusSq < 0
    ∧ protonMass < neutronMass
    ∧ protonMass + electronMass < neutronMass
    ∧ ∀ yUp yDown v : ℝ, HasNeutronMassDecomposition yUp yDown v

/-- The neutron particle model is checked from existing flavor, spin-statistics,
conservation-law, and form-factor infrastructure. -/
lemma neutronParticleModel_checked : HasNeutronParticleModel :=
  ⟨neutron_charge_zero,
    neutron_baryonNumber_one,
    neutron_isospin_hypercharge.1,
    neutron_isospin_hypercharge.2,
    neutron_gellMannNishijima,
    neutron_is_fermion,
    standardNeutron_beta_decay_conserves,
    neutronMagneticMoment_nonzero,
    neutronMagneticMoment_negative,
    neutronChargeRadiusSq_negative,
    neutronMass_gt_protonMass,
    neutron_beta_decay_mass_window,
    neutronMassDecomposition_checked⟩

/-- The neutron package extends the existing named-hadron computations rather
than duplicating them. -/
lemma neutronParticleModel_with_hadron_sector :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.HasNamedHadronComputations
      ∧ HasNeutronParticleModel :=
  ⟨Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.namedHadronComputations_checked,
    neutronParticleModel_checked⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutron_gellMannNishijima where
  formalizes @ "claim:the-neutron-udd-satisfies-the-strong-gell-mann-nishijima-relation-with-electric-charge-zero",
  supported_by @ "paper:pdg-2026-review-baryon-properties"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutron_baryonNumber_one where
  formalizes @ "claim:the-neutron-udd-has-baryon-number-one-and-zero-electric-charge",
  requires @ "claim:the-neutron-udd-satisfies-the-strong-gell-mann-nishijima-relation-with-electric-charge-zero"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutronGFactor_eq_two_mul_moment where
  formalizes @ "claim:the-neutron-g-factor-is-twice-its-negative-magnetic-moment-a-nonzero-moment-for-a-neutral-composite-revealing-quark-substructure"

zil_file_contract physlib.neutronProperties where
  promises "The neutron particle model assembled from existing flavor, spin-statistics and magnetic-moment infrastructure: the neutron udd has electric charge zero and baryon number one and satisfies the strong Gell-Mann-Nishijima relation; it is a fermion; its g-factor is twice its (negative) magnetic moment -- a nonzero magnetic moment for an electrically neutral composite, the signature of quark substructure -- with the neutron-proton mass difference, mean life, negative mean-square charge radius and EDM bound recorded."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutronMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutronMagneticMoment"]
  forbids_substitutes ["a QCD calculation of the neutron mass or magnetic moment, whose numerical values are PDG inputs",
    "a first-principles derivation of the quark content, taken from the flavor model"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutron_charge_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutron_gellMannNishijima,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutron_baryonNumber_one,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutron_is_fermion,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutronGFactor_eq_two_mul_moment]

/- ZIL-END -/
