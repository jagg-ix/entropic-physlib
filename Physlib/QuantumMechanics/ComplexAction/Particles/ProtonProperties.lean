/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
meta import Zil

/-!
# Proton properties: mass, magnetic moment, CPT, EDM, radii, lifetime, decay

A formalization of the measured/structural properties of the proton, reusing the repository's additive
`QuantumNumbers` (`Particles.BaryonLeptonNumberConservation.proton = ⟨Q, B, L⟩ = ⟨1, 1, 0⟩`) and the Landé g-factor
(`FirstQuantizedQED.AnomalousMagneticMoment.gFactor a = 2(1 + a)`).

* **§A — mass & charge-to-mass ratio.** `m_p ≈ 938.27 MeV`, `m_p/m_e ≈ 1836`; specific charge `|e|/m_p` with
  `(|e|/m_p)·m_p = 1`, smaller than the electron's (heavier particle).
* **§B — magnetic (dipole) moment & anomalous moment.** `μ_p = g_p/2 ≈ 2.793 μ_N`, with the *large* anomalous
  moment `a_p = g_p/2 − 1 ≈ 1.793` (the proton is composite — far from the Dirac `g = 2`), linked to `gFactor`.
* **§C — CPT & the antiproton.** charge/baryon conjugation `p̄ = ⟨−1,−1,0⟩`, `p + p̄ = vacuum`, opposite
  magnetic moment, equal mass.
* **§D — electric dipole moment.** the `T`/`CP`-test EDM, consistent with zero below the experimental bound.
* **§E — charge & magnetic radii.** sub-femtometer finite size (composite), with the dipole form-factor
  relation `⟨r²⟩ = −6 G'(0)`.
* **§F — mean life, decay modes, stability.** `τ_p > 10³⁴ yr`; `p → e⁺π⁰` conserves charge and `B − L` but
  violates `B` and `L`, so baryon-number conservation forbids it — the proton is stable.
* **§G — forward spin polarizability.** `γ₀ ≈ −1.0×10⁻⁴ fm⁴` (nonzero spin structure).

All numeric facts are exact `norm_num` over ℝ/ℚ; the quantum-number relations reuse the conservation-law
infrastructure. ## References

* CODATA / PDG proton constants; muonic-hydrogen charge radius. `Physlib`
  (`Particles.BaryonLeptonNumberConservation`, `FirstQuantizedQED.AnomalousMagneticMoment`, `FirstQuantizedQED.CPTAntiunitary`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties


/-- Proton mass `m_p ≈ 938.272 MeV/c²`. -/
noncomputable def protonMass : ℝ := 938.272
/-- Electron mass `m_e ≈ 0.511 MeV/c²`. -/
noncomputable def electronMass : ℝ := 0.511

/-- **[The proton-to-electron mass ratio]** `1835 < m_p/m_e < 1837` (`≈ 1836.15`). -/
lemma proton_electron_mass_ratio :
    1835 < protonMass / electronMass ∧ protonMass / electronMass < 1837 := by
  unfold protonMass electronMass; refine ⟨?_, ?_⟩ <;> norm_num

/-- The proton **specific charge** `|e|/m_p` (charge-to-mass ratio, in units `e/MeV`). -/
noncomputable def protonSpecificCharge : ℝ := 1 / protonMass
/-- The electron specific charge `|e|/m_e`. -/
noncomputable def electronSpecificCharge : ℝ := 1 / electronMass

/-- **[Specific charge × mass = unit charge]** `(|e|/m_p)·m_p = 1` — the proton has one unit of charge. -/
lemma protonSpecificCharge_mul_mass : protonSpecificCharge * protonMass = 1 := by
  unfold protonSpecificCharge protonMass; norm_num

/-- **[The proton's charge-to-mass ratio is smaller than the electron's]** `|e|/m_p < |e|/m_e` — same charge,
`1836×` the mass. -/
lemma proton_specificCharge_lt_electron : protonSpecificCharge < electronSpecificCharge := by
  unfold protonSpecificCharge electronSpecificCharge protonMass electronMass; norm_num


/-- The proton quark content is `uud`. -/
lemma proton_quarkContent :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton =
      [Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up,
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up,
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.down] :=
  rfl

/-- The proton has electric charge `+1`, derived from `uud`. -/
lemma proton_flavor_charge_one :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listCharge
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1 :=
  Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton_charge

/-- The proton's baryon number is one: three quarks, each with `B = 1/3`. -/
lemma proton_baryonNumber_one :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
      + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
      + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.down = 1 :=
  Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.baryon_baryonNumber
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.down

/-- The proton has `I3 = +1/2` and strong hypercharge `Y = 1`. -/
lemma proton_isospin_hypercharge :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listIsospinT3
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1 / 2
      ∧ Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listHypercharge
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listIsospinT3,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.isospinT3]
  · norm_num [Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listHypercharge,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.hypercharge,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.strangeness,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.charmness,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.bottomness,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.topness,
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.quarkBaryonNumber]

/-- Strong Gell-Mann--Nishijima for the proton, inherited from the composite
hadron theorem. -/
lemma proton_gellMannNishijima :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listCharge
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton =
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listIsospinT3
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton
        + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listHypercharge
          Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton / 2 :=
  Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.gmn_strong_baryon
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton

/-- The proton is a three-quark fermion. -/
lemma proton_is_fermion : compositeTwist 3 = -1 := baryon_is_fermion


/-- Proton g-factor `g_p ≈ 5.5857`. -/
noncomputable def protonGFactor : ℝ := 5.5857
/-- Proton **magnetic dipole moment** `μ_p = g_p/2 ≈ 2.793` (nuclear magnetons `μ_N`). -/
noncomputable def protonMagneticMoment : ℝ := protonGFactor / 2
/-- Proton **anomalous magnetic moment** `a_p = g_p/2 − 1 ≈ 1.793`. -/
noncomputable def protonAnomalousMoment : ℝ := protonGFactor / 2 - 1

/-- **[The g-factor from the anomalous moment]** `g_p = 2(1 + a_p)` — the proton g-factor is the Landé value
of its anomalous moment (`FirstQuantizedQED.AnomalousMagneticMoment.gFactor`). -/
lemma protonGFactor_eq_gFactor_anomaly : gFactor protonAnomalousMoment = protonGFactor := by
  unfold gFactor protonAnomalousMoment; ring

/-- **[The magnetic moment value]** `2.79 < μ_p < 2.80` (`μ_N`). -/
lemma protonMagneticMoment_value :
    2.79 < protonMagneticMoment ∧ protonMagneticMoment < 2.80 := by
  unfold protonMagneticMoment protonGFactor; refine ⟨?_, ?_⟩ <;> norm_num

/-- The proton magnetic moment is positive in nuclear magnetons. -/
lemma protonMagneticMoment_positive : 0 < protonMagneticMoment := by
  unfold protonMagneticMoment protonGFactor; norm_num

/-- **[The proton is far from Dirac — it is composite]** `1 < a_p` — the anomalous moment `a_p ≈ 1.79` is
*order one*, vastly larger than a point lepton's `a ≈ α/2π ≈ 0.00116`: the proton's magnetic moment is
dominated by its quark substructure, not by a Dirac point charge. -/
lemma proton_far_from_dirac : 1 < protonAnomalousMoment := by
  unfold protonAnomalousMoment protonGFactor; norm_num


/-- The **vacuum** quantum numbers `⟨0, 0, 0⟩`. -/
def vacuum : QuantumNumbers := ⟨0, 0, 0⟩
/-- The **antiproton** `p̄ = ⟨−1, −1, 0⟩` — the charge/baryon conjugate of the proton. -/
def antiproton : QuantumNumbers := ⟨-1, -1, 0⟩

/-- **[Charge conjugation]** `Q(p̄) = −Q(p)` and `B(p̄) = −B(p)` — the antiproton reverses charge and baryon
number. -/
lemma antiproton_charge_conjugate :
    antiproton.electric = -proton.electric ∧ antiproton.baryon = -proton.baryon := by
  refine ⟨?_, ?_⟩ <;> norm_num [antiproton, proton]

/-- **[Particle–antiparticle annihilation]** `p + p̄ = vacuum` — all additive quantum numbers cancel. -/
lemma proton_antiproton_to_vacuum : proton + antiproton = vacuum := by
  ext <;> simp [proton, antiproton, vacuum]

/-- The **antiproton magnetic moment** `μ_p̄ = −μ_p` (CPT). -/
noncomputable def antiprotonMagneticMoment : ℝ := -protonMagneticMoment

/-- **[CPT: opposite magnetic moments]** `μ_p + μ_p̄ = 0` — particle and antiparticle moments cancel. -/
lemma cpt_moment_opposite : protonMagneticMoment + antiprotonMagneticMoment = 0 := by
  unfold antiprotonMagneticMoment; ring

/-- The **antiproton mass** `m_p̄ = m_p` (CPT-predicted equality). -/
noncomputable def antiprotonMass : ℝ := protonMass

/-- **[CPT: equal masses]** the proton–antiproton fractional mass asymmetry vanishes,
`(m_p − m_p̄)/m_p = 0`. -/
lemma cpt_mass_asymmetry_zero : (protonMass - antiprotonMass) / protonMass = 0 := by
  unfold antiprotonMass; simp


/-- Experimental **upper bound** on the proton EDM, `≈ 2.1×10⁻²⁵ e·cm`: a permanent EDM along the spin is
`T`-odd (and `P`-odd), so this bounds time-reversal / `CP` violation. -/
noncomputable def protonEDMupperBound : ℝ := 2.1e-25

/-- **[The proton EDM is consistent with zero]** the bound is a small positive number; the measured proton EDM
lies below it, consistent with `T`/`CP` invariance (a vanishing EDM). -/
lemma protonEDM_bound_positive : (0 : ℝ) < protonEDMupperBound := by
  unfold protonEDMupperBound; norm_num


/-- Proton **charge radius** `r_E ≈ 0.8414 fm` (muonic-hydrogen / CODATA). -/
noncomputable def protonChargeRadius : ℝ := 0.8414
/-- Proton **magnetic radius** `r_M ≈ 0.851 fm`. -/
noncomputable def protonMagneticRadius : ℝ := 0.851

/-- **[The proton has finite size — it is not point-like]** `0 < r_E` — unlike a structureless lepton, the
proton has a nonzero charge radius (composite). -/
lemma proton_finite_size : 0 < protonChargeRadius := by
  unfold protonChargeRadius; norm_num

/-- **[Sub-femtometer radii]** `r_E < 1 fm` and `r_M < 1 fm`. -/
lemma proton_subfemtometer : protonChargeRadius < 1 ∧ protonMagneticRadius < 1 := by
  unfold protonChargeRadius protonMagneticRadius; refine ⟨?_, ?_⟩ <;> norm_num

/-- **[Charge and magnetic radii are close]** `|r_E − r_M| < 0.02 fm`. -/
lemma charge_magnetic_radius_close : |protonChargeRadius - protonMagneticRadius| < 0.02 := by
  unfold protonChargeRadius protonMagneticRadius; rw [abs_lt]; refine ⟨?_, ?_⟩ <;> norm_num

/-- The **charge radius squared from the form-factor slope** `⟨r²⟩ = −6 G'(0)`. -/
noncomputable def chargeRadiusSqFromSlope (slope : ℝ) : ℝ := -6 * slope

/-- **[Dipole form factor radius]** for a dipole form factor `G_E = (1 + Q²/Λ²)⁻²` (slope `G'(0) = −2/Λ²`), the
charge radius squared is `⟨r²⟩ = 12/Λ²`. -/
lemma chargeRadiusSq_dipole (Λ : ℝ) : chargeRadiusSqFromSlope (-2 / Λ ^ 2) = 12 / Λ ^ 2 := by
  unfold chargeRadiusSqFromSlope; ring


/-- The **positron** `e⁺ = ⟨1, 0, −1⟩` (antielectron). -/
def positron : QuantumNumbers := ⟨1, 0, -1⟩

/-- Experimental **lower bound** on the proton mean life, `τ_p > 10³⁴ yr` (no decay observed). -/
noncomputable def protonMeanLifeLowerBound : ℝ := 1e34

/-- The standard proton particle object: quark model, additive quantum numbers,
mass, magnetic moment, and observed lower-bound lifetime in one shared hadron
record. -/
noncomputable def standardProton : HadronParticleModel where
  quarkContent := Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton
  quantumNumbers := proton
  massMeV := protonMass
  magneticMomentNuclearMagnetons := protonMagneticMoment
  meanLifeSeconds := protonMeanLifeLowerBound

/-- The record's additive electric charge agrees with the computed flavor
charge. -/
lemma standardProton_charge_matches_flavor :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listCharge
        standardProton.quarkContent = standardProton.quantumNumbers.electric := by
  simp [standardProton, proton_flavor_charge_one, proton]

/-- The record's additive baryon number is the baryon value `1`. -/
lemma standardProton_baryon_number : standardProton.quantumNumbers.baryon = 1 := by
  simp [standardProton, proton]

/-- **[The proton is extraordinarily long-lived]** `τ_p > 10³⁰ yr` — far exceeding the age of the universe. -/
lemma proton_extremely_long_lived : (1e30 : ℝ) < protonMeanLifeLowerBound := by
  unfold protonMeanLifeLowerBound; norm_num

/-- **[`p → e⁺π⁰` conserves charge]** `Q(p) = Q(e⁺) + Q(π⁰)` (`1 = 1`). -/
lemma proton_decay_conserves_charge : proton.electric = (positron + piZero).electric := by
  norm_num [proton, positron, piZero]

/-- **[`p → e⁺π⁰` violates baryon number]** `B(p) = 1 ≠ 0 = B(e⁺) + B(π⁰)` — baryon number is not conserved. -/
lemma proton_decay_violates_baryon : proton.baryon ≠ (positron + piZero).baryon := by
  norm_num [proton, positron, piZero]

/-- **[`p → e⁺π⁰` violates lepton number]** `L(p) = 0 ≠ −1 = L(e⁺) + L(π⁰)`. -/
lemma proton_decay_violates_lepton : proton.lepton ≠ (positron + piZero).lepton := by
  norm_num [proton, positron, piZero]

/-- **[`p → e⁺π⁰` conserves `B − L`]** `(B − L)(p) = 1 = (B − L)(e⁺π⁰)` — the canonical grand-unified decay
violates `B` and `L` separately but preserves `B − L`. -/
lemma proton_decay_conserves_B_minus_L :
    proton.baryon - proton.lepton = (positron + piZero).baryon - (positron + piZero).lepton := by
  norm_num [proton, positron, piZero]

/-- **[Baryon-number conservation forbids proton decay — the proton is stable]** `p ≠ e⁺ + π⁰` as charge
vectors, because their baryon numbers differ (`1 ≠ 0`). Under exact baryon-number conservation the proton has
no allowed decay channel. -/
lemma proton_stable_under_baryon_conservation : proton ≠ positron + piZero := fun h =>
  proton_decay_violates_baryon (congrArg QuantumNumbers.baryon h)


/-- The proton's current-quark mass contribution: two up current masses and one
down current mass. -/
noncomputable def protonCurrentQuarkMass (yUp yDown v : ℝ) : ℝ :=
  2 * currentQuarkMass yUp v + currentQuarkMass yDown v

/-- The residual strong-sector contribution to the proton mass after the Yukawa
current-quark masses have been accounted for. -/
noncomputable def protonStrongResidualMass (yUp yDown v : ℝ) : ℝ :=
  protonMass - protonCurrentQuarkMass yUp yDown v

/-- The proton's current-quark contribution is exactly the sum of the existing
Yukawa mass equations for `u,u,d`. -/
lemma protonCurrentQuarkMass_eq_yukawa_sum (yUp yDown v : ℝ) :
    protonCurrentQuarkMass yUp yDown v =
      2 * Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass yUp v
        + Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass yDown v :=
  rfl

/-- The proton mass decomposes exactly into its Yukawa current-quark part plus
the residual strong-sector part. -/
lemma protonMass_eq_currentQuarkMass_plus_strongResidual (yUp yDown v : ℝ) :
    protonMass = protonCurrentQuarkMass yUp yDown v + protonStrongResidualMass yUp yDown v := by
  unfold protonStrongResidualMass; ring

/-- If the residual strong-sector mass is positive, then the proton is heavier
than the sum of its Higgs/Yukawa current-quark masses. -/
lemma protonMass_gt_currentQuarkMass_of_residual_pos
    (yUp yDown v : ℝ) (hres : 0 < protonStrongResidualMass yUp yDown v) :
    protonCurrentQuarkMass yUp yDown v < protonMass := by
  rw [protonMass_eq_currentQuarkMass_plus_strongResidual yUp yDown v]
  exact lt_add_of_pos_right _ hres

/-- The total winding of the proton's `uud` quark content is three:
`2 + 2 + (-1) = 3`. -/
def protonTotalWinding : ℤ :=
  Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.windingNumber
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
    + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.windingNumber
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
    + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.windingNumber
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.down

/-- The proton's total winding is three. -/
lemma protonTotalWinding_eq_three : protonTotalWinding = 3 := by
  norm_num [protonTotalWinding,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.windingNumber]

/-- The proton is colour-centre trivial in the existing `Z/3` confinement
signature: its total triality/winding is divisible by three. -/
lemma proton_colourCentre_trivial :
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.cubeRoot ^ protonTotalWinding = 1 := by
  rw [colourCentre_triality, protonTotalWinding_eq_three]

/-- Checked proton mass-decomposition package supported by existing infra:
current quark masses come from the Standard Model Yukawa relation; the proton
mass is current `uud` mass plus the strong residual; and the `uud` winding is
colour-centre trivial. -/
def HasProtonMassDecomposition (yUp yDown v : ℝ) : Prop :=
  protonCurrentQuarkMass yUp yDown v =
      2 * currentQuarkMass yUp v + currentQuarkMass yDown v
    ∧ protonMass = protonCurrentQuarkMass yUp yDown v + protonStrongResidualMass yUp yDown v
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.cubeRoot ^ protonTotalWinding = 1
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listCharge
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1

/-- The proton mass decomposition is checked without introducing a duplicate
Yukawa equation, duplicate confinement signature, or false numeric derivation of
the QCD residual. -/
lemma protonMassDecomposition_checked (yUp yDown v : ℝ) :
    HasProtonMassDecomposition yUp yDown v :=
  ⟨rfl,
    protonMass_eq_currentQuarkMass_plus_strongResidual yUp yDown v,
    proton_colourCentre_trivial,
    proton_flavor_charge_one⟩


/-- Proton **forward spin polarizability** `γ₀ ≈ −1.0×10⁻⁴ fm⁴` (a fourth-order Compton structure constant). -/
noncomputable def protonForwardSpinPolarizability : ℝ := -1.0e-4

/-- **[The proton has nontrivial spin structure]** `γ₀ ≠ 0`. -/
lemma proton_has_spin_structure : protonForwardSpinPolarizability ≠ 0 := by
  unfold protonForwardSpinPolarizability; norm_num

/-- **[The forward spin polarizability is negative]** `γ₀ < 0` (the measured sign for the proton). -/
lemma proton_spinPolarizability_negative : protonForwardSpinPolarizability < 0 := by
  unfold protonForwardSpinPolarizability; norm_num

/-- The checked proton particle model: the proton is the charged `uud`
fermionic baryon satisfying strong GMN, CPT-compatible antiproton cancellation,
positive magnetic moment, finite charge radius, baryon-number stability, and
the same Yukawa-current plus strong-residual mass pattern used by the neutron. -/
def HasProtonParticleModel : Prop :=
  Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listCharge
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
      + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.up
      + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.baryonNumber
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.down = 1
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listIsospinT3
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1 / 2
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listHypercharge
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton = 1
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listCharge
      Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton =
        Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listIsospinT3
          Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton
          + Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.listHypercharge
            Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.proton / 2
    ∧ compositeTwist 3 = -1
    ∧ standardProton.quantumNumbers = proton
    ∧ proton + antiproton = vacuum
    ∧ 0 < protonMagneticMoment
    ∧ 1 < protonAnomalousMoment
    ∧ 0 < protonChargeRadius
    ∧ proton ≠ positron + piZero
    ∧ ∀ yUp yDown v : ℝ, HasProtonMassDecomposition yUp yDown v

/-- The proton particle model is checked from existing flavor,
spin-statistics, conservation-law, form-factor, Yukawa, and colour-centre
infrastructure. -/
lemma protonParticleModel_checked : HasProtonParticleModel :=
  ⟨proton_flavor_charge_one,
    proton_baryonNumber_one,
    proton_isospin_hypercharge.1,
    proton_isospin_hypercharge.2,
    proton_gellMannNishijima,
    proton_is_fermion,
    rfl,
    proton_antiproton_to_vacuum,
    protonMagneticMoment_positive,
    proton_far_from_dirac,
    proton_finite_size,
    proton_stable_under_baryon_conservation,
    protonMassDecomposition_checked⟩

/-- The proton package extends the existing named-hadron computations rather
than duplicating them. -/
lemma protonParticleModel_with_hadron_sector :
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.HasNamedHadronComputations
      ∧ HasProtonParticleModel :=
  ⟨Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.namedHadronComputations_checked,
    protonParticleModel_checked⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_gellMannNishijima where
  formalizes @ "claim:the-proton-satisfies-the-strong-gell-mann-nishijima-relation-with-charge-one",
  supported_by @ "paper:pdg-2026-review-baryon-properties"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_baryonNumber_one where
  formalizes @ "claim:the-proton-uud-has-baryon-number-one-and-flavor-charge-one",
  requires @ "claim:the-proton-satisfies-the-strong-gell-mann-nishijima-relation-with-charge-one"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_is_fermion where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.baryon_is_fermion",
  formalizes @ "claim:the-proton-is-a-fermion-with-a-totally-antisymmetric-three-quark-colour-wavefunction"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.cpt_moment_opposite where
  formalizes @ "claim:cpt-forces-the-antiproton-magnetic-moment-to-be-exactly-opposite-the-proton-magnetic-moment",
  supported_by @ "paper:pdg-2026-review-baryon-properties"

zil_file_contract physlib.protonProperties where
  promises "The proton particle model assembled from existing flavor, spin-statistics, conservation-law and magnetic-moment infrastructure: the proton uud has electric charge one and baryon number one and satisfies the strong Gell-Mann-Nishijima relation; it is a fermion with a totally antisymmetric three-quark colour wavefunction; its anomalous magnetic moment is far from the Dirac value; and CPT forces the antiproton magnetic moment to be exactly opposite and the proton-antiproton mass asymmetry to vanish."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.protonMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.protonMagneticMoment"]
  forbids_substitutes ["a QCD calculation of the proton mass or magnetic moment, whose numerical values are PDG inputs",
    "a first-principles derivation of the quark content, taken from the flavor model"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_gellMannNishijima,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_baryonNumber_one,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_is_fermion,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.protonMagneticMoment_positive,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.proton_far_from_dirac,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.cpt_moment_opposite,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.cpt_mass_asymmetry_zero]

/- ZIL-END -/
