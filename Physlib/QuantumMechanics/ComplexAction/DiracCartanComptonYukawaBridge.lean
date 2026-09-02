/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor
public import Physlib.QuantumMechanics.ComplexAction.EinsteinCartanAxialTorsion
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour
public import Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator
meta import Zil

/-!
# Dirac--Cartan--binary-icosahedral Compton--Yukawa assembly

This file joins the concrete binary-icosahedral four-spinor action, the
canonical Dirac axial current and algebraic Cartan equation, the four-spinor
Dirac mass operator, and the Yukawa complex mass whose imaginary rest energy is
the CAT/EPT entropy-production rate.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge

open Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor
open Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction
open Physlib.QuantumMechanics.ComplexAction.EinsteinCartanAxialTorsion
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation
open Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-- Parameters whose Yukawa mass and internal Compton-clock mass are identified. -/
structure DiracCartanComptonYukawaData where
  y : ℝ
  v : ℝ
  omega : ℝ
  c : ℝ
  hbar : ℝ
  kappa : ℝ
  v_ne : v ≠ 0
  c_ne : c ≠ 0
  hbar_ne : hbar ≠ 0
  kappa_ne : kappa ≠ 0
  massClock : yukawaMass y v = comptonMass omega c hbar

/-- The identified mass-clock relation isolates the Yukawa coupling. -/
theorem isolated_yukawa_from_compton_clock (D : DiracCartanComptonYukawaData) :
    D.y = Real.sqrt 2 * D.hbar * D.omega / (D.c ^ 2 * D.v) :=
  yukawa_isolated_explicit D.y D.v D.omega D.c D.hbar D.v_ne D.massClock

/-- The Yukawa mass is the mass term of the actual four-spinor Dirac operator,
    with the exact Compton-clock mass shell. -/
theorem diracHamiltonian4_sq_yukawaClock
    (D : DiracCartanComptonYukawaData) (p1 p2 p3 : ℝ) :
    diracHamiltonian4 p1 p2 p3 (yukawaMass D.y D.v)
        * diracHamiltonian4 p1 p2 p3 (yukawaMass D.y D.v)
      = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + (yukawaMass D.y D.v) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [D.massClock]
  exact diracHamiltonian4_sq_comptonMass p1 p2 p3 D.omega D.c D.hbar

/-- The same clock obeys the rest-energy identity `hbar omega = m_Y c^2`. -/
theorem yukawaClock_restEnergy (D : DiracCartanComptonYukawaData) :
    D.hbar * D.omega = yukawaMass D.y D.v * D.c ^ 2 := by
  calc
    D.hbar * D.omega = comptonMass D.omega D.c D.hbar * D.c ^ 2 :=
      comptonMass_restEnergy D.omega D.c D.hbar D.c_ne
    _ = yukawaMass D.y D.v * D.c ^ 2 := by rw [← D.massClock]

/-- The imaginary part of the complex Yukawa rest energy is the entropic rate. -/
theorem yukawaComplexEnergy_im_is_entropicRate
    (D : DiracCartanComptonYukawaData) :
    (yukawaComplexRestEnergy D.y D.v D.omega D.hbar D.c).im
      = yukawaEntropyRate D.y D.omega D.hbar :=
  yukawaComplexRestEnergy_im_eq_entropyRate
    D.y D.v D.omega D.hbar D.c D.c_ne

/-- One checked assembly of the new particle-model ingredients: the complete
binary-icosahedral Dirac-spinor action and central-pair density descent, the
four-spinor Dirac mass shell, the Compton rest-energy clock, the Yukawa entropic
rate, and the canonical Dirac-axial Cartan equation with its eliminated contact
density. -/
theorem dirac_cartan_2I_compton_yukawa_assembly
    (D : DiracCartanComptonYukawaData)
    (g : BinaryIcosahedralGroup)
    (binaryPsi : BinaryDiracSpinor)
    (diracPsi : ComplexDiracSpinor)
    (p1 p2 p3 : ℝ) :
    diracSpinorDensity (binaryDiracSpinorAction g binaryPsi)
        = diracSpinorDensity binaryPsi
      ∧ diracSpinorDensity (binaryDiracSpinorAction (-g) binaryPsi)
          = diracSpinorDensity (binaryDiracSpinorAction g binaryPsi)
      ∧ diracHamiltonian4 p1 p2 p3 (yukawaMass D.y D.v)
          * diracHamiltonian4 p1 p2 p3 (yukawaMass D.y D.v)
        = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + (yukawaMass D.y D.v) ^ 2 : ℝ) : ℂ) •
            (1 : Matrix (Fin 4) (Fin 4) ℂ)
      ∧ D.hbar * D.omega = yukawaMass D.y D.v * D.c ^ 2
      ∧ (yukawaComplexRestEnergy D.y D.v D.omega D.hbar D.c).im
          = yukawaEntropyRate D.y D.omega D.hbar
      ∧ (∀ mu, cartanResidual D.kappa
          (diracSourcedContorsion D.kappa diracPsi mu)
          (diracAxialCurrent diracPsi mu) = 0)
      ∧ (∑ mu, cartanAuxiliaryDensity D.kappa
          (diracSourcedContorsion D.kappa diracPsi mu)
          (diracAxialCurrent diracPsi mu))
          = hehlDattaContactDensity D.kappa (diracAxialCurrent diracPsi) := by
  exact ⟨binaryDiracSpinorAction_density g binaryPsi,
    central_pair_same_dirac_density g binaryPsi,
    diracHamiltonian4_sq_yukawaClock D p1 p2 p3,
    yukawaClock_restEnergy D,
    yukawaComplexEnergy_im_is_entropicRate D,
    fun mu => diracSourcedContorsion_solves D.kappa diracPsi mu,
    eliminate_dirac_cartan_spinor D.kappa diracPsi D.kappa_ne⟩

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.diracHamiltonian4_sq_yukawaClock where
  formalizes @ "claim:the-yukawa-compton-clock-mass-is-the-mass-term-of-the-four-spinor-dirac-operator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator.diracHamiltonian4_sq_comptonMass",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.yukawaComplexEnergy_im_is_entropicRate where
  formalizes @ "claim:the-imaginary-yukawa-rest-energy-is-the-cat-ept-entropy-production-rate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour.yukawaComplexRestEnergy_im_eq_entropyRate",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.dirac_cartan_2I_compton_yukawa_assembly where
  formalizes @ "claim:a-dirac-cartan-binary-icosahedral-compton-yukawa-particle-carrier-has-one-checked-formal-assembly",
  requires @ "claim:the-yukawa-compton-clock-mass-is-the-mass-term-of-the-four-spinor-dirac-operator",
  requires @ "claim:the-imaginary-yukawa-rest-energy-is-the-cat-ept-entropy-production-rate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor.binary_icosahedral_dirac_spinor_assembly",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinCartanAxialTorsion.dirac_cartan_axial_elimination_assembly",
  epistemic_status @ "conditional-model"

zil_file_contract physlib.diracCartan2IComptonYukawa where
  promises "The concrete 120-element binary icosahedral group acts norm-preservingly on a four-component Dirac spinor and its central pair descends at the complete density level; the Yukawa-generated mass equals the Compton-clock mass in the four-spinor Dirac operator; the clock obeys hbar omega equals m c squared; the complex Yukawa rest energy has imaginary part equal to the entropy-production rate; and the canonical Dirac axial current sources algebraic Cartan contorsion whose elimination gives the Hehl-Datta contact density."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction.BinaryIcosahedralGroup",
    "lean:Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour.yukawaComplexRestEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4",
    "lean:Physlib.Relativity.CliffordAlgebra.gamma5"]
  forbids_substitutes ["a dynamical selection of the 2I sector or identification with a measured electron",
    "a derivation of the Yukawa coupling value or the physical mass calibration"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.dirac_cartan_2I_compton_yukawa_assembly]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
