/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
public import Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
public import Physlib.QuantumMechanics.ComplexAction.DowkerHalliwellDecoherenceFunctional
meta import Zil

/-!
# Second-quantized Dirac--Cartan--2I--Compton--Yukawa QCD carrier

This module lifts the concrete one-particle binary-icosahedral Dirac action to
fermionic exterior-algebra Fock space.  The same construction then attaches the
Compton/Yukawa energy and entropy rate to the QCD complex-action history weight.

The resulting theorem surface contains:

* the real-linear one-particle `2I` action on the four-component quaternionic
  Dirac carrier;
* its fermionic second quantization `Gamma(g) = ExteriorAlgebra.map rho(g)`;
* creation-operator intertwining and Pauli exclusion;
* the fixed-occupation Compton energy `E_N = N hbar omega_C = N m_Y c^2`;
* a QCD history weight whose real action is the theta sector and whose imaginary
  action is confinement plus the occupation-dependent Yukawa entropy action;
* the corresponding Born diagonal and Hermitian history decoherence functional.
-/

set_option autoImplicit false
open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD

open Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor
open Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction
open Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
open Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.ComplexAction.DowkerHalliwellDecoherenceFunctional
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality

/-- The concrete binary-icosahedral action as a real-linear endomorphism of the
four-component quaternionic Dirac carrier. -/
noncomputable def binaryDiracActionLinear (g : BinaryIcosahedralGroup) :
    BinaryDiracSpinor →ₗ[ℝ] BinaryDiracSpinor where
  toFun := binaryDiracSpinorAction g
  map_add' ψ φ := by
    funext block
    simp [binaryDiracSpinorAction, binarySpinorAction, mul_add]
  map_smul' r ψ := by
    funext block
    ext <;>
      simp [binaryDiracSpinorAction, binarySpinorAction, Quaternion.re_mul,
        Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

@[simp] theorem binaryDiracActionLinear_apply
    (g : BinaryIcosahedralGroup) (ψ : BinaryDiracSpinor) :
    binaryDiracActionLinear g ψ = binaryDiracSpinorAction g ψ := rfl

/-- Fermionic Fock space of the binary-icosahedral Dirac one-particle carrier. -/
abbrev BinaryDiracFock := Fock BinaryDiracSpinor

/-- The second-quantized binary-icosahedral transformation on fermionic Fock
space. -/
noncomputable def secondQuantized2I (g : BinaryIcosahedralGroup) :
    BinaryDiracFock →ₐ[ℝ] BinaryDiracFock :=
  secondQuant (binaryDiracActionLinear g)

/-- Second quantization implements the one-particle `2I` action on creation
operators. -/
theorem secondQuantized2I_creation
    (g : BinaryIcosahedralGroup) (ψ : BinaryDiracSpinor) (x : BinaryDiracFock) :
    secondQuantized2I g (creationOp ψ x) =
      creationOp (binaryDiracSpinorAction g ψ) (secondQuantized2I g x) := by
  simpa [secondQuantized2I] using
    (secondQuant_creationOp (binaryDiracActionLinear g) ψ x)

/-- Pauli exclusion for every binary-icosahedral one-particle mode. -/
theorem binaryDirac_creation_pauli
    (g : BinaryIcosahedralGroup) (ψ : BinaryDiracSpinor) (x : BinaryDiracFock) :
    creationOp (binaryDiracSpinorAction g ψ)
        (creationOp (binaryDiracSpinorAction g ψ) x) = 0 :=
  creationOp_sq (binaryDiracSpinorAction g ψ) x

/-- Complete creation/annihilation CAR for a binary-icosahedral transformed
mode and any real dual mode. -/
theorem binaryDirac_creation_annihilation_car
    (g : BinaryIcosahedralGroup) (d : Module.Dual ℝ BinaryDiracSpinor)
    (ψ : BinaryDiracSpinor) (x : BinaryDiracFock) :
    annihilationOp d (creationOp (binaryDiracSpinorAction g ψ) x)
        + creationOp (binaryDiracSpinorAction g ψ) (annihilationOp d x)
      = d (binaryDiracSpinorAction g ψ) • x :=
  car d (binaryDiracSpinorAction g ψ) x

/-- Fixed-occupation Compton energy of `N` identical excitations. -/
noncomputable def fockComptonEnergy
    (D : DiracCartanComptonYukawaData) (N : ℕ) : ℝ :=
  (N : ℝ) * (D.hbar * D.omega)

/-- The second-quantized Compton energy is the occupation number times the
Yukawa rest energy. -/
theorem fockComptonEnergy_eq_yukawaRestEnergy
    (D : DiracCartanComptonYukawaData) (N : ℕ) :
    fockComptonEnergy D N = (N : ℝ) * (yukawaMass D.y D.v * D.c ^ 2) := by
  unfold fockComptonEnergy
  rw [yukawaClock_restEnergy D]

/-- Occupation-dependent Yukawa entropy action accumulated over time `t`. -/
noncomputable def fockYukawaEntropyAction
    (D : DiracCartanComptonYukawaData) (N : ℕ) (t : ℝ) : ℝ :=
  (N : ℝ) * yukawaEntropyRate D.y D.omega D.hbar * t

/-- The imaginary action of a second-quantized QCD history: confinement plus
Yukawa/CAT-EPT entropy production. -/
noncomputable def qcdFockImaginaryAction
    (D : DiracCartanComptonYukawaData) (N : ℕ) (σ A t : ℝ) : ℝ :=
  σ * A + fockYukawaEntropyAction D N t

/-- Entanglement-action normalization used by the history decoherence
functional, `S_ent = 2 S_I / hbar`. -/
noncomputable def qcdFockEntanglementAction
    (D : DiracCartanComptonYukawaData) (N : ℕ) (σ A t hbar : ℝ) : ℝ :=
  2 * qcdFockImaginaryAction D N σ A t / hbar

/-- Complex history amplitude containing the QCD theta phase, confinement
weight, and second-quantized Yukawa entropy action. -/
noncomputable def qcdFockHistoryWeight
    (D : DiracCartanComptonYukawaData) (N : ℕ)
    (θ σ A t hbar : ℝ) (n : ℤ) : ℂ :=
  historyWeight (θ * (n : ℝ)) (qcdFockEntanglementAction D N σ A t hbar) hbar

/-- The history amplitude is exactly the master complex-action path-integral
weight with real action `theta*n` and imaginary action `sigma*A + S_I^Y`. -/
theorem qcdFockHistoryWeight_eq_master
    (D : DiracCartanComptonYukawaData) (N : ℕ)
    (θ σ A t hbar : ℝ) (n : ℤ) (hhbar : hbar ≠ 0) :
    qcdFockHistoryWeight D N θ σ A t hbar n =
      complexActionPathIntegralWeight (θ * (n : ℝ))
        (qcdFockImaginaryAction D N σ A t) hbar := by
  unfold qcdFockHistoryWeight historyWeight qcdFockEntanglementAction
  congr 1
  field_simp [hhbar]

/-- The Born diagonal of the second-quantized QCD history is the exponential of
minus its entanglement action. -/
theorem qcdFockHistoryWeight_born
    (D : DiracCartanComptonYukawaData) (N : ℕ)
    (θ σ A t hbar : ℝ) (n : ℤ) (hhbar : hbar ≠ 0) :
    Complex.normSq (qcdFockHistoryWeight D N θ σ A t hbar n) =
      Real.exp (-(qcdFockEntanglementAction D N σ A t hbar)) := by
  unfold qcdFockHistoryWeight
  exact historyWeight_born (θ * (n : ℝ))
    (qcdFockEntanglementAction D N σ A t hbar) hbar hhbar

/-- History decoherence functional for the second-quantized QCD amplitudes. -/
noncomputable def qcdFockDecoherenceFunctional {ι : Type*}
    (w : ι → ℂ) : ι → ι → ℂ :=
  decoherenceFunctional w

/-- The QCD/Fock history decoherence functional is Hermitian. -/
theorem qcdFockDecoherenceFunctional_hermitian {ι : Type*} (w : ι → ℂ) :
    IsHermitianKernel (qcdFockDecoherenceFunctional w) :=
  decoherenceFunctional_isHermitian w

/-- One theorem-facing assembly of second quantization, `2I` covariance,
Compton/Yukawa energy, QCD complex action, and the history Born rule. -/
theorem dirac_cartan_2I_second_quantized_qcd_assembly
    (D : DiracCartanComptonYukawaData) (g : BinaryIcosahedralGroup)
    (ψ : BinaryDiracSpinor) (x : BinaryDiracFock) (N : ℕ)
    (θ σ A t hbar : ℝ) (n : ℤ) (hhbar : hbar ≠ 0) :
    secondQuantized2I g (creationOp ψ x) =
        creationOp (binaryDiracSpinorAction g ψ) (secondQuantized2I g x)
      ∧ creationOp (binaryDiracSpinorAction g ψ)
          (creationOp (binaryDiracSpinorAction g ψ) x) = 0
      ∧ fockComptonEnergy D N = (N : ℝ) * (yukawaMass D.y D.v * D.c ^ 2)
      ∧ Complex.normSq (qcdFockHistoryWeight D N θ σ A t hbar n) =
          Real.exp (-(qcdFockEntanglementAction D N σ A t hbar)) :=
  ⟨secondQuantized2I_creation g ψ x,
    binaryDirac_creation_pauli g ψ x,
    fockComptonEnergy_eq_yukawaRestEnergy D N,
    qcdFockHistoryWeight_born D N θ σ A t hbar n hhbar⟩

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD.secondQuantized2I_creation where
  formalizes @ "claim:the-concrete-binary-icosahedral-dirac-action-lifts-to-fermionic-fock-space-and-intertwines-creation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor.secondQuant_creationOp",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor.binary_icosahedral_dirac_spinor_assembly",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD.fockComptonEnergy_eq_yukawaRestEnergy where
  formalizes @ "claim:the-fixed-occupation-fock-energy-is-n-times-the-compton-yukawa-rest-energy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.yukawaClock_restEnergy",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD.qcdFockHistoryWeight_eq_master where
  formalizes @ "claim:the-second-quantized-qcd-history-weight-combines-theta-confinement-and-yukawa-entropy-in-one-complex-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.qcd_theta_confinement_factorization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston.historyWeight_born",
  epistemic_status @ "conditional-model"

zil_file_contract physlib.diracCartan2ISecondQuantizedQCD where
  promises "The concrete binary-icosahedral four-spinor action is a real-linear one-particle symmetry whose exterior-algebra second quantization intertwines creation and satisfies Pauli/CAR; fixed occupation multiplies the Compton-Yukawa rest energy; and QCD theta phase, confinement damping, and Yukawa entropy production form one complex-action history amplitude with its Born diagonal and Hermitian decoherence functional."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor.BinaryDiracSpinor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor.Fock",
    "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.DiracCartanComptonYukawaData"]
  forbids_substitutes ["a dynamical selection of the QCD sector or identification with measured hadrons",
    "a derivation of the theta angle, confinement scale, or physical couplings"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD.dirac_cartan_2I_second_quantized_qcd_assembly]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD

end
