/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen

/-!
# Yukawa mass as a Nagao-Nielsen complex mass and lapse-contour source

This bridge attaches the conditional Yukawa proportionality of
`Yukawa.MassDecoherenceProportionality` to the repo's existing complex-action carriers.

The input remains exactly the modest, formalizable content:

* `m_f = y v / sqrt 2`;
* `Gamma_f = y omega0 / hbar`;
* `Sdot_I = Gamma_f / 2`.

No theorem here derives `y`.  Instead, the shared coupling is used to place the Yukawa mass in the
Nagao-Nielsen complex-mass slot and the entropy-production rate in the imaginary energy / contour slot:

* the real part of the complex mass is the Yukawa mass;
* choosing `m_I = Sdot_I / c^2` makes `Im(m c^2) = Sdot_I`;
* the Bender width is therefore `Gamma_f = widthFromRate (Im E)`;
* choosing lapse displacement `epsilon = Sdot_I / H` makes the gravitational lapse contour carry the
  same imaginary action `epsilon H = Sdot_I`;
* in the Levi-Civita momentum-density layer, a scalar entropic stress with coefficient `Sdot_I` gives
  imaginary momentum density `Sdot_I * u`.

This is the disciplined link: Yukawa data feed an already-existing complex-action / Levi-Civita source
slot, without asserting a geometric derivation of the Yukawa coupling.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour

open Matrix
open Physlib.QuantumMechanics.ComplexAction
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen


/-- The imaginary mass chosen so that its Einstein rest energy is the Yukawa entropy-production rate. -/
def yukawaImaginaryMass (y omega0 hbar c : ℝ) : ℝ :=
  yukawaEntropyRate y omega0 hbar / c ^ 2

/-- The Nagao-Nielsen complex mass whose real part is the Yukawa mass and whose imaginary rest energy is
the Yukawa entropy-production rate. -/
def yukawaNagaoNielsenMass (y v omega0 hbar c : ℝ) : ℂ :=
  complexMass (yukawaMass y v) (yukawaImaginaryMass y omega0 hbar c)

@[simp] lemma yukawaNagaoNielsenMass_re (y v omega0 hbar c : ℝ) :
    (yukawaNagaoNielsenMass y v omega0 hbar c).re = yukawaMass y v := by
  simp [yukawaNagaoNielsenMass]

@[simp] lemma yukawaNagaoNielsenMass_im (y v omega0 hbar c : ℝ) :
    (yukawaNagaoNielsenMass y v omega0 hbar c).im = yukawaImaginaryMass y omega0 hbar c := by
  simp [yukawaNagaoNielsenMass]

/-- The same Yukawa complex mass in the fermionic Dirac/Weyl carrier. -/
def yukawaComplexFermionMass (y v omega0 hbar c : ℝ) : ℂ :=
  complexFermionMass (yukawaMass y v) (yukawaImaginaryMass y omega0 hbar c)

@[simp] lemma yukawaComplexFermionMass_re (y v omega0 hbar c : ℝ) :
    (yukawaComplexFermionMass y v omega0 hbar c).re = yukawaMass y v := by
  simp [yukawaComplexFermionMass, complexFermionMass_re]

@[simp] lemma yukawaComplexFermionMass_im (y v omega0 hbar c : ℝ) :
    (yukawaComplexFermionMass y v omega0 hbar c).im = yukawaImaginaryMass y omega0 hbar c := by
  simp [yukawaComplexFermionMass, complexFermionMass_im]

/-- The imaginary part of the fermionic mass-square is the Yukawa mass times the entropic mass component. -/
lemma yukawaComplexFermionMass_sq_im (y v omega0 hbar c : ℝ) :
    ((yukawaComplexFermionMass y v omega0 hbar c) ^ 2).im
      = 2 * yukawaMass y v * yukawaImaginaryMass y omega0 hbar c := by
  rw [yukawaComplexFermionMass, complexFermionMass_sq_im]


/-- The complex Einstein rest energy of the Yukawa complex mass. -/
def yukawaComplexRestEnergy (y v omega0 hbar c : ℝ) : ℂ :=
  complexEinsteinEnergy (yukawaMass y v) (yukawaImaginaryMass y omega0 hbar c) c

lemma yukawaComplexRestEnergy_re (y v omega0 hbar c : ℝ) :
    (yukawaComplexRestEnergy y v omega0 hbar c).re = yukawaMass y v * c ^ 2 := by
  rw [yukawaComplexRestEnergy, complexEinsteinEnergy_re]

lemma yukawaComplexRestEnergy_im (y v omega0 hbar c : ℝ) :
    (yukawaComplexRestEnergy y v omega0 hbar c).im
      = yukawaImaginaryMass y omega0 hbar c * c ^ 2 := by
  rw [yukawaComplexRestEnergy, complexEinsteinEnergy_im]

/-- With nonzero light speed, the imaginary rest energy is exactly the Yukawa entropy-production rate. -/
lemma yukawaComplexRestEnergy_im_eq_entropyRate (y v omega0 hbar c : ℝ) (hc : c ≠ 0) :
    (yukawaComplexRestEnergy y v omega0 hbar c).im = yukawaEntropyRate y omega0 hbar := by
  rw [yukawaComplexRestEnergy_im, yukawaImaginaryMass]
  field_simp [pow_ne_zero 2 hc]

/-- The Yukawa decoherence width is the Bender width of the imaginary complex rest energy. -/
lemma yukawaWidth_eq_widthFromRate_complexRestEnergy_im
    (y v omega0 hbar c : ℝ) (hc : c ≠ 0) :
    yukawaDecoherenceWidth y omega0 hbar
      = widthFromRate ((yukawaComplexRestEnergy y v omega0 hbar c).im) := by
  rw [yukawaComplexRestEnergy_im_eq_entropyRate y v omega0 hbar c hc]
  exact yukawaWidth_eq_widthFromRate_entropyRate y omega0 hbar

@[simp] lemma yukawaNagaoNielsenMass_massless (v omega0 hbar c : ℝ) :
    yukawaNagaoNielsenMass 0 v omega0 hbar c = 0 := by
  simp [yukawaNagaoNielsenMass, yukawaImaginaryMass, yukawaMass, yukawaEntropyRate,
    yukawaDecoherenceWidth, complexMass]

@[simp] lemma yukawaComplexRestEnergy_massless (v omega0 hbar c : ℝ) :
    yukawaComplexRestEnergy 0 v omega0 hbar c = 0 := by
  simp [yukawaComplexRestEnergy, yukawaImaginaryMass, yukawaMass, yukawaEntropyRate,
    yukawaDecoherenceWidth, complexEinsteinEnergy, complexMass]


/-- The lapse-contour displacement whose imaginary action is the Yukawa entropy-production rate. -/
def yukawaLapseGap (y omega0 hbar Ham : ℝ) : ℝ :=
  yukawaEntropyRate y omega0 hbar / Ham

lemma yukawaLapseGap_mul_Ham (y omega0 hbar Ham : ℝ) (hHam : Ham ≠ 0) :
    yukawaLapseGap y omega0 hbar Ham * Ham = yukawaEntropyRate y omega0 hbar := by
  rw [yukawaLapseGap]
  field_simp [hHam]

/-- The lapse-displaced gravitational weight is the master complex-action weight with Yukawa imaginary
action. -/
lemma yukawaLapseWeight_eq_master (N y omega0 hbar Ham : ℝ) (hHam : Ham ≠ 0) :
    lapseWeight N (yukawaLapseGap y omega0 hbar Ham) Ham
      = complexActionPathIntegralWeight (-(N * Ham)) (yukawaEntropyRate y omega0 hbar) 1 := by
  rw [lapseWeight_eq_master, yukawaLapseGap_mul_Ham y omega0 hbar Ham hHam]

/-- The modulus of the same lapse weight is the Kuiken damping with Yukawa entropy-production rate. -/
lemma yukawaLapseWeight_modulus (N y omega0 hbar Ham : ℝ) (hHam : Ham ≠ 0) :
    ‖lapseWeight N (yukawaLapseGap y omega0 hbar Ham) Ham‖
      = kuikenWeight 1 (yukawaEntropyRate y omega0 hbar) := by
  rw [lapseWeight_modulus, yukawaLapseGap_mul_Ham y omega0 hbar Ham hHam]

/-- The imaginary part of the complex lapse is the negative Yukawa gap. -/
lemma yukawaLapse_im_eq_gap (N y omega0 hbar Ham : ℝ) :
    (Physlib.QuantumMechanics.NonHermitian.WickRotation.complexEnergy
      N (yukawaLapseGap y omega0 hbar Ham)).im
        = -yukawaLapseGap y omega0 hbar Ham :=
  lapse_im_eq_gap N (yukawaLapseGap y omega0 hbar Ham)

@[simp] lemma yukawaLapseGap_massless (omega0 hbar Ham : ℝ) :
    yukawaLapseGap 0 omega0 hbar Ham = 0 := by
  simp [yukawaLapseGap, yukawaEntropyRate, yukawaDecoherenceWidth]


/-- A scalar entropic stress tensor with coefficient equal to the Yukawa entropy-production rate. -/
def yukawaScalarEntropicStress {ι : Type*} [DecidableEq ι] (y omega0 hbar : ℝ) :
    Matrix ι ι ℝ :=
  yukawaEntropyRate y omega0 hbar • (1 : Matrix ι ι ℝ)

lemma yukawaScalarEntropicStress_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y omega0 hbar : ℝ) (u : ι → ℝ) :
    yukawaScalarEntropicStress y omega0 hbar *ᵥ u
      = fun nu => yukawaEntropyRate y omega0 hbar * u nu := by
  rw [yukawaScalarEntropicStress, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- In the Levi-Civita complex momentum density, the imaginary momentum current of the Yukawa scalar
entropic source is `Sdot_I * u`. -/
lemma yukawaComplexMomentumDensity_im {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (u : ι → ℝ) (y omega0 hbar : ℝ) (nu : ι) :
    (complexMomentumDensity T (yukawaScalarEntropicStress y omega0 hbar) u nu).im
      = yukawaEntropyRate y omega0 hbar * u nu := by
  rw [complexMomentumDensity_im, entropicMomentumDensity, yukawaScalarEntropicStress_mulVec]

/-- Bundled repo-facing statement: the same Yukawa rate is simultaneously the imaginary Einstein rest
energy, the Bender width source, the lapse-contour imaginary action, and the Levi-Civita entropic
momentum-current coefficient. -/
lemma yukawa_complexMass_contour_leviCivita_assembly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (u : ι → ℝ) (nu : ι)
    (N y v omega0 hbar c Ham : ℝ) (hc : c ≠ 0) (hHam : Ham ≠ 0) :
    (yukawaNagaoNielsenMass y v omega0 hbar c).re = yukawaMass y v
      ∧ (yukawaComplexRestEnergy y v omega0 hbar c).im = yukawaEntropyRate y omega0 hbar
      ∧ yukawaDecoherenceWidth y omega0 hbar
          = widthFromRate ((yukawaComplexRestEnergy y v omega0 hbar c).im)
      ∧ lapseWeight N (yukawaLapseGap y omega0 hbar Ham) Ham
          = complexActionPathIntegralWeight (-(N * Ham)) (yukawaEntropyRate y omega0 hbar) 1
      ∧ (complexMomentumDensity T (yukawaScalarEntropicStress y omega0 hbar) u nu).im
          = yukawaEntropyRate y omega0 hbar * u nu := by
  exact ⟨yukawaNagaoNielsenMass_re y v omega0 hbar c,
    yukawaComplexRestEnergy_im_eq_entropyRate y v omega0 hbar c hc,
    yukawaWidth_eq_widthFromRate_complexRestEnergy_im y v omega0 hbar c hc,
    yukawaLapseWeight_eq_master N y omega0 hbar Ham hHam,
    yukawaComplexMomentumDensity_im T u y omega0 hbar nu⟩

end Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour

end

end
