/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Winding.ChargeFockRealization
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.CoulombGegenbauer
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
meta import Zil

/-!
# M9 charge, Klein--Gordon, and orbital-quantization criterion bridges

This module packages theorem surfaces that already exist across the live Physlib
repository and adds the small finite-mode algebra needed by the OpenWave M9
criterion matrix.

* Charge is an additive winding grading, with conjugation, integer/fractional
  sectors, the observed third-charge table, and a Fock-space `U(1)` realization.
* A Klein--Gordon Fourier mode has frequency
  `sqrt (c^2 k^2 + m^2)` and an exact conserved quadratic mode energy.
* The unscreened Yukawa endpoint is the Coulomb problem with integer-labelled
  `O(4)/S^3` Gegenbauer harmonics; a negative hydrogenic ladder is supplied as
  the dimensionless radial energy label used by the executable study.

The bridges do not identify the winding with a particular measured elementary
charge, derive a scalar particle from the full CAT/EPT dynamics, or calibrate an
atomic system in physical units.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria

open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Winding.ChargeFockRealization
open Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor
open Physlib.QuantumMechanics.ComplexAction.Yukawa.CoulombGegenbauer
open Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

/-! ## M9.90: winding charge quantization -/

/-- Capstone for the live winding-charge arithmetic: the standard charge table,
additivity, conjugation, and the exact integer-sector divisibility criterion. -/
theorem chargeQuantizationCriterion :
    windingCharge upWinding = 2 / 3 ∧
    windingCharge downWinding = -1 / 3 ∧
    windingCharge (-3) = -1 ∧
    windingCharge 0 = 0 ∧
    (∀ m n : ℤ, windingCharge m + windingCharge n = windingCharge (m + n)) ∧
    (∀ n : ℤ, windingCharge (-n) = -windingCharge n) ∧
    (∀ n : ℤ, (∃ k : ℤ, windingCharge n = (k : ℚ)) ↔ (3 : ℤ) ∣ n) := by
  exact ⟨upQuark_charge, downQuark_charge, electron_charge, neutrino_charge,
    fun m n => windingCharge_add m n,
    fun n => windingCharge_neg n,
    fun n => windingCharge_integer_iff n⟩

/-- The scalar winding grading is realized on the actual fermionic creation
operator by second quantization of a scalar one-particle action. -/
theorem chargeCreationOperatorGrading
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (c : ℝ) (m : M) (x : Fock M) :
    secondQuant (c • LinearMap.id) (creationOp m x) =
      c • creationOp m (secondQuant (c • LinearMap.id) x) :=
  secondQuant_scalar_creationOp c m x

/-! ## M9.91: finite spectral Klein--Gordon mode -/

/-- Positive-frequency Klein--Gordon dispersion relation. -/
noncomputable def kleinGordonFrequency (c m k : ℝ) : ℝ :=
  Real.sqrt (c ^ 2 * k ^ 2 + m ^ 2)

lemma kleinGordonFrequency_nonneg (c m k : ℝ) :
    0 ≤ kleinGordonFrequency c m k :=
  Real.sqrt_nonneg _

/-- The frequency squares to the exact massive dispersion
`omega^2 = c^2 k^2 + m^2`. -/
theorem kleinGordonFrequency_sq (c m k : ℝ) :
    kleinGordonFrequency c m k ^ 2 = c ^ 2 * k ^ 2 + m ^ 2 := by
  unfold kleinGordonFrequency
  rw [Real.sq_sqrt]
  positivity

/-- Position coordinate of one real Klein--Gordon Fourier mode. -/
noncomputable def kleinGordonModePosition
    (omega t a b : ℝ) : ℝ :=
  a * Real.cos (omega * t) + b * Real.sin (omega * t)

/-- Canonical momentum coordinate of one real Klein--Gordon Fourier mode. -/
noncomputable def kleinGordonModeMomentum
    (omega t a b : ℝ) : ℝ :=
  omega * (-a * Real.sin (omega * t) + b * Real.cos (omega * t))

/-- Quadratic energy of one Klein--Gordon mode. -/
def kleinGordonModeEnergy (omega q p : ℝ) : ℝ :=
  p ^ 2 + omega ^ 2 * q ^ 2

@[simp] theorem kleinGordonModePosition_zero (omega a b : ℝ) :
    kleinGordonModePosition omega 0 a b = a := by
  simp [kleinGordonModePosition]

@[simp] theorem kleinGordonModeMomentum_zero (omega a b : ℝ) :
    kleinGordonModeMomentum omega 0 a b = omega * b := by
  simp [kleinGordonModeMomentum]

/-- Exact conservation of the finite spectral Klein--Gordon mode energy. -/
theorem kleinGordonModeEnergy_conserved
    (omega t a b : ℝ) :
    kleinGordonModeEnergy omega
      (kleinGordonModePosition omega t a b)
      (kleinGordonModeMomentum omega t a b) =
        omega ^ 2 * (a ^ 2 + b ^ 2) := by
  unfold kleinGordonModeEnergy kleinGordonModePosition kleinGordonModeMomentum
  have h := Real.sin_sq_add_cos_sq (omega * t)
  linear_combination omega ^ 2 * (a ^ 2 + b ^ 2) * h

/-- Combined finite-mode certificate: exact dispersion and conserved mode energy. -/
theorem kleinGordonFiniteModeCriterion
    (c m k t a b : ℝ) :
    kleinGordonFrequency c m k ^ 2 = c ^ 2 * k ^ 2 + m ^ 2 ∧
    kleinGordonModeEnergy (kleinGordonFrequency c m k)
      (kleinGordonModePosition (kleinGordonFrequency c m k) t a b)
      (kleinGordonModeMomentum (kleinGordonFrequency c m k) t a b) =
        kleinGordonFrequency c m k ^ 2 * (a ^ 2 + b ^ 2) :=
  ⟨kleinGordonFrequency_sq c m k,
    kleinGordonModeEnergy_conserved (kleinGordonFrequency c m k) t a b⟩

/-! ## M9.92: Coulomb orbital quantization -/

/-- Dimensionless hydrogenic bound-state energy labelled by the positive
principal quantum number `n+1`. -/
noncomputable def hydrogenicEnergy (n : ℕ) : ℝ :=
  -1 / (2 * ((n : ℝ) + 1) ^ 2)

lemma hydrogenicEnergy_neg (n : ℕ) : hydrogenicEnergy n < 0 := by
  unfold hydrogenicEnergy
  have hden : 0 < 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- The live Coulomb/O(4) theorem together with a negative integer-labelled
hydrogenic energy level. -/
theorem orbitalQuantizationCriterion (m r : ℝ) (n : ℕ) :
    entropicMass m (-m ^ 2) = 0 ∧
    yukawaPotential 0 r = 1 / r ∧
    gegenbauerEigenvalue 1 n = (n : ℝ) * ((n : ℝ) + 2) ∧
    (∃ dy, IsGegenbauerSolution 1 n (gegenbauerOne n) dy) ∧
    hydrogenicEnergy n < 0 := by
  rcases yukawa_coulomb_o4_gegenbauer m r n with
    ⟨hmass, hpotential, heigen, dy, hsolution⟩
  exact ⟨hmass, hpotential, heigen, ⟨dy, hsolution⟩,
    hydrogenicEnergy_neg n⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.chargeQuantizationCriterion where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.downQuark_charge",
  formalizes @ "claim:winding-charge-is-additive-conjugation-odd-quantized-in-thirds-and-integer-exactly-on-windings-divisible-by-three"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.kleinGordonFiniteModeCriterion where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.kleinGordonFrequency_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.kleinGordonModeEnergy_conserved",
  formalizes @ "claim:each-finite-klein-gordon-fourier-mode-has-the-exact-massive-dispersion-and-conserved-quadratic-mode-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.orbitalQuantizationCriterion where
  supported_by @ "lean:yukawa_coulomb_o4_gegenbauer",
  formalizes @ "claim:the-unscreened-coulomb-endpoint-has-integer-labelled-o-four-gegenbauer-harmonics-and-negative-hydrogenic-energy-labels"

zil_file_contract physlib.m9ChargeKleinOrbitalCriteria where
  promises "Criterion bridges for winding charge quantization, finite spectral Klein-Gordon evolution, and Coulomb orbital quantization."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.kleinGordonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor.Fock"]
  forbids_substitutes ["claiming elementary-charge identity, a full interacting scalar quantum field, or calibrated atomic phenomenology"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.chargeQuantizationCriterion,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.kleinGordonFiniteModeCriterion,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria.orbitalQuantizationCriterion ]

/- ZIL-END -/
