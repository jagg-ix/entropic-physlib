/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.Relativity.Special.ProperTimeWorldlineIntegral
public import Physlib.SpaceAndTime.EntropicProperTimeOnGRWorldline

meta import Zil

/-!
# OVV Type-IIB fluxes, the IKKT matrix action, and the entropic Compton clock

This module is a thin cross-sector bridge.  It connects three existing, independently
formalized presentations without identifying them by fiat:

* the Ooguri--Vafa--Verlinde Type-IIB flux insertion and OSV wavefunction;
* the IKKT/IIB bosonic matrix action, including its proved coupling absorption;
* the entropic-time Compton clock and the exact rest-frame identity
  `omega_Z = 2 omega_C` from `FrequencyTrinity`.
* the Lorentz-invariant inertial-worldline proper-time integral and the recent
  Jacobson Clausius-to-Einstein equation-of-state chain.

The common carrier is the repository's `lorentzianKernel`.  The OVV insertion fixes
an explicit imaginary action.  An IKKT matrix configuration has the same weight only
under the visible action-matching premise, and that action becomes independent of the
positive coupling after the already-proved matrix rescaling.  Likewise, reading the
OVV entropic phase as a particle clock requires the explicit rest-energy calibration
`S_I = m c^2 tau`; no Type-IIB compactification scale is asserted to determine a
particle mass.  The bridge also proves that IKKT central translations remain exact
symmetries of the path weight, specializes the action match to the finite OVV flux
superpotential, and transports the OVV real/holomorphic polarization equality to the
matrix presentation.  Finally, nonnegative proper time selects `Im W <= 0`, precisely
the calibrated sector in which the shared weight is nonexpansive rather than enhanced.
The final section replaces the formerly abstract proper-time parameter by the
repository's worldline integral, identifies the resulting Compton phase with the
existing scalar entropic-proper-time observable, and composes its Clausius reading
with the recent Einstein-equation theorem.  The matrix/flux, rest-energy, heat, and
all-null-direction Clausius identifications remain separate visible premises.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.SpaceTime
open SpaceTime
open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics

namespace Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge

/-- The imaginary action carried by the OVV real-polarization flux insertion at
Planck scale `hbar`. -/
def ovvImaginaryAction (hbar : Real) (W : Complex) : Real :=
  -(hbar * (Real.pi / 2 * W.im))

/-- The IIB matrix action evaluated by the repository's common complex-action
path-integral kernel. -/
def iibBosonicPathWeight {N d : Nat} (g hbar : Real)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex) : Complex :=
  let S := iibBosonicAction g A
  lorentzianKernel S.re S.im hbar

/-- The full bosonic action, not merely its quartic potential, is invariant
under the IKKT central translation `A_mu ↦ A_mu + c_mu 1`. -/
@[zil_level bridge_theorem]
theorem iibBosonicAction_translation_invariant
    {N d : Nat} (g : Real) (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (c : Fin d → Complex) :
    iibBosonicAction g (fun mu ↦ A mu + c mu • 1) = iibBosonicAction g A := by
  unfold iibBosonicAction
  rw [iibBosonic_translation_invariant]

/-- IKKT translation symmetry survives evaluation by the common
complex-action path-integral weight. -/
@[zil_level bridge_theorem]
theorem iibBosonicPathWeight_translation_invariant
    {N d : Nat} (g hbar : Real) (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (c : Fin d → Complex) :
    iibBosonicPathWeight g hbar (fun mu ↦ A mu + c mu • 1) =
      iibBosonicPathWeight g hbar A := by
  unfold iibBosonicPathWeight
  rw [iibBosonicAction_translation_invariant]

/-- At path-weight level, the proved positive-coupling rescaling replaces the
IKKT action by the normalized action `-B(A)`. -/
@[zil_level bridge_theorem]
theorem iibBosonicPathWeight_coupling_absorbed
    {N d : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu) =
      lorentzianKernel (-iibBosonic A).re (-iibBosonic A).im hbar := by
  unfold iibBosonicPathWeight
  rw [iibBosonicAction_coupling_absorbed g hg A]

/-- The dimensionless OVV entropic phase is independent of the unit used for
action: `S_I / hbar = -(pi/2) Im W`. -/
@[zil_level bridge_theorem]
lemma ovvImaginaryAction_div_hbar (W : Complex) (hbar : Real) (hhbar : hbar ≠ 0) :
    ovvImaginaryAction hbar W / hbar = -(Real.pi / 2 * W.im) := by
  unfold ovvImaginaryAction
  field_simp

/-- The OVV insertion is the common complex-action kernel at its explicit
imaginary action, for every nonzero choice of `hbar`. -/
@[zil_level bridge_theorem]
lemma fluxInsertion_eq_ovvKernel (W : Complex) (hbar : Real) (hhbar : hbar ≠ 0) :
    fluxInsertion W = lorentzianKernel 0 (ovvImaginaryAction hbar W) hbar := by
  rw [fluxInsertion_eq_exp_im]
  unfold lorentzianKernel
  have hratio : (ovvImaginaryAction hbar W : Complex) / (hbar : Complex) =
      ((-(Real.pi / 2 * W.im) : Real) : Complex) := by
    norm_cast
    exact ovvImaginaryAction_div_hbar W hbar hhbar
  rw [hratio]
  simp

/-- A typed, deliberately conditional bridge between the IKKT/IIB matrix action
and the OVV flux insertion.  If the matrix action is the purely imaginary OVV
action, their path weights are identical. -/
@[zil_level bridge_theorem]
theorem iibBosonicPathWeight_eq_fluxInsertion_of_action_match
    {N d : Nat} (g hbar : Real) (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (W : Complex) (hhbar : hbar ≠ 0)
    (hmatch : iibBosonicAction g A = Complex.I * (ovvImaginaryAction hbar W : Complex)) :
    iibBosonicPathWeight g hbar A = fluxInsertion W := by
  rw [fluxInsertion_eq_ovvKernel W hbar hhbar]
  simp [iibBosonicPathWeight, hmatch]

/-- After the proved IKKT field rescaling absorbs a positive matrix coupling, a
match of the normalized bosonic action to the OVV imaginary action gives exactly
the OVV flux weight. -/
@[zil_level bridge_theorem]
theorem iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
    {N d : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex) (W : Complex)
    (hhbar : hbar ≠ 0)
    (hmatch : -iibBosonic A = Complex.I * (ovvImaginaryAction hbar W : Complex)) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu) = fluxInsertion W := by
  apply iibBosonicPathWeight_eq_fluxInsertion_of_action_match g hbar _ W hhbar
  rw [iibBosonicAction_coupling_absorbed g hg A]
  exact hmatch

/-- The action-matching theorem specialized to the actual finite OVV electric
and magnetic flux superpotential. -/
@[zil_level bridge_theorem]
theorem iibRescaledBosonicPathWeight_eq_fluxSectorWeight_of_normalized_match
    {N d n : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (q p : Fin n → Real) (X F : Fin n → Complex) (hhbar : hbar ≠ 0)
    (hmatch : -iibBosonic A = Complex.I *
      (ovvImaginaryAction hbar (fluxSuperpotential q p X F) : Complex)) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu) =
      fluxSectorWeight q p X F := by
  unfold fluxSectorWeight
  exact iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
    g hbar hg A (fluxSuperpotential q p X F) hhbar hmatch

/-- Under the same explicit normalized-action match, the rescaled IKKT path
weight and the OVV holomorphic topological-string wave have exactly the same
norm square. -/
@[zil_level bridge_theorem]
theorem normSq_iibRescaledBosonicPathWeight_eq_holomorphicFluxWave
    {N d : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex) (W : Complex)
    (hhbar : hbar ≠ 0)
    (hmatch : -iibBosonic A = Complex.I * (ovvImaginaryAction hbar W : Complex)) :
    Complex.normSq (iibBosonicPathWeight g hbar
      (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu)) =
        Complex.normSq (holomorphicFluxWave W) := by
  rw [iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
    g hbar hg A W hhbar hmatch]
  exact (holomorphicFluxWave_normSq_eq_realPolarization W).symm

/-- Calibrating the OVV imaginary action by the rest-energy law makes its
dimensionless entropic phase exactly the Compton phase. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_eq_comptonPhase
    (W : Complex) (m c hbar tau : Real) (hhbar : hbar ≠ 0)
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    ovvImaginaryAction hbar W / hbar = comptonPhase m c hbar tau := by
  rw [hclock]
  unfold comptonPhase comptonFrequency
  field_simp

/-- Under the same explicit clock calibration, the OVV entropic phase is also
one half of the rest-frame Zitterbewegung phase. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_eq_half_zitterbewegungPhase
    (W : Complex) (m c hbar tau : Real) (hm : 0 ≤ m) (hhbar : hbar ≠ 0)
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    ovvImaginaryAction hbar W / hbar =
      (zitterbewegungFrequency 0 m c hbar / 2) * tau := by
  rw [ovvEntropicPhase_eq_comptonPhase W m c hbar tau hhbar hclock,
    zitterbewegung_rest_eq_two_compton m c hbar hm]
  unfold comptonPhase
  ring

/-- The norm of the calibrated OVV flux weight is the entropic Compton-clock
damping `exp (-omega_C tau)`. -/
@[zil_level bridge_theorem]
theorem norm_fluxInsertion_eq_exp_neg_comptonPhase
    (W : Complex) (m c hbar tau : Real) (hhbar : hbar ≠ 0)
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    ‖fluxInsertion W‖ = Real.exp (-(comptonPhase m c hbar tau)) := by
  rw [fluxInsertion_eq_ovvKernel W hbar hhbar,
    lorentzianKernel_norm_is_damping,
    ovvEntropicPhase_eq_comptonPhase W m c hbar tau hhbar hclock]

/-- A nonnegative-mass, nonnegative-proper-time Compton calibration selects the
nonpositive-`Im W` OVV sector.  This is precisely the sector where the generic
OVV exponential is damping rather than enhancement. -/
@[zil_level bridge_theorem]
theorem ovvSuperpotential_im_nonpos_of_comptonCalibration
    (W : Complex) (m c hbar tau : Real) (hm : 0 ≤ m) (hhbar : 0 < hbar)
    (htau : 0 ≤ tau)
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    W.im ≤ 0 := by
  have hrhs : 0 ≤ m * c ^ 2 * tau :=
    mul_nonneg (mul_nonneg hm (sq_nonneg c)) htau
  have hsi : 0 ≤ ovvImaginaryAction hbar W := hclock.symm ▸ hrhs
  have hsi' : 0 ≤ -(hbar * (Real.pi / 2) * W.im) := by
    simpa [ovvImaginaryAction, mul_assoc] using hsi
  have hcoef : 0 < hbar * (Real.pi / 2) :=
    mul_pos hhbar (div_pos Real.pi_pos (by norm_num))
  nlinarith

/-- The calibrated OVV/IIB flux weight is nonexpansive in the physical future:
its norm is at most one. -/
@[zil_level bridge_theorem]
theorem norm_fluxInsertion_le_one_of_comptonCalibration
    (W : Complex) (m c hbar tau : Real) (hm : 0 ≤ m) (hhbar : 0 < hbar)
    (htau : 0 ≤ tau)
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    ‖fluxInsertion W‖ ≤ 1 := by
  rw [norm_fluxInsertion_eq_exp_neg_comptonPhase W m c hbar tau hhbar.ne' hclock,
    Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (mul_nonneg (entropicTime_rate_nonneg m c hbar hm hhbar) htau)

/-- A flux trajectory obeying the rest-energy action calibration inherits the
proved Compton entropic-time arrow. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_monotone_of_comptonCalibration
    (W : Real → Complex) (m c hbar : Real) (hm : 0 ≤ m) (hhbar : 0 < hbar)
    (hclock : ∀ tau, ovvImaginaryAction hbar (W tau) = m * c ^ 2 * tau) :
    Monotone (fun tau ↦ ovvImaginaryAction hbar (W tau) / hbar) := by
  intro tau₁ tau₂ htau
  change ovvImaginaryAction hbar (W tau₁) / hbar ≤
    ovvImaginaryAction hbar (W tau₂) / hbar
  rw [ovvEntropicPhase_eq_comptonPhase (W tau₁) m c hbar tau₁ hhbar.ne' (hclock tau₁),
    ovvEntropicPhase_eq_comptonPhase (W tau₂) m c hbar tau₂ hhbar.ne' (hclock tau₂)]
  exact comptonPhase_monotone m c hbar hm hhbar htau

/-- In the calibrated physical-future sector, the matched rescaled IKKT weight
is nonexpansive and the OVV superpotential necessarily has nonpositive
imaginary part. -/
@[zil_level bridge_theorem]
theorem iib_ovv_comptonFuture_damping_sector
    {N d : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (W : Complex) (m c tau : Real) (hm : 0 ≤ m) (hhbar : 0 < hbar)
    (htau : 0 ≤ tau)
    (haction : -iibBosonic A = Complex.I * (ovvImaginaryAction hbar W : Complex))
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    W.im ≤ 0 ∧
      ‖iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu)‖ ≤ 1 := by
  refine ⟨ovvSuperpotential_im_nonpos_of_comptonCalibration
      W m c hbar tau hm hhbar htau hclock, ?_⟩
  rw [iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
    g hbar hg A W hhbar.ne' haction]
  exact norm_fluxInsertion_le_one_of_comptonCalibration
    W m c hbar tau hm hhbar htau hclock

/-- The complete honest link: a matched IKKT matrix action and OVV flux sector
have the same complex-action weight; the OVV imaginary action is the entropic
phase; and a separately supplied rest-energy calibration reads that phase as
the Compton clock, equivalently half the rest-frame Zitterbewegung clock. -/
@[zil_level bridge_theorem]
theorem iib_ovv_entropicTime_compton_zitterbewegung_chain
    {N d : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (W : Complex) (m c tau : Real) (hm : 0 ≤ m) (hhbar : 0 < hbar)
    (haction : -iibBosonic A = Complex.I * (ovvImaginaryAction hbar W : Complex))
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tau) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu) = fluxInsertion W
      ∧ fluxInsertion W = lorentzianKernel 0 (ovvImaginaryAction hbar W) hbar
      ∧ ovvImaginaryAction hbar W / hbar = comptonPhase m c hbar tau
      ∧ ovvImaginaryAction hbar W / hbar =
        (zitterbewegungFrequency 0 m c hbar / 2) * tau
      ∧ 0 ≤ comptonFrequency m c hbar := by
  exact ⟨iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
      g hbar hg A W hhbar.ne' haction,
    fluxInsertion_eq_ovvKernel W hbar hhbar.ne',
    ovvEntropicPhase_eq_comptonPhase W m c hbar tau hhbar.ne' hclock,
    ovvEntropicPhase_eq_half_zitterbewegungPhase W m c hbar tau hm hhbar.ne' hclock,
    entropicTime_rate_nonneg m c hbar hm hhbar⟩

/-! ## The recent worldline and Clausius--Einstein links -/

/-- The abstract clock parameter in the OVV--Compton calibration can be replaced
by the repository's actual Lorentzian arc-length functional.  On a straight
worldline this phase is the scalar entropic proper time whose rate is the
Compton frequency, evaluated on the two-point proper-time interval. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_eq_inertialWorldlineEntropicProperTime
    {d : Nat} (W : Complex) (m c hbar : Real) (q v : SpaceTime d)
    (T : Real) (hT : 0 ≤ T) (hhbar : hbar ≠ 0)
    (hclock : ovvImaginaryAction hbar W =
      m * c ^ 2 * properTimeIntegral (fun lam ↦ q + lam • v) T) :
    ovvImaginaryAction hbar W / hbar =
      entropicProperTimeFromGR (comptonFrequency m c hbar)
        (properTime q (q + T • v)) := by
  rw [← properTimeIntegral_straight q v T hT]
  rw [ovvEntropicPhase_eq_comptonPhase W m c hbar
    (properTimeIntegral (fun lam ↦ q + lam • v) T) hhbar hclock]
  rfl

/-- Under the explicit Badiali/OVV action and Clausius heat calibrations, the
same dimensionless quantity is both `S_I / hbar` and `delta Q / (k_B T)`.
This is the typed interface from the flux damping exponent to the repository's
entropic-proper-time/Clausius carrier. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_eq_clausiusEntropicProperTime
    (W : Complex) (hbar kB temp rate dTau deltaQ : Real)
    (hhbar : 0 < hbar) (hkB : 0 < kB) (htemp : 0 < temp)
    (haction : ovvImaginaryAction hbar W = hbar * (rate * dTau))
    (hheat : deltaQ = kB * temp * (rate * dTau)) :
    ovvImaginaryAction hbar W / hbar =
      entropicProperTimeFromGR rate dTau ∧
    ovvImaginaryAction hbar W / hbar = deltaQ / (kB * temp) := by
  have hfour := entropicProperTime_four_equivalences
    hhbar hkB htemp haction (show kB * (rate * dTau) = kB * (rate * dTau) by rfl) hheat
  exact ⟨hfour.1.symm, hfour.1.symm.trans hfour.2.2⟩

/-- The completed conditional chain from the recent work.  A normalized IKKT
configuration matching an OVV flux sector supplies the same complex weight; a
rest-energy calibration on an inertial worldline makes its imaginary action a
Compton entropic-proper-time clock; a Clausius heat calibration gives its
thermal reading; and the independently stated all-null-direction Jacobson
balance yields the Einstein equation with coupling `8 pi G`.

No implication between the matrix-action match and the horizon Clausius input
is silently assumed: both are fields of this theorem. -/
@[zil_level bridge_theorem]
theorem iib_ovv_worldline_clausius_einstein_chain
    {N d n : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) Complex)
    (W : Complex) (m c : Real) (q v : SpaceTime n) (duration : Real)
    (hDuration : 0 ≤ duration) (hhbar : 0 < hbar)
    (rate kB temp deltaQ : Real) (hkB : 0 < kB) (htemp : 0 < temp)
    (Ric stress : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) Real)
    (G boostKappa unruhTemp : Real)
    (hRic : Ric.IsSymm) (hStress : stress.IsSymm) (hG : G ≠ 0)
    (hBoostKappa : boostKappa ≠ 0)
    (hUnruh : unruhTemp = boostKappa / (2 * Real.pi))
    (hMatrixFlux : -iibBosonic A =
      Complex.I * (ovvImaginaryAction hbar W : Complex))
    (hClock : ovvImaginaryAction hbar W =
      m * c ^ 2 * properTimeIntegral (fun lam ↦ q + lam • v) duration)
    (hRate : rate = comptonFrequency m c hbar)
    (hHeat : deltaQ = kB * temp *
      (rate * properTime q (q + duration • v)))
    (hClausius : ∀ k : (Fin 1 ⊕ Fin n) → Real,
      k ⬝ᵥ (minkowskiMatrix *ᵥ k) = 0 →
        boostKappa * (k ⬝ᵥ (stress *ᵥ k)) =
          unruhTemp * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G))) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A mu) = fluxInsertion W
      ∧ ovvImaginaryAction hbar W / hbar =
        entropicProperTimeFromGR rate (properTime q (q + duration • v))
      ∧ ovvImaginaryAction hbar W / hbar = deltaQ / (kB * temp)
      ∧ ∃ cosmologicalConstant : Real,
        einsteinFieldEquationCosmological Ric
          (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix stress
          cosmologicalConstant (8 * Real.pi * G) ∧
        complexEinsteinFieldEquation
          (einsteinTensor Ric (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix) 0
          (stress - (cosmologicalConstant / (8 * Real.pi * G)) • minkowskiMatrix)
          (entropicStressTensor 0 0 minkowskiMatrix) (8 * Real.pi * G) := by
  have hWeight :=
    iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
      g hbar hg A W hhbar.ne' hMatrixFlux
  have hProper := ovvEntropicPhase_eq_inertialWorldlineEntropicProperTime
    W m c hbar q v duration hDuration hhbar.ne' hClock
  rw [hRate] at hHeat ⊢
  have hAction : ovvImaginaryAction hbar W = hbar *
      (comptonFrequency m c hbar * properTime q (q + duration • v)) := by
    calc
      ovvImaginaryAction hbar W =
          hbar * (ovvImaginaryAction hbar W / hbar) := by field_simp
      _ = hbar * (comptonFrequency m c hbar *
          properTime q (q + duration • v)) := by
        simpa [entropicProperTimeFromGR] using congrArg (fun x ↦ hbar * x) hProper
  have hThermal := ovvEntropicPhase_eq_clausiusEntropicProperTime W hbar kB temp
    (comptonFrequency m c hbar) (properTime q (q + duration • v)) deltaQ
    hhbar hkB htemp hAction hHeat
  obtain ⟨cosmologicalConstant, hEinstein⟩ :=
    einstein_from_clausius Ric stress G boostKappa unruhTemp hRic hStress hG
      hBoostKappa hUnruh hClausius
  have hEinsteinCoupling : 8 * Real.pi * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hG
  exact ⟨hWeight, hProper, hThermal.2, cosmologicalConstant, hEinstein,
    cosmologicalEinstein_to_equilibriumComplex Ric
      (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix stress
      cosmologicalConstant (8 * Real.pi * G) hEinsteinCoupling hEinstein⟩

/-! ## Finite-rapidity non-equilibrium continuation -/

/-- If the OVV imaginary action is calibrated by the repository's independently
defined Schmidt-rapidity action `hbar log K(eta)`, its dimensionless phase is
exactly `log K(eta)`. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_eq_logSchmidtNumber
    (W : Complex) (hbar eta : Real) (hhbar : hbar ≠ 0)
    (hRapidity : ovvImaginaryAction hbar W = entropicAction hbar eta) :
    ovvImaginaryAction hbar W / hbar = Real.log (schmidtNumber eta) := by
  rw [hRapidity]
  unfold entropicAction
  field_simp

/-- In the positive-rapidity sector, the same calibration makes the exact OVV
flux modulus equal the repository's entanglement suppression factor
`tanh eta = 1 / K(eta)`. -/
@[zil_level bridge_theorem]
theorem norm_fluxInsertion_eq_tanh_of_rapidityCalibration
    (W : Complex) (hbar eta : Real) (hhbar : hbar ≠ 0) (heta : 0 < eta)
    (hRapidity : ovvImaginaryAction hbar W = entropicAction hbar eta) :
    ‖fluxInsertion W‖ = Real.tanh eta := by
  rw [fluxInsertion_eq_ovvKernel W hbar hhbar,
    lorentzianKernel_norm_is_damping, hRapidity]
  exact suppression_eq_tanh hbar eta hhbar heta

/-- Beyond the explicit reversible-limit threshold, the calibrated OVV phase
is nonnegative and bounded by the proved exponential rapidity error
`4 exp(-2 eta)`. -/
@[zil_level bridge_theorem]
theorem ovvEntropicPhase_bounds_of_rapidityCalibration
    (W : Complex) (hbar eta : Real) (hhbar : hbar ≠ 0)
    (heta : Real.log 2 / 2 ≤ eta)
    (hRapidity : ovvImaginaryAction hbar W = entropicAction hbar eta) :
    0 ≤ ovvImaginaryAction hbar W / hbar ∧
      ovvImaginaryAction hbar W / hbar ≤ 4 * Real.exp (-(2 * eta)) := by
  rw [ovvEntropicPhase_eq_logSchmidtNumber W hbar eta hhbar hRapidity]
  exact log_schmidtNumber_le_exp_rate eta heta

/-- A rapidity-indexed normalized IKKT configuration and OVV flux trajectory
remain equal at path-weight level.  Under the independent Schmidt-action
calibration, their shared phase is `log K`, and at positive rapidity their
shared modulus is exactly `tanh eta`. -/
@[zil_level bridge_theorem]
theorem iib_ovv_rapidityPathWeightTrajectory
    {N d : Nat} (g hbar : Real) (hg : 0 < g)
    (A : Real → Fin d → Matrix (Fin N) (Fin N) Complex)
    (W : Real → Complex) (hhbar : hbar ≠ 0)
    (hMatrixFlux : ∀ eta : Real, -iibBosonic (A eta) =
      Complex.I * (ovvImaginaryAction hbar (W eta) : Complex))
    (hRapidity : ∀ eta : Real,
      ovvImaginaryAction hbar (W eta) = entropicAction hbar eta) :
    ∀ eta : Real,
      iibBosonicPathWeight g hbar
          (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A eta mu) =
          fluxInsertion (W eta)
      ∧ ovvImaginaryAction hbar (W eta) / hbar =
          Real.log (schmidtNumber eta)
      ∧ (0 < eta →
        ‖iibBosonicPathWeight g hbar
          (fun mu ↦ ((Real.sqrt g : Real) : Complex) • A eta mu)‖ =
            Real.tanh eta) := by
  intro eta
  have hWeight := iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
    g hbar hg (A eta) (W eta) hhbar (hMatrixFlux eta)
  refine ⟨hWeight,
    ovvEntropicPhase_eq_logSchmidtNumber (W eta) hbar eta hhbar (hRapidity eta), ?_⟩
  intro heta
  rw [hWeight]
  exact norm_fluxInsertion_eq_tanh_of_rapidityCalibration
    (W eta) hbar eta hhbar heta (hRapidity eta)

/-- The reusable real-sector adapter for the non-equilibrium continuation.
Jacobson supplies the cosmological equation at `8 pi G`; an explicit coupling
match rewrites it at the inference coupling, and the equilibrium-complex
adapter returns the shifted ordinary Einstein source equation required by the
existing rapidity family. -/
@[zil_level bridge_theorem]
theorem jacobsonClausius_to_inferenceRealEinstein {d : Nat}
    (Ric stress : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) Real)
    (G boostKappa unruhTemp c hbar sigma0 : Real)
    (hRic : Ric.IsSymm) (hStress : stress.IsSymm) (hG : G ≠ 0)
    (hBoostKappa : boostKappa ≠ 0)
    (hUnruh : unruhTemp = boostKappa / (2 * Real.pi))
    (hInferenceCoupling : inferenceEinsteinCoupling hbar c sigma0 ≠ 0)
    (hCoupling : 8 * Real.pi * G = inferenceEinsteinCoupling hbar c sigma0)
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → Real,
      k ⬝ᵥ (minkowskiMatrix *ᵥ k) = 0 →
        boostKappa * (k ⬝ᵥ (stress *ᵥ k)) =
          unruhTemp * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G))) :
    ∃ cosmologicalConstant : Real,
      einsteinFieldEquationCosmological Ric
        (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix stress
        cosmologicalConstant (inferenceEinsteinCoupling hbar c sigma0)
      ∧ einsteinFieldEquation Ric (Matrix.trace (minkowskiMatrix * Ric))
        minkowskiMatrix
        (stress -
          (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
            minkowskiMatrix)
        (inferenceEinsteinCoupling hbar c sigma0) := by
  obtain ⟨cosmologicalConstant, hEinstein⟩ :=
    einstein_from_clausius Ric stress G boostKappa unruhTemp hRic hStress hG
      hBoostKappa hUnruh hClausius
  rw [hCoupling] at hEinstein
  have hEquilibrium := cosmologicalEinstein_to_equilibriumComplex Ric
    (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix stress
    cosmologicalConstant (inferenceEinsteinCoupling hbar c sigma0)
    hInferenceCoupling hEinstein
  exact ⟨cosmologicalConstant, hEinstein,
    (complexEinstein_equilibrium_reduces Ric
      (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix
      (stress -
        (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
          minkowskiMatrix)
      (inferenceEinsteinCoupling hbar c sigma0)).mp hEquilibrium⟩

/-- **Jacobson equilibrium data seeds the existing non-equilibrium rapidity
family.**  Match the thermodynamic coupling `8 pi G` to the repository's
independently parameterized inference coupling.  The all-null-direction
Clausius theorem first derives the real equation with cosmological term.  After
the exact effective-stress shift, that real sector is fed to the existing
`log K` entropic-stress family, yielding a full complex-Einstein equation at
every rapidity and convergence of its imaginary curvature to zero.

The reference tensor `S0` and coupling match remain explicit model inputs; the
theorem does not derive a unique irreversible stress law from Clausius data. -/
@[zil_level bridge_theorem]
theorem jacobsonClausius_to_gFree_rapidityComplexEinsteinFamily {d : Nat}
    (Ric stress S0 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) Real)
    (G boostKappa unruhTemp c hbar sigma0 eta0 : Real)
    (hRic : Ric.IsSymm) (hStress : stress.IsSymm) (hG : G ≠ 0)
    (hBoostKappa : boostKappa ≠ 0)
    (hUnruh : unruhTemp = boostKappa / (2 * Real.pi))
    (hSigma : 0 < sigma0) (hc : 0 < c) (hhbar : 0 < hbar) (heta0 : 0 < eta0)
    (hCoupling : 8 * Real.pi * G = inferenceEinsteinCoupling hbar c sigma0)
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → Real,
      k ⬝ᵥ (minkowskiMatrix *ᵥ k) = 0 →
        boostKappa * (k ⬝ᵥ (stress *ᵥ k)) =
          unruhTemp * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G))) :
    ∃ cosmologicalConstant : Real,
      einsteinFieldEquationCosmological Ric
        (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix stress
        cosmologicalConstant (inferenceEinsteinCoupling hbar c sigma0)
      ∧ inferenceEinsteinCoupling hbar c sigma0 =
          8 * Real.pi *
            (Physlib.Thermodynamics.sphereArea
                (entropicProperDistance (inferenceMass sigma0) c hbar eta0) /
              comptonCellBits (inferenceMass sigma0) c hbar eta0) / (hbar * c)
      ∧ (∀ eta : Real,
        complexEinsteinFieldEquation
          (einsteinTensor Ric (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix)
          (inferenceEinsteinCoupling hbar c sigma0 • rapidityEntropicStress S0 eta)
          (stress -
            (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
              minkowskiMatrix)
          (rapidityEntropicStress S0 eta) (inferenceEinsteinCoupling hbar c sigma0))
      ∧ Filter.Tendsto
        (fun eta : Real ↦
          inferenceEinsteinCoupling hbar c sigma0 • rapidityEntropicStress S0 eta)
        Filter.atTop (nhds 0) := by
  have hInferenceCoupling : inferenceEinsteinCoupling hbar c sigma0 ≠ 0 := by
    unfold inferenceEinsteinCoupling
    positivity
  obtain ⟨cosmologicalConstant, hEinstein, hReal⟩ :=
    jacobsonClausius_to_inferenceRealEinstein Ric stress G boostKappa unruhTemp
      c hbar sigma0 hRic hStress hG hBoostKappa hUnruh hInferenceCoupling
      hCoupling hClausius
  have hFamily := gFree_complexEinstein_reversibleFamily Ric
    (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix
    (stress -
      (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
        minkowskiMatrix)
    S0 c hbar sigma0 eta0 hSigma hc hhbar heta0 hReal
  exact ⟨cosmologicalConstant, hEinstein, hFamily⟩

/-- **Bianchi-consistent non-equilibrium continuation.**  With a contracted
Bianchi identity for the Jacobson-derived real tensor and a divergence-free
reference entropic stress, every rapidity member satisfies the complex Einstein
equation, the complex Bianchi identity, and conservation of both shifted matter
and rapidity-scaled entropic sources. -/
@[zil_level bridge_theorem]
theorem jacobsonClausius_to_gFree_rapidityComplexEinsteinConservationFamily
    {d : Nat}
    (Div : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) Real →ₗ[Real]
      ((Fin 1 ⊕ Fin d) → Real))
    (Ric stress S0 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) Real)
    (G boostKappa unruhTemp c hbar sigma0 : Real)
    (hRic : Ric.IsSymm) (hStress : stress.IsSymm) (hG : G ≠ 0)
    (hBoostKappa : boostKappa ≠ 0)
    (hUnruh : unruhTemp = boostKappa / (2 * Real.pi))
    (hSigma : 0 < sigma0) (hc : 0 < c) (hhbar : 0 < hbar)
    (hCoupling : 8 * Real.pi * G = inferenceEinsteinCoupling hbar c sigma0)
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → Real,
      k ⬝ᵥ (minkowskiMatrix *ᵥ k) = 0 →
        boostKappa * (k ⬝ᵥ (stress *ᵥ k)) =
          unruhTemp * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G)))
    (hBianchi : Div
      (einsteinTensor Ric (Matrix.trace (minkowskiMatrix * Ric))
        minkowskiMatrix) = 0)
    (hS0 : Div S0 = 0) :
    ∃ cosmologicalConstant : Real,
      einsteinFieldEquationCosmological Ric
        (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix stress
        cosmologicalConstant (inferenceEinsteinCoupling hbar c sigma0)
      ∧ ∀ eta : Real,
        complexEinsteinFieldEquation
            (einsteinTensor Ric (Matrix.trace (minkowskiMatrix * Ric))
              minkowskiMatrix)
            (inferenceEinsteinCoupling hbar c sigma0 • rapidityEntropicStress S0 eta)
            (stress -
              (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
                minkowskiMatrix)
            (rapidityEntropicStress S0 eta) (inferenceEinsteinCoupling hbar c sigma0)
        ∧ complexDiv Div
            (complexEinsteinTensor
              (einsteinTensor Ric (Matrix.trace (minkowskiMatrix * Ric))
                minkowskiMatrix)
              (inferenceEinsteinCoupling hbar c sigma0 •
                rapidityEntropicStress S0 eta)) = 0
        ∧ Div
            (stress -
              (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
                minkowskiMatrix) = 0
        ∧ Div (rapidityEntropicStress S0 eta) = 0 := by
  have hInferenceCoupling : inferenceEinsteinCoupling hbar c sigma0 ≠ 0 := by
    unfold inferenceEinsteinCoupling
    positivity
  obtain ⟨cosmologicalConstant, hEinstein, hReal⟩ :=
    jacobsonClausius_to_inferenceRealEinstein Ric stress G boostKappa unruhTemp
      c hbar sigma0 hRic hStress hG hBoostKappa hUnruh hInferenceCoupling
      hCoupling hClausius
  refine ⟨cosmologicalConstant, hEinstein, ?_⟩
  exact gFree_complexEinstein_conservationFamily Div Ric
    (Matrix.trace (minkowskiMatrix * Ric)) minkowskiMatrix
    (stress -
      (cosmologicalConstant / inferenceEinsteinCoupling hbar c sigma0) •
        minkowskiMatrix)
    S0 c hbar sigma0 hSigma hc hhbar hReal hBianchi hS0

end Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge

end

/- ZIL-BEGIN -/

open Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge

zil attach fluxInsertion_eq_ovvKernel where
  formalizes @ "claim:the-ovv-type-iib-flux-insertion-is-the-common-complex-action-kernel-with-imaginary-action-minus-hbar-pi-over-two-times-im-w",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-hartle-hawking-wave-function-for-flux-compactifications",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.fluxInsertion_eq_lorentzianKernel"

zil attach iibBosonicPathWeight_translation_invariant where
  formalizes @ "claim:the-ikkt-central-translation-symmetry-is-preserved-by-the-common-complex-action-path-weight",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonic_translation_invariant"

zil attach iibBosonicPathWeight_coupling_absorbed where
  formalizes @ "claim:the-positive-ikkt-coupling-is-absorbed-at-the-complex-action-path-weight-level",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonicAction_coupling_absorbed"

zil attach iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match where
  formalizes @ "claim:after-the-iib-matrix-coupling-is-absorbed-a-normalized-action-match-makes-the-ikkt-path-weight-equal-the-ovv-flux-insertion",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-bosonic-action-equals-the-purely-imaginary-ovv-flux-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonicAction_coupling_absorbed",
  caveat @ "claim:this-is-a-typed-common-weight-bridge-not-a-derivation-of-ovv-flux-compactification-from-the-ikkt-matrix-model"

zil attach iibRescaledBosonicPathWeight_eq_fluxSectorWeight_of_normalized_match where
  formalizes @ "claim:the-matched-rescaled-ikkt-weight-is-the-actual-finite-electric-magnetic-ovv-flux-sector-weight",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-bosonic-action-equals-the-purely-imaginary-ovv-finite-flux-superpotential-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.fluxSuperpotential",
  caveat @ "claim:the-action-match-remains-explicit-and-is-not-derived-from-the-two-type-iib-presentations"

zil attach normSq_iibRescaledBosonicPathWeight_eq_holomorphicFluxWave where
  formalizes @ "claim:under-the-action-match-the-rescaled-ikkt-path-weight-and-ovv-holomorphic-topological-string-wave-have-the-same-norm-square",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-bosonic-action-equals-the-purely-imaginary-ovv-flux-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.holomorphicFluxWave_normSq_eq_realPolarization"

zil attach ovvEntropicPhase_eq_comptonPhase where
  formalizes @ "claim:under-the-explicit-rest-energy-calibration-the-ovv-imaginary-action-in-hbar-units-is-the-entropic-compton-phase",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-m-c-squared-times-proper-time",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.ħ_comptonPhase_eq_restEnergy_properTime",
  caveat @ "claim:the-calibration-does-not-claim-that-type-iib-flux-data-derives-a-particle-mass"

zil attach norm_fluxInsertion_eq_exp_neg_comptonPhase where
  formalizes @ "claim:under-rest-energy-calibration-the-ovv-flux-weight-modulus-is-exp-minus-the-compton-entropic-phase",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-m-c-squared-times-proper-time",
  supported_by @ "lean:Physlib.QFT.PathIntegral.lorentzianKernel_norm_is_damping"

zil attach ovvEntropicPhase_monotone_of_comptonCalibration where
  formalizes @ "claim:a-calibrated-ovv-flux-trajectory-inherits-the-monotone-compton-entropic-time-arrow",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-m-c-squared-times-proper-time",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.comptonPhase_monotone"

zil attach ovvSuperpotential_im_nonpos_of_comptonCalibration where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:a-positive-hbar-nonnegative-mass-future-directed-compton-calibration-selects-the-nonpositive-im-w-ovv-damping-sector",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-m-c-squared-times-proper-time",
  caveat @ "claim:generic-ovv-flux-insertions-can-enhance-the-weight-the-damping-sign-follows-only-in-the-calibrated-physical-future-sector"

zil attach iib_ovv_comptonFuture_damping_sector where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match",
  supported_by @ "lean:ovvSuperpotential_im_nonpos_of_comptonCalibration",
  formalizes @ "claim:in-the-calibrated-physical-future-the-matched-rescaled-ikkt-ovv-weight-is-nonexpansive-and-im-w-is-nonpositive",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-bosonic-action-equals-the-purely-imaginary-ovv-flux-action",
  requires @ "assumption:the-ovv-imaginary-action-equals-m-c-squared-times-proper-time",
  caveat @ "claim:nonexpansiveness-is-a-sector-theorem-not-a-property-of-every-ovv-flux-insertion"

zil attach iib_ovv_entropicTime_compton_zitterbewegung_chain where
  formalizes @ "claim:the-matched-ovv-and-rescaled-iib-matrix-weights-share-one-entropic-phase-which-under-rest-energy-calibration-is-the-compton-clock-and-half-the-rest-zitterbewegung-clock",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-bosonic-action-equals-the-purely-imaginary-ovv-flux-action",
  requires @ "assumption:the-ovv-imaginary-action-equals-m-c-squared-times-proper-time",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton",
  caveat @ "claim:the-theorem-composes-exact-carriers-under-two-visible-cross-sector-calibrations-and-does-not-identify-the-ikkt-model-with-an-ovv-compactification-or-predict-the-compton-mass-scale"

zil attach ovvEntropicPhase_eq_inertialWorldlineEntropicProperTime where
  formalizes @ "claim:the-ovv-entropic-phase-calibrated-by-rest-energy-on-a-straight-worldline-is-the-compton-rate-times-the-lorentzian-interval-proper-time",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-rest-energy-times-the-repository-worldline-proper-time-integral",
  supported_by @ "lean:SpaceTime.properTimeIntegral_straight",
  supported_by @ "lean:Physlib.SpaceTime.entropicProperTimeFromGR",
  caveat @ "claim:the-worldline-theorem-removes-the-abstract-time-parameter-but-retains-the-explicit-rest-energy-calibration"

zil attach ovvEntropicPhase_eq_clausiusEntropicProperTime where
  formalizes @ "claim:under-explicit-action-and-heat-calibrations-the-ovv-damping-exponent-is-both-s-i-over-hbar-and-delta-q-over-k-b-t",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-and-clausius-heat-increment-represent-the-same-entropic-proper-time",
  supported_by @ "lean:Physlib.SpaceTime.entropicProperTime_four_equivalences",
  caveat @ "claim:this-is-the-common-scalar-clausius-interface-not-a-derivation-of-horizon-heat-flux-from-flux-compactification"

zil attach iib_ovv_worldline_clausius_einstein_chain where
  formalizes @ "claim:a-matched-iib-ovv-weight-calibrated-on-a-lorentzian-worldline-has-a-clausius-entropic-time-reading-and-the-all-null-direction-jacobson-balance-yields-both-the-real-cosmological-einstein-equation-and-its-equilibrium-complex-einstein-presentation",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-bosonic-action-equals-the-purely-imaginary-ovv-flux-action",
  requires @ "assumption:the-ovv-imaginary-action-equals-rest-energy-times-the-worldline-proper-time-integral",
  requires @ "assumption:the-same-entropic-proper-time-calibrates-the-horizon-heat-increment",
  requires @ "assumption:the-jacobson-clausius-balance-holds-in-every-local-null-direction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius",
  caveat @ "claim:the-capstone-composes-four-visible-physical-inputs-and-does-not-derive-horizon-thermodynamics-or-einstein-gravity-from-the-iib-matrix-model-alone"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.cosmologicalEinstein_to_equilibriumComplex where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinstein_equilibrium_reduces",
  formalizes @ "claim:a-real-einstein-equation-with-cosmological-term-embeds-exactly-in-the-equilibrium-complex-einstein-sector-after-shifting-the-cosmological-term-to-the-effective-real-stress",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-stress-shift-is-an-algebraic-presentation-adapter-not-a-dynamical-derivation-of-vacuum-energy-or-the-imaginary-sector"

zil attach ovvEntropicPhase_eq_logSchmidtNumber where
  formalizes @ "claim:under-the-explicit-schmidt-rapidity-calibration-the-ovv-imaginary-action-in-hbar-units-is-log-of-the-schmidt-number",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-the-repository-schmidt-rapidity-entropic-action-hbar-log-k",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.entropicAction"

zil attach norm_fluxInsertion_eq_tanh_of_rapidityCalibration where
  formalizes @ "claim:under-schmidt-rapidity-calibration-the-positive-rapidity-ovv-flux-modulus-is-exactly-tanh-eta-equal-to-the-entanglement-suppression-factor-one-over-k",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-the-repository-schmidt-rapidity-entropic-action-hbar-log-k",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.suppression_eq_tanh",
  caveat @ "claim:the-tanh-law-follows-from-the-visible-cross-sector-calibration-and-is-not-a-generic-property-of-every-ovv-flux-sector"

zil attach ovvEntropicPhase_bounds_of_rapidityCalibration where
  formalizes @ "claim:beyond-log-two-over-two-the-schmidt-calibrated-ovv-entropic-phase-is-between-zero-and-four-exp-minus-two-eta",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-ovv-imaginary-action-equals-the-repository-schmidt-rapidity-entropic-action-hbar-log-k",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.log_schmidtNumber_le_exp_rate",
  caveat @ "claim:the-exponential-bound-belongs-to-the-explicit-schmidt-rapidity-parametrization-not-to-arbitrary-flux-trajectories"

zil attach iib_ovv_rapidityPathWeightTrajectory where
  formalizes @ "claim:a-rapidity-indexed-normalized-ikkt-configuration-matched-to-an-ovv-flux-trajectory-shares-its-path-weight-log-k-phase-and-positive-rapidity-tanh-eta-modulus",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-normalized-ikkt-action-matches-the-ovv-imaginary-action-at-every-rapidity",
  requires @ "assumption:the-ovv-imaginary-action-equals-hbar-log-k-at-every-rapidity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge.iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match",
  caveat @ "claim:the-trajectory-theorem-transports-visible-pointwise-matches-and-does-not-derive-the-flux-trajectory-from-ikkt-dynamics"

zil attach jacobsonClausius_to_inferenceRealEinstein where
  formalizes @ "claim:the-jacobson-clausius-cosmological-einstein-equation-at-a-matched-inference-coupling-supplies-the-shifted-real-source-equation-needed-by-the-complex-einstein-rapidity-family",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-all-null-direction-jacobson-clausius-balance",
  requires @ "assumption:eight-pi-g-equals-the-repository-inference-einstein-coupling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.cosmologicalEinstein_to_equilibriumComplex",
  caveat @ "claim:the-effective-stress-shift-is-exact-algebra-but-the-coupling-identification-remains-a-visible-cross-model-input"

zil attach jacobsonClausius_to_gFree_rapidityComplexEinsteinFamily where
  formalizes @ "claim:the-jacobson-clausius-derived-real-cosmological-einstein-sector-seeds-the-existing-log-k-non-equilibrium-complex-einstein-family-at-the-matched-g-free-inference-coupling-and-its-imaginary-curvature-converges-to-zero",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-all-null-direction-jacobson-clausius-balance",
  requires @ "assumption:eight-pi-g-equals-the-repository-inference-einstein-coupling",
  requires @ "model:the-entropic-stress-is-log-k-times-a-supplied-reference-tensor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_reversibleFamily",
  caveat @ "claim:the-family-reuses-an-explicit-model-interpolation-and-does-not-derive-a-unique-irreversible-stress-law-from-clausius-thermodynamics"

zil attach jacobsonClausius_to_gFree_rapidityComplexEinsteinConservationFamily where
  formalizes @ "claim:with-real-bianchi-and-divergence-free-reference-entropic-stress-the-jacobson-seeded-rapidity-family-satisfies-the-complex-einstein-equation-complex-bianchi-and-both-source-conservation-laws-at-every-rapidity",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-all-null-direction-jacobson-clausius-balance",
  requires @ "assumption:eight-pi-g-equals-the-repository-inference-einstein-coupling",
  requires @ "assumption:the-real-einstein-tensor-and-reference-entropic-stress-are-divergence-free",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily",
  caveat @ "claim:bianchi-consistency-and-conservation-propagate-the-supplied-log-k-source-model-they-do-not-select-that-model-uniquely"

zil_file_contract physlib.ovvIIBEntropicClockBridge where
  promises "A typed bridge from the Ooguri-Vafa-Verlinde Type-IIB flux insertion through the common complex-action kernel to the IKKT/IIB bosonic matrix action and the entropic Compton-Zitterbewegung clock. The OVV imaginary action and its dimensionless entropic phase are exact. IKKT central translations leave both the action and path weight invariant, and the positive coupling is absorbed at path-weight level by the existing matrix rescaling theorem. Under an explicit normalized-action match the rescaled IKKT weight is the actual finite OVV electric-magnetic flux-sector weight and has the same norm square as the holomorphic topological-string wave. Under a separate rest-energy action calibration the same phase is the Compton phase and half the rest-frame Zitterbewegung phase, its norm is exp minus that phase, and calibrated flux trajectories inherit the monotone entropic-time arrow. In the nonnegative-proper-time sector the calibration selects Im W nonpositive and makes the matched weight nonexpansive. The formerly abstract time parameter is also instantiated by the Lorentzian inertial-worldline proper-time integral. Through the existing scalar entropic-proper-time carrier the phase has the Clausius reading delta Q over k B T, and, under the separately visible all-null-direction Jacobson balance, the recent equation-of-state theorem yields the Einstein equation with coupling eight pi G. Moving its cosmological term to the effective real stress embeds that derived equation exactly in the equilibrium complex-Einstein presentation. Under a separate Schmidt-rapidity calibration the OVV phase becomes log K, obeys the explicit four exp minus two eta bound beyond the proved threshold, and its flux modulus becomes tanh eta. The IKKT-OVV equality, phase and modulus hold pointwise along any trajectory satisfying the visible action matches. Matching the Jacobson coupling to the G-free inference coupling lets the derived real sector seed the existing log-K complex-Einstein family at every rapidity, whose imaginary curvature converges to zero. With real Bianchi and a divergence-free reference entropic stress, that entire family obeys complex Bianchi and conserves both sources. The reference entropic stress remains a visible model input; no unique irreversible source law is inferred from equilibrium Clausius data."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.fluxInsertion",
    "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonicAction",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegungFrequency",
    "lean:SpaceTime.properTimeIntegral",
    "lean:Physlib.SpaceTime.entropicProperTime_four_equivalences",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.cosmologicalEinstein_to_equilibriumComplex",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.suppression_eq_tanh",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_reversibleFamily",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily"
  ]
  forbids_substitutes [
    "a derivation of the OVV flux compactification from the IKKT matrix model",
    "a claim that Type-IIB flux data fixes a particle mass or Compton frequency",
    "hiding either the matrix-action match or the rest-energy clock calibration",
    "a claim that the IIB matrix or OVV flux action alone derives the Clausius law or Einstein equation",
    "a claim that equilibrium Clausius thermodynamics uniquely determines the finite-rapidity entropic stress tensor"
  ]
  witnessed_by [
    iibBosonicAction_translation_invariant,
    iibBosonicPathWeight_translation_invariant,
    iibBosonicPathWeight_coupling_absorbed,
    fluxInsertion_eq_ovvKernel,
    ovvImaginaryAction_div_hbar,
    iibBosonicPathWeight_eq_fluxInsertion_of_action_match,
    iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match,
    iibRescaledBosonicPathWeight_eq_fluxSectorWeight_of_normalized_match,
    normSq_iibRescaledBosonicPathWeight_eq_holomorphicFluxWave,
    ovvEntropicPhase_eq_comptonPhase,
    ovvEntropicPhase_eq_half_zitterbewegungPhase,
    norm_fluxInsertion_eq_exp_neg_comptonPhase,
    ovvSuperpotential_im_nonpos_of_comptonCalibration,
    norm_fluxInsertion_le_one_of_comptonCalibration,
    ovvEntropicPhase_monotone_of_comptonCalibration,
    iib_ovv_comptonFuture_damping_sector,
    iib_ovv_entropicTime_compton_zitterbewegung_chain,
    ovvEntropicPhase_eq_inertialWorldlineEntropicProperTime,
    ovvEntropicPhase_eq_clausiusEntropicProperTime,
    iib_ovv_worldline_clausius_einstein_chain,
    ovvEntropicPhase_eq_logSchmidtNumber,
    norm_fluxInsertion_eq_tanh_of_rapidityCalibration,
    ovvEntropicPhase_bounds_of_rapidityCalibration,
    iib_ovv_rapidityPathWeightTrajectory,
    jacobsonClausius_to_inferenceRealEinstein,
    jacobsonClausius_to_gFree_rapidityComplexEinsteinFamily,
    jacobsonClausius_to_gFree_rapidityComplexEinsteinConservationFamily
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.ovvIIBEntropicClockBridge
