/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
public import Physlib.Relativity.Special.HyperbolicBoost
public import Physlib.Relativity.Special.ProperTimeWorldlineIntegral

meta import Zil

/-!
# G-free Compton rapidity clock

This module constructs the flat 1+1-dimensional rapidity geometry of one
counted Compton tick directly from GFreeComptonCellCalibration. It proves
the de Broglie mass shell, Minkowski phase, proper-time integral, and cell-area
closure without an actual finite tiling or a natural-number count-agreement
field. A finite relational clock may inherit this API through its G-free base,
but it is not a premise of these results.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
namespace GFreeComptonCellCalibration

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
open Physlib.Relativity.Special

/-! # A. Constructed rapidity geometry -/

/-- The coordinate duration of one counted Compton tick at rapidity `theta`.
This depends only on the G-free counted screen data, not on a finite tiling. -/
noncomputable def rapidityCoordinateTick
    (B : GFreeComptonCellCalibration) (theta : ℝ) : ℝ :=
  B.countedPlanckTime / Real.sqrt (1 - Real.tanh theta ^ 2)

/-- The de Broglie four-momentum reconstructed directly from G-free counted
screen data at dimensionless velocity `beta`. -/
noncomputable def deBroglieFourMomentum
    (B : GFreeComptonCellCalibration) (beta : ℝ) : Lorentz.Vector 1 :=
  Sum.elim
    (fun _ => B.hbar * phaseFrequency
      (comptonFrequency B.screenMass B.lightSpeed B.hbar) beta / B.lightSpeed)
    (fun _ => B.hbar * phaseWavenumber
      (comptonFrequency B.screenMass B.lightSpeed B.hbar) B.lightSpeed beta)

/-- The inertial displacement reconstructed from G-free counted screen data. -/
def worldlineDisplacement
    (B : GFreeComptonCellCalibration) (beta deltaT : ℝ) : Lorentz.Vector 1 :=
  Sum.elim
    (fun _ => B.lightSpeed * deltaT)
    (fun _ => beta * B.lightSpeed * deltaT)

/-- The Minkowski-paired de Broglie phase of the G-free reconstructed momentum
and inertial displacement. -/
noncomputable def minkowskiWorldlinePhaseAdvance
    (B : GFreeComptonCellCalibration) (beta deltaT : ℝ) : ℝ :=
  Lorentz.Vector.minkowskiProduct
      (B.deBroglieFourMomentum beta) (B.worldlineDisplacement beta deltaT) /
    B.hbar

/-- The plane-wave phase advance along a trajectory with dimensionless velocity
beta. -/
noncomputable def worldlinePhaseAdvance
    (omega0 c beta deltaT : ℝ) : ℝ :=
  (phaseFrequency omega0 beta -
    phaseWavenumber omega0 c beta * (beta * c)) * deltaT

/-- Along the group trajectory, the de Broglie phase rate is the time-dilated
Compton rate. -/
lemma worldlinePhaseRate_eq_timeDilation
    (omega0 c beta : ℝ) (hc : c ≠ 0) (hbeta : beta ^ 2 < 1) :
    phaseFrequency omega0 beta - phaseWavenumber omega0 c beta * (beta * c) =
      omega0 * Real.sqrt (1 - beta ^ 2) := by
  have hspos : 0 < Real.sqrt (1 - beta ^ 2) :=
    Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (1 - beta ^ 2) ^ 2 = 1 - beta ^ 2 :=
    Real.sq_sqrt (by linarith)
  unfold phaseFrequency phaseWavenumber
  field_simp [hspos.ne']
  rw [hsq]

/-- Rapidity gives the standard Lorentz dilation of the counted Compton tick. -/
lemma rapidityCoordinateTick_eq_cosh_mul_countedPlanckTime
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    B.rapidityCoordinateTick theta = Real.cosh theta * B.countedPlanckTime := by
  unfold rapidityCoordinateTick
  have hgamma := γ_tanh_eq_cosh theta
  unfold LorentzGroup.γ at hgamma
  have hgamma' : (Real.sqrt (1 - Real.tanh theta ^ 2))⁻¹ = Real.cosh theta := by
    simpa using hgamma
  rw [div_eq_mul_inv, hgamma']
  ring

/-- The temporal component of the G-free reconstructed de Broglie momentum is
`m c cosh theta`. -/
lemma deBroglieFourMomentum_tanh_time
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    B.deBroglieFourMomentum (Real.tanh theta) (Sum.inl 0) =
      B.screenMass * B.lightSpeed * Real.cosh theta := by
  unfold deBroglieFourMomentum phaseFrequency comptonFrequency
  simp only [Sum.elim_inl]
  have hgamma := γ_tanh_eq_cosh theta
  unfold LorentzGroup.γ at hgamma
  have hgamma' : (Real.sqrt (1 - Real.tanh theta ^ 2))⁻¹ = Real.cosh theta := by
    simpa using hgamma
  rw [show B.screenMass * B.lightSpeed ^ 2 / B.hbar /
      Real.sqrt (1 - Real.tanh theta ^ 2) =
      B.screenMass * B.lightSpeed ^ 2 / B.hbar *
        (Real.sqrt (1 - Real.tanh theta ^ 2))⁻¹ by ring,
    hgamma']
  field_simp [B.hbar_pos.ne', B.lightSpeed_pos.ne']

/-- The spatial component of the G-free reconstructed de Broglie momentum is
`m c sinh theta`. -/
lemma deBroglieFourMomentum_tanh_space
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    B.deBroglieFourMomentum (Real.tanh theta) (Sum.inr 0) =
      B.screenMass * B.lightSpeed * Real.sinh theta := by
  unfold deBroglieFourMomentum phaseWavenumber comptonFrequency
  simp only [Sum.elim_inr]
  have hgamma := γ_tanh_eq_cosh theta
  unfold LorentzGroup.γ at hgamma
  have hgamma' : (Real.sqrt (1 - Real.tanh theta ^ 2))⁻¹ = Real.cosh theta := by
    simpa using hgamma
  rw [show B.screenMass * B.lightSpeed ^ 2 / B.hbar * Real.tanh theta /
      (B.lightSpeed * Real.sqrt (1 - Real.tanh theta ^ 2)) =
      B.screenMass * B.lightSpeed ^ 2 / B.hbar * Real.tanh theta *
        (Real.sqrt (1 - Real.tanh theta ^ 2))⁻¹ / B.lightSpeed by ring,
    hgamma', Real.tanh_eq_sinh_div_cosh]
  field_simp [B.hbar_pos.ne', B.lightSpeed_pos.ne', (Real.cosh_pos theta).ne']

/-- The G-free reconstructed de Broglie momentum lies on its Minkowski mass
shell for every rapidity. -/
lemma deBroglieFourMomentum_tanh_massShell
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    Lorentz.Vector.minkowskiProduct
        (B.deBroglieFourMomentum (Real.tanh theta))
        (B.deBroglieFourMomentum (Real.tanh theta)) =
      (B.screenMass * B.lightSpeed) ^ 2 := by
  rw [Lorentz.Vector.minkowskiProduct_toCoord]
  simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  rw [B.deBroglieFourMomentum_tanh_time, B.deBroglieFourMomentum_tanh_space]
  linear_combination
    (B.screenMass * B.lightSpeed) ^ 2 * Real.cosh_sq_sub_sinh_sq theta

/-- The reconstructed Minkowski pairing equals the scalar plane-wave phase. -/
lemma minkowskiWorldlinePhaseAdvance_eq_worldlinePhaseAdvance
    (B : GFreeComptonCellCalibration) (beta deltaT : ℝ) :
    B.minkowskiWorldlinePhaseAdvance beta deltaT =
      worldlinePhaseAdvance
        (comptonFrequency B.screenMass B.lightSpeed B.hbar)
        B.lightSpeed beta deltaT := by
  unfold minkowskiWorldlinePhaseAdvance
  rw [Lorentz.Vector.minkowskiProduct_toCoord]
  unfold deBroglieFourMomentum worldlineDisplacement
    worldlinePhaseAdvance
  simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr]
  field_simp [B.hbar_pos.ne', B.lightSpeed_pos.ne']

/-- The G-free reconstructed Minkowski phase advances by one radian over one
rapidity-dilated counted Compton tick. -/
lemma minkowskiWorldlinePhaseAdvance_rapidityTick_eq_one
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    B.minkowskiWorldlinePhaseAdvance (Real.tanh theta)
      (B.rapidityCoordinateTick theta) = 1 := by
  rw [B.minkowskiWorldlinePhaseAdvance_eq_worldlinePhaseAdvance]
  unfold worldlinePhaseAdvance rapidityCoordinateTick
  have hbeta : Real.tanh theta ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one (Real.tanh theta)).2 (abs_tanh_lt_one theta)
  rw [worldlinePhaseRate_eq_timeDilation _ _ _
      B.lightSpeed_pos.ne' hbeta,
    B.countedPlanckTime_eq_inv_comptonFrequency]
  have hs : Real.sqrt (1 - Real.tanh theta ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith)).ne'
  have homega :
      comptonFrequency B.screenMass B.lightSpeed B.hbar ≠ 0 := by
    unfold comptonFrequency
    exact div_ne_zero
      (mul_ne_zero B.screenMass_pos.ne' (pow_ne_zero 2 B.lightSpeed_pos.ne'))
      B.hbar_pos.ne'
  field_simp

/-- The proper time of the G-free reconstructed rapidity displacement is the
counted Compton tick length. -/
lemma properTime_rapidityTick_eq_lightSpeed_mul_countedPlanckTime
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    SpaceTime.properTime 0
        (B.worldlineDisplacement (Real.tanh theta)
          (B.rapidityCoordinateTick theta)) =
      B.lightSpeed * B.countedPlanckTime := by
  have hdelta : 0 ≤ B.countedPlanckTime := by
    unfold countedPlanckTime countedPlanckLength
    exact (div_pos (Real.sqrt_pos.2 B.cellArea_pos) B.lightSpeed_pos).le
  have hcosh : Real.cosh theta ≠ 0 := (Real.cosh_pos theta).ne'
  have hnorm :
      Lorentz.Vector.minkowskiProduct
          (B.worldlineDisplacement (Real.tanh theta)
            (B.rapidityCoordinateTick theta))
          (B.worldlineDisplacement (Real.tanh theta)
            (B.rapidityCoordinateTick theta)) =
        (B.lightSpeed * B.countedPlanckTime) ^ 2 := by
    rw [Lorentz.Vector.minkowskiProduct_toCoord]
    simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    unfold worldlineDisplacement
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [B.rapidityCoordinateTick_eq_cosh_mul_countedPlanckTime,
      Real.tanh_eq_sinh_div_cosh]
    field_simp [hcosh]
    linear_combination
      (B.lightSpeed * B.countedPlanckTime) ^ 2 *
        Real.cosh_sq_sub_sinh_sq theta
  unfold SpaceTime.properTime
  simp only [sub_zero, hnorm]
  exact Real.sqrt_sq (mul_nonneg B.lightSpeed_pos.le hdelta)

/-- The straight-worldline proper-time integral of the G-free reconstructed
rapidity trajectory is the counted Compton tick length. -/
lemma properTimeIntegral_rapidityTick_eq_lightSpeed_mul_countedPlanckTime
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    SpaceTime.properTimeIntegral
        (fun lam => lam • B.worldlineDisplacement (Real.tanh theta)
          (B.rapidityCoordinateTick theta)) 1 =
      B.lightSpeed * B.countedPlanckTime := by
  let v := B.worldlineDisplacement (Real.tanh theta)
    (B.rapidityCoordinateTick theta)
  have hstraight := SpaceTime.properTimeIntegral_straight
    (0 : SpaceTime 1) v 1 (by norm_num)
  simpa [v, B.properTime_rapidityTick_eq_lightSpeed_mul_countedPlanckTime theta]
    using hstraight

/-- The squared proper tick length of the G-free rapidity construction is the
counted cell area. -/
lemma rapidityTickLength_sq_eq_cellArea
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    (B.lightSpeed * (B.rapidityCoordinateTick theta / Real.cosh theta)) ^ 2 =
      B.cellArea := by
  rw [B.rapidityCoordinateTick_eq_cosh_mul_countedPlanckTime]
  field_simp [(Real.cosh_pos theta).ne']
  unfold countedPlanckTime
  field_simp [B.lightSpeed_pos.ne']
  unfold countedPlanckLength
  exact Real.sq_sqrt B.cellArea_pos.le

/-- The premise-minimal rapidity realization: G-free counted screen data alone
construct the momentum, worldline, proper-time integral, unit phase tick, and
area quantum. No finite tiling or finite-clock calibration is required. -/
@[zil_level bridge_theorem]
lemma rapidityMinkowskiPhaseTick_areaQuantum_closure
    (B : GFreeComptonCellCalibration) (theta : ℝ) :
    B.minkowskiWorldlinePhaseAdvance (Real.tanh theta)
        (B.rapidityCoordinateTick theta) = 1
      ∧ SpaceTime.properTimeIntegral
          (fun lam => lam • B.worldlineDisplacement (Real.tanh theta)
            (B.rapidityCoordinateTick theta)) 1 =
        B.lightSpeed * B.countedPlanckTime
      ∧ (B.lightSpeed *
          (B.rapidityCoordinateTick theta / Real.cosh theta)) ^ 2 = B.cellArea
      ∧ B.cellArea = B.countedNewtonG * B.hbar / B.lightSpeed ^ 3 :=
  ⟨B.minkowskiWorldlinePhaseAdvance_rapidityTick_eq_one theta,
    B.properTimeIntegral_rapidityTick_eq_lightSpeed_mul_countedPlanckTime theta,
    B.rapidityTickLength_sq_eq_cellArea theta,
    B.cellArea_eq_countedPlanckArea⟩

end GFreeComptonCellCalibration
end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

end

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant in
#physlib_axiom_clean_all [
  GFreeComptonCellCalibration.rapidityMinkowskiPhaseTick_areaQuantum_closure ]

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant in
#physlib_non_vacuous_all [
  GFreeComptonCellCalibration.rapidityMinkowskiPhaseTick_areaQuantum_closure ]

/-! # B. ZIL metadata -/

/- ZIL-BEGIN -/

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

zil attach GFreeComptonCellCalibration.rapidityMinkowskiPhaseTick_areaQuantum_closure where
  formalizes @ "claim:g-free-counted-screen-data-construct-explicit-minkowski-\
rapidity-momentum-worldline-proper-time-unit-phase-and-area-quantum-closure",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.\
cellArea_eq_countedPlanckArea",
  supported_by @ "lean:Physlib.Relativity.Special.SpaceTime.\
properTimeIntegral_straight",
  caveat @ "epistemic:this-needs-no-finite-tiling-or-natural-count-agreement-\
but-remains-a-constructed-flat-minkowski-realization-not-gravitational-field-\
quantization"

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

/- ZIL-END -/
