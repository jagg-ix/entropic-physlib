/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.TolmanScaling
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.Relativity.Special.UnruhEntropicRate
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS

/-!
# Tolman-Ehrenfest redshift for temperature, dissipation, and KMS rates

This module ports only the connected Tolman-Ehrenfest content from the complex-action/entropic-time reference tree:

* complex-action/entropic-time's `T_loc(x) = T_infty / N(x)` becomes a concrete `TolmanScaling` over
  `Physlib.SpaceTime.Lapse`.
* complex-action/entropic-time's redshifted dissipation rate `gamma_infty(x) = N(x) * gamma_loc(x)` becomes a reusable
  reconstruction map from a local field to its infinity-frame rate.
* complex-action/entropic-time's dimensional dictionary `beta_tilde = hbar * gamma` is proved to commute with the redshift.
* The same law is connected to the existing `ThermoFieldDynamics.KMS` thermal rate `k_B T / hbar`.
* For horizons, Tolman-redshifting the Hawking temperature recovers the existing
  `SurfaceGravityEntropicRate.lambdaSG` / `UnruhEntropicRate.lambdaU`.

The intentionally omitted complex-action/entropic-time material is the plugin-slot and flat-background wrapper layer.  In Physlib,
those statements are useful only when stated through existing structures such as `Lapse.unit`, `TolmanScaling`,
`KMSScale`, and `SurfaceGravityEntropicRate`; this file does exactly that and adds no standalone vacuous
physics assertions.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
open Physlib.Relativity.SemiClassical
open Physlib.Relativity.Special

variable {sd : ℕ}

/-! ## §A — Tolman-Ehrenfest temperature as an existing `TolmanScaling` -/

/-- **Tolman-Ehrenfest temperature scaling** over a Physlib lapse:

`T_loc(x) = T_infty / N(x)`, hence `T_loc(x) * N(x) = T_infty`.

This is the connected Physlib form of the complex-action/entropic-time reference definition `Tloc_redshift`. -/
def tolmanEhrenfestTemperature (L : Lapse sd) (T_infty : ℝ) : TolmanScaling sd where
  L := L
  asymptotic := T_infty
  localValue := fun x => T_infty / L.N x
  law := fun x => Lapse.tolman_invariant L T_infty x

@[simp] theorem tolmanEhrenfestTemperature_localValue
    (L : Lapse sd) (T_infty : ℝ) (x : SpaceTime sd) :
    (tolmanEhrenfestTemperature L T_infty).localValue x = T_infty / L.N x :=
  rfl

/-- Positive infinity-frame temperature gives positive local Tolman-Ehrenfest temperature. -/
theorem tolmanEhrenfestTemperature_pos
    (L : Lapse sd) {T_infty : ℝ} (hT : 0 < T_infty) (x : SpaceTime sd) :
    0 < (tolmanEhrenfestTemperature L T_infty).localValue x :=
  div_pos hT (L.N_pos x)

/-- Unit-lapse limit: no gravitational redshift, so local and infinity-frame temperatures agree. -/
theorem tolmanEhrenfestTemperature_unit_lapse
    (T_infty : ℝ) (x : SpaceTime sd) :
    (tolmanEhrenfestTemperature (Lapse.unit (d := sd)) T_infty).localValue x = T_infty := by
  rw [tolmanEhrenfestTemperature_localValue, Lapse.unit_N, div_one]

/-! ## §B — Dissipation-rate redshift and the `hbar * gamma` dictionary -/

/-- **Redshifted dissipation rate** reconstructed from a local rate field:

`gamma_infty(x) := N(x) * gamma_loc(x)`.

When `gamma_loc` is the local component of a `TolmanScaling`, this is pointwise equal to the asymptotic
rate by `tolmanScaling_redshiftedDissipationRate_eq_asymptotic`. -/
def redshiftedDissipationRate
    (L : Lapse sd) (gamma_loc : SpaceTime sd → ℝ) : SpaceTime sd → ℝ :=
  fun x => L.N x * gamma_loc x

/-- Positivity of the reconstructed infinity-frame dissipation rate. -/
theorem redshiftedDissipationRate_pos
    (L : Lapse sd) (gamma_loc : SpaceTime sd → ℝ)
    (hgamma : ∀ x, 0 < gamma_loc x) (x : SpaceTime sd) :
    0 < redshiftedDissipationRate L gamma_loc x :=
  mul_pos (L.N_pos x) (hgamma x)

/-- **Redshifted dissipation energy scale** `beta_tilde_infty = N * (hbar * gamma_loc)`. -/
def redshiftedDissipationEnergyScale
    (L : Lapse sd) (hbar : ℝ) (gamma_loc : SpaceTime sd → ℝ) : SpaceTime sd → ℝ :=
  fun x => L.N x * (hbar * gamma_loc x)

/-- The dimensional dictionary `beta_tilde = hbar * gamma` is preserved by the Tolman redshift. -/
theorem redshiftedDissipationEnergyScale_eq_hbar_mul_redshiftedDissipationRate
    (L : Lapse sd) (hbar : ℝ) (gamma_loc : SpaceTime sd → ℝ) (x : SpaceTime sd) :
    redshiftedDissipationEnergyScale L hbar gamma_loc x
      = hbar * redshiftedDissipationRate L gamma_loc x := by
  unfold redshiftedDissipationEnergyScale redshiftedDissipationRate
  ring

/-- If a local dissipation rate is a `TolmanScaling`, redshifting it reconstructs the asymptotic rate. -/
theorem tolmanScaling_redshiftedDissipationRate_eq_asymptotic
    (Gamma : TolmanScaling sd) (x : SpaceTime sd) :
    redshiftedDissipationRate Gamma.L Gamma.localValue x = Gamma.asymptotic := by
  simpa [redshiftedDissipationRate, mul_comm] using Gamma.law x

/-- The redshifted energy scale of a Tolman-scaled rate reconstructs `hbar * gamma_infty`. -/
theorem tolmanScaling_redshiftedDissipationEnergy_eq_hbar_mul_asymptotic
    (Gamma : TolmanScaling sd) (hbar : ℝ) (x : SpaceTime sd) :
    redshiftedDissipationEnergyScale Gamma.L hbar Gamma.localValue x
      = hbar * Gamma.asymptotic := by
  rw [redshiftedDissipationEnergyScale_eq_hbar_mul_redshiftedDissipationRate,
    tolmanScaling_redshiftedDissipationRate_eq_asymptotic]

/-! ## §C — KMS thermal rate under Tolman-Ehrenfest redshift -/

/-- Local Tolman-Ehrenfest temperature associated with a KMS scale. -/
def localKMSTolmanTemperature
    (K : KMSScale) (L : Lapse sd) (x : SpaceTime sd) : ℝ :=
  K.T / L.N x

/-- Local KMS thermal rate computed from the local Tolman-Ehrenfest temperature. -/
def localKMSTolmanThermalRate
    (K : KMSScale) (L : Lapse sd) (x : SpaceTime sd) : ℝ :=
  K.kB * localKMSTolmanTemperature K L x / K.ℏ

/-- The local KMS thermal rate satisfies the Tolman-Ehrenfest invariant:

`lambda_th,loc(x) * N(x) = lambda_th,infty`.

This connects the complex-action/entropic-time Tolman temperature redshift to Physlib's existing `ThermoFieldDynamics.KMS.KMSScale`. -/
theorem localKMSTolmanThermalRate_mul_lapse
    (K : KMSScale) (L : Lapse sd) (x : SpaceTime sd) :
    localKMSTolmanThermalRate K L x * L.N x = K.thermalRate := by
  unfold localKMSTolmanThermalRate localKMSTolmanTemperature KMSScale.thermalRate
  unfold Physlib.Optics.TemporalDoubleSlit.thermalEntropicRate
  have hN : L.N x ≠ 0 := (L.N_pos x).ne'
  have hhbar : K.ℏ ≠ 0 := K.ℏ_pos.ne'
  field_simp [hN, hhbar]

/-! ## §D — Horizon temperature redshift recovers the Unruh/surface-gravity rate -/

/-- Local Tolman-Ehrenfest temperature obtained by redshifting the Hawking temperature. -/
def localHawkingTolmanTemperature
    (L : Lapse sd) (hbar kappa c kB : ℝ) (x : SpaceTime sd) : ℝ :=
  hawkingTemperature hbar kappa c kB / L.N x

/-- Local thermal entropic rate built from the redshifted Hawking temperature. -/
def localHawkingTolmanThermalRate
    (L : Lapse sd) (hbar kappa c kB : ℝ) (x : SpaceTime sd) : ℝ :=
  kB * localHawkingTolmanTemperature L hbar kappa c kB x / hbar

/-- Redshifting the Hawking temperature and converting it to a local thermal rate recovers the
surface-gravity entropic rate after multiplying by the lapse. -/
theorem localHawkingTolmanThermalRate_mul_lapse_eq_surfaceGravityRate
    (L : Lapse sd) (hbar kappa c kB : ℝ)
    (hhbar : 0 < hbar) (hc : 0 < c) (hkB : 0 < kB) (x : SpaceTime sd) :
    localHawkingTolmanThermalRate L hbar kappa c kB x * L.N x
      = kappa / (2 * Real.pi * c) := by
  unfold localHawkingTolmanThermalRate localHawkingTolmanTemperature hawkingTemperature
  have hN : L.N x ≠ 0 := (L.N_pos x).ne'
  have hhbar_ne : hbar ≠ 0 := hhbar.ne'
  have hc_ne : c ≠ 0 := hc.ne'
  have hkB_ne : kB ≠ 0 := hkB.ne'
  have hden : 2 * Real.pi * c * kB ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hc_ne) hkB_ne
  field_simp [hN, hhbar_ne, hc_ne, hkB_ne, hden]

/-- structure-level form: the Tolman-redshifted local Hawking thermal rate reconstructs
`SurfaceGravityEntropicRate.lambdaSG`. -/
theorem localHawkingTolmanThermalRate_mul_lapse_eq_lambdaSG
    (L : Lapse sd) (M : SurfaceGravityEntropicRate) (hbar : ℝ) (hhbar : 0 < hbar)
    (x : SpaceTime sd) :
    localHawkingTolmanThermalRate L hbar M.κ M.c M.kB x * L.N x = M.lambdaSG := by
  rw [localHawkingTolmanThermalRate_mul_lapse_eq_surfaceGravityRate
    L hbar M.κ M.c M.kB hhbar M.c_pos M.kB_pos x]
  rfl

/-- Rindler/Unruh form: at `kappa = a`, the same Tolman-redshifted horizon rate reconstructs
`UnruhEntropicRate.lambdaU`. -/
theorem localHawkingTolmanThermalRate_mul_lapse_eq_lambdaU
    (L : Lapse sd) (U : UnruhEntropicRate) (hbar : ℝ) (hhbar : 0 < hbar)
    (x : SpaceTime sd) :
    localHawkingTolmanThermalRate L hbar U.a U.c U.kB x * L.N x = U.lambdaU := by
  rw [localHawkingTolmanThermalRate_mul_lapse_eq_surfaceGravityRate
    L hbar U.a U.c U.kB hhbar U.c_pos U.kB_pos x]
  rfl

end Physlib.SpaceTime

end
