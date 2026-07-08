/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods

/-!
# The Araki–Woods modular parameter of the Kay–Wald quasifree state is the Hawking Boltzmann factor

Bridges the Kay–Wald thermal arc to the repository's **Araki–Woods** one-particle / GNS structure of a quasifree
state (`AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods`). The Araki–Woods construction assigns a quasifree state a
density parameter `ρ = (2A)⁻¹` and a modular (factor) parameter `γ = ρ/(1+ρ) = (1+2A)⁻¹`. For the Kay–Wald horizon
state these are *exactly* the thermal data: with the one-particle contraction fixed by the Hawking temperature
(`A = (e^{βω} − 1)/2`),

`ρ = 1/(e^{βω} − 1) = n` (the Bose occupation), `γ = 1/e^{βω} = e^{−βω}` (the Boltzmann factor),

so the Araki–Woods density is the Bose–Einstein occupation and the Araki–Woods modular parameter is the Hawking
Boltzmann factor `e^{−βω} = n/(n+1)`. This is the AQFT reason the quasifree horizon state is a KMS/thermal state:
its GNS modular parameter *is* the detailed-balance ratio.

* the **Araki–Woods density is the Bose occupation** `ρ = n` (`arakiWoods_rho_is_hawkingOccupation`);
* the **Araki–Woods modular parameter is the Boltzmann factor** `γ = e^{−βω}`
 (`arakiWoods_gamma_is_boltzmann`) — the modular parameter of the quasifree GNS factor is the Hawking Boltzmann
 weight;
* the **modular parameter is the occupation ratio** `γ = n/(1+n)` (`arakiWoods_gamma_eq_occupation_ratio`) — reusing
 the Araki–Woods map `γ = ρ/(1+ρ)` (`arakiWoodsGamma_eq_rho`) with `ρ = n`, so `γ = n/(1+n) = e^{−βω}` is the KMS
 detailed-balance ratio;
* the **Hawking specialization** `β = 2π/κ` (`hawking_arakiWoods_gamma`).

So the Kay–Wald quasifree state's Araki–Woods GNS factor records modular parameter `γ = e^{−βω}` and density `ρ = n`:
the one-particle / modular structure of the horizon state is the thermal occupation, and its modular parameter is
the Boltzmann factor — the Tomita–Takesaki / Araki–Woods root of the Hawking KMS property.

* **§A — the thermal Araki–Woods parameters** (`arakiWoods_rho_is_hawkingOccupation`,
 `arakiWoods_gamma_is_boltzmann`).
* **§B — the modular parameter is the occupation ratio** (`arakiWoods_gamma_eq_occupation_ratio`).
* **§C — the Hawking specialization `β = 2π/κ`** (`hawking_arakiWoods_gamma`).

The identifications of the Araki–Woods density and modular parameters with the Bose
occupation and the Boltzmann factor are exact algebra, reusing `arakiWoodsRho`, `arakiWoodsGamma`, and the
Araki–Woods map `arakiWoodsGamma_eq_rho`. The full Araki–Woods construction (the one-particle Hilbert space, the
GNS triple, the modular operator) lives in the referenced modules and is not re-derived. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; H. Araki, E.J. Woods; W. Labuschagne, W.A. Majewski §7.1. Repo
 structures: `AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods` (`arakiWoodsRho`, `arakiWoodsGamma`),
 `EntropicTime.KayWaldHawkingRadiationBoseEinstein` (`hawkingOccupation`, `hawking_detailed_balance`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldArakiWoodsThermalParameter

/-! ## §A — the thermal Araki–Woods parameters -/

/-- **The thermal one-particle contraction parameter** `A = (e^{βω} − 1)/2` — the value of the Araki–Woods
contraction `A` for which the quasifree state is the Hawking–KMS state at inverse temperature `β`. -/
noncomputable def thermalContraction (β ω : ℝ) : ℝ := (Real.exp (β * ω) - 1) / 2

/-- **[The Araki–Woods density is the Bose occupation] `ρ = n`.** At the thermal contraction the Araki–Woods
density parameter `ρ = (2A)⁻¹` is exactly the Bose–Einstein occupation `n = 1/(e^{βω}−1)`. -/
theorem arakiWoods_rho_is_hawkingOccupation (β ω : ℝ) :
    arakiWoodsRho (thermalContraction β ω) = hawkingOccupation β ω := by
  unfold arakiWoodsRho thermalContraction hawkingOccupation
  rw [show 2 * ((Real.exp (β * ω) - 1) / 2) = Real.exp (β * ω) - 1 from by ring]

/-- **[The Araki–Woods modular parameter is the Boltzmann factor] `γ = e^{−βω}`.** At the thermal contraction the
Araki–Woods factor parameter `γ = (1+2A)⁻¹` is exactly the Hawking Boltzmann factor `e^{−βω}`: the modular
parameter of the quasifree GNS factor is the thermal weight. -/
theorem arakiWoods_gamma_is_boltzmann (β ω : ℝ) :
    arakiWoodsGamma (thermalContraction β ω) = Real.exp (-(β * ω)) := by
  unfold arakiWoodsGamma thermalContraction
  rw [show (1 : ℝ) + 2 * ((Real.exp (β * ω) - 1) / 2) = Real.exp (β * ω) from by ring,
    Real.exp_neg, one_div]

/-! ## §B — the modular parameter is the occupation ratio -/

/-- **[The Araki–Woods modular parameter is the occupation ratio] `γ = n/(1+n)`.** Reusing the Araki–Woods map
`γ = ρ/(1+ρ)` (`arakiWoodsGamma_eq_rho`) with `ρ = n`: the modular parameter is the KMS detailed-balance ratio
`n/(1+n) = e^{−βω}` of the Hawking state. -/
theorem arakiWoods_gamma_eq_occupation_ratio (β ω : ℝ) (hβω : 0 < β * ω) :
    arakiWoodsGamma (thermalContraction β ω)
      = hawkingOccupation β ω / (1 + hawkingOccupation β ω) := by
  have hA : 0 < thermalContraction β ω := by
    have h1 : 1 < Real.exp (β * ω) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hβω
    unfold thermalContraction; linarith
  rw [arakiWoodsGamma_eq_rho _ hA, arakiWoods_rho_is_hawkingOccupation]

/-! ## §C — the Hawking specialization `β = 2π/κ` -/

/-- **[The Araki–Woods modular parameter at the Hawking temperature] `γ = e^{−(2π/κ)ω}`.** Specializing to the
Hawking inverse temperature `β = hawkingBeta 1 κ 1 1 = 2π/κ`: the Araki–Woods GNS factor of the
bifurcate-Killing-horizon quasifree state has modular parameter the Hawking Boltzmann factor. -/
theorem hawking_arakiWoods_gamma (κ ω : ℝ) :
    arakiWoodsGamma (thermalContraction (hawkingBeta 1 κ 1 1) ω)
      = Real.exp (-(hawkingBeta 1 κ 1 1 * ω)) :=
  arakiWoods_gamma_is_boltzmann (hawkingBeta 1 κ 1 1) ω

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldArakiWoodsThermalParameter

end
