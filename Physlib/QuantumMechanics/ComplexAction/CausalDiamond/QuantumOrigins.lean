/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixB
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalAcceleration
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium
public import Physlib.Relativity.SemiClassical.CausalDiamondThermodynamics

/-!
# The quantum-mechanical origin of the Jacobson–Visser causal diamond (consolidated)

Every face of the Jacobson–Visser causal-diamond physics is governed by the **metric common root**
`v = ξ/E = tanh(R_*/L) = R/L`, the Bogoliubov velocity of the mode `(ξ, Δ, E) = (sinh η, 1, cosh η)`
(dispersion `E² = ξ² + Δ²`), whose complexification is the Nagao–Nielsen complex momentum. This module
consolidates the QM-origin link layers:

* **§A1** the AdS dispersion ↔ Nagao–Nielsen complex `p, q` (`E ↔ L`, `ξ ↔ R = |p|`, `Δ ↔ √(L²−R²)`);
* **§B1** the geometric definitions (`meanCurvature`, `alphaDotZero`, `adsExtrinsicK`) as Bogoliubov
  momenta;
* **§C1** the thermodynamic definitions (area, volume, `k`, negative temperature) through `R = L v`;
* **§D1** the master synthesis bundling gravity, thermodynamics, information, dissipation, and the
  conformal flow at the single velocity `v = tanh η`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumOrigins

open Physlib.Relativity.SemiClassical
open Physlib.Relativity.SemiClassical.CausalDiamondThermodynamics
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixB
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalAcceleration
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot


/-! ## §A — the geometric ↔ Bogoliubov dictionary `E ↔ L`, `ξ ↔ R`, `Δ ↔ √(L²−R²)` -/

/-- **The diamond gap** `Δ = √(L²−R²)` forced by `E² = ξ² + Δ²` with `E = L`, `ξ = R`. -/
def diamondGap (L R : ℝ) : ℝ := Real.sqrt (L ^ 2 - R ^ 2)

/-- **`E = L`: the diamond radius is the Bogoliubov momentum with energy = curvature scale.**
`bogoliubovEnergy(R, √(L²−R²)) = √(R² + (L²−R²)) = √(L²) = L`. -/
theorem diamond_energy_eq_curvatureScale (L R : ℝ) (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) :
    bogoliubovEnergy R (diamondGap L R) = L := by
  rw [bogoliubovEnergy, diamondGap, Real.sq_sqrt (by linarith),
    show R ^ 2 + (L ^ 2 - R ^ 2) = L ^ 2 by ring, Real.sqrt_sq hL.le]

/-- **`Δ/E = √(1−(R/L)²) = sqrtFactor`** — the Bogoliubov mass ratio is the relativistic factor. -/
theorem diamondGap_over_energy_eq_sqrtFactor (L R : ℝ) (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) :
    diamondGap L R / L = sqrtFactor L R := by
  have h1 : 0 ≤ diamondGap L R / L := div_nonneg (Real.sqrt_nonneg _) hL.le
  have h2 : 0 ≤ sqrtFactor L R := Real.sqrt_nonneg _
  have hRL : (R / L) ^ 2 ≤ 1 := by rw [div_pow, div_le_one (by positivity)]; exact hR2
  have hsq : (diamondGap L R / L) ^ 2 = sqrtFactor L R ^ 2 := by
    rw [div_pow, diamondGap, Real.sq_sqrt (by linarith), sqrtFactor, Real.sq_sqrt (by linarith)]
    field_simp
  rw [← Real.sqrt_sq h1, hsq, Real.sqrt_sq h2]

/-- **`Δ = L · sqrtFactor`** (the gap as the curvature scale times the relativistic factor). -/
theorem diamondGap_eq_L_sqrtFactor (L R : ℝ) (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) :
    diamondGap L R = L * sqrtFactor L R := by
  rw [← diamondGap_over_energy_eq_sqrtFactor L R hL hR2]; field_simp

/-! ## §B — at the rapidity `R = L tanh(R_*/L)`: `Δ = L sech(R_*/L)` -/

/-- **`Δ = L sech(R_*/L)`** at the diamond rapidity `R = L tanh(R_*/L)` (Eq. 2.3): the gap is the
curvature scale times `sech`, reusing `sqrtFactor_diamond` (`√(1−(R/L)²) = 1/cosh(R_*/L)`). -/
theorem diamondGap_at_rapidity (L Rstar : ℝ) (hL : 0 < L) :
    diamondGap L (L * Real.tanh (Rstar / L)) = L / Real.cosh (Rstar / L) := by
  have ht : Real.tanh (Rstar / L) ^ 2 < 1 := by
    nlinarith [Real.abs_tanh_lt_one (Rstar / L), abs_nonneg (Real.tanh (Rstar / L)),
      sq_abs (Real.tanh (Rstar / L))]
  have hR2 : (L * Real.tanh (Rstar / L)) ^ 2 ≤ L ^ 2 := by nlinarith [sq_nonneg L]
  rw [diamondGap_eq_L_sqrtFactor L _ hL hR2, sqrtFactor_diamond L Rstar hL.ne', mul_one_div]

/-! ## §C — the complex dispersion (Nagao–Nielsen complex `p, q`) -/

/-- **The complex dispersion `bogoliubovDispersionℂ(R, Δ) = L²`** — over `ℂ`, the diamond's Bogoliubov
dispersion (momentum `ξ = R`, gap `Δ = √(L²−R²)`) is the curvature scale squared `L²`, the
`CausalDiamond.AdSComplexMomentum` dispersion at the geometric data. -/
theorem diamond_bogoliubovDispersion_eq_curvatureScale_sq (L R : ℝ) (hR2 : R ^ 2 ≤ L ^ 2) :
    bogoliubovDispersionℂ (R : ℂ) (diamondGap L R : ℂ) = (L : ℂ) ^ 2 := by
  rw [bogoliubovDispersionℂ, diamondGap]
  have hΔ : (Real.sqrt (L ^ 2 - R ^ 2) : ℂ) ^ 2 = ((L ^ 2 - R ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
  rw [hΔ]
  push_cast
  ring

/-- **The diamond velocity is the geometric ratio** `ξ/E = R/L` (with `E = L`). With `R = L tanh(R_*/L)`
this is `tanh(R_*/L)` — the metric common root. -/
theorem diamond_velocity_eq_ratio (L R : ℝ) (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) :
    R / bogoliubovEnergy R (diamondGap L R) = R / L := by
  rw [diamond_energy_eq_curvatureScale L R hL hR2]

/-- **Nagao–Nielsen complex `p, q`: the complexified gap converges iff `Im m > 0`.** Complexifying the
diamond gap `Δ` to the Nagao–Nielsen complex mass `m`, the momentum Gaussian — the complex-action /
Feynman–Kac weight `e^{−S_I/ℏ}` — has positive real part exactly when `Im m > 0`. -/
theorem diamond_complexGap_converges (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm

/-! ## §D — the `L → iL` continuation: gap ratio ↔ AdS conformal-Killing factor -/

/-- **`(Δ/E)² + (√(1+(R/L)²))² = 2`** — the dispersion gap ratio `Δ/E = sqrtFactor = √(1−(R/L)²)` and the
AdS diamond conformal-Killing factor `adsConfKillingFactor = √(1+(R/L)²)` (Eq. D.12) are `L → iL`
continuations of each other (`adS_dS_factor_continuation`). This ties the Bogoliubov dispersion to the
§D.2 AdS conformal-Killing vector. -/
theorem gap_ratio_adsFactor_continuation (L R : ℝ) (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) :
    (diamondGap L R / L) ^ 2 + adsConfKillingFactor L R ^ 2 = 2 := by
  rw [diamondGap_over_energy_eq_sqrtFactor L R hL hR2, add_comm]
  exact adS_dS_factor_continuation L R (by rw [div_pow, div_le_one (by positivity)]; exact hR2)

/-! ## §E — main result -/

/-- **The AdS diamond dispersion ↔ Nagao–Nielsen link, bundled.** For curvature scale `L > 0`, diamond
radius `R` (sub-luminal `R² ≤ L²`), complex mass `m ≠ 0`, and `ℏ, Δt > 0`:

* **(dictionary)** `bogoliubovEnergy(R, Δ) = L` — `R = |p|` is the momentum, `L = E` the energy;
* **(mass ratio)** `Δ/E = √(1−(R/L)²) = sqrtFactor`;
* **(complex dispersion)** `bogoliubovDispersionℂ(R, Δ) = L²` over `ℂ`;
* **(`L → iL`)** `(Δ/E)² + adsConfKillingFactor² = 2` (tie to the §D.2 AdS conformal-Killing vector);
* **(Nagao–Nielsen)** the complexified gap converges iff `Im m > 0`.

The §D.2 Anti-de Sitter conformal data, the complex Bogoliubov dispersion, and the Nagao–Nielsen complex
`p, q` meet at the diamond's metric common root `R/L = tanh(R_*/L)`. -/
theorem adS_dispersion_nn_link (L R : ℝ) (m : ℂ) {ℏ dt : ℝ}
    (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    bogoliubovEnergy R (diamondGap L R) = L
      ∧ diamondGap L R / L = sqrtFactor L R
      ∧ bogoliubovDispersionℂ (R : ℂ) (diamondGap L R : ℂ) = (L : ℂ) ^ 2
      ∧ (diamondGap L R / L) ^ 2 + adsConfKillingFactor L R ^ 2 = 2
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im) :=
  ⟨diamond_energy_eq_curvatureScale L R hL hR2,
   diamondGap_over_energy_eq_sqrtFactor L R hL hR2,
   diamond_bogoliubovDispersion_eq_curvatureScale_sq L R hR2,
   gap_ratio_adsFactor_continuation L R hL hR2,
   diamond_complexGap_converges m hℏ hdt hm⟩


/-! ## §A — the Bogoliubov dispersion and velocity (recap, for the linking theorems) -/

/-- **The Bogoliubov dispersion** `E = bogoliubovEnergy(ξ, 1) = cosh η` for `ξ = sinh η`. -/
theorem bogoliubov_dispersion (η : ℝ) : bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η :=
  diamond_horizon_energy η

/-- **The Bogoliubov velocity** `ξ/E = sinh η / cosh η = tanh η = v` — the metric common root. -/
theorem bogoliubov_velocity (η : ℝ) :
    Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = Real.tanh η :=
  diamond_metric_velocity η

/-! ## §B — `meanCurvature` is the ratio of Bogoliubov momenta -/

/-- **The mean curvature is the ratio of Bogoliubov momenta** `K = (1−d)/L · ξ(s)/ξ(R_*/L)`, with
`ξ(η) = sinh η` the Bogoliubov momentum (Appendix B, Eq. B.6). -/
theorem meanCurvature_eq_momentum_ratio (d L Rstar s : ℝ) :
    meanCurvature d L Rstar s = (1 - d) / L * (Real.sinh s / Real.sinh (Rstar / L)) := by
  rw [meanCurvature]; ring

/-- **The mean curvature's momenta include the Bogoliubov dispersion** `bogoliubovEnergy(sinh s, 1) =
cosh s` and velocity `tanh s` — the `sinh s` in `K` is the metric-common-root momentum. -/
theorem meanCurvature_momentum_dispersion (s : ℝ) :
    bogoliubovEnergy (Real.sinh s) 1 = Real.cosh s
      ∧ Real.sinh s / bogoliubovEnergy (Real.sinh s) 1 = Real.tanh s :=
  ⟨bogoliubov_dispersion s, bogoliubov_velocity s⟩

/-! ## §C — `alphaDotZero` is the inverse Bogoliubov momentum -/

/-- **The York-time rate is the inverse Bogoliubov momentum** `α̇|_{s=0} = −1/(L·ξ_*)`, with
`ξ_* = sinh(R_*/L)` the Bogoliubov momentum at the diamond rapidity (Eq. 2.11). -/
theorem alphaDotZero_eq_inv_momentum (L Rstar : ℝ) :
    alphaDotZero L Rstar = -(1 / (L * Real.sinh (Rstar / L))) := rfl

/-- **The York-time momentum includes the Bogoliubov dispersion** `bogoliubovEnergy(sinh(R_*/L), 1) =
cosh(R_*/L)`. -/
theorem alphaDotZero_momentum_dispersion (L Rstar : ℝ) :
    bogoliubovEnergy (Real.sinh (Rstar / L)) 1 = Real.cosh (Rstar / L) :=
  bogoliubov_dispersion (Rstar / L)

/-! ## §D — `adsExtrinsicK` is the Bogoliubov mass ratio over `R` -/

/-- **The AdS extrinsic curvature is the Bogoliubov mass ratio over `R`** `k = (d−2)·(Δ/E)/R =
(d−2)·sech(R_*/L)/R` (Eq. 2.12). At the diamond (`R = L tanh(R_*/L)`, `s = sqrtFactor = Δ/E`), the
relativistic factor `s` is the Bogoliubov mass ratio `Δ/E = 1/cosh(R_*/L)` (`sqrtFactor_diamond`). -/
theorem adsExtrinsicK_eq_massRatio (d L Rstar : ℝ) (hL : L ≠ 0) :
    adsExtrinsicK d (L * Real.tanh (Rstar / L)) (sqrtFactor L (L * Real.tanh (Rstar / L)))
      = (d - 2) * (1 / Real.cosh (Rstar / L)) / (L * Real.tanh (Rstar / L)) := by
  rw [adsExtrinsicK, sqrtFactor_diamond L Rstar hL]

/-! ## §E — main result -/

/-- **The diamond's geometric definitions include the Bogoliubov / metric-common-root structure.** The
mean curvature is a ratio of Bogoliubov momenta `ξ(η) = sinh η` (dispersion `bogoliubovEnergy(ξ, 1) =
cosh η`, velocity `tanh η`); the York-time rate is `−1/(L·ξ_*)`; the AdS extrinsic curvature is the
Bogoliubov mass ratio `Δ/E = sech(R_*/L)` over `R`. Every geometric quantity is governed by the
quantum-mechanical origin `v = ξ/E = tanh(R_*/L)`. -/
theorem diamond_geometry_bogoliubov_origin (d L Rstar s : ℝ) (hL : L ≠ 0) :
    meanCurvature d L Rstar s = (1 - d) / L * (Real.sinh s / Real.sinh (Rstar / L))
      ∧ bogoliubovEnergy (Real.sinh s) 1 = Real.cosh s
      ∧ alphaDotZero L Rstar = -(1 / (L * Real.sinh (Rstar / L)))
      ∧ adsExtrinsicK d (L * Real.tanh (Rstar / L)) (sqrtFactor L (L * Real.tanh (Rstar / L)))
          = (d - 2) * (1 / Real.cosh (Rstar / L)) / (L * Real.tanh (Rstar / L)) :=
  ⟨meanCurvature_eq_momentum_ratio d L Rstar s, bogoliubov_dispersion s,
   alphaDotZero_eq_inv_momentum L Rstar, adsExtrinsicK_eq_massRatio d L Rstar hL⟩


/-! ## §A — the central link: the diamond radius is the curvature scale times the velocity -/

/-- **The diamond radius is the curvature scale times the Bogoliubov velocity** `R = L · v = L · tanh(R_*/L)
= L · (ξ/E)`. This single identity makes every thermodynamic quantity a function of the metric common
root `v`. -/
theorem diamond_radius_eq_velocity_scale (L Rstar : ℝ) :
    L * Real.tanh (Rstar / L)
      = L * (Real.sinh (Rstar / L) / bogoliubovEnergy (Real.sinh (Rstar / L)) 1) := by
  rw [diamond_metric_velocity]

/-! ## §B — area, volume, extrinsic curvature as functions of `R = L v` -/

/-- **The extrinsic curvature is inverse in the velocity scale** `k = (d−2)/(L v)` at the diamond
`R = L tanh(R_*/L)`. -/
theorem extrinsicK_eq_velocity (d L Rstar : ℝ) :
    extrinsicK d (L * Real.tanh (Rstar / L)) = (d - 2) / (L * Real.tanh (Rstar / L)) := rfl

/-- **The area is `Ω(Lv)^{d−2}`** at the diamond `R = L tanh(R_*/L)`. -/
theorem diamondArea_eq_velocity (Ω d L Rstar : ℝ) :
    diamondArea Ω d (L * Real.tanh (Rstar / L)) = Ω * (L * Real.tanh (Rstar / L)) ^ (d - 2) := rfl

/-- **The volume is `Ω(Lv)^{d−1}/(d−1)`** at the diamond `R = L tanh(R_*/L)`. -/
theorem diamondVolume_eq_velocity (Ω d L Rstar : ℝ) :
    diamondVolume Ω d (L * Real.tanh (Rstar / L))
      = Ω * (L * Real.tanh (Rstar / L)) ^ (d - 1) / (d - 1) := rfl

/-! ## §C — the negative temperature and the luminal/reversible limit -/

/-- **The diamond temperature is minus the Unruh temperature** `T = −T_H = −unruhTemperature` (at
`a = κ`, the inverted acceleration temperature). -/
theorem diamondTemperature_eq_neg_unruh (ℏ κ c kB : ℝ) :
    diamondTemperature ℏ κ c kB = -unruhTemperature ℏ κ c kB := by
  rw [diamondTemperature, unruhTemperature]

/-- **The diamond temperature is negative** for `κ > 0` — the inverted-temperature regime (vs the
positive Hawking/Unruh temperature). -/
theorem diamondTemperature_negative (ℏ κ c kB : ℝ) (hℏ : 0 < ℏ) (hκ : 0 < κ) (hc : 0 < c)
    (hkB : 0 < kB) : diamondTemperature ℏ κ c kB < 0 :=
  diamondTemperature_neg ℏ κ c kB hℏ hκ hc hkB

/-- **The entropic proper time vanishes at the luminal/reversible limit** `τ_ent = 0 ⟺ v = ±1` — the
static-patch limit `R/L = ±1` where the diamond degenerates. The reversible point of the thermal
structure is the metric-luminal velocity. -/
theorem diamond_reversible_at_luminal (η : ℝ) :
    bogoliubovEntropicTime (Real.sinh η) 1 = 0 ↔ Real.tanh η = 1 ∨ Real.tanh η = -1 :=
  CausalDiamond.MetricCommonRoot.diamond_entropicTime_zero_iff_luminal η

/-! ## §D — main result -/

/-- **The diamond's thermodynamic definitions include the metric-common-root / Bogoliubov structure.** The
radius is `R = L v` (`v = ξ/E = tanh(R_*/L)`), so the extrinsic curvature is `(d−2)/(L v)`, the area
`Ω(Lv)^{d−2}`, and the volume `Ω(Lv)^{d−1}/(d−1)`; the temperature is the negative (inverted) Unruh
temperature, `< 0` for `κ > 0`; the reversible point is the metric-luminal limit `v = ±1`. -/
theorem diamond_thermo_bogoliubov_origin (Ω d L Rstar ℏ κ c kB : ℝ)
    (hℏ : 0 < ℏ) (hκ : 0 < κ) (hc : 0 < c) (hkB : 0 < kB) :
    L * Real.tanh (Rstar / L)
        = L * (Real.sinh (Rstar / L) / bogoliubovEnergy (Real.sinh (Rstar / L)) 1)
      ∧ extrinsicK d (L * Real.tanh (Rstar / L)) = (d - 2) / (L * Real.tanh (Rstar / L))
      ∧ diamondArea Ω d (L * Real.tanh (Rstar / L)) = Ω * (L * Real.tanh (Rstar / L)) ^ (d - 2)
      ∧ diamondTemperature ℏ κ c kB = -unruhTemperature ℏ κ c kB
      ∧ diamondTemperature ℏ κ c kB < 0 :=
  ⟨diamond_radius_eq_velocity_scale L Rstar, extrinsicK_eq_velocity d L Rstar,
   diamondArea_eq_velocity Ω d L Rstar, diamondTemperature_eq_neg_unruh ℏ κ c kB,
   diamondTemperature_negative ℏ κ c kB hℏ hκ hc hkB⟩


/-! ## §1 — the central identity: the metric common root is the Bogoliubov velocity -/

/-- **The metric common root is the Bogoliubov velocity** `v = ξ/E = sinh η / bogoliubovEnergy(sinh η, 1)
= tanh η`. This single velocity — the quantum-mechanical origin — governs every face of the causal
diamond below. -/
theorem metric_common_root (η : ℝ) :
    Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = Real.tanh η :=
  diamond_metric_velocity η

/-! ## §2 — the master synthesis at the rapidity `η` -/

/-- **The quantum-mechanical origin of the Jacobson–Visser causal diamond.** For the diamond rapidity
`η = R_*/L` (velocity `v = tanh η`), complex mass `m ≠ 0`, thermal data `ℏ, κ, c, k_B`, conformal-Killing
scale `R ≠ 0`, and `ℏ, Δt > 0`, the following hold *simultaneously*, all governed by the Bogoliubov mode
`(ξ, Δ, E) = (sinh η, 1, cosh η)`:

* **(QM origin)** `bogoliubovEnergy(sinh η, 1) = cosh η` — the dispersion `E² = ξ² + Δ²`;
* **(gravity §4 / Appendix F)** `γ²(1 − v²) = 1` (`γ = cosh η`) and `unruhT = hawkingT` (equivalence
  principle at `a = κ`);
* **(information)** `τ_ent = binEntropy((1 − v)/2)`;
* **(dissipation, Nagao–Nielsen)** the complex-action weight converges iff `Im m > 0`;
* **(Appendix F)** the redshifted proper acceleration `C·a = tanh η = v`.

Gravity, thermodynamics, information, dissipation, and the conformal flow are one — at the metric common
root, the Bogoliubov velocity, the quantum-mechanical origin. -/
theorem jacobson_diamond_quantum_origin (η : ℝ) (m : ℂ) (ℏ κ c kB R : ℝ) {dt : ℝ}
    (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) (hR : R ≠ 0) :
    bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η
      ∧ lorentzFactor η ^ 2 * (1 - Real.tanh η ^ 2) = 1
      ∧ unruhTemperature ℏ κ c kB = hawkingTemperature ℏ κ c kB
      ∧ bogoliubovEntropicTime (Real.sinh η) 1 = Real.binEntropy ((1 - Real.tanh η) / 2)
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im)
      ∧ redshiftFactor R η * properAcceleration R η = Real.tanh η :=
  ⟨diamond_horizon_energy η,
   diamond_lorentzFactor_velocity η,
   diamond_equivalence_principle ℏ κ c kB,
   diamond_entropicTime_eq_velocity η,
   diamond_complexAction_converges m hℏ hdt hm,
   redshifted_acceleration_eq_tanh R η hR⟩

/-- **Appendix F: the proper acceleration is the Bogoliubov momentum.** `R · a(η) = sinh η = ξ`, with
`bogoliubovEnergy(R·a, 1) = cosh η = E` — the gravitational acceleration of the conformal Killing flow is
the Bogoliubov momentum of the same mode (`CausalDiamond.ConformalAcceleration`). -/
theorem acceleration_is_bogoliubov_momentum (R η : ℝ) (hR : R ≠ 0) :
    bogoliubovEnergy (properAcceleration R η * R) 1 = Real.cosh η :=
  properAcceleration_is_bogoliubovMomentum R η hR

/-! ## §3 — the AdS (Appendix D.2) and zeroth-law faces, through their bridges -/

/-- **The Anti-de Sitter face (Appendix D.2).** The diamond radius `R` is the Bogoliubov momentum, the
curvature scale `L` the energy, with the complex dispersion `bogoliubovDispersionℂ(R, Δ) = L²` and the
Nagao–Nielsen convergence `Im m > 0` (`adS_dispersion_nn_link`). -/
theorem adS_face (L R : ℝ) (m : ℂ) {ℏ dt : ℝ}
    (hL : 0 < L) (hR2 : R ^ 2 ≤ L ^ 2) (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    bogoliubovEnergy R (diamondGap L R) = L
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im) :=
  ⟨diamond_energy_eq_curvatureScale L R hL hR2,
   diamond_complexGap_converges m hℏ hdt hm⟩

/-- **The zeroth-law face.** A constant surface gravity `κ = κ'` gives uniform QIF entropic rate, Hawking
and Unruh temperature — the accelerated thermal equilibrium
(`CausalDiamond.QIFEquilibrium.qif_zerothLaw_equilibrium`). -/
theorem zerothLaw_face (ℏ κ κ' c kB : ℝ) (h : κ = κ') :
    CausalDiamond.QIFEquilibrium.qifEntropicRate κ c = CausalDiamond.QIFEquilibrium.qifEntropicRate κ' c
      ∧ hawkingTemperature ℏ κ c kB = hawkingTemperature ℏ κ' c kB
      ∧ unruhTemperature ℏ κ c kB = unruhTemperature ℏ κ' c kB :=
  CausalDiamond.QIFEquilibrium.qif_zerothLaw_equilibrium ℏ κ κ' c kB h


end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumOrigins

end
