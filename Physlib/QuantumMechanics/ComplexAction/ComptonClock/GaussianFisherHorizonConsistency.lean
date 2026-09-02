/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration
public import Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate
public import Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
meta import Zil

/-!
# Survival tests: the Planck calibration against the black-hole area equations and the
inverse-square law

The calibration theorems (`GaussianFisherPlanckCalibration`) claim `G = ħcσ₀⁴` is the
one-bit-per-Planck-area postulate with a unique width and no per-system freedom.  If that
were wrong, it would break against the two hardest fixed points of the gravitational
sector: black-hole horizon thermodynamics and the inverse-square law.  This module runs
both collisions inside the kernel.  All four survive — not approximately, but exactly:

* **The Bekenstein count** (`tiled_horizonCount_eq_bekenstein`): the Compton–Fisher tiling
  evaluated on the Schwarzschild horizon of its own coupling carries exactly
  `N = 16πGM²/(ħc)` — the Bekenstein bit count of a mass-`M` black hole, the same count
  the temperature-octagon weld `bitScreen_eq_schwarzschildHawking_iff` isolated as a
  rest-point condition.  Closed form: `N_hor = 16πσ₀⁴M²`.
* **The Hawking temperature emerges** (`tiledScreen_at_horizon_is_hawking`): the
  equipartition temperature of the tiled screen at the horizon *equals* the
  Schwarzschild–Hawking temperature `ħc³/(8πGMk_B)` at the constructed coupling — no
  temperature was inserted; Hawking's value is forced by the count.
* **The area law** (`tiled_count_eq_areaEntropy_natural`): in natural units the tiled
  count on any sphere is four times `bekensteinHawkingEntropy = A/4G` — i.e.
  `N = A/ℓ_P²`, the Bekenstein–Hawking area law read as a bit count.
* **The inverse-square law** (`tiledScreen_inverseSquare`): `F·R²` is
  radius-independent — the tiled response is exactly inverse-square at every radius, and
  `tiledBits_areaScaling` exhibits the count in the `σ·R²` form of certificate B
  (`areaScaling_inverseSquare`).  The library's own contrast certificate
  (`volumeScaling_not_inverseSquare`) shows a volume-scaling tiling would have *broken*
  the inverse-square law — so this survival is discriminating, not automatic.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency

/-- The Schwarzschild radius at the constructed coupling, in closed form:
`r_s = 2ħσ₀⁴M/c`. -/
lemma tiledHorizonRadius (σ₀ M c ħ : ℝ) (hc : c ≠ 0) :
    schwarzschildRadius M (ħ * c * σ₀ ^ 4) c = 2 * ħ * σ₀ ^ 4 * M / c := by
  unfold schwarzschildRadius
  field_simp

/-- **Survival I — the Bekenstein count.**  The Compton–Fisher tiling on the Schwarzschild
horizon of its own coupling is exactly the Bekenstein bit count
`16πGM²/(ħc)` at `G = ħcσ₀⁴`; in closed form, `16πσ₀⁴M²`. -/
theorem tiled_horizonCount_eq_bekenstein (σ₀ M c ħ : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonBitDensity σ₀ c ħ * sphereArea (schwarzschildRadius M (ħ * c * σ₀ ^ 4) c)
      = 16 * Real.pi * (ħ * c * σ₀ ^ 4) * M ^ 2 / (ħ * c) := by
  rw [tiledHorizonRadius σ₀ M c ħ hc]
  unfold comptonBitDensity sphereArea
  field_simp
  ring

/-- The Bekenstein count in closed form: `N_hor = 16πσ₀⁴M²`. -/
theorem tiled_horizonCount_closedForm (σ₀ M c ħ : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonBitDensity σ₀ c ħ * sphereArea (schwarzschildRadius M (ħ * c * σ₀ ^ 4) c)
      = 16 * Real.pi * σ₀ ^ 4 * M ^ 2 := by
  rw [tiled_horizonCount_eq_bekenstein σ₀ M c ħ hσ hc hħ]
  field_simp

/-- **Survival II — the Hawking temperature emerges.**  The equipartition temperature of
the Compton–Fisher-tiled screen at the horizon equals the Schwarzschild–Hawking
temperature at the constructed coupling.  No temperature was inserted anywhere: Hawking's
`ħc³/(8πGMk_B)` is forced by the count `16πσ₀⁴M²`. -/
theorem tiledScreen_at_horizon_is_hawking (σ₀ M c kB ħ : ℝ)
    (hσ : 0 < σ₀) (hM : 0 < M) (hc : 0 < c) (hkB : 0 < kB) (hħ : 0 < ħ) :
    bitScreenTemperature M c
        (comptonBitDensity σ₀ c ħ * sphereArea (schwarzschildRadius M (ħ * c * σ₀ ^ 4) c)) kB
      = schwarzschildHawkingTemperature ħ (ħ * c * σ₀ ^ 4) M c kB := by
  have hG : 0 < ħ * c * σ₀ ^ 4 :=
    mul_pos (mul_pos hħ hc) (pow_pos hσ 4)
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB,
    tiled_horizonCount_closedForm σ₀ M c ħ hσ.ne' hc.ne' hħ.ne']
  unfold bitScreenTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Survival III — the area law.**  In natural units (`ħ = c = 1`) the tiled count on
any sphere is four times the Bekenstein–Hawking entropy `A/4G` at the constructed
coupling: `N = A/ℓ_P²`, the area law read as a bit count. -/
theorem tiled_count_eq_areaEntropy_natural (σ₀ R : ℝ) (hσ : σ₀ ≠ 0) :
    comptonBitDensity σ₀ 1 1 * sphereArea R
      = 4 * bekensteinHawkingEntropy (sphereArea R) (1 * 1 * σ₀ ^ 4) := by
  unfold comptonBitDensity sphereArea bekensteinHawkingEntropy
  field_simp

/-- **Survival IV — the inverse-square law.**  `F·R²` is the same at every radius: the
tiled-screen response is exactly inverse-square.  (The library's certificate
`volumeScaling_not_inverseSquare` shows a volume-scaling tiling would have broken this, so
the survival is discriminating.) -/
theorem tiledScreen_inverseSquare (σ₀ M c kB m ħ Δx R₁ R₂ : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hm : m ≠ 0) (hM : M ≠ 0) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    verlindeEntropicForce
        (bitScreenTemperature M c (comptonBitDensity σ₀ c ħ * sphereArea R₁) kB)
        (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R₁ ^ 2
      = verlindeEntropicForce
        (bitScreenTemperature M c (comptonBitDensity σ₀ c ħ * sphereArea R₂) kB)
        (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R₂ ^ 2 := by
  rw [tiledScreen_gravitationalResponse σ₀ M c kB m ħ Δx R₁ hσ hc hħ hkB hΔx hm hM hR₁,
    tiledScreen_gravitationalResponse σ₀ M c kB m ħ Δx R₂ hσ hc hħ hkB hΔx hm hM hR₂]
  field_simp

/-- The tiled count in the `σ·R²` form of certificate B (`areaScaling_inverseSquare`):
area scaling with `σ = 4π · comptonBitDensity`. -/
lemma tiledBits_areaScaling (σ₀ c ħ R : ℝ) :
    comptonBitDensity σ₀ c ħ * sphereArea R
      = (4 * Real.pi * comptonBitDensity σ₀ c ħ) * R ^ 2 := by
  unfold sphereArea
  ring

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency

zil attach tiled_horizonCount_eq_bekenstein where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledHorizonRadius",
  formalizes @ "claim:the-compton-fisher-tiling-on-the-schwarzschild-horizon-of-its-own-\
coupling-carries-exactly-the-bekenstein-bit-count-sixteen-pi-g-m-squared-over-hbar-c",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledBits_eq_holographicBits"

zil attach tiledScreen_at_horizon_is_hawking where
  supported_by @ "lean:Physlib.Relativity.SemiClassical.schwarzschildHawkingTemperature_eq",
  formalizes @ "claim:the-equipartition-temperature-of-the-compton-fisher-tiled-screen-at-\
the-horizon-equals-the-schwarzschild-hawking-temperature-at-the-constructed-coupling-with-\
no-temperature-inserted",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiled_horizonCount_closedForm"

zil attach tiledScreen_inverseSquare where
  supported_by @ "lean:tiledScreen_gravitationalResponse",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.areaScaling_inverseSquare",
  formalizes @ "claim:the-tiled-screen-response-is-exactly-inverse-square-at-every-radius-\
while-the-librarys-volume-scaling-certificate-shows-this-was-falsifiable",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.volumeScaling_not_inverseSquare"

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency
