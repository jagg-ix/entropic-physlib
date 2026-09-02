/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
public import Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
meta import Zil

/-!
# Reissner–Nordström horizon area and Bekenstein–Hawking entropy

The outer-horizon area of a Reissner–Nordström black hole is `𝒜 = 4π r_+²`, and its Bekenstein–Hawking
entropy is `S = 𝒜/4G = π r_+²/G`.  The repository carried the generic `bekensteinHawkingEntropy`
carrier but no charged-horizon area to feed it.

* `rnHorizonArea` — `𝒜 = 4π r_+²`.
* `rnHorizonArea_pos` — the area is positive for `M > 0`.
* `rnEntropy_eq` — `S = π r_+²/G`.
* `rnEntropy_extremal` — at extremality `M² = Q²` (so `r_+ = M`) the entropy is `π M²/G`.

Honest scope: this is the horizon-area/entropy algebra taking the Bekenstein–Hawking area law as given;
the microscopic state counting is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
open Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics

/-- **The Reissner–Nordström outer-horizon area** `𝒜 = 4π r_+²`. -/
def rnHorizonArea (M Q : ℝ) : ℝ := 4 * Real.pi * outerHorizon M Q ^ 2

/-- **The outer horizon is positive** `r_+ = M + √(M² − Q²) > 0` for `M > 0`. -/
theorem outerHorizon_pos (M Q : ℝ) (hM : 0 < M) : 0 < outerHorizon M Q := by
  unfold outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- **The horizon area is positive** for `M > 0`. -/
@[zil_level physical_theorem]
theorem rnHorizonArea_pos (M Q : ℝ) (hM : 0 < M) : 0 < rnHorizonArea M Q := by
  unfold rnHorizonArea
  have hr := outerHorizon_pos M Q hM
  positivity

/-- **The Bekenstein–Hawking entropy of the Reissner–Nordström horizon** `S = 𝒜/4G = π r_+²/G`. -/
@[zil_level physical_theorem]
theorem rnEntropy_eq (M Q G : ℝ) :
    bekensteinHawkingEntropy (rnHorizonArea M Q) G = Real.pi * outerHorizon M Q ^ 2 / G := by
  unfold bekensteinHawkingEntropy rnHorizonArea
  rw [show (4 : ℝ) * Real.pi * outerHorizon M Q ^ 2 = 4 * (Real.pi * outerHorizon M Q ^ 2) from by ring]
  exact mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)

/-- **The extremal Reissner–Nordström entropy** `S = π M²/G` (the extremal horizon sits at `r_+ = M`). -/
@[zil_level physical_theorem]
theorem rnEntropy_extremal (M Q G : ℝ) (h : M ^ 2 = Q ^ 2) :
    bekensteinHawkingEntropy (rnHorizonArea M Q) G = Real.pi * M ^ 2 / G := by
  rw [rnEntropy_eq, (extremal_horizons_eq M Q h).1]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea

zil attach rnHorizonArea_pos where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea.outerHorizon_pos",
  formalizes @ "claim:the-reissner-nordstrom-outer-horizon-area-four-pi-r-plus-squared-is-positive-for-positive-mass"

zil attach rnEntropy_eq where
  formalizes @ "claim:the-bekenstein-hawking-entropy-of-the-reissner-nordstrom-outer-horizon-is-the-area-over-four-g-equal-to-pi-r-plus-squared-over-g"

zil attach rnEntropy_extremal where
  supported_by @ "lean:extremal_horizons_eq",
  supported_by @ "lean:rnEntropy_eq",
  formalizes @ "claim:the-extremal-reissner-nordstrom-entropy-is-pi-m-squared-over-g-since-the-extremal-horizon-sits-at-r-plus-equals-m"

zil_file_contract physlib.reissnerNordstromEntropyArea where
  promises "The Reissner-Nordstrom horizon area and Bekenstein-Hawking entropy. The outer-horizon area is four pi times the outer horizon radius squared, which is positive for positive mass. The Bekenstein-Hawking entropy of the horizon is the area over four G, equal to pi times the outer horizon radius squared over G. At extremality M squared equals Q squared, where the extremal horizon sits at r plus equals M, the entropy is pi M squared over G. Reuses the generic Bekenstein-Hawking entropy carrier and the Reissner-Nordstrom horizons. Honest scope: this is the horizon-area and entropy algebra taking the Bekenstein-Hawking area law as given; the microscopic state counting is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.outerHorizon",
    "lean:Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics.bekensteinHawkingEntropy"
  ]
  forbids_substitutes [
    "reading the horizon-area and entropy algebra as a microscopic state counting deriving the Bekenstein-Hawking area law"
  ]
  witnessed_by [
    rnHorizonArea_pos,
    rnEntropy_eq,
    rnEntropy_extremal
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromEntropyArea
