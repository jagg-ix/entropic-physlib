/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.VerlindeEntropicForce
meta import Zil

/-!
# The Unruh detection threshold is the Compton–Unruh weld

Toussaint (arXiv:2512.17959) proves that exciting a massive field from the Unruh bath is
suppressed as `exp(−const·Mc²/(ħa/c))`, and that the fundamental condition for a
non-suppressed effect is `ħa/c ≳ Mc²` — for an electron-mass field the required
acceleration is `∼10²⁹ m/s²`, and at achievable accelerations the suppression exceeds
`10⁹` orders of magnitude.  This module identifies that experimental threshold with a
structure the library already carries:

* **the suppression scale is the temperature ratio**
  (`suppressionScale_eq_temperatureRatio`): `Mc³/(ħa) = T_Compton/T_Unruh` exactly — the
  `2π`s and `k_B`s cancel; the paper's universal exponent is the ratio of two carriers of
  the temperature octagon;
* **the detection threshold is the weld** (`detectionThreshold_iff_temperatures_weld`):
  the non-suppression boundary `a = Mc³/ħ` is precisely the rest point
  `unruh_eq_comptonTemperature_iff` at which the Unruh and Compton temperature carriers
  coincide — the groupoid weld the temperature gate certifies is, physically, the
  observability threshold of the Unruh effect for a massive field;
* **suppressed means below the weld** (`suppressed_iff_below_weld`): the exponentially
  suppressed regime `Mc³/(ħa) > 1` is exactly `T_Unruh < T_Compton`;
* **the weight is a Boltzmann nat count**
  (`suppressionWeight_eq_exp_neg_temperatureRatio`): the suppression factor is
  `exp(−T_C/T_U)` — an `E/k_BT`-shaped exponent, information-dimensional under the
  Brillouin price like every Boltzmann weight in `Physlib.Meta.PathIntegralBitGate`.

**Why this matters for the derived Verlinde ansatz.**  The displacement-entropy
derivation (`DisplacementEntropyFromUnruhInertia`) exchanges the ansatz for Unruh
thermality plus inertia.  This module records the empirical status of that thermality
premise: for *real* masses at achievable accelerations the system sits far below the
weld, so the massive-field Unruh response is unobservable in principle by direct
excitation; the falsifiable route is the paper's engineered-low-mass analog
(`ħa/c ≫ M_eff c²`, superconducting qubit, linear response `P ≈ S·δω`).  The premise is
KMS-grounded and analog-testable, not laboratory-verified for real masses — and the
threshold separating those regimes is a theorem of the temperature groupoid.
-/

set_option autoImplicit false

open Physlib.Thermodynamics

@[expose] public section

namespace Physlib.Thermodynamics.UnruhDetectionThreshold

/-- **The universal suppression scale is the Compton/Unruh temperature ratio**:
`Mc³/(ħa) = T_C/T_U` exactly — `2π` and `k_B` cancel. -/
theorem suppressionScale_eq_temperatureRatio (m c ħ kB a : ℝ)
    (hc : 0 < c) (hħ : 0 < ħ) (hkB : 0 < kB) (ha : a ≠ 0) :
    m * c ^ 3 / (ħ * a)
      = comptonTemperature m c kB / unruhTemperature ħ kB c a := by
  unfold comptonTemperature deBroglieTemperature unruhTemperature
  rw [div_div_div_eq]
  field_simp

/-- **The detection threshold is the weld**: the non-suppression boundary `a = Mc³/ħ` is
exactly the rest point at which the Unruh temperature meets the Compton temperature —
the temperature-octagon weld read as an observability condition. -/
theorem detectionThreshold_iff_temperatures_weld (m c ħ kB a : ℝ)
    (hħ : 0 < ħ) (hkB : 0 < kB) (hc : 0 < c) :
    a = m * c ^ 3 / ħ
      ↔ unruhTemperature ħ kB c a = comptonTemperature m c kB :=
  (unruh_eq_comptonTemperature_iff hħ hkB hc).symm

/-- **Suppressed means below the weld**: the exponentially suppressed regime
`Mc³/(ħa) > 1` is exactly `T_Unruh < T_Compton`. -/
theorem suppressed_iff_below_weld (m c ħ kB a : ℝ)
    (hc : 0 < c) (hħ : 0 < ħ) (hkB : 0 < kB) (ha : 0 < a) :
    1 < m * c ^ 3 / (ħ * a)
      ↔ unruhTemperature ħ kB c a < comptonTemperature m c kB := by
  rw [suppressionScale_eq_temperatureRatio m c ħ kB a hc hħ hkB ha.ne']
  have hTU : 0 < unruhTemperature ħ kB c a := by
    unfold unruhTemperature
    positivity
  rw [lt_div_iff₀ hTU, one_mul]

/-- **The suppression weight is a Boltzmann factor in the temperature ratio**:
`exp(−Mc³/(ħa)) = exp(−T_C/T_U)`. -/
theorem suppressionWeight_eq_exp_neg_temperatureRatio (m c ħ kB a : ℝ)
    (hc : 0 < c) (hħ : 0 < ħ) (hkB : 0 < kB) (ha : a ≠ 0) :
    Real.exp (-(m * c ^ 3 / (ħ * a)))
      = Real.exp (-(comptonTemperature m c kB / unruhTemperature ħ kB c a)) := by
  rw [suppressionScale_eq_temperatureRatio m c ħ kB a hc hħ hkB ha]

end Physlib.Thermodynamics.UnruhDetectionThreshold

namespace Physlib.Thermodynamics.UnruhDetectionThreshold

zil attach suppressionScale_eq_temperatureRatio where
  formalizes @ "claim:the-universal-mass-suppression-scale-of-unruh-detection-m-c-cubed-\
over-hbar-a-is-exactly-the-compton-over-unruh-temperature-ratio-two-pi-and-kb-cancel",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:toussaint-2025-detecting-the-unruh-effect-via-an-engineered-low-mass-field-in-a-superconducting-qubit-arxiv-2512-17959",
  supported_by @ "lean:Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff"

zil attach detectionThreshold_iff_temperatures_weld where
  formalizes @ "claim:the-fundamental-condition-for-a-non-suppressed-unruh-effect-on-a-\
massive-field-is-exactly-the-compton-unruh-temperature-weld-of-the-temperature-octagon-\
the-groupoid-rest-point-is-the-observability-threshold",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:toussaint-2025-detecting-the-unruh-effect-via-an-engineered-low-mass-field-in-a-superconducting-qubit-arxiv-2512-17959",
  supported_by @ "lean:Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff"

end Physlib.Thermodynamics.UnruhDetectionThreshold
