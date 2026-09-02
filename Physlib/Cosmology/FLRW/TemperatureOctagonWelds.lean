/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.HorizonEntropyExpansion
public import Physlib.Thermodynamics.NewtonGIsolation
public import Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate

/-!
# The temperature-octagon welds

The temperature hexagon (`Physlib.Meta.TemperaturePentagonGate`) extends by two carriers:
`bitScreenTemperature` (`2Mc²/(N·k_B)` — Verlinde's equipartition screen with a *free bit
count*, no `G`) and `schwarzschildHawkingTemperature` (`ℏc³/(8πGMk_B)` — Hawking's 1975
result, the surface-gravity map at the Schwarzschild horizon).  `#zil_groupoid_report` on the
octagon found all 28 edges dimensionally homogeneous with 16 proven, surfaced the five
bit-screen composites (every bit-screen edge beyond its proven Unruh flank,
`NewtonGIsolation.unruh_matches_screen`), and showed `schwarzschildHawkingTemperature`
fully isolated — its definitional relation to `hawkingTemperature` lived only in a proof
body, invisible to the environment pass.  The twelve welds below close every open edge.

Three name fundamental identifications:

* `bitScreen_eq_verlindeGravityTemperature_iff` — the two Verlinde temperatures agree
  exactly at `GℏN = 4πR²c³`, i.e. **`N = A·c³/(Gℏ)` with `A = 4πR²`: Verlinde's holographic
  bit-count postulate** is the rest-point of his own two temperature carriers, and the
  screen mass cancels.
* `bitScreen_eq_schwarzschildHawking_iff` — `16πGM² = Nℏc`, the **Bekenstein bit count**
  `N = A_horizon·c³/(Gℏ)` of a mass-`M` black hole: the same holographic count, read at the
  horizon.
* `compton_eq_schwarzschildHawking_iff` — `4GMm = ℏc`, the **Compton–Hawking mass duality**
  `M·m = m_P²/4`: the black hole whose Hawking temperature is a particle's Compton
  temperature sits at the Planck-mass geometric mean.
-/

@[expose] public section

namespace Cosmology.FLRW.TemperatureOctagonWelds

open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.Relativity.SemiClassical
open Cosmology.FLRW.HorizonEntropyExpansion

/-! ## §A — the bit-screen edges (the five predicted composites) -/

/-- **The bit screen at the Compton temperature: `mN = 4πM`** — the particle whose Compton
clock matches an `N`-bit screen of mass `M` carries the per-bit mass share times `4π`. -/
theorem bitScreen_eq_comptonTemperature_iff {M c N kB m : ℝ}
    (hc : 0 < c) (hkB : 0 < kB) (hN : 0 < N) :
    bitScreenTemperature M c N kB = Physlib.Thermodynamics.comptonTemperature m c kB
      ↔ m * N = 4 * Real.pi * M := by
  unfold bitScreenTemperature Physlib.Thermodynamics.comptonTemperature
    Physlib.Thermodynamics.deBroglieTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (c ^ 2 * kB : ℝ) ≠ 0 by positivity)
      (show m * N * (c ^ 2 * kB) = 4 * Real.pi * M * (c ^ 2 * kB) by linear_combination -h)
  · intro h
    linear_combination (-(c ^ 2 * kB)) * h

/-- **The bit screen at the de Broglie temperature: `EN = 4πMc²`** — equipartition read
against a general carrier energy: `N` bits at `T_dB(E)` hold the screen's rest energy
(times `4π` over the Boltzmann half). -/
theorem bitScreen_eq_deBroglieTemperature_iff {M c N kB E : ℝ}
    (hkB : 0 < kB) (hN : 0 < N) :
    bitScreenTemperature M c N kB = Physlib.Thermodynamics.deBroglieTemperature E kB
      ↔ E * N = 4 * Real.pi * M * c ^ 2 := by
  unfold bitScreenTemperature Physlib.Thermodynamics.deBroglieTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (kB : ℝ) ≠ 0 by positivity)
      (show E * N * kB = 4 * Real.pi * M * c ^ 2 * kB by linear_combination -h)
  · intro h
    linear_combination (-kB) * h

/-- **The bit screen at the Hawking temperature: `ℏκN = 4πMc³`** — the surface gravity whose
Hawking bath equilibrates an `N`-bit screen of mass `M`. -/
theorem bitScreen_eq_hawkingTemperature_iff {M c N kB ℏ κ : ℝ}
    (hkB : 0 < kB) (hN : 0 < N) (hc : 0 < c) :
    bitScreenTemperature M c N kB = hawkingTemperature ℏ κ c kB
      ↔ ℏ * κ * N = 4 * Real.pi * M * c ^ 3 := by
  unfold bitScreenTemperature hawkingTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (kB : ℝ) ≠ 0 by positivity)
      (show ℏ * κ * N * kB = 4 * Real.pi * M * c ^ 3 * kB by linear_combination -h)
  · intro h
    linear_combination (-kB) * h

/-- **The bit screen at the Gibbons–Hawking temperature: `ℏHN = 4πMc²`** — the Hubble rate
whose de Sitter bath equilibrates the screen. -/
theorem bitScreen_eq_gibbonsHawkingSI_iff {M c N kB ℏ H : ℝ}
    (hkB : 0 < kB) (hN : 0 < N) :
    bitScreenTemperature M c N kB = gibbonsHawkingTemperatureSI ℏ H kB
      ↔ ℏ * H * N = 4 * Real.pi * M * c ^ 2 := by
  rw [gibbonsHawkingTemperatureSI]
  exact (bitScreen_eq_deBroglieTemperature_iff hkB hN).trans
    (by constructor <;> intro h <;> linear_combination h)

/-- **The two Verlinde temperatures meet exactly at `GℏN = 4πR²c³`** — the screen mass
cancels, leaving **`N = A·c³/(Gℏ)` with `A = 4πR²`: Verlinde's holographic bit-count
postulate**, recovered as the rest-point of his equipartition screen against his entropic
gravity temperature. -/
theorem bitScreen_eq_verlindeGravityTemperature_iff {M c N kB G ℏ R : ℝ}
    (hM : 0 < M) (hkB : 0 < kB) (hN : 0 < N) (hc : 0 < c) (hR : 0 < R) :
    bitScreenTemperature M c N kB = verlindeGravityTemperature M G ℏ c R kB
      ↔ G * ℏ * N = 4 * Real.pi * R ^ 2 * c ^ 3 := by
  unfold bitScreenTemperature verlindeGravityTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (M * kB : ℝ) ≠ 0 by positivity)
      (show G * ℏ * N * (M * kB) = 4 * Real.pi * R ^ 2 * c ^ 3 * (M * kB) by
        linear_combination -h)
  · intro h
    linear_combination (-(M * kB)) * h

/-! ## §B — attaching the Schwarzschild–Hawking vertex -/

/-- **The Unruh weld of the Schwarzschild vertex: `4GMa = c⁴`** — the acceleration is the
Schwarzschild surface gravity `c⁴/(4GM)`; statement-level form of the definitional relation
that the environment pass could not see. -/
theorem unruh_eq_schwarzschildHawking_iff {ℏ kB c a G M : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    unruhTemperature ℏ kB c a = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 4 * G * M * a = c ^ 4 := by
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
  unfold unruhTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (2 * Real.pi * ℏ * kB : ℝ) ≠ 0 by positivity)
      (show 4 * G * M * a * (2 * Real.pi * ℏ * kB) = c ^ 4 * (2 * Real.pi * ℏ * kB) by
        linear_combination h)
  · intro h
    linear_combination (2 * Real.pi * ℏ * kB) * h

/-- **The generic Hawking carrier meets its Schwarzschild instance exactly at
`κ = c⁴/(4GM)`** (stated multiplicatively). -/
theorem hawking_eq_schwarzschildHawking_iff {ℏ kB c κ G M : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    hawkingTemperature ℏ κ c kB = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 4 * G * M * κ = c ^ 4 := by
  rw [← Physlib.Thermodynamics.unruhTemperature_eq_hawkingTemperature]
  exact unruh_eq_schwarzschildHawking_iff hℏ hkB hc hG hM

/-- **The Compton–Hawking mass duality: `4GMm = ℏc`**, i.e. `M·m = m_P²/4` — the black hole
whose Hawking temperature is a particle's Compton temperature sits at the Planck-mass
geometric mean of the two masses. -/
theorem compton_eq_schwarzschildHawking_iff {m c kB ℏ G M : ℝ}
    (hkB : 0 < kB) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    Physlib.Thermodynamics.comptonTemperature m c kB
        = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 4 * G * M * m = ℏ * c := by
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
  unfold Physlib.Thermodynamics.comptonTemperature Physlib.Thermodynamics.deBroglieTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (2 * Real.pi * c ^ 2 * kB : ℝ) ≠ 0 by positivity)
      (show 4 * G * M * m * (2 * Real.pi * c ^ 2 * kB)
          = ℏ * c * (2 * Real.pi * c ^ 2 * kB) by linear_combination h)
  · intro h
    linear_combination (2 * Real.pi * c ^ 2 * kB) * h

/-- **The de Broglie weld of the Schwarzschild vertex: `4GME = ℏc³`** — the carrier energy
is the Hawking energy scale of a mass-`M` hole. -/
theorem deBroglie_eq_schwarzschildHawking_iff {E kB ℏ G M c : ℝ}
    (hkB : 0 < kB) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    Physlib.Thermodynamics.deBroglieTemperature E kB
        = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 4 * G * M * E = ℏ * c ^ 3 := by
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
  unfold Physlib.Thermodynamics.deBroglieTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (2 * Real.pi * kB : ℝ) ≠ 0 by positivity)
      (show 4 * G * M * E * (2 * Real.pi * kB) = ℏ * c ^ 3 * (2 * Real.pi * kB) by
        linear_combination h)
  · intro h
    linear_combination (2 * Real.pi * kB) * h

/-- **The Gibbons–Hawking weld of the Schwarzschild vertex: `4GMH = c³`** — the Hubble rate
whose de Sitter temperature matches a mass-`M` hole, the Schwarzschild–de Sitter
temperature coincidence. -/
theorem gibbonsHawkingSI_eq_schwarzschildHawking_iff {ℏ H kB G M c : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    gibbonsHawkingTemperatureSI ℏ H kB = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 4 * G * M * H = c ^ 3 := by
  rw [gibbonsHawkingTemperatureSI]
  rw [deBroglie_eq_schwarzschildHawking_iff hkB hc hG hM]
  constructor
  · intro h
    exact mul_right_cancel₀ hℏ.ne'
      (show 4 * G * M * H * ℏ = c ^ 3 * ℏ by linear_combination h)
  · intro h
    linear_combination ℏ * h

/-- **The Verlinde screen meets the Schwarzschild vertex exactly at `4G²M² = c⁴R²`**, i.e.
`R = r_s = 2GM/c²` for positive data — the screen at the horizon, at the level of the two
temperature carriers with the shared mass. -/
theorem verlinde_eq_schwarzschildHawking_iff {G ℏ c R kB M : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) (hR : 0 < R) :
    verlindeGravityTemperature M G ℏ c R kB = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 4 * G ^ 2 * M ^ 2 = c ^ 4 * R ^ 2 := by
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
  unfold verlindeGravityTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (2 * Real.pi * ℏ * kB : ℝ) ≠ 0 by positivity)
      (show 4 * G ^ 2 * M ^ 2 * (2 * Real.pi * ℏ * kB)
          = c ^ 4 * R ^ 2 * (2 * Real.pi * ℏ * kB) by linear_combination h)
  · intro h
    linear_combination (2 * Real.pi * ℏ * kB) * h

/-- **The bit screen at the Schwarzschild–Hawking temperature: `16πGM² = Nℏc`** — the
**Bekenstein bit count** `N = A_horizon·c³/(Gℏ)` of a mass-`M` black hole, the same
holographic count as `bitScreen_eq_verlindeGravityTemperature_iff` read at `R = r_s`. -/
theorem bitScreen_eq_schwarzschildHawking_iff {M c N kB ℏ G : ℝ}
    (hkB : 0 < kB) (hN : 0 < N) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    bitScreenTemperature M c N kB = schwarzschildHawkingTemperature ℏ G M c kB
      ↔ 16 * Real.pi * G * M ^ 2 = N * ℏ * c := by
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
  unfold bitScreenTemperature
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (kB * c ^ 2 : ℝ) ≠ 0 by positivity)
      (show 16 * Real.pi * G * M ^ 2 * (kB * c ^ 2) = N * ℏ * c * (kB * c ^ 2) by
        linear_combination h)
  · intro h
    linear_combination (kB * c ^ 2) * h

end Cosmology.FLRW.TemperatureOctagonWelds
