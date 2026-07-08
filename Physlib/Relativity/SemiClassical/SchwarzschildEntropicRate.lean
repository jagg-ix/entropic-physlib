/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.SemiClassical.HawkingTemperature

/-!
# Schwarzschild Hawking temperature and entropic rate (Eqs 47, 48)

Port of the symbolic Mathematica derivations from
`entropic-time/verification/mathematica/modules/CAT_EPT_Extended_Part2.wl`,
equations (47) and (48):

* **Eq (47)**: `T_H = ℏ·c³/(8π·G·M·k_B)` — Schwarzschild Hawking
  temperature, derived from the surface gravity
  `κ_Schwarzschild = c⁴/(4·G·M)` via the generic
  `hawkingTemperature ℏ κ c k_B` formula (already in
  `Physlib/Relativity/SemiClassical/HawkingTemperature.lean`).
* **Eq (48)**: `λ_BH = c³/(8π·G·M)` — Schwarzschild entropic rate
  at the horizon, derived from `λ = k_B·T_H/ℏ` (fluctuation-
  dissipation / Connes-Rovelli relation).

The Mathematica verification (Wolfram) showed both as symbolic
identities; the Lean port makes them concrete `ℝ`-valued
definitions plus the bridge theorems.

## Why this is portable

Both Eqs 47 and 48 are pure algebra: given `hawkingTemperature` as
the generic structure, plugging in `κ_Schwarzschild = c⁴/(4GM)` gives
the specific `T_H` formula, and the FDT relation `λ = k_B·T/ℏ`
gives the corresponding entropic rate.  No new structures needed,
just specific definitions plus simplification theorems.

## Contents

* `schwarzschildSurfaceGravity G M c := c⁴ / (4·G·M)` — surface
  gravity at the Schwarzschild horizon.
* `schwarzschildHawkingTemperature ℏ G M c k_B` — Eq (47), defined
  via `hawkingTemperature ℏ κ c k_B`.
* `schwarzschildHawkingTemperature_eq` — explicit form
  `ℏ·c³/(8π·G·M·k_B)`.
* `schwarzschildEntropicRate G M c := c³/(8π·G·M)` — Eq (48).
* `schwarzschildEntropicRate_eq_kB_T_over_hbar` — FDT bridge
  `λ_BH = k_B·T_H/ℏ`.
* Positivity theorems.

## References

* Hawking 1975 — *Particle creation by black holes*, Commun. Math.
  Phys. 43, 199.
* Schwarzschild 1916 — original solution.
* Bekenstein 1973 — *Black holes and entropy*, Phys. Rev. D 7, 2333.
  formulation.
* `entropic-time/.../CAT_EPT_Extended_Part2.wl` — Wolfram symbolic
  derivation source for both equations.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.SemiClassical

/-! ## §1 — Schwarzschild surface gravity -/

/-- **Schwarzschild surface gravity** `κ = c⁴/(4·G·M)`.

The surface gravity at the event horizon of a Schwarzschild black
hole of mass `M`, gravitational constant `G`, speed of light `c`.
This is the input to the generic `hawkingTemperature` formula. -/
def schwarzschildSurfaceGravity (G M c : ℝ) : ℝ :=
  c^4 / (4 * G * M)

/-- The Schwarzschild surface gravity is positive at positive `G, M, c`. -/
theorem schwarzschildSurfaceGravity_pos
    {G M c : ℝ} (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) :
    0 < schwarzschildSurfaceGravity G M c := by
  unfold schwarzschildSurfaceGravity
  apply div_pos
  · positivity
  · positivity

/-! ## §2 — Eq (47): Schwarzschild Hawking temperature -/

/-- **Schwarzschild Hawking temperature** (Eq 47):
`T_H = ℏ·c³/(8π·G·M·k_B)`.

Defined as `hawkingTemperature ℏ κ_Schw c k_B` with
`κ_Schw := c⁴/(4·G·M)`; the explicit `c³/(8πGM·k_B)` form is the
content of `schwarzschildHawkingTemperature_eq` below.

This realises Hawking's 1975 result for a Schwarzschild black hole
as a specific instance of physlib's generic surface-gravity →
temperature map. -/
def schwarzschildHawkingTemperature (ℏ G M c kB : ℝ) : ℝ :=
  hawkingTemperature ℏ (schwarzschildSurfaceGravity G M c) c kB

/-- **Explicit form of `schwarzschildHawkingTemperature`** (Eq 47).

`T_H = ℏ·c³/(8π·G·M·k_B)`. -/
theorem schwarzschildHawkingTemperature_eq
    {ℏ G M c kB : ℝ} (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) (hkB : 0 < kB) :
    schwarzschildHawkingTemperature ℏ G M c kB =
      ℏ * c^3 / (8 * Real.pi * G * M * kB) := by
  unfold schwarzschildHawkingTemperature hawkingTemperature
    schwarzschildSurfaceGravity
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have h2pic_ne : (2 * Real.pi * c) ≠ 0 := by positivity
  field_simp
  ring

/-- The Schwarzschild Hawking temperature is positive at positive
inputs. -/
theorem schwarzschildHawkingTemperature_pos
    {ℏ G M c kB : ℝ} (hℏ : 0 < ℏ) (hG : 0 < G) (hM : 0 < M)
    (hc : 0 < c) (hkB : 0 < kB) :
    0 < schwarzschildHawkingTemperature ℏ G M c kB :=
  hawkingTemperature_pos ℏ (schwarzschildSurfaceGravity G M c) c kB
    hℏ (schwarzschildSurfaceGravity_pos hG hM hc) hc hkB

/-! ## §3 — Eq (48): Schwarzschild entropic rate -/

/-- **Schwarzschild entropic rate at the horizon** (Eq 48):
`λ_BH := c³/(8π·G·M)`.

Derived via the fluctuation-dissipation relation `λ = k_B·T_H/ℏ`
applied to the Schwarzschild Hawking temperature.  Same form as
the Unruh rate `λ_U = a/(2πc)` after substituting `κ_Schw` for `a`
(in fact `λ_BH = κ_Schw/(2πc²)`). -/
def schwarzschildEntropicRate (G M c : ℝ) : ℝ :=
  c^3 / (8 * Real.pi * G * M)

/-- **The Schwarzschild entropic rate equals `k_B·T_H/ℏ`** —
Eq (48) derivation. -/
theorem schwarzschildEntropicRate_eq_kB_T_over_hbar
    {ℏ G M c kB : ℝ} (hℏ : 0 < ℏ) (hG : 0 < G) (hM : 0 < M)
    (hc : 0 < c) (hkB : 0 < kB) :
    schwarzschildEntropicRate G M c =
      kB * schwarzschildHawkingTemperature ℏ G M c kB / ℏ := by
  rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
  unfold schwarzschildEntropicRate
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have h2π : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The Schwarzschild entropic rate is positive at positive inputs. -/
theorem schwarzschildEntropicRate_pos
    {G M c : ℝ} (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) :
    0 < schwarzschildEntropicRate G M c := by
  unfold schwarzschildEntropicRate
  apply div_pos
  · positivity
  · positivity

/-! ## §4 — Surface-gravity / entropic-rate consistency -/

/-- **The Schwarzschild entropic rate equals `κ_Schw/(2πc)`** —
exactly the Unruh-form `λ_U = a/(2πc)` with `a` replaced by the
Schwarzschild surface gravity (rescaled by `c`).

This puts Eq (48) into the same Unruh-like form
(`UnruhEntropicRate.lambdaU` in the surface-gravity structure).  All
"radiating horizons" follow the same `λ = κ/(2πc)` form once the
appropriate surface gravity is identified. -/
theorem schwarzschildEntropicRate_eq_surfaceGravity_form
    {G M c : ℝ} (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) :
    schwarzschildEntropicRate G M c =
      schwarzschildSurfaceGravity G M c / (2 * Real.pi * c) := by
  unfold schwarzschildEntropicRate schwarzschildSurfaceGravity
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Physlib.Relativity.SemiClassical

end
