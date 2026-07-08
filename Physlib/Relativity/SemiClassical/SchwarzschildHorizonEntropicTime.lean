/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Schwarzschild horizon entropic time: three equivalent forms

Algebraic identities relating three formulations of the
**entropic-time differential at a Schwarzschild horizon**:

* **Bekenstein** (1973): `dτ_hor = dA / (4·ℓ_P²)`,
* **Schwarzschild mass**: `dτ_hor = 8π·G·M·dM / (ℏ·c)`,
* **Jacobson** (1995): `dτ_hor = dE / (k_B·T_H)`,

with the Schwarzschild area `A = 16π·G²·M²/c⁴`, Planck length
`ℓ_P² = ℏ·G/c³`, energy `dE = c²·dM`, and Hawking temperature
`T_H = ℏ·c³ / (8π·G·M·k_B)` (already in
`Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate`).

All three forms compute the **same scalar** along the horizon
worldline. This file proves the three-form equivalence at the
algebraic level, with `dA/dM = 32π·G²·M/c⁴` derived from the
area definition via Mathlib's `deriv`.

## Scope

This file contains **only what can be derived** from existing
physlib content plus standard real-analysis calculus. The full
GR collapse dynamics (Misner–Sharp 1964 ideal-fluid equations
`D_t R = U`, `D_t m = −4π R²·p·U`, etc.) require the Einstein
field equations and ideal-fluid stress-energy, neither of which
is formalised in physlib. Those equations are therefore **not
shipped** here — only the algebraic identities at the
Schwarzschild horizon that follow from the standard area
formula.

## Contents

### §1 — Schwarzschild horizon area

* `schwarzschildArea M G c := 16π · G² · M² / c⁴`.
* `schwarzschildArea_pos`.
* **`schwarzschildArea_hasDerivAt_mass`** — derived calculus:
 `dA/dM = 32π · G² · M / c⁴`.

### §2 — Horizon-clock differential

* `horizonClock_diff_from_area dA ℓP := dA / (4·ℓ_P²)`.

### §3 — Three-form equivalence at the horizon

* **`schwarzschildHorizonEntropicTime_three_equivalences`** —
 Bekenstein area form, Schwarzschild mass form, and Jacobson
 energy/temperature form compute the same `dτ_hor` under the
 Planck-length identification `ℓ_P² = ℏ·G/c³`.

## References

* Bekenstein 1973 *Phys. Rev. D* 7, 2333.
* Jacobson 1995 *Phys. Rev. Lett.* 75, 1260.
* `Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate`
 — Schwarzschild Hawking temperature.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.SemiClassical

open Real

/-! ## §1 — Schwarzschild horizon area + derivative -/

/-- **Schwarzschild horizon area** as a function of mass:

  `A_S(M) := 16π · G² · M² / c⁴`. -/
def schwarzschildArea (M G c : ℝ) : ℝ := 16 * Real.pi * G^2 * M^2 / c^4

/-- **The Schwarzschild horizon area is positive** for positive
mass `M`, gravitational constant `G`, and speed of light `c`. -/
theorem schwarzschildArea_pos
    {M G c : ℝ} (hM : 0 < M) (hG : 0 < G) (hc : 0 < c) :
    0 < schwarzschildArea M G c := by
  unfold schwarzschildArea
  have : 0 < 16 * Real.pi * G^2 * M^2 := by positivity
  positivity

/-- **`dA/dM = 32π · G² · M / c⁴`** — derivative of the
Schwarzschild area with respect to mass, computed via Mathlib's
`HasDerivAt` infrastructure.

This is the **calculus identity** at the heart of the
Bekenstein-form horizon-clock differential
`dτ_hor = dA / (4·ℓ_P²)`. -/
theorem schwarzschildArea_hasDerivAt_mass
    (M G c : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun M' => schwarzschildArea M' G c)
      (32 * Real.pi * G^2 * M / c^4) M := by
  unfold schwarzschildArea
  have hM_sq : HasDerivAt (fun M' : ℝ => M' ^ 2) (2 * M) M := by
    have := hasDerivAt_pow 2 M
    simpa using this
  have h1 : HasDerivAt (fun M' : ℝ => 16 * Real.pi * G^2 * M'^2)
              (16 * Real.pi * G^2 * (2 * M)) M :=
    HasDerivAt.const_mul (16 * Real.pi * G^2) hM_sq
  have h2 : HasDerivAt (fun M' : ℝ => 16 * Real.pi * G^2 * M'^2 / c^4)
              ((16 * Real.pi * G^2 * (2 * M)) / c^4) M :=
    HasDerivAt.div_const h1 (c^4)
  convert h2 using 1
  ring

/-! ## §2 — Horizon-clock differential -/

/-- **Bekenstein horizon-clock differential**:

  `dτ_hor := dA / (4·ℓ_P²)`.

The horizon-area entropic-time advance per unit area increment
(Bekenstein 1973). -/
def horizonClock_diff_from_area (dA ℓP : ℝ) : ℝ := dA / (4 * ℓP^2)

/-! ## §3 — Three-form equivalence at the Schwarzschild horizon -/

/-- **:Schwarzschild horizon three-form equivalence**.

The three forms of the horizon entropic-time differential
**coincide algebraically** at the Schwarzschild horizon under
the standard identifications:

  `dτ_hor = dA / (4·ℓ_P²)`        (Bekenstein 1973),
  `dτ_hor = 8π·G·M·dM / (ℏ·c)`     (Schwarzschild mass form),
  `dτ_hor = dE / (k_B·T_H)`        (Jacobson 1995),

with `ℓ_P² = ℏ·G/c³`, `dE = c²·dM`, and `T_H` the Schwarzschild
Hawking temperature.

**Hypotheses**: the Planck-length identification `ℓ_P² = ℏ·G/c³`
and the dimensional / sign positivity conditions `ℏ, G, M, c, k_B > 0`.

The `dA` increment is taken at `dA = 32π·G²·M·dM/c⁴` — this is
the derivative-times-`dM` of `schwarzschildArea`, certified by
`schwarzschildArea_hasDerivAt_mass`. -/
theorem schwarzschildHorizonEntropicTime_three_equivalences
    {M G c ℏ kB ℓP dM : ℝ}
    (hℏ : 0 < ℏ) (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) (hkB : 0 < kB)
    (h_ℓP_sq : ℓP^2 = ℏ * G / c^3) :
    horizonClock_diff_from_area (32 * Real.pi * G^2 * M * dM / c^4) ℓP
      = 8 * Real.pi * G * M * dM / (ℏ * c) ∧
    horizonClock_diff_from_area (32 * Real.pi * G^2 * M * dM / c^4) ℓP
      = (dM * c^2) / (kB * schwarzschildHawkingTemperature ℏ G M c kB) := by
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_⟩
  · -- Bekenstein form = Schwarzschild mass form
    unfold horizonClock_diff_from_area
    rw [h_ℓP_sq]
    field_simp
    ring
  · -- Bekenstein form = Jacobson energy/temperature form
    unfold horizonClock_diff_from_area
    rw [schwarzschildHawkingTemperature_eq hG hM hc hkB]
    rw [h_ℓP_sq]
    field_simp
    ring

end Physlib.Relativity.SemiClassical

end
