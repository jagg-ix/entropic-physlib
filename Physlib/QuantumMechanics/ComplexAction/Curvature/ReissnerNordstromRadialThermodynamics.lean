/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.SemiClassical.HawkingTemperature
meta import Zil

/-!
# Reissner–Nordström thermodynamics parametrized by the horizon radius

For the first law and its calculus it is natural to take the outer-horizon radius `r` and charge `Q` as
the independent variables (with the mass `M` derived).  In geometric units `G = ℏ = c = k_B = 1`:

* mass `M(r,Q) = (r + Q²/r)/2` (from `2M = r_+ + Q²/r_+`);
* surface gravity `κ(r,Q) = (r² − Q²)/(2r³)` (`= (r − Q²/r)/(2r²)`, with the inner horizon `r_- = Q²/r`);
* entropy `S(r) = π r²` (`= 𝒜/4`);
* horizon potential `Φ(r,Q) = Q/r`;
* temperature `T(r,Q) = κ/(2π)`.

This module records the sign/limit structure that the first law (`ReissnerNordstromFirstLaw`) builds on:
the surface gravity vanishes at extremality `r² = Q²`, is positive for a non-degenerate horizon `Q² < r²`,
reduces to Schwarzschild `1/(2r)` at zero charge, and the temperature is positive off extremality.

Honest scope: this is the radius-parametrized thermodynamic algebra in geometric units; the constants
`G, ℏ, c, k_B` are set to one.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics

/-- **Mass parametrized by horizon radius** `M(r,Q) = (r + Q²/r)/2`. -/
def rnMassR (r Q : ℝ) : ℝ := (r + Q ^ 2 / r) / 2

/-- **Surface gravity parametrized by horizon radius** `κ(r,Q) = (r² − Q²)/(2r³)`. -/
def rnSurfaceGravityR (r Q : ℝ) : ℝ := (r ^ 2 - Q ^ 2) / (2 * r ^ 3)

/-- **Entropy parametrized by horizon radius** `S(r) = π r²` (geometric units, `= 𝒜/4`). -/
def rnEntropyR (r : ℝ) : ℝ := Real.pi * r ^ 2

/-- **Horizon electric potential** `Φ(r,Q) = Q/r`. -/
def rnPotentialR (r Q : ℝ) : ℝ := Q / r

/-- **Temperature parametrized by horizon radius** `T(r,Q) = κ/(2π)`. -/
def rnTempR (r Q : ℝ) : ℝ := rnSurfaceGravityR r Q / (2 * Real.pi)

/-- **The surface gravity vanishes at extremality** `r² = Q² ⇒ κ = 0`. -/
@[zil_level physical_theorem]
theorem rnSurfaceGravityR_extremal (r Q : ℝ) (h : r ^ 2 = Q ^ 2) :
    rnSurfaceGravityR r Q = 0 := by
  unfold rnSurfaceGravityR
  rw [h, sub_self, zero_div]

/-- **The surface gravity is positive for a non-degenerate horizon** `0 < r`, `Q² < r² ⇒ 0 < κ`. -/
@[zil_level physical_theorem]
theorem rnSurfaceGravityR_pos (r Q : ℝ) (hr : 0 < r) (h : Q ^ 2 < r ^ 2) :
    0 < rnSurfaceGravityR r Q := by
  unfold rnSurfaceGravityR
  apply div_pos (by linarith)
  positivity

/-- **At zero charge the surface gravity is the Schwarzschild value** `κ = 1/(2r)` (for `r ≠ 0`). -/
@[zil_level physical_theorem]
theorem rnSurfaceGravityR_schwarzschild (r : ℝ) (hr : r ≠ 0) :
    rnSurfaceGravityR r 0 = 1 / (2 * r) := by
  unfold rnSurfaceGravityR
  rw [show (0 : ℝ) ^ 2 = 0 from by ring, sub_zero]
  field_simp

/-- **The temperature is positive off extremality** `0 < r`, `Q² < r² ⇒ 0 < T`. -/
@[zil_level physical_theorem]
theorem rnTempR_pos (r Q : ℝ) (hr : 0 < r) (h : Q ^ 2 < r ^ 2) : 0 < rnTempR r Q := by
  unfold rnTempR
  apply div_pos (rnSurfaceGravityR_pos r Q hr h)
  positivity

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics

zil attach rnSurfaceGravityR_extremal where
  formalizes @ "claim:the-radius-parametrized-reissner-nordstrom-surface-gravity-r-squared-minus-q-squared-over-two-r-cubed-vanishes-at-extremality-r-squared-equals-q-squared"

zil attach rnSurfaceGravityR_pos where
  formalizes @ "claim:the-radius-parametrized-reissner-nordstrom-surface-gravity-is-positive-for-a-non-degenerate-horizon-q-squared-less-than-r-squared"

zil attach rnTempR_pos where
  supported_by @ "lean:rnSurfaceGravityR_pos",
  formalizes @ "claim:the-radius-parametrized-reissner-nordstrom-temperature-kappa-over-two-pi-is-positive-off-extremality"

zil_file_contract physlib.reissnerNordstromRadialThermodynamics where
  promises "The Reissner-Nordstrom thermodynamics parametrized by the outer-horizon radius, the natural variables for the first law and its calculus, in geometric units. The mass is r plus Q squared over r all over two, the surface gravity is r squared minus Q squared over two r cubed, the entropy is pi r squared, the horizon potential is Q over r, and the temperature is the surface gravity over two pi. The surface gravity vanishes at extremality r squared equals Q squared, is positive for a non-degenerate horizon Q squared less than r squared, and reduces to the Schwarzschild value one over two r at zero charge; the temperature is positive off extremality. Honest scope: this is the radius-parametrized thermodynamic algebra in geometric units with the constants set to one."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics.rnSurfaceGravityR",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics.rnTempR"
  ]
  forbids_substitutes [
    "reading the geometric-unit radius-parametrized algebra as carrying the dimensional constants G, hbar, c, k_B explicitly"
  ]
  witnessed_by [
    rnSurfaceGravityR_extremal,
    rnSurfaceGravityR_pos,
    rnSurfaceGravityR_schwarzschild,
    rnTempR_pos
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromRadialThermodynamics
