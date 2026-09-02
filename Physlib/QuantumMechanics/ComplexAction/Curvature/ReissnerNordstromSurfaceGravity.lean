/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
public import Physlib.Relativity.SemiClassical.HawkingTemperature
meta import Zil

/-!
# Reissner–Nordström surface gravity and Hawking temperature

Building on the Reissner–Nordström horizon structure (`ReissnerNordstromHorizons`), the surface gravity
at the outer horizon is

`κ = (r_+ − r_-) / (2 r_+²) = √(M² − Q²) / r_+²`,

which reduces to the Schwarzschild value `1/(4M)` at zero charge and **vanishes at extremality**
`M² = Q²` (the two horizons merge), so the Hawking temperature `T = ℏκ/(2π c k_B)` of an extremal
black hole is zero — the third-law behaviour.  The repository had the generic `hawkingTemperature`
carrier but no charged-horizon surface gravity to feed it.

* `rnSurfaceGravity` — `κ = (r_+ − r_-)/(2 r_+²)`.
* `rnSurfaceGravity_eq` — `κ = √(M² − Q²)/r_+²`.
* `rnSurfaceGravity_schwarzschild` — `κ = 1/(4M)` at `Q = 0`.
* `rnSurfaceGravity_extremal` / `rnHawkingTemperature_extremal` — `κ = 0` and `T = 0` at `M² = Q²`.

Honest scope: this is the classical surface-gravity/temperature algebra; the derivation of the surface
gravity from the Killing-horizon normalization of the full metric is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
open Physlib.Relativity.SemiClassical

/-- **The Reissner–Nordström surface gravity at the outer horizon** `κ = (r_+ − r_-)/(2 r_+²)`. -/
def rnSurfaceGravity (M Q : ℝ) : ℝ :=
  (outerHorizon M Q - innerHorizon M Q) / (2 * outerHorizon M Q ^ 2)

/-- **The surface gravity in closed form** `κ = √(M² − Q²)/r_+²` (since `r_+ − r_- = 2√(M² − Q²)`). -/
@[zil_level physical_theorem]
theorem rnSurfaceGravity_eq (M Q : ℝ) :
    rnSurfaceGravity M Q = Real.sqrt (M ^ 2 - Q ^ 2) / outerHorizon M Q ^ 2 := by
  unfold rnSurfaceGravity outerHorizon innerHorizon
  rw [show M + Real.sqrt (M ^ 2 - Q ^ 2) - (M - Real.sqrt (M ^ 2 - Q ^ 2))
        = 2 * Real.sqrt (M ^ 2 - Q ^ 2) from by ring]
  rw [mul_div_mul_left _ _ (two_ne_zero)]

/-- **At zero charge the surface gravity is the Schwarzschild value** `κ = 1/(4M)` (for `M > 0`). -/
@[zil_level physical_theorem]
theorem rnSurfaceGravity_schwarzschild (M : ℝ) (hM : 0 < M) :
    rnSurfaceGravity M 0 = 1 / (4 * M) := by
  unfold rnSurfaceGravity outerHorizon innerHorizon
  rw [show (M : ℝ) ^ 2 - (0 : ℝ) ^ 2 = M ^ 2 from by ring, Real.sqrt_sq hM.le,
    show M + M - (M - M) = 2 * M from by ring, show M + M = 2 * M from by ring]
  have hM0 : M ≠ 0 := hM.ne'
  field_simp
  ring

/-- **The surface gravity vanishes at extremality** `M² = Q² ⇒ κ = 0` — the two horizons merge. -/
@[zil_level physical_theorem]
theorem rnSurfaceGravity_extremal (M Q : ℝ) (h : M ^ 2 = Q ^ 2) :
    rnSurfaceGravity M Q = 0 := by
  unfold rnSurfaceGravity
  obtain ⟨ho, hi⟩ := extremal_horizons_eq M Q h
  rw [ho, hi, sub_self, zero_div]

/-- **The Hawking temperature of an extremal Reissner–Nordström black hole is zero** — the third-law
behaviour, since the extremal surface gravity vanishes. -/
@[zil_level physical_theorem]
theorem rnHawkingTemperature_extremal (ℏ c kB M Q : ℝ) (h : M ^ 2 = Q ^ 2) :
    hawkingTemperature ℏ (rnSurfaceGravity M Q) c kB = 0 := by
  rw [rnSurfaceGravity_extremal M Q h]
  simp [hawkingTemperature]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity

zil attach rnSurfaceGravity_eq where
  formalizes @ "claim:the-reissner-nordstrom-surface-gravity-at-the-outer-horizon-equals-the-square-root-of-m-squared-minus-q-squared-divided-by-the-outer-horizon-radius-squared"

zil attach rnSurfaceGravity_schwarzschild where
  supported_by @ "lean:HermitianMat.sqrt_sq",
  formalizes @ "claim:at-zero-charge-the-reissner-nordstrom-surface-gravity-reduces-to-the-schwarzschild-value-one-over-four-m"

zil attach rnHawkingTemperature_extremal where
  formalizes @ "claim:the-hawking-temperature-of-an-extremal-reissner-nordstrom-black-hole-m-squared-equals-q-squared-is-zero-the-third-law-behaviour-since-the-extremal-surface-gravity-vanishes",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity.rnSurfaceGravity_extremal"

zil_file_contract physlib.reissnerNordstromSurfaceGravity where
  promises "The Reissner-Nordstrom surface gravity and Hawking temperature, building on the charged horizon structure. The surface gravity at the outer horizon is the difference of the horizon radii over twice the outer radius squared, which in closed form equals the square root of M squared minus Q squared over the outer horizon radius squared. It reduces to the Schwarzschild value one over four M at zero charge and vanishes at extremality M squared equals Q squared, where the two horizons merge, so the Hawking temperature of an extremal black hole is zero, the third-law behaviour. Reuses the generic Hawking temperature carrier and the Reissner-Nordstrom horizons. Honest scope: this is the classical surface-gravity and temperature algebra; the derivation of the surface gravity from the Killing-horizon normalization of the full metric is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.outerHorizon",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.innerHorizon",
    "lean:Physlib.Relativity.SemiClassical.hawkingTemperature"
  ]
  forbids_substitutes [
    "reading the classical surface-gravity and temperature algebra as a derivation of the surface gravity from the Killing-horizon normalization of the full metric"
  ]
  witnessed_by [
    rnSurfaceGravity_eq,
    rnSurfaceGravity_schwarzschild,
    rnSurfaceGravity_extremal,
    rnHawkingTemperature_extremal
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromSurfaceGravity
