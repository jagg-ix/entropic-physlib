/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons
public import Physlib.Relativity.SemiClassical.HawkingTemperature

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities -/

/-!
# Kerr–Newman horizon quantities: area, angular velocity, potential, surface gravity

With the horizon radius `r_+` and the combination `Σ_+ = r_+² + a²`, the outer-horizon quantities of a
Kerr–Newman black hole are

* area `𝒜 = 4π Σ_+`;
* angular velocity `Ω_H = a/Σ_+` (frame dragging);
* electric potential `Φ_H = Q r_+/Σ_+`;
* surface gravity `κ = (r_+ − r_-)/(2 Σ_+) = √(M² − a² − Q²)/Σ_+`.

These are the rotating generalizations of the Reissner–Nordström quantities (`Σ_+ = r_+²` and `Ω_H = 0`
at `a = 0`).

* `knSurfaceGravity_eq` — the closed form `κ = √(M² − a² − Q²)/Σ_+`.
* `knSurfaceGravity_extremal` — `κ = 0` at extremality `M² = a² + Q²`.
* `knHorizonArea_pos` — the area is positive for `M > 0`.
* `knAngularVelocity_reissnerNordstrom` — `Ω_H = 0` at zero spin (no frame dragging).

Honest scope: the horizon-quantity algebra; the geometric derivation of these from the metric (Killing
horizon, angular momentum) is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons

/-- **The outer-horizon area** `𝒜 = 4π Σ_+ = 4π(r_+² + a²)`. -/
def knHorizonArea (M a Q : ℝ) : ℝ := 4 * Real.pi * (knOuterHorizon M a Q ^ 2 + a ^ 2)

/-- **The horizon angular velocity** `Ω_H = a/Σ_+` (frame dragging). -/
def knAngularVelocity (M a Q : ℝ) : ℝ := a / (knOuterHorizon M a Q ^ 2 + a ^ 2)

/-- **The horizon electric potential** `Φ_H = Q r_+/Σ_+`. -/
def knHorizonPotential (M a Q : ℝ) : ℝ :=
  Q * knOuterHorizon M a Q / (knOuterHorizon M a Q ^ 2 + a ^ 2)

/-- **The surface gravity** `κ = (r_+ − r_-)/(2 Σ_+)`. -/
def knSurfaceGravity (M a Q : ℝ) : ℝ :=
  (knOuterHorizon M a Q - knInnerHorizon M a Q) / (2 * (knOuterHorizon M a Q ^ 2 + a ^ 2))

/-- **The outer horizon is positive** `r_+ = M + √(M² − a² − Q²) > 0` for `M > 0`. -/
theorem knOuterHorizon_pos (M a Q : ℝ) (hM : 0 < M) : 0 < knOuterHorizon M a Q := by
  unfold knOuterHorizon
  have := Real.sqrt_nonneg (M ^ 2 - a ^ 2 - Q ^ 2)
  linarith

/-- **The area denominator is positive** `Σ_+ = r_+² + a² > 0` for `M > 0`. -/
theorem knHorizonDenom_pos (M a Q : ℝ) (hM : 0 < M) : 0 < knOuterHorizon M a Q ^ 2 + a ^ 2 := by
  have hr := knOuterHorizon_pos M a Q hM
  positivity

/-- **The surface gravity in closed form** `κ = √(M² − a² − Q²)/Σ_+` (since `r_+ − r_- = 2√(M² − a² − Q²)`). -/
@[zil_level physical_theorem]
theorem knSurfaceGravity_eq (M a Q : ℝ) :
    knSurfaceGravity M a Q =
      Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) / (knOuterHorizon M a Q ^ 2 + a ^ 2) := by
  unfold knSurfaceGravity knInnerHorizon
  rw [show knOuterHorizon M a Q - (M - Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2))
        = 2 * Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) from by unfold knOuterHorizon; ring]
  rw [mul_div_mul_left _ _ (two_ne_zero)]

/-- **The surface gravity vanishes at extremality** `M² = a² + Q² ⇒ κ = 0`. -/
@[zil_level physical_theorem]
theorem knSurfaceGravity_extremal (M a Q : ℝ) (h : M ^ 2 = a ^ 2 + Q ^ 2) :
    knSurfaceGravity M a Q = 0 := by
  unfold knSurfaceGravity
  obtain ⟨ho, hi⟩ := knHorizon_extremal M a Q h
  rw [ho, hi, sub_self, zero_div]

/-- **The horizon area is positive** for `M > 0`. -/
@[zil_level physical_theorem]
theorem knHorizonArea_pos (M a Q : ℝ) (hM : 0 < M) : 0 < knHorizonArea M a Q := by
  have hd := knHorizonDenom_pos M a Q hM
  have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
  unfold knHorizonArea
  exact mul_pos h4 hd

/-- **At zero spin the angular velocity vanishes** `Ω_H = 0` — no frame dragging. -/
@[zil_level physical_theorem]
theorem knAngularVelocity_reissnerNordstrom (M Q : ℝ) : knAngularVelocity M 0 Q = 0 := by
  simp [knAngularVelocity]

end Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities

zil attach knSurfaceGravity_eq where
  formalizes @ "claim:the-kerr-newman-surface-gravity-at-the-outer-horizon-equals-the-square-root-of-m-squared-minus-a-squared-minus-q-squared-over-the-horizon-cross-section-r-plus-squared-plus-a-squared"

zil attach knSurfaceGravity_extremal where
  supported_by @ "lean:knHorizon_extremal",
  formalizes @ "claim:the-kerr-newman-surface-gravity-vanishes-at-extremality-m-squared-equals-a-squared-plus-q-squared"

zil attach knHorizonArea_pos where
  formalizes @ "claim:the-kerr-newman-outer-horizon-area-four-pi-times-r-plus-squared-plus-a-squared-is-positive-for-positive-mass"

zil attach knAngularVelocity_reissnerNordstrom where
  formalizes @ "claim:at-zero-spin-the-kerr-newman-horizon-angular-velocity-vanishes-there-is-no-frame-dragging"

zil_file_contract physlib.kerrNewmanHorizonQuantities where
  promises "The Kerr-Newman outer-horizon quantities: area, angular velocity, electric potential, and surface gravity, the rotating generalizations of the Reissner-Nordstrom quantities with the horizon cross-section r-plus-squared plus a-squared. The area is four pi times the horizon cross-section, the angular velocity is the spin parameter over the cross-section, the electric potential is the charge times the outer horizon radius over the cross-section, and the surface gravity is the horizon-radius difference over twice the cross-section, equal in closed form to the square root of mass-squared minus spin-squared minus charge-squared over the cross-section. The surface gravity vanishes at extremality mass-squared equals spin-squared plus charge-squared, the area is positive for positive mass, and at zero spin the angular velocity vanishes, there is no frame dragging. Honest scope: the horizon-quantity algebra; the geometric derivation of these from the metric is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knOuterHorizon",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knInnerHorizon"
  ]
  forbids_substitutes [
    "reading the horizon-quantity algebra as a geometric derivation of these quantities from the Kerr-Newman metric Killing horizon"
  ]
  witnessed_by [
    knSurfaceGravity_eq,
    knSurfaceGravity_extremal,
    knHorizonArea_pos,
    knAngularVelocity_reissnerNordstrom
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.kerrNewmanHorizonQuantities

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw -/

/-!
# The third law for the Kerr–Newman black hole

At extremality `M² = a² + Q²` the two horizons merge and the surface gravity vanishes
(`knSurfaceGravity_extremal`), so the Hawking temperature `T = ℏκ/(2π c k_B)` of an extremal Kerr–Newman
black hole is **zero** — the third-law behaviour, now including rotation and charge together.  At
extremality the horizon sits at `r_+ = M`, so the horizon area is `𝒜 = 4π(M² + a²)`.

* `kn_hawkingTemperature_extremal` — `T = 0` at `M² = a² + Q²`.
* `knExtremalArea` — `𝒜 = 4π(M² + a²)` at extremality.

Honest scope: the extremal-limit temperature/area algebra; the third law as an unattainability statement
about physical processes is not addressed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities
open Physlib.Relativity.SemiClassical

/-- **The Hawking temperature of an extremal Kerr–Newman black hole is zero** — the third-law behaviour,
since the extremal surface gravity vanishes. -/
@[zil_level physical_theorem]
theorem kn_hawkingTemperature_extremal (ℏ c kB M a Q : ℝ) (h : M ^ 2 = a ^ 2 + Q ^ 2) :
    hawkingTemperature ℏ (knSurfaceGravity M a Q) c kB = 0 := by
  rw [knSurfaceGravity_extremal M a Q h]
  simp [hawkingTemperature]

/-- **The extremal Kerr–Newman horizon area** `𝒜 = 4π(M² + a²)` (the extremal horizon sits at `r_+ = M`). -/
@[zil_level physical_theorem]
theorem knExtremalArea (M a Q : ℝ) (h : M ^ 2 = a ^ 2 + Q ^ 2) :
    knHorizonArea M a Q = 4 * Real.pi * (M ^ 2 + a ^ 2) := by
  unfold knHorizonArea
  rw [(knHorizon_extremal M a Q h).1]

end Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw

zil attach kn_hawkingTemperature_extremal where
  formalizes @ "claim:the-hawking-temperature-of-an-extremal-kerr-newman-black-hole-m-squared-equals-a-squared-plus-q-squared-is-zero-the-third-law-behaviour-with-rotation-and-charge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities.knSurfaceGravity_extremal"

zil attach knExtremalArea where
  supported_by @ "lean:knHorizon_extremal",
  formalizes @ "claim:the-extremal-kerr-newman-horizon-area-is-four-pi-times-m-squared-plus-a-squared-since-the-extremal-horizon-sits-at-r-plus-equals-m"

zil_file_contract physlib.kerrNewmanThirdLaw where
  promises "The third law for the Kerr-Newman black hole. At extremality mass-squared equals spin-squared plus charge-squared the two horizons merge and the surface gravity vanishes, so the Hawking temperature of an extremal Kerr-Newman black hole is zero, the third-law behaviour now including rotation and charge together. At extremality the horizon sits at the outer radius equal to the mass, so the horizon area is four pi times mass-squared plus spin-squared. Honest scope: the extremal-limit temperature and area algebra; the third law as an unattainability statement about physical processes is not addressed."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities.knSurfaceGravity",
    "lean:Physlib.Relativity.SemiClassical.hawkingTemperature"
  ]
  forbids_substitutes [
    "reading the extremal-limit temperature and area algebra as the third law stated as an unattainability principle for physical processes"
  ]
  witnessed_by [
    kn_hawkingTemperature_extremal,
    knExtremalArea
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.kerrNewmanThirdLaw

