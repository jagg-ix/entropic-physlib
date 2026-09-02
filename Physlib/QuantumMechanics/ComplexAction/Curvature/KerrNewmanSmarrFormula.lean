/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities
meta import Zil

/-!
# The Kerr–Newman Smarr formula

The Smarr mass formula for the most general stationary black hole ties together **all four** horizon
quantities — surface gravity, area, angular velocity/momentum, and charge/potential:

`M = κ 𝒜/(4π) + 2 Ω_H J + Φ_H Q`,   `J = M a`.

The rotational term `2 Ω_H J` is the Kerr–Newman generalization of the Reissner–Nordström Smarr formula.
The geometric term collapses to `κ 𝒜/(4π) = r_+ − M`, and the whole identity is equivalent to the horizon
equation `Δ(r_+) = 0`.

* `knAngularMomentum` — `J = M a`.
* `knSmarrGeometricTerm_eq` — `κ 𝒜/(4π) = r_+ − M`.
* `kn_smarr_formula` — `M = κ 𝒜/(4π) + 2 Ω_H J + Φ_H Q`.

Honest scope: the static (integral) Smarr identity connecting the algebraic quantities; the differential
first law `dM = (κ/8π) d𝒜 + Ω_H dJ + Φ_H dQ` as a genuine variation is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanSmarrFormula

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities

/-- **The angular momentum** `J = M a`. -/
def knAngularMomentum (M a : ℝ) : ℝ := M * a

/-- **The Smarr geometric term** `κ 𝒜/(4π) = r_+ − M`. -/
@[zil_level physical_theorem]
theorem knSmarrGeometricTerm_eq (M a Q : ℝ) (hM : 0 < M) :
    knSurfaceGravity M a Q * knHorizonArea M a Q / (4 * Real.pi) = knOuterHorizon M a Q - M := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hDne : knOuterHorizon M a Q ^ 2 + a ^ 2 ≠ 0 := (knHorizonDenom_pos M a Q hM).ne'
  rw [knSurfaceGravity_eq, knHorizonArea,
    show knOuterHorizon M a Q - M = Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) from by unfold knOuterHorizon; ring]
  field_simp

/-- **The Kerr–Newman Smarr formula** `M = κ 𝒜/(4π) + 2 Ω_H J + Φ_H Q` — the total mass from the surface
gravity, area, angular velocity/momentum and charge/potential of the rotating charged horizon. -/
@[zil_level bridge_theorem]
theorem kn_smarr_formula (M a Q : ℝ) (h : a ^ 2 + Q ^ 2 ≤ M ^ 2) (hM : 0 < M) :
    knSurfaceGravity M a Q * knHorizonArea M a Q / (4 * Real.pi)
      + 2 * knAngularVelocity M a Q * knAngularMomentum M a
      + knHorizonPotential M a Q * Q = M := by
  have hDne : knOuterHorizon M a Q ^ 2 + a ^ 2 ≠ 0 := (knHorizonDenom_pos M a Q hM).ne'
  have hΔ : knOuterHorizon M a Q ^ 2 - 2 * M * knOuterHorizon M a Q + (a ^ 2 + Q ^ 2) = 0 := by
    have hroot := knHorizon_root M a Q (knOuterHorizon M a Q) h (Or.inl rfl)
    unfold knDelta at hroot; linarith [hroot]
  rw [knSmarrGeometricTerm_eq M a Q hM, knAngularVelocity, knHorizonPotential, knAngularMomentum]
  field_simp
  linear_combination knOuterHorizon M a Q * hΔ

end Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanSmarrFormula

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanSmarrFormula

zil attach knSmarrGeometricTerm_eq where
  supported_by @ "lean:knSurfaceGravity_eq",
  formalizes @ "claim:the-kerr-newman-smarr-geometric-term-surface-gravity-times-horizon-area-over-four-pi-equals-the-outer-horizon-radius-minus-the-mass"

zil attach kn_smarr_formula where
  formalizes @ "claim:the-kerr-newman-smarr-formula-the-total-mass-equals-surface-gravity-times-area-over-four-pi-plus-twice-the-angular-velocity-times-angular-momentum-plus-the-horizon-potential-times-charge-connecting-all-four-horizon-quantities",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_root",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanSmarrFormula.knSmarrGeometricTerm_eq"

zil_file_contract physlib.kerrNewmanSmarrFormula where
  promises "The Kerr-Newman Smarr formula, the mass formula for the most general stationary black hole, tying together all four horizon quantities. The angular momentum is mass times spin parameter. The Smarr geometric term, the surface gravity times the horizon area over four pi, equals the outer horizon radius minus the mass. The Smarr formula then states the total mass equals the surface gravity times area over four pi plus twice the angular velocity times angular momentum plus the horizon electric potential times charge, connecting surface gravity, area, angular velocity and momentum, and charge and potential; the rotational term is the Kerr-Newman generalization of the Reissner-Nordstrom Smarr formula, and the identity is equivalent to the horizon equation. Honest scope: the static integral Smarr identity connecting the algebraic quantities; the differential first law as a genuine variation is not carried here."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities.knSurfaceGravity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities.knAngularVelocity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_root"
  ]
  forbids_substitutes [
    "reading the static integral Smarr identity as the differential first law of Kerr-Newman thermodynamics proved as a genuine variation"
  ]
  witnessed_by [
    knSmarrGeometricTerm_eq,
    kn_smarr_formula
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.kerrNewmanSmarrFormula
