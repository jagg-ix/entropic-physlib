/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
meta import Zil

/-!
# The Kerr–Newman black hole: horizons

The Kerr–Newman metric is the most general stationary electrovacuum black hole (mass `M`, spin parameter
`a = J/M`, charge `Q`).  Its horizons are the roots of `Δ(r) = r² − 2Mr + (a² + Q²)`:

`r_± = M ± √(M² − a² − Q²)`,

reducing to Reissner–Nordström at `a = 0` and to Kerr at `Q = 0`.  This module supplies the horizon
function, the outer/inner horizons, and the horizon/spin/charge algebra — the Kerr–Newman generalization
of `ReissnerNordstromHorizons` (`a² + Q²` in place of `Q²`).

* `knDelta` — `Δ(r) = r² − 2Mr + (a² + Q²)`.
* `knOuterHorizon` / `knInnerHorizon` — `r_± = M ± √(M² − a² − Q²)`.
* `knHorizon_root` — `Δ` vanishes at both `r_±` (for `a² + Q² ≤ M²`).
* `knHorizon_product` — `r_+ · r_- = a² + Q²`; `knHorizon_sum` — `r_+ + r_- = 2M`.
* `knHorizon_extremal` — at extremality `M² = a² + Q²` the horizons coincide at `r = M`.
* `knOuterHorizon_reissnerNordstrom` — at zero spin the outer horizon is the Reissner–Nordström one.

Honest scope: this is the horizon polynomial `Δ` and its root/spin/charge algebra; the full Kerr–Newman
metric and its Einstein–Maxwell verification are not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

/-- **The Kerr–Newman horizon function** `Δ(r) = r² − 2Mr + (a² + Q²)`. -/
def knDelta (M a Q r : ℝ) : ℝ := r ^ 2 - 2 * M * r + (a ^ 2 + Q ^ 2)

/-- **The outer horizon** `r_+ = M + √(M² − a² − Q²)`. -/
def knOuterHorizon (M a Q : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2)

/-- **The inner (Cauchy) horizon** `r_- = M − √(M² − a² − Q²)`. -/
def knInnerHorizon (M a Q : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2)

/-- **The horizon function vanishes at both `r_±`** (for `a² + Q² ≤ M²`). -/
theorem knHorizon_root (M a Q x : ℝ) (h : a ^ 2 + Q ^ 2 ≤ M ^ 2)
    (hx : x = knOuterHorizon M a Q ∨ x = knInnerHorizon M a Q) :
    knDelta M a Q x = 0 := by
  have hd : (0 : ℝ) ≤ M ^ 2 - a ^ 2 - Q ^ 2 := by linarith
  have hsq : Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - a ^ 2 - Q ^ 2 := Real.sq_sqrt hd
  unfold knDelta
  rcases hx with h | h <;> subst h <;> simp only [knOuterHorizon, knInnerHorizon] <;> nlinarith [hsq]

/-- **The horizon product equals the spin-plus-charge combination** `r_+ · r_- = a² + Q²`. -/
@[zil_level physical_theorem]
theorem knHorizon_product (M a Q : ℝ) (h : a ^ 2 + Q ^ 2 ≤ M ^ 2) :
    knOuterHorizon M a Q * knInnerHorizon M a Q = a ^ 2 + Q ^ 2 := by
  have hd : (0 : ℝ) ≤ M ^ 2 - a ^ 2 - Q ^ 2 := by linarith
  have hsq : Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - a ^ 2 - Q ^ 2 := Real.sq_sqrt hd
  simp only [knOuterHorizon, knInnerHorizon]; nlinarith [hsq]

/-- **The horizon sum equals twice the mass** `r_+ + r_- = 2M`. -/
@[zil_level physical_theorem]
theorem knHorizon_sum (M a Q : ℝ) : knOuterHorizon M a Q + knInnerHorizon M a Q = 2 * M := by
  simp only [knOuterHorizon, knInnerHorizon]; ring

/-- **At extremality `M² = a² + Q²` the two horizons coincide** at `r = M`. -/
@[zil_level physical_theorem]
theorem knHorizon_extremal (M a Q : ℝ) (h : M ^ 2 = a ^ 2 + Q ^ 2) :
    knOuterHorizon M a Q = M ∧ knInnerHorizon M a Q = M := by
  have hz : M ^ 2 - a ^ 2 - Q ^ 2 = 0 := by rw [h]; ring
  simp [knOuterHorizon, knInnerHorizon, hz]

/-- **At zero spin the Kerr–Newman outer horizon is the Reissner–Nordström one** `r_+ = M + √(M² − Q²)`. -/
@[zil_level physical_theorem]
theorem knOuterHorizon_reissnerNordstrom (M Q : ℝ) :
    knOuterHorizon M 0 Q = outerHorizon M Q := by
  simp only [knOuterHorizon, outerHorizon]
  rw [show M ^ 2 - (0 : ℝ) ^ 2 - Q ^ 2 = M ^ 2 - Q ^ 2 from by ring]

end Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons

zil attach knHorizon_product where
  formalizes @ "claim:the-product-of-the-kerr-newman-outer-and-inner-horizon-radii-equals-the-spin-squared-plus-charge-squared-combination"

zil attach knHorizon_extremal where
  formalizes @ "claim:at-extremality-m-squared-equals-a-squared-plus-q-squared-the-kerr-newman-outer-and-inner-horizons-coincide-at-r-equals-m"

zil attach knOuterHorizon_reissnerNordstrom where
  formalizes @ "claim:at-zero-spin-the-kerr-newman-outer-horizon-reduces-to-the-reissner-nordstrom-outer-horizon"

zil_file_contract physlib.kerrNewmanHorizons where
  promises "The Kerr-Newman black hole horizons, the most general stationary electrovacuum black hole with mass, spin parameter, and charge, generalizing Reissner-Nordstrom with the spin-squared plus charge-squared combination in place of charge-squared. The horizon function Delta of r is r squared minus two M r plus a squared plus Q squared, whose roots are the outer and inner horizons M plus or minus the square root of M squared minus a squared minus Q squared. Delta vanishes at both horizons for spin-squared plus charge-squared at most mass-squared. The product of the horizon radii equals the spin-squared plus charge-squared combination, their sum equals twice the mass, and at extremality M squared equals a squared plus Q squared the two horizons coincide at r equals M. At zero spin the outer horizon reduces to the Reissner-Nordstrom outer horizon. Honest scope: this is the horizon polynomial and its root, spin, and charge algebra; the full Kerr-Newman metric and its Einstein-Maxwell verification are not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.outerHorizon"
  ]
  forbids_substitutes [
    "reading the Kerr-Newman horizon and spin-charge algebra as a verification that the full rotating charged metric solves the Einstein-Maxwell field equation"
  ]
  witnessed_by [
    knHorizon_product,
    knHorizon_sum,
    knHorizon_extremal,
    knOuterHorizon_reissnerNordstrom
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.kerrNewmanHorizons
