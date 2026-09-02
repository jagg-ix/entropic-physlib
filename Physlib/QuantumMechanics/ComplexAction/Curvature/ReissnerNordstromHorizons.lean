/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicciFromMetric
meta import Zil

/-!
# The Reissner–Nordström charged black hole: metric function and horizons

The repository carries the Schwarzschild vacuum metric function `schwF M r = 1 − 2M/r` but no charged
(Einstein–Maxwell electrovacuum) analog.  The Reissner–Nordström metric of a charged black hole has
the lapse function `f(r) = 1 − 2M/r + Q²/r²`; this module supplies it and its horizon structure.

* `reissnerNordstromF` — `f(r) = 1 − 2M/r + Q²/r²`; `reissnerNordstromF_uncharged` reduces it to
  Schwarzschild `schwF` at zero charge.
* `reissnerNordstromF_outerHorizon` / `_innerHorizon` — `f` vanishes at the horizons
  `r_± = M ± √(M² − Q²)` (for `Q² ≤ M²`).
* `horizon_product` — `r_+ · r_- = Q²`; `horizon_sum` — `r_+ + r_- = 2M`.
* `extremal_horizons_eq` — at extremality `M² = Q²` the two horizons coincide at `r = M`.

Honest scope: this is the metric function and its horizon/charge algebra; the verification that the
full Reissner–Nordström metric solves the Einstein–Maxwell equation `G = κ T^Maxwell` (a curvature
computation) is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci

/-- **The Reissner–Nordström lapse function** `f(r) = 1 − 2M/r + Q²/r²` of a charged black hole. -/
def reissnerNordstromF (M Q r : ℝ) : ℝ := 1 - 2 * M / r + Q ^ 2 / r ^ 2

/-- **At zero charge Reissner–Nordström reduces to Schwarzschild** `f(r) = 1 − 2M/r`. -/
@[zil_level physical_theorem]
theorem reissnerNordstromF_uncharged (M r : ℝ) : reissnerNordstromF M 0 r = schwF M r := by
  simp [reissnerNordstromF, schwF]

/-- The lapse cleared of denominators: `f(r)·r² = r² − 2Mr + Q²` (`r ≠ 0`). -/
theorem reissnerNordstromF_mul_rSq (M Q r : ℝ) (hr : r ≠ 0) :
    reissnerNordstromF M Q r * r ^ 2 = r ^ 2 - 2 * M * r + Q ^ 2 := by
  unfold reissnerNordstromF
  field_simp

/-- **The outer horizon** `r_+ = M + √(M² − Q²)`. -/
def outerHorizon (M Q : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - Q ^ 2)

/-- **The inner (Cauchy) horizon** `r_- = M − √(M² − Q²)`. -/
def innerHorizon (M Q : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - Q ^ 2)

/-- The Reissner–Nordström horizon polynomial `r² − 2Mr + Q²` vanishes at both `r_±`. -/
theorem horizon_root (M Q x : ℝ) (h : Q ^ 2 ≤ M ^ 2)
    (hx : x = outerHorizon M Q ∨ x = innerHorizon M Q) :
    x ^ 2 - 2 * M * x + Q ^ 2 = 0 := by
  have hd : (0 : ℝ) ≤ M ^ 2 - Q ^ 2 := by linarith
  have hsq : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := Real.sq_sqrt hd
  rcases hx with h | h <;> subst h <;> simp only [outerHorizon, innerHorizon] <;> nlinarith [hsq]

/-- **The lapse vanishes at the outer horizon** `f(r_+) = 0` (for `Q² ≤ M²`, `r_+ ≠ 0`). -/
@[zil_level physical_theorem]
theorem reissnerNordstromF_outerHorizon (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hr : outerHorizon M Q ≠ 0) :
    reissnerNordstromF M Q (outerHorizon M Q) = 0 := by
  have hpoly := horizon_root M Q (outerHorizon M Q) h (Or.inl rfl)
  have hmul := reissnerNordstromF_mul_rSq M Q (outerHorizon M Q) hr
  rw [hpoly] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 2 hr)

/-- **The lapse vanishes at the inner (Cauchy) horizon** `f(r_-) = 0` (for `Q² ≤ M²`, `r_- ≠ 0`). -/
@[zil_level physical_theorem]
theorem reissnerNordstromF_innerHorizon (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hr : innerHorizon M Q ≠ 0) :
    reissnerNordstromF M Q (innerHorizon M Q) = 0 := by
  have hpoly := horizon_root M Q (innerHorizon M Q) h (Or.inr rfl)
  have hmul := reissnerNordstromF_mul_rSq M Q (innerHorizon M Q) hr
  rw [hpoly] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 2 hr)

/-- **The horizon product equals the squared charge** `r_+ · r_- = Q²`. -/
@[zil_level physical_theorem]
theorem horizon_product (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) :
    outerHorizon M Q * innerHorizon M Q = Q ^ 2 := by
  have hd : (0 : ℝ) ≤ M ^ 2 - Q ^ 2 := by linarith
  have hsq : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := Real.sq_sqrt hd
  simp only [outerHorizon, innerHorizon]; nlinarith [hsq]

/-- **The horizon sum equals twice the mass** `r_+ + r_- = 2M`. -/
theorem horizon_sum (M Q : ℝ) : outerHorizon M Q + innerHorizon M Q = 2 * M := by
  simp only [outerHorizon, innerHorizon]; ring

/-- **At extremality `M² = Q²` the two horizons coincide** at `r = M`. -/
@[zil_level physical_theorem]
theorem extremal_horizons_eq (M Q : ℝ) (h : M ^ 2 = Q ^ 2) :
    outerHorizon M Q = M ∧ innerHorizon M Q = M := by
  have hz : M ^ 2 - Q ^ 2 = 0 := by rw [h]; ring
  simp [outerHorizon, innerHorizon, hz]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

zil attach reissnerNordstromF_uncharged where
  formalizes @ "claim:the-reissner-nordstrom-charged-black-hole-lapse-function-one-minus-two-m-over-r-plus-q-squared-over-r-squared-reduces-to-the-schwarzschild-lapse-at-zero-charge"

zil attach reissnerNordstromF_outerHorizon where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.horizon_root",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.reissnerNordstromF_mul_rSq",
  formalizes @ "claim:the-reissner-nordstrom-lapse-function-vanishes-at-the-outer-horizon-r-plus-equals-m-plus-square-root-of-m-squared-minus-q-squared"

zil attach horizon_product where
  formalizes @ "claim:the-product-of-the-reissner-nordstrom-outer-and-inner-horizon-radii-equals-the-squared-charge"

zil attach extremal_horizons_eq where
  formalizes @ "claim:at-extremality-m-squared-equals-q-squared-the-reissner-nordstrom-outer-and-inner-horizons-coincide-at-r-equals-m"

zil_file_contract physlib.reissnerNordstromHorizons where
  promises "The Reissner-Nordstrom charged black hole metric function and horizon structure, the charged Einstein-Maxwell analog the repository lacked. The Reissner-Nordstrom lapse function one minus two M over r plus Q squared over r squared reduces to the Schwarzschild lapse at zero charge. The lapse vanishes at the outer and inner horizons r plus and r minus equal M plus or minus the square root of M squared minus Q squared for squared charge at most squared mass. The product of the horizon radii equals the squared charge, their sum equals twice the mass, and at extremality M squared equals Q squared the two horizons coincide at r equals M. Honest scope: this is the metric function and its horizon and charge algebra; the verification that the full Reissner-Nordstrom metric solves the Einstein-Maxwell equation is a curvature computation not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.schwF"
  ]
  forbids_substitutes [
    "reading the Reissner-Nordstrom lapse and horizon algebra as a verification that the full charged metric solves the Einstein-Maxwell field equation"
  ]
  witnessed_by [
    reissnerNordstromF_uncharged,
    reissnerNordstromF_outerHorizon,
    reissnerNordstromF_innerHorizon,
    horizon_product,
    extremal_horizons_eq
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromHorizons
