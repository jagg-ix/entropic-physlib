/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicciFromMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits
meta import Zil

/-!
# The Schwarzschild–de Sitter (Kottler) black hole: horizons

A black hole in a cosmological (de Sitter) background has the Kottler lapse
`f(r) = 1 − 2M/r − Λr²/3`, interpolating between Schwarzschild (`Λ = 0`) and de Sitter (`M = 0`).  Its
horizons are the positive roots of the cubic `p(r) = Λr³ − 3r + 6M` (the cleared `f(r) = 0`): a
black-hole horizon and a cosmological horizon.

* `kottlerF` — `f(r) = 1 − 2M/r − Λr²/3`; `kottlerF_schwarzschild` / `kottlerF_deSitter` its two limits.
* `kottlerHorizonPoly` — `p(r) = Λr³ − 3r + 6M`.
* `kottlerHorizonPoly_eq` — `f(r)·(−3r) = p(r)`; `kottlerF_zero_iff` — for `r ≠ 0`, `f(r) = 0 ⇔ p(r) = 0`.

Honest scope: the lapse function and the cleared horizon cubic; the explicit horizon radii (cubic roots)
and the full metric are not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits

/-- **The Kottler (Schwarzschild–de Sitter) lapse** `f(r) = 1 − 2M/r − Λr²/3`. -/
def kottlerF (M Λ r : ℝ) : ℝ := 1 - 2 * M / r - Λ * r ^ 2 / 3

/-- **The Kottler horizon cubic** `p(r) = Λr³ − 3r + 6M` (the cleared `f(r) = 0`). -/
def kottlerHorizonPoly (M Λ r : ℝ) : ℝ := Λ * r ^ 3 - 3 * r + 6 * M

/-- **At zero cosmological constant Kottler reduces to Schwarzschild** `f = 1 − 2M/r`. -/
@[zil_level physical_theorem]
theorem kottlerF_schwarzschild (M r : ℝ) : kottlerF M 0 r = schwF M r := by
  simp [kottlerF, schwF]

/-- **At zero mass Kottler reduces to de Sitter**, and the lapse vanishes at the de Sitter (cosmological)
horizon `r = √(3/Λ)`. -/
@[zil_level physical_theorem]
theorem kottlerF_deSitter (Λ : ℝ) (hΛ : 0 < Λ) : kottlerF 0 Λ (deSitterRadius Λ) = 0 := by
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have hr : deSitterRadius Λ ≠ 0 := (deSitterRadius_pos hΛ).ne'
  unfold kottlerF
  rw [deSitterRadius_sq hΛ]
  field_simp
  ring

/-- **The cleared horizon cubic** `f(r)·(−3r) = p(r)` (for `r ≠ 0`). -/
theorem kottlerHorizonPoly_eq (M Λ r : ℝ) (hr : r ≠ 0) :
    kottlerF M Λ r * (-3 * r) = kottlerHorizonPoly M Λ r := by
  unfold kottlerF kottlerHorizonPoly
  field_simp
  ring

/-- **The lapse and the horizon cubic vanish together** `f(r) = 0 ⇔ p(r) = 0` (for `r ≠ 0`). -/
@[zil_level physical_theorem]
theorem kottlerF_zero_iff (M Λ r : ℝ) (hr : r ≠ 0) :
    kottlerF M Λ r = 0 ↔ kottlerHorizonPoly M Λ r = 0 := by
  rw [← kottlerHorizonPoly_eq M Λ r hr]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have h3r : (-3 * r : ℝ) ≠ 0 := by
      simp only [neg_mul, neg_ne_zero]; positivity
    exact (mul_eq_zero.mp h).resolve_right h3r

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons

zil attach kottlerF_schwarzschild where
  formalizes @ "claim:at-zero-cosmological-constant-the-kottler-schwarzschild-de-sitter-lapse-reduces-to-the-schwarzschild-lapse"

zil attach kottlerF_deSitter where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.deSitterRadius_pos",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.deSitterRadius_sq",
  formalizes @ "claim:at-zero-mass-the-kottler-lapse-reduces-to-de-sitter-and-vanishes-at-the-de-sitter-cosmological-horizon-radius-square-root-of-three-over-lambda"

zil attach kottlerF_zero_iff where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerHorizonPoly_eq",
  formalizes @ "claim:the-kottler-lapse-and-its-cleared-horizon-cubic-lambda-r-cubed-minus-three-r-plus-six-m-vanish-together-for-nonzero-radius"

zil_file_contract physlib.schwarzschildDeSitterHorizons where
  promises "The Schwarzschild-de Sitter Kottler black hole horizons, a black hole in a cosmological de Sitter background. The Kottler lapse is one minus two M over r minus Lambda r squared over three, interpolating between Schwarzschild at zero cosmological constant and de Sitter at zero mass, where it vanishes at the de Sitter cosmological horizon radius square root of three over Lambda. The horizons are the positive roots of the cleared cubic Lambda r cubed minus three r plus six M, obtained from the lapse times minus three r; the lapse and the cubic vanish together for nonzero radius. Honest scope: the lapse function and the cleared horizon cubic; the explicit horizon radii, being cubic roots, and the full metric are not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.schwF",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.deSitterRadius"
  ]
  forbids_substitutes [
    "reading the cleared horizon cubic as an explicit solution for the Kottler black-hole and cosmological horizon radii"
  ]
  witnessed_by [
    kottlerF_schwarzschild,
    kottlerF_deSitter,
    kottlerF_zero_iff
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.schwarzschildDeSitterHorizons
