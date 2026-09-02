/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai
meta import Zil

/-!
# The Schwarzschild–de Sitter horizon-existence bound

The horizon cubic `p(r) = Λr³ − 3r + 6M` has a positive leading coefficient and its local minimum sits at
the Nariai radius `r₀ = 1/√Λ`, with value `p(r₀) = 6M − 2r₀`.  Two distinct positive horizons (a
black-hole horizon below `r₀` and a cosmological horizon above) exist exactly when this local minimum is
**negative**, i.e. when `9ΛM² < 1` — the sub-Nariai regime.  At `9ΛM² = 1` the horizons merge (Nariai),
and for `9ΛM² > 1` the local minimum is positive and there is no black-hole horizon.

* `nariai_localMin_neg_iff` — `p(r₀) < 0 ⇔ 9ΛM² < 1` (two horizons exist).
* `nariai_localMin_pos_iff` — `p(r₀) > 0 ⇔ 9ΛM² > 1` (no black-hole horizon).

Honest scope: the sign of the cubic's local-minimum value; the full root-count via the intermediate value
theorem is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizonBound

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai

/-- **Sub-Nariai ⇒ two horizons**: the horizon cubic's local minimum is negative exactly when
`9ΛM² < 1`. -/
@[zil_level physical_theorem]
theorem nariai_localMin_neg_iff (M Λ : ℝ) (hΛ : 0 < Λ) (hM : 0 < M) :
    kottlerHorizonPoly M Λ (nariaiRadius Λ) < 0 ↔ 9 * Λ * M ^ 2 < 1 := by
  rw [kottlerHorizonPoly_nariai_value M Λ hΛ]
  have hr := nariaiRadius_pos hΛ
  have hΛr : Λ * nariaiRadius Λ ^ 2 = 1 := by
    rw [nariaiRadius_sq hΛ, mul_one_div, div_self hΛ.ne']
  constructor
  · intro h
    have hprod : (0 : ℝ) < Λ * (nariaiRadius Λ - 3 * M) * (nariaiRadius Λ + 3 * M) :=
      mul_pos (mul_pos hΛ (by linarith)) (by linarith)
    nlinarith [hprod, hΛr]
  · intro h
    have hr2 : 9 * M ^ 2 < nariaiRadius Λ ^ 2 := by nlinarith [h, hΛr, hΛ]
    have h3 : 3 * M < nariaiRadius Λ := by nlinarith [hr2, hr, hM]
    linarith

/-- **Super-Nariai ⇒ no black-hole horizon**: the horizon cubic's local minimum is positive exactly when
`9ΛM² > 1`. -/
@[zil_level physical_theorem]
theorem nariai_localMin_pos_iff (M Λ : ℝ) (hΛ : 0 < Λ) (hM : 0 < M) :
    0 < kottlerHorizonPoly M Λ (nariaiRadius Λ) ↔ 1 < 9 * Λ * M ^ 2 := by
  rw [kottlerHorizonPoly_nariai_value M Λ hΛ]
  have hr := nariaiRadius_pos hΛ
  have hΛr : Λ * nariaiRadius Λ ^ 2 = 1 := by
    rw [nariaiRadius_sq hΛ, mul_one_div, div_self hΛ.ne']
  constructor
  · intro h
    have h3 : nariaiRadius Λ < 3 * M := by linarith
    have hprod : (0 : ℝ) < Λ * (3 * M - nariaiRadius Λ) * (3 * M + nariaiRadius Λ) :=
      mul_pos (mul_pos hΛ (by linarith)) (by linarith)
    nlinarith [hprod, hΛr]
  · intro h
    have hr2 : nariaiRadius Λ ^ 2 < 9 * M ^ 2 := by nlinarith [h, hΛr, hΛ]
    have h3 : nariaiRadius Λ < 3 * M := by nlinarith [hr2, hr, hM]
    linarith

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizonBound

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizonBound

zil attach nariai_localMin_neg_iff where
  supported_by @ "lean:kottlerHorizonPoly_nariai_value",
  formalizes @ "claim:the-schwarzschild-de-sitter-horizon-cubic-local-minimum-is-negative-exactly-when-nine-lambda-m-squared-is-less-than-one-the-sub-nariai-regime-with-two-distinct-horizons"

zil attach nariai_localMin_pos_iff where
  supported_by @ "lean:kottlerHorizonPoly_nariai_value",
  formalizes @ "claim:the-schwarzschild-de-sitter-horizon-cubic-local-minimum-is-positive-exactly-when-nine-lambda-m-squared-exceeds-one-the-super-nariai-regime-with-no-black-hole-horizon"

zil_file_contract physlib.schwarzschildDeSitterHorizonBound where
  promises "The Schwarzschild-de Sitter horizon-existence bound. The horizon cubic Lambda r cubed minus three r plus six M has a positive leading coefficient with local minimum at the Nariai radius, value six M minus twice the Nariai radius. Two distinct positive horizons, a black-hole horizon below the Nariai radius and a cosmological horizon above, exist exactly when this local minimum is negative, that is when nine Lambda M squared is less than one, the sub-Nariai regime; at nine Lambda M squared equals one the horizons merge, and for nine Lambda M squared greater than one the local minimum is positive and there is no black-hole horizon. Honest scope: the sign of the cubic's local-minimum value; the full root-count via the intermediate value theorem is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerHorizonPoly",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariaiRadius"
  ]
  forbids_substitutes [
    "reading the local-minimum sign as a full intermediate-value-theorem root count of the horizon cubic"
  ]
  witnessed_by [
    nariai_localMin_neg_iff,
    nariai_localMin_pos_iff
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.schwarzschildDeSitterHorizonBound
