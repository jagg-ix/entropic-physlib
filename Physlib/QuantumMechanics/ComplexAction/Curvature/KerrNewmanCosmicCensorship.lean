/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons
meta import Zil

/-!
# Kerr–Newman cosmic censorship and extremality classification

The Kerr–Newman horizon structure classifies by the sign of `M² − a² − Q²` — the rotating generalization
of the Reissner–Nordström `M² − Q²`:

* **sub-extremal** `a² + Q² < M²`: two distinct horizons `r_- < r_+`;
* **extremal** `a² + Q² = M²`: the horizons coincide at `r = M`;
* **super-extremal** `a² + Q² > M²`: `Δ(r) = r² − 2Mr + (a² + Q²)` has no real root — no horizon, a naked
  singularity.

The bound `a² + Q² ≤ M²` is the weak-cosmic-censorship boundary: for a black hole to exist the spin and
charge together cannot exceed the mass (`|J| ≤ M²` in the uncharged Kerr limit).

* `knInnerHorizon_lt_outerHorizon` — `a² + Q² < M² ⇒ r_- < r_+`.
* `knInnerHorizon_nonneg` — `0 ≤ M`, `a² + Q² ≤ M² ⇒ 0 ≤ r_-`.
* `knNoHorizonOfNaked` — `M² < a² + Q² ⇒ Δ(r) ≠ 0` for every `r`.

Honest scope: the horizon-polynomial discriminant algebra; the global cosmic-censorship conjecture is not
addressed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanCosmicCensorship

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons

/-- **Sub-extremal ⇒ distinct horizons** `a² + Q² < M² ⇒ r_- < r_+`. -/
@[zil_level physical_theorem]
theorem knInnerHorizon_lt_outerHorizon (M a Q : ℝ) (h : a ^ 2 + Q ^ 2 < M ^ 2) :
    knInnerHorizon M a Q < knOuterHorizon M a Q := by
  unfold knInnerHorizon knOuterHorizon
  have hpos : 0 < Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) := Real.sqrt_pos.mpr (by linarith)
  linarith

/-- **The inner horizon is non-negative** `0 ≤ M`, `a² + Q² ≤ M² ⇒ 0 ≤ r_-`. -/
@[zil_level physical_theorem]
theorem knInnerHorizon_nonneg (M a Q : ℝ) (hM : 0 ≤ M) (h : a ^ 2 + Q ^ 2 ≤ M ^ 2) :
    0 ≤ knInnerHorizon M a Q := by
  unfold knInnerHorizon
  have hle : Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) ≤ M := by
    have hs := Real.sqrt_le_sqrt (show M ^ 2 - a ^ 2 - Q ^ 2 ≤ M ^ 2 from by
      nlinarith [sq_nonneg a, sq_nonneg Q])
    rwa [Real.sqrt_sq hM] at hs
  linarith

/-- **The naked-singularity threshold** `M² < a² + Q² ⇒ Δ(r) ≠ 0` for every `r`: super-extremal
Kerr–Newman has no horizon, since `Δ(r) = (r − M)² + (a² + Q² − M²)` is a sum of a square and a positive
constant. -/
@[zil_level physical_theorem]
theorem knNoHorizonOfNaked (M a Q : ℝ) (h : M ^ 2 < a ^ 2 + Q ^ 2) (r : ℝ) :
    knDelta M a Q r ≠ 0 := by
  unfold knDelta
  rw [show r ^ 2 - 2 * M * r + (a ^ 2 + Q ^ 2) = (r - M) ^ 2 + (a ^ 2 + Q ^ 2 - M ^ 2) from by ring]
  have h1 : (0 : ℝ) ≤ (r - M) ^ 2 := sq_nonneg _
  have hpos : 0 < (r - M) ^ 2 + (a ^ 2 + Q ^ 2 - M ^ 2) := by linarith
  exact hpos.ne'

end Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanCosmicCensorship

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanCosmicCensorship

zil attach knInnerHorizon_lt_outerHorizon where
  supported_by @ "lean:HermitianMat.sqrt_pos",
  formalizes @ "claim:sub-extremal-kerr-newman-spin-squared-plus-charge-squared-less-than-mass-squared-has-two-distinct-horizons-the-inner-horizon-strictly-below-the-outer-horizon"

zil attach knInnerHorizon_nonneg where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  supported_by @ "lean:HermitianMat.sqrt_sq",
  formalizes @ "claim:the-kerr-newman-inner-horizon-is-non-negative-for-non-negative-mass-and-spin-squared-plus-charge-squared-at-most-mass-squared"

zil attach knNoHorizonOfNaked where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:super-extremal-kerr-newman-mass-squared-less-than-spin-squared-plus-charge-squared-has-no-horizon-the-horizon-function-has-no-real-root-a-naked-singularity"

zil_file_contract physlib.kerrNewmanCosmicCensorship where
  promises "The Kerr-Newman cosmic censorship and extremality classification by the sign of mass-squared minus spin-squared minus charge-squared, the rotating generalization of the Reissner-Nordstrom classification. Sub-extremal spin-squared plus charge-squared less than mass-squared has two distinct horizons, the inner horizon strictly below the outer horizon. The inner horizon is non-negative for non-negative mass and spin-squared plus charge-squared at most mass-squared. Super-extremal mass-squared less than spin-squared plus charge-squared has no horizon: the horizon function has no real root, being a sum of a square and a positive constant, a naked singularity. The bound spin-squared plus charge-squared at most mass-squared is the weak-cosmic-censorship boundary. Honest scope: the horizon-polynomial discriminant algebra; the global cosmic-censorship conjecture is not addressed."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knOuterHorizon",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knDelta"
  ]
  forbids_substitutes [
    "reading the horizon-polynomial discriminant algebra as a proof of the global weak cosmic censorship conjecture for rotating charged collapse"
  ]
  witnessed_by [
    knInnerHorizon_lt_outerHorizon,
    knInnerHorizon_nonneg,
    knNoHorizonOfNaked
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.kerrNewmanCosmicCensorship
