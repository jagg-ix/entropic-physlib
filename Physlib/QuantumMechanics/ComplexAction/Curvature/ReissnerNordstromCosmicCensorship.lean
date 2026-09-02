/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
meta import Zil

/-!
# Reissner–Nordström cosmic censorship and extremality classification

The Reissner–Nordström horizon structure classifies by the sign of `M² − Q²`:

* **sub-extremal** `Q² < M²`: two distinct horizons `r_- < r_+` — a regular black hole;
* **extremal** `Q² = M²`: the horizons coincide at `r_+ = r_- = M` (`extremal_horizons_eq`);
* **super-extremal** `Q² > M²`: the horizon polynomial `r² − 2Mr + Q²` has **no real root**, so no horizon
  forms and the singularity is naked.

This module records the sub-extremal distinctness, the non-negativity of the inner horizon (the horizon
sits at `r ≥ 0`), and the naked-singularity threshold — the weak-cosmic-censorship boundary `|Q| ≤ M`.

* `innerHorizon_lt_outerHorizon` — `Q² < M² ⇒ r_- < r_+`.
* `innerHorizon_nonneg` — `0 ≤ M`, `Q² ≤ M² ⇒ 0 ≤ r_-`.
* `no_horizon_of_naked` — `M² < Q² ⇒ r² − 2Mr + Q² ≠ 0` for every `r` (no horizon).

Honest scope: this is the horizon-polynomial discriminant algebra; the global cosmic-censorship
conjecture (that generic collapse does not produce naked singularities) is not addressed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

/-- **Sub-extremal ⇒ distinct horizons** `Q² < M² ⇒ r_- < r_+`. -/
@[zil_level physical_theorem]
theorem innerHorizon_lt_outerHorizon (M Q : ℝ) (h : Q ^ 2 < M ^ 2) :
    innerHorizon M Q < outerHorizon M Q := by
  unfold innerHorizon outerHorizon
  have hpos : 0 < Real.sqrt (M ^ 2 - Q ^ 2) := Real.sqrt_pos.mpr (by linarith)
  linarith

/-- **The inner horizon is non-negative** `0 ≤ M`, `Q² ≤ M² ⇒ 0 ≤ r_-` — the horizon sits at `r ≥ 0`. -/
@[zil_level physical_theorem]
theorem innerHorizon_nonneg (M Q : ℝ) (hM : 0 ≤ M) (h : Q ^ 2 ≤ M ^ 2) :
    0 ≤ innerHorizon M Q := by
  unfold innerHorizon
  have hle : Real.sqrt (M ^ 2 - Q ^ 2) ≤ M := by
    have hs := Real.sqrt_le_sqrt (show M ^ 2 - Q ^ 2 ≤ M ^ 2 from by linarith [sq_nonneg Q])
    rwa [Real.sqrt_sq hM] at hs
  linarith

/-- **The naked-singularity threshold** `M² < Q² ⇒ r² − 2Mr + Q² ≠ 0` for every `r`: super-extremal
Reissner–Nordström has no horizon, since the horizon polynomial `= (r − M)² + (Q² − M²)` is a sum of a
square and a positive constant. -/
@[zil_level physical_theorem]
theorem no_horizon_of_naked (M Q : ℝ) (h : M ^ 2 < Q ^ 2) (r : ℝ) :
    r ^ 2 - 2 * M * r + Q ^ 2 ≠ 0 := by
  rw [show r ^ 2 - 2 * M * r + Q ^ 2 = (r - M) ^ 2 + (Q ^ 2 - M ^ 2) from by ring]
  have h1 : (0 : ℝ) ≤ (r - M) ^ 2 := sq_nonneg _
  have hpos : 0 < (r - M) ^ 2 + (Q ^ 2 - M ^ 2) := by linarith
  exact hpos.ne'

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship

zil attach innerHorizon_lt_outerHorizon where
  supported_by @ "lean:HermitianMat.sqrt_pos",
  formalizes @ "claim:sub-extremal-reissner-nordstrom-q-squared-less-than-m-squared-has-two-distinct-horizons-the-inner-horizon-strictly-below-the-outer-horizon"

zil attach innerHorizon_nonneg where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  supported_by @ "lean:HermitianMat.sqrt_sq",
  formalizes @ "claim:the-reissner-nordstrom-inner-horizon-is-non-negative-for-non-negative-mass-and-q-squared-at-most-m-squared-so-the-horizon-sits-at-non-negative-radius"

zil attach no_horizon_of_naked where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:super-extremal-reissner-nordstrom-m-squared-less-than-q-squared-has-no-horizon-the-horizon-polynomial-has-no-real-root-being-a-sum-of-a-square-and-a-positive-constant-a-naked-singularity"

zil_file_contract physlib.reissnerNordstromCosmicCensorship where
  promises "The Reissner-Nordstrom cosmic censorship and extremality classification by the sign of M squared minus Q squared. Sub-extremal Q squared less than M squared has two distinct horizons, the inner horizon strictly below the outer horizon. The inner horizon is non-negative for non-negative mass and Q squared at most M squared, so the horizon sits at non-negative radius. Super-extremal M squared less than Q squared has no horizon: the horizon polynomial r squared minus two M r plus Q squared has no real root, being a sum of a square and a positive constant, a naked singularity. This is the weak-cosmic-censorship boundary absolute value of Q at most M. Honest scope: this is the horizon-polynomial discriminant algebra; the global cosmic-censorship conjecture that generic collapse does not produce naked singularities is not addressed."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.outerHorizon",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.innerHorizon"
  ]
  forbids_substitutes [
    "reading the horizon-polynomial discriminant algebra as a proof of the global weak cosmic censorship conjecture for gravitational collapse"
  ]
  witnessed_by [
    innerHorizon_lt_outerHorizon,
    innerHorizon_nonneg,
    no_horizon_of_naked
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromCosmicCensorship
