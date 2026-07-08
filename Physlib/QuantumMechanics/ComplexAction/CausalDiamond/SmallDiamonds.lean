/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

/-!
# Small diamonds and Minkowski space (Jacobson–Visser §5.2)

In the small-radius limit `R ≪ L` (equivalently `L → ∞`, the flat/Minkowski limit) the (A)dS causal
diamond becomes a flat-space diamond. This file formalizes that limit for the geometric quantities of
`CausalDiamond.AdS`:

* `sqrtFactor_tendsto_one` — `√(1−(R/L)²) → 1` as `L → ∞` (the relativistic factor trivializes);
* `adsExtrinsicK_tendsto_flat` — `k = (d-2)√(1−(R/L)²)/R → (d-2)/R`, the flat extrinsic curvature
  (Jacobson–Visser Eq. 5.5 leading order);
* `thermoVolume_eq_dsq` — the flat thermodynamic volume `V_ζ^flat = κΩR^d/(d²−1)` (Eq. 5.6 leading
  term, since `(d-1)(d+1) = d²−1`);
* `confKillingFlat_*` — the flat conformal Killing vector `ζ^flat = (1/2R)[(R²−t²−r²)∂_t − 2tr∂_r]`
  (Eq. 5.8, the `L → ∞` limit of Eq. 2.6) is the `CausalDiamond.Construction` field normalized by
  `1/2R`, and vanishes at the vertices and the edge `∂Σ`.

So as `R/L → 0` the first law of causal diamonds reduces to the Minkowski first law of [Jacobson '15]
(Eq. 5.7), and the diamond's conformal isometry becomes the flat one (Eq. 5.8).

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, §5.2, Eqs. 5.5–5.8. This development:
  `CausalDiamond.AdS`, `CausalDiamond.Area`, `CausalDiamond.Construction`.

No new axioms.
-/

set_option autoImplicit false

open Real Filter Topology

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.SmallDiamonds

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

/-! ## §A — the flat (`L → ∞`) limit of the relativistic factor and `k` -/

/-- **The relativistic factor trivializes in the flat limit** `√(1−(R/L)²) → 1` as `L → ∞`. -/
theorem sqrtFactor_tendsto_one (R : ℝ) :
    Tendsto (fun L => sqrtFactor L R) atTop (𝓝 1) := by
  have h0 : Tendsto (fun L : ℝ => R / L) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have h1 : Tendsto (fun L : ℝ => 1 - (R / L) ^ 2) atTop (𝓝 1) := by
    have h2 := h0.pow 2
    simpa using Tendsto.const_sub (1 : ℝ) h2
  have h3 := (Real.continuous_sqrt.tendsto 1).comp h1
  simpa [sqrtFactor, Function.comp_def, Real.sqrt_one] using h3

/-- **The extrinsic curvature tends to its flat value** `k = (d-2)√(1−(R/L)²)/R → (d-2)/R` as
`L → ∞` (Jacobson–Visser Eq. 5.5, leading order): the small diamond is Minkowskian. -/
theorem adsExtrinsicK_tendsto_flat (d R : ℝ) (hR : R ≠ 0) :
    Tendsto (fun L => adsExtrinsicK d R (sqrtFactor L R)) atTop (𝓝 (extrinsicK d R)) := by
  have h : Tendsto (fun L => (d - 2) * sqrtFactor L R / R) atTop (𝓝 ((d - 2) * 1 / R)) :=
    (Tendsto.const_mul (d - 2) (sqrtFactor_tendsto_one R)).div_const R
  simpa [adsExtrinsicK, extrinsicK] using h

/-! ## §B — the flat thermodynamic volume (Eq. 5.6 leading term) -/

/-- **The flat thermodynamic volume** `V_ζ^flat = κΩR^d/(d²−1)` (Jacobson–Visser Eq. 5.6, leading
term): the `CausalDiamond.Area.thermoVolume` rewritten with `(d-1)(d+1) = d²−1`. -/
theorem thermoVolume_eq_dsq (κ Ω d R : ℝ) :
    thermoVolume κ Ω d R = κ * Ω * R ^ d / (d ^ 2 - 1) := by
  unfold thermoVolume
  rw [show (d - 1) * (d + 1) = d ^ 2 - 1 by ring]

/-! ## §C — the flat conformal Killing vector (Eq. 5.8) -/

/-- **Time component of the flat conformal Killing vector** `ζ^flat,t = (R²−t²−r²)/(2R)`
(Jacobson–Visser Eq. 5.8): the `CausalDiamond.Construction` field normalized by `1/2R`. -/
def confKillingFlatTime (R t r : ℝ) : ℝ := confKillingTime R t r / (2 * R)

/-- **Radial component of the flat conformal Killing vector** `ζ^flat,r = −2tr/(2R) = −tr/R`. -/
def confKillingFlatRad (R t r : ℝ) : ℝ := confKillingRad R t r / (2 * R)

/-- **Eq. 5.8 explicitly** `ζ^flat,t = (R²−t²−r²)/(2R)`. -/
theorem confKillingFlatTime_eq (R t r : ℝ) :
    confKillingFlatTime R t r = (R ^ 2 - t ^ 2 - r ^ 2) / (2 * R) := by
  rw [confKillingFlatTime, confKillingTime]

/-- **The flat conformal Killing vector vanishes on the edge `∂Σ`** `= (0, R)` (the bifurcation
surface fixed by the conformal flow), inherited from the construction. -/
theorem confKillingFlat_vanishes_edge (R : ℝ) :
    confKillingFlatTime R 0 R = 0 ∧ confKillingFlatRad R 0 R = 0 := by
  obtain ⟨ht, hr⟩ := confKilling_vanishes_edge R
  rw [confKillingFlatTime, confKillingFlatRad, ht, hr]
  simp

/-- **The flat conformal Killing vector vanishes at the two vertices** `(∓R, 0)`. -/
theorem confKillingFlat_vanishes_vertices (R : ℝ) :
    (confKillingFlatTime R R 0 = 0 ∧ confKillingFlatRad R R 0 = 0) ∧
    (confKillingFlatTime R (-R) 0 = 0 ∧ confKillingFlatRad R (-R) 0 = 0) := by
  obtain ⟨⟨ht1, hr1⟩, ht2, hr2⟩ := confKilling_vanishes_vertices R
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [confKillingFlatTime, confKillingFlatRad, ht1, hr1, ht2, hr2, zero_div]

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.SmallDiamonds

end
