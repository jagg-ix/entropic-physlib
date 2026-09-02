/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.SignalDelayCausalReach
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell
meta import Zil

/-!
# The radar light cone and the Einstein Equivalence Principle

The operational radar distance `d = c·T/2` (`RadarDistanceOperational`) is
reconstructed from a light signal whose one-way spacetime displacement has time
component `c·Δt = c·(signalDelay d c 0) = c·(d/c) = d` and space component `d`.
That light leg is a **null** vector of the Minkowski form.

This module links the causal-emergence spine (`signalDelay` → `radarDistance`) to
the Einstein Equivalence Principle already instantiated in the Compton-clock arc.
The Local Lorentz Invariance pillar of the EEP is the theorem
`PoincareCasimirMassShell.poincareRestMassSq_boost_invariant` — the Poincaré rest
mass `μ² = η_{ab}p^a p^b` is a boost scalar (boost = inertial gauge, only rest mass
physical); the same statement carries the tetrad-gauge form
`EquivalencePrincipleMassShell.fourMomentum_norm_tetrad_gauge_invariant` and the
Nagao–Nielsen convergence-cone form `NagaoNielsenMassShellCone.nnLorentzForm`.

Here the radar light leg is shown to be a massless (`μ² = 0`) mass-shell vector
whose null character is **boost-invariant** (`radarLightLeg_massless_boost_invariant`),
sitting exactly on the boundary of the Nagao–Nielsen convergence cone
(`radarLightLeg_nnLorentzForm_zero`, `not_nnConverges_radarLightLeg`).  So the
frame-covariance of the operational distance rests on the very Lorentz-invariant
light-cone structure the EEP asserts: `radarDistance_lightLeg_null` closes the
loop back onto the reconstructed distance.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell

namespace Physlib.QuantumMechanics.RelationalTime

/-- **The time component `c·Δt` of the radar light leg** over distance `d` at
signal speed `c`: `c` times the one-way light-travel time `signalDelay d c 0`. -/
def radarLightLegCT (d c : ℝ) : ℝ := c * signalDelay d c 0

/-- The light-leg time component equals the distance, `c·(d/c) = d`: a light
signal covers `ct = d` while crossing spatial separation `d` (the null relation). -/
@[zil_level structural]
theorem radarLightLegCT_eq_distance (d c : ℝ) (hc : c ≠ 0) :
    radarLightLegCT d c = d := by
  unfold radarLightLegCT signalDelay; rw [add_zero]; field_simp

/-- **The radar light leg is a massless mass-shell vector** — its Poincaré rest
mass vanishes, `μ²(c·Δt, d, 0, 0) = 0`.  The signal is null, the `m = 0` point of
the Compton mass-shell. -/
@[zil_level physical_theorem]
theorem radarLightLeg_restMassSq_zero (d c : ℝ) (hc : c ≠ 0) :
    poincareRestMassSq (radarLightLegCT d c) d 0 0 = 0 := by
  rw [radarLightLegCT_eq_distance d c hc]
  unfold poincareRestMassSq; ring

/-- **Local Lorentz Invariance of the radar light cone (EEP).**  Under a boost of
rapidity `θ` the radar light leg stays null: its Poincaré rest mass — the
boost-invariant Casimir of `poincareRestMassSq_boost_invariant` — remains `0` in
every inertial frame.  This is the Einstein-Equivalence-Principle content that
makes the operational distance frame-covariant: all inertial observers agree the
signal is a null light-cone vector. -/
@[zil_level bridge_theorem]
theorem radarLightLeg_massless_boost_invariant (d c θ : ℝ) (hc : c ≠ 0) :
    poincareRestMassSq
        (radarLightLegCT d c * Real.cosh θ - d * Real.sinh θ)
        (d * Real.cosh θ - radarLightLegCT d c * Real.sinh θ) 0 0 = 0 := by
  rw [poincareRestMassSq_boost_invariant]
  exact radarLightLeg_restMassSq_zero d c hc

/-- **The radar light leg as a complex coordinate** `q = c·Δt + i·d`, in the
Nagao–Nielsen steepest-descent plane. -/
def radarLightLegComplex (d c : ℝ) : ℂ := ⟨radarLightLegCT d c, d⟩

/-- **The radar light leg sits on the Nagao–Nielsen convergence-cone boundary** —
its `(1,1)` Minkowski form vanishes, `(Re q)² − (Im q)² = 0`.  This is the light
cone `|θ| = π/4` bounding the NN steepest-descent contour: the same null structure,
now on the complex-coordinate plane. -/
@[zil_level bridge_theorem]
theorem radarLightLeg_nnLorentzForm_zero (d c : ℝ) (hc : c ≠ 0) :
    nnLorentzForm (radarLightLegComplex d c) = 0 := by
  rw [nnLorentzForm_is_first_casimir]
  exact radarLightLeg_restMassSq_zero d c hc

/-- **The radar light leg does not lie in the open NN convergence cone** — being on
the boundary (`nnLorentzForm = 0`), it is not strictly convergent (`0 < nnLorentzForm`
fails).  The light cone separates the convergent (timelike, massive) interior from
the exterior. -/
@[zil_level physical_theorem]
theorem not_nnConverges_radarLightLeg (d c : ℝ) (hc : c ≠ 0) :
    ¬ nnConverges (radarLightLegComplex d c) := by
  unfold nnConverges
  rw [radarLightLeg_nnLorentzForm_zero d c hc]
  exact lt_irrefl 0

/-- **Closing the loop onto the reconstructed distance** — the light leg over the
radar-reconstructed distance `radarDistance T c` is null.  The distance recovered
from a round-trip clock reading rides on a boost-invariant null light-cone vector,
grounding the operational reconstruction in the EEP's Local Lorentz Invariance. -/
@[zil_level bridge_theorem]
theorem radarDistance_lightLeg_null (T c : ℝ) (hc : c ≠ 0) :
    poincareRestMassSq (radarLightLegCT (radarDistance T c) c) (radarDistance T c) 0 0 = 0 :=
  radarLightLeg_restMassSq_zero (radarDistance T c) c hc

end Physlib.QuantumMechanics.RelationalTime

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.RelationalTime

zil attach radarLightLeg_massless_boost_invariant where
  formalizes @ "claim:the-radar-light-leg-is-a-boost-invariant-null-mass-shell-vector-so-local-lorentz-invariance-the-einstein-equivalence-principle-makes-the-operational-radar-distance-frame-covariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell.poincareRestMassSq_boost_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.signalDelay",
  caveat @ "claim:this-is-the-one-plus-one-massless-limit-of-the-poincare-rest-mass-casimir-not-the-full-three-plus-one-tetrad-gauge-orbit"

zil attach radarLightLeg_nnLorentzForm_zero where
  formalizes @ "claim:the-radar-light-leg-sits-on-the-nagao-nielsen-convergence-cone-boundary-with-vanishing-one-one-minkowski-form-the-light-cone-theta-equals-pi-over-four",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell.nnLorentzForm_is_first_casimir"

zil attach radarDistance_lightLeg_null where
  formalizes @ "claim:the-light-leg-over-the-radar-reconstructed-distance-is-a-null-mass-shell-vector-closing-the-loop-onto-the-operational-distance",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.radarDistance"

zil_file_contract physlib.radarLightConeEquivalencePrinciple where
  promises "The operational radar distance is linked to the Einstein Equivalence Principle already instantiated in the Compton-clock arc. The radar light leg, whose time component c times the signal delay equals the spatial separation d, is a massless mass-shell vector with zero Poincare rest mass. Its null character is boost-invariant by poincareRestMassSq_boost_invariant - the Local Lorentz Invariance pillar of the EEP, boost as inertial gauge with only rest mass physical - so the operational distance is frame-covariant. The same null vector sits on the boundary of the Nagao-Nielsen convergence cone via nnLorentzForm_is_first_casimir, and the loop closes onto the radar-reconstructed distance."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.RelationalTime.radarLightLegCT",
    "lean:Physlib.QuantumMechanics.RelationalTime.signalDelay",
    "lean:Physlib.QuantumMechanics.RelationalTime.radarDistance",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell.poincareRestMassSq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm"
  ]
  forbids_substitutes [
    "reading the one-plus-one massless limit as the full three-plus-one tetrad-gauge Lorentz orbit",
    "claiming the light leg lies inside the open convergence cone rather than on its boundary"
  ]
  witnessed_by [
    radarLightLegCT_eq_distance,
    radarLightLeg_restMassSq_zero,
    radarLightLeg_massless_boost_invariant,
    radarLightLeg_nnLorentzForm_zero,
    not_nnConverges_radarLightLeg,
    radarDistance_lightLeg_null
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.radarLightConeEquivalencePrinciple
