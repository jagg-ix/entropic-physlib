/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.LandauerShannonDuality

/-!
# Lean-machine bridge

A "Lean machine" is a physical computer (Lean kernel running on real
hardware) viewed as an entropic-time spacetime region — equivalently, an
`EntropicChannelPair` operating at a definite temperature `T > 0` while
respecting the Landauer floor.

This module formalises that bridge as a single structure
`LeanMachine` and the `leanMachine_safety` theorem: any
`LeanMachine` automatically satisfies the Landauer–Shannon lower
bound on total information cost.  A canonical inhabitant — the
identity-channel pair saturating Landauer at the bridge's temperature —
witnesses non-vacuity.


## References

- **Landauer 1961** — *Irreversibility and Heat Generation in Computing*
- **Bennett 1982** — *The thermodynamics of computation — a review*
-/

set_option autoImplicit false
set_option linter.dupNamespace false

@[expose] public section


open Physlib.Thermodynamics.LandauerShannonDuality
open Physlib.QuantumMechanics.QuantumChannel Physlib.Thermodynamics.Landauer
namespace Physlib.Thermodynamics.LeanMachine

open Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit
open Physlib.Thermodynamics.LandauerShannonDuality

variable {backend : QuantumChannelBackend}

/-- A **Lean-machine bridge**: an entropic channel pair operating at a
definite positive temperature, certified to respect the Landauer floor
at that temperature.

The bridge encapsulates the physical-computer-as-spacetime-region picture:
a Lean kernel running on hardware dissipates at least `landauerCost T`
of free energy per bit erased and contributes phase only via the
communication lane. -/
structure LeanMachine (backend : QuantumChannelBackend) where
  /-- The underlying entropic channel pair. -/
  pair : EntropicChannelPair backend
  /-- Operating temperature of the machine. -/
  temperature : ℝ
  /-- The operating temperature is strictly positive. -/
  temperature_pos : 0 < temperature
  /-- The channel pair respects the Landauer floor at `temperature`. -/
  landauerCompatible : pair.RespectsLandauer temperature

namespace LeanMachine

/-- **Lean-machine safety.** Every Lean-machine bridge automatically
satisfies the Landauer–Shannon lower bound on total information cost.
The "safety" here is thermodynamic: the bridge cannot pretend to a
sub-Landauer info budget. -/
theorem leanMachine_safety (B : LeanMachine backend) :
    landauerCost B.temperature ≤ totalInfoCost B.pair :=
  qtmFull_landauer_shannon B.pair B.temperature B.landauerCompatible

/-- **Canonical bridge.** For every backend and every positive
temperature `T`, the saturating identity-channel pair from
`LandauerShannonDuality` lifts to a `LeanMachine` whose safety
bound is tight. -/
noncomputable def canonical (backend : QuantumChannelBackend) (T : ℝ) (hT : 0 < T) :
    LeanMachine backend where
  pair :=
    { pair := QuantumChannelPair.identityPair backend
    , dissipationRate := landauerCost T
    , phaseRate := 0
    , dissipationRate_nonneg := landauerCost_nonneg T (le_of_lt hT) }
  temperature := T
  temperature_pos := hT
  landauerCompatible := le_refl _

/-- **Saturation at the canonical bridge.** The canonical Lean-machine
bridge meets the Landauer–Shannon bound with equality:
`totalInfoCost = landauerCost T`. -/
theorem canonical_saturates
    (backend : QuantumChannelBackend) (T : ℝ) (hT : 0 < T) :
    totalInfoCost (canonical backend T hT).pair = landauerCost T := by
  simp [canonical, totalInfoCost, abs_zero]

end LeanMachine

end Physlib.Thermodynamics.LeanMachine
