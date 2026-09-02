/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.RelationalTime.SignalDelayCausalReach -/

/-!
# The operational signal-delay law and causal reach

Relational time is established by exchanged signals, whose delay between systems
at operational distance `d` decomposes into a light-travel time and a
processing/interaction delay,

`Δt = d/c + Δt_int`.

The repository formalized the *conventionality* of distant simultaneity
(`SimultaneityConventionShear.synchronyShear`) but never the underlying signal
law.  This module supplies it, together with its two operational consequences:

* the **light-cone lower bound** `d/c ≤ Δt` — no signal arrives before the
  light-travel time (finite causal propagation, operational form); and
* **no synchronization without causal communication**: a pair separated by less
  than the light-travel time (`Δt < d/c`, spacelike) admits *no* signal, so it
  cannot be synchronized by any physical exchange — which is exactly why its
  distant simultaneity is convention-dependent.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.RelationalTime

/-- **The operational signal delay** between two systems at distance `d`, signal
speed `c`, and processing/interaction delay `Δt_int`: `Δt = d/c + Δt_int`. -/
def signalDelay (d c Δt_int : ℝ) : ℝ := d / c + Δt_int

/-- **The light-cone lower bound**: with a non-negative processing delay, the
signal never arrives before the light-travel time `d/c` — the operational form of
finite causal propagation. -/
@[zil_level physical_theorem]
theorem lightTime_le_signalDelay (d c Δt_int : ℝ) (h : 0 ≤ Δt_int) :
    d / c ≤ signalDelay d c Δt_int := by
  unfold signalDelay; linarith

/-- **The delay saturates the light-travel time iff there is no processing delay.** -/
@[zil_level physical_theorem]
theorem signalDelay_eq_lightTime_iff (d c Δt_int : ℝ) :
    signalDelay d c Δt_int = d / c ↔ Δt_int = 0 := by
  unfold signalDelay; constructor <;> intro h <;> linarith

/-- **The delay decomposition**: the signal delay minus the light-travel time is
exactly the processing delay. -/
@[zil_level structural]
theorem signalDelay_sub_lightTime (d c Δt_int : ℝ) :
    signalDelay d c Δt_int - d / c = Δt_int := by
  unfold signalDelay; ring

/-- **Signal delays compose additively along a relayed path**: relaying a signal
through an intermediate adds the leg distances and the leg processing delays. -/
@[zil_level physical_theorem]
theorem signalDelay_relay (d₁ d₂ c Δt₁ Δt₂ : ℝ) :
    signalDelay d₁ c Δt₁ + signalDelay d₂ c Δt₂
      = signalDelay (d₁ + d₂) c (Δt₁ + Δt₂) := by
  unfold signalDelay; ring

/-- **Operational causal reach**: a signal covering distance `d` in elapsed time
`Δt` at speed `c` reaches its target exactly when `d/c ≤ Δt` — the operational
causal-future condition. -/
def canSignalReach (Δt d c : ℝ) : Prop := d / c ≤ Δt

/-- **A physically emitted signal always reaches** at its own delay (its target is
in the operational causal future). -/
@[zil_level physical_theorem]
theorem signalDelay_canSignalReach (d c Δt_int : ℝ) (h : 0 ≤ Δt_int) :
    canSignalReach (signalDelay d c Δt_int) d c :=
  lightTime_le_signalDelay d c Δt_int h

/-- **No synchronization without causal communication**: a pair separated by less
than the light-travel time (`Δt < d/c`, spacelike) admits no signal — it cannot be
synchronized by any physical exchange, so its distant simultaneity is
convention-dependent, not physical. -/
@[zil_level bridge_theorem]
theorem not_canSignalReach_of_spacelike (Δt d c : ℝ) (h : Δt < d / c) :
    ¬ canSignalReach Δt d c := by
  unfold canSignalReach; linarith

end Physlib.QuantumMechanics.RelationalTime

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.RelationalTime

zil attach lightTime_le_signalDelay where
  formalizes @ "claim:a-signal-never-arrives-before-the-light-travel-time-d-over-c-the-operational-form-of-finite-causal-propagation",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.signalDelay"

zil attach not_canSignalReach_of_spacelike where
  formalizes @ "claim:a-spacelike-separated-pair-with-time-separation-less-than-the-light-travel-time-admits-no-signal-so-synchronization-requires-causal-communication",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.canSignalReach",
  caveat @ "claim:distant-simultaneity-of-such-a-pair-is-convention-dependent-per-the-synchrony-shear-not-physically-determined"

zil attach signalDelay_relay where
  formalizes @ "claim:signal-delays-compose-additively-along-a-relayed-path-adding-leg-distances-and-processing-delays"

zil_file_contract physlib.signalDelayCausalReach where
  promises "The operational signal delay between systems at distance d and signal speed c with processing delay Delta t decomposes as d over c plus Delta t, bounded below by the light-travel time d over c with equality iff there is no processing delay, and composing additively along a relayed path. Its causal-reach consequence: a physically emitted signal always reaches its target in operational causal future, while a spacelike-separated pair whose time separation is below the light-travel time admits no signal at all - so synchronization requires causal communication and the distant simultaneity of such a pair is convention-dependent rather than physical."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.RelationalTime.signalDelay",
    "lean:Physlib.QuantumMechanics.RelationalTime.canSignalReach"
  ]
  forbids_substitutes [
    "asserting a signal reaches faster than the light-travel time",
    "reading the operational causal reach as a physical proof of distant simultaneity"
  ]
  witnessed_by [
    lightTime_le_signalDelay,
    signalDelay_eq_lightTime_iff,
    signalDelay_relay,
    signalDelay_canSignalReach,
    not_canSignalReach_of_spacelike
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.signalDelayCausalReach

/- Consolidated from Physlib.QuantumMechanics.RelationalTime.RadarDistanceOperational -/

/-!
# Operational spatial distance from round-trip signal time (radar distance)

Spatial separation is not primitive: it is *reconstructed* from causal relations
among events.  The operational reconstruction is the **radar distance** — bounce a
signal off the distant system and read the round-trip time on a local clock.

Building on the one-way signal-delay law `Δt = d/c + Δt_int`
(`SignalDelayCausalReach.signalDelay`), a zero-processing round trip takes
`T = 2·(d/c)`, so the distance is recovered as

`d = c·T/2`.

This module supplies that inversion (`radarDistance_roundTripTime`,
`roundTripTime_radarDistance`), its strict monotonicity in the clock reading, and
its consistency with the flat Lorentzian interval: each light leg is null,
`−c²(d/c)² + d² = 0`, so the reconstructed distance is exactly the spatial part of
`ds² = −c²dt² + dx²` for a null signal.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.RelationalTime

/-- **The round-trip signal time** over distance `d` at signal speed `c`: two
zero-processing one-way legs, `T = signalDelay d c 0 + signalDelay d c 0`. -/
def roundTripTime (d c : ℝ) : ℝ := signalDelay d c 0 + signalDelay d c 0

/-- The round-trip time is twice the one-way light-travel time, `T = 2·(d/c)`. -/
@[zil_level structural]
theorem roundTripTime_eq (d c : ℝ) : roundTripTime d c = 2 * (d / c) := by
  unfold roundTripTime signalDelay; ring

/-- **The radar distance** reconstructed from a round-trip clock reading `T` at
signal speed `c`: `d = c·T/2`. -/
def radarDistance (T c : ℝ) : ℝ := c * T / 2

/-- **Operational reconstruction of distance** — the radar distance recovers the
true separation from its round-trip signal time: `radarDistance (roundTripTime d) = d`.
This is the operational emergence of spatial separation from purely causal
(clock-and-signal) data. -/
@[zil_level bridge_theorem]
theorem radarDistance_roundTripTime (d c : ℝ) (hc : c ≠ 0) :
    radarDistance (roundTripTime d c) c = d := by
  rw [roundTripTime_eq, radarDistance]; field_simp

/-- **Round trip of the radar distance returns the clock reading** — bouncing a
signal off the radar-reconstructed point takes exactly the original round-trip
time. -/
@[zil_level physical_theorem]
theorem roundTripTime_radarDistance (T c : ℝ) (hc : c ≠ 0) :
    roundTripTime (radarDistance T c) c = T := by
  rw [roundTripTime_eq, radarDistance]; field_simp

/-- **The radar distance is strictly increasing in the round-trip reading** (at
positive signal speed): a longer round trip reconstructs a strictly larger
distance. -/
@[zil_level physical_theorem]
theorem radarDistance_strictMono (c : ℝ) (hc : 0 < c) {T₁ T₂ : ℝ} (h : T₁ < T₂) :
    radarDistance T₁ c < radarDistance T₂ c := by
  unfold radarDistance
  apply div_lt_div_of_pos_right _ (by norm_num : (0:ℝ) < 2)
  exact mul_lt_mul_of_pos_left h hc

/-- **Each light leg is null in the flat interval** — the one-way light-travel
distance `d` and time `d/c` satisfy `−c²(d/c)² + d² = 0`, so the radar-reconstructed
distance is exactly the spatial part of `ds² = −c²dt² + dx²` for a null signal. -/
@[zil_level bridge_theorem]
theorem lightLeg_null_interval (d c : ℝ) (hc : c ≠ 0) :
    -(c ^ 2) * (d / c) ^ 2 + d ^ 2 = 0 := by
  field_simp; ring

end Physlib.QuantumMechanics.RelationalTime

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.RelationalTime

zil attach radarDistance_roundTripTime where
  formalizes @ "claim:spatial-separation-is-operationally-reconstructed-from-the-round-trip-signal-time-as-d-equals-c-times-t-over-two-recovering-the-true-distance",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.signalDelay",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.roundTripTime"

zil attach lightLeg_null_interval where
  formalizes @ "claim:the-radar-reconstructed-distance-is-the-spatial-part-of-the-flat-lorentzian-interval-ds-squared-equals-minus-c-squared-dt-squared-plus-dx-squared-for-a-null-light-leg",
  caveat @ "claim:this-is-the-flat-minkowski-null-condition-for-a-single-light-leg-not-a-curved-effective-metric-geodesic-distance"

zil_file_contract physlib.radarDistanceOperational where
  promises "Spatial separation is operationally reconstructed from causal data: bouncing a signal off a distant system, the zero-processing round-trip time is twice the one-way light-travel time T = 2 d over c from the signal-delay law, and inverting gives the radar distance d = c T over 2. This reconstruction recovers the true separation, its round trip returns the original clock reading, it is strictly increasing in the round-trip reading, and it is consistent with the flat Lorentzian interval since each light leg is null, minus c squared times (d over c) squared plus d squared equals zero - the spatial part of ds squared = minus c squared dt squared plus dx squared for a null signal."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.RelationalTime.signalDelay",
    "lean:Physlib.QuantumMechanics.RelationalTime.roundTripTime",
    "lean:Physlib.QuantumMechanics.RelationalTime.radarDistance"
  ]
  forbids_substitutes [
    "reading the flat null-leg condition as a curved effective-metric geodesic distance",
    "asserting distance is primitive rather than reconstructed from round-trip signal time"
  ]
  witnessed_by [
    roundTripTime_eq,
    radarDistance_roundTripTime,
    roundTripTime_radarDistance,
    radarDistance_strictMono,
    lightLeg_null_interval
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.radarDistanceOperational

