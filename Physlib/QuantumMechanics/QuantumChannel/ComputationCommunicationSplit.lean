/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Units.Dimension
public import Physlib.QuantumMechanics.QuantumChannel.Basic
public import Physlib.Thermodynamics.Landauer

/-!
# Computation / communication split of the complex action

The entropic-time framework decomposes the complex action

  `S(γ)  =  S_R(γ)  +  i · S_I(γ)`

into a real part driving *dissipation* (the Landauer / thermodynamic
direction) and an imaginary part driving *coherent phase* (the
Schrödinger / unitary direction).  This module makes that split
quantitative on three layers:

1. **Dimensional layer.** `dimComputation` and `dimCommunication` are
   both the information dimension `I𝓭` in `Physlib.Units.Dimension`; the
   parity `dimComputation = dimCommunication` is then a definitional
   identity, and the *rate* dimension `[I·T⁻¹]` is genuinely computed
   from the abelian-group structure of `Dimension`.
2. **Channel layer.** An entropic channel pair refines the abstract
   `QuantumChannelPair` from `Physlib.QuantumMechanics.QuantumChannel`
   with two real-valued annotations: a dissipation rate `γ ≥ 0` on the
   computation lane and a phase rate `ω ∈ ℝ` on the communication lane.
3. **Thermodynamic-of-computation hook.** The dissipation rate γ at
   temperature `T > 0` is bounded below by `landauerCost T` per bit
   erased per unit time — exposed here as a predicate
   `RespectsLandauer` to be supplied by concrete entropic-time
   instances (Lindblad, non-Hermitian Schrödinger, Matsubara, ...).

The identification `[Re S] = [Im S] = [ℏ]` and the subsequent
`dim_computation_rate = dim_energy` claim are entropic-time postulates
living in `Physlib.Thermodynamics.LandauerShannonDuality`.  This
module provides the dimensional + channel-level scaffold that the postulate
consumes.


## References

- **Bennett 1982** — *The thermodynamics of computation — a review*
- **Landauer 1961** — *Irreversibility and Heat Generation in Computing*
-/

set_option autoImplicit false

@[expose] public section


open Physlib.QuantumMechanics.QuantumChannel Physlib.Thermodynamics.Landauer
namespace Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit

open Dimension

/-! ### Dimensional layer -/

/-- The dimension of the **computation** part of the complex action — the
information dimension `I𝓭` in the entropic-time identification. -/
def dimComputation : Dimension := I𝓭

/-- The dimension of the **communication** part of the complex action — also
the information dimension `I𝓭` in the entropic-time identification. -/
def dimCommunication : Dimension := I𝓭

/-- **Computation / communication dimensional parity.** Both parts of the
complex action include the same physical dimension. -/
theorem dimComputation_eq_dimCommunication :
    dimComputation = dimCommunication := rfl

/-- The dimension of the **computation rate**: information per unit time
`[I · T⁻¹]`. -/
def dimComputationRate : Dimension := dimComputation / T𝓭

/-- The dimension of the **communication rate**: information per unit time
`[I · T⁻¹]`. -/
def dimCommunicationRate : Dimension := dimCommunication / T𝓭

/-- **Computation / communication rate parity.** -/
theorem dimComputationRate_eq_dimCommunicationRate :
    dimComputationRate = dimCommunicationRate := rfl

/-- The information slot of the computation-rate dimension equals `1`. -/
@[simp] theorem dimComputationRate_information :
    dimComputationRate.information = 1 := by
  simp [dimComputationRate, dimComputation]

/-- The time slot of the computation-rate dimension equals `-1`. -/
@[simp] theorem dimComputationRate_time :
    dimComputationRate.time = -1 := by
  simp [dimComputationRate, dimComputation]

/-! ### Channel layer -/

/-- An **entropic channel pair** is a `QuantumChannelPair` together with two
real-valued annotations:

* `dissipationRate ≥ 0` — the rate at which the computation lane
  reduces a free-energy / entropy proxy (the Re(S) direction).
* `phaseRate ∈ ℝ`     — the rate at which the communication lane
  advances coherent phase (the Im(S) direction). -/
structure EntropicChannelPair (backend : QuantumChannelBackend) where
  /-- The underlying channel pair. -/
  pair : QuantumChannelPair backend
  /-- Dissipation rate associated with the computation lane. -/
  dissipationRate : ℝ
  /-- Phase rate associated with the communication lane. -/
  phaseRate : ℝ
  /-- Dissipation is non-negative (Re(S) drives free-energy decrease). -/
  dissipationRate_nonneg : 0 ≤ dissipationRate

namespace EntropicChannelPair

variable {backend : QuantumChannelBackend}

/-- Trivial entropic channel pair: identity channels on both lanes, zero
dissipation and zero phase rate.  Witnesses non-vacuity of the
structure. -/
def trivial (backend : QuantumChannelBackend) : EntropicChannelPair backend where
  pair := QuantumChannelPair.identityPair backend
  dissipationRate := 0
  phaseRate := 0
  dissipationRate_nonneg := le_refl _

/-- **Landauer compatibility.** An entropic channel pair *respects the
Landauer bound at temperature `T`* if its dissipation rate is at least
`landauerCost T` (the per-bit-per-unit-time floor). -/
def RespectsLandauer (R : EntropicChannelPair backend) (T : ℝ) : Prop :=
  landauerCost T ≤ R.dissipationRate

/-- A pair with dissipation rate at least `landauerCost T` respects the
Landauer bound at `T`. -/
theorem respectsLandauer_of_dissipation_ge
    (R : EntropicChannelPair backend) (T : ℝ)
    (h : landauerCost T ≤ R.dissipationRate) : R.RespectsLandauer T :=
  h

/-- **Trivial-region anti-witness.** The trivial entropic pair (zero
dissipation) does NOT respect the Landauer bound at any positive
temperature — its dissipation rate is `0` while `landauerCost T > 0`.
This makes `RespectsLandauer` non-vacuous as a separating predicate. -/
theorem trivial_not_respectsLandauer
    (backend : QuantumChannelBackend) (T : ℝ) (hT : 0 < T) :
    ¬ (trivial backend).RespectsLandauer T := by
  intro h
  have hpos : 0 < landauerCost T := landauerCost_pos T hT
  have h0 : landauerCost T ≤ 0 := h
  exact (lt_irrefl _) (lt_of_lt_of_le hpos h0)

end EntropicChannelPair

end Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit
