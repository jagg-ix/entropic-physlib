/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit

/-!
# Landauer–Shannon duality

The computation / communication split (`Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit`)
attaches two real annotations to a quantum channel pair: a dissipation rate
`γ ≥ 0` on the computation lane and a phase rate `ω ∈ ℝ` on the communication
lane.  This module provides the unifying synthesis:

* **Lower bound (Landauer floor).**  Any channel pair respecting the
  Landauer bound at temperature `T > 0` has total information cost
  `γ + |ω| ≥ landauerCost T`.
* **Tightness witness.**  There is a channel pair on every backend whose
  total cost is exactly `landauerCost T` — the identity-channel pair with
  `γ = landauerCost T` and `ω = 0`.

The lower bound is a genuine algebraic claim (uses `abs_nonneg` and a
linear-arithmetic chain); the witness saturates it.  Together they make
`landauerCost T` a true infimum of entropic-compatible total info cost,
not a placeholder.


## References

- **Landauer 1961** — *Irreversibility and Heat Generation in Computing*
- **Bennett 1982** — *The thermodynamics of computation — a review*
-/

set_option autoImplicit false

@[expose] public section


open Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit
open Physlib.QuantumMechanics.QuantumChannel Physlib.Thermodynamics.Landauer
namespace Physlib.Thermodynamics.LandauerShannonDuality

open Physlib.QuantumMechanics.QuantumChannel.ComputationCommunicationSplit

variable {backend : QuantumChannelBackend}

/-- **Total information cost** of a channel pair: dissipation rate
on the computation lane plus absolute phase rate on the communication lane.
Both terms are non-negative, so the total is non-negative. -/
def totalInfoCost (R : EntropicChannelPair backend) : ℝ :=
  R.dissipationRate + |R.phaseRate|

@[simp] theorem totalInfoCost_def (R : EntropicChannelPair backend) :
    totalInfoCost R = R.dissipationRate + |R.phaseRate| := rfl

theorem totalInfoCost_nonneg (R : EntropicChannelPair backend) :
    0 ≤ totalInfoCost R := by
  have hd : 0 ≤ R.dissipationRate := R.dissipationRate_nonneg
  have hp : 0 ≤ |R.phaseRate| := abs_nonneg _
  simpa [totalInfoCost] using add_nonneg hd hp

/-- **Landauer–Shannon lower bound.** Any entropic channel pair that respects
the Landauer floor at temperature `T` has total information cost at least
`landauerCost T`. -/
theorem qtmFull_landauer_shannon
    (R : EntropicChannelPair backend) (T : ℝ)
    (h : R.RespectsLandauer T) :
    landauerCost T ≤ totalInfoCost R := by
  have hLB : landauerCost T ≤ R.dissipationRate := h
  have hphase : 0 ≤ |R.phaseRate| := abs_nonneg _
  have := add_le_add hLB hphase
  simpa [totalInfoCost, add_zero] using this

/-- **Saturating witness.** For every backend and every `T ≥ 0`, the
identity-channel pair with dissipation rate `landauerCost T` and zero
phase rate saturates the Landauer–Shannon bound. -/
theorem exists_saturating_pair
    (backend : QuantumChannelBackend) (T : ℝ) (hT : 0 ≤ T) :
    ∃ R : EntropicChannelPair backend, totalInfoCost R = landauerCost T := by
  refine
    ⟨{ pair := QuantumChannelPair.identityPair backend
       , dissipationRate := landauerCost T
       , phaseRate := 0
       , dissipationRate_nonneg := landauerCost_nonneg T hT }, ?_⟩
  simp [totalInfoCost, abs_zero]

/-- **Infimum form of the theorem.** Combining the lower bound and the
saturating witness: among all entropic channel pairs respecting the
Landauer floor at `T > 0`, the infimum of `totalInfoCost` is exactly
`landauerCost T`. (Stated existentially: the bound holds and is met.) -/
theorem landauerCost_is_attained_infimum
    (backend : QuantumChannelBackend) (T : ℝ) (hT : 0 < T) :
    (∀ R : EntropicChannelPair backend, R.RespectsLandauer T →
        landauerCost T ≤ totalInfoCost R) ∧
    (∃ R : EntropicChannelPair backend, R.RespectsLandauer T ∧
        totalInfoCost R = landauerCost T) := by
  refine ⟨fun R h => qtmFull_landauer_shannon R T h, ?_⟩
  refine ⟨{ pair := QuantumChannelPair.identityPair backend
          , dissipationRate := landauerCost T
          , phaseRate := 0
          , dissipationRate_nonneg := landauerCost_nonneg T (le_of_lt hT) }, ?_, ?_⟩
  · -- RespectsLandauer T at this saturating pair
    show landauerCost T ≤ landauerCost T
    exact le_refl _
  · -- totalInfoCost = landauerCost T
    simp [totalInfoCost, abs_zero]

end Physlib.Thermodynamics.LandauerShannonDuality
