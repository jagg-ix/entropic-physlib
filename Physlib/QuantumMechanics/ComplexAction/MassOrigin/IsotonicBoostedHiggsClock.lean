/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IsotonicRapidityComptonClock
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins

/-!
# The isotonic rapidity boost acts on the Higgs clock: closing the arc

Two threads meet here. `IsotonicRapidityComptonClock` showed the isotonic hyperbolic factor `√(ξ²+1) = cosh η` is
the **Lorentz/de Broglie boost** `γ` of a Compton clock. `HiggsClockThreeOrigins` showed the three Higgs-free mass
origins (Yukawa, horizon-entropy, Chern–Simons) are **one internal Compton clock** `higgsClockFrequency`. Composing
them: the single isotonic Lorentz factor `γ = √(ξ²+1)` boosts that one clock, and — because the clock frequency has
three equivalent closed forms — it boosts all three mass-origin forms **uniformly**.

* **`isotonic_boosts_higgs_clock`** — `ω_dB(γ · yukawaMass · c²) = γ · higgsClockFrequency`: the isotonic boost of
  the Higgs clock.
* **`isotonic_boosts_three_origins`** — under the same coincidence of the three masses, the boosted de Broglie
  frequency equals `γ · c³Ȧ_H/(4Għ)` (boosted horizon form) and `γ · comptonFrequency (topologicalMass dj)`
  (boosted topological form).

**Honest layering.** Exact composition of `IsotonicRapidityComptonClock.sqrt_sq_add_one_boosts_compton` (the boost)
with `HiggsClockThreeOrigins.higgs_clock_three_origins` (the three-form clock); no new physical input beyond the
two source modules. This closes the isotonic → rapidity → clock → mass-origin arc: the mechanical isotonic geometry
supplies the boost `γ`, the mass unification supplies the clock `ω`, and the boosted clock `γω` is the de Broglie
frequency common to all three origins.

## References

* Composes `IsotonicRapidityComptonClock` and `MassOrigin.HiggsClockThreeOrigins`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IsotonicRapidityComptonClock
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.IsotonicBoostedHiggsClock

/-- **The isotonic Lorentz factor boosts the Higgs clock** `ω_dB(γ · yukawaMass · c²) = γ · higgsClockFrequency`,
with `γ = √(ξ²+1)` — the isotonic oscillator's hyperbolic factor is the de Broglie boost acting on the internal
Higgs-mass Compton clock. -/
lemma isotonic_boosts_higgs_clock (y v c ħ ξ : ℝ) :
    deBroglieFrequency (Real.sqrt (ξ ^ 2 + 1) * (yukawaMass y v * c ^ 2)) ħ
      = Real.sqrt (ξ ^ 2 + 1) * higgsClockFrequency y v c ħ := by
  unfold higgsClockFrequency
  exact sqrt_sq_add_one_boosts_compton (yukawaMass y v) c ħ ξ

/-- **The isotonic boost acts uniformly on the three mass-origin forms** — when the three masses coincide, the
boosted de Broglie frequency of the Higgs clock equals the boosted horizon form `γ · c³Ȧ_H/(4Għ)` and the boosted
topological form `γ · comptonFrequency (topologicalMass dj)`: the single isotonic Lorentz factor scales all three
Higgs-free origins together. -/
lemma isotonic_boosts_three_origins (y v G c Adot ħ ξ : ℝ) (dj : DJTData) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hHorizon : yukawaMass y v = gravitationalMass G c Adot)
    (hTopo : yukawaMass y v = topologicalMass dj) :
    deBroglieFrequency (Real.sqrt (ξ ^ 2 + 1) * (yukawaMass y v * c ^ 2)) ħ
        = Real.sqrt (ξ ^ 2 + 1) * (c ^ 3 * Adot / (4 * G * ħ))
      ∧ deBroglieFrequency (Real.sqrt (ξ ^ 2 + 1) * (yukawaMass y v * c ^ 2)) ħ
        = Real.sqrt (ξ ^ 2 + 1) * comptonFrequency (topologicalMass dj) c ħ := by
  obtain ⟨-, -, -, hhor, htop⟩ :=
    higgs_clock_three_origins y v G c Adot ħ dj hc hħ hHorizon hTopo
  refine ⟨?_, ?_⟩ <;> rw [isotonic_boosts_higgs_clock]
  · rw [hhor]
  · rw [htop]

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.IsotonicBoostedHiggsClock
