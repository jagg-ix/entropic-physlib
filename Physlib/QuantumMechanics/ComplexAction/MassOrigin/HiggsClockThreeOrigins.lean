/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT

/-!
# The three Higgs-free mass origins are one internal Compton clock

Three distinct "origins" of an inertial mass appear across the repository, none of them the Higgs mechanism in the
usual sense:

* the **Higgs/Yukawa** mass `m = yukawaMass y v = y·v/√2` (`Yukawa.MassDecoherenceProportionality`);
* the **gravitational (horizon-entropy)** mass `m = gravitationalMass G c Ȧ = (c/4G)Ȧ_H`, sourced by the
 Bekenstein–Hawking horizon area growth with no Yukawa coupling (`MassOrigin.GravitationalMassHorizonEntropyNoYukawa`);
* the **topological (Chern–Simons)** mass `m = topologicalMass dj = e²|k|/2π` from the Deser–Jackiw–Templeton term
 (`ChernSimons.TopologicalMassDJT`).

This module shows they are the **same internal Compton clock** `m = ℏω/c²` (`comptonMass`): whenever the three
masses coincide, the single clock frequency `ω = higgsClockFrequency y v c ħ = comptonFrequency (yukawaMass y v)`
has **three equivalent closed forms** —

* `ω = c²(yv/√2)/ℏ` (Higgs VEV, `higgsClockFrequency_eq`);
* `ω = c³Ȧ_H/(4Għ)` (horizon entropy, 4th conjunct);
* `ω = comptonFrequency (topologicalMass dj)` = `m_CS c²/ℏ` (Chern–Simons level, 5th conjunct).

The recovery `comptonMass ω = m` is exactly `Winding.NumberMass.comptonMass_comptonFrequency` (the clock is the
`mass ↔ frequency` involution).

* **`higgsClockFrequency`** — the internal clock frequency of the Higgs mass, `comptonFrequency (yukawaMass y v)`;
 **`higgsClockFrequency_eq`** its Higgs-VEV closed form.
* **`higgs_clock_three_origins`** — the five-fold identity: mass = clock energy, = horizon-entropy mass, =
 topological mass, with `ω` in horizon form and in topological form.

All are exact `ring`/`field` identities over the existing mass definitions; the hypotheses
`hHorizon`, `hTopo` (the three masses coincide) are the physical input identifying the origins, exactly as in the
motivating reasoning. This is the mass-side counterpart of the rapidity/Compton-clock link in
`IsotonicRapidityComptonClock`: the isotonic Lorentz factor boosts *this* clock.

## References

* `Yukawa.CouplingIsolation`, `MassOrigin.GravitationalMassHorizonEntropyNoYukawa`,
 `ChernSimons.TopologicalMassDJT`, `Winding.NumberMass`. Unifies the three mass origins as one Compton clock.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins

/-- The **internal Compton-clock frequency of the Higgs (Yukawa) mass** `ω = comptonFrequency (yukawaMass y v) =
c²(yv/√2)/ℏ`. -/
noncomputable def higgsClockFrequency (y v c ħ : ℝ) : ℝ := comptonFrequency (yukawaMass y v) c ħ

/-- **The Higgs-VEV closed form** `ω = c²(yv/√2)/ℏ` — the clock frequency written through the Yukawa coupling and
the Higgs VEV. -/
theorem higgsClockFrequency_eq (y v c ħ : ℝ) :
    higgsClockFrequency y v c ħ = y * v / Real.sqrt 2 * c ^ 2 / ħ := by
  unfold higgsClockFrequency comptonFrequency yukawaMass; ring

/-- **The three Higgs-free mass origins are one internal Compton clock.** When the Higgs/Yukawa mass equals the
gravitational horizon-entropy mass (`hHorizon`) and the topological Chern–Simons mass (`hTopo`), the single clock
frequency `ω = higgsClockFrequency y v c ħ` recovers the mass as clock energy `ℏω/c²`, and has the horizon form
`c³Ȧ_H/(4Għ)` and the topological form `comptonFrequency (topologicalMass dj)` — three equivalent closed forms of
one frequency. -/
theorem higgs_clock_three_origins (y v G c Adot ħ : ℝ) (dj : DJTData) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hHorizon : yukawaMass y v = gravitationalMass G c Adot)
    (hTopo : yukawaMass y v = topologicalMass dj) :
    comptonMass (higgsClockFrequency y v c ħ) c ħ = yukawaMass y v
      ∧ yukawaMass y v = gravitationalMass G c Adot
      ∧ yukawaMass y v = topologicalMass dj
      ∧ higgsClockFrequency y v c ħ = c ^ 3 * Adot / (4 * G * ħ)
      ∧ higgsClockFrequency y v c ħ = comptonFrequency (topologicalMass dj) c ħ := by
  refine ⟨comptonMass_comptonFrequency (yukawaMass y v) c ħ hc hħ, hHorizon, hTopo, ?_, ?_⟩
  · unfold higgsClockFrequency comptonFrequency
    rw [hHorizon, gravitationalMass_eq G c Adot hc]
    ring
  · unfold higgsClockFrequency
    rw [hTopo]

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins
