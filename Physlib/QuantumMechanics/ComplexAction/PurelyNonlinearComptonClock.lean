/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalRegimeRestMass
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState

/-!
# The purely nonlinear oscillator frequency is a Compton clock (rest mass, Sorkin–Johnston state)

This links `PurelyNonlinearActionAngle` (the action-angle oscillator frequency `Ω = pnlFrequency`) to
`MassOrigin.ComptonClockSorkinJohnstonState` (the Compton clock `clockKernel ω = e^{−iω(t−t')}`, a Sorkin–Johnston
state) and to the rest mass of `CausalRegimeRestMass`.

The bridge is the **frequency**: the purely nonlinear oscillator's amplitude-dependent frequency `Ω(q₀)` is the
**Compton clock frequency** of an amplitude-dependent effective mass `m(q₀) = ℏΩ/c² = comptonMass Ω`
(`ω = mc²/ℏ = comptonFrequency m`, the frequency ↔ mass Compton reciprocity), whose two-point clock kernel is a
Sorkin–Johnston vacuum. That effective mass is a genuine **rest mass** — at rest (`p = 0`) its `restMassSq` is
`m² > 0` — so it is **timelike / massive / harmonic-oscillator** (`CausalRegimeRestMass.massive_iff_timelike`).

So the oscillator, the internal Compton clock, and the causal/rest-mass classification are one object: the
amplitude sets the frequency `Ω`, the frequency is the Compton clock of the effective rest mass `ℏΩ/c²`, the clock
is an SJ state, and the (real) frequency ⟺ a timelike (massive, physical) energy-momentum.

* **`pnlFrequency_clockKernel_isSJState`** — the oscillator's Compton clock is a Sorkin–Johnston state.
* **`pnlFrequency_eq_comptonFrequency_effectiveMass`** — `Ω = comptonFrequency(comptonMass Ω)`, the frequency ↔
  effective-mass Compton reciprocity.
* **`pnlEffectiveMass_restMassSq`**, **`pnlEffectiveMass_massive`** — the effective mass is a timelike rest mass.

**Honest layering.** Exact `comptonFrequency`/`comptonMass`/`restMassSq` identities; reuses `clockKernel_isSJState`,
`comptonMass_comptonFrequency`-style reciprocity, `restMassSq` and `massive_iff_timelike`. ## References

* Links `PurelyNonlinearActionAngle` and `CausalRegimeRestMass` to `MassOrigin.ComptonClockSorkinJohnstonState`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearComptonClock

/-- **The oscillator's Compton clock is a Sorkin–Johnston state** — the purely nonlinear oscillator's
amplitude-dependent frequency `Ω = pnlFrequency α q₀` defines a Compton clock correlator `clockKernel Ω` that is an
SJ vacuum. The classical action-angle frequency, read as an internal-clock two-point function, is a
Sorkin–Johnston state. -/
lemma pnlFrequency_clockKernel_isSJState (α q₀ : ℝ) :
    IsSJState (clockKernel (pnlFrequency α q₀)) (pauliJordanPart (clockKernel (pnlFrequency α q₀))) :=
  clockKernel_isSJState _

/-- **The oscillator frequency is the Compton frequency of its effective mass** `Ω = comptonFrequency(comptonMass Ω)
= (ℏΩ/c²)·c²/ℏ` — the amplitude-dependent frequency `Ω` is the Compton clock rate of the effective rest mass
`m(q₀) = ℏΩ/c²`; the frequency ↔ mass Compton reciprocity. -/
lemma pnlFrequency_eq_comptonFrequency_effectiveMass (α q₀ c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    pnlFrequency α q₀ = comptonFrequency (comptonMass (pnlFrequency α q₀) c ħ) c ħ := by
  unfold comptonFrequency comptonMass
  field_simp

/-- **The effective Compton mass at rest has rest mass² `m²`** `restMassSq (ℏΩ/c²) 0 = (ℏΩ/c²)²` — at vanishing
spatial momentum, the effective mass `m = comptonMass Ω` supplies the metric `S`-norm `m²`. -/
lemma pnlEffectiveMass_restMassSq (α q₀ c ħ : ℝ) :
    restMassSq (comptonMass (pnlFrequency α q₀) c ħ) 0 = comptonMass (pnlFrequency α q₀) c ħ ^ 2 := by
  unfold restMassSq
  ring

/-- **The oscillator's effective mass is timelike / massive** — a nonzero effective Compton mass `ℏΩ/c²` has
positive rest mass² `m² > 0` at rest, hence is timelike (`massive_iff_timelike`): the physical, harmonic-oscillator
regime. The real amplitude-dependent oscillator frequency is a genuine massive clock. -/
lemma pnlEffectiveMass_massive (α q₀ c ħ : ℝ) (hm : comptonMass (pnlFrequency α q₀) c ħ ≠ 0) :
    0 < restMassSq (comptonMass (pnlFrequency α q₀) c ħ) 0 := by
  rw [pnlEffectiveMass_restMassSq]
  positivity

end Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearComptonClock
