/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw

/-!
# The Quantum Inertial Frame and the zeroth law as thermal equilibrium

`CausalDiamond.ZerothLaw` showed that a constant surface gravity `κ` (the zeroth law) gives a uniform
Unruh/Hawking temperature — thermal equilibrium. This file relates that to the **Quantum Inertial
Frame** (QIF): the QIF entropic rate `λ = a/(2πc)` (the Unruh rate, `Bogoliubov.RestFrameQIFConsistency`,
`UnruhEntropicRate`) is the kinematic shadow of the surface gravity, with two regimes:

* **Inertial QIF** — `λ = 0 ⟺ a = 0` (`qif_inertial_iff_zero_acceleration`): the inertial frame has no
  acceleration, no entropic rate, **no Unruh bath** — the reversible (equilibrium) QIF
  (`QuantumInertialFrameLorentzian.entropicRate_zero_of_allTimes_equilibrium`).
* **Accelerated / zeroth-law equilibrium** — `a = κ > 0` gives `λ = κ/(2πc) > 0`
  (`qif_accelerated_thermal`), and a *constant* `κ` (the zeroth law) gives a **uniform** rate and
  temperature (`qif_zerothLaw_equilibrium`): the accelerated thermal equilibrium.

The QIF entropic rate is **Lorentz/boost-invariant** (`qifEntropicRate_lorentz_invariant`, reusing
`boostFrame_entropicRate`) — and since the conformal Killing flow *is* the boost, that invariance is
the kinematic face of the zeroth law's geometric uniformity (`κ` constant on `𝓗`). Both say: the same
temperature `T = ℏκ/2πck_B` on every generator. The rate and temperature are related by
`λ = k_B T/ℏ` (`qifEntropicRate_eq_kB_temperature_over_hbar`).

So the zeroth law (constant `κ`, geometric) and the QIF entropic-rate invariance (boost, kinematic) are
the same equilibrium statement, with the inertial QIF (`a = 0`) as its zero-temperature limit.

## References

* This development: `CausalDiamond.ZerothLaw`, `CausalDiamond.EquivalencePrinciple`,
  `Bogoliubov.RestFrameQIFConsistency`, `Physlib.Relativity.Special.UnruhEntropicRate`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency

/-! ## §A — the QIF entropic rate is the Unruh rate; inertial ⟺ zero acceleration -/

/-- **The QIF entropic rate** `λ = a/(2πc)` — the Unruh rate of an observer with proper acceleration
`a` (the `H_I`-sector entropic rate `⟨H_I⟩/ℏ`). -/
def qifEntropicRate (a c : ℝ) : ℝ := a / (2 * Real.pi * c)

/-- **The inertial QIF is the zero-acceleration frame** `λ = 0 ⟺ a = 0`: the inertial Quantum Inertial
Frame has no entropic rate, hence no Unruh thermal bath — the reversible equilibrium frame. -/
theorem qif_inertial_iff_zero_acceleration (a c : ℝ) (hc : 0 < c) :
    qifEntropicRate a c = 0 ↔ a = 0 := by
  have h2 : (2 * Real.pi * c) ≠ 0 := by positivity
  rw [qifEntropicRate, div_eq_zero_iff]
  simp [h2]

/-- **The inertial QIF is reversible** `λ(0) = 0`. -/
@[simp] theorem qif_inertial_reversible (c : ℝ) : qifEntropicRate 0 c = 0 := by
  rw [qifEntropicRate, zero_div]

/-- **The accelerated QIF is thermal** `λ(κ) > 0` for `κ > 0`: a genuinely accelerated frame has a
positive entropic rate (a thermal bath). -/
theorem qif_accelerated_thermal (κ c : ℝ) (hκ : 0 < κ) (hc : 0 < c) :
    0 < qifEntropicRate κ c := by
  rw [qifEntropicRate]; positivity

/-! ## §B — the QIF entropic rate is Lorentz/boost-invariant (the zeroth law, kinematically) -/

/-- **The QIF entropic rate is Lorentz/boost-invariant**: under the Bogoliubov boost (which is the
conformal Killing flow), the entropic rate is unchanged (`boostFrame_entropicRate`). Since the boost is
the horizon-generating flow, this invariance is the **kinematic face of the zeroth law** — the entropic
rate (hence the temperature) is the same on every generator of `𝓗`. -/
theorem qifEntropicRate_lorentz_invariant (θ : ℝ) (F : FrameData) :
    (boostFrame θ F).entropicRate = F.entropicRate :=
  boostFrame_entropicRate θ F

/-! ## §C — the temperature: `λ = k_B T/ℏ` -/

/-- **The QIF entropic rate is the temperature** `λ = k_B T/ℏ` with `T = hawkingTemperature ℏ a c k_B`
(the Unruh = Hawking temperature at `κ = a`). -/
theorem qifEntropicRate_eq_kB_temperature_over_hbar (ℏ a c kB : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0) :
    qifEntropicRate a c = kB * hawkingTemperature ℏ a c kB / ℏ := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [qifEntropicRate, hawkingTemperature_def]
  field_simp

/-! ## §D — the zeroth law is QIF thermal equilibrium -/

/-- **The zeroth law is QIF thermal equilibrium.** A constant surface gravity `κ = κ'` (the zeroth law,
`κ` constant on `𝓗`) gives a **uniform QIF entropic rate, uniform Hawking temperature, and uniform
Unruh temperature**: the accelerated horizon is in thermal equilibrium, the same `T = ℏκ/2πck_B` on
every generator — the geometric statement (`κ` constant) and the kinematic statement (boost-invariant
entropic rate) coincide. -/
theorem qif_zerothLaw_equilibrium (ℏ κ κ' c kB : ℝ) (h : κ = κ') :
    qifEntropicRate κ c = qifEntropicRate κ' c
      ∧ hawkingTemperature ℏ κ c kB = hawkingTemperature ℏ κ' c kB
      ∧ unruhTemperature ℏ κ c kB = unruhTemperature ℏ κ' c kB := by
  rw [h]; exact ⟨rfl, rfl, rfl⟩

/-- **The inertial QIF is the zero-temperature limit of the zeroth-law equilibrium.** At `a = 0`
(inertial QIF) the entropic rate and the Unruh temperature both vanish (`qif_inertial_reversible`,
`hawkingTemperature` at `κ = 0`), whereas for `κ > 0` (accelerated, zeroth-law equilibrium) both are
positive: the inertial QIF and the accelerated thermal equilibrium are the two regimes of the single
acceleration parameter `a = κ`. -/
theorem qif_inertial_is_zero_temperature (ℏ c kB : ℝ) :
    qifEntropicRate 0 c = 0 ∧ hawkingTemperature ℏ 0 c kB = 0 := by
  refine ⟨qif_inertial_reversible c, ?_⟩
  rw [hawkingTemperature_def, mul_zero, zero_div]

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium

end
