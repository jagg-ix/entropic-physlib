/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.HerglotzLazoContact
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization

/-!
# Herglotz mechanics converges to Hamilton's equations at the computable / reversible point

This file proves that the thermodynamic / computability arc (`ThermoFieldDynamics.ThermodynamicCanonicalQuantization`,
the Landauer computability theorems `RelationalTime.EntropicLandauer.landauer_export` /
`RelationalTime.Landauer.swap_erasure_exports_erased_information`) **converges with Herglotz
classical mechanics** (`ClassicalMechanics.HerglotzLazoContact`) and, in the reversible limit,
with **Hamilton's equations** (`ClassicalMechanics.HamiltonsEquations`).

## The Herglotz contact Lagrangian and its reversible limit

Herglotz contact mechanics records dissipation in an accumulated-action variable `s` (with
`ds/dt = L_I`, the imaginary Lagrangian), via the effective Lagrangian

  `L_eff(t) = L_R(t) − ρ(t)·s(t)`.

When the accumulated imaginary action `s` vanishes, the contact-friction term drops and
`L_eff = L_R`: the standard conservative Euler–Lagrange / Hamilton flow
(`HerglotzLazoContact.effectiveLagrangian_at_zero_action`).

## Why the arc drives `s → 0`

The accumulated action `s` is exactly the entropic time of the arc:

* **Thermodynamics** — `s = S_I/b̄`, the entropic-damping exponent of the complex action
  weight (`‖thermoActionWeight S_R S_I b̄‖ = e^{−S_I/b̄} = e^{−s}`, `thermoHerglotz_damping`).
  The no-information / `T = 0` condition `‖thermoActionWeight‖ = 1` forces `S_I = 0`, hence
  `s = 0` (`thermoActionWeight_norm_one_iff`).
* **Computability** — `s = D(ρ‖σ)`, the relative-entropy / Landauer information. A reversible
  (non-erasing) computation has `ρ = σ`, so `D(ρ‖σ) = 0` (`entropicProperTime_self`): no
  information is erased, no entropy is exported (`landauer_export`'s `≥ ln 2` is for erasure;
  reversible computation pays `0`), so `s = 0`.

Either driver collapses the Herglotz contact term, so the dissipative contact dynamics
**converges to Hamilton's equations**:

* `thermoHerglotz_converges_to_hamilton` — no imaginary action (`‖thermoActionWeight‖ = 1`)
  ⟹ `L_eff = L_R`.
* `computability_reversible_to_hamilton` — reversible computation (`ρ = σ`, zero Landauer
  cost) ⟹ `L_eff = L_R`.

So `T = 0 / S_I = 0 / no information / reversible computation` — the same point as the whole
arc — is exactly where Herglotz dissipative mechanics reduces to conservative Hamiltonian
mechanics.

## References

* Herglotz contact mechanics, Lazo non-conservative principle (`HerglotzLazoContact`).
* Landauer / computability: `RelationalTime.EntropicLandauer.landauer_export`,
  `RelationalTime.Landauer.swap_erasure_exports_erased_information`.
* `ThermoFieldDynamics.ThermodynamicCanonicalQuantization` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open ClassicalMechanics
open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.HerglotzThermoComputability

/-! ## §A — thermodynamic Herglotz slice: `s = S_I/b̄` (entropic time) -/

/-- The Herglotz contact slice whose accumulated action `s` is the thermodynamic entropic time
`S_I/b̄` (the exponent of the entropic damping `e^{−S_I/b̄}`). -/
def thermoHerglotzSlice (L_R ρ S_I : ℝ → ℝ) (b : ℝ) : HerglotzContactSlice where
  L_R := L_R
  ρ := ρ
  s := fun t => S_I t / b

/-- **The Herglotz accumulated action is the entropic-damping exponent**:
`‖thermoActionWeight S_R (S_I t) b̄‖ = e^{−s(t)}`, with `s = S_I/b̄`. -/
theorem thermoHerglotz_damping (L_R ρ S_I : ℝ → ℝ) (b S_R : ℝ) (t : ℝ) :
    ‖thermoActionWeight S_R (S_I t) b‖
      = Real.exp (-((thermoHerglotzSlice L_R ρ S_I b).s t)) := by
  rw [norm_thermoActionWeight]
  rfl

/-- **Thermodynamic convergence to Hamilton**: when the complex action weight is unimodular
(`‖thermoActionWeight‖ = 1`, no imaginary action / `T = 0` / no information), the Herglotz
contact Lagrangian reduces to the reversible part `L_eff = L_R` — the standard conservative
Euler–Lagrange / Hamilton flow. -/
theorem thermoHerglotz_converges_to_hamilton (L_R ρ S_I : ℝ → ℝ) (b S_R : ℝ) (hb : b ≠ 0)
    (t : ℝ) (h : ‖thermoActionWeight S_R (S_I t) b‖ = 1) :
    (thermoHerglotzSlice L_R ρ S_I b).effectiveLagrangian t = L_R t := by
  have hSI : S_I t = 0 := (thermoActionWeight_norm_one_iff hb S_R (S_I t)).mp h
  have hs : (thermoHerglotzSlice L_R ρ S_I b).s t = 0 := by
    show S_I t / b = 0
    rw [hSI, zero_div]
  exact effectiveLagrangian_at_zero_action _ t hs

/-! ## §B — computability Herglotz slice: `s = D(ρ‖σ)` (Landauer information) -/

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Herglotz contact slice whose accumulated action `s` is the relative-entropy / Landauer
information `D(ρ‖σ)` — the entropic proper time between the computation's input and output
states. -/
def computabilityHerglotzSlice (L_R ρ : ℝ → ℝ) (states : ℝ → MState d × MState d) :
    HerglotzContactSlice where
  L_R := L_R
  ρ := ρ
  s := fun t => (entropicProperTime (states t).1 (states t).2).toReal

/-- **Computability convergence to Hamilton**: a *reversible* (non-erasing) computation has
input = output state (`ρ = σ`), so the Landauer information `D(ρ‖σ) = 0` — no entropy exported
(`landauer_export`'s `≥ ln 2` cost is for erasure; reversible computation pays `0`). The
Herglotz contact term then vanishes and `L_eff = L_R`: the dissipative contact dynamics
converges to Hamilton's equations. -/
theorem computability_reversible_to_hamilton (L_R ρ : ℝ → ℝ)
    (states : ℝ → MState d × MState d) (t : ℝ)
    (h_reversible : (states t).1 = (states t).2) :
    (computabilityHerglotzSlice L_R ρ states).effectiveLagrangian t = L_R t := by
  apply effectiveLagrangian_at_zero_action
  show (entropicProperTime (states t).1 (states t).2).toReal = 0
  rw [h_reversible, entropicProperTime_self]
  simp

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.HerglotzThermoComputability

end

end
