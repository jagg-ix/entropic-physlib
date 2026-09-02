/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular

/-!
# The entropic clock is imaginary modular time: von Neumann evolution as the modular flow

The whole computation → causal set → Malament → dilation arc drives one clock —
the entropic time (the computational step count, the Kullback–Leibler / Landauer
cost, Malament's proper time, the `√c` dilation flow).  `KazamaTomitaTakesaki
Modular` already names what that clock **is**.

`vonNeumannGen_eq_smul_modularGenerator` proves
`vonNeumannGen ℏ H ρ = −(i/ℏ) · modularGenerator H ρ`: the von Neumann / Schrödinger
state rate is exactly `−(i/ℏ)` times the **modular generator** `δ_H` of
Tomita–Takesaki.  Equivalently the physical evolution `e^{−(i/ℏ)Ht}` is the modular
flow `Δ^{is}` at **imaginary modular time `s = t/ℏ`** — the Bisognano–Wichmann
identification of Hamiltonian time with modular time.  The same module shows `δ_H`
is simultaneously the Misra–Prigogine `liouvillian` (the internal-time generator),
the thermofield `hatHamiltonian` (the KMS/thermal superoperator), and the von
Neumann rate up to `−(i/ℏ)`.  One commutator superoperator, four readings.

## What this fixes in place for the arc

* **Entropic time = imaginary modular time.**  The KL / Landauer clock of
  `DataDrivenClockAutomaton` and `ComputationCausalSetBridge`, and Malament's
  proper time of `ComputationMalamentSpacetime`, are all the *same* clock; this
  theorem names it — imaginary modular time `s = t/ℏ`, the Tomita–Takesaki flow.

* **The Malament `√c` dilation is the modular flow.**  By Bisognano–Wichmann the
  modular flow of a wedge algebra is a **boost** — a Rindler dilation of the wedge.
  So the dilation group of `MalamentDilationBlochTetrahedral` (interval by `c`,
  log-scale translation, loxodromic Bloch/Poincaré Möbius) is the modular flow, and
  `√c` is a modular-time step.

* **The timeless vacuum is the modular-fixed sector.**
  `vonNeumann_stationary_iff_modularFixed` proves a state has zero von Neumann /
  Schrödinger rate iff it is annihilated by the modular generator (`[H, ρ] = 0`,
  the KMS-equilibrium / modular-fixed sector).  That is exactly the data-free,
  time-independent-Schrödinger, fixed-point sector where the computation's clock
  is frozen (`DataDrivenClockAutomaton.timeless_constant_on_data`): no data ⇒ no
  modular flow ⇒ no entropic time.

* **KMS is the thermodynamics.**  The modular generator being the thermofield
  `hatHamiltonian` is the same KMS/thermal structure the `ComputationLandauer`
  Kullback–Leibler cost measures — the modular temperature is the entropic clock's
  rate.

The classical substrate (Horn certificates, causal links) is real and kernel-clean;
this fixes the *identity of its clock* — imaginary modular time — while the full
Koopman/Tomita–Takesaki quantum lift onto the emergent spacetime remains open.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicClockImaginaryModularTime

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular

/-- **The timeless sector is the modular-fixed sector.**  For `ℏ ≠ 0`, a state has
vanishing von Neumann / Schrödinger rate iff the modular generator annihilates it —
`[H, ρ] = 0`, KMS equilibrium.  Since the von Neumann rate is `−(i/ℏ)·δ_H`
(`vonNeumannGen_eq_smul_modularGenerator`), the stationary states of physical time
and the fixed points of imaginary modular time coincide: the data-free,
time-independent-Schrödinger vacuum where the entropic clock is frozen. -/
theorem vonNeumann_stationary_iff_modularFixed {n : Type*} [Fintype n] [DecidableEq n]
    (ℏ : ℂ) (hℏ : ℏ ≠ 0) (H ρ : Matrix n n ℂ) :
    PeriodicQHermitian.Basic.vonNeumannGen ℏ H ρ = 0 ↔ modularGenerator H ρ = 0 := by
  rw [vonNeumannGen_eq_smul_modularGenerator, smul_eq_zero]
  exact or_iff_right (neg_ne_zero.mpr (div_ne_zero Complex.I_ne_zero hℏ))

end Physlib.QuantumMechanics.ComplexAction.EntropicClockImaginaryModularTime
