/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState

/-!
# The action-angle phase is the Compton clock phase

This links the purely nonlinear oscillator's **classical action-angle phase** `θ(t) = Ω t + θ₀`
(`PurelyNonlinearGeneralizedTrig.angleEvolution`, Ghosh–Bhamidipati 1905.08062 Eq. 2.12) to the **quantum Compton
clock** `ComptonClockSorkinJohnstonState.clockKernel ω t t' = e^{−iω(t−t')}` — the Sorkin–Johnston two-point
function of the internal mass-clock.

The classical angle variable, which advances linearly at the (amplitude-dependent) frequency `Ω`, is exactly the
argument of the quantum clock phase: `clockKernel Ω t 0 = e^{−i·θ(t)}`. Since the angle is a *real* phase, the
clock kernel has unit modulus — the classical periodic motion is the reversible (unitary, zero imaginary action)
limit, matching the pure-phase sector of the master complex-action weight.

* **`clock_phase_eq_angleEvolution`** — the Compton clock phase is `e^{−i}` of the classical action-angle phase.
* **`angleEvolution_clock_reversible`** — the clock phase has unit modulus (the real angle ⇒ reversible/unitary).

**Honest layering.** Exact `Complex.exp` / `Real.exp` identities. Reuses `angleEvolution` and `clockKernel`; no new
axioms.

## References

* A. Ghosh, C. Bhamidipati, arXiv:1905.08062, Eq. 2.12. Linked to `ComptonClockSorkinJohnstonState`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleClockLink

/-- **The Compton clock phase is `e^{−i}` of the classical action-angle phase** — the internal mass-clock two-point
function `clockKernel Ω t 0 = e^{−iΩt}` is the exponential of `−i` times the classical action-angle phase
`θ(t) = Ω t` (`angleEvolution Ω 0 t`, Eq. 2.12). The action variable's angle *is* the clock's phase. -/
lemma clock_phase_eq_angleEvolution (Ω t : ℝ) :
    clockKernel Ω t 0 = Complex.exp (-Complex.I * ((angleEvolution Ω 0 t : ℝ) : ℂ)) := by
  unfold clockKernel
  congr 1
  simp only [angleEvolution]
  push_cast
  ring

/-- **The action-angle clock phase is reversible (unit modulus)** — because the classical angle `θ = Ωt` is a real
phase, the Compton clock kernel has `‖e^{−iθ}‖ = 1`: the periodic motion is the reversible (unitary, zero imaginary
action) limit, the pure-phase sector of the complex-action weight. -/
lemma angleEvolution_clock_reversible (Ω t : ℝ) : ‖clockKernel Ω t 0‖ = 1 := by
  rw [clock_phase_eq_angleEvolution, Complex.norm_exp]
  simp

end Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleClockLink
