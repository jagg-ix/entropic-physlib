/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins
public import Mathlib.Analysis.Complex.Exponential

/-!
# The Compton mass-clock is a Sorkin–Johnston state

Linking the mass-origin Compton clock (`MassOrigin.HiggsClockThreeOrigins`) to the Sorkin–Johnston Hermitian
decomposition (`SorkinJohnstonHermitianDecomposition`). A clock ticking at frequency `ω` has the two-point **phase
correlator** `W(t,t') = e^{−iω(t−t')}`, which is a **Hermitian kernel** `W(t,t') = conj W(t',t)`. By the general
principle that a Hermitian kernel with non-negative diagonal is a Sorkin–Johnston state
(`SorkinJohnstonHermitianDecomposition.hermitian_isSJState`), the clock correlator **is** an SJ vacuum: its real
part `Re W = cos(ω Δt)` is the Hadamard (symmetric) part and its imaginary part `2 Im W = −2 sin(ω Δt)` is the
Pauli–Jordan (antisymmetric, commutator) part with the clock frequency.

Since `ω = higgsClockFrequency y v c ħ` is the single frequency behind the three Higgs-free mass origins (Yukawa,
horizon-entropy, Chern–Simons), the internal mass-clock of every one of those origins is one and the same SJ state.

* **`clockKernel`** — the phase correlator `e^{−iω(t−t')}`; **`clockKernel_isHermitian`**.
* **`clockKernel_hadamardPart`** — `Re W = cos(ω Δt)` (the Hadamard part is the clock's real correlation).
* **`clockKernel_isSJState`** — the clock correlator is a Sorkin–Johnston state.
* **`higgsClock_isSJState`** — the mass-origin Compton clock (`higgsClockFrequency`) is that SJ state.

Exact `Complex.exp`/`Real.cos` identities plus the abstract `hermitian_isSJState`. This ties
the mass-side arc (`HiggsClockThreeOrigins`, `IsotonicBoostedHiggsClock`) to the SJ decomposition: the internal
clock whose energy is the mass is, as a two-point function, a Sorkin–Johnston vacuum.

## References

* Composes `SorkinJohnstonHermitianDecomposition` and `MassOrigin.HiggsClockThreeOrigins`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState

/-- The **Compton clock two-point phase correlator** `W(t,t') = e^{−iω(t−t')}` — the correlation between the clock
phase at times `t` and `t'`, ticking at frequency `ω`. -/
noncomputable def clockKernel (ω t t' : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (ω : ℂ) * ((t - t' : ℝ) : ℂ))

/-- **The clock correlator is a Hermitian kernel** `W(t,t') = conj W(t',t)` — reflection is complex conjugation. -/
theorem clockKernel_isHermitian (ω : ℝ) : IsHermitianKernel (clockKernel ω) := by
  intro t t'
  unfold clockKernel
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **The Hadamard part is the clock's real correlation** `Re W = cos(ω(t−t'))` — the symmetric (reversible) part
of the clock two-point function. -/
theorem clockKernel_hadamardPart (ω t t' : ℝ) :
    hadamardPart (clockKernel ω) t t' = Real.cos (ω * (t - t')) := by
  unfold hadamardPart clockKernel
  rw [show -Complex.I * (ω : ℂ) * ((t - t' : ℝ) : ℂ) = ((-(ω * (t - t')) : ℝ) : ℂ) * Complex.I from by
    push_cast; ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **The clock diagonal is real and unit** `Re W(t,t) = 1` — the equal-time correlation, giving SJ positivity for
free. -/
theorem clockKernel_diag_re (ω t : ℝ) : (clockKernel ω t t).re = 1 := by
  unfold clockKernel; simp

/-- **The Compton clock correlator is a Sorkin–Johnston state** `IsSJState W (2 Im W)` — the Hermitian phase
correlator, being diagonally positive (`Re W(t,t) = 1 ≥ 0`), realizes an SJ vacuum whose Pauli–Jordan commutator
`2 Im W = −2 sin(ω Δt)` includes the clock frequency. -/
theorem clockKernel_isSJState (ω : ℝ) :
    IsSJState (clockKernel ω) (pauliJordanPart (clockKernel ω)) :=
  hermitian_isSJState (clockKernel_isHermitian ω) (fun t => by rw [clockKernel_diag_re]; norm_num)

/-- **The mass-origin Compton clock is a Sorkin–Johnston state** — the single frequency `higgsClockFrequency`
behind the three Higgs-free mass origins gives a clock correlator that is an SJ vacuum: the internal clock whose
energy `ℏω/c²` is the inertial mass is, as a two-point function, a Sorkin–Johnston state. -/
theorem higgsClock_isSJState (y v c ħ : ℝ) :
    IsSJState (clockKernel (higgsClockFrequency y v c ħ))
      (pauliJordanPart (clockKernel (higgsClockFrequency y v c ħ))) :=
  clockKernel_isSJState _

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState
