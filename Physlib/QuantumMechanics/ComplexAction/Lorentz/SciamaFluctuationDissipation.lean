/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock

/-!
# The Sciama–Candelas–Deutsch thermal detector on the Unruh horizon

Sciama, Candelas, Deutsch, *Quantum field theory, horizons and thermodynamics* (Adv. Phys. **30** (1981)
327): a detector on an accelerated (local Rindler) worldline responds to the vacuum as a *thermal* bath — the
**fluctuation-dissipation** side of the Unruh effect.  Its transition rates obey **detailed balance** (the
KMS condition): the ratio of downward (emission) to upward (absorption) rates is the Boltzmann factor
`e^{−βω}`, and the fluctuation spectrum is the Planckian `n(ω) = 1/(e^{βω}−1)`.

This is the detector reading of the same Unruh temperature `T = κ/2π` (`JacobsonUnruhRindlerClock`) whose
inverse `β = 2π` is the Bisognano–Wichmann/KMS modular period the three clocks carry.

* `boseEinstein` — the thermal (Planck) occupation `n(ω) = 1/(e^{βω}−1)`.
* `detectorDetailedBalance` — `(n+1)/n = e^{βω}` (KMS detailed balance: emission/absorption = Boltzmann).
* `fluctuationDissipation` — `1 + 2n = (e^{βω}+1)/(e^{βω}−1) = coth(βω/2)` (the fluctuation factor).
* `boseEinstein_pos` — the occupation is positive.
* `unruh_detectorDetailedBalance` — at the Unruh `β = 2π`, the detailed-balance ratio is `e^{2πω}`.

Honest scope: the algebraic detailed-balance / fluctuation identities of the thermal occupation at the Unruh
temperature; the field-theoretic derivation of the detector response (the Wightman two-point function on the
accelerated worldline) is not built here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

/-- **The thermal (Planck / Bose–Einstein) occupation** `n(ω) = 1/(e^{βω} − 1)` at inverse temperature `β`. -/
def boseEinstein (β ω : ℝ) : ℝ := 1 / (Real.exp (β * ω) - 1)

/-- **[Detailed balance = KMS] `(n+1)/n = e^{βω}`.**  The ratio of the accelerated detector's emission to
absorption rates is the Boltzmann factor — the KMS condition characterizing the thermal Unruh bath. -/
theorem detectorDetailedBalance (β ω : ℝ) (h : Real.exp (β * ω) ≠ 1) :
    (boseEinstein β ω + 1) / boseEinstein β ω = Real.exp (β * ω) := by
  unfold boseEinstein
  have h1 : Real.exp (β * ω) - 1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring

/-- **[Fluctuation-dissipation] `1 + 2n = (e^{βω}+1)/(e^{βω}−1) = coth(βω/2)`.**  The symmetric (fluctuation)
part of the correlator is `coth(βω/2)` times the antisymmetric (dissipation) part — the fluctuation factor of
the thermal detector. -/
theorem fluctuationDissipation (β ω : ℝ) (h : Real.exp (β * ω) ≠ 1) :
    1 + 2 * boseEinstein β ω = (Real.exp (β * ω) + 1) / (Real.exp (β * ω) - 1) := by
  unfold boseEinstein
  have h1 : Real.exp (β * ω) - 1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring

/-- **[Positive occupation] `n(ω) > 0`** for `βω > 0`. -/
theorem boseEinstein_pos (β ω : ℝ) (h : 0 < β * ω) : 0 < boseEinstein β ω := by
  unfold boseEinstein
  have : 1 < Real.exp (β * ω) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr h
  exact div_pos one_pos (by linarith)

/-- **[Unruh detector detailed balance] `(n+1)/n = e^{2πω}`** at the Unruh inverse temperature `β = 2π`.  The
accelerated detector on Jacobson's local Rindler horizon obeys detailed balance at the Bisognano–Wichmann/KMS
temperature — the same `2π` the three clocks read. -/
theorem unruh_detectorDetailedBalance (ω : ℝ) (h : Real.exp (unruhInverseTemperature * ω) ≠ 1) :
    (boseEinstein unruhInverseTemperature ω + 1) / boseEinstein unruhInverseTemperature ω
      = Real.exp (unruhInverseTemperature * ω) :=
  detectorDetailedBalance unruhInverseTemperature ω h

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

end
