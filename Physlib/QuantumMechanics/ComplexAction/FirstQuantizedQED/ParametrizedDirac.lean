/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracHydrogenSaveliev

/-!
# Agreement with Bennett's first-quantized (parametrized) electrodynamics

Proves that the arc's Dirac mass / contour / proper-time objects **agree with** the parametrized
Dirac–QED of *A. F. Bennett, "First Quantized Electrodynamics", arXiv:1406.0750v3*. Bennett's wavefunction
`ψ(x,τ)` evolves in an **independent parameter `τ`** with no mass constant; the mass enters as the
τ-frequency `ψ ∝ e^{±i m_p τ}`, with `m_p = √(−p·p)` (timelike, `p·p ≤ 0`), energy `E_p = |p⁰|`, and
`dt/dτ = ±m_p/E_p` (his Eq. 13). Each of these is an existing arc object:

* **§A — the mass shell** (`bennett_massSq_eq_lorentzianForm`, `bennett_energy_eq_bogoliubov`). Bennett's
  `m_p² = (p⁰)² − |p|²` is `lorentzianForm` of the `(p⁰, |p|)` contour point, and his energy `E_p = |p⁰| =
  bogoliubovEnergy(|p|, m_p) = √(m_p²+|p|²)` — the arc's Dirac/Bogoliubov dispersion.
* **§B — the timelike cone** (`bennett_mass_real_iff_timelike`). Bennett's subluminal condition `p·p ≤ 0`
  (`m_p` real) is exactly the Nagao–Nielsen convergence cone `lorentzianForm ≥ 0`.
* **§C — the parameter clock** (`bennett_dt_dtau_eq_sech`). Bennett's `dt/dτ = m_p/E_p` is, at rapidity `η`,
  `sech η = 1/cosh η = 1/γ` (`fermionMass_rapidity`, `E_p = m_p cosh η`): the parameter `τ` and the
  coordinate time `t` are related by the Lorentz factor — the same coordinate-vs-parameter distinction the
  arc's clock clarification makes.
* **§D — the τ-frequency mass and the iε pole** (`bennett_tau_phase_unimodular`, `bennett_iEps_pole_gap`).
  Bennett's free τ-evolution `e^{i m_p τ}` is unimodular — the free Dirac is reversible (`S_I = 0`); and the
  `±iε` displacement of his mass pole `m_p² ± iε` (Eq. 25) is the `complexEnergy` contour point with gap `ε`
  (`lapse_im_eq_gap`) — the same Feynman/Banihashemi–Jacobson contour as the lapse arc.

So Bennett's `m_p`, `E_p`, `dt/dτ`, the timelike shell, the τ-frequency, and the iε pole are the arc's
`bogoliubovEnergy`, `lorentzianForm`, `fermionMass_rapidity`, the NN cone, the reversible fiber, and
`complexEnergy` — the parametrized first-quantized QED and the lapse/entropic-time arc are the same objects.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3 (2020) — Eqs. 1, 11–17, 13, 25. The
  parametrized Dirac equation; mass as τ-frequency; the iε mass-plane contour.
* R. P. Feynman (parametrized formalism); E. C. G. Stueckelberg (the parameter `τ`).
* Repo dependencies: `Bogoliubov.Transformation` (`bogoliubovEnergy`), `ComplexDelta.Convergence`
  (`lorentzianForm`), `WickRotation` (`complexEnergy`), `Dirac.ComplexWeylDiracHydrogenSaveliev`
  (`fermionMass_rapidity`), `GravLapse.ContourEntropicTime` (`lapse_lorentzianForm_eq`),
  `GravLapse.ContourMaster` (`lapse_im_eq_gap`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac

open Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracHydrogenSaveliev
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## §A — Bennett's mass shell `m_p = √(−p·p)`, `E_p = √(m_p²+|p|²)` -/

/-- **[Agreement — Bennett `m_p = √(−p·p)`] The Bennett mass-squared is the Minkowski interval.**
`m_p² = (p⁰)² − |p|² = lorentzianForm (complexEnergy p⁰ |p|)`: Bennett's invariant mass-squared is the
arc's `lorentzianForm` of the `(energy, momentum)` contour point (the spacetime interval). -/
theorem bennett_massSq_eq_lorentzianForm (p0 pmag : ℝ) (h : pmag ^ 2 ≤ p0 ^ 2) :
    (Real.sqrt (p0 ^ 2 - pmag ^ 2)) ^ 2 = lorentzianForm (complexEnergy p0 pmag) := by
  rw [lapse_lorentzianForm_eq, Real.sq_sqrt (by linarith)]

/-- **[Agreement — Bennett `E_p = |p⁰|`] Bennett's energy is the Bogoliubov/Dirac dispersion.**
`E_p = |p⁰| = bogoliubovEnergy(|p|, m_p) = √(m_p² + |p|²)` with `m_p = √((p⁰)²−|p|²)`: Bennett's on-shell
energy is the arc's Dirac/Bogoliubov energy (`realFermionMass_diracEnergy`). -/
theorem bennett_energy_eq_bogoliubov (p0 pmag : ℝ) (h : pmag ^ 2 ≤ p0 ^ 2) :
    |p0| = bogoliubovEnergy pmag (Real.sqrt (p0 ^ 2 - pmag ^ 2)) := by
  unfold bogoliubovEnergy
  rw [Real.sq_sqrt (by linarith), show pmag ^ 2 + (p0 ^ 2 - pmag ^ 2) = p0 ^ 2 by ring,
    Real.sqrt_sq_eq_abs]

/-! ## §B — the timelike (subluminal) cone -/

/-- **[Agreement — Bennett's `p·p ≤ 0`] The subluminal condition is the Nagao–Nielsen convergence cone.**
`m_p` is real (`|p| ≤ |p⁰|`) **iff** `lorentzianForm (complexEnergy p⁰ |p|) ≥ 0` — Bennett's "states are not
superluminal, so `p·p ≤ 0`" is exactly the timelike cone `lorentzianForm ≥ 0` of `ComplexDelta.Convergence`. -/
theorem bennett_mass_real_iff_timelike (p0 pmag : ℝ) :
    pmag ^ 2 ≤ p0 ^ 2 ↔ 0 ≤ lorentzianForm (complexEnergy p0 pmag) := by
  rw [lapse_lorentzianForm_eq]
  constructor <;> intro h <;> linarith

/-! ## §C — the parameter clock `dt/dτ = m_p/E_p` -/

/-- **[Agreement — Bennett Eq. 13] The parameter clock is the inverse Lorentz factor.**
`dt/dτ = m_p/E_p = 1/cosh η = sech η = 1/γ` at rapidity `η` (using `E_p = m_p cosh η`,
`fermionMass_rapidity`): the independent parameter `τ` runs faster than coordinate time `t` by `γ`. This is
the coordinate-time-vs-parameter relation the arc's clock clarification makes explicit. -/
theorem bennett_dt_dtau_eq_sech (m η : ℝ) (hm : 0 < m) :
    m / bogoliubovEnergy (m * Real.sinh η) m = 1 / Real.cosh η := by
  rw [fermionMass_rapidity m η hm.le]
  field_simp

/-! ## §D — the τ-frequency mass and the iε mass pole -/

/-- **[Agreement — Bennett `ψ ∝ e^{±i m_p τ}`] The free τ-evolution is unitary (reversible).** The τ-phase
`e^{i m_p τ}` is unimodular: Bennett's free, massive Dirac evolution in the parameter `τ` is reversible —
the `S_I = 0` fiber of the arc (no entropic damping for a real mass). -/
theorem bennett_tau_phase_unimodular (m_p τ : ℝ) :
    ‖Complex.exp (Complex.I * ((m_p * τ : ℝ) : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- **[Agreement — Bennett Eq. 25] The iε mass pole is a `complexEnergy` contour point.** Bennett's free
influence function has the denominator `m² − (m_p² ± iε)` with the pole displaced by `±iε` into the complex
mass plane (the Feynman prescription). The displaced value `m_p² − iε = complexEnergy m_p² ε` has imaginary
part `−ε` (`lapse_im_eq_gap`): the same `iε` contour displacement as the lapse / Banihashemi–Jacobson
arc, with `ε` the gap. -/
theorem bennett_iEps_pole_gap (msq ε : ℝ) : (complexEnergy msq ε).im = -ε :=
  lapse_im_eq_gap msq ε

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac

end
