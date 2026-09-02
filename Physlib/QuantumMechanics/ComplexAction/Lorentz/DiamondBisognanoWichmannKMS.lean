/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

/-!
# Bisognano–Wichmann KMS structure of the diamond entropic clock

The Bisognano–Wichmann theorem: the vacuum modular flow of a wedge *is* the Lorentz boost, and the vacuum is
a KMS thermal state at the Unruh inverse temperature `β = 2π` (`SummersRelativisticVacuum.unruhInverseTemperature`).
On the diamond mode, whose boost parameter is the rapidity `θ`, this is manifest in the analytic continuation
of the diamond energy to *complex* rapidity: the KMS condition is exactly the periodicity of the correlator
in imaginary rapidity with period `β i = 2π i`.

Continuing the diamond horizon energy to `diamondEnergyC z = cosh z` (real part at real `θ` the Euclidean
`bogoliubovEnergy`, cf. `DiamondLorentzianEntropicClock`):

* **KMS periodicity** `cosh(z + 2π i) = cosh z`, `sinh(z + 2π i) = sinh z` — the diamond correlators are
  periodic in imaginary rapidity with period the Unruh `β = 2π`, so the diamond entropic clock is a *thermal*
  clock at the Bisognano–Wichmann/Unruh temperature `1/β = 1/(2π)`.
* **Modular conjugation** `cosh(z + π i) = −cosh z` — the half-period `β/2 = π` shift implements the modular
  conjugation `J` / PCT wedge reflection (`Δ^{1/2}`), reversing the temporal orientation.
* **Analytic mass shell** `cosh²z − sinh²z = 1` — the Lorentzian invariant survives the continuation, so the
  KMS flow preserves the rest mass.

* `diamondEnergyC`, `diamondEnergyC_ofReal` — the continued diamond energy and its real restriction.
* `diamond_energy_kms_periodic`, `diamond_momentum_kms_periodic` — KMS periodicity at `β = 2π`.
* `diamond_modular_reflection` — the half-period modular conjugation.
* `diamond_complexMassShell` — the continued Lorentzian invariant.

Honest scope: the analytic (imaginary-rapidity) periodicity and reflection identities of the diamond energy
and their identification with the Unruh inverse temperature; no Tomita–Takesaki modular operator or KMS
two-point function is constructed here (those live in `AlgebraicQFT`/`WickClock`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondBisognanoWichmannKMS

open Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

/-- **The diamond horizon energy continued to complex rapidity** `diamondEnergyC z = cosh z`. -/
def diamondEnergyC (z : ℂ) : ℂ := Complex.cosh z

/-- **The diamond momentum continued to complex rapidity** `diamondMomentumC z = sinh z`. -/
def diamondMomentumC (z : ℂ) : ℂ := Complex.sinh z

/-- At real rapidity the continued diamond energy is the real diamond horizon energy `cosh θ`. -/
theorem diamondEnergyC_ofReal (θ : ℝ) : diamondEnergyC (θ : ℂ) = (Real.cosh θ : ℂ) :=
  (Complex.ofReal_cosh θ).symm

/-- **[KMS periodicity of the diamond energy] `cosh(z + β i) = cosh z` at `β = 2π`.**  The continued diamond
horizon energy is periodic in imaginary rapidity with period the Unruh inverse temperature — the
Bisognano–Wichmann KMS condition for the diamond wedge. -/
theorem diamond_energy_kms_periodic (z : ℂ) :
    diamondEnergyC (z + (unruhInverseTemperature : ℂ) * Complex.I) = diamondEnergyC z := by
  unfold diamondEnergyC
  rw [show (unruhInverseTemperature : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from by
      unfold unruhInverseTemperature; push_cast; ring,
    Complex.cosh, Complex.cosh, Complex.exp_periodic z]
  have h2 : Complex.exp (-(z + 2 * (Real.pi : ℂ) * Complex.I)) = Complex.exp (-z) := by
    rw [show -(z + 2 * (Real.pi : ℂ) * Complex.I) = -z - 2 * (Real.pi : ℂ) * Complex.I from by ring]
    exact Complex.exp_periodic.sub_eq (-z)
  rw [h2]

/-- **[KMS periodicity of the diamond momentum] `sinh(z + β i) = sinh z` at `β = 2π`.** -/
theorem diamond_momentum_kms_periodic (z : ℂ) :
    diamondMomentumC (z + (unruhInverseTemperature : ℂ) * Complex.I) = diamondMomentumC z := by
  unfold diamondMomentumC
  rw [show (unruhInverseTemperature : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from by
      unfold unruhInverseTemperature; push_cast; ring,
    Complex.sinh, Complex.sinh, Complex.exp_periodic z]
  have h2 : Complex.exp (-(z + 2 * (Real.pi : ℂ) * Complex.I)) = Complex.exp (-z) := by
    rw [show -(z + 2 * (Real.pi : ℂ) * Complex.I) = -z - 2 * (Real.pi : ℂ) * Complex.I from by ring]
    exact Complex.exp_periodic.sub_eq (-z)
  rw [h2]

/-- **[Modular conjugation / PCT] `cosh(z + (β/2) i) = −cosh z` at `β/2 = π`.**  The half modular period is the
modular conjugation `J` (`Δ^{1/2}` implements PCT and the wedge reflection), reversing the temporal
orientation of the diamond. -/
theorem diamond_modular_reflection (z : ℂ) :
    diamondEnergyC (z + (unruhInverseTemperature : ℂ) / 2 * Complex.I) = -diamondEnergyC z := by
  unfold diamondEnergyC
  rw [show (unruhInverseTemperature : ℂ) / 2 * Complex.I = (Real.pi : ℂ) * Complex.I from by
      unfold unruhInverseTemperature; push_cast; ring,
    Complex.cosh, Complex.cosh, Complex.exp_add, Complex.exp_pi_mul_I,
    show -(z + (Real.pi : ℂ) * Complex.I) = -z - (Real.pi : ℂ) * Complex.I from by ring,
    Complex.exp_sub, Complex.exp_pi_mul_I]
  ring

/-- **[Analytic Lorentzian mass shell] `cosh²z − sinh²z = 1`.**  The Lorentzian invariant `E² − p² = 1`
survives the analytic continuation, so the KMS/modular flow preserves the diamond rest mass. -/
theorem diamond_complexMassShell (z : ℂ) : diamondEnergyC z ^ 2 - diamondMomentumC z ^ 2 = 1 := by
  unfold diamondEnergyC diamondMomentumC
  exact Complex.cosh_sq_sub_sinh_sq z

end Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondBisognanoWichmannKMS

end
