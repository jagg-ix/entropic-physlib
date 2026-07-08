/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit

/-!
# The `coth`/`tanh` of the Bogoliubov rapidity are the Bose/Fermi occupation factors

The Bose–Fermi reciprocity `(1 + 2 n_B)(1 − 2 n_F) = 1` (`StatisticalMechanics.BoseFermiOccupationInformationLimit`) is the same
`coth·tanh = 1` that runs the Bogoliubov / causal-diamond rapidity arc. With the rapidity `η` identified with
half the dimensionless energy (`βℏω = 2η`), this file makes that explicit.

For a Bogoliubov mode `ξ = sinh η`, `Δ = 1`, the energy is `E = bogoliubovEnergy(sinh η, 1) = cosh η`
(`bogoliubovEnergy_sinh_one`), and the group velocity is `v = ξ/E = tanh η`. The identifications:

* **Fermion side `= tanh η = v`** (`bogoliubovVelocity_eq_one_sub_two_fermiDirac`): the Bogoliubov velocity
  equals the Pauli-bounded fermion occupation factor `1 − 2 n_F`. `tanh η ∈ (0,1)` is exactly the bounded
  fermionic occupation.
* **Boson side `= coth η`** (`coshDivSinh_eq_one_add_two_boseEinstein`): `E/ξ = coth η = 1 + 2 n_B`, the
  unbounded bosonic occupation factor (the BH/graviton-condensate side).
* **Reciprocity** (`bogoliubovVelocity_mul_coth`): `v · (E/ξ) = tanh η · coth η = 1` — the velocity and its
  inverse are the fermion/boson occupation factors.
* **Entropy = `ℏ log` of the boson factor** (`bogoliubovEntropy_eq_log_one_add_two_boseEinstein`):
  `S_I = ℏ log coth η = ℏ log(1 + 2 n_B)` — the imaginary action is `ℏ log` of the bosonic occupation, the
  `S_I = ℏ log coth η` of the rapidity arc.

So one `coth`/`tanh` pair records all of it: `tanh η` is simultaneously the metric/Bogoliubov velocity, the
fermion occupation factor (Pauli-bounded), and the kinematic root; `coth η` is the boson occupation factor
and the `e^{S_I/ℏ}` weight of the entropic-time arc.

## References

* Bogoliubov transformation; thermofield dynamics (`n_B = sinh²θ`). `Physlib`
  (`Bogoliubov.Transformation.bogoliubovEnergy`, `StatisticalMechanics.BoseFermiOccupationInformationLimit`,
  `ComplexOscillator.ComplexFermionicOscillator.fermiDirac`, `ThermoFieldDynamics.MatsubaraThermalOscillator.boseEinstein`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh

/-- **[`tanh η` is the fermion occupation factor]** `tanh η = 1 − 2 n_F` at `βℏω = 2η`. The bounded
`tanh η ∈ (0,1)` is the Pauli-bounded fermionic occupation. -/
theorem tanh_eq_one_sub_two_fermiDirac (η : ℝ) :
    Real.tanh η = 1 - 2 * fermiDirac (2 * η) := by
  unfold fermiDirac
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg,
    show (2 : ℝ) * η = η + η from by ring, Real.exp_add]
  have h2 : Real.exp η ≠ 0 := (Real.exp_pos η).ne'
  field_simp
  ring

/-- **[The Bogoliubov energy of a `sinh η` mode is `cosh η`]** `bogoliubovEnergy(sinh η, 1) = cosh η`
(`√(sinh²η + 1) = cosh η`). -/
theorem bogoliubovEnergy_sinh_one (η : ℝ) :
    bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η := by
  unfold bogoliubovEnergy
  rw [one_pow, show Real.sinh η ^ 2 + 1 = Real.cosh η ^ 2 from by rw [Real.cosh_sq],
    Real.sqrt_sq (Real.cosh_pos η).le]

/-- **[The Bogoliubov group velocity is `tanh η`]** `v = ξ/E = sinh η / cosh η = tanh η`. -/
theorem bogoliubovVelocity_eq_tanh (η : ℝ) :
    Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = Real.tanh η := by
  rw [bogoliubovEnergy_sinh_one, Real.tanh_eq_sinh_div_cosh]

/-- **[The Bogoliubov velocity is the fermion occupation factor]** `v = ξ/E = 1 − 2 n_F`: the
metric/Bogoliubov group velocity equals the Pauli-bounded fermionic occupation factor `tanh η`. The kinematic
root and the fermion statistics are the same `tanh η`. -/
theorem bogoliubovVelocity_eq_one_sub_two_fermiDirac (η : ℝ) :
    Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = 1 - 2 * fermiDirac (2 * η) := by
  rw [bogoliubovVelocity_eq_tanh, tanh_eq_one_sub_two_fermiDirac]

/-- **[`coth η` is the boson occupation factor]** `E/ξ = cosh η / sinh η = coth η = 1 + 2 n_B` (`η ≠ 0`): the
inverse Bogoliubov velocity is the unbounded bosonic occupation factor. -/
theorem coshDivSinh_eq_one_add_two_boseEinstein (η : ℝ) (hη : η ≠ 0) :
    Real.cosh η / Real.sinh η = 1 + 2 * boseEinstein 1 (2 * η) := by
  have hs : Real.sinh η ≠ 0 := fun hh => hη (Real.sinh_injective (hh.trans Real.sinh_zero.symm))
  have hc : Real.cosh η ≠ 0 := (Real.cosh_pos η).ne'
  have htanh : Real.tanh η = 1 - 2 * fermiDirac (2 * η) := tanh_eq_one_sub_two_fermiDirac η
  have hrec : (1 + 2 * boseEinstein 1 (2 * η)) * (1 - 2 * fermiDirac (2 * η)) = 1 := by
    simpa using boseFermi_reciprocity 1 (2 * η) (by simpa using hη)
  have hkey : Real.cosh η / Real.sinh η * (1 - 2 * fermiDirac (2 * η)) = 1 := by
    rw [← htanh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hne : (1 - 2 * fermiDirac (2 * η)) ≠ 0 := by
    rw [← htanh, Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero hs hc
  exact mul_right_cancel₀ hne (hkey.trans hrec.symm)

/-- **[Velocity × inverse-velocity = 1 = the Bose–Fermi reciprocity]** `tanh η · coth η = 1` — the same
reciprocity `(1 + 2 n_B)(1 − 2 n_F) = 1`, read as `v · v⁻¹`. -/
theorem bogoliubovVelocity_mul_coth (η : ℝ) (hη : η ≠ 0) :
    Real.tanh η * (Real.cosh η / Real.sinh η) = 1 := by
  have hs : Real.sinh η ≠ 0 := fun hh => hη (Real.sinh_injective (hh.trans Real.sinh_zero.symm))
  have hc : Real.cosh η ≠ 0 := (Real.cosh_pos η).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- **[The imaginary action is `ℏ log` of the boson factor]** `S_I = ℏ log coth η = ℏ log(1 + 2 n_B)` — the
entropic-time `S_I = ℏ log coth η` is `ℏ log` of the bosonic occupation. -/
theorem bogoliubovEntropy_eq_log_one_add_two_boseEinstein (ℏ η : ℝ) (hη : η ≠ 0) :
    ℏ * Real.log (Real.cosh η / Real.sinh η) = ℏ * Real.log (1 + 2 * boseEinstein 1 (2 * η)) := by
  rw [coshDivSinh_eq_one_add_two_boseEinstein η hη]

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh

end
