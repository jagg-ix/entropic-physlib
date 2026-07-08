/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

/-!
# Bose → Fermi statistics: the Pauli occupation bound is the per-mode information limit

In the holographic picture (`AdSCFT.PenroseHolographicMassEntropyBound`) the black hole **saturates** the
information bound while atomic shells are **tiny finite registers** (`Particles.AtomicShellInformationCapacityOctet`).
The distinction is *statistics*: the boson → fermion transition imposes the Pauli occupation bound, and that
bound is exactly the "one bit per mode" that discretizes the continuous holographic capacity into the finite
octet registers.

The two occupations are reciprocal. With `x = β ℏω`:

* **Boson** `n_B = 1/(e^x − 1)` (`boseEinstein`): `1 + 2 n_B = coth(x/2)`, **unbounded** as `x → 0⁺` — the
  bosonic (graviton-condensate) side that *saturates* the gravitational ceiling.
* **Fermion** `n_F = 1/(e^x + 1)` (`fermiDirac`): `1 − 2 n_F = tanh(x/2) ∈ (0,1)`, so `0 < n_F < 1` — the
  **Pauli-bounded** side, each mode at most one fermion = one bit.

This file proves:

* `fermiDirac_pos`, `fermiDirac_lt_one`: `0 < n_F < 1` — the Pauli bound, the per-mode information limit that
  underlies the finite shell capacities `2(2l+1)` and the octet's 8 bits.
* `fermiDirac_lt_half_of_pos`: at positive energy `n_F < 1/2` (below the Fermi level).
* `boseFermi_reciprocity`: `(1 + 2 n_B)(1 − 2 n_F) = 1` — the `coth·tanh = 1` relation joining the unbounded
  bosonic occupation (BH saturation) to the Pauli-bounded fermionic occupation (atomic registers).

So the boson→fermion transition is the discretizer: bosons (no bound) let the black hole saturate the
holographic ceiling; fermions (Pauli bound `n_F < 1`) turn each mode into one bit, building the finite atomic
registers nested far below.

## References

* W. Pauli (1925); Bose–Einstein and Fermi–Dirac statistics. `Physlib` (`ComplexOscillator.ComplexFermionicOscillator.fermiDirac`,
  `ThermoFieldDynamics.MatsubaraThermalOscillator.boseEinstein`, `Particles.AtomicShellInformationCapacityOctet`,
  `AdSCFT.PenroseHolographicMassEntropyBound`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit

/-- **[Fermion occupation is positive]** `0 < n_F`. -/
theorem fermiDirac_pos (x : ℝ) : 0 < fermiDirac x := by
  unfold fermiDirac; positivity

/-- **[The Pauli bound: `n_F < 1`]** the Fermi–Dirac occupation never reaches `1` — at most one fermion per
mode. This per-mode bound is the "one bit per mode" that makes the atomic shell capacities `2(2l+1)` (and the
octet's 8 bits) finite. -/
theorem fermiDirac_lt_one (x : ℝ) : fermiDirac x < 1 := by
  unfold fermiDirac
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos x]

/-- **[Below the Fermi level]** at positive energy `n_F < 1/2`. -/
theorem fermiDirac_lt_half_of_pos {x : ℝ} (hx : 0 < x) : fermiDirac x < 1 / 2 := by
  unfold fermiDirac
  have he : (1 : ℝ) < Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- **[Bose–Fermi reciprocity `coth·tanh = 1`]** `(1 + 2 n_B)(1 − 2 n_F) = 1` (for `β ℏω ≠ 0`): the unbounded
bosonic occupation `1 + 2 n_B = coth(βℏω/2)` and the Pauli-bounded fermionic occupation
`1 − 2 n_F = tanh(βℏω/2)` are reciprocal. The boson side can saturate (coth → ∞); the fermion side is capped
(tanh < 1) — the statistical origin of "BH saturates, atomic registers stay finite". -/
theorem boseFermi_reciprocity (β ℏω : ℝ) (hx : β * ℏω ≠ 0) :
    (1 + 2 * boseEinstein β ℏω) * (1 - 2 * fermiDirac (β * ℏω)) = 1 := by
  unfold boseEinstein fermiDirac
  have h1 : Real.exp (β * ℏω) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => hx (Real.exp_injective (h.trans Real.exp_zero.symm))
  have h2 : Real.exp (β * ℏω) + 1 ≠ 0 := (by positivity : (0 : ℝ) < Real.exp (β * ℏω) + 1).ne'
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit

end
