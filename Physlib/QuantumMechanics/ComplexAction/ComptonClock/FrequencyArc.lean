/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime

/-!
# The Compton frequency trinity is the Schmidt-rapidity / horizon-cell arc

Ties the **Compton frequency trinity** (`ComptonClock.FrequencyTrinity`) into the rest of the
Schmidt-rapidity / horizon-cell / vacuum-Bell arc. A single rapidity `η` governs all of it: the de
Broglie phase boost, the entanglement, the oscillator energy vector, and the Reeh–Schlieder spatial
decay.

The **de Broglie boost factor** `γ = cosh η = bogoliubovEnergy(sinh η, 1)` (`diamond_horizon_energy`) —
the Lorentz factor multiplying the Compton frequency in `deBroglie_eq_bogoliubovEnergy_compton` — is, at
the same rapidity:

* the **Schmidt energy** `E = K·ξ`, the numerator of `K = E/ξ = coth η`
  (`deBroglie_boost_eq_schmidt_mul_momentum`, from `schmidtNumber`);
* the **horizon-cell oscillator energy** `Re ω`, the real part of the cell's complex frequency
  `ω = cosh η + i·sinh η` (`deBroglie_boost_eq_cellEnergyVector_re`, from `cellEnergyVector`).

And the **Compton-wavelength vacuum Bell decay** is the spatial face of the **entanglement suppression**:
at the spacelike separation `r = λ_C · log K = λ_C · (S_I/ħ)`, the vacuum Bell concurrence factor
`e^{−r/λ_C}` equals the entanglement-suppression / boost velocity `e^{−S_I/ħ} = tanh η`
(`vacuumBell_at_entropicScale`). So `r/λ_C = S_I/ħ`: the Reeh–Schlieder spatial decay measured in Compton
wavelengths is the entropic action measured in `ħ`, and both are `log K = log coth η`.

`comptonTrinity_arc_links` collects the three. The de Broglie boost, the Schmidt entanglement, the
horizon-cell oscillator, and the Compton-wavelength vacuum decay are one rapidity.

* **§A — de Broglie boost = Schmidt energy** (`deBroglie_boost_eq_schmidt_mul_momentum`).
* **§B — de Broglie boost = horizon-cell oscillator energy** (`deBroglie_boost_eq_cellEnergyVector_re`).
* **§C — vacuum Bell decay = entanglement suppression at `r/λ_C = S_I/ħ`**
  (`vacuumBell_at_entropicScale`).
* **§D — the assembly** (`comptonTrinity_arc_links`).

## References

* Repo dependencies: `ComptonClock.FrequencyTrinity` (`comptonWavelength`, `deBroglieFrequency`),
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification` (`schmidtNumber`, `entropicAction`, `suppression_eq_tanh`),
  `HorizonCell.CellOscillatorRegime` (`cellEnergyVector`), `CausalDiamond.Helicity`
  (`diamond_horizon_energy`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ## §A — the de Broglie boost factor is the Schmidt energy -/

/-- **[de Broglie boost = Schmidt energy] `γ = K·ξ`.** The Lorentz factor `γ = cosh η =
bogoliubovEnergy(sinh η, 1)` multiplying the Compton frequency in the de Broglie frequency
(`deBroglie_eq_bogoliubovEnergy_compton`) is the Schmidt number `K = coth η` times the momentum
`ξ = sinh η` — the energy `E` in the inverse-velocity relation `K = E/ξ`
(`schmidtNumber_eq_energy_over_momentum`). -/
theorem deBroglie_boost_eq_schmidt_mul_momentum (η : ℝ) (hη : 0 < η) :
    bogoliubovEnergy (Real.sinh η) 1 = schmidtNumber η * Real.sinh η := by
  have hs : Real.sinh η ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hη)
  rw [diamond_horizon_energy, schmidtNumber, div_mul_cancel₀ _ hs]

/-! ## §B — the de Broglie boost factor is the horizon-cell oscillator energy -/

/-- **[de Broglie boost = horizon-cell oscillator energy] `γ = Re ω`.** The de Broglie boost factor
`γ = cosh η = bogoliubovEnergy(sinh η, 1)` is the real part of the horizon cell's complex frequency
`ω = cosh η + i·sinh η` (`cellEnergyVector`) — the Dynamics-face oscillator energy. The de Broglie phase
boost and the underdamped-oscillator energy are the same `cosh η`. -/
theorem deBroglie_boost_eq_cellEnergyVector_re (η : ℝ) :
    bogoliubovEnergy (Real.sinh η) 1 = (cellEnergyVector η).re := by
  simp only [cellEnergyVector, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-! ## §C — the Compton-wavelength vacuum decay is the entanglement suppression -/

/-- **[Vacuum Bell decay = entanglement suppression at `r/λ_C = S_I/ħ`] `e^{−r/λ_C} = tanh η`.** At the
spacelike separation `r = λ_C · log K = λ_C · (S_I/ħ)`, the vacuum Bell concurrence factor `e^{−r/λ_C}`
of the Compton-wavelength decay (`vacuum_bell_compton_decay`) equals the entanglement-suppression / boost
velocity `e^{−S_I/ħ} = tanh η` (`suppression_eq_tanh`). The Reeh–Schlieder spatial decay measured in
Compton wavelengths is the entropic action measured in `ħ`: both are `log K = log coth η`. -/
theorem vacuumBell_at_entropicScale (η m c ħ : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    Real.exp (-(comptonWavelength m c ħ * Real.log (schmidtNumber η) / comptonWavelength m c ħ))
      = Real.tanh η := by
  have hK : 0 < schmidtNumber η := by
    have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
    unfold schmidtNumber; positivity
  rw [mul_comm, mul_div_assoc, div_self hlam, mul_one, Real.exp_neg, Real.exp_log hK, schmidtNumber,
    inv_div, ← Real.tanh_eq_sinh_div_cosh]

/-! ## §D — the assembly -/

/-- **[The Compton frequency trinity is the Schmidt-rapidity / horizon-cell arc].** At rapidity `η`, the
de Broglie boost factor `γ = cosh η = bogoliubovEnergy(sinh η, 1)` is simultaneously the Schmidt energy
`K·ξ` (`deBroglie_boost_eq_schmidt_mul_momentum`), the horizon-cell oscillator energy `Re ω`
(`deBroglie_boost_eq_cellEnergyVector_re`), and the Compton-wavelength vacuum Bell decay at the entropic
separation `r = λ_C·log K` reproduces the entanglement suppression `tanh η`
(`vacuumBell_at_entropicScale`). The de Broglie phase boost, the Schmidt entanglement, the horizon-cell
oscillator, and the Reeh–Schlieder vacuum decay over the Compton wavelength are one rapidity. -/
theorem comptonTrinity_arc_links (η m c ħ : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    bogoliubovEnergy (Real.sinh η) 1 = schmidtNumber η * Real.sinh η
      ∧ bogoliubovEnergy (Real.sinh η) 1 = (cellEnergyVector η).re
      ∧ Real.exp (-(comptonWavelength m c ħ * Real.log (schmidtNumber η)
          / comptonWavelength m c ħ)) = Real.tanh η :=
  ⟨deBroglie_boost_eq_schmidt_mul_momentum η hη,
    deBroglie_boost_eq_cellEnergyVector_re η,
    vacuumBell_at_entropicScale η m c ħ hη hlam⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc

end
