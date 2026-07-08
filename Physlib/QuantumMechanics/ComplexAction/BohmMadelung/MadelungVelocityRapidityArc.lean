/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungFisherScore
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc

/-!
# The Madelung complex velocity is the Bogoliubov complex frequency: osmotic = momentum = entropic

Analyzes the Madelung complex velocity `V = v + iu` (`BohmMadelung.MadelungOsmoticQuantumPotential`,
`BohmMadelung.MadelungFisherScore`) through the **Nagao–Nielsen contour** and the **Compton / Schmidt-rapidity**
arc (`ComptonClock.FrequencyArc`, `HorizonCell.CellOscillatorRegime`).

The Schrödinger–Burgers complex velocity `V = v + iu` has the *same complex shape* as the horizon-cell /
Bogoliubov complex energy vector `ω = cosh η + i·sinh η` (`cellEnergyVector`): at the rapidity-`η`
Bogoliubov mode, `v = cosh η` (current velocity) and `u = sinh η` (osmotic velocity), so

  `V = cosh η + i·sinh η = cellEnergyVector η`   (`complexVelocity_eq_cellEnergyVector`).

Reading off the Nagao–Nielsen real/imaginary split:

* the **real part** (current velocity, the `S_R`/phase sector) is the **de Broglie boost** factor
  `Re V = bogoliubovEnergy(sinh η, 1) = cosh η = γ = E` (`complexVelocity_re_is_deBroglie_boost`);
* the **imaginary part** (osmotic velocity = the **Fisher score**, the `S_I`/density sector, of
  `complexVelocity_im_is_score`) is the **Bogoliubov momentum** `Im V = sinh η = ξ`
  (`complexVelocity_im_is_momentum`) — the entropic sector;
* their **ratio** is the **entanglement suppression** `Im V / Re V = ξ/E = tanh η`
  (`complexVelocity_im_div_re_is_suppression`), which is the Nagao–Nielsen imaginary-action weight
  `e^{−S_I/ħ} = tanh η` (`suppression_eq_tanh`).

So the osmotic / Fisher-score sector of the Madelung complex velocity *is* the entropic momentum `ξ = sinh
η` of the Compton / Schmidt rapidity arc, and the osmotic-to-current ratio is the entanglement suppression
`e^{−S_I/ħ}` of the complex-action contour. The Madelung dissipative velocity field and the Bogoliubov
complex frequency are one rapidity.

* **§A — the Madelung complex velocity is the Bogoliubov complex frequency**
  (`complexVelocity_eq_cellEnergyVector`, `complexVelocity_re_is_deBroglie_boost`,
  `complexVelocity_im_is_momentum`).
* **§B — the osmotic/current ratio is the entanglement suppression**
  (`complexVelocity_im_div_re_is_suppression`).
* **§C — the assembly** (`madelung_velocity_rapidity`).

## References

* Madelung / Schrödinger–Burgers complex velocity; the Nagao–Nielsen complex action `e^{iS_R/ħ − S_I/ħ}`.
  structures: `BohmMadelung.MadelungOsmoticQuantumPotential` (`complexVelocity`), `HorizonCell.CellOscillatorRegime`
  (`cellEnergyVector`), `MuonAnomaly.SchmidtRapidityHyperbolicUnification` (`suppression_eq_tanh`,
  `suppression_eq_diamond_velocity`), `Bogoliubov.Transformation` (`bogoliubovEnergy`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungVelocityRapidityArc

open Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungOsmoticQuantumPotential
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime

/-! ## §A — the Madelung complex velocity is the Bogoliubov complex frequency -/

/-- **[The Madelung complex velocity is the cell/Bogoliubov complex frequency] `V = cosh η + i·sinh η`.**
At the rapidity-`η` Bogoliubov mode (current velocity `v = bogoliubovEnergy(sinh η,1) = cosh η`, osmotic
velocity `u = sinh η`), the Schrödinger–Burgers complex velocity `V = v + iu` is *exactly* the horizon-cell
complex energy vector `ω = cosh η + i·sinh η` (`cellEnergyVector`). -/
theorem complexVelocity_eq_cellEnergyVector (η : ℝ) :
    complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η) = cellEnergyVector η :=
  rfl

/-- **[Real part = de Broglie boost] `Re V = bogoliubovEnergy(sinh η,1) = cosh η = γ`.** The current
velocity (the `S_R`/phase sector) is the de Broglie boost factor / Bogoliubov energy. -/
theorem complexVelocity_re_is_deBroglie_boost (η : ℝ) :
    (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).re
      = bogoliubovEnergy (Real.sinh η) 1 :=
  complexVelocity_re _ _

/-- **[Imaginary part = Bogoliubov momentum] `Im V = sinh η = ξ`.** The osmotic velocity — the Fisher
score, the `S_I`/density sector — is the Bogoliubov momentum `ξ`, the entropic sector. -/
theorem complexVelocity_im_is_momentum (η : ℝ) :
    (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).im = Real.sinh η :=
  complexVelocity_im _ _

/-! ## §B — the osmotic/current ratio is the entanglement suppression -/

/-- **[The osmotic-to-current ratio is the entanglement suppression] `Im V / Re V = ξ/E = tanh η`.** The
ratio of the osmotic (Fisher-score, entropic) part to the current (de Broglie boost) part of the Madelung
complex velocity is the boost velocity `tanh η` — the entanglement suppression `e^{−S_I/ħ}`. -/
theorem complexVelocity_im_div_re_is_suppression (η : ℝ) :
    (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).im
        / (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).re
      = Real.tanh η := by
  rw [complexVelocity_im, complexVelocity_re]
  exact (suppression_eq_diamond_velocity η).symm

/-! ## §C — the assembly -/

/-- **[The Madelung complex velocity is the Bogoliubov complex frequency, assembled].** At the rapidity-`η`
Bogoliubov mode the Schrödinger–Burgers complex velocity `V = v + iu` is the horizon-cell complex frequency
`cosh η + i·sinh η`; its real part (current velocity) is the de Broglie boost `cosh η = bogoliubovEnergy`;
its imaginary part (osmotic velocity = Fisher score) is the Bogoliubov momentum `sinh η` — the entropic
sector; and the osmotic/current ratio is the entanglement suppression `tanh η = e^{−S_I/ħ}` of the
Nagao–Nielsen contour (`ħ ≠ 0`, `η > 0`). The Madelung dissipative velocity field, the de Broglie boost,
the Bogoliubov momentum, and the complex-action entropic suppression are one rapidity. -/
theorem madelung_velocity_rapidity (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) :
    complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η) = cellEnergyVector η
      ∧ (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).re
          = bogoliubovEnergy (Real.sinh η) 1
      ∧ (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).im = Real.sinh η
      ∧ (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).im
          / (complexVelocity (bogoliubovEnergy (Real.sinh η) 1) (Real.sinh η)).re = Real.tanh η
      ∧ Real.exp (-(entropicAction ħ η / ħ)) = Real.tanh η :=
  ⟨complexVelocity_eq_cellEnergyVector η, complexVelocity_re_is_deBroglie_boost η,
    complexVelocity_im_is_momentum η, complexVelocity_im_div_re_is_suppression η,
    suppression_eq_tanh ħ η hħ hη⟩

end Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungVelocityRapidityArc

end
