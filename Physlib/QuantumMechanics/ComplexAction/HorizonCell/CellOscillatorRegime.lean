/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

/-!
# A horizon Planck cell is a timelike harmonic-oscillator mode

Links the **horizon Planck cell** (`HorizonCell.CellBondDimension` / `HorizonCell.CellQuasifree`, the
Verch quasifree state with bond dimension `k = e^{1/4}`, Schmidt number `K = coth η`) to the
**Nagao–Nielsen oscillator-regime causal trichotomy** (`ComplexOscillator.CausalRegimes`), where
`lorentzianForm ω = Re(ω²)` is the unit-mass oscillator discriminant and the causal character of a
complex frequency is its oscillator regime (timelike ⟺ harmonic oscillator / underdamped, spacelike ⟺
inverted oscillator / overdamped, lightlike ⟺ critically damped).

The horizon cell has a **rest mass** `Δ = 1`, so its Bogoliubov energy vector `ω = E + iξ = cosh η +
i·sinh η` (`cellEnergyVector`) is **timelike** — a genuine **harmonic oscillator** (underdamped,
oscillatory), the *Dynamics* face (`cellEnergyVector_isHarmonicOscillator`, `cellEnergyVector_timelike`,
via `massive_energyVector_isHarmonicOscillator`). Its **Schmidt number is the energy-vector real /
imaginary ratio** `K = (Re ω)/(Im ω) = E/ξ` (`schmidtNumber_eq_energyVector_ratio`) — the inverse
velocity / inverse `tanh η` — so entanglement `K > 1` is *exactly* the timelike, harmonic-oscillator
regime (`cell_entangled_harmonicOscillator`): the massive horizon cell oscillates, never runs away.

So the Verch quasifree horizon cell is a timelike, underdamped harmonic-oscillator mode of the horizon
algebra; its entanglement `K = coth η` is the oscillator's `Re/Im` frequency ratio. (The massless limit
`Δ = 0` would be lightlike / critically damped — `Rapidity.LightCone45RapidityUnification`.)

* **§A — the cell is a harmonic oscillator** (`cellEnergyVector`,
  `cellEnergyVector_isHarmonicOscillator`, `cellEnergyVector_timelike`).
* **§B — the Schmidt number is the frequency ratio** (`schmidtNumber_eq_energyVector_ratio`).
* **§C — entanglement is the harmonic-oscillator regime** (`cell_entangled_harmonicOscillator`).

## References

* K. Nagao, H. B. Nielsen (complex action / complex oscillator). Repo dependencies:
  `HorizonCell.CellBondDimension`, `MuonAnomaly.SchmidtRapidityHyperbolicUnification` (`schmidtNumber`),
  `ComplexOscillator.CausalRegimes` (`IsHarmonicOscillator`, `timelike`,
  `massive_energyVector_isHarmonicOscillator`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime

open Real
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

/-! ## §A — the horizon cell is a harmonic oscillator (timelike, underdamped) -/

/-- **The horizon cell's complex frequency / energy vector** `ω = E + iξ = cosh η + i·sinh η` — the
Bogoliubov energy vector of a unit-mass (`Δ = 1`) cell at rapidity `η`. -/
noncomputable def cellEnergyVector (η : ℝ) : ℂ :=
  (bogoliubovEnergy (Real.sinh η) 1 : ℂ) + (Real.sinh η : ℂ) * Complex.I

/-- **[The cell is a harmonic oscillator] `IsHarmonicOscillator 1 ω`.** With a rest mass `Δ = 1`, the
horizon cell's energy vector is a genuine (underdamped) harmonic oscillator — the real frequency
dominates, the mode oscillates (`massive_energyVector_isHarmonicOscillator`). -/
theorem cellEnergyVector_isHarmonicOscillator (η : ℝ) :
    IsHarmonicOscillator 1 (cellEnergyVector η) :=
  massive_energyVector_isHarmonicOscillator (Real.sinh η) 1 one_ne_zero

/-- **[The cell is timelike] the Dynamics face.** The horizon cell's energy vector lies inside the
`45°` cone (`|Im ω| < |Re ω|`, `E > ξ`) — the timelike / underdamped region. -/
theorem cellEnergyVector_timelike (η : ℝ) : timelike (cellEnergyVector η) :=
  (timelike_iff_isHarmonicOscillator _).mpr (cellEnergyVector_isHarmonicOscillator η)

/-! ## §B — the Schmidt number is the frequency real/imaginary ratio -/

/-- **[The Schmidt number is the frequency ratio] `K = (Re ω)/(Im ω) = E/ξ`.** The cell's Schmidt
number `K = coth η` is the real-to-imaginary ratio of its complex frequency — the inverse velocity
`E/ξ = 1/tanh η`, the oscillator's underdamping ratio. -/
theorem schmidtNumber_eq_energyVector_ratio (η : ℝ) :
    schmidtNumber η = (cellEnergyVector η).re / (cellEnergyVector η).im := by
  rw [schmidtNumber_eq_energy_over_momentum]
  simp only [cellEnergyVector, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, mul_one, zero_add]

/-! ## §C — entanglement is the harmonic-oscillator regime -/

/-- **[Entanglement ⟺ timelike harmonic oscillator] the massive cell oscillates.** For `η > 0` the
horizon cell is entangled (`K = coth η > 1`) *and* a timelike harmonic oscillator (underdamped,
Dynamics face), with `K = (Re ω)/(Im ω)`: the entanglement of the cell is exactly its
harmonic-oscillator frequency ratio — a stable, oscillatory (never runaway) mode. -/
theorem cell_entangled_harmonicOscillator (η : ℝ) (hη : 0 < η) :
    IsHarmonicOscillator 1 (cellEnergyVector η)
      ∧ timelike (cellEnergyVector η)
      ∧ schmidtNumber η = (cellEnergyVector η).re / (cellEnergyVector η).im
      ∧ 1 < schmidtNumber η :=
  ⟨cellEnergyVector_isHarmonicOscillator η, cellEnergyVector_timelike η,
    schmidtNumber_eq_energyVector_ratio η, schmidtNumber_gt_one η hη⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime

end
