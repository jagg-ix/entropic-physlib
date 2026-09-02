/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree

/-!
# The horizon Planck cell, assembled across all three faces

A single main result proof assembling the whole horizon-cell cluster into *one* statement. A horizon
Planck cell at rapidity `η` whose Schmidt number equals the Bekenstein–Hawking bond dimension
`k = e^{1/4}` (`schmidtNumber η = cellBondDimension`) is simultaneously, and provably:

* **Information face** — an entangled mode: Schmidt number `K = coth η = k > 1`, imaginary action
  `S_I = ħ·log k = ħ/4`, per-cell entropy quantum `log k = 1/4`;
* **path-integral / quasifree weight** — suppression `e^{−S_I/ħ} = tanh η = 1/k = e^{−1/4}`, equal to
  the Verch quasifree (Hadamard) weight with one-particle structure `μ = 2 log k = 1/2`; a Verch
  symplectomorphism on the Weyl CCR algebra with pure-state complex structure `σ² = −1`;
* **horizon thermodynamics** — `N = A/ℓ_P²` such cells recover the Bekenstein–Hawking area law
  `S = A/(4ℓ_P²)`;
* **Dynamics face** — a timelike, underdamped harmonic-oscillator mode, with `K = (Re ω)/(Im ω)` the
  oscillator's frequency ratio of the complex frequency `ω = cosh η + i·sinh η`.

`horizonCell_threeFaces` proves all of these at once. Each conjunct is an already-proven repo lemma —
the entanglement / Schmidt rapidity, the Bekenstein–Hawking per-cell bond dimension, the Verch quasifree
(Hadamard) state, and the Nagao–Nielsen oscillator regime — so the theorem is the explicit witness that
the information geometry, the relativistic boost, the holographic horizon entropy, the curved-spacetime
quasifree state, and the underdamped oscillator are one structure.

## References

* Repo carriers: `MuonAnomaly.SchmidtRapidityHyperbolicUnification`, `HorizonCell.CellBondDimension`,
  `HorizonCell.CellQuasifree`, `HorizonCell.CellOscillatorRegime`, `AlgebraicQFT.SchmidtVerchQuasifree`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellThreeFacesAssembly

open Real
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian

/-- **[The horizon Planck cell, assembled across all three faces].** A horizon cell at rapidity `η`
whose Schmidt number is the Bekenstein–Hawking bond dimension `k = e^{1/4}`
(`schmidtNumber η = cellBondDimension`) is, simultaneously and provably:

* **Information** — entangled (`K = k > 1`) with imaginary action `S_I = ħ/4` and per-cell entropy
  quantum `log k = 1/4`;
* **quasifree** — suppression / Verch Hadamard weight `e^{−S_I/ħ} = tanh η = e^{−1/4}` with one-particle
  structure `μ = 1/2`, a Verch symplectomorphism with pure-state complex structure `σ² = −1`;
* **horizon** — `N = A/ℓ_P²` cells recover Bekenstein–Hawking `S = A/(4ℓ_P²)`;
* **Dynamics** — a timelike, underdamped harmonic oscillator with `K = (Re ω)/(Im ω)`.

The information geometry, the relativistic boost, the holographic horizon entropy, the curved-spacetime
quasifree (Hadamard) state, and the underdamped oscillator are one provable structure. -/
lemma horizonCell_threeFaces (ħ η A ℓP : ℝ) (φ : Fin 2 → ℝ)
    (hħ : ħ ≠ 0) (hη : 0 < η) (hℓ : ℓP ≠ 0) (hcell : schmidtNumber η = cellBondDimension) :
    -- Information face: entanglement, imaginary action, per-cell entropy quantum
    schmidtNumber η = cellBondDimension
      ∧ 1 < schmidtNumber η
      ∧ entropicAction ħ η = ħ * (1 / 4)
      ∧ Real.log cellBondDimension = 1 / 4
      -- quasifree weight = suppression = tanh η = e^{-1/4}; one-particle μ = 1/2; symplectomorphism
      ∧ Real.exp (-(entropicAction ħ η / ħ)) = Real.tanh η
      ∧ entanglementOneParticle ħ η = 1 / 2
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.exp (-(1 / 4))
      ∧ Symplectomorphism (thermoBogoliubov η)
      ∧ sympForm * sympForm = -1
      -- horizon thermodynamics: Bekenstein-Hawking area law
      ∧ microstateEntropy (A / ℓP ^ 2) = A / (4 * ℓP ^ 2)
      -- Dynamics face: timelike harmonic oscillator, K = Re/Im frequency ratio
      ∧ IsHarmonicOscillator 1 (cellEnergyVector η)
      ∧ timelike (cellEnergyVector η)
      ∧ schmidtNumber η = (cellEnergyVector η).re / (cellEnergyVector η).im :=
  ⟨hcell,
    schmidtNumber_gt_one η hη,
    singleCell_entropicAction ħ η hcell,
    log_cellBondDimension,
    suppression_eq_tanh ħ η hħ hη,
    cell_oneParticle ħ η hħ hcell,
    cell_quasifreeWeight ħ η hħ hη φ hcell,
    cell_bogoliubov_symplectomorphism η,
    pure_state_complex_structure,
    bekensteinHawking_recovery A ℓP hℓ,
    cellEnergyVector_isHarmonicOscillator η,
    cellEnergyVector_timelike η,
    schmidtNumber_eq_energyVector_ratio η⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellThreeFacesAssembly

end
