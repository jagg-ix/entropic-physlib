/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionQubit
public import Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState
public import Physlib.QuantumMechanics.NonHermitian.WickRotation
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMatterEnergyDensity

/-!
# Linking the standard electron wave function to the exclusion-cell arc

The **standard single-particle electron wave function** is not one object but a product of four pieces, and
each attaches to a module of the electron-exclusion-cell arc through the shared **Pauli 2-spinor**
`χ : Fin 2 → ℂ`:

 `ψ(t) = ⏟(restPositiveSpinor χ) · ⏟(e^{−imc²t/ℏ}), |ψ|² = R²`
 Dirac spinor / spin Compton-clock phase Born density

* **spin** — the `χ` of the Dirac rest wave function `restPositiveSpinor χ = (χ, 0)`
 (`Dirac.Spinors`) is *the same* `χ` that is the exclusion-cell **qubit** on the Bloch sphere
 (`ElectronExclusionQubit`, `IsHopfBlochVector χ r`);
* **energy** — the wave function solves the rest-frame Dirac equation `H ψ = mc²·ψ`
 (`diracHamiltonian_rest_positive_energy`), and that rest energy is the qubit's level gap
 `mc² = ℏ·ω_C` (`comptonFrequency`), the photon gap of `ElectronExclusionPhotonBifurcation`;
* **phase** — the rest-frame time evolution `e^{−imc²t/ℏ}` is the Compton clock
 `clockKernel ω_C t 0` (`MassOrigin.ComptonClockSorkinJohnstonState`), equal to the reversible phase
 `reversiblePhase (mc²) ℏ t`;
* **amplitude** — the Born density `|ψ|² = R² = madelungDensity ψ` (`Schrodinger.MadelungPolarDecomposition`)
 is the electron's matter source `T⁰⁰ = complexMatterEnergyDensity ψ (mc²) (m_Ic²)`, whose real part
 `mc²·ρ` sources the real curvature `G` and whose imaginary part `−m_Ic²·ρ` sources `Λ`
 (`ElectronExclusionComplexEinstein`).

So the standard electron wave function *is* the arc's electron, resolved into representations: its spin is the
qubit, its rest energy is the exclusion gap, its phase is the Compton clock, and its Born density is the
complex-Einstein matter source.

* **§A — spin: the wave function's spinor is the qubit** (`electron_wavefunction_spinor_is_qubit`).
* **§B — energy: the rest energy is the qubit gap** (`rest_energy_is_compton_gap`).
* **§C — phase: the wave function's phase is the Compton clock** (`electron_wavefunction_phase_is_comptonClock`).
* **§D — amplitude: the Born density is the complex-Einstein source** (`electron_wavefunction_sources_matter`).
* **§E — assembled** (`electron_wavefunction_arc_link`).

Every link is exact reuse: `diracHamiltonian_rest_positive_energy`,
`hopfBlochVector_lies_on_poincare_sphere`, `comptonFrequency`, `clockKernel`, `reversiblePhase`,
`complexMatterEnergyDensity_{re,im}`. The content is the *identification* — the pieces of the standard electron
wave function are the arc's qubit / gap / clock / matter source, joined by the shared 2-spinor `χ` and the rest
energy `mc²`. No new axioms.

## References

* P. A. M. Dirac (1928). Repo dependencies: `Dirac.Spinors`, `ComptonClock.FrequencyTrinity`,
 `MassOrigin.ComptonClockSorkinJohnstonState`, `NonHermitian.WickRotation`,
 `ComplexEinstein.ComplexMatterEnergyDensity`, `HorizonCell.ElectronExclusionQubit`.

No new axioms.
-/

set_option autoImplicit false

open scoped Matrix
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation
open Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMatterEnergyDensity
open Physlib.QuantumMechanics.Schrodinger

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronWaveFunctionLink

/-! ## §A — spin: the wave function's spinor is the qubit -/

/-- **[The electron wave function's spinor is the exclusion-cell qubit].** The rest positive-energy electron
wave function `restPositiveSpinor χ = (χ, 0)` solves the rest-frame Dirac equation `H ψ = mc²·ψ`, and its
Pauli 2-spinor `χ` is exactly the exclusion-cell qubit — its Bloch vector lies on the Bloch/Poincaré sphere.
The spin of the standard electron wave function *is* the arc's qubit (shared `χ`). -/
theorem electron_wavefunction_spinor_is_qubit (c mc2 : ℝ) (χ : Fin 2 → ℂ) (r : BlochVector)
    (h : IsHopfBlochVector χ r) :
    diracHamiltonian c 0 0 0 mc2 *ᵥ restPositiveSpinor χ = ((mc2 : ℝ) : ℂ) • restPositiveSpinor χ
      ∧ (r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2 + (r 2 : ℂ) ^ 2 = hopfIntensity χ ^ 2 :=
  ⟨diracHamiltonian_rest_positive_energy c mc2 χ, hopfBlochVector_lies_on_poincare_sphere χ r h⟩

/-! ## §B — energy: the rest energy is the qubit gap -/

/-- **[The wave function's rest energy is the qubit level gap] `mc² = ℏ·ω_C`.** The rest-frame Dirac energy
`mc²` (the `+mc²` eigenvalue of `restPositiveSpinor χ`) is `ℏ` times the Compton frequency — the exclusion-cell
qubit's level gap / photon gap. -/
theorem rest_energy_is_compton_gap (m c ħ : ℝ) (hħ : ħ ≠ 0) :
    m * c ^ 2 = ħ * comptonFrequency m c ħ := by
  unfold comptonFrequency; field_simp

/-! ## §C — phase: the wave function's phase is the Compton clock -/

/-- **[The wave function's rest-frame phase is the Compton clock] `e^{−imc²t/ℏ} = clockKernel ω_C t 0`.** The
unitary time evolution of the rest-frame electron wave function is the Compton-clock two-point phase at the
Compton frequency, equal to the reversible phase `reversiblePhase (mc²) ℏ t`. -/
theorem electron_wavefunction_phase_is_comptonClock (m c ħ t : ℝ) :
    clockKernel (comptonFrequency m c ħ) t 0
      = Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhase (m * c ^ 2) ħ t := by
  unfold clockKernel comptonFrequency Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhase
  rw [sub_zero]

/-! ## §D — amplitude: the Born density is the complex-Einstein source -/

/-- **[The wave function's Born density is the complex-Einstein matter source].** The electron wave function's
Born density `|ψ|² = R² = madelungDensity ψ` enters the complex matter energy density
`T⁰⁰ = complexMatterEnergyDensity ψ (mc²) (m_Ic²)`: its real part `mc²·ρ` is the real stress sourcing the
curvature `G`, and its imaginary part `−m_Ic²·ρ` is the entropic stress sourcing `Λ`. -/
theorem electron_wavefunction_sources_matter (ψ : MadelungWaveFunction) (m m_I c : ℝ) :
    (complexMatterEnergyDensity ψ (m * c ^ 2) (m_I * c ^ 2)).re = m * c ^ 2 * madelungDensity ψ
      ∧ (complexMatterEnergyDensity ψ (m * c ^ 2) (m_I * c ^ 2)).im
          = -(m_I * c ^ 2) * madelungDensity ψ :=
  ⟨complexMatterEnergyDensity_re ψ (m * c ^ 2) (m_I * c ^ 2),
    complexMatterEnergyDensity_im ψ (m * c ^ 2) (m_I * c ^ 2)⟩

/-! ## §E — assembled -/

/-- **[The standard electron wave function is the arc's electron, assembled].** For the rest positive-energy
electron wave function `restPositiveSpinor χ` (rest energy `mc²`), spin qubit `χ ↦ r` on the Bloch sphere,
Compton phase, and Born density `madelungDensity ψ`:

* it solves the rest-frame Dirac equation `H ψ = mc²·ψ` and its spinor `χ` is the qubit on the Bloch sphere;
* its rest energy is the qubit gap `mc² = ℏ·ω_C`;
* its phase `e^{−imc²t/ℏ}` is the Compton clock;
* its Born density is the complex-Einstein matter source (`mc²·ρ → G`, `−m_Ic²·ρ → Λ`).

The standard electron wave function is the exclusion-cell electron resolved into representations. -/
theorem electron_wavefunction_arc_link
    (m m_I c ħ t : ℝ) (hħ : ħ ≠ 0) (χ : Fin 2 → ℂ) (r : BlochVector) (ψ : MadelungWaveFunction)
    (h : IsHopfBlochVector χ r) :
    (diracHamiltonian c 0 0 0 (m * c ^ 2) *ᵥ restPositiveSpinor χ
          = ((m * c ^ 2 : ℝ) : ℂ) • restPositiveSpinor χ)
      ∧ (r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2 + (r 2 : ℂ) ^ 2 = hopfIntensity χ ^ 2
      ∧ m * c ^ 2 = ħ * comptonFrequency m c ħ
      ∧ clockKernel (comptonFrequency m c ħ) t 0
          = Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhase (m * c ^ 2) ħ t
      ∧ (complexMatterEnergyDensity ψ (m * c ^ 2) (m_I * c ^ 2)).re = m * c ^ 2 * madelungDensity ψ
      ∧ (complexMatterEnergyDensity ψ (m * c ^ 2) (m_I * c ^ 2)).im
          = -(m_I * c ^ 2) * madelungDensity ψ :=
  ⟨diracHamiltonian_rest_positive_energy c (m * c ^ 2) χ,
    hopfBlochVector_lies_on_poincare_sphere χ r h,
    rest_energy_is_compton_gap m c ħ hħ,
    electron_wavefunction_phase_is_comptonClock m c ħ t,
    complexMatterEnergyDensity_re ψ (m * c ^ 2) (m_I * c ^ 2),
    complexMatterEnergyDensity_im ψ (m * c ^ 2) (m_I * c ^ 2)⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronWaveFunctionLink

end
