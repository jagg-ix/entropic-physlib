/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha

/-!
# The muon `g − 2` mode is the same hyperbolic object as the horizon cell — at its own rapidity

The horizon-cell arc (`HorizonCell.CellOscillatorRegime`, `HorizonCell.CellThreeFacesAssembly`) showed the
Bekenstein–Hawking cell is a timelike underdamped harmonic oscillator / Verch quasifree mode, parametrized by
the Schmidt number `K = coth η`. The muon `g − 2` arc (`MuonAnomaly.SchmidtNumberFromAlpha`) showed the mode is
parametrized by the *same* `K = coth η`, at `K = √(1 + α/2π)`. They are therefore the **same hyperbolic
object** — `cellEnergyVector η = cosh η + i·sinh η` — evaluated at two different rapidities. This file makes
the weld explicit.

Define the muon's rapidity from the fine-structure constant, `η_μ = η(K(α))` (`muonRapidity`). Then the
muon `g − 2` mode is, by the *horizon cell's own theorems*:

* **Dynamics face** — a timelike, underdamped harmonic oscillator `IsHarmonicOscillator 1 ω`
  (`muonMode_isHarmonicOscillator`, `muonMode_timelike`), `ω = cosh η_μ + i·sinh η_μ`;
* **Information face** — entangled with Schmidt number `K = √(1 + α/2π)`
  (`muonMode_entangled`, `muonMode_schmidt`), `K = (Re ω)/(Im ω)` the oscillator frequency ratio
  (`muonMode_schmidt_eq_ratio`);
* and its anomaly is the Schwinger value `a = α/2π` (`muonMode_anomaly`).

`muonMode_threeFaces` bundles these: the muon `g − 2` mode resolves to the *same* Three-Faces
structure as the holographic horizon cell — only the rapidity differs. The horizon cell sits at
`K = e^{1/4} ≈ 1.284` (a genuinely entangled bond dimension); the muon sits at `K = √(1 + α/2π) ≈ 1.00058`
(barely entangled, `η_μ ≈ 4.07`, near the separable limit).

**Honest layering.** This is a **shared-parametrization** identity: both modes are `coth η` Bogoliubov
oscillators built from the *same* `schmidtNumber`/`cellEnergyVector` machinery, so the horizon cell's verified
theorems apply verbatim to the muon mode. It is **not** a claim that the muon anomaly is a gravitational or
horizon effect — the two live at different rapidities and different physics fixes each `η`. What is proven is
structural: g-2 is the Information+Dynamics face of the hyperbolic object whose gravity face is
Bekenstein–Hawking, with `K` the single shared coordinate.

## References

* `Physlib` (`HorizonCell.CellOscillatorRegime.cellEnergyVector`, `MuonAnomaly.SchmidtNumberFromAlpha.schmidtNumberFromAlpha`,
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeThreeFaces

/-- **The muon's operating-point rapidity from `α`** `η_μ = η(K(α))`, with `K(α) = √(1 + α/2π)` the Schmidt number
forced by the Schwinger value. The muon mode's energy vector is then `cellEnergyVector η_μ`. -/
noncomputable def muonRapidity (α : ℝ) : ℝ := rapidity (schmidtNumberFromAlpha α)

/-! ### Dynamics face — the muon mode is a timelike underdamped harmonic oscillator -/

/-- **[Dynamics: the muon mode oscillates]** `IsHarmonicOscillator 1 ω` — the muon `g − 2` mode is a
genuine (underdamped) harmonic oscillator, exactly as the horizon cell (the horizon theorem applied at
`η_μ`). -/
lemma muonMode_isHarmonicOscillator (α : ℝ) :
    IsHarmonicOscillator 1 (cellEnergyVector (muonRapidity α)) :=
  cellEnergyVector_isHarmonicOscillator _

/-- **[Dynamics: timelike]** the muon mode's energy vector lies inside the `45°` cone (`E > ξ`). -/
lemma muonMode_timelike (α : ℝ) : timelike (cellEnergyVector (muonRapidity α)) :=
  cellEnergyVector_timelike _

/-! ### Information face — Schmidt number `K = √(1 + α/2π)`, the oscillator frequency ratio -/

/-- **[Information: the Schmidt number is `√(1 + α/2π)`]** the muon mode's entanglement is the Schmidt number
forced by the Schwinger value. -/
lemma muonMode_schmidt (α : ℝ) (hα : 0 < α) :
    schmidtNumber (muonRapidity α) = schmidtNumberFromAlpha α :=
  schmidtNumber_rapidity_eq α hα

/-- **[Information = Dynamics: `K = (Re ω)/(Im ω)`]** the muon mode's Schmidt number is the real/imaginary
frequency ratio of its energy vector — entanglement is the oscillator's underdamping ratio. -/
lemma muonMode_schmidt_eq_ratio (α : ℝ) :
    schmidtNumber (muonRapidity α)
      = (cellEnergyVector (muonRapidity α)).re / (cellEnergyVector (muonRapidity α)).im :=
  schmidtNumber_eq_energyVector_ratio _

/-- **[Information: entangled, barely]** `1 < K = √(1 + α/2π)` — the muon mode is entangled, but only just
(`K ≈ 1.00058` at `α ≈ 1/137`), near the separable limit, in contrast to the horizon cell's `K = e^{1/4}`. -/
lemma muonMode_entangled (α : ℝ) (hα : 0 < α) :
    1 < schmidtNumber (muonRapidity α) := by
  rw [muonMode_schmidt α hα]; exact one_lt_schmidtNumberFromAlpha α hα

/-- **[The anomaly is the Schwinger value]** `a(η_μ) = α/2π` — the anomaly of the muon mode is the
verified leading QED anomaly. -/
lemma muonMode_anomaly (α : ℝ) (hα : 0 < α) :
    anomaly (muonRapidity α) = schwingerAnomaly α :=
  anomaly_chain_eq_schwinger α hα

/-! ### The weld — the muon `g − 2` mode IS the Three-Faces object, at its own rapidity -/

/-- **[The muon `g − 2` mode resolves to the same Three-Faces structure as the horizon cell]** at
rapidity `η_μ = η(√(1+α/2π))`: a timelike underdamped harmonic oscillator (Dynamics), entangled with Schmidt
number `K = √(1+α/2π) > 1` equal to the oscillator frequency ratio (Information), carrying the Schwinger
anomaly `α/2π`. The *same* hyperbolic `cellEnergyVector` object whose gravity face is Bekenstein–Hawking —
differing only in the rapidity (muon `K ≈ 1.00058`, horizon `K = e^{1/4}`). -/
lemma muonMode_threeFaces (α : ℝ) (hα : 0 < α) :
    IsHarmonicOscillator 1 (cellEnergyVector (muonRapidity α))
      ∧ timelike (cellEnergyVector (muonRapidity α))
      ∧ schmidtNumber (muonRapidity α)
          = (cellEnergyVector (muonRapidity α)).re / (cellEnergyVector (muonRapidity α)).im
      ∧ schmidtNumber (muonRapidity α) = schmidtNumberFromAlpha α
      ∧ 1 < schmidtNumber (muonRapidity α)
      ∧ anomaly (muonRapidity α) = schwingerAnomaly α :=
  ⟨muonMode_isHarmonicOscillator α, muonMode_timelike α,
    muonMode_schmidt_eq_ratio α, muonMode_schmidt α hα,
    muonMode_entangled α hα, muonMode_anomaly α hα⟩

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeThreeFaces

end
