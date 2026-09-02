/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeThreeFaces

/-!
# The muon `g − 2` mode is a Verch quasifree (Hadamard) state — every face the horizon cell has

`MuonAnomaly.ModeThreeFaces` gave the muon mode the Information + Dynamics faces of the horizon cell's
"Three Faces". This file completes the picture with the curved-spacetime QFT faces (`HorizonCell.CellQuasifree`
§A–§D): the muon `g − 2` mode is a concrete **Verch quasifree (Hadamard) state** of the Weyl CCR algebra,
exactly as the Bekenstein–Hawking horizon cell — only the one-particle structure / weight take the muon's
values (set by `K = √(1 + α/2π)` instead of `k = e^{1/4}`).

At rapidity `η_μ = η(K(α))`:

* **§A — one-particle structure** `μ_μ = 2 log K = log(1 + α/2π)` (`muonMode_oneParticle`) — the Hadamard
  two-point datum (horizon: `μ = 1/2`); for the muon `μ_μ ≈ 1.16×10⁻³ ≈ α/π`, barely above the pure vacuum.
* **§B — quasifree weight** `e^{−μ_μ/2} = tanh η_μ = 1/K = 1/√(1 + α/2π)` (`muonMode_quasifreeWeight`) — the
  Gaussian entanglement-suppression weight (horizon: `e^{−1/4} = 1/k`).
* **§C — symplectomorphism** `thermoBogoliubov η_μ` is a Verch symplectomorphism `MᵀσM = σ`
  (`muonMode_symplectomorphism`, η-independent — the *same* curved-spacetime one-particle structure).
* **§D — assembly** `muonMode_quasifree_state` (4-conjunct, pure complex structure `σ² = −1`), and
  `muonMode_allFaces` joining it to the Information + Dynamics faces — the muon mode carries **every** face.

**Honest layering.** As in `MuonAnomaly.ModeThreeFaces`, this is a **shared-parametrization** identity: the muon
mode and the horizon cell are built from the *same* `entanglementOneParticle`/`quasifreeWeight`/`thermoBogoliubov`
machinery, so the Verch quasifree theorems apply verbatim — at the muon's rapidity `η_μ` (barely-entangled,
`K ≈ 1.00058`) rather than the horizon's (`K = e^{1/4}`). It is **not** a claim that the muon anomaly is a
horizon/gravitational effect; it places g-2 as a near-vacuum Verch quasifree mode of the same Weyl algebra.

## References

* `Physlib` (`HorizonCell.CellQuasifree`, `AlgebraicQFT.SchmidtVerchQuasifree.entanglementOneParticle`/`quasifreeWeight_eq_suppression`,
  `MuonAnomaly.ModeThreeFaces.muonRapidity`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeThreeFaces

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeQuasifree


/-- **[The muon mode's Hadamard one-particle structure] `μ_μ = 2 log K = log(1 + α/2π)`.** The Verch quasifree
two-point datum of the muon `g − 2` mode (horizon analogue: `μ = 1/2`); `≈ α/π` at `α ≈ 1/137`, barely
above the pure (separable) vacuum. -/
lemma muonMode_oneParticle (ħ α : ℝ) (hħ : ħ ≠ 0) (hα : 0 < α) :
    entanglementOneParticle ħ (muonRapidity α) = Real.log (1 + schwingerAnomaly α) := by
  have hd : 0 < schwingerAnomaly α := by rw [schwingerAnomaly]; exact div_pos hα (by positivity)
  have h0 : (0 : ℝ) ≤ 1 + schwingerAnomaly α := by linarith
  unfold entanglementOneParticle entropicAction
  rw [muonMode_schmidt α hα, schmidtNumberFromAlpha, Real.log_sqrt h0]
  field_simp


/-- **[The muon mode's quasifree weight] `e^{−μ_μ/2} = tanh η_μ = 1/K = 1/√(1 + α/2π)`.** The Gaussian
entanglement-suppression weight of the Verch quasifree state at the muon rapidity (horizon analogue:
`e^{−1/4} = 1/k`). -/
lemma muonMode_quasifreeWeight (ħ α : ℝ) (hħ : ħ ≠ 0) (hα : 0 < α) (φ : Fin 2 → ℝ) :
    quasifreeWeight (fun _ _ => entanglementOneParticle ħ (muonRapidity α)) φ
      = (schmidtNumberFromAlpha α)⁻¹ := by
  have hη : 0 < muonRapidity α :=
    rapidity_pos (schmidtNumberFromAlpha α) (one_lt_schmidtNumberFromAlpha α hα)
  rw [quasifreeWeight_eq_suppression ħ (muonRapidity α) hħ hη φ]
  have ht : Real.tanh (muonRapidity α) = (schmidtNumber (muonRapidity α))⁻¹ := by
    rw [Real.tanh_eq_sinh_div_cosh, schmidtNumber, inv_div]
  rw [ht, muonMode_schmidt α hα]


/-- **[The muon mode's Bogoliubov boost is a Verch symplectomorphism].** `thermoBogoliubov η_μ` satisfies
`MᵀσM = σ` — the *same* curved-spacetime one-particle structure as the horizon cell (η-independent). -/
lemma muonMode_symplectomorphism (α : ℝ) :
    Symplectomorphism (thermoBogoliubov (muonRapidity α)) :=
  schmidtBogoliubov_symplectomorphism (muonRapidity α)


/-- **[The muon `g − 2` mode is a Verch quasifree (Hadamard) state, assembled].** One-particle structure
`μ_μ = log(1+α/2π)`, quasifree weight `1/√(1+α/2π)`, entanglement boost a Verch symplectomorphism with pure
complex structure `σ² = −1` — the curved-spacetime QFT faces, at the muon rapidity. -/
lemma muonMode_quasifree_state (ħ α : ℝ) (hħ : ħ ≠ 0) (hα : 0 < α) (φ : Fin 2 → ℝ) :
    entanglementOneParticle ħ (muonRapidity α) = Real.log (1 + schwingerAnomaly α)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ (muonRapidity α)) φ
          = (schmidtNumberFromAlpha α)⁻¹
      ∧ Symplectomorphism (thermoBogoliubov (muonRapidity α))
      ∧ sympForm * sympForm = -1 :=
  ⟨muonMode_oneParticle ħ α hħ hα, muonMode_quasifreeWeight ħ α hħ hα φ,
    muonMode_symplectomorphism α, pure_state_complex_structure⟩

/-- **[The muon `g − 2` mode carries every face]** Information + Dynamics (`muonMode_threeFaces`:
timelike underdamped oscillator, `K = √(1+α/2π) > 1`, `a = α/2π`) *and* curved-spacetime QFT
(`muonMode_quasifree_state`: Verch quasifree state, weight `1/√(1+α/2π)`, symplectomorphism, `σ² = −1`). The
muon mode is the same hyperbolic object as the Bekenstein–Hawking horizon cell, with every face proven, at its
own rapidity. -/
lemma muonMode_allFaces (ħ α : ℝ) (hħ : ħ ≠ 0) (hα : 0 < α) (φ : Fin 2 → ℝ) :
    (IsHarmonicOscillator 1 (cellEnergyVector (muonRapidity α))
      ∧ timelike (cellEnergyVector (muonRapidity α))
      ∧ schmidtNumber (muonRapidity α)
          = (cellEnergyVector (muonRapidity α)).re / (cellEnergyVector (muonRapidity α)).im
      ∧ schmidtNumber (muonRapidity α) = schmidtNumberFromAlpha α
      ∧ 1 < schmidtNumber (muonRapidity α)
      ∧ anomaly (muonRapidity α) = schwingerAnomaly α)
    ∧ (entanglementOneParticle ħ (muonRapidity α) = Real.log (1 + schwingerAnomaly α)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ (muonRapidity α)) φ
          = (schmidtNumberFromAlpha α)⁻¹
      ∧ Symplectomorphism (thermoBogoliubov (muonRapidity α))
      ∧ sympForm * sympForm = -1) :=
  ⟨muonMode_threeFaces α hα, muonMode_quasifree_state ħ α hħ hα φ⟩

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeQuasifree

end
