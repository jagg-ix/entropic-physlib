/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree

/-!
# A horizon Planck cell is a Verch quasifree (Hadamard) state

Links the **horizon per-cell bond dimension** `k = e^{1/4}` (`HorizonCell.CellBondDimension`, the
Bekenstein–Hawking microstate quantum `log k = 1/4`) to the **Verch quasifree (Hadamard) state**
structure (`AlgebraicQFT.SchmidtVerchQuasifree`). A single horizon Planck cell, whose Schmidt number equals
the bond dimension `k = e^{1/4}`, is a *specific* Verch quasifree state of the curved-spacetime Weyl CCR
system:

* its **one-particle structure** is `μ = 2 log k = 1/2` (`cell_oneParticle`) — the Hadamard two-point
  datum of the cell;
* its **quasifree (Hadamard) weight** is `e^{−μ/2} = e^{−1/4} = 1/k` (`cell_quasifreeWeight`) — the
  entanglement-suppression `tanh η` of the cell, the Gaussian weight of the quasifree state;
* its **entanglement Bogoliubov boost** `thermoBogoliubov η` is a Verch symplectomorphism
  (`cell_bogoliubov_symplectomorphism`, the one-particle structure of the Weyl CCR system), with
  pure-state complex structure `σ² = −1` (`pure_state_complex_structure`).

So the Bekenstein–Hawking per-cell entropy quantum is realized as a concrete curved-spacetime quasifree
(Hadamard) state: a Bogoliubov-boosted, Gaussian-weighted Weyl state with one-particle structure
`μ = 1/2`, with imaginary action `ħ·log k = ħ/4`. `N` such cells give the area-law entropy
`S = A/(4ℓ_P²)`, each a Verch quasifree mode of the horizon algebra.

* **§A — the cell's one-particle structure** (`cell_oneParticle`).
* **§B — the cell's quasifree weight** (`cell_quasifreeWeight`).
* **§C — the cell's symplectomorphism** (`cell_bogoliubov_symplectomorphism`).
* **§D — the assembly** (`horizonCell_quasifree_state`).

## References

* R. Verch, arXiv:funct-an/9609004 (quasifree / Hadamard states, the pure-state polarizator); the
  Bekenstein–Hawking area law. Repo dependencies: `HorizonCell.CellBondDimension`, `AlgebraicQFT.SchmidtVerchQuasifree`
  (`entanglementOneParticle`, `quasifreeWeight_eq_suppression`), `OperatorAlgebra.WeylCCRSpacetime` (`quasifreeWeight`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree

open Real
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

/-! ## §A — the cell's one-particle structure `μ = 2 log k = 1/2` -/

/-- **[The cell's Hadamard one-particle structure] `μ = 2 log k = 1/2`.** A horizon cell whose Schmidt
number equals the bond dimension `k = e^{1/4}` has Verch quasifree one-particle structure
`μ = 2 S_I/ħ = 2 log k = 1/2` (from the per-cell imaginary action `S_I = ħ/4`). -/
theorem cell_oneParticle (ħ η : ℝ) (hħ : ħ ≠ 0) (h : schmidtNumber η = cellBondDimension) :
    entanglementOneParticle ħ η = 1 / 2 := by
  unfold entanglementOneParticle
  rw [singleCell_entropicAction ħ η h]; field_simp; ring

/-! ## §B — the cell's quasifree (Hadamard) weight `e^{−1/4} = 1/k` -/

/-- **[The cell's quasifree weight] `e^{−μ/2} = e^{−1/4} = 1/k`.** The Verch quasifree (Hadamard) weight
of a horizon cell (one-particle structure `μ = 1/2`) is `e^{−1/4} = 1/cellBondDimension` — the
entanglement-suppression `tanh η` of the cell, the Gaussian weight of the quasifree state. -/
theorem cell_quasifreeWeight (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ)
    (h : schmidtNumber η = cellBondDimension) :
    quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.exp (-(1 / 4)) := by
  rw [quasifreeWeight_eq_suppression ħ η hħ hη φ]
  have ht : Real.tanh η = (schmidtNumber η)⁻¹ := by
    rw [Real.tanh_eq_sinh_div_cosh, schmidtNumber, inv_div]
  rw [ht, h, cellBondDimension, ← Real.exp_neg]

/-! ## §C — the cell's entanglement boost is a Verch symplectomorphism -/

/-- **[The cell's Bogoliubov boost is a Verch symplectomorphism].** The entanglement-generating
Bogoliubov boost `thermoBogoliubov η` of a horizon cell is a Verch symplectomorphism (`MᵀσM = σ`) — the
one-particle structure of the curved-spacetime Weyl CCR system. -/
theorem cell_bogoliubov_symplectomorphism (η : ℝ) : Symplectomorphism (thermoBogoliubov η) :=
  schmidtBogoliubov_symplectomorphism η

/-! ## §D — the assembly -/

/-- **[A horizon Planck cell is a Verch quasifree (Hadamard) state, assembled].** A horizon cell whose
Schmidt number equals the Bekenstein–Hawking bond dimension `k = e^{1/4}` is a concrete Verch quasifree
state: one-particle structure `μ = 1/2` (`cell_oneParticle`), quasifree (Hadamard) weight
`e^{−1/4} = 1/k` (`cell_quasifreeWeight`), entanglement Bogoliubov boost a Verch symplectomorphism
(`cell_bogoliubov_symplectomorphism`) with pure-state complex structure `σ² = −1`
(`pure_state_complex_structure`). The Bekenstein–Hawking per-cell entropy quantum is the
curved-spacetime quasifree state of the horizon algebra. -/
theorem horizonCell_quasifree_state (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ)
    (h : schmidtNumber η = cellBondDimension) :
    entanglementOneParticle ħ η = 1 / 2
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.exp (-(1 / 4))
      ∧ Symplectomorphism (thermoBogoliubov η)
      ∧ sympForm * sympForm = -1 :=
  ⟨cell_oneParticle ħ η hħ h, cell_quasifreeWeight ħ η hħ hη φ h,
    cell_bogoliubov_symplectomorphism η, pure_state_complex_structure⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree

end
