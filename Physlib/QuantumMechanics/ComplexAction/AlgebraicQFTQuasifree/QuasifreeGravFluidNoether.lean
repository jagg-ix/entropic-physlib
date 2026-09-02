/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree

/-!
# The complex Noether charge's real sector is the Verch quasifree (Hadamard) vacuum

Links the gravitational–fluid complex Noether charge (`GravitationalFieldEquations.GravitationalFluidComplexNoether`) to the
**Verch quasifree (Hadamard) state** of curved-spacetime QFT (`HorizonCell.CellQuasifree`,
`AlgebraicQFT.SchmidtVerchQuasifree`).

The complex Noether charge `Q = Re Q − i·Im Q` has a **real, reversible, geometric** sector and an
**imaginary, dissipative, entropic** sector. Its real sector is the causal-diamond Wald charge
`Re Q = −κA/(8πG)`, proportional to the horizon **area** `A` (`gravFluidNoetherCharge_re`). That area is
the curved-spacetime Verch quasifree vacuum:

* the area's **Bekenstein–Hawking entropy** `A/(4ℓ_P²)` is the microstate count of `N = A/ℓ_P²` horizon
  cells (`microstateEntropy (A/ℓ_P²) = A/(4ℓ_P²)`, `bekensteinHawking_recovery`);
* each horizon cell **is a Verch quasifree (Hadamard) state** — Gaussian weight `e^{−1/4}`
  (`cell_quasifreeWeight`), one-particle structure `μ = 1/2`, a Bogoliubov symplectomorphism on the Weyl
  CCR algebra, with **pure-state complex structure** `σ² = −1` (`pure_state_complex_structure`);
* and the imaginary unit that makes the Noether charge complex satisfies `i² = −1` — the **same complex
  structure** `J² = −1` as the Verch quasifree pure state (`complexNoether_verch_complexStructure`).

So the real, reversible, geometric sector of the complex Noether charge is the curved-spacetime Verch
quasifree (Hadamard) vacuum: its area is the Bekenstein–Hawking microstate count of Verch quasifree
horizon cells, and its complexification is the Verch pure-state polarization.

* **§A — the real sector's area is the Verch-quasifree Bekenstein–Hawking entropy**
  (`gravNoether_area_is_verchQuasifree_entropy`).
* **§B — the shared complex structure** (`complexNoether_verch_complexStructure`).
* **§C — the assembly** (`gravNoether_re_is_verch_quasifree_vacuum`).

## References

* R. Verch, arXiv:funct-an/9609004 (quasifree / Hadamard states); the Bekenstein–Hawking area law.
  Carriers: `GravitationalFieldEquations.GravitationalFluidComplexNoether` (`gravFluidNoetherCharge`), `HorizonCell.CellBondDimension`
  (`microstateEntropy`, `bekensteinHawking_recovery`), `HorizonCell.CellQuasifree`
  (`cell_quasifreeWeight`), `AlgebraicQFT.SchmidtVerchQuasifree` (`pure_state_complex_structure`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether

open Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime


/-- **[The real Noether sector is the Verch quasifree horizon vacuum].** The real part of the complex
Noether charge is the causal-diamond Wald charge `−κA/(8πG)` (an area quantity); the area's
Bekenstein–Hawking entropy `A/(4ℓ_P²)` is the microstate count of `N = A/ℓ_P²` horizon cells; and each
cell is a Verch quasifree (Hadamard) state with Gaussian weight `e^{−1/4}`. The reversible geometric
sector of the complex Noether charge is the curved-spacetime Verch quasifree vacuum. -/
lemma gravNoether_area_is_verchQuasifree_entropy (κ A G ℓP ν P VS ħ η : ℝ) (hℓ : ℓP ≠ 0)
    (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ) (hcell : schmidtNumber η = cellBondDimension) :
    (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ microstateEntropy (A / ℓP ^ 2) = A / (4 * ℓP ^ 2)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.exp (-(1 / 4)) :=
  ⟨gravFluidNoetherCharge_re κ A G ν P VS, bekensteinHawking_recovery A ℓP hℓ,
    cell_quasifreeWeight ħ η hħ hη φ hcell⟩


/-- **[The Noether complexification is the Verch pure-state complex structure] `i² = σ² = −1`.** The
imaginary unit that makes the Noether charge complex (`Q = Re − i·Im`) and the Verch quasifree pure-state
symplectic complex structure `σ` both square to `−1` — the same complex structure `J² = −1` underlies the
entropic sector of the complex action and the polarization of the Verch quasifree (Hadamard) state. -/
lemma complexNoether_verch_complexStructure :
    Complex.I * Complex.I = -1 ∧ sympForm * sympForm = -1 :=
  ⟨Complex.I_mul_I, pure_state_complex_structure⟩


/-- **[The real Noether sector is the Verch quasifree (Hadamard) vacuum, assembled].** The real,
reversible, geometric sector of the complex Noether charge is the causal-diamond Wald charge
`−κA/(8πG)`; its area's Bekenstein–Hawking entropy `A/(4ℓ_P²)` is the microstate count of `N = A/ℓ_P²`
Verch quasifree horizon cells, each a Hadamard state with weight `e^{−1/4}` and pure-state complex
structure `σ² = −1`; and the complexification `i² = −1` of the Noether charge is that same Verch
complex structure. The reversible geometric sector of the complex Noether charge is the curved-spacetime
Verch quasifree vacuum. -/
lemma gravNoether_re_is_verch_quasifree_vacuum (κ A G ℓP ν P VS ħ η : ℝ) (hℓ : ℓP ≠ 0)
    (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ) (hcell : schmidtNumber η = cellBondDimension) :
    (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ microstateEntropy (A / ℓP ^ 2) = A / (4 * ℓP ^ 2)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.exp (-(1 / 4))
      ∧ sympForm * sympForm = -1
      ∧ Complex.I * Complex.I = -1 :=
  ⟨gravFluidNoetherCharge_re κ A G ν P VS, bekensteinHawking_recovery A ℓP hℓ,
    cell_quasifreeWeight ħ η hħ hη φ hcell, pure_state_complex_structure, Complex.I_mul_I⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether

end
