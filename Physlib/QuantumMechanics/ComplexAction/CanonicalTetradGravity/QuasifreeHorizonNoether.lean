/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

/-!
# The gravitational sector on the Lusanna ADM geometry: tetrad, Wald charge, Verch quasifree horizon

Links the reversible gravitational sector of the complex Noether charge — the causal-diamond Wald charge
realized as the Verch quasifree (Hadamard) Bekenstein–Hawking horizon (`AlgebraicQFTQuasifree.QuasifreeGravFluidNoether`)
— to **ADM tetrad gravity** (`CanonicalTetradGravity.TetradADMGravity`). The same geometric sector is, simultaneously:

* a **Lorentz-gauge-invariant tetrad geometry** `g = EᵀηE`, unchanged by a local Lorentz frame rotation
  `E ↦ ΛE` (`tetradMetric_lorentz_gauge`) — the `𝔰𝔬(1,3)` frame freedom is pure inertial gauge;
* satisfying the **vacuum ADM Hamiltonian constraint** `ℋ = 0 ⟺ ³R + (tr K)² = K_ij K^ij`
  (`hamiltonianConstraint_vacuum_iff`, the `G_{nn} = 0` Einstein equation, with York time `tr K`);
* whose **complex Noether real sector** is the Wald charge `Re Q = −κA/(8πG)`
  (`gravFluidNoetherCharge_re`);
* whose horizon **area** is the **Verch quasifree Bekenstein–Hawking entropy** `A/(4ℓ_P²)`, the microstate
  count of `N = A/ℓ_P²` Verch quasifree (Hadamard) cells of Gaussian weight `e^{−1/4}`
  (`bekensteinHawking_recovery`, `cell_quasifreeWeight`).

So the reversible gravitational sector of the complex Noether charge lives on the Lusanna canonical ADM
tetrad geometry: a Lorentz-gauge-invariant metric satisfying the vacuum Hamiltonian constraint, whose
Wald-charge horizon area is the curved-spacetime Verch quasifree (Hadamard) vacuum.

* **§A — the gravitational sector across the ADM, Wald-charge, and Verch-quasifree faces**
  (`lusanna_verch_quasifree_gravitational_sector`).

## References

* L. Lusanna (canonical ADM tetrad gravity); R. Wald (Noether-charge entropy); R. Verch (quasifree /
  Hadamard states). Carriers: `CanonicalTetradGravity.TetradADMGravity` (`tetradMetric`, `tetradMetric_lorentz_gauge`,
  `hamiltonianConstraint_vacuum_iff`, `yorkTime`), `AlgebraicQFTQuasifree.QuasifreeGravFluidNoether`
  (`gravFluidNoetherCharge_re`, `bekensteinHawking_recovery`, `cell_quasifreeWeight`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.QuasifreeHorizonNoether

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime


/-- **[The gravitational sector lives on the Lusanna ADM geometry].** For a Lorentz frame `Λ ∈ SO(1,3)`, a
cotetrad `E`, ADM canonical data `(³R, K, K_ij K^ij)`, and a Verch quasifree horizon cell
(`schmidtNumber η = cellBondDimension`), the reversible gravitational sector of the complex Noether charge
is simultaneously:

* the Lorentz-gauge-invariant tetrad metric `g[ΛE] = g[E]` (`tetradMetric_lorentz_gauge`);
* the vacuum ADM Hamiltonian constraint `ℋ = 0 ⟺ ³R + (tr K)² = K_ij K^ij`
  (`hamiltonianConstraint_vacuum_iff`, the `G_{nn}` Einstein equation);
* the Wald charge `Re Q = −κA/(8πG)` (`gravFluidNoetherCharge_re`);
* the Verch quasifree Bekenstein–Hawking horizon `A/(4ℓ_P²) = microstateEntropy(A/ℓ_P²)` of cells with
  Hadamard weight `e^{−1/4}` (`bekensteinHawking_recovery`, `cell_quasifreeWeight`).

The Lusanna canonical ADM tetrad geometry, the Wald/Noether charge, and the Verch quasifree (Hadamard)
horizon are one reversible gravitational sector. -/
lemma lusanna_verch_quasifree_gravitational_sector {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ)
    (κ A G ℓP ν P VS ħ η : ℝ) (hℓ : ℓP ≠ 0) (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ)
    (hcell : schmidtNumber η = cellBondDimension) :
    tetradMetric (Λ * E) = tetradMetric E
      ∧ (hamiltonianConstraint R3 KdotK K = 0 ↔ R3 + yorkTime K ^ 2 = KdotK)
      ∧ (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ microstateEntropy (A / ℓP ^ 2) = A / (4 * ℓP ^ 2)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.exp (-(1 / 4)) :=
  ⟨tetradMetric_lorentz_gauge hΛ, hamiltonianConstraint_vacuum_iff R3 KdotK K,
    gravFluidNoetherCharge_re κ A G ν P VS, bekensteinHawking_recovery A ℓP hℓ,
    cell_quasifreeWeight ħ η hħ hη φ hcell⟩

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.QuasifreeHorizonNoether

end
