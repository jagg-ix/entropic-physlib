/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

/-!
# The Schmidt / entanglement structure is the Verch curved-spacetime quasifree state

Links the Schmidt-number / CHSH **entanglement** cluster (`MuonAnomaly.SchmidtRapidityHyperbolicUnification`,
`Bell.EntropicEnvelope`) to the **curved-spacetime QFT** sub-arc — R. Verch's symplectic-adjoint /
Hadamard work (`AlgebraicQFT.SymplecticAdjointHadamard`, `OperatorAlgebra.WeylCCRSpacetime`). The Hyperbolic Unification's
entanglement *is* the Verch quasifree (Hadamard) state structure:

* the **entanglement-generating Bogoliubov boost** `thermoBogoliubov η` at the Schmidt rapidity `η`
  (`K = coth η`) is a Verch **symplectomorphism** (`schmidtBogoliubov_symplectomorphism`,
  `Mᵀσ M = σ`, `Sp(2) = SL(2)`) — the one-particle structure of the curved-spacetime CCR Weyl system —
  with `(U_B(η), U_B(−η))` a **symplectically-adjoint pair** (`schmidtBogoliubov_adjoint_pair`,
  entangle / disentangle);
* the **entanglement-suppression factor** `e^{−S_I/ħ} = tanh η = 1/K` **is the Verch quasifree
  (Hadamard) weight** `e^{−μ/2}` (`OperatorAlgebra.WeylCCRSpacetime.quasifreeWeight`) with one-particle structure
  `μ = 2 S_I/ħ = 2 log K` (`quasifreeWeight_eq_suppression`) — the Gaussian weight of the quasifree
  state;
* the **separable / reversible limit** `K = 1`, `S_I = 0` (`μ = 0`) is the **pure quasifree Hadamard
  vacuum** (weight `1`, `pure_quasifree_separable`), whose **complex structure** is the pure-state
  polarizator `J² = −1` (`sympForm_sq`, Verch Eq. 2.4).

So the entanglement content `S_I = ħ log K`, the path-integral / quasifree suppression `tanh η`, and the
CHSH violation envelope are the curved-spacetime quasifree state: a Verch symplectomorphism on the Weyl
CCR algebra, weighted by the Hadamard one-particle structure, pure exactly in the separable limit.

* **§A — the Bogoliubov boost is a Verch symplectomorphism** (`schmidtBogoliubov_symplectomorphism`,
  `schmidtBogoliubov_adjoint_pair`).
* **§B — the suppression is the quasifree weight** (`entanglementOneParticle`,
  `quasifreeWeight_eq_suppression`).
* **§C — the separable limit is the pure Hadamard vacuum** (`pure_quasifree_separable`,
  `pure_state_complex_structure`).
* **§D — the unification** (`schmidt_quasifree_bridge`).

## References

* R. Verch, *Continuity of symplectically adjoint maps and the algebraic structure of Hadamard vacuum
  representations*, arXiv:funct-an/9609004 (pure-state polarizator, quasifree weights). Repo dependencies:
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification`, `AlgebraicQFT.SymplecticAdjointHadamard` (`Symplectomorphism`,
  `thermoBogoliubov_symplectomorphism`, `sympForm_sq`), `OperatorAlgebra.WeylCCRSpacetime` (`quasifreeWeight`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree

open Real Matrix
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

/-! ## §A — the entanglement Bogoliubov boost is a Verch symplectomorphism -/

/-- **[Entanglement is a symplectomorphism] `U_B(η)ᵀ σ U_B(η) = σ`.** The Bogoliubov boost
`thermoBogoliubov η` that generates the entanglement (Schmidt number `K = coth η`) is a Verch
**symplectomorphism** — the one-particle structure of the curved-spacetime CCR Weyl system
(`Sp(2) = SL(2)`). -/
theorem schmidtBogoliubov_symplectomorphism (η : ℝ) : Symplectomorphism (thermoBogoliubov η) :=
  thermoBogoliubov_symplectomorphism η

/-- **[Entangle / disentangle is a symplectically-adjoint pair] `(U_B(η), U_B(−η))`.** The
entanglement-generating boost and its inverse (the disentangling boost) form a Verch
symplectically-adjoint pair `(T, T⁻¹)` — `U_B(η)ᵀ σ = σ U_B(−η)`. -/
theorem schmidtBogoliubov_adjoint_pair (η : ℝ) :
    (thermoBogoliubov η)ᵀ * sympForm = sympForm * thermoBogoliubov (-η) :=
  thermoBogoliubov_adjoint_pair η

/-! ## §B — the entanglement-suppression is the Verch quasifree weight -/

/-- **The entanglement one-particle structure** `μ = 2 S_I/ħ = 2 log K` — the Verch quasifree
(Hadamard) two-point / one-particle datum encoded in the imaginary action. -/
noncomputable def entanglementOneParticle (ħ η : ℝ) : ℝ := 2 * entropicAction ħ η / ħ

/-- **[The suppression IS the quasifree weight] `e^{−μ/2} = tanh η = 1/K`.** The Verch quasifree
(Hadamard) state weight `quasifreeWeight = e^{−μ/2}` with one-particle structure `μ = 2 S_I/ħ`
(`entanglementOneParticle`) is exactly the entanglement-suppression factor `e^{−S_I/ħ} = tanh η = 1/K`
of the Hyperbolic Unification — the Gaussian weight of the quasifree state is the entanglement
suppression. -/
theorem quasifreeWeight_eq_suppression (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ) :
    quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.tanh η := by
  unfold quasifreeWeight entanglementOneParticle
  rw [show -(2 * entropicAction ħ η / ħ) / 2 = -(entropicAction ħ η / ħ) from by ring]
  exact suppression_eq_tanh ħ η hħ hη

/-! ## §C — the separable limit is the pure Hadamard vacuum -/

/-- **[Separable = pure quasifree Hadamard vacuum] `μ = 0 ⟹ weight = 1`.** In the separable /
reversible limit (`K = 1`, `S_I = 0`, so `μ = 0`) the Verch quasifree weight is `1` — the **pure
quasifree Hadamard vacuum** (no entanglement, no suppression). -/
theorem pure_quasifree_separable (φ : Fin 2 → ℝ) :
    quasifreeWeight (fun _ _ => (0 : ℝ)) φ = 1 := by
  unfold quasifreeWeight; simp

/-- **[The pure-state complex structure] `J² = −1`.** The Verch pure-state polarizator / symplectic
form satisfies `σ² = −1` (Eq. 2.4) — the complex structure of the pure quasifree Hadamard vacuum, the
`K = 1` limit of the entanglement. -/
theorem pure_state_complex_structure : sympForm * sympForm = -1 := sympForm_sq

/-! ## §D — the unification -/

/-- **[The Schmidt / entanglement structure is the Verch quasifree state, assembled].** The
entanglement-generating Bogoliubov boost is a Verch symplectomorphism
(`schmidtBogoliubov_symplectomorphism`); the entanglement-suppression `e^{−S_I/ħ} = tanh η` is the Verch
quasifree (Hadamard) weight `e^{−μ/2}` with `μ = 2 S_I/ħ` (`quasifreeWeight_eq_suppression`); the
separable limit is the pure Hadamard vacuum (`pure_quasifree_separable`) with complex structure
`J² = −1` (`pure_state_complex_structure`). The Hyperbolic-Unification entanglement is the
curved-spacetime quasifree state — a symplectomorphism on the Weyl CCR algebra, Hadamard-weighted, pure
in the separable limit. -/
theorem schmidt_quasifree_bridge (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ) :
    Symplectomorphism (thermoBogoliubov η)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.tanh η
      ∧ quasifreeWeight (fun _ _ => (0 : ℝ)) φ = 1
      ∧ sympForm * sympForm = -1 :=
  ⟨schmidtBogoliubov_symplectomorphism η, quasifreeWeight_eq_suppression ħ η hħ hη φ,
    pure_quasifree_separable φ, pure_state_complex_structure⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree

end
