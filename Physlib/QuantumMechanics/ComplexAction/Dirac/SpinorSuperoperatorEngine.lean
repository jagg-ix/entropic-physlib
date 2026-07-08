/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMetricRoot

/-!
# A spinor superoperator field driving the quantum-Boltzmann engine

Includes the `StatisticalMechanics.QuantumClausiusEngine` thermodynamics (first law from the Saveliev collision operator, second
law from the Snoke quantum-Boltzmann H-theorem) onto the **Dirac spinor sector**, as a *superoperator field*.

The Dirac Hamiltonian `H = α·p + βm` (`Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4`) lives in the
four-spinor operator algebra `Matrix (Fin 4) (Fin 4) ℂ`. Its **adjoint action** `ad_H = [H, ·]` — the
Heisenberg/Liouville superoperator — is a *field* over momentum `p` (a superoperator at each `p`). This is
exactly the Saveliev `collisionStar` (`= ad`) instantiated at the spinor algebra, so the whole engine wiring
transfers:

* the superoperator **conserves its own generator** `ad_H H = [H,H] = 0` — the **first law** (energy
  conservation, `CollisionOperatorSl2.LinearBoltzmannOperator.energyConserving_self`);
* the conserved quantity is the **mass shell** `H² = E_D²·1`, and `E_D = √(p²+m²) = `
  `quantumCarnotHeat(|p|, m)` is *the engine's quantum heat* (`CausalDiamond.DiracMetricRoot.diracEnergy_eq_bogoliubov`);
* paired with the H-theorem, both thermodynamic laws hold (`quantumBoltzmann_engine_two_laws`).

* **§A — the spinor superoperator field** (`diracAdjoint`, `diracAdjoint_apply`,
  `diracAdjoint_eq_collisionStar`, `diracAdjoint_one`, `diracAdjoint_self`, `diracSpinorField`). `ad_H = [H,·]`
  on `Matrix (Fin 4) (Fin 4) ℂ`, the Saveliev `collisionStar` of the Dirac Hamiltonian.
* **§B — the first law (energy conservation)** (`diracField_self_zero`, `diracField_energyConserving`). The
  superoperator annihilates its own generator: `ad_H H = 0`, i.e. `EnergyConserving H H`.
* **§C — the working substance is the engine's quantum heat** (`diracHeat_eq_quantumCarnotHeat`,
  `diracMassShell_eq_heatSq`). `E_D = quantumCarnotHeat(|p|,m)`; the conserved mass shell `H² = E_D²·1` is the
  engine heat squared.
* **§D — both thermodynamic laws on the spinor field** (`dirac_spinor_engine_two_laws`,
  `dirac_spinor_engine_complete`). First law from the spinor superoperator's self-conservation, second law
  from the H-theorem ⟹ Carnot bound; `dirac_spinor_engine_complete` conjoins *all six* facts (field
  conservation, first law, heat identity, mass shell, time-reversal evenness, Carnot bound).

## References

* Repo dependencies: `StatisticalMechanics.QuantumClausiusEngine` (`quantumCarnotHeat`, `quantumBoltzmann_engine_two_laws`);
  `CollisionOperatorSl2.LinearBoltzmannOperator.energyConserving_self`; `Thermodynamics.SecondLawQuantumBoltzmann.hTheorem`;
  `Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4`; `CausalDiamond.DiracMatter` (`diracEnergy`,
  `diracHamiltonian4_sq_energy`); `CausalDiamond.DiracMetricRoot.diracEnergy_eq_bogoliubov`;
  `Electromagnetic.EMFieldSuperoperator.emFieldAdjoint` (the analogous real-field superoperator).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.SpinorSuperoperatorEngine

open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMetricRoot
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum

/-- The four-spinor operator algebra `Matrix (Fin 4) (Fin 4) ℂ`. -/
abbrev MatC := Matrix (Fin 4) (Fin 4) ℂ

/-! ## §A — the spinor superoperator field -/

/-- **The Dirac spinor superoperator** `ad_H = [H, ·] = mulLeft H − mulRight H` on the four-spinor operator
algebra. This is the Heisenberg/Liouville generator of the Dirac Hamiltonian — the complex-spinor analogue of
`Electromagnetic.EMFieldSuperoperator.emFieldAdjoint`. -/
noncomputable def diracAdjoint (H : MatC) : MatC →ₗ[ℂ] MatC :=
  LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H

/-- **`ad_H(X) = [H, X]`** — the commutator action on spinor operators. -/
@[simp] theorem diracAdjoint_apply (H X : MatC) : diracAdjoint H X = H * X - X * H := by
  simp [diracAdjoint]

/-- **The spinor superoperator is the Saveliev `collisionStar`** of the Dirac Hamiltonian — `ad_H = [H,·]`
inherits the full `*`-calculus (Leibniz, the adjoint homomorphism, Jacobi). -/
theorem diracAdjoint_eq_collisionStar (H X : MatC) : diracAdjoint H X = collisionStar H X := by
  rw [diracAdjoint_apply, collisionStar]

/-- **`ad_H(1) = 0`** — the Hamiltonian commutes with the identity. -/
@[simp] theorem diracAdjoint_one (H : MatC) : diracAdjoint H 1 = 0 := by
  simp [diracAdjoint_apply]

/-- **`ad_H(H) = 0`** — the superoperator annihilates its own generator. -/
@[simp] theorem diracAdjoint_self (H : MatC) : diracAdjoint H H = 0 := by
  rw [diracAdjoint_eq_collisionStar, collisionStar_self]

/-- **The spinor superoperator field** `p ↦ ad_{H(p)}` — at each momentum the Heisenberg generator of the
Dirac Hamiltonian `H(p) = α·p + βm`. -/
noncomputable def diracSpinorField (p1 p2 p3 m : ℝ) : MatC →ₗ[ℂ] MatC :=
  diracAdjoint (diracHamiltonian4 p1 p2 p3 m)

/-! ## §B — the first law (energy conservation) -/

/-- **The spinor field annihilates its own Dirac Hamiltonian** `ad_{H(p)} H(p) = 0`. -/
@[simp] theorem diracField_self_zero (p1 p2 p3 m : ℝ) :
    diracSpinorField p1 p2 p3 m (diracHamiltonian4 p1 p2 p3 m) = 0 :=
  diracAdjoint_self _

/-- **[First law] The Dirac Hamiltonian is energy-conserving under its own superoperator** —
`EnergyConserving H H` (`[H,H] = 0`), the Saveliev energy conservation on the spinor field. -/
theorem diracField_energyConserving (p1 p2 p3 m : ℝ) :
    EnergyConserving (diracHamiltonian4 p1 p2 p3 m) (diracHamiltonian4 p1 p2 p3 m) :=
  energyConserving_self _

/-! ## §C — the working substance is the engine's quantum heat -/

/-- **The Dirac energy is the engine's quantum heat** `E_D = √(p²+m²) = quantumCarnotHeat(|p|, m)` — the
spinor field's conserved energy is the Bogoliubov mass-shell heat the engine exchanges. -/
theorem diracHeat_eq_quantumCarnotHeat (p : Fin 3 → ℝ) (m : ℝ) :
    diracEnergy (p 0) (p 1) (p 2) m = quantumCarnotHeat (helicityMomentum p) m := by
  unfold quantumCarnotHeat
  exact diracEnergy_eq_bogoliubov p m

/-- **The conserved mass shell is the quantum heat squared** `H² = E_D²·1 = quantumCarnotHeat(|p|,m)²·1` —
the conserved quantity of the spinor superoperator field *is* the engine's working-substance heat (squared). -/
theorem diracMassShell_eq_heatSq (p : Fin 3 → ℝ) (m : ℝ) :
    diracHamiltonian4 (p 0) (p 1) (p 2) m * diracHamiltonian4 (p 0) (p 1) (p 2) m
      = ((quantumCarnotHeat (helicityMomentum p) m ^ 2 : ℝ) : ℂ) • (1 : MatC) := by
  rw [diracHamiltonian4_sq_energy, diracHeat_eq_quantumCarnotHeat]

/-! ## §D — both thermodynamic laws on the spinor field -/

/-- **[The two laws on the Dirac spinor field]** The spinor superoperator field records both thermodynamic
laws: the **first law** is its self-conservation `[H,H] = 0` (`EnergyConserving`, the Dirac Hamiltonian's
energy is conserved under its own Heisenberg flow), the **second law** is the quantum-Boltzmann H-theorem
capping the efficiency at Carnot. The working substance is the Dirac mass-shell heat `E_D = √(p²+m²)`. -/
theorem dirac_spinor_engine_two_laws (p1 p2 p3 m : ℝ) {ι : Type*} [Fintype ι]
    (Qh Th Qc Tc : ℝ) (hTh : 0 < Th) (hTc : 0 < Tc) (hQh : 0 < Qh) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hident : entropyProduction Qh Th Qc Tc
      = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i)) :
    EnergyConserving (diracHamiltonian4 p1 p2 p3 m) (diracHamiltonian4 p1 p2 p3 m)
      ∧ engineEfficiency Qh Qc ≤ carnotEfficiency Th Tc :=
  quantumBoltzmann_engine_two_laws (diracHamiltonian4 p1 p2 p3 m) Qh Th Qc Tc hTh hTc hQh a b ha hb
    hident

/-- **[The complete spinor superoperator engine] Every established fact at once.** For a Dirac mode of
momentum `p` and mass `m`, with engine heats whose entropy production realizes the quantum-Boltzmann
H-theorem sum, the spinor superoperator field `ad_H` satisfies *all* of:

* **(i)** it annihilates its own generator `ad_{H(p)} H(p) = 0` (the field is conservative);
* **(ii)** the **first law** `EnergyConserving H H` (`[H,H] = 0`);
* **(iii)** its conserved energy is the engine's quantum heat `E_D = √(p²+m²) = quantumCarnotHeat(|p|,m)`;
* **(iv)** the conserved **mass shell** is that heat squared `H² = quantumCarnotHeat(|p|,m)²·1`;
* **(v)** the heat is **time-reversal even** `Q(−|p|) = Q(|p|)` — the reversible mass shell;
* **(vi)** the **second law** — the Carnot bound `η ≤ 1 − T_c/T_h`.

This is the full statement: one superoperator field, both thermodynamic laws, the Dirac mass shell as the
reversible working substance. -/
theorem dirac_spinor_engine_complete (p : Fin 3 → ℝ) (m : ℝ) {ι : Type*} [Fintype ι]
    (Qh Th Qc Tc : ℝ) (hTh : 0 < Th) (hTc : 0 < Tc) (hQh : 0 < Qh) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hident : entropyProduction Qh Th Qc Tc
      = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i)) :
    diracSpinorField (p 0) (p 1) (p 2) m (diracHamiltonian4 (p 0) (p 1) (p 2) m) = 0
      ∧ EnergyConserving (diracHamiltonian4 (p 0) (p 1) (p 2) m)
          (diracHamiltonian4 (p 0) (p 1) (p 2) m)
      ∧ diracEnergy (p 0) (p 1) (p 2) m = quantumCarnotHeat (helicityMomentum p) m
      ∧ diracHamiltonian4 (p 0) (p 1) (p 2) m * diracHamiltonian4 (p 0) (p 1) (p 2) m
          = ((quantumCarnotHeat (helicityMomentum p) m ^ 2 : ℝ) : ℂ) • (1 : MatC)
      ∧ quantumCarnotHeat (-(helicityMomentum p)) m = quantumCarnotHeat (helicityMomentum p) m
      ∧ engineEfficiency Qh Qc ≤ carnotEfficiency Th Tc :=
  ⟨diracField_self_zero (p 0) (p 1) (p 2) m,
   diracField_energyConserving (p 0) (p 1) (p 2) m,
   diracHeat_eq_quantumCarnotHeat p m,
   diracMassShell_eq_heatSq p m,
   quantumCarnotHeat_timeReversal (helicityMomentum p) m,
   (dirac_spinor_engine_two_laws (p 0) (p 1) (p 2) m Qh Th Qc Tc hTh hTc hQh a b ha hb hident).2⟩

end Physlib.QuantumMechanics.ComplexAction.Dirac.SpinorSuperoperatorEngine

end
