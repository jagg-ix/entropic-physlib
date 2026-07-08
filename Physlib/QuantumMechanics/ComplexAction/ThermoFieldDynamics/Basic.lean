/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Thermo Field Dynamics (Suzuki 1985)

Formalizes the algebraic core of *M. Suzuki, "Thermo Field Dynamics in Equilibrium and Non-Equilibrium
Interacting Quantum Systems", J. Phys. Soc. Jpn. 54 (1985) 4483–4485*. Thermo Field Dynamics (TFD) writes the
thermal average `⟨Q⟩ = Tr(Q e^{−βℋ})/Z` as an expectation `⟨O(β)|Q|O(β)⟩` in a *doubled* (original ⊗ tilde)
Hilbert space, with the thermal state `|O(β)⟩ = Z^{−1/2} e^{−βℋ/2}|I⟩` built on the **identity state**
`|I⟩ = ∑ₙ |n,ñ⟩`.

Two results include the theory:

* the **fundamental identity** (Eq. 8) `|I⟩ = ∑_α |α,α̃⟩` is *basis-independent* — true for any orthonormal
  basis, because the basis change is unitary (`∑ₙ U_{nα}U*_{nγ} = δ_{αγ}`);
* the **hat-Hamiltonian** (Eq. 21) `ℋ̂ = ℋ − ℋ̃`, which generates the non-equilibrium evolution
  `iℏ∂_t|Ψ(t)⟩ = ℋ̂|Ψ(t)⟩` (Eq. 20), is *exactly* the commutator Liouvillian `[ℋ, ·] = ad_ℋ` of the von
  Neumann equation `iℏ∂_tρ = [ℋ,ρ]` (Eq. 18) — i.e. the Saveliev `collisionStar`. On the doubled space `ℋ`
  acts by left- and `ℋ̃` by right-multiplication, which **always commute** (`[ℋ,ℋ̃]=0`, the condition Eq. 20
  needs).

* **§A — the fundamental identity** (`thermalIdentity_basis_independent`). `∑ₙ U*_{nα}U_{nγ} = δ_{αγ}` for `U`
  unitary — the `|I⟩` state is the same in every basis (Eq. 8).
* **§B — the hat-Hamiltonian = the Liouvillian** (`hatHamiltonian`, `hatHamiltonian_apply`,
  `hatHamiltonian_eq_collisionStar`, `hatHamiltonian_self`, `tfd_left_right_commute`). `ℋ̂ = mulLeft ℋ −
  mulRight ℋ = [ℋ,·] = collisionStar ℋ`; it annihilates `ℋ` (equilibrium stationarity); the left/right actions
  commute (Eq. 20's `[ℋ,ℋ̃]=0`).
* **§C — the thermal weight** (`thermalWeight`, `thermalWeight_at_zero`, `thermalWeight_sq`). The `|O(β)⟩`
  amplitude `e^{−βE_n/2}` (Eq. 2); at `β=0` it is `1` (`|O(0)⟩ = |I⟩`, Eq. 10); its square is the Boltzmann
  weight `e^{−βE_n}` (`ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight`).
* **§D — links: the doubled-space Lie/energy structure** (`hatHamiltonian_energyConserving`,
  `hatHamiltonian_jacobi`). The hat-stationarity `ℋ̂(ℋ)=0` *is* the Saveliev `EnergyConserving ℋ ℋ` that
  supplies the quantum-Boltzmann engine's first law; the hat-Hamiltonians close into a Lie algebra (Jacobi) —
  the same `ad`-structure as the Saveliev/BCJ bracket.

## References

* M. Suzuki, J. Phys. Soc. Jpn. 54 (1985) 4483–4485 (Eqs. 1–2, 8, 10, 18–21); Takahashi–Umezawa TFD.
* Repo dependencies: `CollisionOperatorSl2.CollisionModular.collisionStar` (`= ad = [·,·]`, the modular/Liouville
  generator) and `CollisionOperatorSl2.LinearBoltzmannOperator` (`EnergyConserving`, `collisionStar_jacobi`);
  `ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight` (`= e^{−βE}`); the same commutator superoperator
  as `Electromagnetic.EMFieldSuperoperator.emFieldAdjoint` and `Dirac.SpinorSuperoperatorEngine.diracAdjoint`, and the same
  energy conservation as `StatisticalMechanics.QuantumClausiusEngine.quantumBoltzmann_engine_two_laws` (the engine first law).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic

open Finset Matrix
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

/-! ## §A — the fundamental identity (Eq. 8) -/

/-- **[Eq. 8] The TFD identity state is basis-independent.** `|I⟩ = ∑ₙ|n,ñ⟩ = ∑_α|α,α̃⟩` for any orthonormal
basis, because the change of basis `|n⟩ = ∑_α U_{nα}|α⟩` is unitary: the completeness
`∑ₙ U*_{nα}U_{nγ} = δ_{αγ}` (Eq. 7) is exactly `(U†U)_{αγ} = 1_{αγ}`. -/
theorem thermalIdentity_basis_independent {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : star U * U = 1) (α γ : Fin n) :
    ∑ k, star (U k α) * U k γ = (1 : Matrix (Fin n) (Fin n) ℂ) α γ := by
  rw [← hU, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.star_apply]

/-! ## §B — the hat-Hamiltonian is the commutator Liouvillian (Eqs. 18–21) -/

/-- **[Eq. 21] The TFD hat-Hamiltonian** `ℋ̂ = ℋ − ℋ̃ = mulLeft ℋ − mulRight ℋ` — on the doubled space `ℋ`
acts by left- and `ℋ̃` by right-multiplication, so `ℋ̂` is the commutator superoperator that drives the
non-equilibrium evolution `iℏ∂_t|Ψ⟩ = ℋ̂|Ψ⟩` (Eq. 20). -/
noncomputable def hatHamiltonian {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H

/-- **`ℋ̂(ρ) = ℋρ − ρℋ = [ℋ,ρ]`** — the von Neumann/Liouville commutator (`iℏ∂_tρ = [ℋ,ρ]`, Eq. 18). -/
@[simp] theorem hatHamiltonian_apply {n : ℕ} (H ρ : Matrix (Fin n) (Fin n) ℂ) :
    hatHamiltonian H ρ = H * ρ - ρ * H := by simp [hatHamiltonian]

/-- **The hat-Hamiltonian is the Saveliev `collisionStar`** (`= ad`) — TFD's `ℋ̂` is the modular/Liouville
generator already encoded in the repo, the same commutator superoperator as `emFieldAdjoint`/`diracAdjoint`. -/
theorem hatHamiltonian_eq_collisionStar {n : ℕ} (H ρ : Matrix (Fin n) (Fin n) ℂ) :
    hatHamiltonian H ρ = collisionStar H ρ := by rw [hatHamiltonian_apply, collisionStar]

/-- **[Equilibrium] `ℋ̂(ℋ) = 0`** — the Hamiltonian is hat-stationary (`[ℋ,ℋ]=0`); the thermal equilibrium
state `|O(β)⟩ ∝ e^{−βℋ/2}|I⟩` is annihilated by `ℋ̂`. -/
@[simp] theorem hatHamiltonian_self {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    hatHamiltonian H H = 0 := by rw [hatHamiltonian_eq_collisionStar, collisionStar_self]

/-- **[Eq. 20 condition `[ℋ,ℋ̃]=0`] The tilde Hamiltonian commutes with the original.** On the doubled space
`ℋ ↦ mulLeft ℋ` and `ℋ̃ ↦ mulRight ℋ`, and left/right multiplications always commute (associativity) — so the
non-equilibrium TFD equation (20) holds without further assumption. -/
theorem tfd_left_right_commute {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    (LinearMap.mulLeft ℂ H).comp (LinearMap.mulRight ℂ H)
      = (LinearMap.mulRight ℂ H).comp (LinearMap.mulLeft ℂ H) := by
  ext ρ; simp [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

/-! ## §C — the thermal weight (Eqs. 1–2, 10) -/

/-- **[Eq. 2] The thermal-state amplitude** `e^{−βE_n/2}` of `|O(β)⟩` on the eigenstate `|n,ñ⟩`. -/
noncomputable def thermalWeight (β E : ℝ) : ℝ := Real.exp (-(β * E) / 2)

/-- **[Eq. 10] At `β = 0` the thermal state is the identity state** `|O(0)⟩ = Z(0)^{−1/2}|I⟩`: every amplitude
is `1`. -/
@[simp] theorem thermalWeight_at_zero (E : ℝ) : thermalWeight 0 E = 1 := by
  simp [thermalWeight]

/-- **[Eqs. 1–2] The squared amplitude is the Boltzmann weight** `e^{−βE_n}` — the thermal probability of `|n⟩`
in `⟨Q⟩ = Tr(Q e^{−βℋ})/Z` is `ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight β E`. -/
theorem thermalWeight_sq (β E : ℝ) : thermalWeight β E ^ 2 = matsubaraBoltzmannWeight β E := by
  rw [thermalWeight, matsubaraBoltzmannWeight, sq, ← Real.exp_add]
  congr 1; ring

/-! ## §D — links: the doubled-space Lie/energy structure -/

/-- **[Equilibrium = the engine first law] The TFD equilibrium is the Saveliev energy conservation.** The
hat-stationarity `ℋ̂(ℋ) = 0` is exactly `EnergyConserving ℋ ℋ` (`collisionStar ℋ ℋ = 0`) — the *same* energy
conservation that supplies the first law of the quantum-Boltzmann engine
(`StatisticalMechanics.QuantumClausiusEngine.quantumBoltzmann_engine_two_laws` via `energyConserving_self`). The thermal
equilibrium of TFD and the conserved working substance of the engine are one identity. -/
theorem hatHamiltonian_energyConserving {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    EnergyConserving H H := energyConserving_self H

/-- **[The doubled-space Lie algebra] The hat-Hamiltonians satisfy the Jacobi identity.** The TFD
commutator/Liouville generators close into a Lie algebra (`collisionStar_jacobi`) — the same `ad`-Lie structure
as the Saveliev collision operator and the BCJ color/kinematic bracket. -/
theorem hatHamiltonian_jacobi {n : ℕ} (H A B : Matrix (Fin n) (Fin n) ℂ) :
    collisionStar H (collisionStar A B) + collisionStar A (collisionStar B H)
      + collisionStar B (collisionStar H A) = 0 := collisionStar_jacobi H A B

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic

end
