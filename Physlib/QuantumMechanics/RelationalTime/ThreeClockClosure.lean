/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Physlib.QuantumMechanics.RelationalTime.EntropicThermalComplementarity

/-!
# Three-clock conditioning, separation, and calibration

This module closes three public interfaces left downstream by the existing
Page--Wootters and modular/entropic files:

1. an exact finite conditioning certificate over a physical Hamiltonian-constraint state;
2. a theorem that entropy-preserving modular flow cannot equal a strictly
   entropy-producing flow away from equilibrium; and
3. composable equivalences between Page--Wootters, modular, and entropic clock
   parameters.

The conditioning certificate records a consumer-proved conditioning equality;
it does not manufacture a tensor-factorization theorem. The non-coincidence and
calibration results are actual theorems derived from the stated fields.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure

open Physlib.QuantumMechanics.RelationalTime

/-- Exact finite Page--Wootters conditioning data for a physical history state. -/
structure FiniteConditioningCertificate
    (Global Clock System : Type*)
    [NormedAddCommGroup Global] [InnerProductSpace ℂ Global] where
  constraint : HamiltonianConstraint Global
  historyState : Global
  history_isPhysical : constraint.IsPhysical historyState
  conditionedState : Clock → System
  directState : Clock → System
  conditioning_eq_direct : ∀ τ, conditionedState τ = directState τ

namespace FiniteConditioningCertificate

variable {Global Clock System : Type*}
  [NormedAddCommGroup Global] [InnerProductSpace ℂ Global]

/-- Every clock reading recovers the declared direct system state exactly. -/
theorem all_conditioned_states_recovered
    (C : FiniteConditioningCertificate Global Clock System) :
    ∀ τ, C.conditionedState τ = C.directState τ :=
  C.conditioning_eq_direct

/-- The history state used by the conditioning certificate satisfies the
Page--Wootters Hamiltonian constraint. -/
theorem history_satisfies_constraint
    (C : FiniteConditioningCertificate Global Clock System) :
    C.constraint.H_total C.historyState = 0 :=
  C.history_isPhysical

end FiniteConditioningCertificate

/-- A shared carrier with entropy-preserving modular flow and strictly
entropy-decreasing entropic flow. -/
structure ReversibleIrreversibleClockCarrier (State Param : Type*) [Zero Param] [LT Param] where
  entropy : State → ℝ
  modularFlow : Param → State → State
  entropicFlow : Param → State → State
  modular_entropy_preserved : ∀ s ρ, entropy (modularFlow s ρ) = entropy ρ
  entropic_entropy_strict : ∀ s ρ, 0 < s → entropy (entropicFlow s ρ) < entropy ρ

namespace ReversibleIrreversibleClockCarrier

variable {State : Type*}

/-- Away from equilibrium, a strictly entropy-producing entropic flow cannot
coincide with an entropy-preserving modular flow at the same positive reading. -/
theorem modularFlow_ne_entropicFlow
    (C : ReversibleIrreversibleClockCarrier State ℝ)
    (s : ℝ) (ρ : State) (hs : 0 < s) :
    C.modularFlow s ρ ≠ C.entropicFlow s ρ := by
  intro h
  have hm := C.modular_entropy_preserved s ρ
  have he := C.entropic_entropy_strict s ρ hs
  rw [← h, hm] at he
  exact (lt_irrefl _ he)

/-- Equality of the two flows forces failure of strict entropy production. -/
theorem coincidence_forces_not_strict
    (C : ReversibleIrreversibleClockCarrier State ℝ)
    (s : ℝ) (ρ : State)
    (h : C.modularFlow s ρ = C.entropicFlow s ρ) :
    ¬ C.entropy (C.entropicFlow s ρ) < C.entropy ρ := by
  rw [← h, C.modular_entropy_preserved]
  exact lt_irrefl _

end ReversibleIrreversibleClockCarrier

/-- Explicit invertible calibration between the three clock parameters. -/
structure ThreeClockCalibration (PW Modular Entropic : Type*) where
  pwToModular : PW ≃ Modular
  modularToEntropic : Modular ≃ Entropic

namespace ThreeClockCalibration

variable {PW Modular Entropic : Type*}

/-- Composite Page--Wootters to entropic calibration. -/
def pwToEntropic
    (C : ThreeClockCalibration PW Modular Entropic) : PW ≃ Entropic :=
  C.pwToModular.trans C.modularToEntropic

@[simp] theorem pwToEntropic_apply
    (C : ThreeClockCalibration PW Modular Entropic) (τ : PW) :
    C.pwToEntropic τ = C.modularToEntropic (C.pwToModular τ) := rfl

@[simp] theorem pwToEntropic_symm_apply_apply
    (C : ThreeClockCalibration PW Modular Entropic) (τ : PW) :
    C.pwToEntropic.symm (C.pwToEntropic τ) = τ :=
  C.pwToEntropic.symm_apply_apply τ

/-- The composite calibration is injective, so distinct relational readings
cannot collapse to one entropic reading. -/
theorem pwToEntropic_injective
    (C : ThreeClockCalibration PW Modular Entropic) :
    Function.Injective C.pwToEntropic :=
  C.pwToEntropic.injective

/-- The composite calibration is surjective onto the declared entropic clock. -/
theorem pwToEntropic_surjective
    (C : ThreeClockCalibration PW Modular Entropic) :
    Function.Surjective C.pwToEntropic :=
  C.pwToEntropic.surjective

end ThreeClockCalibration

end Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure
