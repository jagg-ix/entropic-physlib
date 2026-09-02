/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure

/-!
# Functorial conditioning and calibrated dynamics

This module proves three consequences of the merged finite-conditioning and
three-clock calibration interfaces:

1. exact conditioning is stable under arbitrary deterministic post-processing;
2. every observable or predicate has the same value on conditioned and direct
   system states; and
3. Page--Wootters endomorphisms conjugate through the composite clock
   equivalence, preserving identity and composition.

The module does not construct the underlying conditioning equality or physical
clock calibration. It proves what follows functorially once those premises are
supplied.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure

variable {Global Clock System Target Observable : Type*}
  [NormedAddCommGroup Global] [InnerProductSpace ℂ Global]

namespace FiniteConditioningCertificate

/-- Post-process both conditioned and direct states through the same function. -/
def mapSystem
    (C : FiniteConditioningCertificate Global Clock System)
    (f : System → Target) :
    FiniteConditioningCertificate Global Clock Target where
  constraint := C.constraint
  historyState := C.historyState
  history_isPhysical := C.history_isPhysical
  conditionedState := fun τ => f (C.conditionedState τ)
  directState := fun τ => f (C.directState τ)
  conditioning_eq_direct := fun τ => congrArg f (C.conditioning_eq_direct τ)

@[simp] theorem mapSystem_conditionedState
    (C : FiniteConditioningCertificate Global Clock System)
    (f : System → Target) (τ : Clock) :
    (C.mapSystem f).conditionedState τ = f (C.conditionedState τ) := rfl

@[simp] theorem mapSystem_directState
    (C : FiniteConditioningCertificate Global Clock System)
    (f : System → Target) (τ : Clock) :
    (C.mapSystem f).directState τ = f (C.directState τ) := rfl

/-- Every deterministic observable agrees exactly on conditioned and direct
states. -/
theorem observable_transport
    (C : FiniteConditioningCertificate Global Clock System)
    (O : System → Observable) (τ : Clock) :
    O (C.conditionedState τ) = O (C.directState τ) :=
  congrArg O (C.conditioning_eq_direct τ)

/-- Every state predicate is preserved by exact conditioning. -/
theorem predicate_transport
    (C : FiniteConditioningCertificate Global Clock System)
    (P : System → Prop) (τ : Clock) :
    P (C.conditionedState τ) ↔ P (C.directState τ) := by
  rw [C.conditioning_eq_direct τ]

/-- Post-processing composes exactly. -/
theorem mapSystem_comp
    (C : FiniteConditioningCertificate Global Clock System)
    (f : System → Target) (g : Target → Observable) :
    (C.mapSystem f).mapSystem g = C.mapSystem (g ∘ f) := rfl

end FiniteConditioningCertificate

namespace ThreeClockCalibration

variable {PW Modular Entropic : Type*}

/-- Conjugate a Page--Wootters endomorphism through the composite
Page--Wootters/entropic calibration. -/
def conjugatePWEndomorphism
    (C : ThreeClockCalibration PW Modular Entropic)
    (step : PW → PW) : Entropic → Entropic :=
  fun τ => C.pwToEntropic (step (C.pwToEntropic.symm τ))

@[simp] theorem conjugatePWEndomorphism_apply
    (C : ThreeClockCalibration PW Modular Entropic)
    (step : PW → PW) (τ : PW) :
    C.conjugatePWEndomorphism step (C.pwToEntropic τ) =
      C.pwToEntropic (step τ) := by
  simp only [conjugatePWEndomorphism, Equiv.symm_apply_apply]

/-- Conjugation preserves the identity endomorphism. -/
theorem conjugatePWEndomorphism_id
    (C : ThreeClockCalibration PW Modular Entropic) :
    C.conjugatePWEndomorphism id = id := by
  funext τ
  simp only [conjugatePWEndomorphism, id_eq, Equiv.apply_symm_apply]

/-- Conjugation preserves composition of endomorphisms. -/
theorem conjugatePWEndomorphism_comp
    (C : ThreeClockCalibration PW Modular Entropic)
    (f g : PW → PW) :
    C.conjugatePWEndomorphism (f ∘ g) =
      C.conjugatePWEndomorphism f ∘ C.conjugatePWEndomorphism g := by
  funext τ
  simp only [conjugatePWEndomorphism, Function.comp_apply, Equiv.symm_apply_apply]

/-- Conjugation by a clock equivalence is injective on endomorphisms. -/
theorem conjugatePWEndomorphism_injective
    (C : ThreeClockCalibration PW Modular Entropic) :
    Function.Injective C.conjugatePWEndomorphism := by
  intro f g h
  funext τ
  apply C.pwToEntropic.injective
  have hτ := congrFun h (C.pwToEntropic τ)
  simpa only [conjugatePWEndomorphism, Equiv.symm_apply_apply] using hτ

end ThreeClockCalibration

end Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure
