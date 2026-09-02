/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure

/-!
# Conditioned dynamics, proper-time completion, and ordered clock calibration

This module advances the three-clock closure in three directions:

1. an exact direct evolution law is transported through a proved finite
   Page--Wootters conditioning equality;
2. the Page--Wootters/modular/entropic calibration chain is completed with an
   explicit entropic/proper-time equivalence; and
3. strict monotonicity of the pairwise calibrations is composed to prove that
   physical clock order is preserved from relational time through proper time.

The calibration maps and their monotonicity remain explicit physical premises.
The theorems prove the resulting dynamics and composition laws without promoting
those premises to independently derived physical identifications.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics

open Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure

/-- A finite Page--Wootters conditioning certificate together with a direct
one-step system evolution law. -/
structure ConditionedEvolutionCertificate
    (Global Clock System : Type*)
    [NormedAddCommGroup Global] [InnerProductSpace ℂ Global] where
  conditioning : FiniteConditioningCertificate Global Clock System
  advance : Clock → Clock
  systemStep : System → System
  direct_evolves : ∀ τ,
    conditioning.directState (advance τ) =
      systemStep (conditioning.directState τ)

namespace ConditionedEvolutionCertificate

variable {Global Clock System : Type*}
  [NormedAddCommGroup Global] [InnerProductSpace ℂ Global]

/-- The direct evolution law transports exactly to the conditioned states. -/
theorem conditioned_evolves
    (C : ConditionedEvolutionCertificate Global Clock System) (τ : Clock) :
    C.conditioning.conditionedState (C.advance τ) =
      C.systemStep (C.conditioning.conditionedState τ) := by
  calc
    C.conditioning.conditionedState (C.advance τ)
        = C.conditioning.directState (C.advance τ) :=
          C.conditioning.conditioning_eq_direct _
    _ = C.systemStep (C.conditioning.directState τ) := C.direct_evolves τ
    _ = C.systemStep (C.conditioning.conditionedState τ) :=
          congrArg C.systemStep (C.conditioning.conditioning_eq_direct τ).symm

/-- The conditioned trajectory and direct trajectory agree before and after one
clock advance. -/
theorem conditioned_step_pair
    (C : ConditionedEvolutionCertificate Global Clock System) (τ : Clock) :
    C.conditioning.conditionedState τ = C.conditioning.directState τ
      ∧ C.conditioning.conditionedState (C.advance τ) =
          C.conditioning.directState (C.advance τ) :=
  ⟨C.conditioning.conditioning_eq_direct τ,
    C.conditioning.conditioning_eq_direct (C.advance τ)⟩

end ConditionedEvolutionCertificate

/-- Explicit invertible calibration from Page--Wootters time through modular and
entropic time to physical proper time. -/
structure FourClockCalibration
    (PW Modular Entropic Proper : Type*) where
  threeClock : ThreeClockCalibration PW Modular Entropic
  entropicToProper : Entropic ≃ Proper

namespace FourClockCalibration

variable {PW Modular Entropic Proper : Type*}

/-- Modular-to-proper calibration obtained through entropic time. -/
def modularToProper
    (C : FourClockCalibration PW Modular Entropic Proper) : Modular ≃ Proper :=
  C.threeClock.modularToEntropic.trans C.entropicToProper

/-- Page--Wootters-to-proper calibration through the full clock chain. -/
def pwToProper
    (C : FourClockCalibration PW Modular Entropic Proper) : PW ≃ Proper :=
  C.threeClock.pwToEntropic.trans C.entropicToProper

@[simp] theorem pwToProper_apply
    (C : FourClockCalibration PW Modular Entropic Proper) (τ : PW) :
    C.pwToProper τ =
      C.entropicToProper
        (C.threeClock.modularToEntropic (C.threeClock.pwToModular τ)) := rfl

/-- The two explicit paths from Page--Wootters time to proper time commute. -/
theorem pw_modular_entropic_proper_commutes
    (C : FourClockCalibration PW Modular Entropic Proper) (τ : PW) :
    C.pwToProper τ =
      C.modularToProper (C.threeClock.pwToModular τ) := rfl

@[simp] theorem pwToProper_symm_apply_apply
    (C : FourClockCalibration PW Modular Entropic Proper) (τ : PW) :
    C.pwToProper.symm (C.pwToProper τ) = τ :=
  C.pwToProper.symm_apply_apply τ

/-- The complete calibration is injective: distinct relational readings cannot
collapse to one proper-time reading. -/
theorem pwToProper_injective
    (C : FourClockCalibration PW Modular Entropic Proper) :
    Function.Injective C.pwToProper :=
  C.pwToProper.injective

/-- Every reading in the declared proper-time carrier has a relational preimage. -/
theorem pwToProper_surjective
    (C : FourClockCalibration PW Modular Entropic Proper) :
    Function.Surjective C.pwToProper :=
  C.pwToProper.surjective

end FourClockCalibration

/-- A four-clock calibration whose physical maps preserve strict temporal order. -/
structure OrderedFourClockCalibration
    (PW Modular Entropic Proper : Type*)
    [Preorder PW] [Preorder Modular] [Preorder Entropic] [Preorder Proper] where
  calibration : FourClockCalibration PW Modular Entropic Proper
  pwToModular_strictMono : StrictMono calibration.threeClock.pwToModular
  modularToEntropic_strictMono : StrictMono calibration.threeClock.modularToEntropic
  entropicToProper_strictMono : StrictMono calibration.entropicToProper

namespace OrderedFourClockCalibration

variable {PW Modular Entropic Proper : Type*}
  [Preorder PW] [Preorder Modular] [Preorder Entropic] [Preorder Proper]

/-- Strict monotonicity composes across the complete relational-to-proper chain. -/
theorem pwToProper_strictMono
    (C : OrderedFourClockCalibration PW Modular Entropic Proper) :
    StrictMono C.calibration.pwToProper :=
  C.entropicToProper_strictMono.comp
    (C.modularToEntropic_strictMono.comp C.pwToModular_strictMono)

/-- Earlier Page--Wootters readings map to earlier proper-time readings. -/
theorem pw_lt_implies_proper_lt
    (C : OrderedFourClockCalibration PW Modular Entropic Proper)
    {τ₁ τ₂ : PW} (h : τ₁ < τ₂) :
    C.calibration.pwToProper τ₁ < C.calibration.pwToProper τ₂ :=
  C.pwToProper_strictMono h

/-- Strict clock order prevents collapse after complete physical calibration. -/
theorem proper_readings_ne_of_pw_lt
    (C : OrderedFourClockCalibration PW Modular Entropic Proper)
    {τ₁ τ₂ : PW} (h : τ₁ < τ₂) :
    C.calibration.pwToProper τ₁ ≠ C.calibration.pwToProper τ₂ :=
  ne_of_lt (C.pwToProper_strictMono h)

end OrderedFourClockCalibration

end Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics
