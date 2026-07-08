/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic
/-!

# Energy

In this module we define the dimensionful type corresponding to an energy.
We define specific instances of energy.

-/

@[expose] public section

open Dimension
open NNReal

/-- Energy as a dimensional quantity with dimension `MLT⁻2`.. -/
abbrev DimEnergy : Type := Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

namespace DimEnergy
open UnitChoices Dimensionful CarriesDimension

/-- The dimensional energy corresponding to 1 joule, J. -/
noncomputable def joule : DimEnergy := toDimensionful SI ⟨1⟩

/-- The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J. -/
noncomputable def electronVolt : DimEnergy := toDimensionful SI ⟨1.602176634e-19⟩

/-- The dimensional energy corresponding to 1 calorie, 4.184 J. -/
noncomputable def calorie : DimEnergy := toDimensionful SI ⟨4.184⟩

/-- The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J). -/
noncomputable def kilowattHour : DimEnergy := toDimensionful SI ⟨3600000⟩

end DimEnergy

/-! ## Derived dimensions of action, energy, ℏ, k_B, and speed

The following named `Dimension` values catalogue the standard derived
dimensions of the central physical quantities in the action / energy
family (ISQ derived from `{L, T, M, C, Θ, I}` in `Physlib.Units.Dimension`).
They are the dimensional skeletons consumed by typed `WithDim`
quantities in this file and downstream.
-/

/-- **Action dimension** `[A] = M·L²·T⁻¹`. -/
def dimAction : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- **Energy dimension** `[E] = M·L²·T⁻²`. -/
def dimEnergy : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- **Planck constant ℏ** has action dimension. -/
def dimℏ : Dimension := dimAction

/-- **Boltzmann constant** `k_B` has dimension `[E·Θ⁻¹·I⁻¹]` — the
*information-aware* SI extension making `S = k_B · I` dimensionally
consistent. -/
def dimkB : Dimension :=
  dimEnergy * Θ𝓭⁻¹ * I𝓭⁻¹

/-- **Speed dimension** `[c] = L·T⁻¹`. -/
def dimSpeed : Dimension := L𝓭 * T𝓭⁻¹

/-- **Informational imaginary action dimension** `[S_I] = M·L²·T⁻¹·I`. -/
def dimImaginaryAction : Dimension := dimAction * I𝓭

/-! ### Component lemmas -/

@[simp] lemma dimAction_length : dimAction.length = 2 := by
  simp [dimAction]; norm_num
@[simp] lemma dimAction_time : dimAction.time = -1 := by
  simp [dimAction]
@[simp] lemma dimAction_mass : dimAction.mass = 1 := by
  simp [dimAction]
@[simp] lemma dimAction_charge : dimAction.charge = 0 := by
  simp [dimAction]
@[simp] lemma dimAction_temperature : dimAction.temperature = 0 := by
  simp [dimAction]
@[simp] lemma dimAction_information : dimAction.information = 0 := by
  simp [dimAction]

@[simp] lemma dimEnergy_length : dimEnergy.length = 2 := by
  simp [dimEnergy]; norm_num
@[simp] lemma dimEnergy_time : dimEnergy.time = -2 := by
  simp [dimEnergy]; norm_num
@[simp] lemma dimEnergy_mass : dimEnergy.mass = 1 := by
  simp [dimEnergy]
@[simp] lemma dimEnergy_charge : dimEnergy.charge = 0 := by
  simp [dimEnergy]
@[simp] lemma dimEnergy_temperature : dimEnergy.temperature = 0 := by
  simp [dimEnergy]
@[simp] lemma dimEnergy_information : dimEnergy.information = 0 := by
  simp [dimEnergy]

@[simp] lemma dimℏ_eq_dimAction : dimℏ = dimAction := rfl

/-- **Boltzmann maps `k_B · Θ · I = E`** —
`[k_B] · [Θ] · [I] = (E·Θ⁻¹·I⁻¹) · Θ · I = E`. -/
theorem dimkB_times_temperature_times_information_eq_dimEnergy :
    dimkB * Θ𝓭 * I𝓭 = dimEnergy := by
  ext <;> simp [dimkB, dimEnergy]
