/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic
public import Physlib.Units.LTMCTIDimensionBase
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
open LTMCTUnitChoices Dimensionful CarriesDimension

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

The following named `Dimension LTMCTIDimensionBase` values catalogue the standard derived
dimensions of the central physical quantities in the action / energy
family (ISQ derived from `{L, T, M, C, Θ, I}` in `Physlib.Units.Dimension`).
They are the dimensional skeletons consumed by typed `WithDim`
quantities in this file and downstream.
-/

/-- **Action dimension** `[A] = M·L²·T⁻¹`. -/
def dimAction : Dimension LTMCTIDimensionBase := LTMCTI.M𝓭 * LTMCTI.L𝓭 * LTMCTI.L𝓭 * LTMCTI.T𝓭⁻¹

/-- **Energy dimension** `[E] = M·L²·T⁻²`. -/
def dimEnergy : Dimension LTMCTIDimensionBase := LTMCTI.M𝓭 * LTMCTI.L𝓭 * LTMCTI.L𝓭 * LTMCTI.T𝓭⁻¹ * LTMCTI.T𝓭⁻¹

/-- **Planck constant ℏ** has action dimension. -/
def dimℏ : Dimension LTMCTIDimensionBase := dimAction

/-- **Boltzmann constant** `k_B` carries `[E·Θ⁻¹·I⁻¹]` — the
*information-aware* SI extension making `S = k_B · I` dimensionally
consistent. -/
def dimkB : Dimension LTMCTIDimensionBase :=
  dimEnergy * LTMCTI.Θ𝓭⁻¹ * LTMCTI.I𝓭⁻¹

/-- **Speed dimension** `[c] = L·T⁻¹`. -/
def dimSpeed : Dimension LTMCTIDimensionBase := LTMCTI.L𝓭 * LTMCTI.T𝓭⁻¹

/-- **Informational imaginary action dimension** `[S_I] = M·L²·T⁻¹·I`. -/
def dimImaginaryAction : Dimension LTMCTIDimensionBase := dimAction * LTMCTI.I𝓭

/-! ### Component lemmas -/

@[simp] lemma dimAction_length : dimAction.exponent .length = 2 := by
  simp [dimAction]; norm_num
@[simp] lemma dimAction_time : dimAction.exponent .time = -1 := by
  simp [dimAction]
@[simp] lemma dimAction_mass : dimAction.exponent .mass = 1 := by
  simp [dimAction]
@[simp] lemma dimAction_charge : dimAction.exponent .charge = 0 := by
  simp [dimAction]
@[simp] lemma dimAction_temperature : dimAction.exponent .temperature = 0 := by
  simp [dimAction]
@[simp] lemma dimAction_information : dimAction.exponent .information = 0 := by
  simp [dimAction]

@[simp] lemma dimEnergy_length : dimEnergy.exponent .length = 2 := by
  simp [dimEnergy]; norm_num
@[simp] lemma dimEnergy_time : dimEnergy.exponent .time = -2 := by
  simp [dimEnergy]; norm_num
@[simp] lemma dimEnergy_mass : dimEnergy.exponent .mass = 1 := by
  simp [dimEnergy]
@[simp] lemma dimEnergy_charge : dimEnergy.exponent .charge = 0 := by
  simp [dimEnergy]
@[simp] lemma dimEnergy_temperature : dimEnergy.exponent .temperature = 0 := by
  simp [dimEnergy]
@[simp] lemma dimEnergy_information : dimEnergy.exponent .information = 0 := by
  simp [dimEnergy]

@[simp] lemma dimℏ_eq_dimAction : dimℏ = dimAction := rfl

/-- **Boltzmann maps `k_B · Θ · I = E`** —
`[k_B] · [Θ] · [I] = (E·Θ⁻¹·I⁻¹) · Θ · I = E`. -/
lemma dimkB_times_temperature_times_information_eq_dimEnergy :
    dimkB * LTMCTI.Θ𝓭 * LTMCTI.I𝓭 = dimEnergy := by
  ext b <;> cases b <;> simp [dimkB, dimEnergy]
