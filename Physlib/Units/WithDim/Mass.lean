/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Energy
public import Mathlib.Data.Complex.Basic
/-!

# Mass

In this module we define the dimensionful type `DimMass` corresponding to the
mass of a particle, in an arbitrary (but given) set of units.  Mirrors the
shape of `Physlib.Units.WithDim.Energy.DimEnergy`.

We also expose the **mass ↔ information bridge** behind the
entropic-time *Equation 3* form `M = ℏ · c⁻² · …`: the standard SI mass
dimension `M𝓭` is `dimAction · L𝓭⁻² · T𝓭` (rearranging
`[ℏ] = M·L²·T⁻¹`), so mass values have the same dimensional content as
"action per length-squared, times time".


## References

- **Landauer 1961** — *Irreversibility and Heat Generation in Computing* [bib: `Landauer1961`]
- **Brillouin 1962** — *Science and Information Theory* [bib key needed: `Brillouin1962`]
-/

@[expose] public section

open Dimension
open NNReal

/-- **Mass as a dimensional quantity** with dimension `M`. -/
abbrev DimMass : Type := Dimensionful (WithDim M𝓭 ℝ)

namespace DimMass
open UnitChoices Dimensionful CarriesDimension

/-- The dimensional mass corresponding to 1 kilogram, kg. -/
noncomputable def kilogram : DimMass := toDimensionful SI ⟨1⟩

/-- The dimensional mass corresponding to 1 gram, 10⁻³ kg. -/
noncomputable def gram : DimMass := toDimensionful SI ⟨1e-3⟩

/-- The dimensional mass corresponding to 1 metric tonne, 10³ kg. -/
noncomputable def tonne : DimMass := toDimensionful SI ⟨1e3⟩

/-- The dimensional mass corresponding to the electron rest mass,
9.109 383 7015 × 10⁻³¹ kg. -/
noncomputable def electronMass : DimMass :=
  toDimensionful SI ⟨9.1093837015e-31⟩

/-- The dimensional mass corresponding to the proton rest mass,
1.672 621 923 69 × 10⁻²⁷ kg. -/
noncomputable def protonMass : DimMass :=
  toDimensionful SI ⟨1.67262192369e-27⟩

end DimMass

/-! ## Mass ↔ action / information bridge theorems

In physlib's 6-base `{L, T, M, C, Θ, I}` basis, mass `M𝓭` is a primitive
dimension, *not* derived from information.  The
information-extended ontology (`InformationExtendedBase = {I, T, Q, Θ}`)
treats mass as an emergent quantity (in natural units `c = ℏ = 1`).

We do not collapse the 6-base ontology — we instead expose the
**action-mediated form** of the same identification: `M𝓭` factorises
through `dimAction = M·L²·T⁻¹`, which gives the canonical place where
information enters (the informational imaginary action `S_I = action·I`).

Complex masses do **not** require a complex-valued dimension.  The value
may live in `ℂ`, but the dimension vector remains the ordinary mass
dimension `M𝓭`: `m = m_R + i m_I`, a resonance pole `m - i Γ/2`, and a
Nagao--Nielsen complex mass all have real and imaginary components in
the same mass/energy units.  In natural-unit calculations this same
dimension may be re-expressed as `E/c²` or `ℏω/c²`; that is a derived
identity inside the rational-exponent dimension group, not a new
complex dimension.
-/

/-- **Mass dimension via action and length-time** (Equation 3 form,
rearranged into physlib's ISQ+I basis):
`M = A · L⁻² · T = (M·L²·T⁻¹) · L⁻² · T`.  This is a *re-expression*
of `M𝓭` in terms of derived quantities. -/
theorem M𝓭_eq_dimAction_div_L_sq_times_T :
    M𝓭 = dimAction * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 := by
  ext <;> simp [dimAction]

/-- **Kinematic-viscosity dimensional identity** `[ℏ/m] = L²·T⁻¹`.
This is the dimensional skeleton of the Madelung viscosity `ν = ℏ/(2m)`. -/
theorem dimℏ_div_M𝓭_eq_L_sq_div_T :
    dimℏ * M𝓭⁻¹ = L𝓭 * L𝓭 * T𝓭⁻¹ := by
  ext <;> simp [dimℏ, dimAction]

/-- **Brillouin / Landauer identity** `[S_I / ℏ] = I` — the informational
imaginary action divided by the Planck action is dimensionally the
information base. -/
theorem dimImaginaryAction_div_dimℏ_eq_I𝓭 :
    dimImaginaryAction * dimℏ⁻¹ = I𝓭 := by
  ext <;> simp [dimImaginaryAction, dimℏ, dimAction]

/-- **Mass dimension at the `DimMass`-typed level.**  Restates
`M𝓭_eq_dimAction_div_L_sq_times_T` for the dimension represented by
`DimMass`. -/
theorem dim_DimMass_eq_dimAction_div_L_sq_times_T :
    (dim (WithDim M𝓭 ℝ) : Dimension) = dimAction * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 := by
  simp [WithDim.dim_apply, M𝓭_eq_dimAction_div_L_sq_times_T]

/-! ## Complex-valued mass keeps the ordinary mass dimension -/

/-- **Complex-valued mass**: the value field is complex, but the assigned dimension is still the ordinary mass dimension `M𝓭`. -/
abbrev ComplexDimMass : Type := WithDim M𝓭 ℂ

/-- A complex-valued mass has exactly the same dimension as an
ordinary real-valued mass.  Complexity belongs to the coefficient field,
not to the dimension vector. -/
theorem dim_ComplexDimMass_eq_DimMass :
    (dim (WithDim M𝓭 ℂ) : Dimension) = (dim (WithDim M𝓭 ℝ) : Dimension) := by
  simp [WithDim.dim_apply]

/-- The real and imaginary parts of a complex mass are both mass
components: `[m_R] = [m_I] = M`. -/
theorem complexMass_parts_same_dimension :
    (dim (WithDim M𝓭 ℝ) : Dimension) = M𝓭
      ∧ (dim (WithDim M𝓭 ℝ) : Dimension) = M𝓭
      ∧ (dim (WithDim M𝓭 ℂ) : Dimension) = M𝓭 := by
  simp [WithDim.dim_apply]

/-- **Mass from energy**: `M = E · c⁻²`.  This is the dimensional
skeleton of `m = E/c²`, including complex rest energy values. -/
theorem M𝓭_eq_dimEnergy_div_c_sq :
    M𝓭 = dimEnergy * dimSpeed⁻¹ * dimSpeed⁻¹ := by
  ext <;> simp [dimEnergy, dimSpeed]

/-- **Energy from mass**: `E = M · c²`. -/
theorem dimEnergy_eq_M𝓭_mul_c_sq :
    dimEnergy = M𝓭 * dimSpeed * dimSpeed := by
  ext <;> simp [dimEnergy, dimSpeed]

/-- **Mass from a Compton clock**: `M = ℏ · T⁻¹ · c⁻²`, the dimensional
form of `m = ℏω/c²`.  This is the correct way to treat winding/Compton
mass as derived while retaining `M𝓭` as the primitive mass slot. -/
theorem M𝓭_eq_dimℏ_mul_frequency_div_c_sq :
    M𝓭 = dimℏ * T𝓭⁻¹ * dimSpeed⁻¹ * dimSpeed⁻¹ := by
  ext <;> simp [dimℏ, dimAction, dimSpeed]
