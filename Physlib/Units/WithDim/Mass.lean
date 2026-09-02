/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Energy
public import Physlib.Units.LTMCTIDimensionBase
public import Mathlib.Data.Complex.Basic
/-!

# Mass

In this module we define the dimensionful type `DimMass` corresponding to the
mass of a particle, in an arbitrary (but given) set of units.  Mirrors the
shape of `Physlib.Units.WithDim.Energy.DimEnergy`.

We also expose the **mass ↔ information bridge** behind the
entropic-time *Equation 3* form `M = ℏ · c⁻² · …`: the standard SI mass
dimension `M𝓭` is `dimAction · L𝓭⁻² · T𝓭` (rearranging
`[ℏ] = M·L²·T⁻¹`), so mass values carry the same dimensional content as
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
open LTMCTUnitChoices Dimensionful CarriesDimension

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

In physlib's 6-base `{L, T, M, C, Θ, I}` basis, mass `LTMCTI.M𝓭` is a primitive
dimension, *not* derived from information.  The
information-extended ontology (`InformationExtendedBase = {I, T, Q, Θ}`)
treats mass as an emergent quantity (in natural units `c = ℏ = 1`).

We do not collapse the 6-base ontology — we instead expose the
**action-mediated form** of the same identification: `LTMCTI.M𝓭` factorises
through `dimAction = M·L²·T⁻¹`, which carries the canonical place where
information enters (the informational imaginary action `S_I = action·I`).

Complex masses do **not** require a complex-valued dimension.  The value
may live in `ℂ`, but the dimension vector remains the ordinary mass
dimension `LTMCTI.M𝓭`: `m = m_R + i m_I`, a resonance pole `m - i Γ/2`, and a
Nagao--Nielsen complex mass all have real and imaginary components in
the same mass/energy units.  In natural-unit calculations this same
dimension may be re-expressed as `E/c²` or `ℏω/c²`; that is a derived
identity inside the rational-exponent dimension group, not a new
complex dimension.
-/

/-- **Mass dimension via action and length-time** (Equation 3 form,
rearranged into physlib's ISQ+I basis):
`M = A · L⁻² · T = (M·L²·T⁻¹) · L⁻² · T`.  This is a *re-expression*
of `LTMCTI.M𝓭` in terms of derived quantities. -/
lemma LTMCTI.M𝓭_eq_dimAction_div_L_sq_times_T :
    LTMCTI.M𝓭 = dimAction * LTMCTI.L𝓭⁻¹ * LTMCTI.L𝓭⁻¹ * LTMCTI.T𝓭 := by
  ext b <;> cases b <;> simp [dimAction]

/-- **Kinematic-viscosity dimensional identity** `[ℏ/m] = L²·T⁻¹`.
This is the dimensional skeleton of the Madelung viscosity `ν = ℏ/(2m)`. -/
lemma dimℏ_div_M𝓭_eq_L_sq_div_T :
    dimℏ * LTMCTI.M𝓭⁻¹ = LTMCTI.L𝓭 * LTMCTI.L𝓭 * LTMCTI.T𝓭⁻¹ := by
  ext b <;> cases b <;> simp [dimℏ, dimAction]

/-- **Brillouin / Landauer identity** `[S_I / ℏ] = I` — the informational
imaginary action divided by the Planck action is dimensionally the
information base. -/
lemma dimImaginaryAction_div_dimℏ_eq_I𝓭 :
    dimImaginaryAction * dimℏ⁻¹ = LTMCTI.I𝓭 := by
  ext b <;> cases b <;> simp [dimImaginaryAction, dimℏ, dimAction]

/-! ## Deferred: `WithDim`-typed restatements

The fork's `dim_DimMass_eq_dimAction_div_L_sq_times_T`, `ComplexDimMass`,
`dim_ComplexDimMass_eq_DimMass` and `complexMass_parts_same_dimension` restated the
dimension algebra above at the `WithDim`-carrier level. Upstream's `HasDim` instance is
fixed to the five-generator default basis, so those restatements cannot be stated over
`LTMCTIDimensionBase` until `HasDim` is generalised over the basis; they had no consumers
and are deferred rather than ported. -/
