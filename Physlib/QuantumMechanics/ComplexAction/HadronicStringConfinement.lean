/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement
public import Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# String theory's empirical anchor: the hadronic string, Regge slope, and confinement

The string formalism in this repository — the Regge trajectory `M² = (J − α₀)/α'`
(`Yukawa.ReggeStringMassYukawaReplacement.reggeMassSq`), Newton's constant as the Regge slope
`G = c³α'/ℏ` (`StringScaleHolographicGravity`), the Witt/Virasoro algebra — is anchored there at the
**Planck** scale (`α' = ℓ_P² ≈ 10⁻³⁸ GeV⁻²`, the *gravity* string of Scherk–Schwarz/Yoneya). But string
theory's *empirical* origin is the opposite scale: it was born from **hadron physics**. The Veneziano dual
amplitude fit `ππ` scattering, and the linear Regge trajectories `J = α₀ + α' M²` are the *measured* meson
spectrum (`ρ(770) → a₂(1320) → ρ₃(1690) → a₄(2040)`, slope `α' ≈ 0.88 GeV⁻²`).

This module supplies the bridge the repository is missing: the identity that ties the Regge slope to the
**QCD string tension** `σ`, so that *one* measurable number governs both the hadron spectrum and quark
confinement.

## The Nambu–Goto relation `α' = 1/(2πσ)`

For a relativistic (Nambu–Goto) string of tension `σ`, the Regge slope is `α' = 1/(2πσ)`
(`reggeSlopeOfTension`); scale-independently, `α'·σ = 1/(2π)` (`reggeSlope_mul_tension`). Feeding it into
the Regge trajectory gives the **rotating-string mass** — the mass² of a spinning relativistic string with
its slope replaced by the tension:

  `M² = 2πσ (J − α₀)`   (`reggeMassSq_of_tension`).

So the meson mass spectrum is fixed by the single tension `σ`.

## The same `σ` confines quarks

That same string tension is the coefficient of the **linear confining potential** of QCD. The Wilson-loop
area law `⟨W⟩ = e^{−σ R T}` gives the static quark–antiquark potential `V(R) = σ R`
(`Particles.WilsonLoopConfinementCriterion.staticQuarkPotential`), which is confining
(`staticQuarkPotential_confining`). `hadronic_string_confinement` bundles the two: with one `σ`, the linear
Regge trajectory and the confining potential hold together — the QCD flux tube *is* the hadronic string.

## Actual physics: the numbers agree

The string tension is measured on the lattice, `√σ ≈ 420 MeV`, i.e. `σ ≈ 0.18 GeV²`. Then
`α' = 1/(2πσ) ≈ 0.88 GeV⁻²`, exactly the slope of the measured meson Regge trajectories — the QCD flux tube
and the hadron spectrum are the same string. This is string theory's link to *measured* physics; the
Planckian reading of the same formalism (`StringScaleHolographicGravity`, `α' = ℓ_P²`) is the same string
tuned up to the gravitational scale, `σ_grav = c⁴/(2πG)`.

## References

* T. Regge (1959); G. F. Chew, S. C. Frautschi, *Phys. Rev. Lett.* **8** (1962) 41 (linear trajectories).
* Y. Nambu, T. Goto (relativistic string, `σ = 1/2πα'`).
* K. G. Wilson, *Phys. Rev. D* **10** (1974) 2445 (confinement, area law, `V(R) = σR`).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HadronicStringConfinement

open Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement
open Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion

/-- **The Nambu–Goto Regge slope** `α' = 1/(2πσ)` from the string tension `σ`. -/
noncomputable def reggeSlopeOfTension (σ : ℝ) : ℝ := 1 / (2 * Real.pi * σ)

/-- **The scale-independent string relation** `α'·σ = 1/(2π)`. -/
theorem reggeSlope_mul_tension (σ : ℝ) (hσ : σ ≠ 0) :
    reggeSlopeOfTension σ * σ = 1 / (2 * Real.pi) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [reggeSlopeOfTension]
  field_simp

/-- **The rotating-string mass: `M² = 2πσ(J − α₀)`.**  Replacing the Regge slope by the string tension
`α' = 1/(2πσ)`, the linear Regge trajectory becomes the mass² of a spinning relativistic string of tension
`σ` — the meson spectrum from a single measurable number. -/
theorem reggeMassSq_of_tension (J α₀ σ : ℝ) :
    reggeMassSq J α₀ (reggeSlopeOfTension σ) = 2 * Real.pi * σ * (J - α₀) := by
  rw [reggeMassSq, reggeSlopeOfTension, one_div, div_eq_mul_inv, inv_inv]; ring

/-- **The hadronic string is the QCD flux tube.**  For a positive string tension `σ`, the *same* `σ` gives
the linear Regge trajectory `M² = 2πσ(J − α₀)` (the meson spectrum) and the linear confining potential
`V(R) = σR` (`staticQuarkPotential`), which is confining. One measurable string tension governs both the
hadron spectrum and quark confinement. -/
theorem hadronic_string_confinement (J α₀ σ R : ℝ) (hσ : 0 < σ) :
    reggeMassSq J α₀ (reggeSlopeOfTension σ) = 2 * Real.pi * σ * (J - α₀)
      ∧ staticQuarkPotential σ R = σ * R
      ∧ IsConfining (staticQuarkPotential σ) :=
  ⟨reggeMassSq_of_tension J α₀ σ, rfl, staticQuarkPotential_confining σ hσ⟩

end Physlib.QuantumMechanics.ComplexAction.HadronicStringConfinement

end
