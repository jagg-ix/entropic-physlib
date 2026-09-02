/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.CasimirSelfInteractionEnergyDensity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-!
# Deriving the Casimir-SIE length inputs from the Compton hierarchy

`CasimirSelfInteractionEnergyDensity` took two length/energy inputs from Tkatchenko & Fedorov
(arXiv:2301.10151) as *given*: the Thomson (classical-electron) radius `R_Th = α_fsc²a₀` at which the pairwise
SIE is evaluated (Eq. 5), and the Hartree energy `E_h = α_fsc ħc/a₀` (Eq. 5). Both are **derivable** from the
atomic length hierarchy, which is fixed by the Compton wavelength `ƛ_C = ħ/(mc)` of `ComptonClock.FrequencyTrinity`
and one dimensionless number, the fine-structure constant `α_fsc`. This module derives them, linking the Casimir
work to the Compton-clock arc, and states which paper inputs genuinely *cannot* be derived, with the reason.

The hierarchy is one factor of `α_fsc` per rung:
`a₀ (Bohr) = ƛ_C/α_fsc`, `ƛ_C (Compton) = α_fsc·a₀`, `r_e (classical/Thomson) = α_fsc·ƛ_C = α_fsc²·a₀`.

* **§A — the length hierarchy from the Compton wavelength.** `bohrRadius = ƛ_C/α_fsc`, `thomsonRadius = α_fsc·ƛ_C`;
  **`thomson_eq_alpha_sq_bohr`** (`r_e = α_fsc²·a₀`) — the Thomson radius is *derived*, not assumed.
* **§B — the Hartree energy from the Compton frequency.** `hartreeEnergy = α_fsc²·(ħ·ω_C) = α_fsc²·mc²`;
  **`hartree_eq_from_compton`** (`E_h = α_fsc·ħc/a₀`) — the Hartree energy is *derived* from `ω_C`.
* **§C — the derived inputs feed the pairwise SIE.** `thomson_radius_beta` (`r_e = β⁶·a₀`, `β = α_fsc^{1/3}`) and
  **`sie2_thomson_derived`**: `sie2FromRadius` evaluated at the *derived* Thomson radius reproduces the `β³²`
  pairwise SIE of `sie2_thomson` — the paper's `R = β⁶a₀` input is now the classical-electron-radius derivation.
* **§D — what cannot be derived, and why.** `nEff_leading_exact` (only the kissing-number leading term of the
  `R⁻⁷` lattice sum is closed-form) — the bcc/fcc values `N_eff ≈ 11.05, 13.36` are transcendental Epstein-zeta
  sums with no elementary closed form; and the cosmological constant `Λ` is an observational input (measured, not
  derived). These are documented, not asserted.

**Honest layering.** §A–§C are exact `field_simp`/`ring` derivations turning two paper inputs into consequences of
the Compton wavelength + `α_fsc`. §D records the genuinely non-derivable inputs (a transcendental lattice sum; an
observed constant) with the reason. The `α_fsc`-per-rung hierarchy itself is the definition of the Bohr/Compton/
classical radii, not a fit.

## References

* Tkatchenko & Fedorov, arXiv:2301.10151 (2023), Eq. 5. Built on `Particles.CasimirSelfInteractionEnergyDensity`
  and `ComptonClock.FrequencyTrinity` (`comptonWavelength`, `comptonFrequency`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.CasimirSelfInteractionEnergyDensity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy


/-- The **Bohr radius** `a₀ = ƛ_C/α_fsc` — the reduced Compton wavelength divided by the fine-structure constant,
one rung *up* the atomic length hierarchy. -/
noncomputable def bohrRadius (m c ħ α : ℝ) : ℝ := comptonWavelength m c ħ / α

/-- The **classical electron (Thomson) radius** `r_e = α_fsc·ƛ_C` — the reduced Compton wavelength times the
fine-structure constant, one rung *down* the hierarchy. -/
noncomputable def thomsonRadius (m c ħ α : ℝ) : ℝ := α * comptonWavelength m c ħ

/-- **The Thomson radius is `α_fsc²` times the Bohr radius** `r_e = α_fsc²·a₀` — derived from the two hierarchy
rungs (`a₀ = ƛ_C/α`, `r_e = α·ƛ_C`), so the pairwise-SIE evaluation length of the paper is a *consequence* of the
Compton wavelength, not an input. -/
lemma thomson_eq_alpha_sq_bohr (m c ħ α : ℝ) (hα : α ≠ 0) :
    thomsonRadius m c ħ α = α ^ 2 * bohrRadius m c ħ α := by
  unfold thomsonRadius bohrRadius
  field_simp


/-- The **Hartree energy** `E_h = α_fsc²·(ħ·ω_C) = α_fsc²·mc²` — the rest energy `ħω_C` (Compton frequency of
`FrequencyTrinity`) scaled by `α_fsc²`. -/
noncomputable def hartreeEnergy (m c ħ α : ℝ) : ℝ := α ^ 2 * (ħ * comptonFrequency m c ħ)

/-- **The Hartree energy is `α_fsc·ħc/a₀`** `E_h = α_fsc·ħc/a₀` — derived from the Compton frequency
`ω_C = mc²/ħ` and the Bohr radius `a₀ = ƛ_C/α`, so the energy unit of Eq. 5 is a consequence of the Compton
scale. -/
lemma hartree_eq_from_compton (m c ħ α : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hα : α ≠ 0) :
    hartreeEnergy m c ħ α = α * ħ * c / bohrRadius m c ħ α := by
  unfold hartreeEnergy bohrRadius comptonFrequency comptonWavelength
  field_simp


/-- **The Thomson radius is `β⁶·a₀`** `r_e = β⁶·a₀` with `β = α_fsc^{1/3}` — since `α_fsc² = (β³)² = β⁶`, the
derived Thomson radius has exactly the `β⁶a₀` form used in `sie2_thomson`. -/
lemma thomson_radius_beta (m c ħ α β : ℝ) (hα : α ≠ 0) (hβ : α = β ^ 3) :
    thomsonRadius m c ħ α = β ^ 6 * bohrRadius m c ħ α := by
  rw [thomson_eq_alpha_sq_bohr m c ħ α hα, hβ]
  ring

/-- **The pairwise SIE at the derived Thomson radius is the `β³²` energy** — feeding the *derived*
`thomsonRadius` (§A) into `sie2FromRadius` reproduces `sie2_thomson`'s `−(23ℏc/3072π²)β³²/a₀⁴`, so the paper's
`R = β⁶a₀` input is replaced by the classical-electron-radius derivation with no change to the result. -/
lemma sie2_thomson_derived (m c ħ_field α β a₀ ℏc : ℝ) (hα : α ≠ 0) (hβ : α = β ^ 3)
    (ha : a₀ ≠ 0) (ha0 : bohrRadius m c ħ_field α = a₀) :
    sie2FromRadius β a₀ ℏc (thomsonRadius m c ħ_field α)
      = -(23 * ℏc / (3072 * Real.pi ^ 2)) * β ^ 32 / a₀ ^ 4 := by
  rw [thomson_radius_beta m c ħ_field α β hα hβ, ha0, sie2_thomson β a₀ ℏc ha]

/-!

Two of the paper's inputs are **not** replaceable by derived values:

1. **The bcc/fcc lattice sums `N_eff ≈ 11.05, 13.36`.** These are values of the Epstein zeta function `Z_{Λ,7}`
   for the bcc/fcc lattice — `N_eff = Σ_{Rⱼ≠0}(2R)⁷/|Rⱼ|⁷`, a transcendental number with no elementary closed
   form. Only the *leading* term is derivable: a touching pair (`|Rⱼ| = 2R`) contributes `1`
   (`CasimirSelfInteractionEnergyDensity.nEff_nearest_term`), so the leading `N_eff` is the kissing number
   (`8` bcc, `12` fcc). The remaining tail cannot be reduced in closed form. The *shell-free* alternative
   `N_eff = (768π²/23)α_fsc^{2/3} ≈ 12.40` (`nEff_analytic`) sidesteps the lattice sum entirely — that value
   *is* derived, and it lands between the two transcendental lattice values.
2. **The cosmological constant `Λ`.** The model's agreement `|Ē_SIE| ≈ Λ ≈ 1.9×10⁻²³ Ha/Bohr³` is a comparison
   with the *measured* value (Planck / Hubble Space Telescope). `Λ` is an observational input, fixed by data, so
   it cannot be replaced by a derived value.
-/

end Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
