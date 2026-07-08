/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.LeviCivitaTetrad
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-!
# Cosmic expansion dilutes vacuum Bell correlations

Links the FRW cotetrad geometry (`Cosmology.FLRW.LeviCivitaTetrad`) to the Compton-wavelength vacuum Bell
decay (`ComptonClock.FrequencyTrinity`). The FRW proper distance between two **comoving** points at comoving
separation `χ` is `r = a·χ` — the scale factor `a` rescaling the comoving distance (the spatial part of the
FRW interval `c²t² − a²|x⃗|²`, `frw_spatial_interval`). Feeding this proper distance into the Compton vacuum
Bell envelope `C(r) = C₀·e^{−r/λ_C}` gives, for comoving points,

  `C(a·χ) = C₀·e^{−a·χ/λ_C}`,

so the vacuum CHSH envelope stays under Tsirelson (`frw_vacuum_bell_compton_decay`) and, crucially,
**decreases monotonically as the universe expands**: for scale factors `a₁ ≤ a₂`,

  `S_CHSH(a₂·χ) ≤ S_CHSH(a₁·χ)`   (`frw_expansion_dilutes_vacuum_bell`).

Cosmic expansion grows the proper Compton-scale separation between fixed comoving points, redshifting the
Reeh–Schlieder / Summers vacuum entanglement toward the classical bound. So the cosmological dynamics (the
Friedmann scale factor `a(t)` of `HubbleEvolution`) drives the dilution of vacuum Bell correlations through
the Compton wavelength `λ_C`.

* **§A — the FRW spatial proper interval** (`frw_spatial_interval`).
* **§B — expansion dilutes the vacuum Bell envelope** (`frw_vacuum_bell_compton_decay`,
  `frw_expansion_dilutes_vacuum_bell`).

## References

* FRW comoving proper distance `r = a·χ`; the Reeh–Schlieder/Summers vacuum-correlation decay over the
  Compton wavelength. structures: `Cosmology.FLRW.LeviCivitaTetrad` (`frwCotetrad`, `frw_properSeparationSq`),
  `ComptonClock.FrequencyTrinity` (`comptonWavelength`, `vacuum_bell_compton_decay`,
  `vacuum_bell_compton_monotone`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Cosmology.FLRW.ComptonVacuumBell

open Cosmology.FLRW.LeviCivitaTetrad
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

/-! ## §A — the FRW spatial proper interval -/

/-- **[The FRW spatial proper interval] `xᵀ g_FRW x = −a²|x⃗|²`** for a purely spatial comoving displacement
(`x⁰ = 0`). The spacelike proper distance between comoving points is therefore `a·χ`, the scale factor times
the comoving distance `χ = |x⃗|`. -/
theorem frw_spatial_interval (a c : ℝ) (x : (Fin 1 ⊕ Fin 3) → ℝ) (h0 : x (Sum.inl 0) = 0) :
    properSeparationSq (frwCotetrad a c) x = -(a ^ 2 * ∑ j : Fin 3, (x (Sum.inr j)) ^ 2) := by
  rw [frw_properSeparationSq, h0]; ring

/-! ## §B — expansion dilutes the vacuum Bell envelope -/

/-- **[The vacuum Bell envelope at FRW proper distance respects Tsirelson].** At comoving separation `χ` and
scale factor `a`, the proper distance `r = a·χ` feeds the Compton vacuum Bell decay; the CHSH envelope stays
under the Tsirelson bound. -/
theorem frw_vacuum_bell_compton_decay (C₀ χ m c ħ a : ℝ) (hC₀ : C₀ ^ 2 ≤ 1)
    (hχ : 0 ≤ χ) (ha : 0 ≤ a) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp (-(a * χ / comptonWavelength m c ħ))) ≤ tsirelsonWitness :=
  vacuum_bell_compton_decay C₀ (a * χ) m c ħ hC₀
    (div_nonneg (mul_nonneg ha hχ) (comptonWavelength_pos m c ħ hm hc hħ).le)

/-- **[Cosmic expansion dilutes vacuum Bell correlations] `S_CHSH(a₂·χ) ≤ S_CHSH(a₁·χ)` for `a₁ ≤ a₂`.** As
the universe expands (the Friedmann scale factor `a(t)` grows), the proper Compton-scale separation `a·χ`
between fixed comoving points increases, so the vacuum CHSH envelope decreases monotonically toward the
classical bound — the Reeh–Schlieder/Summers vacuum entanglement is redshifted away by expansion. -/
theorem frw_expansion_dilutes_vacuum_bell (C₀ χ m c ħ a₁ a₂ : ℝ) (hC₀ : 0 ≤ C₀)
    (hχ : 0 ≤ χ) (ha : a₁ ≤ a₂) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp (-(a₂ * χ / comptonWavelength m c ħ)))
      ≤ chshEnvelope (C₀ * Real.exp (-(a₁ * χ / comptonWavelength m c ħ))) :=
  vacuum_bell_compton_monotone C₀ (a₁ * χ) (a₂ * χ) m c ħ hC₀
    (mul_le_mul_of_nonneg_right ha hχ) hm hc hħ

end Cosmology.FLRW.ComptonVacuumBell

end
