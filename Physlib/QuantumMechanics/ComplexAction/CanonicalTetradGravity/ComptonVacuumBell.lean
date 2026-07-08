/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-!
# The Compton-wavelength vacuum Bell decay is local-Lorentz-gauge invariant

Connects **ADM tetrad gravity** (`CanonicalTetradGravity.TetradADMGravity`, Lusanna 2015) to the **Compton-wavelength
vacuum Bell decay** (`ComptonClock.FrequencyTrinity`, Summers / Reeh–Schlieder, routed through
`Bell.EntropicEnvelope`). The vacuum Bell envelope `S_CHSH(r) ≤ 2√(1 + C₀²e^{−2r/λ_C})` decays over the
spacelike separation `r` with decay scale the Compton wavelength `λ_C = ħ/(mc)`. Both ingredients are
**Lorentz scalars**:

* `λ_C` is built from the rest mass `m`, invariant under the local Lorentz gauge of the tetrad;
* the spacelike **proper separation** `r = √(xᵀ g x)` is computed from the reconstructed tetrad metric
  `g = EᵀηE` (`tetradMetric`), which is invariant under the local Lorentz frame rotation `E ↦ ΛE`,
  `Λ ∈ SO(1,3)` (`tetradMetric_lorentz_gauge`) — the `𝔰𝔬(1,3)` frame freedom is pure inertial gauge.

So the proper-separation quadratic form `xᵀ g x` is gauge-invariant (`properSeparationSq_lorentz_gauge`),
hence the vacuum Bell envelope evaluated at the proper separation is the *same* in any local Lorentz frame
(`vacuumBell_compton_lorentz_gauge`) and always respects Tsirelson
(`vacuumBell_compton_gauge_under_tsirelson`, via `vacuum_bell_compton_decay`); and in a fixed frame it
decreases monotonically with proper separation (`vacuumBell_compton_monotone_proper`, via
`vacuum_bell_compton_monotone`). The Reeh–Schlieder exponential decay of vacuum entanglement over the
Compton wavelength is a **frame-independent, GR-gauge-invariant** physical statement.

* **§A — the proper separation from the tetrad metric** (`properSeparationSq`,
  `properSeparationSq_lorentz_gauge`).
* **§B — the vacuum Bell envelope is gauge-invariant and sub-Tsirelson**
  (`vacuumBell_compton_lorentz_gauge`, `vacuumBell_compton_gauge_under_tsirelson`).
* **§C — monotone decay in proper separation** (`vacuumBell_compton_monotone_proper`).
* **§D — the assembly** (`vacuumBell_compton_tetrad_gauge_invariant`).

## References

* L. Lusanna, *Canonical ADM tetrad gravity*, Int. J. Geom. Methods Mod. Phys. 12 (2015) 1530001;
  S. J. Summers, arXiv:0802.1854 (Reeh–Schlieder). Repo dependencies: `CanonicalTetradGravity.TetradADMGravity`
  (`tetradMetric`, `tetradMetric_lorentz_gauge`), `ComptonClock.FrequencyTrinity` (`comptonWavelength`,
  `vacuum_bell_compton_decay`, `vacuum_bell_compton_monotone`), `Bell.EntropicEnvelope`
  (`chshEnvelope`), `Bell.DeterministicBounds` (`tsirelsonWitness`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell

open Matrix
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

variable {d : ℕ}

/-! ## §A — the proper separation from the tetrad metric -/

/-- **The proper separation (squared) of a displacement `x`** `xᵀ g x` with `g = EᵀηE` the tetrad
`4`-metric (`tetradMetric`). The spacelike proper distance over which the vacuum Bell correlation is
measured, built from the orthonormal-frame tetrad `E`. -/
noncomputable def properSeparationSq (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x : (Fin 1 ⊕ Fin d) → ℝ) : ℝ :=
  x ⬝ᵥ (tetradMetric E *ᵥ x)

/-- **[Proper separation is local-Lorentz-gauge invariant] `xᵀ g[ΛE] x = xᵀ g[E] x`.** The
proper-separation quadratic form is unchanged by a local Lorentz frame rotation `E ↦ ΛE`, `Λ ∈ SO(1,3)`
(`tetradMetric_lorentz_gauge`) — the `𝔰𝔬(1,3)` frame freedom is pure inertial gauge, so proper distance
is a Lorentz scalar. -/
theorem properSeparationSq_lorentz_gauge {Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hΛ : Λ ∈ LorentzGroup d) (x : (Fin 1 ⊕ Fin d) → ℝ) :
    properSeparationSq (Λ * E) x = properSeparationSq E x := by
  unfold properSeparationSq; rw [tetradMetric_lorentz_gauge hΛ]

/-! ## §B — the vacuum Bell envelope is gauge-invariant and sub-Tsirelson -/

/-- **[The vacuum Bell envelope is local-Lorentz-gauge invariant].** Evaluated at the proper separation
`r = √(xᵀ g x)`, the Compton-wavelength vacuum Bell envelope is the *same* for the tetrad `E` and any
locally Lorentz-rotated frame `ΛE` (`properSeparationSq_lorentz_gauge`) — the Reeh–Schlieder decay of
vacuum entanglement is a frame-independent observable. -/
theorem vacuumBell_compton_lorentz_gauge {Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hΛ : Λ ∈ LorentzGroup d) (x : (Fin 1 ⊕ Fin d) → ℝ) (C₀ m c ħ : ℝ) :
    chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq (Λ * E) x) / comptonWavelength m c ħ)))
      = chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq E x) / comptonWavelength m c ħ))) := by
  rw [properSeparationSq_lorentz_gauge hΛ]

/-- **[The vacuum Bell envelope respects Tsirelson at the tetrad proper separation] `S_CHSH(r) ≤ 2√2`.**
At the proper separation `r = √(xᵀ g[ΛE] x)` derived from any frame (no Lorentz condition needed — the
bound holds for every real separation), the Compton-wavelength vacuum Bell envelope respects the Tsirelson
bound (`vacuum_bell_compton_decay`); combined with the gauge invariance below, the bound holds in *every*
local Lorentz frame. -/
theorem vacuumBell_compton_gauge_under_tsirelson {Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (x : (Fin 1 ⊕ Fin d) → ℝ) (C₀ m c ħ : ℝ) (hC₀ : C₀ ^ 2 ≤ 1)
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq (Λ * E) x) / comptonWavelength m c ħ)))
      ≤ tsirelsonWitness :=
  vacuum_bell_compton_decay C₀ (Real.sqrt (properSeparationSq (Λ * E) x)) m c ħ hC₀
    (div_nonneg (Real.sqrt_nonneg _) (comptonWavelength_pos m c ħ hm hc hħ).le)

/-! ## §C — monotone decay in proper separation -/

/-- **[The vacuum Bell violation decreases with proper separation].** In a fixed tetrad frame `E`, a
larger spacelike proper separation `√(xᵀ g x)` gives a smaller vacuum CHSH envelope
(`vacuum_bell_compton_monotone`) — the exponential decay of vacuum entanglement over the Compton
wavelength, measured by the GR proper distance. -/
theorem vacuumBell_compton_monotone_proper {E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (x₁ x₂ : (Fin 1 ⊕ Fin d) → ℝ) (C₀ m c ħ : ℝ) (hC₀ : 0 ≤ C₀)
    (hsep : Real.sqrt (properSeparationSq E x₁) ≤ Real.sqrt (properSeparationSq E x₂))
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq E x₂) / comptonWavelength m c ħ)))
      ≤ chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq E x₁) / comptonWavelength m c ħ))) :=
  vacuum_bell_compton_monotone C₀ (Real.sqrt (properSeparationSq E x₁))
    (Real.sqrt (properSeparationSq E x₂)) m c ħ hC₀ hsep hm hc hħ

/-! ## §D — the assembly -/

/-- **[The Compton-wavelength vacuum Bell decay is GR-gauge-invariant, assembled].** Evaluated at the
proper separation `r = √(xᵀ g x)` of the tetrad metric, the Compton-wavelength vacuum Bell envelope is
local-Lorentz-gauge invariant (the *same* for `E` and `ΛE`) *and* respects the Tsirelson bound in every
frame. The Reeh–Schlieder exponential decay of vacuum entanglement over the Compton wavelength is a
frame-independent, sub-Tsirelson physical observable — the gauge invariance is Lusanna's
`tetradMetric_lorentz_gauge` for the reconstructed metric. -/
theorem vacuumBell_compton_tetrad_gauge_invariant
    {Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ} (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (C₀ m c ħ : ℝ) (hC₀ : C₀ ^ 2 ≤ 1)
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq (Λ * E) x) / comptonWavelength m c ħ)))
        = chshEnvelope (C₀ * Real.exp
          (-(Real.sqrt (properSeparationSq E x) / comptonWavelength m c ħ)))
      ∧ chshEnvelope (C₀ * Real.exp
          (-(Real.sqrt (properSeparationSq (Λ * E) x) / comptonWavelength m c ħ)))
        ≤ tsirelsonWitness :=
  ⟨vacuumBell_compton_lorentz_gauge hΛ x C₀ m c ħ,
    vacuumBell_compton_gauge_under_tsirelson (Λ := Λ) (E := E) x C₀ m c ħ hC₀ hm hc hħ⟩

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell

end
