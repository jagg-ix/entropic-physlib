/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.Noether.DissipativeBalance
public import Physlib.Thermodynamics.SecondLaw

/-!
# From the Noether defect to entropic time

The dissipative defect of the Noether balance law is the entropy-production rate:
the imaginary action accumulates it,

  `S_I(t₂) − S_I(t₁) = ∫_{t₁}^{t₂} defect`,   `defect ≥ 0`,

so `S_I` is monotone and the entropic proper time `τ_ent := S_I/ℏ` is monotone
**as a consequence** — entropic time is the normalized readout of accumulated
irreversible defect, not a cause. This realises the chain

  symmetry → conserved current → dissipative defect → positive defect →
  entropy production → entropic time as side effect

and bridges to the existing `Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline`
(`toEntropyArrowWorldline`).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.ClassicalMechanics.Noether.DissipativeBalance Physlib.Thermodynamics.SecondLaw
namespace Physlib.StatisticalMechanics.EntropyProduction


/-- **Entropic Noether worldline.** The imaginary action `S_I` accumulates a
non-negative dissipative defect; `τ_ent := S_I/ℏ`. -/
structure EntropicNoetherWorldline where
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- `ℏ > 0`. -/
  hbar_pos : 0 < hbar
  /-- Imaginary action / accumulated dissipative defect. -/
  S_I : ℝ → ℝ
  /-- Dissipative defect rate. -/
  defect : ℝ → ℝ
  /-- The defect is non-negative (second law / open-system positivity). -/
  defect_nonneg : ∀ t, 0 ≤ defect t
  /-- `S_I` accumulates the defect: `S_I(t₂) − S_I(t₁) = ∫ defect`. -/
  S_I_increment : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → S_I t₂ - S_I t₁ = ∫ t in t₁..t₂, defect t
  /-- Initial imaginary action is non-negative. -/
  S_I_at_zero_nonneg : 0 ≤ S_I 0

namespace EntropicNoetherWorldline

variable (W : EntropicNoetherWorldline)

/-- The imaginary action is monotone — the positive defect integrates forward. -/
theorem S_I_monotone {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) : W.S_I t₁ ≤ W.S_I t₂ := by
  have hb := W.S_I_increment t₁ t₂ h
  have hnn : 0 ≤ ∫ t in t₁..t₂, W.defect t :=
    intervalIntegral.integral_nonneg h (fun u _ => W.defect_nonneg u)
  linarith

/-- The entropic proper time `τ_ent := S_I/ℏ`. -/
def tauEnt (t : ℝ) : ℝ := W.S_I t / W.hbar

/-- **Entropic time is a side effect of the Noether defect**: `τ_ent` is monotone,
derived from `S_I` monotonicity (hence from `defect ≥ 0`). -/
theorem tauEnt_monotone_from_noether_defect {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    W.tauEnt t₁ ≤ W.tauEnt t₂ := by
  unfold tauEnt
  rw [div_le_div_iff_of_pos_right W.hbar_pos]
  exact W.S_I_monotone h

/-- **Bridge to the entropy-arrow layer.** An entropic Noether worldline is an
`EntropyArrowWorldline`: the Noether-defect construction feeds the existing
"entropic time as side effect" theorems. -/
def toEntropyArrowWorldline : EntropyArrowWorldline where
  ℏ := W.hbar
  ℏ_pos := W.hbar_pos
  S_I_along := W.S_I
  τ_ent_along := fun t => W.S_I t / W.hbar
  τ_ent_eq := fun _ => rfl
  S_I_monotone := fun {_ _} h => W.S_I_monotone h
  S_I_at_zero_nonneg := W.S_I_at_zero_nonneg

end EntropicNoetherWorldline

end Physlib.StatisticalMechanics.EntropyProduction

end
