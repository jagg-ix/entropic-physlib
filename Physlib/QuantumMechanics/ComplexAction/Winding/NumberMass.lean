/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

/-!
# Rest mass from internal-clock frequency and winding-number quantization

A massive mode has an internal **de Broglie clock** of angular frequency `ω = mc²/ħ`; inverting this,
`m = ħω/c²` recovers the rest mass from the clock frequency. If the frequency is quantized by a
**winding number** `n ∈ ℤ` (the topological charge of `Hopf.ChargeConjugationRibbonTwist`), the mass spectrum
is `m_n = n·m₀`. This file records that, building on the existing `comptonFrequency` (`ω_C = mc²/ħ`).

* **§A — mass ⟷ clock frequency (Planck–Einstein / de Broglie internal clock).** `comptonMass` is the inverse
  of `comptonFrequency`: `comptonMass (comptonFrequency m) = m` and `comptonFrequency (comptonMass ω) = ω`
  (for `c, ħ ≠ 0`); `comptonMass_restEnergy`: `ħω = mc²`.
* **§B — the winding-number mass spectrum.** At winding `n` the frequency is `ω_n = n ω₀`, so
  `windingMass n = n · m₀` (`windingMass_eq_zsmul`) — mass linear in the winding number; `windingMass_zero`
  (zero winding ⟹ massless), `windingMass_add` (winding numbers add ⟹ masses add), `windingMass_neg`.
* **§C — one integer fixes both charge and mass.** `charge_mass_shared_winding`: the *same* winding addition
  `q + p` governs both the **group-like charge law** `chargeState (q+p) = chargeState q · chargeState p`
  (multiplicative) and the **linear mass law** `windingMass (q+p) = windingMass q + windingMass p` (additive).
  `antiparticle_equal_mass`: the charge-conjugate mode (antipode `q ↦ −q`) has equal rest mass
  `|windingMass (−q)| = |windingMass q|` — the CPT statement `m = m̄`.

**Honest layering.** `m = ħω/c²` and the bijection are the standard Planck–Einstein / de Broglie
internal-clock relation. `ω_n = n ω₀ ⟹ m_n = n m₀` (mass linear in winding number) is a quantization
hypothesis — natural in the topological-charge / winding-number tradition but a modelling assumption; the
algebra (§C) is an exact consequence once it is posited. Spin/statistics is the separate ribbon-twist leg
(`ribbonTwist_fermion`); charge is the `qCharacter` leg.

## References

* de Broglie internal clock (`m c² = ħ ω`); topological winding number. `Physlib`
  (`ComptonClock.FrequencyTrinity.comptonFrequency`, `Hopf.ChargeConjugationRibbonTwist.chargeState`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass


/-- **The rest mass from the internal-clock frequency** `m = ħ ω / c²` — the inverse of `comptonFrequency`
(de Broglie internal clock). -/
noncomputable def comptonMass (ω c ħ : ℝ) : ℝ := ħ * ω / c ^ 2

/-- **[Mass from its Compton clock]** `comptonMass (ω_C) = m`: recovering the rest mass from its internal
clock frequency `ω_C = mc²/ħ` (Planck–Einstein / de Broglie). -/
lemma comptonMass_comptonFrequency (m c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonMass (comptonFrequency m c ħ) c ħ = m := by
  unfold comptonMass comptonFrequency
  field_simp

/-- **[Clock from the mass]** `comptonFrequency (comptonMass ω) = ω`: the clock frequency that yields mass
`m = comptonMass ω` is exactly `ω`. -/
lemma comptonFrequency_comptonMass (ω c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonFrequency (comptonMass ω c ħ) c ħ = ω := by
  unfold comptonMass comptonFrequency
  field_simp

/-- **[`E = ħω = mc²`]** the internal-clock energy `ħω` equals the rest energy `mc²` (de Broglie internal
clock). -/
lemma comptonMass_restEnergy (ω c ħ : ℝ) (hc : c ≠ 0) :
    ħ * ω = comptonMass ω c ħ * c ^ 2 := by
  unfold comptonMass
  field_simp


/-- **The winding frequency** `ω_n = n ω₀` — at winding number `n` the mode cycles at `n` times the
fundamental frequency `ω₀`. -/
noncomputable def windingFrequency (n : ℤ) (ω₀ : ℝ) : ℝ := (n : ℝ) * ω₀

/-- **The winding mass** `m_n = ħ ω_n / c²` — the rest mass at winding number `n`. -/
noncomputable def windingMass (n : ℤ) (ω₀ c ħ : ℝ) : ℝ := comptonMass (windingFrequency n ω₀) c ħ

/-- **[Mass spectrum is linear in winding]** `m_n = n · m₀`: the mass at winding `n` is `n` times the
fundamental mass `m₀ = comptonMass ω₀` (the winding-number quantization hypothesis). -/
lemma windingMass_eq_zsmul (n : ℤ) (ω₀ c ħ : ℝ) :
    windingMass n ω₀ c ħ = (n : ℝ) * comptonMass ω₀ c ħ := by
  unfold windingMass windingFrequency comptonMass
  ring

/-- **[Zero winding ⟹ massless]** `m_0 = 0`. -/
lemma windingMass_zero (ω₀ c ħ : ℝ) : windingMass 0 ω₀ c ħ = 0 := by
  rw [windingMass_eq_zsmul]; simp

/-- **[Winding numbers add ⟹ masses add]** `m_{m+n} = m_m + m_n`: the winding mass is additive in the winding
number — composite modes have the summed mass. -/
lemma windingMass_add (m n : ℤ) (ω₀ c ħ : ℝ) :
    windingMass (m + n) ω₀ c ħ = windingMass m ω₀ c ħ + windingMass n ω₀ c ħ := by
  simp only [windingMass_eq_zsmul, Int.cast_add]; ring

/-- **[Reversed winding negates the winding mass]** `m_{-n} = − m_n`. -/
lemma windingMass_neg (n : ℤ) (ω₀ c ħ : ℝ) :
    windingMass (-n) ω₀ c ħ = - windingMass n ω₀ c ħ := by
  simp only [windingMass_eq_zsmul, Int.cast_neg]; ring


/-- **[Charge and mass share the winding integer]** the *same* winding addition `q + p` governs both the
**group-like charge law** `chargeState (q+p) = chargeState q · chargeState p` (charges multiply,
`Hopf.ChargeConjugationRibbonTwist`) and the **linear mass law** `windingMass (q+p) = windingMass q +
windingMass p` (masses add). One topological integer fixes both quantum numbers. -/
lemma charge_mass_shared_winding (q p : ℤ) (ω₀ c ħ : ℝ) :
    chargeState (q + p) = chargeState q * chargeState p ∧
      windingMass (q + p) ω₀ c ħ = windingMass q ω₀ c ħ + windingMass p ω₀ c ħ :=
  ⟨(chargeState_mul q p).symm, windingMass_add q p ω₀ c ħ⟩

/-- **[Particle and antiparticle have equal rest mass]** `|m_{-q}| = |m_q|`: the charge-conjugate mode
(antipode `q ↦ −q`, `antipode_chargeState`) carries the same rest mass — the CPT statement `m = m̄`. -/
lemma antiparticle_equal_mass (q : ℤ) (ω₀ c ħ : ℝ) :
    |windingMass (-q) ω₀ c ħ| = |windingMass q ω₀ c ħ| := by
  rw [windingMass_neg, abs_neg]

end Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

end
