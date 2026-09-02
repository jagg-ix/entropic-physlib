/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalAutomorphismConformalInvariants
meta import Zil

/-!
# The Compton–de Broglie clock on Malament's proper time

Malament's theorem reconstructs the metric — and proper time — from the causal order up to
a conformal factor, with scale-invariant proper-time ratios exactly determined
(`CausalAutomorphismConformalInvariants`).  This module reads that proper time with the
**Compton–de Broglie internal clock** and situates it in the entropic-time programme.

* **The clock.**  A massive particle carries an internal oscillation at the Compton
  frequency `ω_C = mc²/ℏ` (`FrequencyTrinity.comptonFrequency`), the de Broglie internal
  clock; over a proper-time interval `τ` it accumulates the phase `φ = ω_C·τ`
  (`comptonPhase`).  Its de Broglie clock-wave is luminal: `ω_C·λ_C = c`
  (`comptonClock_luminal`, with `λ_C = ℏ/(mc)` the Compton wavelength = Yukawa range).

* **The Malament link.**  Under a causal automorphism the phase scales by the dilation
  factor `√c`, so **Compton-clock phase ratios are exact causal invariants**
  (`comptonPhase_ratio_causalAutomorphism`) — the de Broglie clock's ratios are read off the
  causal order alone.

* **The entropic-time chain.**  The accumulated phase is the entropic action over `ℏ`:
  `S_I = mc²·τ` (`comptonAnchored_actionRate_eq_restEnergy`), so the Caticha entropic time of
  the Compton-anchored clock equals this geometric proper time
  (`comptonAnchored_entropicTime_eq_geometricProperTime`).  At the three-origin mass
  `m = yukawaMass` — where the Compton mass is simultaneously the Yukawa mass, the Verlinde
  gravitational-horizon mass, and the Witten Chern–Simons topological mass, and
  `ω₀ = c³Ȧ/(4Għ)` (`comptonAnchored_entropicTime_threeOriginMass`) — this single clock is at
  once de Broglie, Yukawa, entropic, holographic-gravitational, and topological.  The
  mass-shell `(mc)² = (Re q)² − (Im q)²` is the Nagao–Nielsen Lorentzian form
  (`NagaoNielsenMassShellCone.nnLorentzForm_energyMomentum`), the same `(1,1)` interval as
  proper time; and Newton's constant is holographic, `G = ℏc/m²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Lorentz Lorentz.Vector SpaceTime

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime

/-- **The de Broglie clock-wave is luminal**: the Compton clock frequency times the Compton
wavelength (the Yukawa range) is the speed of light, `ω_C·λ_C = c`. -/
@[zil_level physical_theorem]
theorem comptonClock_luminal (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonFrequency m c ħ * comptonWavelength m c ħ = c := by
  unfold comptonFrequency comptonWavelength
  field_simp

/-- **The Compton–de Broglie internal phase** accumulated over a proper-time interval `τ`:
`φ = ω_C·τ = mc²τ/ℏ` — the internal clock reading, equal to the entropic action over `ℏ`. -/
def comptonPhase (m c ħ τ : ℝ) : ℝ := comptonFrequency m c ħ * τ

/-- **Compton-clock phase ratios are exact causal invariants.**  Under a causal automorphism
the proper time — and hence the de Broglie phase `φ = ω_C·τ` — scales by the common dilation
factor `√c`, which cancels in a ratio:
`φ(τ(eq,ep))·τ(q',p') = φ(τ(q,p))·τ(eq',ep')`.  The internal clock's phase ratios are read off
the causal order alone. -/
@[zil_level bridge_theorem]
theorem comptonPhase_ratio_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) (m c ħ : ℝ) (q p q' p' : SpaceTime 3) :
    comptonPhase m c ħ (properTime (e q) (e p)) * properTime q' p'
      = comptonPhase m c ħ (properTime q p) * properTime (e q') (e p') := by
  unfold comptonPhase
  rw [mul_assoc, properTime_ratio_causalAutomorphism e hcausal q p q' p', ← mul_assoc]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime

zil attach comptonClock_luminal where
  formalizes @ "claim:the-de-broglie-clock-wave-is-luminal-the-compton-clock-frequency-times-the-compton-wavelength-yukawa-range-equals-the-speed-of-light-omega-c-lambda-c-equals-c"

zil attach comptonPhase_ratio_causalAutomorphism where
  formalizes @ "claim:compton-de-broglie-clock-phase-ratios-are-exact-causal-invariants-the-internal-phase-omega-c-tau-scales-by-the-dilation-factor-which-cancels-in-a-ratio-so-the-clock-reading-ratios-are-fixed-by-the-causal-order",
  supported_by @ "lean:Lorentz.Vector.properTime_ratio_causalAutomorphism",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_eq_geometricProperTime"

zil_file_contract physlib.comptonClockMalamentProperTime where
  promises "Reading Malament's causally-reconstructed proper time with the Compton-de Broglie internal clock. The Compton frequency omega c equals m c squared over hbar is the de Broglie internal clock rate, and over a proper-time interval it accumulates the phase omega c times tau; its clock-wave is luminal, omega c times the Compton wavelength (the Yukawa range) equals the speed of light. Under a causal automorphism the phase scales by the dilation factor which cancels in a ratio, so Compton-clock phase ratios are exact causal invariants read off the causal order alone. The accumulated phase is the entropic action over hbar with rest-energy rate, so the Caticha entropic time equals this geometric proper time; at the three-origin mass the Compton mass is simultaneously the Yukawa, the Verlinde gravitational-horizon, and the Witten Chern-Simons topological mass, the mass-shell is the Nagao-Nielsen Lorentzian form, and Newton's constant is holographic."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
    "lean:Lorentz.Vector.properTime_ratio_causalAutomorphism"
  ]
  forbids_substitutes [
    "reading the dilation scaling of the Compton phase as an invariance rather than only its ratios",
    "claiming the three-origin mass identification is proved here rather than cited from the anchored-clock theorem"
  ]
  witnessed_by [
    comptonClock_luminal,
    comptonPhase_ratio_causalAutomorphism
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.comptonClockMalamentProperTime
