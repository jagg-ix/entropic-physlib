/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
meta import Zil

/-!
# The entropic-time arrow of the Compton clock: `dτ_ent/dτ ≥ 0`

The game-universe framework (gu.md §5.3) leaves an *explicit open request*: to "specify
conditions under which `dτ_ent/dτ ≥ 0`", where the entropic time is `τ_ent = S_I/ℏ` with `S_I`
the imaginary part of the action.  For the Compton-anchored clock the calibration is
`S_I = mc²·τ` (rest energy × proper time), so the entropic time is exactly the Compton phase,

`τ_ent = S_I/ℏ = mc²τ/ℏ = ω_C·τ = comptonPhase`,

and this module closes the request: its rate is `dτ_ent/dτ = ω_C ≥ 0`
(`entropicTime_rate_nonneg`), so the entropic time is monotone in proper time
(`comptonPhase_monotone`), and strictly increasing for a genuine mass
(`comptonPhase_strictMono`).  The entropic action is the rest energy times proper time
(`ħ_comptonPhase_eq_restEnergy_properTime`).

**Honest scope.**  This realizes gu.md's *standard-physics* clock/action axioms (Axiom 6,
Axiom 2.2, §5.3) — not the "minimal game universe" refinement, whose whole point is to *not
assume* the quantum apparatus.  The Compton-anchored clock is the **reversible limit**: its
rate `ω_C` is constant and its generator is unitary, so the arrow `dτ_ent/dτ = ω_C ≥ 0` holds
at the boundary of the reversibility spectrum, *not* through entropy production.  Per gu.md
(line 994) "the intended relationship is not that time equals entropy": the entropic time
here is *proportional* to proper time via the rest energy — monotone, but not identified with
entropy.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow

/-- **The entropic-time arrow `dτ_ent/dτ ≥ 0`** (gu.md §5.3, closing its explicit open
request): the rate of the entropic time `τ_ent = ω_C·τ` in proper time is the Compton
frequency `ω_C = mc²/ℏ ≥ 0` for a non-negative mass. -/
@[zil_level bridge_theorem]
theorem entropicTime_rate_nonneg (m c ħ : ℝ) (hm : 0 ≤ m) (hħ : 0 < ħ) :
    0 ≤ comptonFrequency m c ħ := by
  unfold comptonFrequency
  positivity

/-- **The entropic action is the rest energy times proper time** `S_I = ℏ·τ_ent = mc²·τ`. -/
@[zil_level physical_theorem]
theorem ħ_comptonPhase_eq_restEnergy_properTime (m c ħ τ : ℝ) (hħ : ħ ≠ 0) :
    ħ * comptonPhase m c ħ τ = m * c ^ 2 * τ := by
  unfold comptonPhase comptonFrequency
  field_simp

/-- **The entropic time is monotone in proper time** — the arrow condition of gu.md §5.3
holds: `τ₁ ≤ τ₂ ⟹ τ_ent(τ₁) ≤ τ_ent(τ₂)`. -/
@[zil_level bridge_theorem]
theorem comptonPhase_monotone (m c ħ : ℝ) (hm : 0 ≤ m) (hħ : 0 < ħ) :
    Monotone (comptonPhase m c ħ) := by
  intro a b hab
  unfold comptonPhase
  exact mul_le_mul_of_nonneg_left hab (entropicTime_rate_nonneg m c ħ hm hħ)

/-- **The entropic time strictly increases with proper time** for a genuine mass — the strict
arrow of the reversible Compton clock. -/
@[zil_level physical_theorem]
theorem comptonPhase_strictMono (m c ħ : ℝ) (hm : 0 < m) (hc : c ≠ 0) (hħ : 0 < ħ) :
    StrictMono (comptonPhase m c ħ) := by
  have hpos : 0 < comptonFrequency m c ħ := by unfold comptonFrequency; positivity
  intro a b hab
  unfold comptonPhase
  exact mul_lt_mul_of_pos_left hab hpos

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow

zil attach entropicTime_rate_nonneg where
  formalizes @ "claim:the-entropic-time-arrow-d-tau-ent-over-d-tau-is-the-compton-frequency-omega-c-which-is-nonnegative-for-a-nonnegative-mass-closing-the-explicit-open-request-of-the-game-universe-entropic-time-axiom",
  caveat @ "claim:this-is-the-reversible-limit-with-constant-rate-and-unitary-generator-the-arrow-holds-at-the-boundary-of-the-reversibility-spectrum-not-through-entropy-production-and-the-entropic-time-is-proportional-to-proper-time-via-the-rest-energy-not-identified-with-entropy"

zil attach comptonPhase_monotone where
  supported_by @ "lean:entropicTime_rate_nonneg",
  formalizes @ "claim:the-entropic-time-tau-ent-equals-omega-c-tau-is-monotone-in-proper-time-so-the-game-universe-arrow-condition-holds"

zil attach ħ_comptonPhase_eq_restEnergy_properTime where
  formalizes @ "claim:the-entropic-action-is-the-rest-energy-times-proper-time-s-i-equals-hbar-tau-ent-equals-m-c-squared-tau"

zil_file_contract physlib.comptonClockEntropicArrow where
  promises "Closing the explicit open request of the game-universe entropic-time axiom to specify when d tau-ent over d tau is nonnegative. For the Compton-anchored clock the imaginary action is the rest energy times proper time, so the entropic time equals the Compton phase omega c tau, its rate is the Compton frequency m c squared over hbar which is nonnegative for a nonnegative mass, the entropic time is monotone in proper time and strictly increasing for a genuine mass, and the entropic action is the rest energy times proper time. This realizes the standard-physics clock and action axioms at the reversible limit with constant rate and unitary generator - the arrow holds at the boundary of the reversibility spectrum, not through entropy production, and the entropic time is proportional to proper time via the rest energy rather than identified with entropy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonPhase",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency"
  ]
  forbids_substitutes [
    "identifying the entropic time with entropy rather than with proper time via the rest energy",
    "reading the reversible constant-rate arrow as arising from entropy production"
  ]
  witnessed_by [
    entropicTime_rate_nonneg,
    ħ_comptonPhase_eq_restEnergy_properTime,
    comptonPhase_monotone,
    comptonPhase_strictMono
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.comptonClockEntropicArrow
