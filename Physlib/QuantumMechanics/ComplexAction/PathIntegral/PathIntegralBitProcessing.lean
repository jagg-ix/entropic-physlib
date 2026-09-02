/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ImaginaryLagrangian
public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
meta import Zil

/-!
# The complex path integral as bit processing

The repository's complex-action path integrals suppress paths by the entropic-damping
modulus `kuikenWeight ℏ S_I = exp(−S_I/ℏ)`.  This module proves that, across the whole
family, **the suppression exponent is a nat count**: with the imaginary action in its
entropic form `S_I = (ℏ/k_B)·S_ent` (`ImaginaryLagrangian.entropicAction`), every weight is

  `exp(−S_I/ℏ) = exp(−S_ent/k_B) = exp(−N_nats)`.

* `entropicNatCount` — the count `S_ent/k_B`, the quantity the information-dimension gate
  certifies as `[I]` under the Brillouin per-nat price of `k_B`;
* `kuikenWeight_entropicAction_eq_exp_natCount` — **the universal statement**: the
  path-integral weight of any entropic action is `e^{−nats}`;
* `caldeiraLeggett_imaginaryAction_eq_entropicAction` — the Caldeira–Leggett influence
  functional is an *instance*: its imaginary action `ℏφ`
  (`caldeiraLeggettSuppression_eq_kuiken`) is exactly the entropic action of the bath
  entropy `ΔS = k_B·φ`, so
* `caldeiraLeggettSuppression_eq_exp_natCount` — the Gaussian decoherence factor *is*
  `exp(−ΔS_bath/k_B)`: each path pair's coherence is erased at one weight-e-fold per nat
  transferred to the bath.  Composed with the Feynman–Kac sector's Landauer dichotomy
  (`DampedHeatLandauerDichotomy`: isometric ↔ zero Landauer erasures, damped ↔ positive
  bit-erasure count with `dampedHeat_bit_erasure_time`), the damped/decohering half of the
  path-integral SET is bit processing end to end.
* `fujiwaraComptonTickCount` — the Fujiwara time-ket phase at rest energy
  (`generalizedTimeKet_restEnergy_eq_comptonClock`) advances by `2π` per tick, with
  `ticks = mc²τ/(2πℏ)` — action over `h`.  The gate records the honest boundary: tick
  counts are `k_B`-free, hence **information-neutral** under the Brillouin price — clock
  ticks are not automatically nats; only entropy transfer is.

Inventory note: the repository has no Itô-named carrier (Itô calculus appears only as a
cited-alternative in `DiscreteEntropicTimeTrinity`'s docstring); the stochastic layer is
realized by the damped-heat / Feynman–Kac semigroups, which the Landauer dichotomy already
counts in bits.  Guarded by `Physlib.Meta.PathIntegralBitGate`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ImaginaryLagrangian
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing

/-- **The nat count** `S_ent/k_B` — entropy in Boltzmann units.  Dimensionless in SI;
carries exactly `[I]` under the Brillouin per-nat price of `k_B`
(`Physlib.Meta.PathIntegralBitGate`). -/
noncomputable def entropicNatCount (Sent kB : ℝ) : ℝ := Sent / kB

/-- **The universal statement: every entropic path-integral weight is `e^{−nats}`.**  The
Kuiken damping modulus of the entropic imaginary action `S_I = (ℏ/k_B)·S_ent` is exactly
`exp(−S_ent/k_B)`. -/
theorem kuikenWeight_entropicAction_eq_exp_natCount (Sent ħ kB : ℝ) (hħ : ħ ≠ 0) :
    kuikenWeight ħ (entropicAction Sent ħ kB) = Real.exp (-(entropicNatCount Sent kB)) := by
  unfold kuikenWeight entropicAction entropicNatCount
  congr 1
  field_simp

/-- The bath entropy produced by a Caldeira–Leggett decoherence event: `ΔS = k_B·φ`. -/
noncomputable def caldeiraLeggettEntropyProduced (M γ kB T τ ξ : ℝ) : ℝ :=
  kB * caldeiraLeggettDecoherence M γ kB T τ ξ

/-- **Caldeira–Leggett is an instance of the entropic action**: the influence functional's
imaginary action `ℏφ` is exactly `entropicAction ΔS ℏ k_B` at the bath entropy
`ΔS = k_B·φ`. -/
theorem caldeiraLeggett_imaginaryAction_eq_entropicAction (M γ kB T τ ξ ħ : ℝ)
    (hkB : kB ≠ 0) :
    ħ * caldeiraLeggettDecoherence M γ kB T τ ξ
      = entropicAction (caldeiraLeggettEntropyProduced M γ kB T τ ξ) ħ kB := by
  unfold entropicAction caldeiraLeggettEntropyProduced
  field_simp

/-- **The Caldeira–Leggett decoherence factor is `exp(−ΔS_bath/k_B)`** — the Gaussian
off-diagonal suppression counts the nats transferred to the bath: bit processing, path
pair by path pair. -/
theorem caldeiraLeggettSuppression_eq_exp_natCount (M γ kB T τ ξ : ℝ) (hkB : kB ≠ 0) :
    caldeiraLeggettSuppression M γ kB T τ ξ
      = Real.exp
          (-(entropicNatCount (caldeiraLeggettEntropyProduced M γ kB T τ ξ) kB)) := by
  unfold caldeiraLeggettSuppression entropicNatCount caldeiraLeggettEntropyProduced
  congr 1
  field_simp

/-- The Fujiwara/Compton tick count over duration `τ`: the rest-energy time-ket phase
advances by `2π` per tick. -/
noncomputable def fujiwaraComptonTickCount (m c ħ τ : ℝ) : ℝ :=
  comptonFrequency m c ħ * τ / (2 * Real.pi)

/-- The rest-energy phase is `2π` times the tick count. -/
theorem restEnergy_phase_eq_two_pi_ticks (m c ħ τ : ℝ) :
    comptonFrequency m c ħ * τ = 2 * Real.pi * fujiwaraComptonTickCount m c ħ τ := by
  unfold fujiwaraComptonTickCount
  field_simp

/-- **Tick count is action over `h`**: `ticks = mc²τ/(2πℏ)` — the worldline action in
units of Planck's constant. -/
theorem fujiwaraComptonTickCount_eq_action_over_h (m c ħ τ : ℝ) (hħ : ħ ≠ 0) :
    fujiwaraComptonTickCount m c ħ τ = m * c ^ 2 * τ / (2 * Real.pi * ħ) := by
  unfold fujiwaraComptonTickCount comptonFrequency
  field_simp

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing

zil attach kuikenWeight_entropicAction_eq_exp_natCount where
  formalizes @ "claim:every-complex-action-path-integral-weight-of-an-entropic-imaginary-\
action-is-exp-minus-the-entropy-in-boltzmann-units-a-nat-count",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ImaginaryLagrangian.entropicAction"

zil attach caldeiraLeggettSuppression_eq_exp_natCount where
  formalizes @ "claim:the-caldeira-leggett-gaussian-decoherence-factor-is-exactly-exp-\
minus-bath-entropy-over-kb-so-influence-functional-decoherence-is-nat-counting-bit-\
processing",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettSuppression_eq_kuiken",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing.caldeiraLeggett_imaginaryAction_eq_entropicAction"

zil attach fujiwaraComptonTickCount_eq_action_over_h where
  formalizes @ "claim:the-fujiwara-compton-rest-energy-tick-count-is-the-worldline-action-\
over-plancks-constant-and-is-information-neutral-under-the-brillouin-price-ticks-are-not-\
automatically-nats",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.generalizedTimeKet_restEnergy_eq_comptonClock"

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing
