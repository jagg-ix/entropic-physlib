/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing
public import Physlib.Thermodynamics.NewtonGIsolation
meta import Zil

/-!
# The path-integral nat ledger constrains the holographic Newton coupling

`PathIntegralBitProcessing` made the complex path integral's suppression exponents nat
counts; the holographic Newton chain (`NewtonGIsolation`, `GravitationalCouplingSystem`)
makes `G` the area-per-bit of a screen count.  Both ledgers carry the information
dimension `[I]`, and that shared dimension is leverage.  Three uses, each a theorem:

* **Validation — equipartition is Landauer content**
  (`screenNatContent_priced_eq_twice_restEnergy`): the holographic derivation postulates
  equipartition `½Nk_BT = Mc²`.  Read through the nat ledger this is: *the screen's `N`
  nats, each priced at its own temperature's Landauer energy `k_BT`, hold exactly the
  source's rest energy twice over* — `N·k_BT_screen = 2Mc²`.  The postulate that fixes the
  holographic `G` is a bit-energy bookkeeping identity, not an independent input.

* **Constraint — the screen-fill time** (`caldeiraLeggett_fills_screen_iff`): the
  Caldeira–Leggett bath writes `φ = ΔS_bath/k_B` nats in time `τ`; a screen of radius `R`
  at coupling `G` holds `holographicBits = 4πR²c³/(Gℏ)` nats.  The dynamical ledger
  saturates the static one **exactly at** `τ_fill = 2πR²c³/(GℏMγk_BTξ²)` — a new derived
  timescale linking influence-functional decoherence parameters to the holographic `G`.
  Faster decoherence than the screen can hold, at given `(R, G)`, is the falsification
  interface this bridge exposes.

* **Derivation of `G`'s information charge** (`Physlib.Meta.PathIntegralBitGate` §4): the
  holographic typing `G : L³T⁻²M⁻¹I⁻¹`, *assumed* as a convention by the WEP, temperature,
  length and force gates, is **forced** here: `G = A·c³/(ℏN)` with `N` the same `[I]`
  object the path integral counts gives `G` exactly one inverse nat.  The area-per-bit
  reading of Newton's constant is the unique typing consistent with the path-integral
  ledger.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge

/-- **Newton's constant as area per bit, as a carrier**: `G = A·c³/(ℏN)`.  With `N` typed
`[I]` — the same information dimension the path-integral nat ledger carries — this
carrier's dimension is exactly the holographic `L³T⁻²M⁻¹I⁻¹` every information gate has
assumed; the gate derives that typing rather than choosing it. -/
noncomputable def areaPerBitCoupling (A N ħ c : ℝ) : ℝ := A * c ^ 3 / (ħ * N)

/-- The carrier agrees with the screen-level isolation: at `N = holographicBits A G ℏ c`
the area-per-bit coupling returns `G`. -/
theorem areaPerBitCoupling_eq_newtonG (A G ħ c : ℝ)
    (hA : A ≠ 0) (hG : G ≠ 0) (hħ : ħ ≠ 0) (hc : c ≠ 0) :
    areaPerBitCoupling A (holographicBits A G ħ c) ħ c = G := by
  unfold areaPerBitCoupling holographicBits
  field_simp

/-- **Validation: the equipartition postulate is Landauer content.**  The screen's `N`
nats, each priced at the screen temperature's energy `k_B·T_screen`, hold exactly
`2Mc²` — the equipartition input `½Nk_BT = Mc²` of the holographic Newton derivation is
the statement that the screen's Landauer content is the source's rest energy (twice, for
the two-sided screen). -/
theorem screenNatContent_priced_eq_twice_restEnergy (M c N kB : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) :
    N * (kB * bitScreenTemperature M c N kB) = 2 * M * c ^ 2 := by
  unfold bitScreenTemperature
  field_simp

/-- **The screen-fill time**: the duration in which the Caldeira–Leggett bath writes as
many nats as a radius-`R` screen at coupling `G` can hold. -/
noncomputable def screenFillTime (M γ kB T ξ R G ħ c : ℝ) : ℝ :=
  2 * Real.pi * R ^ 2 * c ^ 3 / (G * ħ * M * γ * kB * T * ξ ^ 2)

/-- **Constraint: the dynamical ledger saturates the static one exactly at the fill
time.**  `ΔS_bath/k_B = holographicBits (sphereArea R) G ℏ c` **iff** `τ = τ_fill` — the
influence-functional nat production meets the holographic screen capacity at one derived
time, tying the Caldeira–Leggett parameters `(M, γ, T, ξ)` to the holographic `(R, G)`. -/
theorem caldeiraLeggett_fills_screen_iff (M γ kB T τ ξ R G ħ c : ℝ)
    (hM : M ≠ 0) (hγ : γ ≠ 0) (hkB : kB ≠ 0) (hT : T ≠ 0) (hξ : ξ ≠ 0)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) :
    entropicNatCount (caldeiraLeggettEntropyProduced M γ kB T τ ξ) kB
        = holographicBits (sphereArea R) G ħ c
      ↔ τ = screenFillTime M γ kB T ξ R G ħ c := by
  unfold entropicNatCount caldeiraLeggettEntropyProduced caldeiraLeggettDecoherence
    holographicBits sphereArea screenFillTime
  rw [mul_comm kB _, mul_div_assoc, div_self hkB, mul_one]
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h / 2
  · intro h
    rw [h]
    field_simp
    ring

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge

zil attach screenNatContent_priced_eq_twice_restEnergy where
  formalizes @ "claim:the-equipartition-postulate-of-the-holographic-newton-derivation-is-\
the-statement-that-the-screens-landauer-nat-content-priced-at-its-own-temperature-equals-\
twice-the-source-rest-energy",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.bitScreenTemperature_solves_equipartition"

zil attach caldeiraLeggett_fills_screen_iff where
  formalizes @ "claim:the-caldeira-leggett-nat-production-saturates-the-holographic-screen-\
capacity-exactly-at-the-derived-fill-time-two-pi-r-squared-c-cubed-over-g-hbar-m-gamma-kb-\
t-xi-squared-a-new-constraint-tying-decoherence-parameters-to-the-holographic-g",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing.caldeiraLeggettSuppression_eq_exp_natCount",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.newtonG_eq_area_per_bit"

zil attach areaPerBitCoupling_eq_newtonG where
  formalizes @ "claim:the-area-per-bit-carrier-a-c-cubed-over-hbar-n-returns-newtons-g-at-\
the-holographic-count-and-with-n-typed-in-the-information-dimension-forces-the-holographic-\
typing-of-g-as-one-inverse-nat",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.newtonG_isolated"

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge
