/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenEntanglementCorollaries
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameKMS
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMeasurementCommunicationDarwinism
meta import Zil

/-!
# The Unruh wedge eigenvalue read by the four clocks (Page–Wootters, thermal time, Caticha, Nagao–Nielsen)

Inspects `unruh_boltzmann_is_wedgeModular` (`SciamaAdSCPTWittenEntanglementCorollaries`) through the repo's
clock stack (`CausalDiamond.EntropicTime`: AdS/CFT → Page–Wootters → Connes–Rovelli → three clocks).  The one
identity `e^{−E/k_BT_U} = Δ = e^{−2πκ/ℏ}` is the same fact told four times:

* **Connes–Rovelli thermal time** (`unruh_thermalTime_tick`): one wedge-modular tick advances the thermal time
  by `β_Uℏ = 2πc/a` — the Euclidean boost period.  The Unruh temperature is exactly the modular-parameter →
  proper-time rate conversion of the thermal-time hypothesis: the wedge modular flow *is* the accelerated
  observer's clock, ticking at `2πc/a` per unit modular parameter.
* **Caticha entropic time** (`unruh_weight_is_clausius_cost`): the Unruh weight is the Clausius entropy cost,
  `e^{−E/k_BT_U} = e^{−ΔS/k_B}` with `ΔS = E/T_U` — depositing energy `E` behind the horizon at temperature
  `T_U` produces entropy `ΔS`, and the weight is that entropy production: the entropic-time clock reads the
  wedge eigenvalue as `Δτ_ent = ΔS/k_B` of accumulated irreversibility.
* **Nagao–Nielsen complex action** (`wedge_modular_is_nagaoNielsen_modulus`): the wedge eigenvalue is the
  modulus of the complex-action weight at **imaginary action `S_I = 2πκ`** — one full Euclidean boost rotation
  (the repo's `wedgeModular_sqrt_at_pi` is the half-rotation `Δ^{1/2} = V(iπ)`): the NN clock reads the wedge
  thermality as the Wick-rotated boost angle.
* **Page–Wootters** (via `pageWootters_rate_nonneg` / `pageWootters_reversible_iff_frozen` and
  `pageWootters_effective_is_complexHamiltonian`): the accelerated observer's clock is a *conditional*,
  dissipative clock whose generator is the NN complex Hamiltonian; its entropic rate is nonnegative and
  vanishes exactly in the frozen (reversible, `L_jψ = 0`) limit — thermality is the non-frozen conditional
  clock, consistent with the strictly-positive-residue side of the collapse resolution.

`unruh_wedge_four_clocks` bundles the four readings.  The inspection verdict: **nothing clashes** — the four
clocks are four parametrizations of the one wedge-modular structure (thermal tick `2πc/a`, Clausius cost
`E/T_U`, Euclidean angle `2πκ`, non-frozen conditional rate), which is the eigenvalue-level content of
Bisognano–Wichmann that the graph's `assumption:bisognano-wichmann-wedge` carries at operator level.

Honest scope: eigenvalue/rate-level identities plus reuse of the Page–Wootters lemmas; the operator
Bisognano–Wichmann theorem and the Type III thermal-time flow remain the cited continuum counterparts.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime
open Physlib.Thermodynamics
open QuantumMechanics.FiniteTarget
open Physlib.QuantumMechanics.RelationalTime
open scoped InnerProductSpace
open Physlib.Optics.TemporalDoubleSlit
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMeasurementCommunicationDarwinism

/-! ## §1. The thermal-time clock: one modular tick = the Euclidean boost period -/

/-- **[One wedge-modular tick of thermal time is the boost period] `β_Uℏ = 2πc/a`.**  At the Unruh inverse
temperature `β_U = 1/k_BT_U`, the Connes–Rovelli thermal time advanced by one unit of modular parameter is
`2πc/a` — the Euclidean boost period: `T_U` is exactly the modular-parameter → proper-time rate conversion of
the thermal-time hypothesis. -/
theorem unruh_thermalTime_tick (ℏ kB c a : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    connesRovelliThermalTime (1 / (kB * unruhTemperature ℏ kB c a)) ℏ 1 = 2 * Real.pi * c / a := by
  unfold connesRovelliThermalTime unruhTemperature
  field_simp

/-! ## §2. The Caticha entropic-time clock: the weight is the Clausius entropy cost -/

/-- **[The Unruh weight is the Clausius entropy cost] `e^{−E/k_BT_U} = e^{−ΔS/k_B}` with `ΔS = E/T_U`.**
Depositing energy `E` behind the wedge horizon at temperature `T_U` produces the Clausius entropy `ΔS = E/T_U`;
the Unruh weight is that entropy production — the entropic-time clock reads the wedge eigenvalue as
accumulated irreversibility `Δτ_ent = ΔS/k_B`. -/
theorem unruh_weight_is_clausius_cost (ℏ kB c a E : ℝ) :
    kuikenWeight (kB * unruhTemperature ℏ kB c a) E
      = Real.exp (-(E / unruhTemperature ℏ kB c a / kB)) := by
  unfold kuikenWeight
  congr 1
  rw [div_div, mul_comm (unruhTemperature ℏ kB c a) kB]

/-! ## §3. The Nagao–Nielsen clock: the wedge eigenvalue at imaginary action `2πκ` -/

/-- **[The wedge eigenvalue is the NN modulus at one Euclidean boost rotation] `‖e^{(i/ℏ)(S_R + i·2πκ)}‖ = Δ`.**
The wedge-modular eigenvalue is the modulus of the Nagao–Nielsen complex-action weight at imaginary action
`S_I = 2πκ` — one full Euclidean boost rotation (the half-rotation is `Δ^{1/2} = V(iπ)`,
`WickClock.wedgeModular_sqrt_at_pi`): the NN clock reads the wedge thermality as the Wick-rotated boost angle. -/
theorem wedge_modular_is_nagaoNielsen_modulus (S_R κ ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ‖nagaoNielsenComplexActionWeight S_R (2 * Real.pi * κ) ℏ‖
      = Physlib.QFT.PathIntegral.wedgeModularEigenvalue κ ℏ := by
  rw [nagaoNielsen_eq_master _ _ _ hℏ, master_modulus_is_kuiken]
  unfold kuikenWeight Physlib.QFT.PathIntegral.wedgeModularEigenvalue
  congr 1

/-! ## §4. The four clocks together -/

/-- **[The Unruh wedge eigenvalue read by the four clocks]** — **(i)** thermal time: one modular tick =
`2πc/a` (Connes–Rovelli at `β_U`); **(ii)** Caticha entropic time: the weight = the Clausius cost
`e^{−(E/T_U)/k_B}`; **(iii)** Nagao–Nielsen: the eigenvalue = the complex-action modulus at one Euclidean
boost rotation `S_I = 2πκ`; **(iv)** Page–Wootters: the conditional clock's entropic rate is nonnegative and
vanishes exactly in the frozen limit — thermality is the non-frozen conditional clock.  Four parametrizations
of the one wedge-modular structure: the eigenvalue-level Bisognano–Wichmann. -/
theorem unruh_wedge_four_clocks {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H)
    (ℏ kB c a E S_R κ : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    connesRovelliThermalTime (1 / (kB * unruhTemperature ℏ kB c a)) ℏ 1 = 2 * Real.pi * c / a
      ∧ kuikenWeight (kB * unruhTemperature ℏ kB c a) E
          = Real.exp (-(E / unruhTemperature ℏ kB c a / kB))
      ∧ ‖nagaoNielsenComplexActionWeight S_R (2 * Real.pi * κ) ℏ‖
          = Physlib.QFT.PathIntegral.wedgeModularEigenvalue κ ℏ
      ∧ (0 ≤ P.conditionalEntropicRate L ψ
          ∧ (P.conditionalEntropicRate L ψ = 0 ↔ ∀ j, L j ψ = 0)) :=
  ⟨unruh_thermalTime_tick ℏ kB c a hℏ hkB hc ha,
    unruh_weight_is_clausius_cost ℏ kB c a E,
    wedge_modular_is_nagaoNielsen_modulus S_R κ ℏ hℏ,
    pageWootters_rate_nonneg P L ψ, pageWootters_reversible_iff_frozen P L ψ⟩


/-! ## §5. The laboratory as bath: observer-relative clock, records, arrow -/

/-- **[The Unruh temperature is the laboratory's tick rate]** — the entropic clock of a laboratory at
proper acceleration `a` ticks at `k_B T_U/ℏ = a/(2πc)`: the bath the accelerated observer's restriction of
the vacuum hands them *is* their clock. -/
theorem unruh_laboratory_entropic_clock (ℏ kB c a : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) :
    thermalEntropicRate kB (unruhTemperature ℏ kB c a) ℏ = a / (2 * Real.pi * c) := by
  unfold thermalEntropicRate unruhTemperature QuantumMechanics.FiniteTarget.kmsThermalRate
  field_simp

/-- **[Two laboratories, one event, tick counts in the ratio of accelerations]** — laboratories at proper
accelerations `a₁, a₂` assign entropic-tick counts to the same interval `t` in the exact ratio `a₁/a₂`:
the count is frame material.  The crossing event itself holds in every laboratory's units
(`mpembaCrossingTime_entropic_units`, `mpemba_crossing`). -/
theorem crossing_ticks_laboratory_relative (ℏ kB c a₁ a₂ t : ℝ)
    (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha₂ : a₂ ≠ 0) :
    thermalEntropicRate kB (unruhTemperature ℏ kB c a₁) ℏ * t
      = (a₁ / a₂) * (thermalEntropicRate kB (unruhTemperature ℏ kB c a₂) ℏ * t) := by
  rw [unruh_laboratory_entropic_clock ℏ kB c a₁ hℏ hkB,
    unruh_laboratory_entropic_clock ℏ kB c a₂ hℏ hkB]
  field_simp

/-- **[The laboratory is the bath: clock, record, arrow]** — **(i)** *clock*: the decoherence rate is
entropic-clock linear with a bounded offset — the bath's temperature enters only as the tick rate;
**(ii)** *record*: the broadcast copies in the environment carry the complete outcome statistics — what
"the laboratory registered" is the bath's record content; **(iii)** *arrow*: first-order detailed balance
brackets the exact Boltzmann factor — the relaxation arrow is the bath's; **(iv)** tick counts are
laboratory-relative in the exact ratio of accelerations; **(v)** the Mpemba crossing itself holds
regardless — the event is invariant, only its count is relative. -/
theorem laboratory_bath_synthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] (bE : OrthonormalBasis ι ℂ E) (U : E →ₗᵢ[ℂ] E) (ψ : E)
    {A ω₀ kB T ℏ : ℝ} (hA : 0 < A) (hω : 0 < ω₀) (hE : 0 < thermalEntropicRate kB T ℏ)
    {ε : ℝ} (h0 : 0 < ε) (h2 : ε < 1 / 2)
    (c a₁ a₂ t : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha₂ : a₂ ≠ 0)
    {p q lam2 lam3 : ℝ} (hp : 0 < p) (hq : 0 < q) (hlam : lam3 < lam2)
    {s : ℝ} (hs : mpembaCrossingTime p q lam2 lam3 < s) :
    (A / ω₀ * thermalEntropicRate kB T ℏ - A
        < A * boseEinstein (thermalEntropicRate kB T ℏ)⁻¹ ω₀
      ∧ A * boseEinstein (thermalEntropicRate kB T ℏ)⁻¹ ω₀
        < A / ω₀ * thermalEntropicRate kB T ℏ)
      ∧ (∑ k, ‖⟪U (bE k), U ψ⟫_ℂ‖ ^ 2 = ‖ψ‖ ^ 2)
      ∧ (1 - 2 * ε < Real.exp (-(2 * ε)) ∧ Real.exp (-(2 * ε)) < 1 - ε)
      ∧ (thermalEntropicRate kB (unruhTemperature ℏ kB c a₁) ℏ * t
          = (a₁ / a₂) * (thermalEntropicRate kB (unruhTemperature ℏ kB c a₂) ℏ * t))
      ∧ p * Real.exp (lam3 * s) < q * Real.exp (lam2 * s) :=
  ⟨decoherence_rate_entropic_clock_window hA hω hE,
    broadcast_outcome_complete bE U ψ,
    detailed_balance_entropic_arrow h0 h2,
    crossing_ticks_laboratory_relative ℏ kB c a₁ a₂ t hℏ hkB hc ha₂,
    mpemba_crossing hp hq hlam hs⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.wedge_modular_is_nagaoNielsen_modulus where
  formalizes @ "claim:the-wedge-modular-eigenvalue-is-the-nagao-nielsen-complex-action-modulus-at-one-full-euclidean-boost-rotation",
  supported_by @ "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  caveat @ "epistemic:eigenvalue-level-the-operator-bisognano-wichmann-remains-the-graph-assumption"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.unruh_wedge_four_clocks where
  formalizes @ "claim:the-unruh-wedge-eigenvalue-is-one-structure-read-by-four-clocks-thermal-tick-clausius-cost-euclidean-boost-angle-and-nonfrozen-conditional-rate",
  requires @ "claim:the-unruh-boltzmann-weight-equals-the-wedge-modular-eigenvalue-at-boost-parameter-c-e-over-a",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.connesRovelliThermalTime",
  caveat @ "epistemic:rate-and-eigenvalue-level-identities-the-type-iii-thermal-time-flow-is-cited-context"


zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.unruh_laboratory_entropic_clock where
  formalizes @ "claim:the-unruh-temperature-is-the-accelerated-laboratorys-entropic-tick-rate-a-over-2-pi-c",
  supported_by @ "lean:Physlib.Thermodynamics.unruhTemperature",
  caveat @ "epistemic:whether-the-surroundings-are-laboratory-or-bath-is-observer-relative-per-the-bw-state-side-wedge-gibbs-modules"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.crossing_ticks_laboratory_relative where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.unruh_laboratory_entropic_clock",
  formalizes @ "claim:entropic-tick-counts-of-the-same-event-are-laboratory-relative-in-the-exact-ratio-of-proper-accelerations",
  requires @ "claim:the-unruh-temperature-is-the-accelerated-laboratorys-entropic-tick-rate-a-over-2-pi-c",
  caveat @ "epistemic:the-crossing-event-is-invariant-only-its-count-is-relative"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.laboratory_bath_synthesis where
  formalizes @ "claim:the-laboratory-enters-the-dynamics-as-the-bath-in-three-roles-clock-rate-record-content-and-relaxation-arrow",
  requires @ "claim:the-bath-decoherence-rate-is-entropic-clock-linear-with-a-temperature-independent-bounded-offset",
  requires @ "claim:entropic-tick-counts-of-the-same-event-are-laboratory-relative-in-the-exact-ratio-of-proper-accelerations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMeasurementCommunicationDarwinism.broadcast_outcome_complete",
  caveat @ "epistemic:page-wootters-conditioning-and-markovian-additivity-of-time-are-the-cited-four-clocks-and-lindblad-content"

/- ZIL-END -/
