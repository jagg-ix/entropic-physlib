/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannel
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
meta import Zil

/-!
# One-level channel: rate calibration, parameter identifiability, held-out prediction

The one-level LDDL channel relaxes the excited occupation as `N(t) = f + (N₀ - f)·exp(-2γt)`
(`RateData.oneLevelChannelAt_excitedOccupation`). This file turns that exact law into an
*anti-circular* empirical test — a calibration → frozen-parameters → held-out-prediction protocol in
which the calibration observables and the tested observable are disjoint.

* **Calibration** fixes the two rate parameters from the *independently counted* in/out transition
  rates: `f = Γ_in/(Γ_in + Γ_out)` and `2γ = Γ_in + Γ_out` (`RateData.ofInOutRates`,
  `ofInOutRates_two_gamma`).
* **Identifiability** — the calibration map is injective (`ofInOutRates_injective`): the counts are
  recovered from `(f, γ)` as `Γ_in = 2γf`, `Γ_out = 2γ(1-f)`. So `f, γ` are *fixed by the counts*, not
  fitted to the occupation trajectory: there is no free parameter to absorb a bad prediction.
* **Held-out prediction** is then the deterministic function `predictedOccupation` of the frozen
  `(f, γ, N₀)`, anchored at the initial datum (`predictedOccupation_zero`) and relaxing to the
  calibrated fixed point `f` (`predictedOccupation_tendsto`); trajectories with equal identified
  parameters coincide (`predictedOccupation_congr`).
* **Binary relative-entropy floor** — the Bernoulli KL of the occupation against the stationary
  reference is nonnegative and vanishes exactly at the calibrated fixed point
  (`binaryKL_nonneg`, `binaryKL_eq_zero_iff`), specializing `klDivergence`.

Honest scope: the relaxation law itself is the exact two-state master-equation solution, shared by every
Markovian open-system model — passing it is a non-circular universality test, not a proof that entropic
time is the mechanism. The content here is that the law is testable *without calibration/test leakage*.
The strict finite-time production `d/dt D_bin = -σ(t) < 0` along the trajectory is the intended follow-up.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Filter
open scoped Topology
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

/-- Calibrate the one-level rates from independently counted in/out transition rates:
`γ = (Γ_in + Γ_out)/2` and `f = Γ_in/(Γ_in + Γ_out)`. -/
def RateData.ofInOutRates (Γin Γout : ℝ) (hin : 0 < Γin) (hout : 0 < Γout) : RateData where
  gamma := (Γin + Γout) / 2
  occupation := Γin / (Γin + Γout)
  gamma_pos := by positivity
  occupation_nonneg := by positivity
  occupation_le_one := by
    rw [div_le_one (by positivity)]; linarith

/-- The calibration reproduces od6's `2γ = Γ_in + Γ_out`. -/
theorem RateData.ofInOutRates_two_gamma (Γin Γout : ℝ) (hin : 0 < Γin) (hout : 0 < Γout) :
    2 * (RateData.ofInOutRates Γin Γout hin hout).gamma = Γin + Γout := by
  show 2 * ((Γin + Γout) / 2) = Γin + Γout
  ring

/-- **Identifiability.** The calibration `(Γ_in, Γ_out) ↦ (f, γ)` is injective: equal calibrated
parameters force equal counts. Hence `f` and `γ` are determined by the independently measured rates —
there is no fitting freedom to absorb a failed held-out prediction. -/
theorem RateData.ofInOutRates_injective
    {Γin Γout Γin' Γout' : ℝ} (hin : 0 < Γin) (hout : 0 < Γout)
    (hin' : 0 < Γin') (hout' : 0 < Γout')
    (h : RateData.ofInOutRates Γin Γout hin hout = RateData.ofInOutRates Γin' Γout' hin' hout') :
    Γin = Γin' ∧ Γout = Γout' := by
  have hS : 0 < Γin + Γout := by positivity
  have hS' : 0 < Γin' + Γout' := by positivity
  have hg : (Γin + Γout) / 2 = (Γin' + Γout') / 2 := congrArg RateData.gamma h
  have hsum : Γin + Γout = Γin' + Γout' := by linarith
  have hf : Γin / (Γin + Γout) = Γin' / (Γin' + Γout') := congrArg RateData.occupation h
  rw [← hsum] at hf
  have hΓin : Γin = Γin' := by
    field_simp at hf
    exact hf
  exact ⟨hΓin, by linarith⟩

/-- The held-out prediction: the excited occupation at time `t` from the frozen calibrated `(f, γ)`
and the initial occupation `N₀`. -/
def RateData.predictedOccupation (r : RateData) (N₀ t : ℝ) : ℝ :=
  r.occupation + (N₀ - r.occupation) * Real.exp (-2 * r.gamma * t)

/-- Initial-condition anchor: the prediction starts at the measured initial occupation. -/
@[simp] theorem RateData.predictedOccupation_zero (r : RateData) (N₀ : ℝ) :
    r.predictedOccupation N₀ 0 = N₀ := by
  simp [RateData.predictedOccupation]

/-- Fixed-point anchor: the prediction relaxes to the calibrated stationary occupation `f`. -/
theorem RateData.predictedOccupation_tendsto (r : RateData) (N₀ : ℝ) :
    Tendsto (fun t => r.predictedOccupation N₀ t) atTop (𝓝 r.occupation) := by
  have hlin : Tendsto (fun t : ℝ => -2 * r.gamma * t) atTop atBot := by
    have h1 : Tendsto (fun t : ℝ => 2 * r.gamma * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (show (0:ℝ) < 2 * r.gamma by have := r.gamma_pos; positivity)
        tendsto_id
    have heq : (fun t : ℝ => -2 * r.gamma * t) = fun t => -(2 * r.gamma * t) := by
      funext t; ring
    rw [heq]
    exact tendsto_neg_atTop_atBot.comp h1
  have hexp : Tendsto (fun t : ℝ => Real.exp (-2 * r.gamma * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hmain :
      Tendsto (fun t => r.occupation + (N₀ - r.occupation) * Real.exp (-2 * r.gamma * t))
        atTop (𝓝 (r.occupation + (N₀ - r.occupation) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hexp)
  simpa [RateData.predictedOccupation] using hmain

/-- The prediction depends only on the identified parameters `(f, γ)` and the initial datum — two
rate models with the same calibrated parameters predict identical held-out trajectories. -/
theorem RateData.predictedOccupation_congr {r₁ r₂ : RateData} (N₀ t : ℝ)
    (hocc : r₁.occupation = r₂.occupation) (hgam : r₁.gamma = r₂.gamma) :
    r₁.predictedOccupation N₀ t = r₂.predictedOccupation N₀ t := by
  simp [RateData.predictedOccupation, hocc, hgam]

/-- The Bernoulli distribution `(x, 1-x)` of a two-state occupation. -/
def binaryDist (x : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then x else 1 - x

theorem binaryDist_sum (x : ℝ) : ∑ i, binaryDist x i = 1 := by
  simp [binaryDist, Fin.sum_univ_two]

/-- Bernoulli (binary) relative entropy of occupation `N` against reference `f`,
`D_bin(N‖f) = N·log(N/f) + (1-N)·log((1-N)/(1-f))`, as the two-point `klDivergence`. -/
def binaryKL (N f : ℝ) : ℝ := klDivergence (binaryDist N) (binaryDist f)

/-- **Second-law floor.** The binary relative entropy of any physical occupation against the calibrated
stationary reference is nonnegative. -/
theorem binaryKL_nonneg {N f : ℝ} (hN0 : 0 ≤ N) (hN1 : N ≤ 1) (hf0 : 0 < f) (hf1 : f < 1) :
    0 ≤ binaryKL N f := by
  rw [binaryKL]
  apply klDivergence_nonneg
  · intro i; fin_cases i <;> simp [binaryDist] <;> linarith
  · intro i; fin_cases i <;> simp [binaryDist] <;> linarith
  · exact binaryDist_sum N
  · exact binaryDist_sum f

/-- The binary relative entropy vanishes **exactly** at the calibrated fixed point `N = f`. -/
theorem binaryKL_eq_zero_iff {N f : ℝ} (hN0 : 0 < N) (hN1 : N < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    binaryKL N f = 0 ↔ N = f := by
  have hpN : ∀ i, 0 < binaryDist N i := by
    intro i; fin_cases i <;> simp [binaryDist] <;> linarith
  have hpf : ∀ i, 0 < binaryDist f i := by
    intro i; fin_cases i <;> simp [binaryDist] <;> linarith
  rw [binaryKL, klDivergence_eq_zero_iff hpN hpf (binaryDist_sum N) (binaryDist_sum f)]
  constructor
  · intro h
    have hval := congrFun h 0
    simpa [binaryDist] using hval
  · intro h
    funext i
    fin_cases i <;> simp [binaryDist, h]

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.ofInOutRates_two_gamma where
  formalizes @ "claim:the-one-level-total-relaxation-rate-two-gamma-equals-the-sum-of-the-independently-counted-in-and-out-transition-rates",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.ofInOutRates_injective where
  formalizes @ "claim:the-one-level-relaxation-parameters-f-and-gamma-are-identified-by-the-independent-in-out-transition-counts-injectively-not-fitted-to-the-occupation-trajectory",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-an-anti-circular-identifiability-result-fixing-the-calibration-observables-disjoint-from-the-held-out-occupation-observable-not-a-derivation-of-the-rates-from-first-principles"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.predictedOccupation_tendsto where
  formalizes @ "claim:the-calibrated-held-out-one-level-occupation-prediction-relaxes-to-the-independently-fixed-stationary-occupation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelChannelAt_excitedOccupation",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.binaryKL_eq_zero_iff where
  formalizes @ "claim:the-binary-relative-entropy-of-the-occupation-against-the-stationary-reference-vanishes-exactly-at-the-calibrated-fixed-point",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_eq_zero_iff",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-exact-two-state-relaxation-law-and-its-monotone-relative-entropy-are-shared-by-every-markovian-open-system-model-passing-this-is-a-non-circular-universality-test-not-a-demonstration-that-entropic-time-is-the-mechanism"

/- ZIL-END -/
