/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettGaussianSaddle
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

meta import Zil

/-!
# The Caldeira–Leggett influence functional: Markov kernel, renormalization, decoherence (Nishimura–Watanabe 2503.20699)

The detailed companion (arXiv:2503.20699, §2) to `ComplexSaddleDecoherence`/`CaldeiraLeggettOhmicRenormalization`
(arXiv:2408.16627). It **derives** — via the Feynman–Vernon influence functional `e^{−W(x,x̃)}` (Eqs. 2.15–2.31),
the Ohmic spectral density and the Markov approximation — the same closed-form endpoints already formalized in this
arc, which this module links back to them. This is the influence-functional route to what the complex-saddle route
(`CaldeiraLeggettGaussianSaddle`) reaches by completing the square.

Tracing out the Ohmic bath gives the real/imaginary influence kernels `W_R, W_I` built from `α(τ)` (Eq. 2.18). In
the Markov limit `ω_cut ≫ 1/τ₀` the kernel collapses to the **sinc kernel**

`f(τ) = ∫_{−ω_cut}^{ω_cut} (dω/2π) cos(ωτ) = sin(ω_cut τ)/(π τ)`,   `f(0) = ω_cut/π`   (Eqs. 2.26–2.27),

which approaches `δ(τ)`. Two consequences match this arc exactly:

* the imaginary kernel's local term **renormalizes the frequency** `ω_r² = ω_b² − (Δω)²`, `(Δω)² = 4γω_cut/π`
  (Eq. 2.29) — identical to `CaldeiraLeggettOhmicRenormalization.renormFreqSq_eq_closed` (Eq. 6 of 2408.16627),
  and `(Δω)² = 4γ·f(0)`;
* the real kernel gives the **decoherence exponent** `W_R = (2Mγ/β) ∫₀^t (x−x̃)²` (Eq. 2.31) — for a sustained
  separation `ξ` over time `t`, `W_R = (2Mγ/β) ξ² t`, identical to `CaldeiraLeggettDecoherence` at `k_B = 1`,
  `T = 1/β` (the fluctuation–dissipation temperature).

* **§A — the Markov (sinc) kernel (Eqs. 2.26–2.27).** `markovKernel`; **`markovKernel_zero`** (`f(0) = ω_cut/π`),
  **`markovKernel_eq_sinc`** (`f(τ) = sin(ω_cut τ)/(π τ)`).
* **§B — frequency renormalization (Eq. 2.29), linked to `CaldeiraLeggettOhmicRenormalization`.** `deltaOmegaSq`,
  `renormFreqSqIF`; **`deltaOmegaSq_eq_four_gamma_markov`** (`(Δω)² = 4γ·f(0)`),
  **`renormFreqSqIF_eq_ohmic`** (the influence-functional and completing-the-square renormalizations agree).
* **§C — the decoherence exponent (Eq. 2.31), linked to `CaldeiraLeggettDecoherence`.** `decoherenceExponentIF`;
  **`decoherenceExponentIF_eq_caldeiraLeggett`**.
* **§D — the thermal environment state (Eq. 2.6).** `thermalDensityMatrix` (Mehler kernel);
  **`thermalDensityMatrix_diagonal`**.

**Honest layering.** Exact `intervalIntegral` / `ring` identities for the sinc kernel, the renormalization/decoherence
cross-links and the thermal-state diagonal. The full non-local double time integral `W(x,x̃)` (Eqs. 2.17–2.21), the
integration by parts and the `δ(τ)`-Markov approximation (Eqs. 2.28, 2.30–2.31), and the `N_ℰ → ∞` spectral-density
limit are the paper's analysis, recorded not re-derived; the closed-form kernels they produce are formalized here.

## References

* J. Nishimura, H. Watanabe, arXiv:2503.20699, §2, Eqs. 2.6, 2.26–2.31. Detailed companion to 2408.16627
  (`ComplexSaddleDecoherence`, `CaldeiraLeggettOhmicRenormalization`, `CaldeiraLeggettDecoherence`).


-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional


/-- The **Markov kernel** `f(τ) = ∫_{−ω_cut}^{ω_cut} (dω/2π) cos(ωτ)` (Eq. 2.27) — the `ω_cut`-band-limited kernel
that collapses the non-local influence functional to a local (`δ(τ)`) one in the Markov limit. -/
noncomputable def markovKernel (ωcut τ : ℝ) : ℝ := (∫ ω in -ωcut..ωcut, Real.cos (ω * τ)) / (2 * π)

/-- **The Markov kernel at zero is `f(0) = ω_cut/π`** (Eq. 2.28, used to absorb the local term into the frequency
renormalization). -/
lemma markovKernel_zero (ωcut : ℝ) : markovKernel ωcut 0 = ωcut / π := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold markovKernel
  simp only [mul_zero, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp
  ring

/-- **The Markov kernel is the sinc** `f(τ) = sin(ω_cut τ)/(π τ)` (Eq. 2.27) — the band-limited kernel, which
tends to `δ(τ)` as `ω_cut → ∞`. -/
lemma markovKernel_eq_sinc (ωcut τ : ℝ) (hτ : τ ≠ 0) :
    markovKernel ωcut τ = Real.sin (ωcut * τ) / (π * τ) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold markovKernel
  rw [intervalIntegral.integral_comp_mul_right Real.cos hτ, integral_cos,
    show (-ωcut) * τ = -(ωcut * τ) by ring, Real.sin_neg, smul_eq_mul]
  field_simp
  ring


/-- The **frequency shift** `(Δω)² = 4γω_cut/π` (Eq. 2.29) — the local imaginary-kernel term absorbed into the
system frequency. -/
noncomputable def deltaOmegaSq (γ ωcut : ℝ) : ℝ := 4 * γ * ωcut / π

/-- **The frequency shift is `4γ·f(0)`** — the renormalization is set by the Markov kernel at zero. -/
lemma deltaOmegaSq_eq_four_gamma_markov (γ ωcut : ℝ) :
    deltaOmegaSq γ ωcut = 4 * γ * markovKernel ωcut 0 := by
  rw [deltaOmegaSq, markovKernel_zero]; ring

/-- The **renormalized frequency** `ω_r² = ω_b² − (Δω)²` (Eq. 2.29), from the influence functional. -/
noncomputable def renormFreqSqIF (ωb γ ωcut : ℝ) : ℝ := ωb ^ 2 - deltaOmegaSq γ ωcut

/-- **The influence-functional and completing-the-square renormalizations agree** — the frequency renormalization
from tracing out the bath (Eq. 2.29 of 2503.20699) equals the one from completing the square over the coupling
(`CaldeiraLeggettOhmicRenormalization.renormFreqSq`, Eq. 6 of 2408.16627): both give `ω_b² − 4γω_cut/π`. -/
lemma renormFreqSqIF_eq_ohmic (ωb γ ωcut NE : ℝ) (n : ℕ)
    (hωcut : ωcut ≠ 0) (hNE : 0 < NE) (hS : ohmicShapeSum NE n ≠ 0) :
    renormFreqSqIF ωb γ ωcut = renormFreqSq ωb γ ωcut NE n := by
  rw [renormFreqSqIF, deltaOmegaSq, renormFreqSq_eq_closed ωb γ ωcut NE n hωcut hNE hS]


/-- The **decoherence exponent** `W_R = (2Mγ/β) ξ² t` (Eq. 2.31) — for a sustained path separation `ξ = x − x̃`
over time `t`, the real influence kernel in the Markov limit. -/
noncomputable def decoherenceExponentIF (M γ β ξ t : ℝ) : ℝ := 2 * M * γ / β * ξ ^ 2 * t

/-- **The influence-functional decoherence exponent is the Caldeira–Leggett damping** — `W_R = (2Mγ/β) ξ² t`
(Eq. 2.31 of 2503.20699) equals `CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence` at `k_B = 1` and
temperature `T = 1/β`: the same `∝ γT` fluctuation–dissipation decoherence, derived two ways. -/
lemma decoherenceExponentIF_eq_caldeiraLeggett (M γ β ξ t : ℝ) :
    decoherenceExponentIF M γ β ξ t = caldeiraLeggettDecoherence M γ 1 (1 / β) t ξ := by
  rw [decoherenceExponentIF, caldeiraLeggettDecoherence]; ring


/-- The **thermal density matrix of a bath oscillator** (Eq. 2.6, the Mehler kernel / imaginary-time propagator) —
`ρ_ℰ^{(k)}(q, q') = √(mω/2π sinh βω) · exp[−(mω/2 sinh βω){(q²+q'²) cosh βω − 2qq'}]`, the canonical (temperature
`T = 1/β`) initial state of an environment oscillator. -/
noncomputable def thermalDensityMatrix (m ω β q q' : ℝ) : ℝ :=
  Real.sqrt (m * ω / (2 * π * Real.sinh (β * ω))) *
    Real.exp (-(m * ω / (2 * Real.sinh (β * ω))) *
      ((q ^ 2 + q' ^ 2) * Real.cosh (β * ω) - 2 * q * q'))

/-- **The thermal density matrix on the diagonal** `q = q'` is the Gaussian
`√(mω/2π sinh βω) · exp[−(mω/sinh βω)(cosh βω − 1) q²]` — the position distribution of a thermal oscillator
(with `(cosh βω − 1)/sinh βω = tanh(βω/2)`, giving width `∝ coth(βω/2)`). -/
lemma thermalDensityMatrix_diagonal (m ω β q : ℝ) :
    thermalDensityMatrix m ω β q q =
      Real.sqrt (m * ω / (2 * π * Real.sinh (β * ω))) *
        Real.exp (-(m * ω / Real.sinh (β * ω)) * (Real.cosh (β * ω) - 1) * q ^ 2) := by
  unfold thermalDensityMatrix
  rw [show -(m * ω / (2 * Real.sinh (β * ω))) *
        ((q ^ 2 + q ^ 2) * Real.cosh (β * ω) - 2 * q * q)
      = -(m * ω / Real.sinh (β * ω)) * (Real.cosh (β * ω) - 1) * q ^ 2 by ring]


/-- **The influence functional is the Feynman–Vernon weight, and its modulus is the entropic damping** — the
Caldeira–Leggett influence functional `e^{−W}` (Eq. 2.16) is the repository's canonical
`PathIntegral.ComplexActionPathIntegralWeight.feynmanVernonWeight` with imaginary action the decoherence exponent
`W_R` (Eq. 2.31); its modulus is `kuikenWeight ℏ W_R = e^{−W_R}` — the same entropic damping
(`master_modulus_is_kuiken`) that runs the whole decoherence-functional / entropic-time edifice. -/
lemma feynmanVernon_modulus_is_decoherence (S_R M γ β ξ t ℏ : ℝ) :
    ‖feynmanVernonWeight S_R (decoherenceExponentIF M γ β ξ t) ℏ‖
      = kuikenWeight ℏ (decoherenceExponentIF M γ β ξ t) := by
  rw [feynmanVernon_eq_master, master_modulus_is_kuiken]

/-- **The reciprocal thermal width is a bosonic coth** `sinh x/(cosh x − 1) = cosh(x/2)/sinh(x/2) = coth(x/2)` —
the half-angle identity for the thermal density matrix's inverse Gaussian width. -/
lemma sinh_div_coshSubOne_eq_coth_half (x : ℝ) (hx : Real.sinh x ≠ 0) :
    Real.sinh x / (Real.cosh x - 1) = Real.cosh (x / 2) / Real.sinh (x / 2) := by
  have hsinh : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    have h := Real.sinh_two_mul (x / 2)
    rwa [show 2 * (x / 2) = x by ring] at h
  have hcm1 : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
    have h := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring, Real.cosh_sq] at h
    rw [h]; ring
  have hs2 : Real.sinh (x / 2) ≠ 0 := fun h => hx (by rw [hsinh, h]; ring)
  rw [hsinh, hcm1]
  set s := Real.sinh (x / 2)
  set c := Real.cosh (x / 2)
  field_simp

/-- **The thermal position variance is the Bose–Einstein occupation** — the thermal density matrix's inverse
Gaussian width `sinh βω/(cosh βω − 1) = coth(βω/2) = 1 + 2 n_B(βω)` (`thermalDensityMatrix_diagonal` has coefficient
`(cosh βω − 1)/sinh βω = tanh(βω/2)`, so the variance `∝ coth(βω/2)`). Links the environment's thermal state
(Eq. 2.6) to the bosonic occupation `Bogoliubov.RapidityBoseFermiCothTanh.coshDivSinh_eq_one_add_two_boseEinstein`. -/
lemma thermalVariance_boseEinstein (β ω : ℝ) (hs : Real.sinh (β * ω) ≠ 0) (hη : β * ω / 2 ≠ 0) :
    Real.sinh (β * ω) / (Real.cosh (β * ω) - 1) = 1 + 2 * boseEinstein 1 (β * ω) := by
  rw [sinh_div_coshSubOne_eq_coth_half (β * ω) hs,
    coshDivSinh_eq_one_add_two_boseEinstein (β * ω / 2) hη, show 2 * (β * ω / 2) = β * ω by ring]

end Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.markovKernel_eq_sinc where
  formalizes @ "claim:tracing-out-the-ohmic-bath-collapses-the-influence-functional-noise-kernel-to-the-band-limited-sinc-sin-omega-cut-tau-over-pi-tau-which-tends-to-a-dirac-delta-the-markov-white-noise-limit-as-the-cutoff-grows",
  supported_by @ "paper:caldeira-leggett-physica-a-121-1983-587-quantum-brownian-motion-influence-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.decoherenceExponentIF_eq_caldeiraLeggett where
  formalizes @ "claim:the-feynman-vernon-influence-functional-route-yields-the-identical-decoherence-exponent-two-m-gamma-over-beta-times-xi-squared-times-t-as-the-complex-saddle-route-confirming-the-same-gamma-t-fluctuation-dissipation-damping-derived-two-independent-ways"

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.feynmanVernon_modulus_is_decoherence where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.feynmanVernon_eq_master",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  formalizes @ "claim:the-caldeira-leggett-influence-functional-exp-minus-w-is-the-repository-canonical-feynman-vernon-weight-whose-modulus-equals-the-entropic-damping-exp-minus-w-real-tying-decoherence-to-the-entropic-time-arrow"

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.renormFreqSqIF_eq_ohmic where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization.renormFreqSq_eq_closed",
  formalizes @ "claim:the-bath-local-imaginary-kernel-renormalizes-the-system-frequency-omega-r-squared-equals-omega-b-squared-minus-four-gamma-omega-cut-over-pi-and-this-influence-functional-shift-agrees-exactly-with-the-completing-the-square-renormalization"

zil_file_contract physlib.caldeiraLeggettInfluenceFunctional where
  promises "The Feynman-Vernon influence functional of the Caldeira-Leggett model (Caldeira-Leggett, Physica A 121 (1983) 587). Tracing out the Ohmic bath collapses the noise kernel to the band-limited sinc sin(omega_cut tau)/(pi tau), tending to delta(tau) in the Markov limit (markovKernel_eq_sinc); the local imaginary kernel renormalizes the frequency omega_r^2 = omega_b^2 - 4 gamma omega_cut/pi, agreeing with the completing-the-square shift (renormFreqSqIF_eq_ohmic). The influence-functional decoherence exponent equals the complex-saddle one (decoherenceExponentIF_eq_caldeiraLeggett) -- the same gamma*T fluctuation-dissipation damping two ways -- and the influence functional e^{-W} is the canonical Feynman-Vernon weight whose modulus is the entropic damping e^{-W_R} (feynmanVernon_modulus_is_decoherence)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.markovKernel",
    "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.decoherenceExponentIF",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.feynmanVernonWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence"]
  forbids_substitutes ["the exact non-Markovian memory kernel and the full frequency-integral of the spectral density, which are the cited bath-integration infrastructure",
    "any claim that the Markov limit is taken rigorously as a distributional limit; only the closed-form sinc kernel and its zero-lag value are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.markovKernel_eq_sinc,
    Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.decoherenceExponentIF_eq_caldeiraLeggett,
    Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.feynmanVernon_modulus_is_decoherence,
    Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional.renormFreqSqIF_eq_ohmic]

/- ZIL-END -/
