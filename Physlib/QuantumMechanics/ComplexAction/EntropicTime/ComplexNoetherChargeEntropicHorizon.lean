/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchwarzschildHorizon
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The complex Noether charge and its decay at the entropic horizon

Formalizes the **complex Noether charge** of complex-action/entropic-time (Paper 2+4, eqs (B7)–(B8)) and links it to the
**entropic-corrected Schwarzschild horizon** (`EntropicTime.SchwarzschildHorizon`).

When the complex Hamiltonian `H_C = H_R − iH_I` has no explicit entropic-time dependence, Noether's
theorem yields the complex charge

 `Q = ⟨H_R⟩ − iħλ` (`complexNoetherCharge`, eq B7).

Since the entropy-production rate is `λ = ⟨H_I⟩/ħ` (so `ħλ = ⟨H_I⟩`), this charge is exactly the
**expectation of the complex Hamiltonian** `Q = ⟨H_R⟩ − i⟨H_I⟩ = ⟨H_C⟩`
(`complexNoetherCharge_eq_complexExpectation`), with `Re Q = ⟨H_R⟩` the energy, `Im Q = −ħλ` the
dissipation, and `|Q|² = ⟨H_R⟩² + ⟨H_I⟩²` (`complexNoetherCharge_normSq`). In the reversible limit
`λ = 0` it is the real conserved energy `Q = ⟨H_R⟩` (`complexNoetherCharge_reversible`).

Rewriting the paper's energy-dissipation law `d⟨H_R⟩/dt = −(2/ħ)⟨H_I⟩⟨H_R⟩` in **entropic time**
(`dτ_ent/dt = λ`, `ħλ = ⟨H_I⟩`) gives `d⟨H_R⟩/dτ_ent = −2⟨H_R⟩`, with solution `⟨H_R⟩(τ) = ⟨H_R⟩₀ e^{−2τ}`
(`entropicEnergyDecay`, `entropicEnergyDecay_hasDerivAt`), decaying to `0` as `τ → ∞`
(`entropicEnergyDecay_tendsto_zero`).

**Link to the horizon.** Near the entropic Schwarzschild horizon the entropic time diverges,
`τ_ent → +∞` as `r → r_h⁺` (`nearHorizonEntropicTime_tendsto_atTop`), so the real Noether charge — the
energy `⟨H_R⟩` — is **redshifted to zero at the horizon** (`nearHorizon_noetherEnergy_tendsto_zero`): the
energy content of a complex-Hamiltonian mode vanishes as it approaches the horizon in entropic time.

> **scope note on eq (B8).** The paper states `dQ/dτ_ent = 0` (Q conserved). With `Q = ⟨H_R⟩ − iħλ` and
> the dissipative dynamics above, `Re Q = ⟨H_R⟩` decays as `e^{−2τ_ent}`, so `Q` is **not** literally
> constant out of equilibrium. The genuine conservation is the stationary/reversible statement: `Q` is
> conserved exactly when both the energy and the entropic rate are stationary
> (`complexNoetherChargePath_hasDerivAt_zero`); at `λ = 0` this is ordinary energy conservation.

* **§A — the complex Noether charge** (`complexNoetherCharge`, `complexNoetherCharge_re/_im`,
 `complexNoetherCharge_eq_complexExpectation`, `complexNoetherCharge_normSq`,
 `complexNoetherCharge_reversible`).
* **§B — energy dissipation in entropic time** (`entropicEnergyDecay`, `entropicEnergyDecay_hasDerivAt`,
 `entropicEnergyDecay_tendsto_zero`).
* **§C — conservation in the stationary limit** (`complexNoetherChargePath`,
 `complexNoetherChargePath_hasDerivAt_zero`).
* **§D — redshift to zero at the entropic horizon** (`nearHorizon_noetherEnergy_tendsto_zero`).

## References

* complex-action/entropic-time complex Noether charge (Paper 2+4, eqs B7–B8); the energy-dissipation law (eq 74). Repo
 structures: `EntropicTime.SchwarzschildHorizon` (`nearHorizonEntropicTime`,
 `nearHorizonEntropicTime_tendsto_atTop`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComplexNoetherChargeEntropicHorizon

open Filter Topology
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchwarzschildHorizon

/-! ## §A — the complex Noether charge `Q = ⟨H_R⟩ − iħλ` -/

/-- **The complex Noether charge** `Q = ⟨H_R⟩ − iħλ` (eq B7) — the Noether charge of entropic-time
translation invariance of the complex Hamiltonian `H_C = H_R − iH_I` (`HR_exp = ⟨H_R⟩`, `lam = λ`). -/
noncomputable def complexNoetherCharge (HR_exp ħ lam : ℝ) : ℂ :=
  (HR_exp : ℂ) - Complex.I * ((ħ * lam : ℝ) : ℂ)

@[simp] theorem complexNoetherCharge_re (HR_exp ħ lam : ℝ) :
    (complexNoetherCharge HR_exp ħ lam).re = HR_exp := by
  simp [complexNoetherCharge]

@[simp] theorem complexNoetherCharge_im (HR_exp ħ lam : ℝ) :
    (complexNoetherCharge HR_exp ħ lam).im = -(ħ * lam) := by
  simp [complexNoetherCharge]

/-- **[The Noether charge is the complex-Hamiltonian expectation] `Q = ⟨H_R⟩ − i⟨H_I⟩ = ⟨H_C⟩`.** Since
the entropy-production rate is `λ = ⟨H_I⟩/ħ`, i.e. `ħλ = ⟨H_I⟩`, the complex Noether charge equals the
expectation of the complex Hamiltonian `H_C = H_R − iH_I`. -/
theorem complexNoetherCharge_eq_complexExpectation (HR_exp ħ lam HI_exp : ℝ) (h : ħ * lam = HI_exp) :
    complexNoetherCharge HR_exp ħ lam = (HR_exp : ℂ) - Complex.I * (HI_exp : ℂ) := by
  rw [complexNoetherCharge, h]

/-- **[The modulus] `|Q|² = ⟨H_R⟩² + (ħλ)²`** — the squared modulus of the complex charge is the sum of
the energy and dissipation squares (`= ⟨H_R⟩² + ⟨H_I⟩²`). -/
theorem complexNoetherCharge_normSq (HR_exp ħ lam : ℝ) :
    Complex.normSq (complexNoetherCharge HR_exp ħ lam) = HR_exp ^ 2 + (ħ * lam) ^ 2 := by
  rw [Complex.normSq_apply, complexNoetherCharge_re, complexNoetherCharge_im]; ring

/-- **[Reversible limit] `Q = ⟨H_R⟩`** at `λ = 0` — the real conserved energy (standard Noether energy,
no dissipation). -/
@[simp] theorem complexNoetherCharge_reversible (HR_exp ħ : ℝ) :
    complexNoetherCharge HR_exp ħ 0 = (HR_exp : ℂ) := by
  simp [complexNoetherCharge]

/-! ## §B — energy dissipation in entropic time `d⟨H_R⟩/dτ_ent = −2⟨H_R⟩` -/

/-- **The entropic-time energy** `⟨H_R⟩(τ) = ⟨H_R⟩₀ e^{−2τ}` — the solution of `d⟨H_R⟩/dτ_ent = −2⟨H_R⟩`,
the paper's energy-dissipation law `d⟨H_R⟩/dt = −(2/ħ)⟨H_I⟩⟨H_R⟩` rewritten in entropic time. -/
noncomputable def entropicEnergyDecay (HR0 τ : ℝ) : ℝ := HR0 * Real.exp (-2 * τ)

/-- **[Energy dissipates in entropic time] `d⟨H_R⟩/dτ_ent = −2⟨H_R⟩`.** -/
theorem entropicEnergyDecay_hasDerivAt (HR0 τ : ℝ) :
    HasDerivAt (fun t => entropicEnergyDecay HR0 t) (-2 * entropicEnergyDecay HR0 τ) τ := by
  unfold entropicEnergyDecay
  have hf : HasDerivAt (fun t : ℝ => -2 * t) (-2 : ℝ) τ := by
    exact ((hasDerivAt_id τ).const_mul (-2)).congr_deriv (by ring)
  have hd := (hf.exp.const_mul HR0)
  exact hd.congr_deriv (by ring)

/-- **[The energy decays to zero] `⟨H_R⟩(τ) → 0` as `τ → +∞`.** -/
theorem entropicEnergyDecay_tendsto_zero (HR0 : ℝ) :
    Tendsto (fun τ => entropicEnergyDecay HR0 τ) atTop (𝓝 0) := by
  unfold entropicEnergyDecay
  have hτ : Tendsto (fun τ : ℝ => -2 * τ) atTop atBot := by
    have h2 : Tendsto (fun τ : ℝ => 2 * τ) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_id
    simpa [neg_mul] using tendsto_neg_atBot_iff.mpr h2
  have hexp : Tendsto (fun τ => Real.exp (-2 * τ)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hτ
  simpa using hexp.const_mul HR0

/-! ## §C — conservation in the stationary limit (eq B8, form) -/

/-- **The complex Noether charge as a trajectory** `Q(τ) = HR(τ) − i L(τ)` (with `L = ħλ`). -/
noncomputable def complexNoetherChargePath (HR L : ℝ → ℝ) (τ : ℝ) : ℂ :=
  (HR τ : ℂ) - Complex.I * (L τ : ℂ)

/-- **[Conservation in the stationary limit] `dQ/dτ_ent = 0`.** The complex Noether charge is conserved
exactly when both the energy `⟨H_R⟩` and the dissipation `ħλ` are stationary — eq (B8) in the
reversible/equilibrium regime (out of equilibrium `Re Q = ⟨H_R⟩` decays as `e^{−2τ_ent}`). -/
theorem complexNoetherChargePath_hasDerivAt_zero (HR L : ℝ → ℝ) (τ : ℝ)
    (hHR : HasDerivAt HR 0 τ) (hL : HasDerivAt L 0 τ) :
    HasDerivAt (complexNoetherChargePath HR L) 0 τ := by
  have h1 : HasDerivAt (fun t => (HR t : ℂ)) 0 τ := by simpa using hHR.ofReal_comp
  have h2 : HasDerivAt (fun t => (L t : ℂ)) 0 τ := by simpa using hL.ofReal_comp
  have h3 : HasDerivAt (fun t => Complex.I * (L t : ℂ)) 0 τ := by
    exact (h2.const_mul Complex.I).congr_deriv (by simp)
  exact (h1.sub h3).congr_deriv (by simp)

/-! ## §D — redshift to zero at the entropic horizon -/

/-- **[The energy redshifts to zero at the horizon] `⟨H_R⟩ → 0` as `r → r_h⁺`.** Composing the entropic
energy decay with the divergence of entropic time at the horizon
(`nearHorizonEntropicTime_tendsto_atTop`): the real Noether charge — the energy of a complex-Hamiltonian
mode — vanishes as the radius approaches the entropic Schwarzschild horizon, the energy infinitely
redshifted in entropic time. -/
theorem nearHorizon_noetherEnergy_tendsto_zero (lam M r_h HR0 : ℝ) (hlam : 0 < lam) (hM : 0 < M) :
    Tendsto (fun r => entropicEnergyDecay HR0 (nearHorizonEntropicTime lam M r r_h))
      (𝓝[>] r_h) (𝓝 0) :=
  (entropicEnergyDecay_tendsto_zero HR0).comp
    (nearHorizonEntropicTime_tendsto_atTop lam M r_h hlam hM)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComplexNoetherChargeEntropicHorizon

end
