/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

/-!
# The Navier–Stokes momentum equation in entropic time

The velocity equation itself — not just the energy or enstrophy budgets — reparametrized from physical time `t`
to entropic time `τ`, where `dτ/dt = (ν/ℏ)Ω` and `Ω = ‖∇u‖²`.

Writing the clock rate `g := dτ/dt = (ν/ℏ)Ω`, the chain rule (`momentum_reparametrization`) gives
`∂ₜu = g·∂_τu`.  Substituting into the physical momentum balance `∂ₜu = νΔu − (u·∇)u − ∇p` turns it into
(`momentum_entropicTime_form`)

  `∂_τ u = (1/g)·(νΔu − (u·∇)u − ∇p)`,      `∇·u = 0`.

At the Constantin–Iyer scale `ℏ = 2ν` the clock rate is `g = Ω/2` and `1/g = 2/Ω`
(`clock_factor_constantinIyer`), so the momentum equation reads

  `∂_τ u = (2/Ω)·(νΔu − (u·∇)u − ∇p)`,      `Ω = ‖∇u‖²`,      `∇·u = 0`.

In the material (Lagrangian) frame `Du/Dτ = (1/g) Du/Dt`, so with `Du/Dt = νΔu − ∇p` the equation is

  `Du/Dτ = (2/Ω)·(νΔu − ∇p)`.

The velocity's whole nonlinearity is carried by the material derivative on the left and the enstrophy `Ω` in
the clock rate on the right — the "velocity and acceleration depend on time" made explicit as the reparametrized
transport and clock.  This file formalizes the reparametrization identities the equation is built from; the
differential operators (`Δ`, `∇`, `∇·`) are the standard spatial ones, unchanged by the time reparametrization.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.EntropicTimeMomentumEquation

/-- **The momentum equation reparametrizes by the clock rate.**  If entropic time advances at rate
`g = dτ/dt` and the velocity component has entropic-time derivative `v = ∂_τu`, then its physical-time
derivative is `∂ₜu = g·v` (chain rule).  This is the identity that carries the momentum balance from `t` to
`τ`. -/
theorem momentum_reparametrization (τfun ufield : ℝ → ℝ) (t g v : ℝ)
    (hτ : HasDerivAt τfun g t) (hu : HasDerivAt ufield v (τfun t)) :
    HasDerivAt (fun s => ufield (τfun s)) (g * v) t := by
  have h := hu.comp t hτ
  rw [mul_comm] at h
  exact h

/-- **The Navier–Stokes momentum equation in entropic time.**  With the clock rate `g = dτ/dt ≠ 0`, the
physical momentum balance `∂ₜu = force` (i.e. `g·∂_τu = force`, `force = νΔu − (u·∇)u − ∇p`) is exactly the
entropic-time equation `∂_τu = force/g`. -/
theorem momentum_entropicTime_form (g dtau_u force : ℝ) (hg : g ≠ 0)
    (hphys : g * dtau_u = force) : dtau_u = force / g := by
  rw [eq_div_iff hg, mul_comm]
  exact hphys

/-- **The clock factor at `ℏ = 2ν`.**  The clock rate `g = (ν/ℏ)Ω` at the Constantin–Iyer scale `ℏ = 2ν` is
`g = Ω/2`, so `1/g = 2/Ω`: the momentum equation's right-hand side is scaled by `2/Ω`. -/
theorem clock_factor_constantinIyer (ν Ω : ℝ) (hν : ν ≠ 0) (hΩ : Ω ≠ 0) :
    (ν / (2 * ν) * Ω)⁻¹ = 2 / Ω := by
  rw [show ν / (2 * ν) = 1 / 2 from by field_simp]
  field_simp

/-! ### The clock dilation in the dilaton group, and its Witten modular width

The proper-time dilation of §above extends into two existing structures.  Two turbulent epochs with
enstrophies `Ω₁, Ω₂` run entropic clocks dilated by the prefactors `2/Ω₁, 2/Ω₂`; their **relative** dilation is
the pure ratio `Ω₁/Ω₂` — the quantum `2 = ℏ/ν` cancels (`clockDilation_ratio`), so the relative aging of
turbulent epochs is *classical scale-group physics*: an element of the dilaton group
(`EntropicTime.ScaleDilationLogMetric.dilationFlow`), reached at flow parameter equal to the **clock rapidity**
`w = log(Ω₁/Ω₂)` (`clockDilation_on_dilaton_orbit`), additive along the flow (`clockRapidity_additive` — the
group law in log coordinates).

That additive log-of-a-scale-ratio is precisely the shape of the **GKP–Witten modular width**: the vacuum
annulus width is `W = log(L/ε)` (`ConformalModularEntanglement.vacuum_annulus_width`) and `W` is an additive
boost interval (the Cardy–Tonni entropy is linear in it).  So the clock rapidity *is* a Witten width, and the
boundary CFT assigns the clock dilation the Cardy–Tonni entropy `S = (c/6)·w`, **additive along the dilaton
flow** (`cardyTonni_clockRapidity_additive`): the proper-time dilation between turbulent epochs is a boost in
the scale group, and `W` is the proper time of that boost. -/

open Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

/-- **The relative clock dilation is the pure enstrophy ratio — the quantum cancels.**
`(2/Ω₂)/(2/Ω₁) = Ω₁/Ω₂`: the dilation relating the entropic clocks of two turbulent epochs is a pure
scale-group element; the `2 = ℏ/ν` cancels, so relative clock dilation is classical dilaton-group physics —
only the *absolute* rate carries `ℏ`. -/
theorem clockDilation_ratio (Ω₁ Ω₂ : ℝ) (h₁ : Ω₁ ≠ 0) (h₂ : Ω₂ ≠ 0) :
    (2 / Ω₂) / (2 / Ω₁) = Ω₁ / Ω₂ := by
  field_simp

/-- **The clock rapidity** `w(Ω₁→Ω₂) := log(Ω₁/Ω₂)` — the additive (log) coordinate of the clock dilation in
the dilaton group. -/
noncomputable def clockRapidity (Ω₁ Ω₂ : ℝ) : ℝ := Real.log (Ω₁ / Ω₂)

/-- **The clock dilation lies on the dilaton-group orbit at parameter `w`.**
`dilationFlow 1 (w(Ω₁→Ω₂)) = Ω₁/Ω₂`: the relative clock dilation is the one-parameter dilation-group element
whose flow parameter is the clock rapidity. -/
theorem clockDilation_on_dilaton_orbit (Ω₁ Ω₂ : ℝ) (h₁ : 0 < Ω₁) (h₂ : 0 < Ω₂) :
    dilationFlow 1 (clockRapidity Ω₁ Ω₂) = Ω₁ / Ω₂ := by
  unfold dilationFlow clockRapidity
  rw [one_mul, Real.exp_log (div_pos h₁ h₂)]

/-- **The rapidity is additive along the flow — the group law in log coordinates.**
`w(Ω₁→Ω₂) + w(Ω₂→Ω₃) = w(Ω₁→Ω₃)`: the dilaton-group cocycle. -/
theorem clockRapidity_additive (Ω₁ Ω₂ Ω₃ : ℝ) (h₁ : Ω₁ ≠ 0) (h₂ : Ω₂ ≠ 0) (h₃ : Ω₃ ≠ 0) :
    clockRapidity Ω₁ Ω₂ + clockRapidity Ω₂ Ω₃ = clockRapidity Ω₁ Ω₃ := by
  unfold clockRapidity
  rw [Real.log_div h₁ h₂, Real.log_div h₂ h₃, Real.log_div h₁ h₃]
  ring

/-- **The clock rapidity is a Witten modular width.**  The boundary CFT assigns the clock dilation the
Cardy–Tonni entropy `S = (c/6)·w(Ω₁→Ω₂)` of a GKP–Witten annulus of width `w`, additive along the dilaton
flow: `S(1→2) + S(2→3) = S(1→3)` — the proper-time dilation between turbulent epochs is a boost in the scale
group whose proper length is the Witten width. -/
theorem cardyTonni_clockRapidity_additive (cCFT Ω₁ Ω₂ Ω₃ : ℝ)
    (h₁ : Ω₁ ≠ 0) (h₂ : Ω₂ ≠ 0) (h₃ : Ω₃ ≠ 0) :
    cardyTonniEntropy cCFT (clockRapidity Ω₁ Ω₂) + cardyTonniEntropy cCFT (clockRapidity Ω₂ Ω₃)
      = cardyTonniEntropy cCFT (clockRapidity Ω₁ Ω₃) := by
  unfold cardyTonniEntropy
  rw [← clockRapidity_additive Ω₁ Ω₂ Ω₃ h₁ h₂ h₃]
  ring

/-! ### The Clay statement, re-evaluated in dilaton–Witten variables

Blow-up means the enstrophy escapes to infinity in finite external time; in the variables of this file that is
an **infinite backward boost in the dilaton group** — the clock rapidity `w(Ω₀→Ω) = log(Ω₀/Ω)` falls below any
`−R` (`unbounded_enstrophy_unbounded_rapidity`) — whose inverse dilation the boundary must price at an
unboundedly wide Witten annulus, entropy `≥ (c/6)·R` for every `R`
(`blowup_witten_entropy_unbounded`).  Three exact facts locate the problem:

* **the gate is forward rapidity** (`gate_positive_iff_rapidity_forward`): the realized depletion margin is
  positive *iff* the epoch rapidity is forward, `0 < δ* ↔ 0 < w(Ω₀→Ω_T)` — so the Clay reduction "uniform
  positive margin" reads, in these variables, **uniform forward confinement in the dilaton group**;
* **2D is forward-confined** (`twoDim_rapidity_forward_confined`): monotone enstrophy keeps the rapidity in
  the forward cone — the solved case is exactly the confined case;
* **the budget cannot decide it** (`finite_budget_unbounded_rapidity`): the finite entropic-time budget bounds
  `∫Ω` (the *area* under the spike), but a spike of height `e^R` and width `B·e^{−R}` reaches any rapidity `R`
  at fixed area `B` — bounded action is compatible with unbounded pointwise rapidity.  (The known Leray
  blow-up lower rate `Ω ≳ (T^*−t)^{−1/2}` is likewise area-integrable — budget-compatible.)

**Re-evaluated Clay statement**: does the Navier–Stokes *nonlinearity* forbid the dilaton-group escape that
the action budget permits — equivalently, does every finite-budget flow keep a uniform forward rapidity
margin?  This is a reformulation locating the openness exactly between the pointwise coordinate `log Ω` and
its integrated exponential `∫Ω`; it resolves nothing, and is stated here so that what is open is exact. -/

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

/-- **Monotone enstrophy confines the rapidity forward — the 2D side.**  When the enstrophy does not exceed
its initial value, the clock rapidity stays in the forward cone: `0 ≤ w(Ω₀→Ω)`. -/
theorem twoDim_rapidity_forward_confined (Ω₀ Ω : ℝ) (hΩ : 0 < Ω) (hle : Ω ≤ Ω₀) :
    0 ≤ clockRapidity Ω₀ Ω := by
  unfold clockRapidity
  exact Real.log_nonneg ((one_le_div hΩ).mpr hle)

/-- **The gate is forward rapidity.**  The realized depletion margin is positive *iff* the epoch's clock
rapidity is forward: `0 < δ* ↔ 0 < w(Ω₀→Ω_T)`.  The Clay reduction "uniform positive margin" is, in dilaton
variables, uniform forward confinement. -/
theorem gate_positive_iff_rapidity_forward (Ω₀ Ω_T ν IP : ℝ)
    (hν : 0 < ν) (hIP : 0 < IP) (hΩ₀ : 0 < Ω₀) (hΩT : 0 < Ω_T) :
    0 < realizedDepletionMargin Ω₀ Ω_T ν IP ↔ 0 < clockRapidity Ω₀ Ω_T := by
  rw [realizedMargin_pos_iff Ω₀ Ω_T ν IP hν hIP]
  unfold clockRapidity
  rw [Real.log_pos_iff (div_pos hΩ₀ hΩT).le, one_lt_div hΩT]

/-- **Unbounded enstrophy is an unbounded dilaton excursion.**  Once the enstrophy exceeds `Ω₀·e^R` the clock
rapidity has fallen below `−R`: blow-up is an infinite backward boost in the dilaton group, in finite external
time. -/
theorem unbounded_enstrophy_unbounded_rapidity (Ω₀ R Ω : ℝ) (hΩ₀ : 0 < Ω₀)
    (hΩ : Ω₀ * Real.exp R ≤ Ω) :
    clockRapidity Ω₀ Ω ≤ -R := by
  have hΩpos : 0 < Ω := lt_of_lt_of_le (by positivity) hΩ
  have key : 0 ≤ Real.log (Ω / (Ω₀ * Real.exp R)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr hΩ)
  rw [Real.log_div hΩpos.ne' (by positivity), Real.log_mul hΩ₀.ne' (Real.exp_ne_zero R),
    Real.log_exp] at key
  unfold clockRapidity
  rw [Real.log_div hΩ₀.ne' hΩpos.ne']
  linarith

/-- **Blow-up demands unbounded Witten width.**  The inverse dilation `Ω → Ω₀` carries Cardy entropy at least
`(c/6)·R` once `Ω ≥ Ω₀·e^R`: to price a blow-up the boundary must supply entropy without bound, at the fixed
rate `c/6` per unit rapidity. -/
theorem blowup_witten_entropy_unbounded (cCFT Ω₀ R Ω : ℝ) (hc : 0 ≤ cCFT) (hΩ₀ : 0 < Ω₀)
    (hΩ : Ω₀ * Real.exp R ≤ Ω) :
    cCFT / 6 * R ≤ cardyTonniEntropy cCFT (clockRapidity Ω Ω₀) := by
  have hΩpos : 0 < Ω := lt_of_lt_of_le (by positivity) hΩ
  have hw : R ≤ clockRapidity Ω Ω₀ := by
    have key : 0 ≤ Real.log (Ω / (Ω₀ * Real.exp R)) :=
      Real.log_nonneg ((one_le_div (by positivity)).mpr hΩ)
    rw [Real.log_div hΩpos.ne' (by positivity), Real.log_mul hΩ₀.ne' (Real.exp_ne_zero R),
      Real.log_exp] at key
    unfold clockRapidity
    rw [Real.log_div hΩpos.ne' hΩ₀.ne']
    linarith
  unfold cardyTonniEntropy
  exact mul_le_mul_of_nonneg_left hw (div_nonneg hc (by norm_num))

/-- **The action budget cannot confine the dilaton coordinate.**  For any budget `B > 0` and any target
rapidity `R`, a spike of height `e^R` and width `B·e^{−R}` reaches rapidity `R` at integrated cost exactly
`B`: the finite entropic-time budget (`τ ≤ E₀/ℏ`, bounding `∫Ω`) is compatible with arbitrarily large
pointwise rapidity.  The Clay question is therefore *not* decided by the budget — it asks whether the
nonlinearity forbids the escape the budget permits. -/
theorem finite_budget_unbounded_rapidity (B R : ℝ) (hB : 0 < B) :
    ∃ H width : ℝ, 0 < width ∧ width * H ≤ B ∧ R ≤ Real.log H := by
  refine ⟨Real.exp R, B * Real.exp (-R), mul_pos hB (Real.exp_pos _), ?_, by rw [Real.log_exp]⟩
  rw [Real.exp_neg, mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero R), mul_one]

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.EntropicTimeMomentumEquation

end
