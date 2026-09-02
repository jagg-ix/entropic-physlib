/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!

# Conformal time in FLRW cosmology

The conformal-time reformulation of FLRW dynamics.  Formalized here: the
conformal-derivative operator `f' = a·∂ₜf` (from `dt = a dη`), the conformal
Hubble factor `ℋ = a·H` (`conformalHubble_eq`), and the Friedmann and
acceleration equations in conformal time — `ℋ² = (8πG/3)ρa² + (Λc²/3)a² − Kc²`
(`conformal_friedmann`) and `a″/a = (4πG/3)(ρ − 3P/c²)a² + (2Λc²/3)a² − Kc²`
(`conformal_acceleration`) — each derived algebraically from the cosmic-time
`FirstOrderFriedmann`/`SecondOrderFriedmann`.  §D defines the conformal time as
the integral `η = ∫dt/a` and proves its defining relation `a·η′ = 1` (`dt = a dη`)
by the fundamental theorem of calculus (`conformalTime_hasDerivAt`).  §E makes the
**conformal flatness** of the metric manifest: the FLRW `4`-metric in conformal
time is pointwise `a²` times an `η`-independent (static) metric
(`flrw_conformally_flat`).

-/

@[expose] public section

namespace Cosmology.FLRW.ConformalTime

open Time
open Cosmology.FLRW.FriedmannEquation

/-- **The conformal derivative** `f' = a·∂ₜf` — the cosmic-to-conformal change of
variables from `dt = a dη` (so `d/dη = a·d/dt`).  The prime of the conformal-time
formulation applied to a cosmic-time function. -/
noncomputable def conformalDeriv (a f : Time → ℝ) : Time → ℝ :=
  fun t => a t * ∂ₜ f t

/-- **The conformal Hubble factor** `ℋ = a'/a` — the logarithmic conformal
derivative of the scale factor. -/
noncomputable def conformalHubble (a : Time → ℝ) : Time → ℝ :=
  fun t => conformalDeriv a a t / a t

/-- **[`ℋ = a·H`]** the conformal Hubble factor is the scale factor times the
cosmic-time Hubble parameter. -/
theorem conformalHubble_eq (a : Time → ℝ) (t : Time) :
    conformalHubble a t = a t * hubbleConstant a t := by
  unfold conformalHubble conformalDeriv hubbleConstant
  rw [mul_div_assoc]

/-- **[The Friedmann equation in conformal time] `ℋ² = (8πG/3)ρa² + (Λc²/3)a² − Kc²`.**
Multiplying the cosmic-time first Friedmann equation by `a²` and using `ℋ = a·H`. -/
theorem conformal_friedmann (a ρ : Time → ℝ) (k Λ G c : ℝ) (t : Time)
    (hfirst : FirstOrderFriedmann a ρ k Λ G c t) (haz : a t ≠ 0) :
    (conformalHubble a t) ^ 2
      = 8 * Real.pi * G / 3 * ρ t * (a t) ^ 2 + Λ * c ^ 2 / 3 * (a t) ^ 2
        - k * c ^ 2 := by
  rw [conformalHubble_eq a t, mul_pow]
  have haSq : (a t) ^ 2 ≠ 0 := pow_ne_zero 2 haz
  have hHa2 : (hubbleConstant a t) ^ 2 * (a t) ^ 2 = (∂ₜ a t) ^ 2 := by
    simp only [hubbleConstant, div_pow]; rw [div_mul_cancel₀ _ haSq]
  have hfirst3 : (∂ₜ a t) ^ 2 * 3
      = 8 * Real.pi * G * ρ t * (a t) ^ 2 - 3 * k * c ^ 2 + Λ * c ^ 2 * (a t) ^ 2 := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    rw [div_pow] at h
    field_simp at h
    linear_combination h
  linear_combination hHa2 + (1 / 3 : ℝ) * hfirst3

/-- **[The acceleration equation in conformal time]
`a″/a = (4πG/3)(ρ − 3P/c²)a² + (2Λc²/3)a² − Kc²`.**  The conformal second
derivative `a″ = (a(aȧ))' = a(ȧ² + aä)`, with `ȧ²` from the first Friedmann
equation and `ä/a` from the second: the `4πG` matter term shifts sign and the
`Λ` term doubles, exactly as in the standard conformal-time acceleration
equation. -/
theorem conformal_acceleration (a ρ p : Time → ℝ) (k Λ G c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ k Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    conformalDeriv a (conformalDeriv a a) t / a t
      = 4 * Real.pi * G / 3 * (ρ t - 3 * p t / c ^ 2) * (a t) ^ 2
        + 2 * Λ * c ^ 2 / 3 * (a t) ^ 2 - k * c ^ 2 := by
  have haSq : (a t) ^ 2 ≠ 0 := pow_ne_zero 2 haz
  -- the conformal second derivative expands by the product rule
  have hstep : conformalDeriv a (conformalDeriv a a) t
      = a t * ((∂ₜ a t) ^ 2 + a t * ∂ₜ (∂ₜ a) t) := by
    unfold conformalDeriv
    rw [Time.deriv_mul t ha hd_a]
    ring
  -- (ȧ)² from the first Friedmann equation (division-free, ×3)
  have hfirst3 : (∂ₜ a t) ^ 2 * 3
      = 8 * Real.pi * G * ρ t * (a t) ^ 2 - 3 * k * c ^ 2 + Λ * c ^ 2 * (a t) ^ 2 := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    rw [div_pow] at h
    field_simp at h
    linear_combination h
  -- ä from the second Friedmann equation
  have hAddot : ∂ₜ (∂ₜ a) t
      = (-(4 * Real.pi * G / 3) * (ρ t + 3 * p t / c ^ 2) + Λ * c ^ 2 / 3) * a t := by
    unfold SecondOrderFriedmann at hsecond
    rw [div_eq_iff haz] at hsecond
    linear_combination hsecond
  rw [hstep, hAddot, mul_comm (a t), mul_div_assoc, div_self haz, mul_one]
  linear_combination (1 / 3 : ℝ) * hfirst3


/-! ## §D — conformal time as an integral -/

open MeasureTheory in
/-- **The conformal time** `η(t) = ∫_{t₀}^{t} dt'/a(t')` (Gumjudpai Eq. (11) context;
`a dη = dt`).  Parametrised by the real cosmic time `A : ℝ → ℝ` (the scale factor
along the trajectory), the natural domain of the interval integral. -/
noncomputable def conformalTime (A : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ s in t₀..t, 1 / A s

open MeasureTheory in
/-- **[The conformal time satisfies its defining ODE] `η′ = 1/a`.**  Fundamental
theorem of calculus: for a continuous, nowhere-vanishing scale factor the
conformal time has cosmic-time derivative `1/a` — the differential form of
`a dη = dt`. -/
theorem conformalTime_hasDerivAt (A : ℝ → ℝ) (t₀ t : ℝ)
    (hA : Continuous A) (hAz : ∀ s, A s ≠ 0) :
    HasDerivAt (conformalTime A t₀) (1 / A t) t := by
  have hcont : Continuous (fun s => 1 / A s) := continuous_const.div hA hAz
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _)
    hcont.continuousAt

open MeasureTheory in
/-- **[The conformal-time derivative] `∂η/∂t = 1/a`.** -/
theorem conformalTime_deriv (A : ℝ → ℝ) (t₀ t : ℝ)
    (hA : Continuous A) (hAz : ∀ s, A s ≠ 0) :
    deriv (conformalTime A t₀) t = 1 / A t :=
  (conformalTime_hasDerivAt A t₀ t hA hAz).deriv

open MeasureTheory in
/-- **[The defining relation] `a·η′ = 1`, i.e. `dt = a dη`.**  The conformal time
reparametrises cosmic time exactly so that the scale factor is absorbed: the
inverse of the conformal-derivative operator `conformalDeriv` of §A. -/
theorem conformalTime_defining_relation (A : ℝ → ℝ) (t₀ t : ℝ)
    (hA : Continuous A) (hAz : ∀ s, A s ≠ 0) :
    A t * deriv (conformalTime A t₀) t = 1 := by
  rw [conformalTime_deriv A t₀ t hA hAz, mul_one_div, div_self (hAz t)]

/-! ## §E — manifest conformal flatness of the FLRW metric -/

/-- **The FLRW `4`-metric in conformal time** (spatially flat, comoving diagonal
gauge): `g = diag(−c²a², a², a², a²)` — the physical line element
`ds² = a²(−c²dη² + dx² + dy² + dz²)`. -/
noncomputable def flrwConformalMetricDiag (a c : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then -(c ^ 2 * a ^ 2) else a ^ 2

/-- **The static (Minkowski) reference metric** `η = diag(−c², 1, 1, 1)` — the
conformal-time metric stripped of the scale factor, manifestly `η`-independent. -/
noncomputable def minkowskiDiag (c : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then -(c ^ 2) else 1

/-- **[Manifest conformal flatness] `g = a²·η`.**  The FLRW `4`-metric in conformal
time is pointwise the conformal factor `a²` times the static Minkowski metric — a
scalar-independent reference.  The dynamics live entirely in the conformal factor
`a(η)²`; the FLRW spacetime is conformally flat (Weyl-flat), the manifest form of
`ds² = a(η)²·(−c²dη² + dσ²)`. -/
theorem flrw_conformally_flat (a c : ℝ) :
    flrwConformalMetricDiag a c = a ^ 2 • minkowskiDiag c := by
  funext i
  simp only [flrwConformalMetricDiag, minkowskiDiag, Pi.smul_apply, smul_eq_mul]
  split <;> ring

end Cosmology.FLRW.ConformalTime

