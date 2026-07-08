/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Acceleration of the conformal Killing flow (Appendix F, Eqs. F.1–F.2)

The orbits of the conformal Killing field that preserves a maximally symmetric causal diamond have
*uniform* proper acceleration (constant on each orbit). This file formalizes Jacobson–Visser Appendix F
and ties it to the metric-common-root / Bogoliubov infrastructure.

In the `(s, x)` coordinates of Appendix B the conformal Killing vector is `ζ = ∂_s`, the velocity is
`u^a = ζ^a/√(−ζ·ζ) = δ^a_s C⁻¹`, and the proper acceleration is

 **F.1** `a(x) = C⁻² ∂_x C = sinh x / R` (`properAcceleration`),

depending only on the orbit label `x` (central orbit `x = 0` unaccelerated, `a(0) = 0`). The key
observation: `R · a(x) = sinh x` is the **Bogoliubov momentum** `ξ = sinh(rapidity)` — the rapidity-`x`
mode `(ξ, Δ, E) = (sinh x, 1, cosh x)` of `diamond_horizon_energy`
(`properAcceleration_is_bogoliubovMomentum`). With the lapse `C` (genuinely `1/confTimeCInv`; a model
`C = R/cosh x` at the edge), the **redshifted acceleration is the metric common root**

 `C · a(x) = tanh x = ξ/E` (`redshifted_acceleration_eq_tanh`,
 `redshifted_acceleration_eq_metricVelocity`),

strictly sub-luminal inside (`|C·a| < 1`), and the surface gravity is its bifurcation-surface limit

 **F.2** `κ = lim_{x→∞} C·a = lim tanh x = 1` (`surfaceGravity_eq_one`),

the luminal (`τ_ent → 0`) value at the edge `∂Σ`, consistent with the constant surface gravity of the
zeroth law (Appendix C).

## Two derivations

**Genuine (from the B.5 conformal factor).** `a = |C⁻²∂_x C| = ∂_x(confTimeCInv)` with the *actual*
Appendix-B factor `C⁻¹ = confTimeCInv` (`confTimeCInv_hasDerivAt_x`). It is manifestly `s`-independent
(`accel_x_deriv_s_independent`, footnote 49), equals `sinh x/R` using `R = L tanh(R_*/L)` (Eq. 2.3,
`properAcceleration_eq_deriv_confTimeCInv`), diverges at the edge (`properAcceleration_tendsto_atTop`),
and gives `κ = lim_{x→∞} C·a = 1` (`surfaceGravity_geom_eq_one`).

**Simplified (edge-lapse model).** A model lapse `C = R/cosh x` reproduces `a = C⁻²∂_x C` and exposes the
metric common root `C·a = tanh x` cleanly, with the same `κ = lim tanh x = 1` (`surfaceGravity_eq_one`).

**Acceleration vector (from the connection).** The acceleration vector `a^b = u^a∇_a u^b` is assembled
from the Christoffel connection of the conformally flat block `g = C²η` (`accelUp_s_eq_zero` `a^s = 0`,
`accelUp_x_eq` `a^x = C⁻³∂_x C`) and its magnitude `√(a^b a_b) = C⁻²|∂_x C| = |∂_x C⁻¹|`
(`accelNorm_eq`, `accelNorm_eq_abs_deriv_cInv`) — Eq. F's `δ^b_x C⁻³∂_x C` and F.1, no longer asserted.

## Scope

The connection uses the explicit conformal-metric Christoffel formula `Γ^a_bc = δ^a_b φ_c + δ^a_c φ_b −
η_bc η^{ad}φ_d` for the 2D `(s, x)` block; the partials `Cs = ∂_s C`, `Cx = ∂_x C` enter as scalar inputs
(their existence is the only abstraction). Both `κ = 1` limits are proved as genuine `atTop` limits. No
new axioms.
-/

set_option autoImplicit false

open Real Filter Topology

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalAcceleration

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry

/-! ## §F.1 — the proper acceleration `a(x) = sinh x / R` -/

/-- **Eq. F.1: the proper acceleration of the conformal Killing flow** `a(x) = sinh x / R`. Depends only
on the orbit label `x` (constant on each conformal Killing orbit). -/
def properAcceleration (R x : ℝ) : ℝ := Real.sinh x / R

/-- **The central orbit is unaccelerated** `a(0) = 0` (`sinh 0 = 0`). -/
@[simp] theorem properAcceleration_at_center (R : ℝ) : properAcceleration R 0 = 0 := by
  rw [properAcceleration, Real.sinh_zero, zero_div]

/-- **`R · a(x) = sinh x`** — the proper acceleration scaled by `R` is exactly `sinh x`. -/
theorem properAcceleration_mul_R_eq_sinh (R x : ℝ) (hR : R ≠ 0) :
    properAcceleration R x * R = Real.sinh x := by
  rw [properAcceleration, div_mul_cancel₀ _ hR]

/-- **The proper acceleration is the Bogoliubov momentum over `R`.** `R · a(x) = sinh x` is the
Bogoliubov momentum `ξ` of the rapidity-`x` mode `(ξ, Δ) = (sinh x, 1)`, whose Bogoliubov energy is
`E = √(ξ² + 1) = cosh x` (`diamond_horizon_energy`). So `a(x) = ξ/R` includes the metric common root. -/
theorem properAcceleration_is_bogoliubovMomentum (R x : ℝ) (hR : R ≠ 0) :
    bogoliubovEnergy (properAcceleration R x * R) 1 = Real.cosh x := by
  rw [properAcceleration_mul_R_eq_sinh R x hR]
  exact diamond_horizon_energy x

/-! ## §0 — limit helpers (`sinh`, `cosh → ∞`; no Mathlib lemma) -/

/-- `(eˣ − 1)/2 → ∞` — the common lower bound for `sinh` and `cosh`. -/
theorem tendsto_exp_sub_one_div_two_atTop :
    Tendsto (fun x : ℝ => (Real.exp x - 1) / 2) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.exp x - 1) atTop atTop := by
    have := Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) Real.tendsto_exp_atTop
    exact this.congr fun x => by ring
  exact h1.atTop_div_const (by norm_num)

/-- **`cosh x → ∞`.** Lower bound `(eˣ − 1)/2 ≤ cosh x`. -/
theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop ?_ tendsto_exp_sub_one_div_two_atTop
  filter_upwards with x
  rw [Real.cosh_eq]
  have : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  linarith

/-- **`sinh x → ∞`.** Lower bound `(eˣ − 1)/2 ≤ sinh x` for `x ≥ 0`. -/
theorem tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop ?_ tendsto_exp_sub_one_div_two_atTop
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.sinh_eq]
  have hexn : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **`tanh x → 1` as `x → ∞`.** Via `tanh x = 1 − 2/(e^{2x} + 1)` and `2/(e^{2x}+1) → 0`. -/
theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have hid : ∀ x : ℝ, Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
    intro x
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, two_mul, Real.exp_add, Real.exp_neg]
    have hE : (0 : ℝ) < Real.exp x := Real.exp_pos x
    have hE2 : Real.exp x * Real.exp x + 1 ≠ 0 := by positivity
    field_simp
    ring
  have h2x : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hdenom : Tendsto (fun x : ℝ => Real.exp (2 * x) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 (Real.tendsto_exp_atTop.comp h2x)
  have h0 : Tendsto (fun x : ℝ => 2 / (Real.exp (2 * x) + 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hdenom
  have hlim : Tendsto (fun x : ℝ => 1 - 2 / (Real.exp (2 * x) + 1)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at hlim
  exact hlim.congr (fun x => (hid x).symm)

/-! ## §F.1 (geometric) — `a(x) = C⁻² ∂_x C` from the actual B.5 conformal factor `C⁻¹ = confTimeCInv`

The derivation uses the **real** conformal factor `C⁻¹ = confTimeCInv` of Appendix B (Eq. B.5),
not a model lapse. Since `a = |C⁻²∂_x C| = |∂_x C⁻¹| = ∂_x(confTimeCInv)`, and `∂_x(confTimeCInv)` is
manifestly independent of `s`, the proper acceleration depends only on `x` (the paper's "surprising fact",
footnote 49). Using `R = L tanh(R_*/L)` (Eq. 2.3) it equals `sinh x / R`. -/

/-- **The `x`-derivative of the B.5 conformal factor** `∂_x C⁻¹ = sinh x · cosh(R_*/L)/(L sinh(R_*/L))` —
note it is **independent of `s`** (the `cosh s` term drops). -/
theorem confTimeCInv_hasDerivAt_x (L Rstar s x : ℝ) :
    HasDerivAt (fun x => confTimeCInv L Rstar s x)
      (Real.sinh x * Real.cosh (Rstar / L) / (L * Real.sinh (Rstar / L))) x := by
  simp only [confTimeCInv]
  have h : HasDerivAt (fun x => Real.cosh s + Real.cosh x * Real.cosh (Rstar / L))
      (Real.sinh x * Real.cosh (Rstar / L)) x :=
    ((Real.hasDerivAt_cosh x).mul_const (Real.cosh (Rstar / L))).const_add (Real.cosh s)
  exact h.div_const (L * Real.sinh (Rstar / L))

/-- **The proper acceleration depends only on `x`** (Jacobson–Visser footnote 49 — the "surprising
fact"): `∂_x C⁻¹` is the same on every conformal Killing orbit (independent of the conformal time `s`),
because `a = ∂_x(confTimeCInv)` and the `s`-dependent `cosh s` term differentiates away. -/
theorem accel_x_deriv_s_independent (L Rstar s s' x : ℝ) :
    deriv (fun x => confTimeCInv L Rstar s x) x = deriv (fun x => confTimeCInv L Rstar s' x) x := by
  rw [(confTimeCInv_hasDerivAt_x L Rstar s x).deriv, (confTimeCInv_hasDerivAt_x L Rstar s' x).deriv]

/-- **Eq. F.1 (genuine): `a(x) = ∂_x(confTimeCInv) = sinh x / R`** with `R = L tanh(R_*/L)` (Eq. 2.3). The
proper acceleration `a = |C⁻²∂_x C| = ∂_x C⁻¹` computed from the **actual** B.5 conformal factor is
`sinh x · cosh(R_*/L)/(L sinh(R_*/L)) = sinh x/(L tanh(R_*/L)) = sinh x/R` — the result `R⁻¹ sinh x`. -/
theorem properAcceleration_eq_deriv_confTimeCInv (L Rstar s x : ℝ) (hL : L ≠ 0)
    (hsh : Real.sinh (Rstar / L) ≠ 0) :
    properAcceleration (L * Real.tanh (Rstar / L)) x = deriv (fun x => confTimeCInv L Rstar s x) x := by
  rw [(confTimeCInv_hasDerivAt_x L Rstar s x).deriv, properAcceleration, Real.tanh_eq_sinh_div_cosh]
  have hcθ : Real.cosh (Rstar / L) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp

/-- **Eq. F.1: the acceleration diverges at the edge** `a(x) → ∞` as `x → ∞`. -/
theorem properAcceleration_tendsto_atTop (R : ℝ) (hR : 0 < R) :
    Tendsto (fun x => properAcceleration R x) atTop atTop := by
  simp only [properAcceleration]
  exact tendsto_sinh_atTop.atTop_div_const hR

/-! ## §F.2 (genuine) — `κ = lim_{x→∞} C·a = 1` from the actual B.5 conformal factor -/

/-- **The genuine redshifted acceleration** `C · a = ∂_x C⁻¹ / C⁻¹ = sinh x cosh(R_*/L)/(cosh s + cosh x
cosh(R_*/L))`, computed from the actual B.5 factor (`C = 1/confTimeCInv`, `a = ∂_x confTimeCInv`). -/
theorem redshiftedAccel_geom_value (L Rstar s x : ℝ) (hL : L ≠ 0)
    (hsh : Real.sinh (Rstar / L) ≠ 0) :
    deriv (fun y => confTimeCInv L Rstar s y) x / confTimeCInv L Rstar s x
      = Real.sinh x * Real.cosh (Rstar / L)
          / (Real.cosh s + Real.cosh x * Real.cosh (Rstar / L)) := by
  rw [(confTimeCInv_hasDerivAt_x L Rstar s x).deriv, confTimeCInv]
  have h1 : L * Real.sinh (Rstar / L) ≠ 0 := mul_ne_zero hL hsh
  have h2 : Real.cosh s + Real.cosh x * Real.cosh (Rstar / L) ≠ 0 := by
    have := Real.cosh_pos s; have := Real.cosh_pos x; have := Real.cosh_pos (Rstar / L); positivity
  field_simp

/-- **Eq. F.2 (genuine): the surface gravity** `κ = lim_{x→∞} C·a = 1`, from the actual B.5 conformal
factor. `C·a = sinh x cosh(R_*/L)/(cosh s + cosh x cosh(R_*/L)) = tanh x/(cosh s/(cosh x cosh(R_*/L)) + 1)
→ 1/(0 + 1) = 1`. The redshifted proper acceleration approaches the luminal value `1` at the bifurcation
surface — the constant surface gravity of the conformal Killing horizon (zeroth law, Appendix C). -/
theorem surfaceGravity_geom_eq_one (L Rstar s : ℝ) (hL : L ≠ 0)
    (hsh : Real.sinh (Rstar / L) ≠ 0) :
    Tendsto (fun x => deriv (fun y => confTimeCInv L Rstar s y) x / confTimeCInv L Rstar s x)
      atTop (𝓝 1) := by
  have hcθ : (0 : ℝ) < Real.cosh (Rstar / L) := Real.cosh_pos _
  have hval : ∀ x, deriv (fun y => confTimeCInv L Rstar s y) x / confTimeCInv L Rstar s x
      = Real.tanh x / (Real.cosh s / (Real.cosh x * Real.cosh (Rstar / L)) + 1) := by
    intro x
    rw [redshiftedAccel_geom_value L Rstar s x hL hsh, Real.tanh_eq_sinh_div_cosh]
    have hcx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    field_simp
  rw [tendsto_congr hval]
  have hden : Tendsto (fun x : ℝ => Real.cosh s / (Real.cosh x * Real.cosh (Rstar / L)) + 1)
      atTop (𝓝 1) := by
    have hd0 : Tendsto (fun x : ℝ => Real.cosh s / (Real.cosh x * Real.cosh (Rstar / L)))
        atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_cosh_atTop.atTop_mul_const hcθ)
    simpa using hd0.add_const 1
  have := Filter.Tendsto.div tendsto_tanh_atTop hden one_ne_zero
  rwa [div_one] at this

/-! ## §F (connection) — the acceleration vector `a^b = u^a ∇_a u^b` from the `(s, x)` conformal metric

The acceleration is assembled here from the **Christoffel connection** of the conformally flat 2D block
`g_ab = C² η_ab` (`η = diag(−1, +1)`, `φ = ln C`), not asserted. For `g = e^{2φ}η` the connection is
`Γ^a_bc = δ^a_b φ_c + δ^a_c φ_b − η_bc η^{ad} φ_d`, giving `Γ^s_ss = φ_s`, `Γ^x_ss = φ_x`. With the unit
velocity `u^a = δ^a_s C⁻¹` (`g(u,u) = −1`), the acceleration `a^b = u^a∇_a u^b` has
`a^s = 0` (the `s`-component cancels) and `a^x = C⁻³ ∂_x C` (Eq. F's `δ^b_x C⁻³∂_x C`), and the magnitude
`√(a^b a_b) = C⁻² |∂_x C| = |∂_x C⁻¹|` is the proper acceleration. Here `Cs = ∂_s C`, `Cx = ∂_x C` enter as
scalar partials (their existence/values are the only abstracted inputs). -/

/-- **The unit velocity** `u = C⁻¹∂_s` is timelike normalized: `g(u,u) = C²(−(C⁻¹)²) = −1`. -/
def velocityNormSq (C : ℝ) : ℝ := C ^ 2 * (-(C⁻¹) ^ 2)

theorem velocity_unit_timelike (C : ℝ) (hC : C ≠ 0) : velocityNormSq C = -1 := by
  rw [velocityNormSq]; field_simp

/-- **The acceleration `s`-component** `a^s = C⁻¹∂_s(C⁻¹) + Γ^s_ss (C⁻¹)²` (`Γ^s_ss = φ_s = Cs/C`). -/
def accelUp_s (C Cs : ℝ) : ℝ := C⁻¹ * (-Cs / C ^ 2) + (Cs / C) * (C⁻¹) ^ 2

/-- **The acceleration `x`-component** `a^x = Γ^x_ss (C⁻¹)²` (`Γ^x_ss = φ_x = Cx/C`). -/
def accelUp_x (C Cx : ℝ) : ℝ := (Cx / C) * (C⁻¹) ^ 2

/-- **`a^s = 0`** — the `s`-component of the acceleration cancels: the `∂_s(C⁻¹)` drift exactly cancels the
`Γ^s_ss` connection term (`−C⁻³Cs + C⁻³Cs = 0`). The conformal Killing orbits have no acceleration along
the flow direction. -/
theorem accelUp_s_eq_zero (C Cs : ℝ) (hC : C ≠ 0) : accelUp_s C Cs = 0 := by
  rw [accelUp_s]; field_simp; ring

/-- **`a^x = C⁻³ ∂_x C`** (Eq. F's `δ^b_x C⁻³∂_x C`) — the entire acceleration is the connection term
`Γ^x_ss (C⁻¹)²`. -/
theorem accelUp_x_eq (C Cx : ℝ) (hC : C ≠ 0) : accelUp_x C Cx = Cx / C ^ 3 := by
  rw [accelUp_x]; field_simp

/-- **The squared acceleration magnitude** `a^b a_b = g_ab a^a a^b = C²(−(a^s)² + (a^x)²) = Cx²/C⁴`
(using `a^s = 0`). -/
def accelNormSq (C Cs Cx : ℝ) : ℝ := C ^ 2 * (-(accelUp_s C Cs) ^ 2 + (accelUp_x C Cx) ^ 2)

theorem accelNormSq_eq (C Cs Cx : ℝ) (hC : C ≠ 0) :
    accelNormSq C Cs Cx = Cx ^ 2 / C ^ 4 := by
  rw [accelNormSq, accelUp_s_eq_zero C Cs hC, accelUp_x_eq C Cx hC]
  field_simp
  ring

/-- **The proper acceleration magnitude** `a = √(a^b a_b) = |∂_x C| / C² = C⁻² |∂_x C|` — Eq. F.1's
`a = C⁻²∂_x C`, now assembled from the connection (not asserted). -/
theorem accelNorm_eq (C Cs Cx : ℝ) (hC : C ≠ 0) :
    Real.sqrt (accelNormSq C Cs Cx) = |Cx| / C ^ 2 := by
  rw [accelNormSq_eq C Cs Cx hC, show Cx ^ 2 / C ^ 4 = (Cx / C ^ 2) ^ 2 by field_simp,
    Real.sqrt_sq_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < C ^ 2 by positivity)]

/-- **The magnitude is `|∂_x C⁻¹|`** — equating `√(a^b a_b) = |Cx|/C²` with the `x`-derivative of the
inverse lapse `∂_x(C⁻¹) = −Cx/C²` (chain rule). For the diamond `C⁻¹ = confTimeCInv`, so the
connection-assembled magnitude is `∂_x(confTimeCInv) = sinh x/R` — exactly
`properAcceleration_eq_deriv_confTimeCInv`. -/
theorem accelNorm_eq_abs_deriv_cInv (C : ℝ → ℝ) (x Cs Cx : ℝ) (hC : C x ≠ 0)
    (hderiv : HasDerivAt C Cx x) :
    Real.sqrt (accelNormSq (C x) Cs Cx) = |deriv (fun y => (C y)⁻¹) x| := by
  have hd : deriv (fun y => (C y)⁻¹) x = -Cx / (C x) ^ 2 := (hderiv.inv hC).deriv
  rw [accelNorm_eq (C x) Cs Cx hC, hd, abs_div, abs_neg,
    abs_of_pos (show (0 : ℝ) < (C x) ^ 2 by positivity)]

/-! ## §F.1 — a simplified edge-lapse model `C = R/cosh x` exposing the metric common root -/

/-- **A model lapse** `C = R / cosh x` — a simplified stand-in for the genuine lapse `1/confTimeCInv`,
agreeing with it asymptotically at the edge `x → ∞` (where `κ` is evaluated); it reproduces
`a = C⁻²∂_x C` and exposes the metric common root `C·a = tanh x` cleanly. The genuine derivation uses
`confTimeCInv` (see `properAcceleration_eq_deriv_confTimeCInv`, `surfaceGravity_geom_eq_one`). -/
def redshiftFactor (R x : ℝ) : ℝ := R / Real.cosh x

theorem redshiftFactor_pos (R x : ℝ) (hR : 0 < R) : 0 < redshiftFactor R x := by
  rw [redshiftFactor]; exact div_pos hR (Real.cosh_pos x)

/-- **The `x`-derivative of the redshift factor** `∂_x C = −R sinh x / cosh²x` (so `|∂_x C|` enters
`a = C⁻²∂_x C`). -/
theorem redshiftFactor_hasDerivAt (R x : ℝ) :
    HasDerivAt (fun y => redshiftFactor R y) (-(R * Real.sinh x) / Real.cosh x ^ 2) x := by
  have hc : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (hasDerivAt_const x R).div hc hne
  simp only [redshiftFactor, zero_mul, zero_sub] at h ⊢
  exact h.congr_deriv (by ring)

/-- **Eq. F.1: the geometric form** `a(x) = C⁻² ∂_x C`. With `C = R/cosh x`, the magnitude
`C⁻² · |∂_x C| = (cosh x/R)² · (R sinh x/cosh²x) = sinh x/R` is the proper acceleration. -/
theorem properAcceleration_eq_cInvSq_deriv (R x : ℝ) (hR : R ≠ 0) :
    (redshiftFactor R x)⁻¹ ^ 2 * (R * Real.sinh x / Real.cosh x ^ 2) = properAcceleration R x := by
  rw [redshiftFactor, properAcceleration]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp

/-! ## §F.1/F.2 — the redshifted acceleration is the metric common root `C·a = tanh x` -/

/-- **The redshifted acceleration is the metric common root** `C · a(x) = tanh x`. The lapse times the
proper acceleration is `(R/cosh x)(sinh x/R) = tanh x` — the boost velocity `ξ/E` of the rapidity-`x`
mode. -/
theorem redshifted_acceleration_eq_tanh (R x : ℝ) (hR : R ≠ 0) :
    redshiftFactor R x * properAcceleration R x = Real.tanh x := by
  rw [redshiftFactor, properAcceleration, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp

/-- **The redshifted acceleration is the Bogoliubov velocity** `C · a(x) = sinh x / E = ξ/E` with
`E = bogoliubovEnergy(sinh x, 1) = cosh x` — the metric common root `diamond_metric_velocity`. -/
theorem redshifted_acceleration_eq_metricVelocity (R x : ℝ) (hR : R ≠ 0) :
    redshiftFactor R x * properAcceleration R x
      = Real.sinh x / bogoliubovEnergy (Real.sinh x) 1 := by
  rw [redshifted_acceleration_eq_tanh R x hR, ← diamond_metric_velocity x]

/-- **The redshifted acceleration is strictly sub-luminal inside the diamond** `|C · a(x)| < 1` — the
conformal Killing orbits are timelike (`|tanh x| < 1`); the luminal value `1` is reached only in the
edge limit. -/
theorem redshifted_acceleration_lt_one (R x : ℝ) (hR : R ≠ 0) :
    |redshiftFactor R x * properAcceleration R x| < 1 := by
  rw [redshifted_acceleration_eq_tanh R x hR]
  exact Real.abs_tanh_lt_one x

/-! ## §F.2 — the surface gravity `κ = lim_{x→∞} C·a = 1` -/

/-- **Eq. F.2: the surface gravity is the bifurcation-surface limit of the redshifted acceleration**
`κ = lim_{x→∞} C · a = lim tanh x = 1`. The redshifted proper acceleration approaches the luminal value
`1` at the edge `∂Σ` — the constant surface gravity of the conformal Killing horizon (the value entering
the zeroth law, Appendix C). -/
theorem surfaceGravity_eq_one (R : ℝ) (hR : R ≠ 0) :
    Tendsto (fun x => redshiftFactor R x * properAcceleration R x) atTop (𝓝 1) := by
  refine tendsto_tanh_atTop.congr (fun x => ?_)
  exact (redshifted_acceleration_eq_tanh R x hR).symm

/-! ## §F — main result -/

/-- **Appendix F, bundled.** For `R ≠ 0` and any orbit label `x`:

* **(F.1)** `R · a(x) = sinh x` is the Bogoliubov momentum of the rapidity-`x` mode
  (`bogoliubovEnergy(R·a, 1) = cosh x`);
* **(metric common root)** the redshifted acceleration `C · a(x) = sinh x/E = tanh x` is the boost
  velocity `ξ/E`;
* **(sub-luminal)** `|C · a(x)| < 1` inside the diamond.

The proper acceleration of the conformal Killing flow is the Bogoliubov momentum over `R`, and its
redshift is the metric common root — gravity (`a`, `κ = 1`) and information (`ξ/E`, `τ_ent`) meet again.
-/
theorem conformal_acceleration_summary (R x : ℝ) (hR : R ≠ 0) :
    (bogoliubovEnergy (properAcceleration R x * R) 1 = Real.cosh x)
      ∧ (redshiftFactor R x * properAcceleration R x
          = Real.sinh x / bogoliubovEnergy (Real.sinh x) 1)
      ∧ |redshiftFactor R x * properAcceleration R x| < 1 :=
  ⟨properAcceleration_is_bogoliubovMomentum R x hR,
   redshifted_acceleration_eq_metricVelocity R x hR,
   redshifted_acceleration_lt_one R x hR⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalAcceleration

end
