/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Schwarzschild with entropic corrections: corrected horizon and near-horizon entropic time

Formalizes the **entropic-corrected Schwarzschild** geometry of complex-action/entropic-time (Paper 2+4, §"Schwarzschild with
Entropic Corrections", eqs (90)–(93), (131)).

The entropic correction modifies the metric function:

 `f(r) = 1 − 2M/r + λ M²/r²` (`entropicSchwarzschildMetric`, eq 91),

reducing to standard Schwarzschild `1 − 2M/r` at `λ = 0` (`entropicSchwarzschildMetric_zero`, eq 90).
The horizon `f(r) = 0` is the quadratic `r² − 2Mr + λM² = 0` (`entropicSchwarzschild_horizon_iff`); its
outer root is

 `r_h = M + √(M² − λM²)` (`entropicHorizon`),

which solves the horizon equation (`entropicHorizon_solves`) and recovers `r_h → 2M` at `λ = 0`
(`entropicHorizon_zero`, the Schwarzschild limit), existence requiring `λ ≤ 1`.

> **scope note on eq (92).** The paper prints the outer horizon as `r_h = M + √(M² − λM⁴)` with
> existence `λM² ≤ 1`. That value is the root of `r² − 2Mr + λM⁴ = 0` (a `λM⁴` constant term), *not* of
> the `r² − 2Mr + λM² = 0` that the eq (91) correction `λM²/r²` actually produces. We formalize the value
> consistent with the eq (91) metric, `r_h = M + √(M² − λM²)`; the `√(M² − λM⁴)` form in eq (92) is an
> algebra slip (the discriminant of `r² − 2Mr + λM²` is `4(M² − λM²)`, not `4(M² − λM⁴)`).

The **modified surface gravity** is the paper's stated value `κ = (1/4M)(1 − 2λM²)`
(`entropicSurfaceGravity`, eq 93), reducing to `κ₀ = 1/(4M)` at `λ = 0`
(`entropicSurfaceGravity_zero`) and *lowering* it for `λ > 0` (`entropicSurfaceGravity_lt_schwarzschild`)
— cooler black holes, slower Hawking evaporation.

The **near-horizon entropic time** diverges (eq 131):

 `τ_ent ≈ −(2M/λ) ln(r − r_h) → +∞` as `r → r_h⁺` (`nearHorizonEntropicTime_tendsto_atTop`),

so the horizon is infinitely far in entropic proper time — information never crosses it in finite
`τ_ent`.

* **§A — the entropic metric function** (`entropicSchwarzschildMetric`, `entropicSchwarzschildMetric_zero`,
 `entropicSchwarzschild_horizon_iff`).
* **§B — the corrected horizon** (`entropicHorizon`, `entropicHorizon_solves`, `entropicHorizon_zero`,
 `entropicSchwarzschild_horizon_zero`).
* **§C — the modified surface gravity** (`entropicSurfaceGravity`, `entropicSurfaceGravity_zero`,
 `entropicSurfaceGravity_lt_schwarzschild`).
* **§D — near-horizon entropic time** (`nearHorizonEntropicTime`,
 `nearHorizonEntropicTime_tendsto_atTop`).

## References

* complex-action/entropic-time entropic Schwarzschild (Paper 2+4, eqs 90–93, 131). Standard references: the Schwarzschild
 metric, surface gravity `κ = ½|f'(r_h)|`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchwarzschildHorizon

open Filter Topology

/-! ## §A — the entropic-corrected metric function -/

/-- **The entropic-corrected Schwarzschild metric function** `f(r) = 1 − 2M/r + λM²/r²` (eq 91) — the
`λM²/r²` term is the entropic correction to the `g_tt`/`g_rr` Schwarzschild function. -/
noncomputable def entropicSchwarzschildMetric (lam M r : ℝ) : ℝ :=
  1 - 2 * M / r + lam * M ^ 2 / r ^ 2

/-- **[Schwarzschild limit] `f(r) = 1 − 2M/r` at `λ = 0`** (eq 90). -/
theorem entropicSchwarzschildMetric_zero (M r : ℝ) :
    entropicSchwarzschildMetric 0 M r = 1 - 2 * M / r := by
  unfold entropicSchwarzschildMetric; ring

/-- **[The horizon is a quadratic] `f(r) = 0 ⟺ r² − 2Mr + λM² = 0`** (for `r ≠ 0`). Multiplying the
metric function by `r²` linearizes the horizon condition. -/
theorem entropicSchwarzschild_horizon_iff (lam M r : ℝ) (hr : r ≠ 0) :
    entropicSchwarzschildMetric lam M r = 0 ↔ r ^ 2 - 2 * M * r + lam * M ^ 2 = 0 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [show entropicSchwarzschildMetric lam M r = (r ^ 2 - 2 * M * r + lam * M ^ 2) / r ^ 2 from by
        unfold entropicSchwarzschildMetric; field_simp,
    div_eq_zero_iff]
  simp [hr2]

/-! ## §B — the corrected horizon `r_h = M + √(M² − λM²)` -/

/-- **The outer entropic horizon** `r_h = M + √(M² − λM²)` — the larger root of `r² − 2Mr + λM² = 0`
(the eq (91) horizon condition; see the scope note on eq (92) in the module docstring). -/
noncomputable def entropicHorizon (lam M : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - lam * M ^ 2)

/-- **[The horizon solves the quadratic] `r_h² − 2M r_h + λM² = 0`** for `M > 0`, `λ ≤ 1`. -/
theorem entropicHorizon_solves (lam M : ℝ) (hlam : lam ≤ 1) :
    (entropicHorizon lam M) ^ 2 - 2 * M * (entropicHorizon lam M) + lam * M ^ 2 = 0 := by
  have hnn : 0 ≤ M ^ 2 - lam * M ^ 2 := by nlinarith [sq_nonneg M]
  have hs : (Real.sqrt (M ^ 2 - lam * M ^ 2)) ^ 2 = M ^ 2 - lam * M ^ 2 := Real.sq_sqrt hnn
  unfold entropicHorizon
  linear_combination hs

/-- **[Schwarzschild limit] `r_h = 2M` at `λ = 0`** (eq 92 limit) — the standard event horizon. -/
theorem entropicHorizon_zero (M : ℝ) (hM : 0 ≤ M) : entropicHorizon 0 M = 2 * M := by
  unfold entropicHorizon
  rw [show M ^ 2 - 0 * M ^ 2 = M ^ 2 from by ring, Real.sqrt_sq hM]; ring

/-- **[The metric vanishes at the horizon] `f(r_h) = 0`** for `M > 0`, `λ ≤ 1` — `r_h` is a genuine
horizon of the entropic-corrected metric. -/
theorem entropicSchwarzschild_horizon_zero (lam M : ℝ) (hM : 0 < M) (hlam : lam ≤ 1) :
    entropicSchwarzschildMetric lam M (entropicHorizon lam M) = 0 := by
  have hpos : 0 < entropicHorizon lam M := by
    unfold entropicHorizon
    have := Real.sqrt_nonneg (M ^ 2 - lam * M ^ 2)
    linarith
  rw [entropicSchwarzschild_horizon_iff lam M _ hpos.ne']
  exact entropicHorizon_solves lam M hlam

/-! ## §C — the modified surface gravity -/

/-- **The modified surface gravity** `κ = (1/4M)(1 − 2λM²)` (eq 93, the paper's stated corrected value). -/
noncomputable def entropicSurfaceGravity (lam M : ℝ) : ℝ := (1 / (4 * M)) * (1 - 2 * lam * M ^ 2)

/-- **[Schwarzschild limit] `κ = 1/(4M)` at `λ = 0`** — the standard Schwarzschild surface gravity. -/
theorem entropicSurfaceGravity_zero (M : ℝ) : entropicSurfaceGravity 0 M = 1 / (4 * M) := by
  unfold entropicSurfaceGravity; ring

/-- **[Cooler black holes] `κ < κ₀ = 1/(4M)`** for `λ > 0`, `M > 0` — the entropic correction lowers the
surface gravity, slowing Hawking evaporation. -/
theorem entropicSurfaceGravity_lt_schwarzschild (lam M : ℝ) (hlam : 0 < lam) (hM : 0 < M) :
    entropicSurfaceGravity lam M < 1 / (4 * M) := by
  unfold entropicSurfaceGravity
  have hprod : 0 < (1 / (4 * M)) * (2 * lam * M ^ 2) := by positivity
  nlinarith [hprod]

/-! ## §D — near-horizon entropic time -/

/-- **The near-horizon entropic time** `τ_ent ≈ −(2M/λ) ln(r − r_h)` (eq 131). -/
noncomputable def nearHorizonEntropicTime (lam M r r_h : ℝ) : ℝ :=
  -(2 * M / lam) * Real.log (r - r_h)

/-- **[The horizon is infinitely far in entropic time] `τ_ent → +∞` as `r → r_h⁺`** (eq 131). The
near-horizon entropic proper time diverges as the radius approaches the horizon from outside — so
information never crosses the horizon in finite entropic time (a resolution of the information paradox in
the entropic-time parametrization). -/
theorem nearHorizonEntropicTime_tendsto_atTop (lam M r_h : ℝ) (hlam : 0 < lam) (hM : 0 < M) :
    Tendsto (fun r => nearHorizonEntropicTime lam M r r_h) (𝓝[>] r_h) atTop := by
  have hc : 0 < 2 * M / lam := by positivity
  have ha : Tendsto (fun r => r - r_h) (𝓝[>] r_h) (𝓝 0) := by
    have h := (continuous_sub_right r_h).tendsto r_h
    simpa using h.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ r in 𝓝[>] r_h, (fun r => r - r_h) r ∈ Set.Ioi (0 : ℝ) :=
    eventually_nhdsWithin_of_forall fun r hr => Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hr))
  have h1 : Tendsto (fun r => r - r_h) (𝓝[>] r_h) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, hb⟩
  have hlog : Tendsto (fun r => Real.log (r - r_h)) (𝓝[>] r_h) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp h1
  have hmul : Tendsto (fun r => (2 * M / lam) * Real.log (r - r_h)) (𝓝[>] r_h) atBot :=
    Tendsto.const_mul_atBot hc hlog
  unfold nearHorizonEntropicTime
  simpa only [neg_mul] using tendsto_neg_atTop_iff.mpr hmul

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchwarzschildHorizon

end
