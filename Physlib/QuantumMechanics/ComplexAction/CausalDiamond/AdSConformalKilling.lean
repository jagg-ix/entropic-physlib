/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS

/-!
# Conformal Killing vectors of Anti-de Sitter space (Appendix D.2, Eqs. D.9–D.14)

`CausalDiamond.AppendixD` formalized the two-time embedding generally (Eqs. D.1–D.6) and
`CausalDiamond.EmbeddingZerothLaw` linked the de Sitter section (Eq. D.3) to the metric-common-root
/ entropic-time infrastructure. This file does the **Anti-de Sitter** half of Appendix D (Jacobson–Visser
§D.2), and connects it to the same common root.

The AdS global embedding (Eq. D.9) is `X^{−1} = √(L²+r²) cos(t/L)`, `X^d = L`,
`X⁰ = √(L²+r²) sin(t/L)`, `Xⁱ = rΩⁱ`. Where the de Sitter section used the **boost** (hyperbolic)
structure `cosh² − sinh² = 1`, AdS uses the **rotation** (trigonometric) structure `cos² + sin² = 1`:

* **D.9** `X · X = 0` from `cos² + sin² = 1` (`adS_embedding_lightCone`); the two timelike coordinates
 `(X^{−1}, X⁰)` rotate on a circle of radius `W = √(L²+r²)` (the AdS curvature combination), and
 `bogoliubovEnergy(X⁰, X^{−1}) = W` (`adS_rotational_energy`).
* **D.10** the induced metric `ds² = −[1+(r/L)²]dt² + [1+(r/L)²]⁻¹dr² + r²dΩ²` (`adSMetricTT`,
 `adSMetricRR`, `adSMetric_tt_rr_product`), the `L → iL` continuation of the dS line element
 `1−(r/L)² ↦ 1+(r/L)²`.
* **D.12** the diamond conformal Killing vector `ζ^{AdS} = (iL/R)[√(1+(R/L)²) J_{0d} − J_{−10}]`, the
 `L → iL` continuation of the dS one `ζ^{dS} = (iL/R)[J_{0d} − √(1−(R/L)²) J_{−10}]` (Eq. D.8): the
 coefficient `√(1−(R/L)²)` (`CausalDiamond.AdS.sqrtFactor`) becomes `√(1+(R/L)²)`
 (`adsConfKillingFactor`), captured by `adS_dS_factor_continuation` (sum of squares `= 2`, i.e.
 `R² ↦ −R²`).

**The common root.** The AdS curvature radius `W = √(L²+r²)` **is** `bogoliubovEnergy(r, L)`
(`adS_radius_eq_bogoliubov`) — radial momentum `ξ = r`, gap `Δ = L` the curvature scale. Hence the radial
velocity `v = r/W = r/bogoliubovEnergy(r, L)` is a metric common root `tanh η`
(`adS_radialVelocity_eq_tanh`) and fixes the entropic proper time
`τ_ent = binEntropy((1 − v)/2)` (`adS_entropicTime_eq_velocity`). Unlike de Sitter — whose static patch
reaches the luminal point `R/L = 1` (`τ_ent = 0`, the cosmological horizon) — AdS is **strictly
sub-luminal** `|v| < 1` for every finite `r` (`adS_velocity_lt_one`): there is no cosmological horizon,
so the AdS diamond never reaches the reversible point. The main result is
`adS_appendixD_entropic_consistency`.

## Scope

The embedding/metric identities (D.9, D.10) and the factor continuation (D.8 ↔ D.12) are exact scalar
identities. The full generator expressions (Eq. D.11) and the Poincaré coordinates (D.13–D.14) are not
built; the radial-velocity ↔ Bogoliubov ↔ entropic-time identification reuses the established lemmas.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS

/-! ## §D.9 — the AdS global embedding lies on the light cone (`cos² + sin² = 1`) -/

/-- **Eq. D.9: the AdS embedding satisfies `X · X = 0`.** With `X^{−1} = W cos(t/L)`,
`X⁰ = W sin(t/L)` (`W² = L² + r²`), `X^d = L`, and `∑(Xⁱ)² = r²`, the AdS embedding lies on the light
cone of `ℝ^{2,d}` — by the **rotation** identity `cos² + sin² = 1` (the AdS analog of the dS boost
identity `cosh² − sinh² = 1`). Equivalently the AdS hyperboloid `−(X^{−1})² − (X⁰)² + r² + L² = 0`. -/
theorem adS_embedding_lightCone (L r t W : ℝ) (hW : W ^ 2 = L ^ 2 + r ^ 2) :
    -(W * Real.cos (t / L)) ^ 2 - (W * Real.sin (t / L)) ^ 2 + (r ^ 2 + L ^ 2) = 0 := by
  have hsc : Real.sin (t / L) ^ 2 + Real.cos (t / L) ^ 2 = 1 := Real.sin_sq_add_cos_sq (t / L)
  linear_combination (-W ^ 2) * hsc - hW

/-- **The two timelike embedding coordinates rotate on the radius `W`** `bogoliubovEnergy(X⁰, X^{−1}) = W`.
With `X⁰ = W sin(t/L)`, `X^{−1} = W cos(t/L)`, `√((W sin)² + (W cos)²) = W√(sin² + cos²) = W`: the
Bogoliubov "energy" of the two rotating timelike coordinates is the conserved circle radius `W` (the AdS
closed-timelike-curve structure before unwrapping). -/
theorem adS_rotational_energy (W θ : ℝ) (hW : 0 ≤ W) :
    bogoliubovEnergy (W * Real.sin θ) (W * Real.cos θ) = W := by
  rw [bogoliubovEnergy,
    show (W * Real.sin θ) ^ 2 + (W * Real.cos θ) ^ 2 = W ^ 2 from by
      linear_combination W ^ 2 * Real.sin_sq_add_cos_sq θ]
  exact Real.sqrt_sq hW

/-! ## §D.10 — the AdS induced metric `ds² = −[1+(r/L)²]dt² + [1+(r/L)²]⁻¹dr² + r²dΩ²` -/

/-- **The AdS metric factor** `f(r) = 1 + (r/L)²` — the `L → iL` continuation of the dS factor
`1 − (r/L)²` (`R² ↦ −R²`). -/
def adSMetricFactor (L r : ℝ) : ℝ := 1 + (r / L) ^ 2

theorem adSMetricFactor_pos (L r : ℝ) : 0 < adSMetricFactor L r := by
  rw [adSMetricFactor]; positivity

/-- **Eq. D.10: `g_tt = −[1+(r/L)²]`** (the AdS lapse). -/
def adSMetricTT (L r : ℝ) : ℝ := -(adSMetricFactor L r)

/-- **Eq. D.10: `g_rr = [1+(r/L)²]⁻¹`** (the AdS radial component). -/
def adSMetricRR (L r : ℝ) : ℝ := (adSMetricFactor L r)⁻¹

/-- **Eq. D.10: the conformally-flat 2D `(t, r)` block** `g_tt · g_rr = −1` — the AdS line element is
conformally flat in the `(t, r)` plane (the AdS analog of the dS `metricSS_eq_neg_metricXX`). -/
theorem adSMetric_tt_rr_product (L r : ℝ) :
    adSMetricTT L r * adSMetricRR L r = -1 := by
  rw [adSMetricTT, adSMetricRR, neg_mul, mul_inv_cancel₀ (adSMetricFactor_pos L r).ne']

/-- **The AdS lapse never degenerates** `1 ≤ f(r) = 1 + (r/L)²` — the metric factor is bounded below by
`1` everywhere, so (unlike de Sitter, where `1 − (r/L)²` vanishes at the horizon `r = L`) the AdS static
metric has no degeneration at any finite `r`. -/
theorem adSMetricFactor_ge_one (L r : ℝ) : 1 ≤ adSMetricFactor L r := by
  rw [adSMetricFactor]; have := sq_nonneg (r / L); linarith

/-- **The lapse is timelike everywhere** `g_tt = −f < 0` — the AdS metric keeps Lorentzian signature at
every `r` (no signature flip), the metric-level statement of *no cosmological horizon*. -/
theorem adSMetricTT_neg (L r : ℝ) : adSMetricTT L r < 0 := by
  rw [adSMetricTT]; have := adSMetricFactor_pos L r; linarith

/-- **The radial component is spacelike everywhere** `g_rr = f⁻¹ > 0`. -/
theorem adSMetricRR_pos (L r : ℝ) : 0 < adSMetricRR L r := by
  rw [adSMetricRR]; exact inv_pos.mpr (adSMetricFactor_pos L r)

/-- **The de Sitter metric factor** `f_dS(r) = 1 − (r/L)²` (the dS static lapse, Eq. 2.1) — the factor
that vanishes at the cosmological horizon `r = L`. -/
def dSMetricFactor (L r : ℝ) : ℝ := 1 - (r / L) ^ 2

/-- **The `L → iL` continuation of the metric factor** `f_AdS + f_dS = 2`, i.e. `f_AdS = 2 − f_dS` — the
`adSMetricFactor` docstring's claim made explicit: `1 + (r/L)²` is `1 − (r/L)²` under `(r/L)² ↦ −(r/L)²`
(`R² ↦ −R²`), the metric-factor counterpart of `adS_dS_factor_continuation`. -/
theorem adS_dS_metricFactor_continuation (L r : ℝ) :
    adSMetricFactor L r + dSMetricFactor L r = 2 := by
  rw [adSMetricFactor, dSMetricFactor]; ring

/-! ## §D.12 — the diamond conformal Killing vector and the `L → iL` continuation -/

/-- **Eq. D.12: the AdS diamond conformal-Killing coefficient** `√(1 + (R/L)²)` of `J_{0d}` in
`ζ^{AdS} = (iL/R)[√(1+(R/L)²) J_{0d} − J_{−10}]` — the `L → iL` continuation of the dS coefficient
`√(1 − (R/L)²)` of `J_{−10}` in `ζ^{dS}` (Eq. D.8). -/
def adsConfKillingFactor (L R : ℝ) : ℝ := Real.sqrt (1 + (R / L) ^ 2)

theorem adsConfKillingFactor_sq (L R : ℝ) :
    adsConfKillingFactor L R ^ 2 = 1 + (R / L) ^ 2 := by
  rw [adsConfKillingFactor, Real.sq_sqrt (by positivity)]

theorem sqrtFactor_sq (L R : ℝ) (h : (R / L) ^ 2 ≤ 1) :
    sqrtFactor L R ^ 2 = 1 - (R / L) ^ 2 := by
  rw [sqrtFactor, Real.sq_sqrt (by linarith)]

/-- **The `L → iL` continuation D.8 ↔ D.12**: the dS coefficient `√(1−(R/L)²)`
(`CausalDiamond.AdS.sqrtFactor`) and the AdS coefficient `√(1+(R/L)²)` (`adsConfKillingFactor`)
satisfy `(√(1+(R/L)²))² + (√(1−(R/L)²))² = 2` — the squares add to `2`, the algebraic signature of
`R² ↦ −R²` that turns the de Sitter diamond's conformal Killing vector into the AdS one. -/
theorem adS_dS_factor_continuation (L R : ℝ) (h : (R / L) ^ 2 ≤ 1) :
    adsConfKillingFactor L R ^ 2 + sqrtFactor L R ^ 2 = 2 := by
  rw [adsConfKillingFactor_sq, sqrtFactor_sq L R h]; ring

/-- **The AdS conformal-Killing factor is positive** `0 < √(1 + (R/L)²)`. -/
theorem adsConfKillingFactor_pos (L R : ℝ) : 0 < adsConfKillingFactor L R := by
  rw [adsConfKillingFactor]; exact Real.sqrt_pos.mpr (by positivity)

/-- **The AdS conformal-Killing factor is at least `1`** `1 ≤ √(1 + (R/L)²)` — the AdS coefficient is
`≥ 1`, the boost-into-rotation signature: it *grows* with `R/L` rather than shrinking. -/
theorem adsConfKillingFactor_ge_one (L R : ℝ) : 1 ≤ adsConfKillingFactor L R := by
  have h1 : adsConfKillingFactor L R ^ 2 = 1 + (R / L) ^ 2 := adsConfKillingFactor_sq L R
  have h2 : 0 ≤ adsConfKillingFactor L R := (adsConfKillingFactor_pos L R).le
  nlinarith [sq_nonneg (R / L), h1, h2]

/-- **The de Sitter conformal-Killing factor is at most `1`** `√(1 − (R/L)²) ≤ 1` — the contrast with
`adsConfKillingFactor_ge_one`: the dS coefficient *shrinks* (it is the `sech` factor, `≤ 1`), while the
AdS one *grows* (`≥ 1`). The `L → iL` continuation flips the inequality, the factor-level face of
boost ↦ rotation. -/
theorem sqrtFactor_le_one (L R : ℝ) : sqrtFactor L R ≤ 1 := by
  rw [sqrtFactor]
  calc Real.sqrt (1 - (R / L) ^ 2) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (R / L)])
    _ = 1 := Real.sqrt_one

/-! ## §common root — the AdS radial structure is the Bogoliubov/entropic common root -/

/-- **The AdS curvature radius is the Bogoliubov energy** `W = √(L²+r²) = bogoliubovEnergy(r, L)` — the
radial momentum `ξ = r` and the curvature scale `Δ = L` as the gap. The AdS curvature combination is the
Bogoliubov dispersion `E = √(ξ² + Δ²)`. -/
theorem adS_radius_eq_bogoliubov (L r : ℝ) :
    Real.sqrt (L ^ 2 + r ^ 2) = bogoliubovEnergy r L := by
  rw [bogoliubovEnergy, add_comm (L ^ 2) (r ^ 2)]

/-- **The AdS radial velocity is a metric common root** `v = r/W = r/bogoliubovEnergy(r, L) = tanh η`
(`metricVelocity_eq_tanh`, `Δ = L > 0`): the AdS radial coordinate includes the same kinematic invariant
as the de Sitter rapidity. -/
theorem adS_radialVelocity_eq_tanh (L r : ℝ) (hL : 0 < L) :
    ∃ η : ℝ, r / bogoliubovEnergy r L = Real.tanh η :=
  metricVelocity_eq_tanh r L hL

/-- **The AdS entropic proper time from the radial velocity** `τ_ent = binEntropy((1 − r/W)/2)` — the
radial velocity `v = r/bogoliubovEnergy(r, L)` of the AdS diamond fixes the entropic proper time
(`entropicTime_eq_binEntropy_velocity`). -/
theorem adS_entropicTime_eq_velocity (L r : ℝ) :
    bogoliubovEntropicTime r L
      = Real.binEntropy ((1 - r / bogoliubovEnergy r L) / 2) :=
  entropicTime_eq_binEntropy_velocity r L

/-- **AdS is strictly sub-luminal: no cosmological horizon.** For every finite `r` (and `L ≠ 0`) the AdS
radial velocity satisfies `|v| = |r/W| < 1`, because `|r| < √(r² + L²) = W`. Unlike the de Sitter static
patch — which reaches the luminal point `R/L = 1` (`τ_ent = 0`, the cosmological horizon) — the AdS
diamond never reaches the reversible/luminal boundary at finite `r`: AdS has no cosmological horizon. -/
theorem adS_velocity_lt_one (L r : ℝ) (hL : L ≠ 0) :
    |r / bogoliubovEnergy r L| < 1 := by
  have hL2 : (0 : ℝ) < L ^ 2 := lt_of_le_of_ne (sq_nonneg L) ((pow_ne_zero 2 hL).symm)
  have hEpos : 0 < bogoliubovEnergy r L := by
    rw [bogoliubovEnergy]; exact Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hEpos, div_lt_one hEpos, ← Real.sqrt_sq_eq_abs, bogoliubovEnergy]
  exact Real.sqrt_lt_sqrt (sq_nonneg r) (by linarith)

/-! ## §main result — AdS Appendix D meets the entropic common root -/

/-- **The AdS half of Appendix D is consistent with the entropic common root.** For `L > 0`, radial
coordinate `r`, time `t`, and the circle radius `W = √(L²+r²)`:

* **(D.9 — light cone)** the AdS embedding point lies on `X · X = 0` (`cos² + sin² = 1`);
* **(common root — energy)** the curvature radius `W = √(L²+r²) = bogoliubovEnergy(r, L)`;
* **(common root — velocity)** the radial velocity `v = r/W = tanh η` is a metric common root;
* **(entropic proper time)** `τ_ent = binEntropy((1 − v)/2)` is fixed by that velocity;
* **(no horizon)** `|v| < 1` strictly — AdS is sub-luminal, with no cosmological horizon.

The Anti-de Sitter conformal-Killing data of Appendix D and the entropic-time common root meet in one
statement — the `L → iL` (boost ↦ rotation) counterpart of the de Sitter consistency
`appendixCD_entropic_consistency`. -/
theorem adS_appendixD_entropic_consistency (L r t W : ℝ) (hL : 0 < L) (hW : W ^ 2 = L ^ 2 + r ^ 2) :
    (-(W * Real.cos (t / L)) ^ 2 - (W * Real.sin (t / L)) ^ 2 + (r ^ 2 + L ^ 2) = 0)
      ∧ Real.sqrt (L ^ 2 + r ^ 2) = bogoliubovEnergy r L
      ∧ (∃ η : ℝ, r / bogoliubovEnergy r L = Real.tanh η)
      ∧ bogoliubovEntropicTime r L = Real.binEntropy ((1 - r / bogoliubovEnergy r L) / 2)
      ∧ |r / bogoliubovEnergy r L| < 1 :=
  ⟨adS_embedding_lightCone L r t W hW, adS_radius_eq_bogoliubov L r,
   adS_radialVelocity_eq_tanh L r hL, adS_entropicTime_eq_velocity L r,
   adS_velocity_lt_one L r hL.ne'⟩

/-- **AdS has no cosmological horizon — at both the metric and kinematic levels.** For `L ≠ 0` and any
finite `r`:

* **(metric)** the lapse `f = 1 + (r/L)² ≥ 1` never degenerates, `g_tt = −f < 0` is timelike and
  `g_rr = f⁻¹ > 0` is spacelike — globally Lorentzian, no signature flip;
* **(kinematic)** the radial velocity is strictly sub-luminal `|v| = |r/W| < 1`.

Unlike de Sitter — whose lapse `1 − (r/L)²` vanishes at `r = L` (the cosmological horizon, luminal
`τ_ent = 0`) — the Anti-de Sitter static patch reaches no horizon at any finite radius. -/
theorem adS_no_cosmological_horizon (L r : ℝ) (hL : L ≠ 0) :
    1 ≤ adSMetricFactor L r ∧ adSMetricTT L r < 0 ∧ 0 < adSMetricRR L r
      ∧ |r / bogoliubovEnergy r L| < 1 :=
  ⟨adSMetricFactor_ge_one L r, adSMetricTT_neg L r, adSMetricRR_pos L r,
   adS_velocity_lt_one L r hL⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling

end
