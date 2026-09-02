/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Data.Fin.VecNotation

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions -/

/-!
# Massive string states and anomalous dimensions (Gubser–Klebanov–Polyakov)

Gubser, Klebanov & Polyakov, *Gauge Theory Correlators from Non-Critical String
Theory*, Phys. Lett. B428 (1998) 105 (hep-th/9802109), §2–§3 — the source of the
holographic dictionary.  This module adds the paper's *specific* content on top of
the existing `GKPWittenAdSCFTDictionary` (from which the operator dimension
`conformalDimension d μ = d/2 + √((d/2)² + μ)` and the mass–dimension relation
`Δ(Δ − d) = μ = m²R²` are **leveraged, not redefined**):

* **§A — the radial wave equation.**  The minimal-scalar equation of motion on
  `AdS₅` (GKP Eq. MinEOM) has radial operator `L = z³ ∂_z(z^{−3} ∂_z)`, which acts on
  the power law `z^a` as `L[z^a] = a(a − 4)z^{a−2}` (`radialOperator_powerLaw`).
  Hence the near-boundary mode `z^Δ` with `Δ = conformalDimension 4 (m²R²)` has
  eigenvalue `m²R²` (`conformalDimension_solves_radial`) — the indicial equation
  of the wave equation *is* the mass–dimension relation.

* **§B — protected operators.**  At `μ = 0` the dimension is `Δ = 4`
  (`massless_dimension`).  The `ℓ`-th `S⁵` partial wave (`μ ↔ ℓ(ℓ+4)`) has integer
  dimension `Δ = 4 + ℓ` (`partialWave_dimension`, GKP Eq. GotFlux): its
  non-perturbative dimension equals its bare dimension — no anomalous dimension.

* **§C — the strong-coupling anomalous dimension (the GKP prediction).**  For a
  level-`n` string state `m²R² = 4n g_{YM}√(2N)` (`massRadiusSq_tHooft`, from
  `m² = 4n/α'`, `R⁴ = 2N g²(α')²`).  The dimension exceeds its floor,
  `mR ≤ Δ − 2 ≤ mR + 2/(mR)` (`dimension_excess_bounds`), so the leading dimension
  grows as `h_n ≈ mR = 2(n g_{YM}√(2N))^{1/2}` (`massRadius_strongCoupling`,
  GKP Eq. anomform) — a new prediction of the string-theoretic approach to large-`N`
  gauge theory, growing without bound with the 't Hooft coupling.

* **§D — conformal flatness of `AdS₅`.**  The near-horizon metric
  `g = (R/z)²·η` (GKP Eq. NearGeom) is a Weyl rescaling of Minkowski
  (`ads_conformally_flat`) — the same structure as
  `Cosmology.FLRW.ConformalTime.flrw_conformally_flat`, with the holographic radial
  coordinate `z` in the role of the conformal factor.

Honest layering: the Bessel-function solution `z²K_ν(kz)` and the flux-factor
extraction of the two-point normalization are the analytic content; the radial
indicial equation and all the algebraic dimension identities are formalized here,
built on the `GKPWittenAdSCFTDictionary`.

## References

* S. S. Gubser, I. R. Klebanov, A. M. Polyakov, Phys. Lett. B428 (1998) 105,
  hep-th/9802109, §2–§3.
* Repo carrier: `AdSCFT.GKPWittenAdSCFTDictionary` (`conformalDimension`,
  `massDimension_relation`, `cftTwoPoint`); `Cosmology.FLRW.ConformalTime`
  (the conformal-flatness pattern).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

/-! ## §A — the AdS₅ radial wave equation and its indicial equation -/

/-- **[The AdS₅ radial operator on a power law] `z³ ∂_z(z^{−3} ∂_z)[z^a] = a(a−4)z^{a−2}`.**
The minimal-scalar radial operator of `AdS₅` (GKP Eq. MinEOM) acting on the
power-law profile `z^a` returns the same power scaled by the indicial symbol
`a(a−4)` (the `d = 4` case of `a(a−d)`). -/
theorem radialOperator_powerLaw (a z : ℝ) (hz : 0 < z) :
    z ^ (3 : ℝ) * deriv (fun w => w ^ (-3 : ℝ) * deriv (fun u => u ^ a) w) z
      = a * (a - 4) * z ^ (a - 2) := by
  have hev : (fun w => w ^ (-3 : ℝ) * deriv (fun u => u ^ a) w)
      =ᶠ[nhds z] fun w => a * w ^ (a - 4) := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    rw [(Real.hasDerivAt_rpow_const (Or.inl hw.ne')).deriv,
      show w ^ (-3 : ℝ) * (a * w ^ (a - 1)) = a * (w ^ (-3 : ℝ) * w ^ (a - 1)) from by ring,
      ← Real.rpow_add hw, show (-3 : ℝ) + (a - 1) = a - 4 from by ring]
  rw [Filter.EventuallyEq.deriv_eq hev,
    ((Real.hasDerivAt_rpow_const (p := a - 4) (Or.inl hz.ne')).const_mul a).deriv]
  have hzz : z ^ (3 : ℝ) * z ^ (a - 4 - 1) = z ^ (a - 2) := by
    rw [← Real.rpow_add hz]; congr 1; ring
  linear_combination (a * (a - 4)) * hzz

/-- **[The dimension `Δ = conformalDimension 4 μ` is the near-boundary radial mode]**
For `μ = m²R² ≥ −4` (the AdS₅ Breitenlohner–Freedman range), the power `z^Δ` with
`Δ` the `GKPWittenAdSCFTDictionary.conformalDimension` solves the radial equation
with eigenvalue `μ`: `L[z^Δ] = μ·z^{Δ−2}`.  The indicial equation of the wave
equation *is* the leveraged `massDimension_relation`. -/
theorem conformalDimension_solves_radial (μ z : ℝ) (hμ : 0 ≤ (4 / 2 : ℝ) ^ 2 + μ)
    (hz : 0 < z) :
    z ^ (3 : ℝ)
        * deriv (fun w => w ^ (-3 : ℝ) *
            deriv (fun u => u ^ conformalDimension 4 μ) w) z
      = μ * z ^ (conformalDimension 4 μ - 2) := by
  rw [radialOperator_powerLaw (conformalDimension 4 μ) z hz,
    massDimension_relation 4 μ hμ]

/-! ## §B — protected operators: massless and partial waves -/

/-- **[The massless operator has dimension `4`] `Δ(μ = 0) = 4`.**  A massless
supergravity field (dilaton, graviton) is dual to a dimension-`4` operator such
as `tr F²`, with no anomalous dimension. -/
theorem massless_dimension : conformalDimension 4 0 = 4 := by
  unfold conformalDimension
  rw [show (4 / 2 : ℝ) ^ 2 + 0 = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **[The `ℓ`-th partial wave has dimension `4 + ℓ`]** with the `S⁵` partial-wave
identification `μ = m²R² ↔ ℓ(ℓ+4)`: `Δ = 2 + √(4 + ℓ(ℓ+4)) = 2 + (ℓ+2) = 4 + ℓ` — an
integer, the bare dimension (GKP Eq. GotFlux); the dilaton tower is protected. -/
theorem partialWave_dimension (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    conformalDimension 4 (ℓ * (ℓ + 4)) = 4 + ℓ := by
  unfold conformalDimension
  have hs : Real.sqrt ((4 / 2 : ℝ) ^ 2 + ℓ * (ℓ + 4)) = ℓ + 2 := by
    rw [show (4 / 2 : ℝ) ^ 2 + ℓ * (ℓ + 4) = (ℓ + 2) ^ 2 from by ring,
      Real.sqrt_sq (by linarith)]
  rw [hs]; ring

/-! ## §C — the strong-coupling anomalous dimension (the GKP prediction) -/

/-- **[The 't Hooft form of the barrier] `m²R² = 4n g_{YM}√(2N)`.**  For a level-`n`
string state `m² = 4n/α'`, and `R² = α' g√(2N)` (the positive root of
`R⁴ = 2N g²(α')²`); the `α'` cancels, leaving the 't Hooft combination. -/
theorem massRadiusSq_tHooft (m R n g N α : ℝ) (hα : α ≠ 0)
    (hm2 : m ^ 2 = 4 * n / α) (hR2 : R ^ 2 = α * g * Real.sqrt (2 * N)) :
    (m * R) ^ 2 = 4 * n * g * Real.sqrt (2 * N) := by
  rw [mul_pow, hm2, hR2]
  field_simp

/-- **[The dimension excess is squeezed onto `mR`] `mR ≤ Δ − 2 ≤ mR + 2/(mR)`** for
`mR > 0` (with `μ = (mR)²`).  Since `Δ − 2 = √(4 + (mR)²)` in `AdS₅`, the anomalous
dimension is asymptotic to `mR` at strong coupling. -/
theorem dimension_excess_bounds (m R : ℝ) (h : 0 < m * R) :
    m * R ≤ conformalDimension 4 ((m * R) ^ 2) - 2
      ∧ conformalDimension 4 ((m * R) ^ 2) - 2 ≤ m * R + 2 / (m * R) := by
  have hne : m * R ≠ 0 := h.ne'
  obtain ⟨hm, hR⟩ := mul_ne_zero_iff.mp hne
  have hν : conformalDimension 4 ((m * R) ^ 2) - 2 = Real.sqrt (4 + (m * R) ^ 2) := by
    unfold conformalDimension; norm_num
  rw [hν]
  have hRHSpos : 0 ≤ m * R + 2 / (m * R) := by positivity
  refine ⟨?_, ?_⟩
  · calc m * R = Real.sqrt ((m * R) ^ 2) := (Real.sqrt_sq h.le).symm
      _ ≤ Real.sqrt (4 + (m * R) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  · have hexpand : (m * R + 2 / (m * R)) ^ 2
        = (m * R) ^ 2 + 4 + (2 / (m * R)) ^ 2 := by field_simp [hm, hR]; ring
    have hle : 4 + (m * R) ^ 2 ≤ (m * R + 2 / (m * R)) ^ 2 := by
      rw [hexpand]; nlinarith [sq_nonneg (2 / (m * R))]
    calc Real.sqrt (4 + (m * R) ^ 2)
          ≤ Real.sqrt ((m * R + 2 / (m * R)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = m * R + 2 / (m * R) := Real.sqrt_sq hRHSpos

/-- **[The strong-coupling mass scale] `mR = 2(n g_{YM}√(2N))^{1/2}`** — the leading
anomalous dimension `h_n ≈ mR` grows as the square root of the level times the
't Hooft coupling (GKP Eq. anomform), without bound. -/
theorem massRadius_strongCoupling (m R n g N : ℝ) (hmR : 0 ≤ m * R)
    (hbarrier : (m * R) ^ 2 = 4 * n * g * Real.sqrt (2 * N)) :
    m * R = 2 * Real.sqrt (n * g * Real.sqrt (2 * N)) := by
  have hnn : 0 ≤ n * g * Real.sqrt (2 * N) := by nlinarith [hbarrier, sq_nonneg (m * R)]
  have hsq : (2 * Real.sqrt (n * g * Real.sqrt (2 * N))) ^ 2 = (m * R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnn, hbarrier]; ring
  have h2 : 0 ≤ 2 * Real.sqrt (n * g * Real.sqrt (2 * N)) := by positivity
  nlinarith [hsq, hmR, h2]

/-! ## §D — conformal flatness of `AdS₅` -/

/-- **The `AdS₅` conformal factor** `(R/z)²` — the Weyl factor of the near-horizon
metric `ds² = (R²/z²)(−dt² + dx⃗² + dz²)` (GKP Eq. NearGeom). -/
noncomputable def adsConformalFactor (R z : ℝ) : ℝ := R ^ 2 / z ^ 2

/-- **The `AdS₅` metric diagonal** `g = diag(−R²/z², R²/z², …)`. -/
noncomputable def adsMetricDiag (R z : ℝ) : Fin 5 → ℝ :=
  fun i => if i = 0 then -(R ^ 2 / z ^ 2) else R ^ 2 / z ^ 2

/-- **The flat (Minkowski) reference** `η = diag(−1, 1, 1, 1, 1)`. -/
noncomputable def minkowskiDiag5 : Fin 5 → ℝ := fun i => if i = 0 then -1 else 1

/-- **[AdS is conformally flat] `g = (R/z)²·η`.**  The `AdS₅` metric is pointwise the
conformal factor `(R/z)²` times the flat Minkowski metric — the same
conformal-flatness structure as
`Cosmology.FLRW.ConformalTime.flrw_conformally_flat`, with the holographic radial
coordinate `z` (`z = R·e^{−φ/R}`, a scale/RG coordinate) in the role of the
conformal factor. -/
theorem ads_conformally_flat (R z : ℝ) :
    adsMetricDiag R z = adsConformalFactor R z • minkowskiDiag5 := by
  funext i
  simp only [adsMetricDiag, adsConformalFactor, minkowskiDiag5, Pi.smul_apply,
    smul_eq_mul]
  split <;> ring

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions

end

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit -/

/-!
# The strong-coupling anomalous dimension as a genuine limit

`MassiveStringAnomalousDimensions.dimension_excess_bounds` established only the two-sided *band*
`mR ≤ Δ − 2 ≤ mR + 2/(mR)` for the AdS₅ operator dimension `Δ = conformalDimension 4 ((mR)²)`.  The
Gubser–Klebanov–Polyakov headline — that the anomalous dimension is *asymptotic* to `mR` (hence grows as
`λ^{1/4}` at strong coupling) — was left as prose.  This module discharges that gap: the band is squeezed
to a genuine limit.

* `conformalDimension_four_sub_two_eq_sqrt` — the closed form `Δ − 2 = √(4 + μ)` in `AdS₅`.
* `dimension_excess_tendsto` — `Δ − 2 − mR → 0` as `mR → ∞`: the dimension excess is **exactly asymptotic**
  to `mR` (upgrading the band to a limit, `Filter.Tendsto … atTop (𝓝 0)`).
* `dimension_excess_ratio_tendsto` — `(Δ − 2)/mR → 1`: the leading anomalous dimension is asymptotically
  `mR`, the `λ^{1/4}` scaling.

Honest scope: this is the asymptotic behaviour of the exact `AdS₅` dimension formula as `mR → ∞`; the full
normalizable Bessel mode `z²K_ν(kz)` and the flux-factor two-point normalization are still the paper's
analytic inputs (as documented in `MassiveStringAnomalousDimensions`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Filter Topology

/-- **The `AdS₅` dimension in closed form** `Δ − 2 = √(4 + μ)` (with `Δ = conformalDimension 4 μ`). -/
theorem conformalDimension_four_sub_two_eq_sqrt (μ : ℝ) :
    conformalDimension 4 μ - 2 = Real.sqrt (4 + μ) := by
  unfold conformalDimension
  norm_num

/-- **The dimension excess is asymptotic to `mR`** `Δ − 2 − mR → 0` as `mR → ∞` — the two-sided band
`mR ≤ Δ − 2 ≤ mR + 2/(mR)` squeezed to a genuine limit. -/
@[zil_level physical_theorem]
theorem dimension_excess_tendsto :
    Tendsto (fun t : ℝ => conformalDimension 4 (t ^ 2) - 2 - t) atTop (𝓝 0) := by
  have hg : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hlo := (dimension_excess_bounds t 1 (by simpa using ht)).1
    simp only [mul_one] at hlo
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hhi := (dimension_excess_bounds t 1 (by simpa using ht)).2
    simp only [mul_one] at hhi
    linarith

/-- **The leading anomalous dimension is asymptotically `mR`** `(Δ − 2)/mR → 1` as `mR → ∞` — the
`λ^{1/4}` strong-coupling scaling as a genuine limit. -/
@[zil_level physical_theorem]
theorem dimension_excess_ratio_tendsto :
    Tendsto (fun t : ℝ => (conformalDimension 4 (t ^ 2) - 2) / t) atTop (𝓝 1) := by
  have hg : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  have hquot : Tendsto (fun t : ℝ => (conformalDimension 4 (t ^ 2) - 2 - t) / t) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hlo := (dimension_excess_bounds t 1 (by simpa using ht)).1
      simp only [mul_one] at hlo
      exact div_nonneg (by linarith) ht.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have h2 : conformalDimension 4 (t ^ 2) - 2 - t ≤ 2 := by
        rw [conformalDimension_four_sub_two_eq_sqrt]
        have hle : Real.sqrt (4 + t ^ 2) ≤ 2 + t := by
          rw [show (2 : ℝ) + t = Real.sqrt ((2 + t) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
          exact Real.sqrt_le_sqrt (by nlinarith)
        linarith
      rw [div_le_div_iff₀ ht ht]
      nlinarith [h2, ht]
  have key : Tendsto (fun t : ℝ => (conformalDimension 4 (t ^ 2) - 2 - t) / t + 1) atTop (𝓝 (0 + 1)) :=
    hquot.add_const 1
  rw [zero_add] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [div_add_one ht.ne']
  congr 1
  ring

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit

zil attach dimension_excess_tendsto where
  formalizes @ "claim:the-ads-five-operator-dimension-excess-delta-minus-two-minus-m-r-tends-to-zero-as-m-r-tends-to-infinity-the-two-sided-band-squeezed-to-a-genuine-limit-the-anomalous-dimension-is-exactly-asymptotic-to-m-r",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions.dimension_excess_bounds"

zil attach dimension_excess_ratio_tendsto where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-ads-five-leading-anomalous-dimension-ratio-delta-minus-two-over-m-r-tends-to-one-as-m-r-tends-to-infinity-the-lambda-to-the-one-quarter-strong-coupling-scaling-as-a-genuine-limit"

zil_file_contract physlib.massiveStringAnomalousDimensionLimit where
  promises "The strong-coupling anomalous dimension of the Gubser-Klebanov-Polyakov massive string state as a genuine limit, upgrading the previously-established two-sided band m R at most Delta minus two at most m R plus two over m R to an actual asymptotic statement. The AdS-five operator dimension has the closed form Delta minus two equals the square root of four plus mu. The dimension excess Delta minus two minus m R tends to zero as m R tends to infinity, so the anomalous dimension is exactly asymptotic to m R, and the ratio Delta minus two over m R tends to one, the lambda-to-the-one-quarter strong-coupling scaling as a genuine limit rather than an inequality band. Honest scope: this is the asymptotic behaviour of the exact AdS-five dimension formula as m R tends to infinity; the full normalizable Bessel mode and the flux-factor two-point normalization remain the paper's analytic inputs."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions.dimension_excess_bounds",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.conformalDimension"
  ]
  forbids_substitutes [
    "reading the asymptotic limit of the exact dimension formula as a derivation of the full normalizable Bessel mode or the flux-factor two-point normalization"
  ]
  witnessed_by [
    dimension_excess_tendsto,
    dimension_excess_ratio_tendsto
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.massiveStringAnomalousDimensionLimit

