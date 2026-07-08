/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Temporal double-slit visibility decay in ENZ materials

Lean-side parametric infrastructure for the optical-frequency
temporal double-slit experiment used to calibrate the relation
between the dimensionless entropic-time accumulator and laboratory
time.

The module is deliberately **parametric**: physical constants and
material parameters enter as explicit inputs, not hard-coded
numerals. The theorems below establish positivity, monotonic-decay,
and boring-model-recovery properties of the formulas; numerical
predictions for specific input values are computed downstream.

## What the formulas predict

* `thermalEntropicRate kB T ℏ := kB·T/ℏ` — the thermal Connes–Rovelli
 rate at temperature `T`. This is **not** a complex-action/entropic-time-specific
 prediction; it is the same rate that appears in any KMS / modular
 treatment of a thermal state.

* `enzEntropicRate kB T ℏ n_g := thermalEntropicRate kB T ℏ · n_g`
 — the slow-light-enhanced rate in epsilon-near-zero (ENZ) media.
 The factor `n_g` (group index) enters as an **input parameter**,
 motivated physically by extended interaction time in slow-light
 media but not derived from first principles in this file.

* `fringeSpacing S := 1/S` — temporal-gate fringe spacing. This is
 the Fourier-conjugate relation for any two-time-gate interference
 experiment; **standard quantum mechanics gives the identical
 formula**, so this prediction does not distinguish complex-action/entropic-time from
 the baseline.

* `visibility V_cl lam_ent S := V_cl · exp(-lam_ent · S)` — the
 complex-action/entropic-time-distinguishing prediction. Standard QM with no entropic
 dissipation predicts `V(S) = V_cl` independent of `S`; complex-action/entropic-time
 predicts the exponential factor. The boring-model recovery at
 `lam_ent = 0` is the lemma `visibility_at_zero_rate` below.

## Scope

* This file encodes the predictions but does **not** prove they are
 experimentally confirmed. At the time of writing, the published
 Tirole et al. 2022 measurement matches the **fringe-spacing**
 formula `Δν = 1/S` (~1.97% MARE per the cited paper), which is
 standard interferometry and not complex-action/entropic-time-specific. The
 **visibility-decay** measurement — the actually distinguishing
 test — is a proposed protocol, not a completed experiment.

* The `n_g` enhancement factor is taken as input. Deriving it from
 ENZ optical properties would require formalising group velocity
 in dispersive media, which is outside the present scope.

* The visibility decay law itself rests on a path-local-decoherence
 assumption in the off-diagonal Lindblad evolution; this is the
 modelling hypothesis of complex-action/entropic-time and is encoded here as the input
 shape `V(S) = V_cl · exp(-lam_ent · S)`, not derived from first
 principles in this file.

## References

* Tirole, R. et al. 2022 — temporal double-slit experiment in
 indium tin oxide near the ENZ wavelength `lam ≈ 1240 nm`.
* CODATA 2018 — physical constants used in numerical predictions
 (`k_B = 1.380649 × 10⁻²³ J/K`, `ℏ = 1.054571817 × 10⁻³⁴ J·s`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.TemporalDoubleSlit

/-! ## §A — Entropic rate -/

/-- **Thermal entropic rate** `lam_th := k_B · T / ℏ`.  Units: `s⁻¹`. -/
def thermalEntropicRate (kB T ℏ : ℝ) : ℝ := kB * T / ℏ

/-- Thermal entropic rate is positive when each of `k_B, T, ℏ` is. -/
theorem thermalEntropicRate_pos {kB T ℏ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hℏ : 0 < ℏ) :
    0 < thermalEntropicRate kB T ℏ := by
  unfold thermalEntropicRate
  exact div_pos (mul_pos hkB hT) hℏ

/-- **ENZ-enhanced entropic rate** `lam_ENZ := lam_th · n_g`.

The group-index enhancement factor `n_g := c / v_g` is taken as an
input parameter, physically motivated by the extended light–matter
interaction time in slow-light media but not derived from first
principles in this file. -/
def enzEntropicRate (kB T ℏ n_g : ℝ) : ℝ :=
  thermalEntropicRate kB T ℏ * n_g

/-- ENZ entropic rate is positive when `k_B, T, ℏ, n_g > 0`. -/
theorem enzEntropicRate_pos {kB T ℏ n_g : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hℏ : 0 < ℏ) (hn_g : 0 < n_g) :
    0 < enzEntropicRate kB T ℏ n_g :=
  mul_pos (thermalEntropicRate_pos hkB hT hℏ) hn_g

/-- **Characteristic timescale** `τ_r := 1 / lam`.

The lab-frame interval over which the dimensionless entropic-time
accumulator advances by one unit at rate `lam`. -/
def characteristicTimescale (lam : ℝ) : ℝ := 1 / lam

theorem characteristicTimescale_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < characteristicTimescale lam :=
  div_pos one_pos hlam

/-- **Rate-timescale duality**: `τ_r · lam = 1`. -/
theorem characteristicTimescale_mul_rate {lam : ℝ} (hlam : lam ≠ 0) :
    characteristicTimescale lam * lam = 1 := by
  unfold characteristicTimescale
  field_simp

/-! ## §B — Fringe spacing (Fourier-conjugate; not complex-action/entropic-time-specific) -/

/-- **Temporal-gate fringe spacing** `Δν := 1/S` for two temporal
gates separated by lab time `S`.

This is the Fourier-conjugate relation between gate-separation and
frequency.  Standard quantum mechanics gives the identical formula;
the prediction is **not** complex-action/entropic-time-distinguishing. -/
def fringeSpacing (S : ℝ) : ℝ := 1 / S

theorem fringeSpacing_pos {S : ℝ} (hS : 0 < S) :
    0 < fringeSpacing S :=
  div_pos one_pos hS

theorem fringeSpacing_mul_S {S : ℝ} (hS : S ≠ 0) :
    fringeSpacing S * S = 1 := by
  unfold fringeSpacing
  field_simp

/-! ## §C — Visibility (complex-action/entropic-time-distinguishing prediction) -/

/-- **Classical visibility factor** for two-path interference with
amplitude ratio `η`: `V_cl(η) := 2η / (1 + η²)`. -/
def classicalVisibility (η : ℝ) : ℝ := 2 * η / (1 + η^2)

theorem classicalVisibility_at_one : classicalVisibility 1 = 1 := by
  unfold classicalVisibility
  norm_num

/-- `V_cl(η) ≥ 0` whenever `η ≥ 0`. -/
theorem classicalVisibility_nonneg {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ classicalVisibility η := by
  unfold classicalVisibility
  have h1 : (0 : ℝ) < 1 + η^2 := by positivity
  exact div_nonneg (by linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη]) h1.le

/-- **complex-action/entropic-time visibility prediction**:
`V(S) := V_cl · exp(-lam_ent · S)`.

The exponential decay at rate `lam_ent` is the falsifiable signature
that distinguishes complex-action/entropic-time from the standard QM baseline.  Standard
QM with no entropic dissipation predicts `V(S) = V_cl` independent
of `S`; complex-action/entropic-time predicts the exponential factor.  See
`visibility_at_zero_rate` for the boring-model recovery (`lam_ent = 0`
collapses to the standard QM baseline). -/
def visibility (V_cl lam_ent S : ℝ) : ℝ :=
  V_cl * Real.exp (-(lam_ent * S))

/-- **Visibility at S = 0** is the unmodified classical visibility. -/
@[simp] theorem visibility_at_zero (V_cl lam_ent : ℝ) :
    visibility V_cl lam_ent 0 = V_cl := by
  unfold visibility
  simp

/-- **Boring-model recovery**: at `lam_ent = 0`, visibility is constant
in `S` and equals `V_cl`.  This is the standard QM baseline; the
complex-action/entropic-time-distinguishing content lives in the `lam_ent > 0` regime. -/
@[simp] theorem visibility_at_zero_rate (V_cl S : ℝ) :
    visibility V_cl 0 S = V_cl := by
  unfold visibility
  simp

/-- **Visibility decays below `V_cl`** whenever `V_cl > 0` and the
exponent `lam_ent · S` is strictly positive. -/
theorem visibility_lt_classical_of_pos {V_cl lam_ent S : ℝ}
    (hV : 0 < V_cl) (hlam : 0 < lam_ent) (hS : 0 < S) :
    visibility V_cl lam_ent S < V_cl := by
  unfold visibility
  have hexp_lt : Real.exp (-(lam_ent * S)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [mul_pos hlam hS]
  calc V_cl * Real.exp (-(lam_ent * S))
      < V_cl * 1 := by
        exact mul_lt_mul_of_pos_left hexp_lt hV
    _ = V_cl := mul_one V_cl

/-- **Visibility is non-negative** for `V_cl ≥ 0`. -/
theorem visibility_nonneg {V_cl lam_ent S : ℝ} (hV : 0 ≤ V_cl) :
    0 ≤ visibility V_cl lam_ent S := by
  unfold visibility
  exact mul_nonneg hV (Real.exp_pos _).le

/-- **Visibility is strictly monotone-decreasing in `S`** at a
positive rate.  Together with `visibility_at_zero` and
`visibility_lt_classical_of_pos`, this is the falsifiable shape of
the complex-action/entropic-time prediction: positive `S` reduces visibility, with rate
`lam_ent` extractable from a slope fit. -/
theorem visibility_strictAnti_of_pos {V_cl lam_ent : ℝ}
    (hV : 0 < V_cl) (hlam : 0 < lam_ent) :
    StrictAnti (fun S : ℝ => visibility V_cl lam_ent S) := by
  intro S₁ S₂ hS
  unfold visibility
  have hexp : Real.exp (-(lam_ent * S₂)) < Real.exp (-(lam_ent * S₁)) := by
    apply Real.exp_lt_exp.mpr
    have := mul_lt_mul_of_pos_left hS hlam
    linarith
  exact mul_lt_mul_of_pos_left hexp hV

/-! ## §D — Log-visibility slope (the extractable observable)

The experimental procedure of the paper (§3315) extracts `lam_ent` by
plotting `ln(V(S)/V_cl)` against `S` and reading off the slope.  In
the complex-action/entropic-time prediction this is `-lam_ent · S`, a straight line through
the origin. -/

/-- **Log-visibility ratio**:
`ln(V(S) / V_cl) = -lam_ent · S` whenever `V_cl > 0`. -/
theorem log_visibility_ratio {V_cl lam_ent S : ℝ} (hV : 0 < V_cl) :
    Real.log (visibility V_cl lam_ent S / V_cl) = -(lam_ent * S) := by
  unfold visibility
  rw [mul_div_cancel_left₀ _ hV.ne']
  exact Real.log_exp _

/-! ## §E — Boring-model survival

The complex-action/entropic-time-specific visibility decay law must fail on the boring "no entropy
production" baseline.  This section records the explicit recovery
at `lam_ent = 0`. -/

/-- The boring "no entropy production" baseline gives a constant
log-visibility of `0`. -/
theorem log_visibility_ratio_at_zero_rate {V_cl S : ℝ} (hV : 0 < V_cl) :
    Real.log (visibility V_cl 0 S / V_cl) = 0 := by
  rw [visibility_at_zero_rate, div_self hV.ne', Real.log_one]

/-! ## §F — Planckian dissipation framework

The complex-action/entropic-time identification between the inverse ENZ entropic rate
and Tirole's measured rise time rests on the **Planckian
dissipation bound**: at electron temperature `T_e`, no quantum
system can thermalise faster than `τ_P := ℏ/(k_B · T_e)`.  Systems
that saturate this bound have `Π := λ · ℏ / (k_B · T_e) ≈ 1`.

For the Tirole ITO sample under intense optical pumping, the
hot-electron temperature reaches `T_e ≈ 10³ K`, giving
`τ_P ≈ 7.6 fs`.  The measured rise time `τ_rise ≈ 7.1 fs` gives
`Π_ENZ ≈ 1.1`, i.e. dissipation at the Planckian bound. -/

/-- **Planckian time** at temperature `T_e`:
`τ_P := ℏ / (k_B · T_e)`. The fundamental thermal timescale for
quantum dissipation at temperature `T_e`. -/
def planckianTime (kB T_e ℏ : ℝ) : ℝ := ℏ / (kB * T_e)

theorem planckianTime_pos {kB T_e ℏ : ℝ}
    (hkB : 0 < kB) (hT_e : 0 < T_e) (hℏ : 0 < ℏ) :
    0 < planckianTime kB T_e ℏ :=
  div_pos hℏ (mul_pos hkB hT_e)

/-- **Planckian dissipation ratio**:
`Π := λ · ℏ / (k_B · T_e) = λ · τ_P`. A dimensionless ratio
measuring how close a system operates to the Planckian
dissipation bound. `Π ≈ 1` saturates the bound. -/
def planckianRatio (lam kB T_e ℏ : ℝ) : ℝ :=
  lam * ℏ / (kB * T_e)

/-- The Planckian ratio equals `λ · τ_P`. -/
theorem planckianRatio_eq_mul_planckianTime
    (lam kB T_e ℏ : ℝ) :
    planckianRatio lam kB T_e ℏ = lam * planckianTime kB T_e ℏ := by
  unfold planckianRatio planckianTime
  ring

/-- The Planckian time times the thermal rate `λ_th := k_B T_e / ℏ`
is `1`: the Planckian time is the inverse thermal rate. -/
theorem planckianTime_mul_thermalEntropicRate
    {kB T_e ℏ : ℝ}
    (hkB : 0 < kB) (hT_e : 0 < T_e) (hℏ : 0 < ℏ) :
    planckianTime kB T_e ℏ * thermalEntropicRate kB T_e ℏ = 1 := by
  unfold planckianTime thermalEntropicRate
  field_simp

/-! ## §G — ENZ identification via Planckian universality

Replaces the earlier `IsEntropicRiseTimeIdentification` framing.
The complex-action/entropic-time paper (§2, Eq. neighborhood of Π_ENZ = 1.1 ± 0.1)
derives the identification from **two independent routes**:

(i) **Top-down (Planckian bound).** At the measured hot-electron
temperature `T_e ≈ 10³ K`, the Planckian time `τ_P = ℏ/(k_B T_e)
≈ 7.6 fs` sets the maximum thermalisation rate.  Measured
`τ_rise = 7.1 fs` saturates this bound with `Π_ENZ = 1.1 ± 0.1`.

(ii) **Bottom-up (group-velocity geometric formula).** At the
ENZ pole `ε(ω₀) ≈ 0`, group velocity vanishes and `λ` is
determined by `(c/2)·∫d³k |v_g|⁻¹ f(k)`.  This is an algebraic
fact about the dielectric pole structure, independent of the
microscopic mechanism (plasma frequency, scattering, effective
mass, density).  The paper claims the formula yields 7.1 fs.

The Lean predicate below encodes route (i): `τ_rise = τ_P` at the
hot-electron temperature. -/

/-- **Planckian identification of the ENZ rise time**: the optical
rise time equals the Planckian time at the hot-electron
temperature.

  `τ_rise = ℏ / (k_B · T_e)`.

This is the saturation condition `Π = 1`; the Tirole experiment
gives `Π ≈ 1.1 ± 0.1`. Stated as a Prop because the saturation
is empirical, not a theorem of the framework. -/
def IsPlanckianRiseTime (τ_rise kB T_e ℏ : ℝ) : Prop :=
  τ_rise = planckianTime kB T_e ℏ

/-- Under the Planckian identification, the rise time scales as
`1/T_e`. Cooling the hot-electron electron gas doubles the rise
time. -/
theorem planckianRiseTime_temperature_scaling
    {τ₁ τ₂ kB T₁ T₂ ℏ : ℝ}
    (hkB : 0 < kB) (hℏ : 0 < ℏ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (h₁ : IsPlanckianRiseTime τ₁ kB T₁ ℏ)
    (h₂ : IsPlanckianRiseTime τ₂ kB T₂ ℏ) :
    τ₂ * T₂ = τ₁ * T₁ := by
  unfold IsPlanckianRiseTime planckianTime at h₁ h₂
  rw [h₁, h₂]
  field_simp

/-- Under the Planckian identification, `λ_rise := 1/τ_rise`
equals the thermal rate `k_B T_e / ℏ`. -/
theorem rate_eq_thermalRate_of_planckian
    {τ_rise kB T_e ℏ : ℝ}
    (hkB : 0 < kB) (hT_e : 0 < T_e) (hℏ : 0 < ℏ)
    (hτ : 0 < τ_rise)
    (h_id : IsPlanckianRiseTime τ_rise kB T_e ℏ) :
    1 / τ_rise = thermalEntropicRate kB T_e ℏ := by
  show 1 / τ_rise = thermalEntropicRate kB T_e ℏ
  unfold thermalEntropicRate
  have h : τ_rise = planckianTime kB T_e ℏ := h_id
  rw [h]
  unfold planckianTime
  rw [one_div, inv_div]

/-! ## §H — Multi-technique consistency

Per the complex-action/entropic-time paper §2, the entropic framework predicts that
**three independent measurement techniques** on the same sample
must yield the same `1/λ` because all three probe the same
operator eigenvalue:

* `τ₁` from ultrafast pump-probe spectroscopy,
* `τ₂` from terahertz modulation spectroscopy,
* `τ₃` from temporal double-slit interferometry.

The paper reports `τ₁ = 7.1 ± 0.3 fs`, `τ₂ = 7.0 ± 0.4 fs`,
`τ₃ = 6.9 ± 0.5 fs` for ITO, with `χ² = 0.14` and `p = 0.93`
favouring a single underlying timescale; `ΔAIC = 4.2` favours
the entropic framework over independent-rate phenomenology.

Standard phenomenology allows independent fits; the entropic
framework forces equality. The structure below records that
prediction as a `Prop`. -/

/-- **Three-technique consistency**: the rise times measured by
pump-probe, THz modulation, and temporal double-slit on the same
sample are all equal under the entropic framework. -/
structure ThreeTechniqueConsistency where
  /-- Pump-probe rise time. -/
  τ_pump_probe   : ℝ
  /-- THz modulation rise time. -/
  τ_thz          : ℝ
  /-- Temporal double-slit rise time. -/
  τ_double_slit  : ℝ
  /-- Entropic framework forces all three equal. -/
  equal_pump_thz : τ_pump_probe = τ_thz
  equal_thz_ds   : τ_thz        = τ_double_slit

namespace ThreeTechniqueConsistency

/-- The common rise time across all three techniques. -/
def commonRiseTime (C : ThreeTechniqueConsistency) : ℝ :=
  C.τ_pump_probe

@[simp] theorem commonRiseTime_eq_pump_probe (C : ThreeTechniqueConsistency) :
    C.commonRiseTime = C.τ_pump_probe := rfl

theorem commonRiseTime_eq_thz (C : ThreeTechniqueConsistency) :
    C.commonRiseTime = C.τ_thz := C.equal_pump_thz

theorem commonRiseTime_eq_double_slit (C : ThreeTechniqueConsistency) :
    C.commonRiseTime = C.τ_double_slit := by
  rw [commonRiseTime_eq_pump_probe, C.equal_pump_thz, C.equal_thz_ds]

end ThreeTechniqueConsistency

end Physlib.Optics.TemporalDoubleSlit

end
