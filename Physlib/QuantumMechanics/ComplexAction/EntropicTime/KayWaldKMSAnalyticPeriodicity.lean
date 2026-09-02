/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Calculus.ParametricIntegral
meta import Zil

/-!
# The KMS condition: the thermal two-point function is analytic and `β`-periodic, `G(t − iβ) = G(−t)` (Kay–Wald)

Formalizes the analytic **Kubo–Martin–Schwinger (KMS) condition** — the defining property that makes the Kay–Wald
horizon state *thermal*. For a single Killing-horizon mode of frequency `ω`, the stationary two-point (Wightman)
function in the Hawking–KMS state is

`G_β(t) = (n+1) e^{−iωt} + n e^{+iωt}`,  `n = 1/(e^{βω} − 1)`  (the Bose occupation),

and it satisfies the KMS periodicity in imaginary time

`G_β(t − iβ) = G_β(−t)`.

This is the algebraic content behind the thermality of the Kay–Wald state: the correlator, analytically continued
by one period `β = 2π/κ` of imaginary Killing time, reproduces the time-reversed correlator. The proof is *exactly*
the detailed-balance relations of the Bose occupation (`KayWaldHawkingRadiationBoseEinstein`),
`(n+1) e^{−βω} = n` and `n e^{βω} = n+1`, lifted to the complexified time argument.

* the **detailed-balance identities** `(n+1) e^{−βω} = n` and `n e^{βω} = n+1` (`occupation_add_one_mul_exp_neg`,
  `occupation_mul_exp`) — the emission/absorption ratios of the Hawking occupation `n`;
* the **thermal Wightman function** `G_β(t) = (n+1) e^{−iωt} + n e^{+iωt}` (`thermalWightman`) — the stationary
  two-point function of a horizon mode in the Hawking–KMS state, on complexified time;
* the **KMS condition** `G_β(t − iβ) = G_β(−t)` (`thermalWightman_kms`) — the imaginary-time periodicity that *is*
  the thermal (KMS) equilibrium condition; the whole statement collapses onto the two detailed-balance identities;
* the **Hawking specialization** `β = 2π/κ` (`hawking_kms_period`) — at the Hawking inverse temperature
  `β = hawkingBeta 1 κ 1 1 = 2π/κ` the horizon correlator's KMS imaginary period is the geometric Killing-horizon
  period (`imaginary_period_is_hawking_beta`), closing the loop geometry → occupation → KMS.

So the Kay–Wald thermality is this one identity: the horizon two-point function is periodic in imaginary Killing
time with period the Hawking inverse temperature `β = 2π/κ`, and that periodicity is nothing but the
detailed-balance ratios of the Bose–Einstein occupation.

* **§A — the detailed-balance identities** (`occupation_add_one_mul_exp_neg`, `occupation_mul_exp`).
* **§B — the thermal Wightman function and the KMS condition** (`thermalWightman`, `thermalWightman_kms`).
* **§C — the Hawking specialization `β = 2π/κ`** (`hawking_kms_period`).

**Honest layering.** The single-mode thermal two-point function, its KMS `β`-periodicity, and the detailed-balance
identities are exact `Real.exp`/`Complex.exp` algebra.  Section D proves that weighted modes are entire, lifts
the KMS boundary equality through a genuine Bochner spectral integral, and proves continuum complex
differentiability from explicit local integrable derivative bounds.  What remains external is the
mode/spectral decomposition of a specific horizon field, its Hadamard/positivity proof, and the equivalence
between this spectral realization and the fully abstract operator-algebraic KMS characterization for a
type-III algebra. ## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; R. Kubo; P.C. Martin, J. Schwinger (KMS condition). Repo carriers:
  `EntropicTime.KayWaldHawkingRadiationBoseEinstein` (`hawkingOccupation`, detailed balance),
  `EntropicTime.KayWaldBifurcateHorizonSurfaceGravity` (`imaginary_period_is_hawking_beta`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Filter MeasureTheory

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity


/-- **[Detailed balance: `(n+1) e^{−βω} = n`].** The total-emission occupation `n+1` times the Boltzmann factor
`e^{−βω}` returns the absorption occupation `n = 1/(e^{βω}−1)` — one of the two KMS detailed-balance ratios of the
Hawking–Bose occupation. -/
lemma occupation_add_one_mul_exp_neg (β ω : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    (hawkingOccupation β ω + 1) * Real.exp (-(β * ω)) = hawkingOccupation β ω := by
  unfold hawkingOccupation
  rw [Real.exp_neg]
  have hE : Real.exp (β * ω) ≠ 0 := Real.exp_ne_zero _
  field_simp
  ring

/-- **[Detailed balance: `n e^{βω} = n+1`].** The absorption occupation `n` times the Boltzmann factor `e^{βω}`
returns the total-emission occupation `n+1` — the second KMS detailed-balance ratio. -/
lemma occupation_mul_exp (β ω : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    hawkingOccupation β ω * Real.exp (β * ω) = hawkingOccupation β ω + 1 := by
  unfold hawkingOccupation
  field_simp
  ring


/-- **The thermal (Wightman) two-point function of a horizon mode** `G_β(t) = (n+1) e^{−iωt} + n e^{+iωt}` with
`n = hawkingOccupation β ω` the Bose occupation — the stationary two-point function of a Killing-horizon mode of
frequency `ω` in the Hawking–KMS state, on complexified time `t ∈ ℂ`. -/
noncomputable def thermalWightman (β ω : ℝ) (t : ℂ) : ℂ :=
  ((hawkingOccupation β ω + 1 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω : ℂ) * t))
    + ((hawkingOccupation β ω : ℝ) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * t)

/-- **[The KMS condition] `G_β(t − iβ) = G_β(−t)`.** The thermal two-point function is periodic under a shift of the
time argument by one imaginary period `−iβ`, reproducing the time-reversed correlator. Expanding the shift,
`e^{−iω(t−iβ)} = e^{−iωt} e^{−βω}` and `e^{+iω(t−iβ)} = e^{+iωt} e^{+βω}`, the two Boltzmann factors turn the
occupation coefficients into one another by detailed balance — `(n+1) e^{−βω} = n` and `n e^{βω} = n+1` — which is
exactly the swap producing `G_β(−t)`. This imaginary-time periodicity is the defining KMS (thermal-equilibrium)
condition of the Kay–Wald state. -/
lemma thermalWightman_kms (β ω : ℝ) (t : ℂ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    thermalWightman β ω (t - Complex.I * (β : ℂ)) = thermalWightman β ω (-t) := by
  unfold thermalWightman
  have db1C : ((hawkingOccupation β ω + 1 : ℝ) : ℂ) * ((Real.exp (-(β * ω)) : ℝ) : ℂ)
      = ((hawkingOccupation β ω : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, occupation_add_one_mul_exp_neg β ω h]
  have db2C : ((hawkingOccupation β ω : ℝ) : ℂ) * ((Real.exp (β * ω) : ℝ) : ℂ)
      = ((hawkingOccupation β ω + 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, occupation_mul_exp β ω h]
  have arg1 : -(Complex.I * (ω : ℂ) * (t - Complex.I * (β : ℂ)))
      = -(Complex.I * (ω : ℂ) * t) + ((-(β * ω) : ℝ) : ℂ) := by
    push_cast
    linear_combination ((β : ℂ) * (ω : ℂ)) * Complex.I_sq
  have arg2 : Complex.I * (ω : ℂ) * (t - Complex.I * (β : ℂ))
      = Complex.I * (ω : ℂ) * t + ((β * ω : ℝ) : ℂ) := by
    push_cast
    linear_combination (-((β : ℂ) * (ω : ℂ))) * Complex.I_sq
  have arg3 : -(Complex.I * (ω : ℂ) * -t) = Complex.I * (ω : ℂ) * t := by ring
  have arg4 : Complex.I * (ω : ℂ) * -t = -(Complex.I * (ω : ℂ) * t) := by ring
  rw [arg1, arg2, arg3, arg4, Complex.exp_add, Complex.exp_add,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  set A := Complex.exp (-(Complex.I * (ω : ℂ) * t))
  set B := Complex.exp (Complex.I * (ω : ℂ) * t)
  linear_combination A * db1C + B * db2C


/-- **[The horizon correlator is KMS at the Hawking inverse temperature] `β = 2π/κ`.** Specializing the KMS
condition to the Hawking inverse temperature `β = hawkingBeta 1 κ 1 1 = 2π/κ`: the stationary two-point function of
a bifurcate-Killing-horizon mode is periodic in imaginary Killing time with period the Hawking `β`, whose value is
the geometric horizon period `2π/κ` (`imaginary_period_is_hawking_beta`). Geometry (`U = e^{κv}`), the Bose
occupation, and the KMS thermal condition close into one. -/
lemma hawking_kms_period (κ ω : ℝ) (t : ℂ)
    (h : Real.exp (hawkingBeta 1 κ 1 1 * ω) - 1 ≠ 0) :
    thermalWightman (hawkingBeta 1 κ 1 1) ω (t - Complex.I * ((hawkingBeta 1 κ 1 1 : ℝ) : ℂ))
      = thermalWightman (hawkingBeta 1 κ 1 1) ω (-t) :=
  thermalWightman_kms (hawkingBeta 1 κ 1 1) ω t h

/-! ## §D Pointwise and continuum spectral KMS analyticity -/

variable {X : Type*}

/-- **A weighted pointwise KMS mode** on an arbitrary spectral carrier. -/
noncomputable def weightedThermalWightman
    (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ) (z : ℂ) (x : X) : ℂ :=
  weight x * thermalWightman β (frequency x) z

/-- **Every weighted spectral mode is entire in complex time.**
This uses the actual complex exponential differentiability, not a declared analyticity flag. -/
theorem weightedThermalWightman_differentiable
    (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ) (x : X) :
    Differentiable ℂ (fun z => weightedThermalWightman β frequency weight z x) := by
  unfold weightedThermalWightman thermalWightman
  fun_prop

/-- **The KMS boundary identity holds pointwise at every regular spectral mode.** -/
theorem weightedThermalWightman_kms
    (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ) (t : ℂ) (x : X)
    (hregular : Real.exp (β * frequency x) - 1 ≠ 0) :
    weightedThermalWightman β frequency weight
        (t - Complex.I * (β : ℂ)) x =
      weightedThermalWightman β frequency weight (-t) x := by
  unfold weightedThermalWightman
  rw [thermalWightman_kms β (frequency x) t hregular]

section Continuum

variable [MeasurableSpace X]

/-- **The continuum thermal Wightman function** obtained by Bochner-integrating
the pointwise KMS modes over an arbitrary spectral measure. -/
noncomputable def continuumThermalWightman
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ) (z : ℂ) : ℂ :=
  ∫ x, weightedThermalWightman β frequency weight z x ∂μ

/-- **[Continuum KMS boundary theorem].**
The pointwise KMS equality lifts through the genuine Bochner spectral integral.  Only
almost-everywhere regularity of the Bose denominator is required. -/
theorem continuumThermalWightman_kms
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ) (t : ℂ)
    (hregular : ∀ᵐ x ∂μ, Real.exp (β * frequency x) - 1 ≠ 0) :
    continuumThermalWightman μ β frequency weight
        (t - Complex.I * (β : ℂ)) =
      continuumThermalWightman μ β frequency weight (-t) := by
  unfold continuumThermalWightman
  apply integral_congr_ae
  filter_upwards [hregular] with x hx
  exact weightedThermalWightman_kms β frequency weight t x hx

/-- **Dominated spectral data for differentiating the continuum KMS integral.**
Every analytic obligation is quantitative: local derivative bounds, their integrability,
and strong measurability of the integrand and derivative. -/
structure ContinuumKMSAnalyticCertificate
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ) where
  neighborhood : ℂ → Set ℂ
  neighborhood_mem : ∀ z, neighborhood z ∈ nhds z
  integrand_measurable :
    ∀ z, AEStronglyMeasurable (weightedThermalWightman β frequency weight z) μ
  integrand_integrable :
    ∀ z, Integrable (weightedThermalWightman β frequency weight z) μ
  derivative_measurable :
    ∀ z, AEStronglyMeasurable
      (fun x => deriv (fun w => weightedThermalWightman β frequency weight w x) z) μ
  bound : ℂ → X → ℝ
  derivative_bound :
    ∀ z, ∀ᵐ x ∂μ, ∀ w ∈ neighborhood z,
      ‖deriv (fun u => weightedThermalWightman β frequency weight u x) w‖ ≤ bound z x
  bound_integrable : ∀ z, Integrable (bound z) μ

/-- **[Continuum KMS analyticity].**
The spectral integral is complex differentiable at every complex time.  Mathlib's
dominated differentiation theorem supplies the continuum passage, while pointwise
differentiability is proved above from `Complex.exp`. -/
theorem continuumThermalWightman_differentiable
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ) (weight : X → ℂ)
    (C : ContinuumKMSAnalyticCertificate μ β frequency weight) :
    Differentiable ℂ (continuumThermalWightman μ β frequency weight) := by
  intro z
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (C.neighborhood_mem z)
      (Filter.Eventually.of_forall C.integrand_measurable)
      (C.integrand_integrable z)
      (C.derivative_measurable z)
      (C.derivative_bound z)
      (C.bound_integrable z)
      (Filter.Eventually.of_forall fun x w _ =>
        (weightedThermalWightman_differentiable β frequency weight x w).hasDerivAt)
  exact h.2.differentiableAt

end Continuum

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.weightedThermalWightman_differentiable where
  formalizes @ "claim:every-weighted-kay-wald-spectral-mode-is-entire-in-complex-killing-time",
  supported_by @ "paper:kay-wald-1991-kms-analyticity-on-a-bifurcate-killing-horizon",
  supported_by @ "lean:Complex.differentiable_exp"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_kms where
  formalizes @ "claim:the-pointwise-kms-boundary-identity-lifts-to-the-continuum-bochner-spectral-integral",
  requires @ "claim:the-bose-denominator-is-nonzero-almost-everywhere-in-the-selected-spectrum",
  supported_by @ "paper:kay-wald-1991-kms-analyticity-on-a-bifurcate-killing-horizon"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_differentiable where
  formalizes @ "claim:dominated-pointwise-entire-kms-modes-produce-a-complex-differentiable-continuum-spectral-correlator",
  requires @ "claim:local-integrable-dominating-bounds-for-the-spectral-derivative",
  supported_by @ "lean:hasDerivAt_integral_of_dominated_loc_of_deriv_le",
  caveat @ "claim:the-certificate-exposes-measurability-integrability-and-local-derivative-domination-rather-than-assuming-the-differentiability-conclusion"

zil_file_contract physlib.kayWaldContinuumKMSAnalyticity where
  promises "Kay-Wald KMS analyticity is lifted from the existing exact complex-time mode theorem to a genuine spectral continuum. Every weighted mode is proved entire from Complex.exp; the KMS boundary equality holds almost everywhere pointwise and therefore under the Bochner spectral integral; quantitative local derivative domination and integrability then prove complex differentiability of the continuum correlator by differentiation under the integral."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.thermalWightman_kms",
    "lean:hasDerivAt_integral_of_dominated_loc_of_deriv_le"]
  forbids_substitutes ["a finite spectral sum relabeled as a continuum integral",
    "an opaque analytic flag replacing complex differentiability",
    "moving a derivative through the spectral integral without an integrable local majorant"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.weightedThermalWightman_differentiable,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.weightedThermalWightman_kms,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_kms,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_differentiable]

/- ZIL-END -/
