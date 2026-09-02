/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

/-!
# The metric is the common root of both invariances (kinematic and entropic)

`Bogoliubov.RestFrameQIFConsistency` showed the metric-preserving boost carries the rest mass (the
`S`-norm) and the entropic rate consistently. This file proves the stronger statement — that the
**metric is the common root** of *both* invariances — grounded in the Nagao-Nielsen complex
oscillator and the arc's entropic time.

## Where the entropic time enters

The arc's entropic time `τ_ent = S_I/ℏ` (entropy production) enters the Bogoliubov transformation as
the **entanglement entropy of the quasiparticle occupation `v²`**. The Bogoliubov mode-mixing
entangles particle and hole; tracing out one partner leaves a single-mode state with occupation `v²`,
whose binary / von Neumann entropy is the entropy production:

  `τ_ent = binEntropy(v²)`   (`Bogoliubov.EntropicTime.bogoliubovEntropicTime`).

## The common root: one metric quantity `m = u² − v²`

Write the **metric `S`-norm** of the Bogoliubov spinor `(u, v)` as `m := u² − v²`. It is the
Minkowski (`S = diag(1,−1)`) quadratic form of the spinor, `m = lorentzianForm(u + iv)`
(`bogoliubov_spinor_metric_norm`), and equals the velocity `ξ/E` (`bogoliubov_uv_diff`). This single
`m` is the root of both invariances:

* **Kinematic** — `m = u² − v² = ξ/E` is the boost velocity, with the mass shell
  `E² = ξ² + Δ²` (`bogoliubovEnergy_sq`; `Δ` the rest mass, `E` the Nagao-Nielsen oscillator
  dispersion `photonDispersion Δ 1 ξ`, `bogoliubovEnergy_is_oscillator_dispersion`);
* **Entropic** — the occupation is `v² = (1 − m)/2` (`bogoliubovV2_eq_half_one_sub_uvDiff`, from the
  normalization `u² + v² = 1`), so the entropic time is a **function of the same `m`**:
  `τ_ent = binEntropy((1 − m)/2)` (`entropicTime_eq_binEntropy_velocity`).

So the kinematic invariant *is* `m`, and the entropic invariant is `binEntropy((1−m)/2)` — both
determined by the single metric `S`-norm `m`. At the **metric-null** points `m = ±1` (the `45°` light
cone, the massless/`Δ→0` limit) the entropy vanishes, `τ_ent = 0`
(`entropicTime_zero_iff_metric_luminal`) — reversibility is exactly the metric-luminal condition.

## Main results

* `bogoliubovEnergy_sq`, `bogoliubovEnergy_is_oscillator_dispersion` — `E² = ξ² + Δ²`, `E` = NN
  oscillator dispersion.
* `bogoliubov_spinor_metric_norm` — `m = u² − v² = lorentzianForm(u + iv) = ξ/E` (the metric `S`-norm).
* `bogoliubovV2_eq_half_one_sub_uvDiff` — `v² = (1 − m)/2`.
* `entropicTime_eq_binEntropy_velocity` — `τ_ent = binEntropy((1 − m)/2)`.
* `entropicTime_zero_iff_metric_luminal` — `τ_ent = 0 ⟺ m = ±1` (metric-null / light cone).
* `metric_common_root` — the bundled statement: one `m` roots both invariances.

## References

* N. N. Bogoliubov 1947; P. T. Nam, M. Napiórkowski, J. P. Solovej, J. Funct. Anal. **270** (2016)
  4340. doi:10.1016/j.jfa.2015.12.007. K. Nagao, H. B. Nielsen, arXiv:1902.01424 (complex oscillator).
* This development: `Bogoliubov.EntropicTime`, `Bogoliubov.Transformation`,
  `TimeOperator.HyperbolicPoincareLorentzMisra`; `Real.binEntropy` (Mathlib).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Real
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime


/-- **The mass shell** `E² = ξ² + Δ²` (`Δ` the rest mass / gap). -/
lemma bogoliubovEnergy_sq (ξ Δ : ℝ) : bogoliubovEnergy ξ Δ ^ 2 = ξ ^ 2 + Δ ^ 2 := by
  unfold bogoliubovEnergy
  rw [Real.sq_sqrt (by positivity)]

/-- **The Bogoliubov quasiparticle energy is the Nagao-Nielsen oscillator dispersion**
`E = photonDispersion Δ 1 ξ` — the Bogoliubov transformation diagonalizes the complex oscillator. -/
lemma bogoliubovEnergy_is_oscillator_dispersion (ξ Δ : ℝ) :
    bogoliubovEnergy ξ Δ = photonDispersion Δ 1 ξ :=
  bogoliubov_energy_eq_photonDispersion ξ Δ


/-- **The metric `S`-norm of the Bogoliubov spinor** `m = u² − v² = lorentzianForm(√u² + i√v²) =
ξ/E`: the Minkowski (`S = diag(1,−1)`) quadratic form of the coherence spinor is the velocity. -/
lemma bogoliubov_spinor_metric_norm (ξ Δ : ℝ) (hu : 0 ≤ bogoliubovU2 ξ Δ)
    (hv : 0 ≤ bogoliubovV2 ξ Δ) :
    lorentzianForm ((Real.sqrt (bogoliubovU2 ξ Δ) : ℂ)
        + (Real.sqrt (bogoliubovV2 ξ Δ) : ℂ) * Complex.I)
      = ξ / bogoliubovEnergy ξ Δ := by
  rw [lorentzianForm_ofReal_add_mul_I, Real.sq_sqrt hu, Real.sq_sqrt hv, bogoliubov_uv_diff]


/-- **The occupation is `v² = (1 − m)/2`** (from the normalization `u² + v² = 1`): the entropic data
is determined by the metric `S`-norm `m = u² − v²`. -/
lemma bogoliubovV2_eq_half_one_sub_uvDiff (ξ Δ : ℝ) :
    bogoliubovV2 ξ Δ = (1 - (bogoliubovU2 ξ Δ - bogoliubovV2 ξ Δ)) / 2 := by
  have h := bogoliubov_normalization ξ Δ
  linarith

/-- **The entropic time is `binEntropy` of the metric quantity** `τ_ent = binEntropy((1 − m)/2)`
with `m = u² − v²`. -/
lemma entropicTime_eq_binEntropy_uvDiff (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ
      = Real.binEntropy ((1 - (bogoliubovU2 ξ Δ - bogoliubovV2 ξ Δ)) / 2) := by
  unfold bogoliubovEntropicTime
  congr 1
  exact bogoliubovV2_eq_half_one_sub_uvDiff ξ Δ

/-- **The entropic time as a function of the velocity** `τ_ent = binEntropy((1 − ξ/E)/2)` (`m = ξ/E`,
the metric `S`-norm). -/
lemma entropicTime_eq_binEntropy_velocity (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2) := rfl


/-- **Reversibility is the metric-luminal condition** `τ_ent = 0 ⟺ m = ±1`: the entropy vanishes
exactly at the metric-null velocity `ξ/E = ±1` — the `45°` light cone, the massless/`Δ → 0` limit. -/
lemma entropicTime_zero_iff_metric_luminal (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = 0
      ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1 := by
  rw [bogoliubov_entropicTime_eq_zero_iff]
  unfold bogoliubovV2
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num


/-- **The metric is the common root of both invariances.** The single metric `S`-norm
`m = u² − v² = ξ/E` roots:

* the **kinematic** invariant — `m` is the boost velocity, with mass shell `E² = ξ² + Δ²`;
* the **entropic** invariant — `τ_ent = binEntropy((1 − m)/2)`, the entanglement entropy of the
  occupation `v² = (1 − m)/2`;

and reversibility (`τ_ent = 0`) is exactly the metric-null `m = ±1` (the light cone). Both the
rest-mass kinematics and the entropy production are functions of the one metric quantity `m`. -/
lemma metric_common_root (ξ Δ : ℝ) :
    bogoliubovEnergy ξ Δ ^ 2 = ξ ^ 2 + Δ ^ 2
      ∧ bogoliubovU2 ξ Δ - bogoliubovV2 ξ Δ = ξ / bogoliubovEnergy ξ Δ
      ∧ bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2)
      ∧ (bogoliubovEntropicTime ξ Δ = 0
          ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1) :=
  ⟨bogoliubovEnergy_sq ξ Δ, bogoliubov_uv_diff ξ Δ,
   entropicTime_eq_binEntropy_velocity ξ Δ, entropicTime_zero_iff_metric_luminal ξ Δ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime

end

end
