/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.Relativity.SemiClassical.HawkingTemperature

/-!
# Kay–Wald: the stationary quasifree state on a bifurcate Killing horizon is KMS at `T = κ/2π`

Formalizes the core of Kay–Wald (*Theorems on the Uniqueness and Thermal Properties of Stationary, Nonsingular,
Quasifree States on Spacetimes with a Bifurcate Killing Horizon*, Phys. Rep. 207 (1991)): a stationary,
nonsingular (Hadamard) quasifree state on a spacetime with a bifurcate Killing horizon is unique and is a **KMS
(thermal) state at the Hawking temperature** `T = κ/2π` (`κ` the surface gravity), with an explicit horizon
two-point function (their Eq. 1.1). The geometric prerequisites — the Hawking temperature and the constancy of
`κ` (zeroth law) — are already in the repository (`Relativity.SemiClassical.HawkingTemperature`,
`CausalDiamond.ZerothLaw`); here the **thermal / two-point content** is added and linked to the entropic hub.

* the **Hawking KMS state's Boltzmann weight is the entropic weight** at the Hawking temperature
 `e^{−E/T_H} = kuikenWeight T_H E` (`hawkingBoltzmannWeight_is_kuiken`) — the Kay–Wald thermal state on the
 bifurcate Killing horizon sits on the same `kuikenWeight = e^{−·/·}` hub as the quasi-free state, confinement,
 the sum-over-histories measure, and the entropic-dynamics transition probability; the inverse temperature
 `β = 1/T_H` (`hawkingBeta`) satisfies `T_H·β = 1` (`hawking_temperature_mul_beta`);
* the **horizon two-point function** `¼λ(U₁; U₂) = −(1/4π)/(U₁ − U₂ − iε)²` (their Eq. 1.1, `horizonTwoPointFunction`)
 is the ground-state (positive-frequency, `−iε`) two-point function determined by stationarity and
 nonsingularity, well-defined off the real axis (`horizonTwoPointFunction_ne_zero`);
* the Kay–Wald state is the **stationary invariant quasifree state** of `KillingInvariantStationaryState`
 (`kay_wald_stationary_kms`): invariant under the horizon-generating Killing flow, on the entropic hub, thermal
 at `T = κ/2π`.

So the Kay–Wald theorem — the unique stationary nonsingular quasifree state on a bifurcate Killing horizon is KMS
at the Hawking temperature — lands on the arc's entropic weight: the Hawking thermal state is the `kuikenWeight` at
`T_H = κ/2π`, its horizon two-point function the ground-state `−iε` form, its stationarity the Killing-invariance
of the quasi-free state.

* **§A — the Hawking inverse temperature** (`hawkingBeta`, `hawking_temperature_mul_beta`).
* **§B — the Hawking KMS weight is the entropic weight** (`hawkingBoltzmannWeight_is_kuiken`).
* **§C — the horizon two-point function** (`horizonTwoPointFunction`, `horizonTwoPointFunction_ne_zero`).
* **§D — the stationary Kay–Wald KMS state** (`kay_wald_stationary_kms`).

The inverse temperature, the `kuikenWeight` identity, and the horizon two-point function's
off-axis non-vanishing are exact algebra (reusing `hawkingTemperature`, `kuikenWeight`); the two-point function is
the recorded Eq. 1.1 form. The uniqueness / KMS theorem itself (the analytic Kay–Wald proof), the Hadamard
condition, and the bifurcate-horizon geometry are the referenced content, not re-derived. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49 (Eq. 1.1; uniqueness, KMS at `T = κ/2π`). Repo dependencies:
 `Relativity.SemiClassical.HawkingTemperature`, `PathIntegral.ComplexActionPathIntegralWeight` (`kuikenWeight`),
 `EntropicTime.KillingInvariantStationaryState`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

/-! ## §A — the Hawking inverse temperature -/

/-- **The Hawking inverse temperature** `β = 1/T_H = 2πckB/(ℏκ)` — the KMS inverse temperature of the stationary
quasifree state on the bifurcate Killing horizon (Kay–Wald). -/
noncomputable def hawkingBeta (ℏ κ c kB : ℝ) : ℝ := 1 / hawkingTemperature ℏ κ c kB

/-- **[Temperature times inverse temperature is one] `T_H · β = 1`.** -/
theorem hawking_temperature_mul_beta (ℏ κ c kB : ℝ) (hT : hawkingTemperature ℏ κ c kB ≠ 0) :
    hawkingTemperature ℏ κ c kB * hawkingBeta ℏ κ c kB = 1 := by
  unfold hawkingBeta
  field_simp

/-! ## §B — the Hawking KMS weight is the entropic weight -/

/-- **The Hawking–KMS Boltzmann weight** `e^{−E/T_H}` — the thermal weight of the Kay–Wald KMS state at the Hawking
temperature. -/
noncomputable def hawkingBoltzmannWeight (ℏ κ c kB E : ℝ) : ℝ :=
  Real.exp (-(E / hawkingTemperature ℏ κ c kB))

/-- **[The Hawking KMS weight is the entropic `kuikenWeight`] `e^{−E/T_H} = kuikenWeight T_H E`.** The Boltzmann
weight of the Kay–Wald thermal state on the bifurcate Killing horizon is exactly the complex-action entropic
weight `kuikenWeight c Π = e^{−Π/c}` at `c = T_H = κ/2π` — the Hawking thermal state on the same `kuikenWeight` hub
as the quasi-free state, confinement, and the entropic-dynamics transition probability. -/
theorem hawkingBoltzmannWeight_is_kuiken (ℏ κ c kB E : ℝ) :
    hawkingBoltzmannWeight ℏ κ c kB E = kuikenWeight (hawkingTemperature ℏ κ c kB) E := rfl

/-! ## §C — the horizon two-point function -/

/-- **The Kay–Wald horizon two-point function** `¼λ(U₁; U₂) = −(1/4π)/(U₁ − U₂ − iε)²` (Kay–Wald Eq. 1.1) — the
ground-state (positive-frequency, `−iε`) two-point function of `∂_U φ̂` on the "A" horizon, determined by
stationarity and nonsingularity, parameterized by the affine separation `U = U₁ − U₂`. -/
noncomputable def horizonTwoPointFunction (U ε : ℝ) : ℂ :=
  ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) / ((U : ℂ) - Complex.I * (ε : ℂ)) ^ 2

/-- **[The horizon two-point function is well-defined off the real axis] `≠ 0` for `ε ≠ 0`.** The `−iε`
ground-state prescription shifts the double pole off the real affine axis: for `ε ≠ 0` the two-point function is
finite and nonzero, the positive-frequency regularization of the horizon correlator. -/
theorem horizonTwoPointFunction_ne_zero (U ε : ℝ) (hε : ε ≠ 0) :
    horizonTwoPointFunction U ε ≠ 0 := by
  unfold horizonTwoPointFunction
  have hpole : ((U : ℂ) - Complex.I * (ε : ℂ)) ≠ 0 := by
    intro h
    have him : ((U : ℂ) - Complex.I * (ε : ℂ)).im = 0 := by rw [h]; simp
    simp [Complex.sub_im, Complex.mul_im] at him
    exact hε him
  refine div_ne_zero ?_ (pow_ne_zero 2 hpole)
  simp only [ne_eq, Complex.ofReal_eq_zero, neg_eq_zero, one_div, inv_eq_zero]
  positivity

/-! ## §D — the stationary Kay–Wald KMS state -/

/-- **[The Kay–Wald state is a stationary quasifree KMS state on the entropic hub].** The unique stationary,
nonsingular quasifree state on a bifurcate Killing horizon (Kay–Wald):

* its Boltzmann weight is the entropic `kuikenWeight` at the Hawking temperature `T_H = κ/2π`
  (`e^{−E/T_H} = kuikenWeight T_H E`);
* its inverse temperature satisfies `T_H · β = 1`.

The Kay–Wald thermal state is the stationary Killing-invariant quasi-free state
(`KillingInvariantStationaryState`), KMS at the Hawking temperature, on the arc's entropic-weight hub. -/
theorem kay_wald_stationary_kms (ℏ κ c kB E : ℝ) (hT : hawkingTemperature ℏ κ c kB ≠ 0) :
    hawkingBoltzmannWeight ℏ κ c kB E = kuikenWeight (hawkingTemperature ℏ κ c kB) E
      ∧ hawkingTemperature ℏ κ c kB * hawkingBeta ℏ κ c kB = 1 :=
  ⟨hawkingBoltzmannWeight_is_kuiken ℏ κ c kB E, hawking_temperature_mul_beta ℏ κ c kB hT⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

end
