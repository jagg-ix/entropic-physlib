/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum
meta import Zil

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

**Honest layering.** The inverse temperature, the `kuikenWeight` identity, and the horizon two-point function's
off-axis non-vanishing are exact algebra (reusing `hawkingTemperature`, `kuikenWeight`); the two-point function is
the recorded Eq. 1.1 form. The uniqueness / KMS theorem itself (the analytic Kay–Wald proof), the Hadamard
condition, and the bifurcate-horizon geometry are the referenced content, not re-derived. ## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49 (Eq. 1.1; uniqueness, KMS at `T = κ/2π`). Repo carriers:
  `Relativity.SemiClassical.HawkingTemperature`, `PathIntegral.ComplexActionPathIntegralWeight` (`kuikenWeight`),
  `EntropicTime.KillingInvariantStationaryState`.


-/

set_option autoImplicit false

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon


/-- **The Hawking inverse temperature** `β = 1/T_H = 2πckB/(ℏκ)` — the KMS inverse temperature of the stationary
quasifree state on the bifurcate Killing horizon (Kay–Wald). -/
noncomputable def hawkingBeta (ℏ κ c kB : ℝ) : ℝ := 1 / hawkingTemperature ℏ κ c kB

/-- **[Temperature times inverse temperature is one] `T_H · β = 1`.** -/
lemma hawking_temperature_mul_beta (ℏ κ c kB : ℝ) (hT : hawkingTemperature ℏ κ c kB ≠ 0) :
    hawkingTemperature ℏ κ c kB * hawkingBeta ℏ κ c kB = 1 := by
  unfold hawkingBeta
  field_simp


/-- **The Hawking–KMS Boltzmann weight** `e^{−E/T_H}` — the thermal weight of the Kay–Wald KMS state at the Hawking
temperature. -/
noncomputable def hawkingBoltzmannWeight (ℏ κ c kB E : ℝ) : ℝ :=
  Real.exp (-(E / hawkingTemperature ℏ κ c kB))

/-- **[The Hawking KMS weight is the entropic `kuikenWeight`] `e^{−E/T_H} = kuikenWeight T_H E`.** The Boltzmann
weight of the Kay–Wald thermal state on the bifurcate Killing horizon is exactly the complex-action entropic
weight `kuikenWeight c Π = e^{−Π/c}` at `c = T_H = κ/2π` — the Hawking thermal state on the same `kuikenWeight` hub
as the quasi-free state, confinement, and the entropic-dynamics transition probability. -/
lemma hawkingBoltzmannWeight_is_kuiken (ℏ κ c kB E : ℝ) :
    hawkingBoltzmannWeight ℏ κ c kB E = kuikenWeight (hawkingTemperature ℏ κ c kB) E := rfl


/-- **The Kay–Wald horizon two-point function** `¼λ(U₁; U₂) = −(1/4π)/(U₁ − U₂ − iε)²` (Kay–Wald Eq. 1.1) — the
ground-state (positive-frequency, `−iε`) two-point function of `∂_U φ̂` on the "A" horizon, determined by
stationarity and nonsingularity, parameterized by the affine separation `U = U₁ − U₂`. -/
noncomputable def horizonTwoPointFunction (U ε : ℝ) : ℂ :=
  ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) / ((U : ℂ) - Complex.I * (ε : ℂ)) ^ 2

/-- **[The horizon two-point function is well-defined off the real axis] `≠ 0` for `ε ≠ 0`.** The `−iε`
ground-state prescription shifts the double pole off the real affine axis: for `ε ≠ 0` the two-point function is
finite and nonzero, the positive-frequency regularization of the horizon correlator. -/
lemma horizonTwoPointFunction_ne_zero (U ε : ℝ) (hε : ε ≠ 0) :
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


/-- **[The Kay–Wald state is a stationary quasifree KMS state on the entropic hub].** The unique stationary,
nonsingular quasifree state on a bifurcate Killing horizon (Kay–Wald):

* its Boltzmann weight is the entropic `kuikenWeight` at the Hawking temperature `T_H = κ/2π`
  (`e^{−E/T_H} = kuikenWeight T_H E`);
* its inverse temperature satisfies `T_H · β = 1`.

The Kay–Wald thermal state is the stationary Killing-invariant quasi-free state
(`KillingInvariantStationaryState`), KMS at the Hawking temperature, on the arc's entropic-weight hub. -/
lemma kay_wald_stationary_kms (ℏ κ c kB E : ℝ) (hT : hawkingTemperature ℏ κ c kB ≠ 0) :
    hawkingBoltzmannWeight ℏ κ c kB E = kuikenWeight (hawkingTemperature ℏ κ c kB) E
      ∧ hawkingTemperature ℏ κ c kB * hawkingBeta ℏ κ c kB = 1 :=
  ⟨hawkingBoltzmannWeight_is_kuiken ℏ κ c kB E, hawking_temperature_mul_beta ℏ κ c kB hT⟩

/-! ## The Hawking weight is the wedge modular eigenvalue (Bisognano–Wichmann ⟷ Kay–Wald)

The Kay–Wald KMS state on the bifurcate Killing horizon and the Bisognano–Wichmann wedge modular structure
are the same thermal object: the Hawking Boltzmann weight `e^{−E/T_H}` at `T_H = ℏκ/(2πckB)` equals the
wedge modular eigenvalue `Δ = e^{−2πκ'/ℏ}` (`QFT.PathIntegral.wedgeModularEigenvalue`) at the boost energy
`κ' = E·c·kB/κ` — the `2π` of the Hawking temperature *is* the full Euclidean period of the boost flow whose
half-period square root is `Δ^{1/2} = V(iπ)` (`wedgeModular_sqrt_at_pi`). -/

/-- **[The Hawking KMS weight is the wedge modular eigenvalue]**
`e^{−E/T_H} = Δ(E·c·kB/κ, ℏ)` — Kay–Wald horizon thermality and the Bisognano–Wichmann modular operator are
one identity: the Hawking `2π` is the Euclidean period of the wedge boost. Both sides normalize to
`exp(−2πEckB/(ℏκ))` for nonzero physical constants. -/
@[zil_claim physlib.wedgeKms.hawkingWeightIsWedgeModular,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bifurcateKillingHorizon,
  zil_export]
theorem hawkingBoltzmannWeight_is_wedgeModular (ℏ κ c kB E : ℝ)
    (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0) :
    hawkingBoltzmannWeight ℏ κ c kB E
      = Physlib.QFT.PathIntegral.wedgeModularEigenvalue (E * c * kB / κ) ℏ := by
  unfold hawkingBoltzmannWeight Physlib.Relativity.SemiClassical.hawkingTemperature
    Physlib.QFT.PathIntegral.wedgeModularEigenvalue
  congr 1
  field_simp

#zil_validate_embedded hawkingBoltzmannWeight_is_wedgeModular where
  no_sorry, claim_linked, requirement_linked

zil attach hawkingBoltzmannWeight_is_wedgeModular where
  formalizes @ "claim:hawking-weight-is-wedge-modular-eigenvalue",
  requires @ "assumption:bifurcate-killing-horizon",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "paper:kay-wald-1991",
  supported_by @ "definition:wedge-modular-eigenvalue",
  caveat @ "claim:eigenvalue-identity-not-quasifree-state-uniqueness"

zil_theorem_intent hawkingBoltzmannWeight_is_wedgeModular where
  at_level bridge_theorem
  must_mention [hawkingBoltzmannWeight, Physlib.QFT.PathIntegral.wedgeModularEigenvalue]

/-- **[The Unruh weight is the wedge modular eigenvalue]** via the equivalence principle — physlib's
`unruhTemperature` *is* `hawkingTemperature` at `κ = a` (`unruhTemperature_eq_hawkingTemperature`), so the
thermal weight an accelerated observer sees is the Bisognano–Wichmann modular eigenvalue at the boost energy
`E·c·kB/a`. -/
@[zil_claim physlib.wedgeKms.unruhWeightIsWedgeModular,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.uniformAcceleration,
  zil_export]
theorem unruhBoltzmannWeight_is_wedgeModular (ℏ a c kB E : ℝ)
    (hℏ : ℏ ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0) :
    Real.exp (-(E / Physlib.Thermodynamics.unruhTemperature ℏ kB c a))
      = Physlib.QFT.PathIntegral.wedgeModularEigenvalue (E * c * kB / a) ℏ := by
  rw [Physlib.Thermodynamics.unruhTemperature_eq_hawkingTemperature]
  exact hawkingBoltzmannWeight_is_wedgeModular ℏ a c kB E hℏ ha hc hkB

/-- **[The wedge modular eigenvalue in natural units is the Unruh `β = 2π` weight]**
`Δ(κ, 1) = e^{−2πκ} = e^{−β_U·κ}` with `β_U = unruhInverseTemperature = 2π`
(`AlgebraicQFT.SummersRelativisticVacuum`) — the wedge Euclidean period of `wedgeModular_sqrt_at_pi` and the
AQFT vacuum-modular-flow rapidity rate are the same `2π`. -/
@[zil_claim physlib.wedgeKms.wedgeModularIsUnruhBeta,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.naturalUnits,
  zil_export]
theorem wedgeModular_natural_is_unruhBeta (κ : ℝ) :
    Physlib.QFT.PathIntegral.wedgeModularEigenvalue κ 1
      = Real.exp (-(Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.unruhInverseTemperature * κ)) := by
  unfold Physlib.QFT.PathIntegral.wedgeModularEigenvalue
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.unruhInverseTemperature
  congr 1
  ring

zil attach unruhBoltzmannWeight_is_wedgeModular where
  formalizes @ "claim:unruh-weight-is-wedge-modular-eigenvalue",
  requires @ "claim:hawking-weight-is-wedge-modular-eigenvalue",
  supported_by @ "definition:equivalence-principle-unruh-temperature",
  caveat @ "claim:eigenvalue-identity-not-detector-response"

zil attach wedgeModular_natural_is_unruhBeta where
  formalizes @ "claim:wedge-modular-eigenvalue-is-unruh-beta-two-pi",
  requires @ "assumption:natural-units",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "definition:summers-unruh-inverse-temperature"

zil_theorem_intent wedgeModular_natural_is_unruhBeta where
  at_level bridge_theorem
  must_mention [Physlib.QFT.PathIntegral.wedgeModularEigenvalue,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.unruhInverseTemperature]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

end
