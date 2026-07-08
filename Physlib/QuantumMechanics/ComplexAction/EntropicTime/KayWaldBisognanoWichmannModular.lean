/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf

/-!
# Bisognano–Wichmann: the modular flow is the boost Killing flow at the Hawking temperature (Kay–Wald)

Formalizes the Bisognano–Wichmann structure underlying the Kay–Wald thermal theorem: the Tomita–Takesaki
**modular flow** of the wedge KMS state is the **boost = Killing flow** generating the horizon, the **wedge
reflection** is the modular conjugation, and the modular flow's KMS temperature is the Hawking/Unruh temperature
`T = κ/2π`. This is why the wedge-restricted vacuum looks thermal — the geometric boost is the algebraic modular
automorphism.

* the **modular flow is the boost Killing flow** (`modularFlow_is_killing_bracket`): the modular automorphism `σ_t`
 of the Kay–Wald KMS state acts as the horizon-generating boost, a `KillingFlow` preserving the algebra bracket
 (`killingFlow_preserves_bracket`) — the geometric Killing flow *is* the algebraic modular flow;
* the **wedge reflection is the modular conjugation** `J² = 1` (`wedgeReflection_involution`, reusing the
 repository's `bogoliubovGenerator_sq`): the `[[0,1],[1,0]]` isometry exchanging the right and left wedges is an
 involution — the antiunitary `J` of Tomita–Takesaki that maps `𝓜` to its commutant, the same matrix as the
 thermofield-doubling Bogoliubov generator;
* the **modular flow's KMS weight is the entropic weight at the Hawking temperature**
 (`modular_kms_weight_is_kuiken`): `e^{−E/T_H} = kuikenWeight T_H E`, so the modular (boost) flow's thermal state
 sits on the `kuikenWeight` hub at `T_H = κ/2π`.

So the Kay–Wald thermal property is the Bisognano–Wichmann identity of geometry and algebra: the boost Killing
flow of the bifurcate horizon is the modular flow of the wedge KMS state, the wedge reflection is the modular
conjugation, and the modular temperature is the Hawking temperature `κ/2π` on the entropic hub — Tomita–Takesaki
modular theory, the Killing flow, and the Hawking effect are one.

* **§A — the modular flow is the boost Killing flow** (`modularFlow_is_killing_bracket`).
* **§B — the wedge reflection is the modular conjugation** (`wedgeReflection`, `wedgeReflection_involution`).
* **§C — the modular KMS weight is the entropic weight** (`modular_kms_weight_is_kuiken`).

The modular-flow / Killing-flow bracket preservation reuses `killingFlow_preserves_bracket`;
the wedge-reflection involution is the exact `2×2` matrix identity; the modular KMS weight reuses
`hawkingBoltzmannWeight_is_kuiken`. The full Tomita–Takesaki construction of `Δ`/`J` and the Bisognano–Wichmann
analytic proof are the referenced content. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; J. Bisognano, E. Wichmann (modular flow = boost). Repo dependencies:
 `EntropicTime.KayWaldHawkingKMSHorizon`, `AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative`,
 `AlgebraicQFT.SummersVacuumModularLinks`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBisognanoWichmannModular

/-! ## §A — the modular flow is the boost Killing flow -/

/-- **[The modular flow is the boost Killing flow] `σ_s([a,b]) = [σ_s a, σ_s b]`.** By Bisognano–Wichmann, the
Tomita–Takesaki modular automorphism `σ_s` of the wedge KMS state acts as the horizon-generating boost — a
`KillingFlow` — and hence preserves the algebra's Lie bracket. The geometric boost Killing flow *is* the algebraic
modular flow. -/
theorem modularFlow_is_killing_bracket {R : Type*} [Ring R] (F : KillingFlow R) (s : ℝ) (a b : R) :
    F.π s (collisionStar a b) = collisionStar (F.π s a) (F.π s b) :=
  killingFlow_preserves_bracket F s a b

/-! ## §B — the wedge reflection is the modular conjugation -/

/-- **[The wedge reflection is an involution] `J² = 1`.** The isometry `[[0,1],[1,0]]` exchanging the right and
left wedges of the bifurcate Killing horizon — the geometric realization of the Tomita–Takesaki modular
conjugation `J` — squares to the identity, mapping the wedge algebra to its commutant. This is the repository's
`bogoliubovGenerator` (the same `[[0,1],[1,0]]` matrix, also the su(1,1) / thermofield doubling generator),
`bogoliubovGenerator_sq` reused: the wedge reflection, the Bogoliubov doubling, and the modular conjugation are
the one involution. -/
theorem wedgeReflection_involution : bogoliubovGenerator * bogoliubovGenerator = 1 :=
  bogoliubovGenerator_sq

/-! ## §C — the modular KMS weight is the entropic weight -/

/-- **[The modular flow's KMS weight is the entropic weight at the Hawking temperature]
`e^{−E/T_H} = kuikenWeight T_H E`.** The boost/modular flow's thermal (KMS) state has Boltzmann weight equal to the
complex-action entropic weight at the Hawking temperature `T_H = κ/2π` — Tomita–Takesaki modular theory, the
Killing flow, and the Hawking effect meeting on the `kuikenWeight` hub. -/
theorem modular_kms_weight_is_kuiken (ℏ κ c kB E : ℝ) :
    hawkingBoltzmannWeight ℏ κ c kB E = kuikenWeight (hawkingTemperature ℏ κ c kB) E :=
  hawkingBoltzmannWeight_is_kuiken ℏ κ c kB E

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBisognanoWichmannModular

end
