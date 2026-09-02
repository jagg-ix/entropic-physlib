/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple

/-!
# The diamond velocity as the metric common root: equivalence principle ⇆ entropic time ⇆ complex action

The previous step recognized the diamond ratio `R/L = tanh(R_*/L)` as a **velocity**, from which the
equivalence principle followed (`CausalDiamond.EquivalencePrinciple`). This file connects that velocity
to the **`EntropicTime.MetricCommonRootEntropicTime`** structure and the **Nagao–Nielsen complex action**: the same
velocity `v = ξ/E = tanh(R_*/L)` is the *metric common root* of three faces of the arc.

* **Kinematic (gravity / equivalence principle)** — `v` is the Lorentz velocity, `γ = cosh(R_*/L)`,
  `γ²(1 − v²) = 1` (`CausalDiamond.EquivalencePrinciple.diamond_lorentzFactor_velocity`); the surface
  gravity `κ` is the proper acceleration (Unruh = Hawking).
* **Entropic (information)** — the same `v` gives the entropic proper time
  `τ_ent = binEntropy((1 − v)/2)` (`diamond_entropicTime_eq_velocity`, from
  `EntropicTime.MetricCommonRootEntropicTime.entropicTime_eq_binEntropy_velocity`); it vanishes iff `v = ±1`
  (luminal / static patch — the reversible point).
* **Complex action (dissipation)** — complexifying the gap `Δ = mc²` to the Nagao–Nielsen complex mass
  `m = m_R + i m_I`, the momentum Gaussian / complex-action weight converges iff `Im m > 0`
  (`diamond_complexAction_converges`), the entropic damping `e^{−S_I/ℏ}`.

So the diamond velocity `v = tanh(R_*/L)` is the single invariant tying together **acceleration /
gravity** (equivalence principle), **information** (entropic proper time), and **dissipation**
(complex-action convergence). The reversible / luminal point `v = ±1` (the de Sitter static patch) is
simultaneously `τ_ent = 0` and the `S_I = 0` boundary of complex-action convergence.

## References

* This development: `CausalDiamond.EquivalencePrinciple`, `CausalDiamond.Helicity`,
  `EntropicTime.MetricCommonRootEntropicTime`, `PathIntegral.MomentumPathIntegral` (Nagao–Nielsen complex action).


-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum
open Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval


/-- **The metric common root is universally a relativistic velocity** `m = ξ/E = tanh η` (for any
mode `(ξ, Δ)` with `Δ > 0`): the kinematic invariant of `EntropicTime.MetricCommonRootEntropicTime` is the boost
velocity `tanh` of a rapidity. This is the general theorem (`Rapidity.PoincarePolarMinkowskiInterval`,
`η = arsinh(ξ/Δ)`) that the causal diamond instantiates. -/
lemma metricVelocity_eq_tanh (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ η : ℝ, ξ / bogoliubovEnergy ξ Δ = Real.tanh η :=
  Rapidity.PoincarePolarMinkowskiInterval.velocity_eq_tanh ξ Δ hΔ

/-- **The metric velocity is the diamond velocity** `m = ξ/E = tanh(R_*/L) = R/L`: the kinematic
invariant of `EntropicTime.MetricCommonRootEntropicTime`, identical to the equivalence-principle velocity. Proved
*directly* — `bogoliubovEnergy(sinh η, 1) = cosh η` (the dispersion `cosh² = sinh² + 1`), so
`ξ/E = sinh η/cosh η = tanh η`. -/
lemma diamond_metric_velocity (η : ℝ) :
    Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = Real.tanh η := by
  rw [diamond_horizon_energy]
  exact (Real.tanh_eq_sinh_div_cosh η).symm

/-- **The diamond rapidity is canonically `R_*/L`**: the rapidity produced by the general construction
`η = arsinh(ξ/Δ)` (`exists_rapidity`) for the diamond mode `ξ = sinh(R_*/L)`, `Δ = 1` is *exactly*
`R_*/L` (since `arsinh ∘ sinh = id`). So the conformal-Killing-horizon coordinate `R_*/L` **is** the
Bogoliubov boost rapidity — the identification is canonical, not merely existential. -/
lemma diamond_rapidity_eq (η : ℝ) :
    Real.sinh η = 1 * Real.sinh (Real.arsinh (Real.sinh η / 1)) ∧
      Real.arsinh (Real.sinh η / 1) = η := by
  refine ⟨?_, ?_⟩
  · rw [div_one, Real.arsinh_sinh, one_mul]
  · rw [div_one, Real.arsinh_sinh]


/-- **The diamond's entropic proper time is `binEntropy((1 − v)/2)`** with `v = tanh(R_*/L) = R/L` the
equivalence-principle velocity (`EntropicTime.MetricCommonRootEntropicTime.entropicTime_eq_binEntropy_velocity`). The
*same* velocity that fixes the Lorentz factor `γ = cosh(R_*/L)` fixes the entropic proper time. -/
lemma diamond_entropicTime_eq_velocity (η : ℝ) :
    bogoliubovEntropicTime (Real.sinh η) 1 = Real.binEntropy ((1 - Real.tanh η) / 2) := by
  rw [entropicTime_eq_binEntropy_velocity, diamond_horizon_energy, ← Real.tanh_eq_sinh_div_cosh]

/-- **The kinematic and entropic invariants share the metric root** `v = tanh(R_*/L)`: the Lorentz
factor `γ = cosh(R_*/L)` (with `γ²(1 − v²) = 1`) and the entropic proper time `binEntropy((1 − v)/2)`
are both functions of the single velocity `v` — gravity and information meet at the metric common
root. -/
lemma diamond_kinematic_entropic_common_root (η : ℝ) :
    lorentzFactor η ^ 2 * (1 - Real.tanh η ^ 2) = 1
      ∧ bogoliubovEntropicTime (Real.sinh η) 1 = Real.binEntropy ((1 - Real.tanh η) / 2) :=
  ⟨diamond_lorentzFactor_velocity η, diamond_entropicTime_eq_velocity η⟩

/-- **The reversible point is the luminal / static-patch limit** `τ_ent = 0 ⟺ v = ±1`: the entropic
proper time vanishes exactly at `tanh(R_*/L) = ±1`, the de Sitter static patch (`R/L = ±1`). -/
lemma diamond_entropicTime_zero_iff_luminal (η : ℝ) :
    bogoliubovEntropicTime (Real.sinh η) 1 = 0 ↔ Real.tanh η = 1 ∨ Real.tanh η = -1 :=
  CausalDiamond.Helicity.diamond_entropicTime_zero_iff_luminal η


/-- **The diamond's complexified gap gives a convergent complex action iff `Im m > 0`**: complexifying
the rest gap `Δ = mc²` to the Nagao–Nielsen complex mass `m = m_R + i m_I`, the momentum Gaussian — the
complex-action / Feynman–Kac weight `e^{−S_I/ℏ}` — has positive real part exactly when `Im m > 0`
(`PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff`). The dissipative face of the metric root. -/
lemma diamond_complexAction_converges (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm


/-- **The metric common root unifies gravity, information, and dissipation.** For the diamond rapidity
`η = R_*/L` (velocity `v = tanh η`), complex mass `m ≠ 0`, and `ℏ, Δt > 0`:

* **(equivalence principle / gravity)** `γ = cosh η` is the Lorentz factor, `γ²(1 − v²) = 1`;
* **(entropic proper time / information)** `τ_ent = binEntropy((1 − v)/2)`;
* **(Nagao–Nielsen complex action / dissipation)** the complex-action weight converges iff `Im m > 0`.

All three are governed by the single metric common root `v = tanh(R_*/L) = ξ/E = R/L`. -/
lemma diamond_metric_common_root_link (η : ℝ) (m : ℂ) {ℏ dt : ℝ}
    (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    lorentzFactor η ^ 2 * (1 - Real.tanh η ^ 2) = 1
      ∧ bogoliubovEntropicTime (Real.sinh η) 1 = Real.binEntropy ((1 - Real.tanh η) / 2)
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im) :=
  ⟨diamond_lorentzFactor_velocity η, diamond_entropicTime_eq_velocity η,
   diamond_complexAction_converges m hℏ hdt hm⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot

end
