/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
public import Physlib.Relativity.LorentzAlgebra.Basis
public import Physlib.Relativity.LorentzGroup.Boosts.Basic

/-!
# The Bogoliubov boost is PhysLean's standard Lorentz boost (generator and group element)

Connects the arc's Bogoliubov boost — both the **generator** `bogoliubovGenerator` (`ThermoFieldDynamics.TFDBogoliubovHopf`)
and the **exponentiated** boost `thermoBogoliubov` — to PhysLean's standard **Lorentz boost generator**
(`lorentzAlgebra.boostGenerator`, `LorentzAlgebra/Basis`) and **explicit boost matrix**
(`LorentzGroup.boost`, `LorentzGroup/Boosts`), which the arc had left floating. Together with
`Lorentz.StandardLorentzBoost` this realizes the algebra→group exponential structure
(`boost = exp(generator)`, the role of `LorentzAlgebra/ExponentialMap`) concretely, without the
intractable `NormedSpace.exp` computation.

* **§A — the generator** (`bogoliubovGenerator_eq_boostGenerator_block`): the arc's `2×2` Bogoliubov
  boost generator `[[0,1],[1,0]]` is the `(t, xᵢ)` block of PhysLean's `𝔰𝔬(1,3)` boost generator
  `lorentzAlgebra.boostGenerator i`.
* **§B — the group element** (`boost_time_component_eq_bogoliubovEnergy`,
  `boost_time_component_eq_oneLoopDet`): the time–time component of PhysLean's explicit boost matrix
  `LorentzGroup.boost i (tanh η)` is `γ(tanh η) = cosh η = bogoliubovEnergy (sinh η) 1` — the arc's
  Bogoliubov energy / causal-diamond horizon energy / one-loop QED determinant.
* **§C — the synthesis** (`lorentzBoost_arc_bridge`): generator block + boost-matrix time component,
  the algebra and group faces of `boost = exp(η · generator)`.

So `lorentzAlgebra.boostGenerator` and `LorentzGroup.boost` are no longer floating — they are the
`𝔰𝔬(1,3)` / `SO⁺(1,3)` home of the arc's Bogoliubov boost.

## References

* PhysLean: `Physlib.Relativity.LorentzAlgebra.Basis` (`boostGenerator`),
  `Physlib.Relativity.LorentzGroup.Boosts.Basic` (`boost`, `γ`). Repo carriers: `ThermoFieldDynamics.TFDBogoliubovHopf`
  (`bogoliubovGenerator`), `Lorentz.StandardLorentzBoost`, `CausalDiamond.Helicity`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.BoostGenerator

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.Relativity.Special


/-- **[Bogoliubov generator = Lorentz boost generator block]** the arc's `2×2` Bogoliubov boost
generator `bogoliubovGenerator = [[0,1],[1,0]]` is exactly the `(t, xᵢ)` block of PhysLean's `𝔰𝔬(1,3)`
boost generator `lorentzAlgebra.boostGenerator i` (`1` at the `(0,i)` and `(i,0)` slots, `0` on the
diagonal). The arc's `K` is the standard Lorentz boost generator restricted to `(1+1)`. -/
lemma bogoliubovGenerator_eq_boostGenerator_block (i : Fin 3) :
    lorentzAlgebra.boostGenerator i (Sum.inl 0) (Sum.inl 0) = bogoliubovGenerator 0 0
      ∧ lorentzAlgebra.boostGenerator i (Sum.inl 0) (Sum.inr i) = bogoliubovGenerator 0 1
      ∧ lorentzAlgebra.boostGenerator i (Sum.inr i) (Sum.inl 0) = bogoliubovGenerator 1 0
      ∧ lorentzAlgebra.boostGenerator i (Sum.inr i) (Sum.inr i) = bogoliubovGenerator 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [lorentzAlgebra.boostGenerator, bogoliubovGenerator]


/-- **[Boost time–time component = Bogoliubov energy] `(Λ_β)₀₀ = γ(tanh η) = cosh η`.** The time–time
component of PhysLean's explicit Lorentz boost matrix `LorentzGroup.boost i (tanh η)` is the Lorentz
factor `γ(tanh η) = cosh η`, equal to the arc's Bogoliubov / causal-diamond horizon energy
`bogoliubovEnergy (sinh η) 1`. -/
lemma boost_time_component_eq_bogoliubovEnergy (i : Fin 3) (η : ℝ) (hβ : |Real.tanh η| < 1) :
    (LorentzGroup.boost i (Real.tanh η) hβ).1 (Sum.inl 0) (Sum.inl 0)
      = bogoliubovEnergy (Real.sinh η) 1 := by
  rw [diamond_horizon_energy, ← γ_tanh_eq_cosh]
  simp [LorentzGroup.boost]

/-- **[Boost time–time component = one-loop QED determinant]** the same time–time component of
PhysLean's boost matrix is the quantum-gravity one-loop fermion functional determinant
`berezin (fermionGaussian (E_η))` — the standard Lorentz boost and the one-loop path integral carry the
same `cosh η`. -/
lemma boost_time_component_eq_oneLoopDet (i : Fin 3) (η : ℝ) (hβ : |Real.tanh η| < 1) :
    (LorentzGroup.boost i (Real.tanh η) hβ).1 (Sum.inl 0) (Sum.inl 0)
      = berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) := by
  rw [boost_time_component_eq_bogoliubovEnergy, berezin_dirac_dispersion]


/-- **[Bogoliubov boost = PhysLean Lorentz boost, generator and group]** the arc's Bogoliubov boost is
PhysLean's standard Lorentz boost on both faces of `boost = exp(η · generator)`: the generator
`bogoliubovGenerator` is the `(t,xᵢ)` block of `lorentzAlgebra.boostGenerator i`
(`bogoliubovGenerator_eq_boostGenerator_block`), and the exponentiated boost matrix
`LorentzGroup.boost i (tanh η)` has time–time component the Bogoliubov energy `cosh η`, which is the
one-loop QED determinant (`boost_time_component_eq_oneLoopDet`). The standard
`lorentzAlgebra.boostGenerator` / `LorentzGroup.boost` are the `𝔰𝔬(1,3)` / `SO⁺(1,3)` home of the
arc's rapidity boost. -/
lemma lorentzBoost_arc_bridge (i : Fin 3) (η : ℝ) (hβ : |Real.tanh η| < 1) :
    lorentzAlgebra.boostGenerator i (Sum.inl 0) (Sum.inr i) = bogoliubovGenerator 0 1
      ∧ (LorentzGroup.boost i (Real.tanh η) hβ).1 (Sum.inl 0) (Sum.inl 0)
          = bogoliubovEnergy (Real.sinh η) 1
      ∧ (LorentzGroup.boost i (Real.tanh η) hβ).1 (Sum.inl 0) (Sum.inl 0)
          = berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) :=
  ⟨(bogoliubovGenerator_eq_boostGenerator_block i).2.1,
    boost_time_component_eq_bogoliubovEnergy i η hβ,
    boost_time_component_eq_oneLoopDet i η hβ⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.BoostGenerator

end
