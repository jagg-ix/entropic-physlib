/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumGravityCausalDiamond
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Physlib.Relativity.Special.HyperbolicBoost

/-!
# The Bogoliubov / diamond rapidity is PhysLean's standard special-relativity boost

Connects the complex-action/entropic-time rapidity machinery — `bogoliubovEnergy`, `thermoBogoliubov`, the causal-diamond
horizon energy `cosh η`, the one-loop determinant — to PhysLean's **standard special-relativity boost
infrastructure** (`Physlib.Relativity.Special.HyperbolicBoost`, `LorentzGroup.γ`), which the arc had
left floating.

The key identification: the arc's **Bogoliubov / diamond-horizon energy** `bogoliubovEnergy (sinh η) 1
= cosh η` is *exactly* PhysLean's **velocity-form Lorentz factor** `LorentzGroup.γ (tanh η)`
(`bogoliubovEnergy_eq_lorentzGamma`, via `Special.γ_tanh_eq_cosh`). So the entire rapidity arc — the
Bogoliubov energy, the diamond horizon, the one-loop QED determinant — is the standard Lorentz `γ`
factor, and `thermoBogoliubov` is the standard unimodular rapidity Lorentz boost.

* **§A — the Bogoliubov energy is the Lorentz `γ`-factor** (`bogoliubovEnergy_eq_lorentzGamma`).
* **§B — `thermoBogoliubov` is the standard rapidity Lorentz boost** (`thermoBogoliubov_det_one`,
  `rapidityBoost_preserves_minkowski`).
* **§C — the one-loop QED determinant is the standard Lorentz `γ`-factor**
  (`quantumGravity_det_eq_lorentzGamma`, `standardBoost_arc_bridge`).

So PhysLean's `HyperbolicBoost` / `LorentzGroup.γ` is no longer floating: it is the velocity-form face
of the arc's rapidity-form Bogoliubov / diamond / one-loop structure.

## References

* PhysLean: `Physlib.Relativity.Special.HyperbolicBoost` (`boostX`, `boostT`, `γ_tanh_eq_cosh`),
  `Physlib.Relativity.LorentzGroup.Boosts.Basic` (`LorentzGroup.γ`). Repo dependencies:
  `CausalDiamond.Helicity` (`diamond_horizon_energy`), `CausalDiamond.QuantumGravityCausalDiamond`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumGravityCausalDiamond
open Physlib.Relativity.Special

/-! ## §A — the Bogoliubov / diamond-horizon energy is the Lorentz `γ`-factor -/

/-- **[Bogoliubov energy = standard Lorentz `γ`-factor] `√(sinh²η + 1) = γ(tanh η)`.** The arc's
Bogoliubov quasiparticle / causal-diamond horizon energy `bogoliubovEnergy (sinh η) 1 = cosh η`
(`diamond_horizon_energy`) is *exactly* PhysLean's standard velocity-form Lorentz factor
`LorentzGroup.γ (tanh η) = 1/√(1 − tanh²η) = cosh η` (`Special.γ_tanh_eq_cosh`) at velocity
`β = tanh η`. The rapidity-form arc and the standard velocity-form special relativity are the same. -/
theorem bogoliubovEnergy_eq_lorentzGamma (η : ℝ) :
    bogoliubovEnergy (Real.sinh η) 1 = LorentzGroup.γ (Real.tanh η) := by
  rw [diamond_horizon_energy, ← γ_tanh_eq_cosh]

/-! ## §B — `thermoBogoliubov` is the standard rapidity Lorentz boost -/

/-- **[`thermoBogoliubov` is a proper Lorentz boost] `det U_B(η) = 1`.** The arc's Bogoliubov boost
`thermoBogoliubov η = [[cosh η, sinh η], [sinh η, cosh η]]` is unimodular (`cosh²η − sinh²η = 1`), a
proper `(1+1)`-dimensional Lorentz boost. -/
theorem thermoBogoliubov_det_one (η : ℝ) : (thermoBogoliubov η).det = 1 := by
  rw [thermoBogoliubov, Matrix.det_fin_two_of]
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

/-- **[The rapidity boost preserves the Minkowski interval] `(boostX)² − (boostT)² = x² − t²`.** The
standard PhysLean rapidity boost (`Special.boostX`/`Special.boostT`, the matrix form of
`thermoBogoliubov`) preserves the `(1+1)` Minkowski interval — the defining property of a Lorentz
transformation, the geometric content of the Bogoliubov unimodularity. -/
theorem rapidityBoost_preserves_minkowski (η x t : ℝ) :
    (boostX η x t) ^ 2 - (boostT η x t) ^ 2 = x ^ 2 - t ^ 2 := by
  simp only [boostX, boostT]
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

/-! ## §C — the one-loop QED determinant is the standard Lorentz `γ`-factor -/

/-- **[The QED one-loop determinant is the standard Lorentz `γ`-factor] `det[E_η] = γ(tanh η)`.** The
quantum-gravity path integral's one-loop fermion functional determinant of a rapidity-`η` Dirac mode
(`CausalDiamond.QuantumGravityCausalDiamond.quantumGravity_det_eq_horizon`, `= cosh η`) is PhysLean's standard
velocity-form Lorentz factor `LorentzGroup.γ (tanh η)`. The one-loop path integral, the causal-diamond
horizon, and the standard special-relativistic boost encode one and the same `γ`. -/
theorem quantumGravity_det_eq_lorentzGamma (η : ℝ) :
    berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = LorentzGroup.γ (Real.tanh η) := by
  rw [berezin_dirac_dispersion, bogoliubovEnergy_eq_lorentzGamma]

/-- **[Standard SR boost ↔ the rapidity arc, unified].** PhysLean's standard special-relativity boost
infrastructure is the velocity-form face of the arc's rapidity machinery: the Bogoliubov / diamond
horizon energy is the Lorentz `γ`-factor (`bogoliubovEnergy_eq_lorentzGamma`); `thermoBogoliubov` is a
proper unimodular Lorentz boost (`thermoBogoliubov_det_one`) preserving the Minkowski interval
(`rapidityBoost_preserves_minkowski`); and the one-loop QED determinant is the same `γ`-factor
(`quantumGravity_det_eq_lorentzGamma`). The standard `HyperbolicBoost` / `LorentzGroup.γ` is no longer
floating. -/
theorem standardBoost_arc_bridge (η x t : ℝ) :
    bogoliubovEnergy (Real.sinh η) 1 = LorentzGroup.γ (Real.tanh η)
      ∧ (thermoBogoliubov η).det = 1
      ∧ (boostX η x t) ^ 2 - (boostT η x t) ^ 2 = x ^ 2 - t ^ 2
      ∧ berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = LorentzGroup.γ (Real.tanh η) :=
  ⟨bogoliubovEnergy_eq_lorentzGamma η, thermoBogoliubov_det_one η,
    rapidityBoost_preserves_minkowski η x t, quantumGravity_det_eq_lorentzGamma η⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost

end
