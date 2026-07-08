/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
public import Physlib.Relativity.SL2C.Basic

/-!
# The Bogoliubov boost is an SL(2,ℂ) spinor transformation (the double cover)

Connects the arc's Bogoliubov boost to PhysLean's standard **spinor double cover**
`SL2C.toLorentzGroup : SL(2,ℂ) → LorentzGroup` (`Physlib.Relativity.SL2C.Basic`), which the arc had
left floating. The arc's real `2×2` Bogoliubov boost `thermoBogoliubov η` (det `= 1`) is an
`SL(2,ℂ)` element (`bogoSL2C`); under the standard double cover it maps to a Lorentz boost whose
time–time component is `cosh²η + sinh²η = cosh(2η)` — exactly the arc's **Bogoliubov energy at the
doubled rapidity** (`bogoSL2C_doubleCover_rapidity`), the hallmark **spinor factor of 2** of the
`SL(2,ℂ) → SO⁺(1,3)` cover (spinor rapidity `η` ↔ vector rapidity `2η`).

* **§A — the Bogoliubov boost as a spinor `SL(2,ℂ)` element** (`bogoSL2C`).
* **§B — the double cover** (`bogoSL2C_toLorentz_time`, `bogoSL2C_doubleCover_rapidity`): the image
  Lorentz boost's time component is the Bogoliubov energy at twice the rapidity.
* **§C — link to the one-loop determinant** (`bogoSL2C_doubleCover_eq_oneLoopDet`,
  `sl2c_doubleCover_bridge`): that time component is the one-loop QED fermion determinant at the
  vector rapidity `2η`.

So PhysLean's `SL2C.toLorentzGroup` double cover is no longer floating — it is the spinor cover of the
arc's Bogoliubov boost, with the characteristic rapidity-doubling into the Bogoliubov energy and
the one-loop path-integral determinant.

## References

* PhysLean: `Physlib.Relativity.SL2C.Basic` (`toLorentzGroup`, `toLorentzGroup_inl_inl`). Repo
  structures: `ThermoFieldDynamics.TFDImaginaryPart` (`thermoBogoliubov`), `CausalDiamond.Helicity`
  (`diamond_horizon_energy`), `PathIntegral.QEDFunctionalIntegralConstruction` (`berezin`, `fermionGaussian`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.SL2CDoubleCover

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open _root_.Lorentz

/-! ## §A — the Bogoliubov boost as a spinor `SL(2,ℂ)` element -/

/-- **[Bogoliubov boost as a spinor] `U_B(η) ∈ SL(2,ℂ)`.** The arc's real `2×2` Bogoliubov boost
`thermoBogoliubov η = [[cosh η, sinh η], [sinh η, cosh η]]`, complexified, is a special-linear
`SL(2,ℂ)` spinor transformation (`det = cosh²η − sinh²η = 1`). -/
noncomputable def bogoSL2C (η : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨(thermoBogoliubov η).map Complex.ofReal, by
    have hd : (thermoBogoliubov η).det = 1 := by
      rw [thermoBogoliubov, Matrix.det_fin_two_of]; nlinarith [Real.cosh_sq_sub_sinh_sq η]
    have h2 : ((thermoBogoliubov η).map Complex.ofReal).det
        = Complex.ofReal ((thermoBogoliubov η).det) :=
      (RingHom.map_det Complex.ofRealHom _).symm
    rw [h2, hd, Complex.ofReal_one]⟩

/-! ## §B — the spinor double cover -/

/-- **[Double-cover time component] `(Λ)₀₀ = cosh²η + sinh²η`.** Under PhysLean's standard spinor
double cover `SL2C.toLorentzGroup`, the Bogoliubov spinor `bogoSL2C η` maps to a Lorentz boost whose
time–time component is `(Σ ‖entries‖²)/2 = cosh²η + sinh²η` (`toLorentzGroup_inl_inl`). -/
theorem bogoSL2C_toLorentz_time (η : ℝ) :
    (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
      = Real.cosh η ^ 2 + Real.sinh η ^ 2 := by
  rw [SL2C.toLorentzGroup_inl_inl]
  simp only [bogoSL2C, thermoBogoliubov, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.empty_val', Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- **[Spinor double-cover rapidity doubling] `(Λ)₀₀ = E_{2η} = √(sinh²2η + 1)`.** The image Lorentz
boost's time component `cosh²η + sinh²η = cosh(2η)` is the arc's Bogoliubov energy
`bogoliubovEnergy (sinh 2η) 1` — the **spinor factor of 2** of the `SL(2,ℂ) → SO⁺(1,3)` cover: the
spinor rapidity `η` corresponds to the vector rapidity `2η`. -/
theorem bogoSL2C_doubleCover_rapidity (η : ℝ) :
    (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
      = bogoliubovEnergy (Real.sinh (2 * η)) 1 := by
  rw [bogoSL2C_toLorentz_time, diamond_horizon_energy, Real.cosh_two_mul]

/-! ## §C — link to the one-loop QED determinant -/

/-- **[Double cover ↔ one-loop determinant] `(Λ)₀₀ = det[E_{2η}]`.** The time component of the
double-cover Lorentz boost of the Bogoliubov spinor is the quantum-gravity one-loop fermion functional
determinant at the vector rapidity `2η` (`berezin_dirac_dispersion`). The spinor cover, the Lorentz
boost, the Bogoliubov energy, and the one-loop path integral coincide at the doubled rapidity. -/
theorem bogoSL2C_doubleCover_eq_oneLoopDet (η : ℝ) :
    (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
      = berezin (fermionGaussian (bogoliubovEnergy (Real.sinh (2 * η)) 1)) := by
  rw [bogoSL2C_doubleCover_rapidity]
  exact (berezin_dirac_dispersion _ _).symm

/-- **[SL(2,ℂ) double cover ↔ the Bogoliubov arc, unified].** The arc's Bogoliubov boost is a spinor
`SL(2,ℂ)` element; under PhysLean's standard double cover `SL2C.toLorentzGroup` it maps to a Lorentz
boost whose time component is the Bogoliubov energy at the **doubled** rapidity
(`bogoSL2C_doubleCover_rapidity`), which is the one-loop QED fermion determinant at vector rapidity `2η`
(`bogoSL2C_doubleCover_eq_oneLoopDet`). `SL2C.toLorentzGroup` is the spinor cover of the arc's boost. -/
theorem sl2c_doubleCover_bridge (η : ℝ) :
    (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
        = bogoliubovEnergy (Real.sinh (2 * η)) 1
      ∧ (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
          = berezin (fermionGaussian (bogoliubovEnergy (Real.sinh (2 * η)) 1)) :=
  ⟨bogoSL2C_doubleCover_rapidity η, bogoSL2C_doubleCover_eq_oneLoopDet η⟩

end Physlib.QuantumMechanics.ComplexAction.Hopf.SL2CDoubleCover

end
