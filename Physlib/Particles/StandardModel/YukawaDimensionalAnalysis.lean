/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.LTMCTIDimensionBase
public import Mathlib.Tactic.NormNum

/-!
# Dimensional analysis of Standard Model Yukawa terms

This file records the first derivation constraint for Standard Model Yukawa couplings:
in four spacetime dimensions, with natural-unit engineering dimensions,

* a Lagrangian density has mass dimension `4`;
* a scalar field, hence the Higgs field and its vacuum expectation value, has mass dimension `1`;
* a Dirac/Weyl fermion field has mass dimension `3 / 2`;
* therefore the Yukawa operator `bar psi * Phi * psi` already has mass dimension `4`;
* hence the Yukawa coefficient is forced to be dimensionless;
* after electroweak symmetry breaking, `y * v / sqrt 2` has mass dimension `1`;
* the physical Higgs-fermion coupling `m / v` is dimensionless.

This is only dimensional analysis.  It does not derive the numerical value of any Yukawa coupling, but it
does prove what any derivation must respect: `y_f` is a dimensionless scalar in the four-dimensional
Standard Model.

The last section records the consequence for the entropic/decoherence ansatz used elsewhere in the repo:
if `Gamma = y * omega0 / hbar` and `y` is the Standard Model Yukawa coupling, then `omega0 / hbar` must
carry the width dimension.  This is a constraint on what `omega0` is allowed to mean.


-/

set_option autoImplicit false

open Dimension.LTMCTI

@[expose] public section

namespace Physlib.Particles.StandardModel.YukawaDimensionalAnalysis

/-! ## Rational engineering mass dimensions in four spacetime dimensions -/

/-- Canonical QFT mass dimension, represented by its exponent. -/
abbrev QFTMassDim := ℚ

/-- In four spacetime dimensions, `[Lagrangian density] = 4`. -/
def lagrangianDensityMassDim4 : QFTMassDim := 4

/-- Derivatives carry mass dimension `1`. -/
def derivativeMassDim4 : QFTMassDim := 1

/-- A scalar field in four spacetime dimensions has mass dimension `1`. -/
def scalarFieldMassDim4 : QFTMassDim := 1

/-- The Higgs field has the scalar-field mass dimension. -/
def higgsFieldMassDim4 : QFTMassDim := scalarFieldMassDim4

/-- The Higgs vacuum expectation value has the same mass dimension as the Higgs field. -/
def higgsVEVMassDim4 : QFTMassDim := scalarFieldMassDim4

/-- A fermion field in four spacetime dimensions has mass dimension `3 / 2`. -/
def fermionFieldMassDim4 : QFTMassDim := 3 / 2

/-- The Dirac adjoint has the same engineering mass dimension as the fermion. -/
def adjointFermionFieldMassDim4 : QFTMassDim := fermionFieldMassDim4

/-- A mass parameter has mass dimension `1`. -/
def massParameterMassDim4 : QFTMassDim := 1

/-- A dimensionless coefficient has mass dimension `0`. -/
def dimensionlessMassDim4 : QFTMassDim := 0

/-- The bare Dirac bilinear `bar psi psi` has mass dimension `3`. -/
def diracBilinearMassDim4 : QFTMassDim :=
  adjointFermionFieldMassDim4 + fermionFieldMassDim4

lemma diracBilinearMassDim4_eq_three :
    diracBilinearMassDim4 = 3 := by
  norm_num [diracBilinearMassDim4, adjointFermionFieldMassDim4, fermionFieldMassDim4]

/-- Therefore the coefficient of `bar psi psi` must have mass dimension `1`. -/
def bareMassCoefficientMassDim4 : QFTMassDim :=
  lagrangianDensityMassDim4 - diracBilinearMassDim4

lemma bareMassCoefficientMassDim4_eq_mass :
    bareMassCoefficientMassDim4 = massParameterMassDim4 := by
  norm_num [bareMassCoefficientMassDim4, lagrangianDensityMassDim4, diracBilinearMassDim4,
    adjointFermionFieldMassDim4, fermionFieldMassDim4, massParameterMassDim4]

/-- The Standard Model Yukawa operator `bar psi * Phi * psi` has mass dimension `4`. -/
def yukawaOperatorMassDim4 : QFTMassDim :=
  adjointFermionFieldMassDim4 + higgsFieldMassDim4 + fermionFieldMassDim4

lemma yukawaOperatorMassDim4_eq_lagrangian :
    yukawaOperatorMassDim4 = lagrangianDensityMassDim4 := by
  norm_num [yukawaOperatorMassDim4, adjointFermionFieldMassDim4, fermionFieldMassDim4,
    higgsFieldMassDim4, scalarFieldMassDim4, lagrangianDensityMassDim4]

/-- The Yukawa coefficient's mass dimension is whatever is missing from the Lagrangian density. -/
def yukawaCouplingMassDim4 : QFTMassDim :=
  lagrangianDensityMassDim4 - yukawaOperatorMassDim4

/-- In the four-dimensional Standard Model, the Yukawa coupling is dimensionless. -/
lemma yukawaCouplingMassDim4_eq_zero :
    yukawaCouplingMassDim4 = dimensionlessMassDim4 := by
  norm_num [yukawaCouplingMassDim4, yukawaOperatorMassDim4, lagrangianDensityMassDim4,
    adjointFermionFieldMassDim4, fermionFieldMassDim4, higgsFieldMassDim4, scalarFieldMassDim4,
    dimensionlessMassDim4]

/-- After electroweak symmetry breaking, `y * v / sqrt 2` has mass dimension `1`. -/
def generatedFermionMassDim4 : QFTMassDim :=
  yukawaCouplingMassDim4 + higgsVEVMassDim4

lemma generatedFermionMassDim4_eq_mass :
    generatedFermionMassDim4 = massParameterMassDim4 := by
  norm_num [generatedFermionMassDim4, yukawaCouplingMassDim4, yukawaOperatorMassDim4,
    lagrangianDensityMassDim4, adjointFermionFieldMassDim4, fermionFieldMassDim4,
    higgsFieldMassDim4, higgsVEVMassDim4, scalarFieldMassDim4, massParameterMassDim4]

/-- The Higgs-fermion coupling `m / v` has mass dimension `0`. -/
def higgsFermionCouplingMassDim4 : QFTMassDim :=
  massParameterMassDim4 - higgsVEVMassDim4

lemma higgsFermionCouplingMassDim4_eq_zero :
    higgsFermionCouplingMassDim4 = dimensionlessMassDim4 := by
  norm_num [higgsFermionCouplingMassDim4, massParameterMassDim4, higgsVEVMassDim4,
    scalarFieldMassDim4, dimensionlessMassDim4]

/-- Matrix-valued Yukawa entries have the same dimension as scalar Yukawa couplings: none. -/
def yukawaMatrixEntryMassDim4 : QFTMassDim := yukawaCouplingMassDim4

/-- Each entry of `M = v Y / sqrt 2` has mass dimension `1`. -/
lemma yukawaMassMatrixEntryMassDim4_eq_mass :
    yukawaMatrixEntryMassDim4 + higgsVEVMassDim4 = massParameterMassDim4 := by
  norm_num [yukawaMatrixEntryMassDim4, yukawaCouplingMassDim4, yukawaOperatorMassDim4,
    lagrangianDensityMassDim4, adjointFermionFieldMassDim4, fermionFieldMassDim4,
    higgsFieldMassDim4, higgsVEVMassDim4, scalarFieldMassDim4, massParameterMassDim4]

/-! ## The same analysis as repo `Dimension LTMCTIDimensionBase` powers -/

/-- The repo `Dimension LTMCTIDimensionBase` carrier for a natural-unit QFT mass-dimension exponent. -/
def qftMassPower (q : ℚ) : Dimension LTMCTIDimensionBase := M𝓭 ^ q

lemma qftMassPower_mul (a b : ℚ) :
    qftMassPower a * qftMassPower b = qftMassPower (a + b) := by
  ext <;> norm_num [qftMassPower] <;> ring

lemma qftMassPower_div (a b : ℚ) :
    qftMassPower a / qftMassPower b = qftMassPower (a - b) := by
  ext <;> norm_num [qftMassPower] <;> ring

/-- The `Dimension LTMCTIDimensionBase` representative of a four-dimensional Lagrangian density, with mass dimension `4`. -/
def lagrangianDensityDim4 : Dimension LTMCTIDimensionBase := qftMassPower lagrangianDensityMassDim4

/-- The `Dimension LTMCTIDimensionBase` representative of a scalar field in four spacetime dimensions. -/
def scalarFieldDim4 : Dimension LTMCTIDimensionBase := qftMassPower scalarFieldMassDim4

/-- The `Dimension LTMCTIDimensionBase` representative of the Higgs field in four spacetime dimensions. -/
def higgsFieldDim4 : Dimension LTMCTIDimensionBase := qftMassPower higgsFieldMassDim4

/-- The `Dimension LTMCTIDimensionBase` representative of the Higgs vacuum expectation value. -/
def higgsVEVDim4 : Dimension LTMCTIDimensionBase := qftMassPower higgsVEVMassDim4

/-- The `Dimension LTMCTIDimensionBase` representative of a Dirac fermion field in four spacetime dimensions. -/
def fermionFieldDim4 : Dimension LTMCTIDimensionBase := qftMassPower fermionFieldMassDim4

/-- The `Dimension LTMCTIDimensionBase` representative of the adjoint Dirac fermion field. -/
def adjointFermionFieldDim4 : Dimension LTMCTIDimensionBase := qftMassPower adjointFermionFieldMassDim4

/-- The `Dimension LTMCTIDimensionBase` representative of a mass parameter. -/
def massParameterDim4 : Dimension LTMCTIDimensionBase := qftMassPower massParameterMassDim4

/-- The dimension of the Yukawa operator `bar psi Phi psi`. -/
def yukawaOperatorDim4 : Dimension LTMCTIDimensionBase :=
  adjointFermionFieldDim4 * higgsFieldDim4 * fermionFieldDim4

lemma yukawaOperatorDim4_eq_lagrangian :
    yukawaOperatorDim4 = lagrangianDensityDim4 := by
  ext <;> norm_num [yukawaOperatorDim4, adjointFermionFieldDim4, fermionFieldDim4,
    higgsFieldDim4, scalarFieldDim4, lagrangianDensityDim4, qftMassPower,
    adjointFermionFieldMassDim4, fermionFieldMassDim4, higgsFieldMassDim4,
    scalarFieldMassDim4, lagrangianDensityMassDim4] <;> ring

/-- The derived dimension of the Yukawa coefficient. -/
def yukawaCouplingDim4 : Dimension LTMCTIDimensionBase :=
  lagrangianDensityDim4 / yukawaOperatorDim4

/-- The Standard Model Yukawa coupling is dimensionless in the repo `Dimension LTMCTIDimensionBase` algebra. -/
lemma yukawaCouplingDim4_eq_one :
    yukawaCouplingDim4 = 1 := by
  ext <;> norm_num [yukawaCouplingDim4, lagrangianDensityDim4, yukawaOperatorDim4,
    adjointFermionFieldDim4, fermionFieldDim4, higgsFieldDim4, scalarFieldDim4, qftMassPower,
    lagrangianDensityMassDim4, adjointFermionFieldMassDim4, fermionFieldMassDim4,
    higgsFieldMassDim4, scalarFieldMassDim4] <;> ring

/-- The generated mass dimension `y * v` is the ordinary mass dimension. -/
lemma generatedFermionDim4_eq_mass :
    yukawaCouplingDim4 * higgsVEVDim4 = massParameterDim4 := by
  ext <;> norm_num [yukawaCouplingDim4, lagrangianDensityDim4, yukawaOperatorDim4,
    adjointFermionFieldDim4, fermionFieldDim4, higgsFieldDim4, higgsVEVDim4,
    scalarFieldDim4, qftMassPower, lagrangianDensityMassDim4, adjointFermionFieldMassDim4,
    fermionFieldMassDim4, higgsFieldMassDim4, higgsVEVMassDim4, scalarFieldMassDim4,
    massParameterDim4, massParameterMassDim4] <;> ring

/-- The Higgs-fermion coupling `m / v` is dimensionless. -/
lemma higgsFermionCouplingDim4_eq_one :
    massParameterDim4 / higgsVEVDim4 = 1 := by
  ext <;> norm_num [massParameterDim4, higgsVEVDim4, qftMassPower, massParameterMassDim4,
    higgsVEVMassDim4, scalarFieldMassDim4] <;> ring

/-! ## Constraint on the entropic/decoherence ansatz -/

/-- A decay width has mass dimension `1` in natural units. -/
def widthDim4 : Dimension LTMCTIDimensionBase := massParameterDim4

/-- The dimension of the entropic scale divided by `hbar` in an ansatz `Gamma = y * omega0 / hbar`. -/
def entropicScaleOverHbarDim4 (omega0Dim hbarDim : Dimension LTMCTIDimensionBase) : Dimension LTMCTIDimensionBase :=
  omega0Dim / hbarDim

/-- Since the Standard Model Yukawa coupling is dimensionless, the ansatz
`Gamma = y * omega0 / hbar` has the width dimension exactly when `omega0 / hbar` has width dimension. -/
lemma entropic_ansatz_dimensional_consistency_iff
    {omega0Dim hbarDim : Dimension LTMCTIDimensionBase} :
    yukawaCouplingDim4 * entropicScaleOverHbarDim4 omega0Dim hbarDim = widthDim4
      ↔ entropicScaleOverHbarDim4 omega0Dim hbarDim = widthDim4 := by
  rw [yukawaCouplingDim4_eq_one, one_mul]

/-- Since the Standard Model Yukawa coupling is dimensionless, the ansatz
`Gamma = y * omega0 / hbar` is dimensionally correct only if `omega0 / hbar` itself has width dimension. -/
lemma entropic_ansatz_requires_scale_over_hbar_width
    {omega0Dim hbarDim : Dimension LTMCTIDimensionBase}
    (hAnsatz : yukawaCouplingDim4 * entropicScaleOverHbarDim4 omega0Dim hbarDim = widthDim4) :
    entropicScaleOverHbarDim4 omega0Dim hbarDim = widthDim4 := by
  rw [yukawaCouplingDim4_eq_one, one_mul] at hAnsatz
  simpa using hAnsatz

/-- In natural units, where `hbar` is dimensionless and `omega0` is an energy/width scale, the ansatz
`Gamma = y * omega0 / hbar` is dimensionally consistent. -/
lemma entropic_ansatz_natural_units_consistent :
    yukawaCouplingDim4 * entropicScaleOverHbarDim4 widthDim4 1 = widthDim4 := by
  rw [yukawaCouplingDim4_eq_one]
  simp [entropicScaleOverHbarDim4]

end Physlib.Particles.StandardModel.YukawaDimensionalAnalysis

end
