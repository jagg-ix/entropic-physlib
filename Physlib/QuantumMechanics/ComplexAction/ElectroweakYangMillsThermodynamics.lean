/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
public import Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks
public import Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex
public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
public import Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
public import Mathlib.Tactic

/-!
# Electroweak parameters from mixed `SU(2)` Yang-Mills thermodynamics

This module formalizes the theorem-level content extracted from

* J. Meinert and R. Hofmann, *Electroweak parameters from mixed `SU(2)`
  Yang-Mills Thermodynamics*, arXiv:2401.03243v2.

The paper proposes a thermodynamic model in which an electron-like droplet
contains two deconfining `SU(2)` Yang-Mills sectors, denoted there by
`SU(2)_CMB` and `SU(2)_e`.  The paper then compares the thermal mixing of
their Cartan sectors with the Standard-Model neutral mixing
`SU(2)_L × U(1)_Y`.

This file does **not** assert the numerical model as established physics.
Instead it extracts the precise conditional algebra that Lean can check:

* the paper's rotation matrix (Eq. 22) is the transpose/inverse convention of
  the existing `WeinbergAngle.neutralMixing`;
* the reduced-charge universality condition (Eq. 27) implies a tangent ratio;
* the mixed bulk-pressure condition (Eq. 31) with `P_bulk = 0` selects
  `sin² θ_W = -P_e/(P_CMB - P_e)`;
* the already-formalized electroweak identity
  `e = g sin θ_W = g' cos θ_W` is reused from `WeinbergAngle`;
* the natural-unit fine-structure constant is `α = q²/(4π)`;
* a thermodynamic Yang-Mills sector carries an existing
  `YangMillsPotentialEquation`, so gauge covariance is inherited from
  `YangMillsGaugeDynamics` rather than redefined here.


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics

open Matrix
open Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics


/-- The unquotiented Standard-Model gauge group already available in physlib. -/
abbrev StandardModelGaugeGroup := _root_.StandardModel.GaugeGroupI

/-- The existing Standard-Model gauge group supplies the `SU(2)` weak projection. -/
lemma standardModelGaugeGroup_toSU2 (G : StandardModelGaugeGroup) :
    _root_.StandardModel.GaugeGroupI.toSU2 G = G.2.1 := rfl

/-- The existing Standard-Model gauge group supplies the `U(1)` hypercharge projection. -/
lemma standardModelGaugeGroup_toU1 (G : StandardModelGaugeGroup) :
    _root_.StandardModel.GaugeGroupI.toU1 G = G.2.2 := rfl

/-- A thermodynamic Yang-Mills sector: the pressure/coupling data are added to
an already-existing Yang-Mills equation of motion. -/
structure ThermalYangMillsSector (X ι 𝔤 : Type*) [Fintype ι] [Ring 𝔤] where
  /-- Coordinate derivative used by the Yang-Mills equation. -/
  deriv : GaugePartial X ι 𝔤
  /-- Gauge connection/potential. -/
  connection : GaugePotential X ι 𝔤
  /-- Gauge current. -/
  current : GaugeCurrent X ι 𝔤
  /-- Thermodynamic pressure of the sector at the chosen temperature. -/
  pressure : ℝ
  /-- Effective thermal coupling of the Cartan mode. -/
  coupling : ℝ
  /-- The sector satisfies the existing Yang-Mills equation of motion. -/
  ym_eom : YangMillsPotentialEquation deriv connection current

/-- Gauge covariance of a thermodynamic sector is exactly the existing
Yang-Mills covariance theorem, with pressure/coupling data carried along but
not involved in the gauge equation. -/
lemma ThermalYangMillsSector.gaugeTransformed_eom
    {X ι 𝔤 : Type*} [Fintype ι] [Ring 𝔤]
    (S : ThermalYangMillsSector X ι 𝔤) (U Uinv : X → 𝔤)
    (hF : GaugeCurvatureCovariant S.deriv U Uinv S.connection)
    (hDiv : GaugeCovariantDivergence S.deriv U Uinv S.connection
      (yangMillsCurvature S.deriv S.connection)) :
    YangMillsPotentialEquation S.deriv
      (gaugeTransformPotential S.deriv U Uinv S.connection)
      (gaugeTransformCurrent U Uinv S.current) :=
  yangMillsPotentialEquation_gauge_covariant
    (deriv := S.deriv) (U := U) (Uinv := Uinv)
    (A := S.connection) (J := S.current) hF hDiv S.ym_eom


/-- The paper's Eq. (22) rotation convention:
`(f_CMB, f_e) ↦ [[cosθ,-sinθ],[sinθ,cosθ]] (f_CMB,f_e)`. -/
noncomputable def thermalGaugeTheoryMixing (g g' : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cosWeinberg g g', -sinWeinberg g g'; sinWeinberg g g', cosWeinberg g g']

/-- The thermal gauge-theory mixing matrix is the transpose convention of the
existing Standard-Model neutral mixing matrix. -/
lemma thermalGaugeTheoryMixing_eq_neutralMixing_transpose (g g' : ℝ) :
    thermalGaugeTheoryMixing g g' = (neutralMixing g g')ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [thermalGaugeTheoryMixing, neutralMixing]

/-- The thermal mixing rotation is orthogonal whenever the two couplings are
not simultaneously zero. -/
lemma thermalGaugeTheoryMixing_orthogonal (g g' : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    (thermalGaugeTheoryMixing g g')ᵀ * thermalGaugeTheoryMixing g g' = 1 := by
  have h := sinSq_add_cosSq g g' hS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thermalGaugeTheoryMixing, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply] <;>
    nlinarith [h]


/-- Reduced-charge universality in the form used by Eq. (27):
`q_CMB sinθ = q_e cosθ`. -/
def ReducedChargeUniversality (g g' qCMB qe : ℝ) : Prop :=
  qCMB * sinWeinberg g g' = qe * cosWeinberg g g'

/-- Eq. (27) implies the tangent-ratio relation
`tan θ_W = q_e/q_CMB`, provided the denominators are nonzero. -/
lemma tanWeinberg_eq_chargeRatio_of_universality
    (g g' qCMB qe : ℝ) (hS : 0 < g ^ 2 + g' ^ 2)
    (hq : qCMB ≠ 0) (hc : cosWeinberg g g' ≠ 0)
    (h : ReducedChargeUniversality g g' qCMB qe) :
    tanWeinberg g g' = qe / qCMB := by
  rw [tan_eq_sin_div_cos g g' hS]
  unfold ReducedChargeUniversality at h
  have hratio : sinWeinberg g g' / cosWeinberg g g' = qe / qCMB := by
    field_simp [hq, hc]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa using hratio

/-- The asymptotic value used in the paper after replacing the CMB-sector
effective coupling by its high-temperature limit, written as a reduced charge. -/
noncomputable def asymptoticCMBReducedCharge : ℝ := Real.sqrt (8 * Real.pi)

/-- In the asymptotic-CMB specialization, the existing Weinberg tangent is the
ratio displayed in Eq. (36). -/
lemma tanWeinberg_asymptoticCMB (eLam : ℝ) :
    tanWeinberg eLam asymptoticCMBReducedCharge = asymptoticCMBReducedCharge / eLam := rfl


/-- Paper Eq. (31): the mixed bulk pressure is the convex-linear expression
`(1 - w) P_e + w P_CMB`, with `w = sin² θ_W` in the application. -/
def mixedBulkPressure (w Pe PCMB : ℝ) : ℝ :=
  (1 - w) * Pe + w * PCMB

/-- Equivalent affine form of Eq. (31). -/
lemma mixedBulkPressure_eq_add_weight_gap (w Pe PCMB : ℝ) :
    mixedBulkPressure w Pe PCMB = Pe + w * (PCMB - Pe) := by
  unfold mixedBulkPressure
  ring

/-- The pressure-selected mixing weight. -/
noncomputable def selectedPressureWeight (Pe PCMB : ℝ) : ℝ :=
  -Pe / (PCMB - Pe)

/-- If `P_CMB ≠ P_e`, then `P_bulk = 0` is equivalent to the selected
pressure weight `w = -P_e/(P_CMB-P_e)`. -/
lemma mixedBulkPressure_eq_zero_iff_weight_eq
    {w Pe PCMB : ℝ} (hgap : PCMB - Pe ≠ 0) :
    mixedBulkPressure w Pe PCMB = 0 ↔ w = selectedPressureWeight Pe PCMB := by
  constructor
  · intro hzero
    rw [mixedBulkPressure_eq_add_weight_gap] at hzero
    have hmul : w * (PCMB - Pe) = -Pe := by linarith
    have hdiv : w * (PCMB - Pe) / (PCMB - Pe) = w := by field_simp [hgap]
    rw [← hdiv, hmul, selectedPressureWeight]
  · intro hw
    rw [mixedBulkPressure_eq_add_weight_gap, hw, selectedPressureWeight]
    field_simp [hgap]
    ring

/-- The square of `sin θ_W` is always an admissible pressure weight. -/
lemma sinWeinberg_sq_mem_unit_interval (g g' : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    0 ≤ sinWeinberg g g' ^ 2 ∧ sinWeinberg g g' ^ 2 ≤ 1 := by
  constructor
  · exact sq_nonneg (sinWeinberg g g')
  · have h := sinSq_add_cosSq g g' hS
    nlinarith [sq_nonneg (cosWeinberg g g')]

/-- A mixed `SU(2)` thermodynamic state carrying the precise data used to
select the Weinberg weight from bulk-pressure stability. -/
structure MixedSU2ThermodynamicState where
  /-- Coupling assigned to the `SU(2)_L`/CMB Cartan side. -/
  su2WeakCoupling : ℝ
  /-- Coupling assigned to the `U(1)_Y`/electron Cartan side. -/
  hyperchargeCoupling : ℝ
  /-- Pressure of the electron-sector deconfining phase. -/
  electronPressure : ℝ
  /-- Pressure of the CMB-sector deconfining phase. -/
  cmbPressure : ℝ
  /-- Bulk stability: the mixed bulk pressure vanishes. -/
  bulk_stable :
    mixedBulkPressure
      (sinWeinberg su2WeakCoupling hyperchargeCoupling ^ 2)
      electronPressure cmbPressure = 0

/-- Bulk stability selects exactly the Weinberg weight. -/
lemma MixedSU2ThermodynamicState.stability_selects_sinSq
    (S : MixedSU2ThermodynamicState)
    (hgap : S.cmbPressure - S.electronPressure ≠ 0) :
    sinWeinberg S.su2WeakCoupling S.hyperchargeCoupling ^ 2 =
      selectedPressureWeight S.electronPressure S.cmbPressure :=
  (mixedBulkPressure_eq_zero_iff_weight_eq hgap).mp S.bulk_stable

/-- The pressure-selected weight is physically admissible whenever the
coupling pair is nonzero. -/
lemma MixedSU2ThermodynamicState.selectedWeight_mem_unit_interval
    (S : MixedSU2ThermodynamicState)
    (hS : 0 < S.su2WeakCoupling ^ 2 + S.hyperchargeCoupling ^ 2)
    (hgap : S.cmbPressure - S.electronPressure ≠ 0) :
    0 ≤ selectedPressureWeight S.electronPressure S.cmbPressure
      ∧ selectedPressureWeight S.electronPressure S.cmbPressure ≤ 1 := by
  have hsel := S.stability_selects_sinSq hgap
  rw [← hsel]
  exact sinWeinberg_sq_mem_unit_interval S.su2WeakCoupling S.hyperchargeCoupling hS


/-- Natural-unit fine-structure constant `α = q²/(4π)`. -/
noncomputable def fineStructureConstant (q : ℝ) : ℝ :=
  q ^ 2 / (4 * Real.pi)

/-- `α` is nonnegative for real charge in natural units. -/
lemma fineStructureConstant_nonneg (q : ℝ) : 0 ≤ fineStructureConstant q := by
  unfold fineStructureConstant
  exact div_nonneg (sq_nonneg q) (by positivity)

/-- Existing electroweak charge identity in the paper's Eq. (2) form:
`e = g sinθ_W = g' cosθ_W`. -/
lemma electroweakCharge_eq_two_forms (g g' : ℝ) :
    g * sinWeinberg g g' = g' * cosWeinberg g g' := by
  simpa [electricCharge] using electricCharge_symm g g'

/-- Fine-structure constant from the existing electroweak electric charge. -/
lemma fineStructureConstant_electricCharge (g g' : ℝ) :
    fineStructureConstant (electricCharge g g') =
      (g * sinWeinberg g g') ^ 2 / (4 * Real.pi) := rfl

/-- The same `α` written in the hypercharge-coupling form using the existing
`electricCharge_symm` theorem. -/
lemma fineStructureConstant_electricCharge_hyperchargeForm (g g' : ℝ) :
    fineStructureConstant (electricCharge g g') =
      (g' * cosWeinberg g g') ^ 2 / (4 * Real.pi) := by
  simp [fineStructureConstant, electricCharge_symm]

/-- Mirror-charge factor appearing in Eq. (23), after the bulk average used in
the paper's droplet model. -/
noncomputable def mirrorChargeFactor : ℝ := 27 / 64

/-- Monopole-charge scale `4π/e(λ)`. -/
noncomputable def monopoleChargeScale (eLam : ℝ) : ℝ :=
  4 * Real.pi / eLam

/-- The paper's mixed droplet charge form from Eq. (23):
`q = -(27/64) (4π/e(λ₀)) cos θ_W`. -/
noncomputable def mixedDropletCharge (eLam g g' : ℝ) : ℝ :=
  -mirrorChargeFactor * monopoleChargeScale eLam * cosWeinberg g g'

/-- Eq. (45): the fine-structure constant of the mixed droplet charge is its
charge square divided by `4π`. -/
lemma mixedDroplet_fineStructure (eLam g g' : ℝ) :
    fineStructureConstant (mixedDropletCharge eLam g g') =
      mixedDropletCharge eLam g g' ^ 2 / (4 * Real.pi) := rfl

/-- A stable mixed thermodynamic state inherits the two electroweak charge
forms from the existing `WeinbergAngle` API. -/
lemma MixedSU2ThermodynamicState.electricCharge_forms
    (S : MixedSU2ThermodynamicState) :
    electricCharge S.su2WeakCoupling S.hyperchargeCoupling =
        S.su2WeakCoupling * sinWeinberg S.su2WeakCoupling S.hyperchargeCoupling
      ∧ electricCharge S.su2WeakCoupling S.hyperchargeCoupling =
        S.hyperchargeCoupling * cosWeinberg S.su2WeakCoupling S.hyperchargeCoupling := by
  constructor
  · rfl
  · exact electricCharge_symm S.su2WeakCoupling S.hyperchargeCoupling

/-- A stable mixed thermodynamic state also inherits
`1/e² = 1/g² + 1/g'²`. -/
lemma MixedSU2ThermodynamicState.inv_electricCharge_sq
    (S : MixedSU2ThermodynamicState)
    (hg : S.su2WeakCoupling ≠ 0) (hg' : S.hyperchargeCoupling ≠ 0)
    (hS : 0 < S.su2WeakCoupling ^ 2 + S.hyperchargeCoupling ^ 2) :
    1 / electricCharge S.su2WeakCoupling S.hyperchargeCoupling ^ 2 =
      1 / S.su2WeakCoupling ^ 2 + 1 / S.hyperchargeCoupling ^ 2 :=
  _root_.Physlib.QuantumMechanics.ComplexAction.WeinbergAngle.inv_electricCharge_sq
    S.su2WeakCoupling S.hyperchargeCoupling hg hg' hS


/-- Dimensionless Yang-Mills temperature `λ = 2πT/Λ`. -/
noncomputable def dimensionlessYangMillsTemperature (T Λ : ℝ) : ℝ :=
  2 * Real.pi * T / Λ

/-- Recover `T` from `λ = 2πT/Λ` when the Yang-Mills scale is nonzero. -/
lemma temperature_eq_of_dimensionlessYangMillsTemperature
    {T Λ : ℝ} (hΛ : Λ ≠ 0) :
    T = dimensionlessYangMillsTemperature T Λ * Λ / (2 * Real.pi) := by
  unfold dimensionlessYangMillsTemperature
  field_simp [hΛ, Real.pi_ne_zero]

/-- Weighted energy-density term in Eq. (50). -/
noncomputable def mixedEnergyDensityWeight
    (g g' κ ρe ρCMB : ℝ) : ℝ :=
  cosWeinberg g g' ^ 2 * ρe + κ ^ 4 * sinWeinberg g g' ^ 2 * ρCMB

/-- Coefficient of the radius variable `χ = r₀H∞(T₀)` in Eq. (50). -/
noncomputable def mixedRadiusCoefficient
    (g g' lambda0 κ ρe ρCMB : ℝ) : ℝ :=
  (64 * Real.pi ^ 3 / (3 * lambda0 ^ 4)) * mixedEnergyDensityWeight g g' κ ρe ρCMB

/-- The BPS-monopole contribution to the mixed mass formula in Eq. (50). -/
noncomputable def mixedMonopoleMassTerm (g g' eLam eCMB : ℝ) : ℝ :=
  cosWeinberg g g' * monopoleChargeScale eLam
    + sinWeinberg g g' * monopoleChargeScale eCMB

/-- Eq. (50) as an affine formula in `χ`. -/
noncomputable def mixedDropletMassOverH
    (g g' eLam eCMB lambda0 κ ρe ρCMB χ : ℝ) : ℝ :=
  mixedMonopoleMassTerm g g' eLam eCMB
    + mixedRadiusCoefficient g g' lambda0 κ ρe ρCMB * χ

/-- Solving the affine mass formula for the radius variable `χ`.  This is the
algebraic part behind extracting a droplet radius once the analytic/numerical
inputs of Eq. (50) are supplied. -/
lemma chi_eq_of_mixedDropletMassOverH
    {g g' eLam eCMB lambda0 κ ρe ρCMB χ M : ℝ}
    (hB : mixedRadiusCoefficient g g' lambda0 κ ρe ρCMB ≠ 0)
    (hM : M = mixedDropletMassOverH g g' eLam eCMB lambda0 κ ρe ρCMB χ) :
    χ =
      (M - mixedMonopoleMassTerm g g' eLam eCMB)
        / mixedRadiusCoefficient g g' lambda0 κ ρe ρCMB := by
  unfold mixedDropletMassOverH at hM
  have hmul :
      mixedRadiusCoefficient g g' lambda0 κ ρe ρCMB * χ =
        M - mixedMonopoleMassTerm g g' eLam eCMB := by
    linarith
  have hdiv :
      mixedRadiusCoefficient g g' lambda0 κ ρe ρCMB * χ
        / mixedRadiusCoefficient g g' lambda0 κ ρe ρCMB = χ := by
    field_simp [hB]
  rw [← hdiv, hmul]


/-- Main bridge theorem: assuming the mixed Yang-Mills bulk is stable and the
two pressures are distinct, the thermodynamic pressure equation selects the
same `sin² θ_W` that the existing electroweak API uses to define the electric
charge and fine-structure constant. -/
lemma mixedSU2_thermodynamic_electroweak_bridge
    (S : MixedSU2ThermodynamicState)
    (hgap : S.cmbPressure - S.electronPressure ≠ 0) :
    sinWeinberg S.su2WeakCoupling S.hyperchargeCoupling ^ 2 =
        selectedPressureWeight S.electronPressure S.cmbPressure
      ∧ electricCharge S.su2WeakCoupling S.hyperchargeCoupling =
        S.hyperchargeCoupling * cosWeinberg S.su2WeakCoupling S.hyperchargeCoupling
      ∧ fineStructureConstant
          (electricCharge S.su2WeakCoupling S.hyperchargeCoupling)
        =
          (S.hyperchargeCoupling
            * cosWeinberg S.su2WeakCoupling S.hyperchargeCoupling) ^ 2
            / (4 * Real.pi) :=
  ⟨S.stability_selects_sinSq hgap,
    electricCharge_symm S.su2WeakCoupling S.hyperchargeCoupling,
    fineStructureConstant_electricCharge_hyperchargeForm
      S.su2WeakCoupling S.hyperchargeCoupling⟩


/-- The W-mass module's `cosWeinberg` is definitionally the same expression as
the canonical `WeinbergAngle.cosWeinberg` used by this bridge. -/
lemma wMassModule_cosWeinberg_eq_repo_cosWeinberg (g g' : ℝ) :
    _root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.cosWeinberg
        g g'
      = cosWeinberg g g' := rfl

/-- The W-mass module's tree-level relation can be used with the canonical
`WeinbergAngle.cosWeinberg` from this file. -/
lemma wMass_eq_zMass_mul_repo_cosWeinberg
    (g g' v : ℝ) (h : 0 < g ^ 2 + g' ^ 2) :
    _root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass
        g v
      =
        _root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass
          g g' v * cosWeinberg g g' := by
  simpa [wMassModule_cosWeinberg_eq_repo_cosWeinberg] using
    _root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass_eq_zMass_mul_cosWeinberg
      g g' v h

/-- The stable mixed-state couplings feed the existing W/Z tree-level
`ρ = 1` relation.  The thermodynamic model supplies the same pair `(g,g')`
that the W-mass module uses in `M_W = M_Z cos θ_W`. -/
lemma MixedSU2ThermodynamicState.wMass_rhoParameter_eq_one
    (S : MixedSU2ThermodynamicState) (v : ℝ)
    (hg : 0 < S.su2WeakCoupling) (hg' : 0 < S.hyperchargeCoupling)
    (hv : 0 < v) :
    rhoParameter
      (_root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass
        S.su2WeakCoupling v)
      (_root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass
        S.su2WeakCoupling S.hyperchargeCoupling v)
      (cosWeinberg S.su2WeakCoupling S.hyperchargeCoupling) = 1 := by
  have hsum : 0 < S.su2WeakCoupling ^ 2 + S.hyperchargeCoupling ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt (S.su2WeakCoupling ^ 2 + S.hyperchargeCoupling ^ 2) :=
    Real.sqrt_pos.mpr hsum
  have hz :
      _root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass
        S.su2WeakCoupling S.hyperchargeCoupling v ≠ 0 := by
    unfold _root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass
    exact div_ne_zero (mul_ne_zero hsqrt.ne' hv.ne') two_ne_zero
  have hc : cosWeinberg S.su2WeakCoupling S.hyperchargeCoupling ≠ 0 := by
    unfold cosWeinberg
    exact div_ne_zero hg.ne' hsqrt.ne'
  exact rho_eq_one
    (_root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass
      S.su2WeakCoupling v)
    (_root_.Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass
      S.su2WeakCoupling S.hyperchargeCoupling v)
    (cosWeinberg S.su2WeakCoupling S.hyperchargeCoupling)
    hz hc (wMass_eq_zMass_mul_repo_cosWeinberg
      S.su2WeakCoupling S.hyperchargeCoupling v hsum)

/-- A stable mixed state links to the repo's gauge-boson classification and
the non-abelian weak three-vertex.  This is the precise repository link for
the paper's identification of the mixed `SU(2)` off-Cartan sector with the
weak sector. -/
lemma MixedSU2ThermodynamicState.links_gaugeBosonZoo_and_weakVertex
    (S : MixedSU2ThermodynamicState)
    (hgap : S.cmbPressure - S.electronPressure ≠ 0) :
    sinWeinberg S.su2WeakCoupling S.hyperchargeCoupling ^ 2 =
        selectedPressureWeight S.electronPressure S.cmbPressure
      ∧
        (Finset.univ.filter
          (fun b =>
            _root_.Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo.gaugeBosonForce b =
            _root_.Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo.Force.weak)).card =
          2 ^ 2 - 1
      ∧
        _root_.Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo.gaugeBosonCharge
          _root_.Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo.GaugeBoson.wPlus = 1
      ∧
        (_root_.Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex.weakVertex).c_s
          + (_root_.Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex.weakVertex).c_t
          + (_root_.Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex.weakVertex).c_u
            = 0 := by
  exact ⟨S.stability_selects_sinSq hgap,
    _root_.Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo.weak_boson_count,
    _root_.Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo.wPlus_charge,
    _root_.Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex.weakVertex.jacobi⟩

/-- Link the thermodynamic Weinberg-angle selection to the existing `SU(5)` /
Gell-Mann-Nishijima particle-charge bridge.  The first component is the new
thermodynamic selection; the second is the repo's already-proven lepton-doublet
charge splitting carried by `W⁺`. -/
lemma MixedSU2ThermodynamicState.links_su5_leptonChargeSplitting
    (S : MixedSU2ThermodynamicState)
    (hgap : S.cmbPressure - S.electronPressure ≠ 0) :
    sinWeinberg S.su2WeakCoupling S.hyperchargeCoupling ^ 2 =
        selectedPressureWeight S.electronPressure S.cmbPressure
      ∧
        _root_.Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor.su5AntifundCharge 4
          - _root_.Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor.su5AntifundCharge 3
        =
          _root_.Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.windingCharge 3 := by
  exact ⟨S.stability_selects_sinSq hgap,
    _root_.Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks.su5_leptonDoublet_splitting_eq_Wcharge⟩

/-- The existing Standard-Model Yukawa dimensional constraints, named here as
a proposition so mixed Yang-Mills thermodynamics can link to them without
redefining the Yukawa equations. -/
def repoStandardModelYukawaDimensionConstraints : Prop :=
  _root_.Physlib.Particles.StandardModel.YukawaDimensionalAnalysis.yukawaCouplingDim4 = 1
    ∧ _root_.Physlib.Particles.StandardModel.YukawaDimensionalAnalysis.yukawaCouplingDim4
        * _root_.Physlib.Particles.StandardModel.YukawaDimensionalAnalysis.higgsVEVDim4
      = _root_.Physlib.Particles.StandardModel.YukawaDimensionalAnalysis.massParameterDim4
    ∧ _root_.Physlib.Particles.StandardModel.YukawaDimensionalAnalysis.massParameterDim4
        / _root_.Physlib.Particles.StandardModel.YukawaDimensionalAnalysis.higgsVEVDim4 = 1

/-- The named Yukawa proposition is exactly the existing
`StandardModelYukawaCoupling` bundled theorem. -/
lemma repoStandardModelYukawaDimensionConstraints_holds :
    repoStandardModelYukawaDimensionConstraints :=
  _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling.standardModelYukawa_dimensional_requirements

/-- Link the mixed Yang-Mills/electroweak bridge to the Standard-Model Yukawa
dimension constraints: the thermodynamic construction selects the gauge angle,
while fermion masses remain in the existing Higgs/Yukawa sector. -/
lemma MixedSU2ThermodynamicState.links_standardModelYukawa_constraints
    (S : MixedSU2ThermodynamicState)
    (hgap : S.cmbPressure - S.electronPressure ≠ 0) :
    sinWeinberg S.su2WeakCoupling S.hyperchargeCoupling ^ 2 =
        selectedPressureWeight S.electronPressure S.cmbPressure
      ∧
        repoStandardModelYukawaDimensionConstraints := by
  exact ⟨S.stability_selects_sinSq hgap,
    repoStandardModelYukawaDimensionConstraints_holds⟩

end Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics

end
