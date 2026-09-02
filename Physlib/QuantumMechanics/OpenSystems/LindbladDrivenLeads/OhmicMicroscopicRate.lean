/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.Basic

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OhmicMicroscopicRate -/

/-!
# Finite-Ohmic coupling origin of the one-level LDDL rate

The one-level LDDL development uses a positive effective rate `γ`.  The existing
Caldeira--Leggett Ohmic-bath formalization already fixes a finite bath coupling
through

`c² = (4 γ / π) ω_cut³ S⁻¹`,

where `S` is the positive finite bath shape sum.  This module inverts that exact
relation:

`γ = π c² S / (4 ω_cut³)`.

It then transports the derived rate into the existing LDDL `RateData`, the exact
occupation vector field, the Lorentzian half-width/full-width, the
Caldeira--Leggett frequency-renormalization shift, the complex-saddle
coherence-width growth, and the strict binary-KL entropy-production rate.

The algebraic inversion and finite-bath cancellation are exact.  Identifying the
Caldeira--Leggett oscillator-bath coefficient with the effective Markovian LDDL
rate still requires a physical weak-coupling/Born--Markov/secular model bridge.
No observed transition, unit calibration, external dataset, or held-out result is
introduced here.
-/

set_option autoImplicit false

open scoped Real

@[expose] public section

noncomputable section

namespace QuantumMechanics.LindbladDrivenLeads

open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
open Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence

/-- Recover the dissipative rate from the squared finite-bath coupling, cutoff,
and positive Ohmic shape sum. -/
noncomputable def gammaFromOhmicCoupling
    (couplingStrengthSq cutoff shapeSum : ℝ) : ℝ :=
  Real.pi * couplingStrengthSq * shapeSum / (4 * cutoff ^ 3)

/-- `gammaFromOhmicCoupling` is an exact left inverse of the existing
Caldeira--Leggett finite-bath coupling law. -/
@[zil_level physical_theorem]
theorem gammaFromOhmicCoupling_couplingSq
    (gamma cutoff shapeSum : ℝ)
    (hcutoff : cutoff ≠ 0) (hshape : shapeSum ≠ 0) :
    gammaFromOhmicCoupling (couplingSq gamma cutoff shapeSum)
      cutoff shapeSum = gamma := by
  unfold gammaFromOhmicCoupling couplingSq
  field_simp [Real.pi_ne_zero, hcutoff, hshape]

/-- Finite Ohmic bath data sufficient to select an effective positive one-level
rate.  The shape sum is the exact one already used by the Caldeira--Leggett
finite-mode discretization. -/
structure FiniteOhmicBathRateData where
  /-- Squared microscopic bilinear coupling `c²`. -/
  couplingStrengthSq : ℝ
  /-- Positive bath cutoff `ω_cut`. -/
  cutoff : ℝ
  /-- Positive bath-size parameter `N_E`. -/
  bathSize : ℝ
  /-- Number of retained finite bath modes. -/
  modes : ℕ
  /-- Target one-level occupation. -/
  occupation : ℝ
  couplingStrengthSq_pos : 0 < couplingStrengthSq
  cutoff_pos : 0 < cutoff
  bathSize_pos : 0 < bathSize
  ohmicShapeSum_pos : 0 < ohmicShapeSum bathSize modes
  occupation_nonneg : 0 ≤ occupation
  occupation_le_one : occupation ≤ 1

namespace FiniteOhmicBathRateData

/-- The finite bath shape sum appearing in the coupling law. -/
noncomputable def shapeSum (b : FiniteOhmicBathRateData) : ℝ :=
  ohmicShapeSum b.bathSize b.modes

@[simp]
theorem shapeSum_pos (b : FiniteOhmicBathRateData) : 0 < b.shapeSum :=
  b.ohmicShapeSum_pos

/-- The rate selected by the finite Ohmic coupling law. -/
noncomputable def derivedGamma (b : FiniteOhmicBathRateData) : ℝ :=
  gammaFromOhmicCoupling b.couplingStrengthSq b.cutoff b.shapeSum

@[simp]
theorem derivedGamma_pos (b : FiniteOhmicBathRateData) :
    0 < b.derivedGamma := by
  have h1 := b.couplingStrengthSq_pos
  have h2 := b.cutoff_pos
  have h3 := b.ohmicShapeSum_pos
  unfold derivedGamma gammaFromOhmicCoupling
  positivity

/-- The derived rate reproduces the original squared microscopic coupling under
the exact finite-bath law. -/
@[zil_level physical_theorem]
theorem couplingSq_derivedGamma (b : FiniteOhmicBathRateData) :
    couplingSq b.derivedGamma b.cutoff b.shapeSum =
      b.couplingStrengthSq := by
  unfold derivedGamma gammaFromOhmicCoupling couplingSq shapeSum
  field_simp [Real.pi_ne_zero, b.cutoff_pos.ne',
    b.ohmicShapeSum_pos.ne']

/-- Construct the existing one-level rate carrier with `γ` no longer supplied as
an independent field. -/
noncomputable def toRateData (b : FiniteOhmicBathRateData) : RateData where
  gamma := b.derivedGamma
  occupation := b.occupation
  gamma_pos := b.derivedGamma_pos
  occupation_nonneg := b.occupation_nonneg
  occupation_le_one := b.occupation_le_one

@[simp]
theorem toRateData_gamma (b : FiniteOhmicBathRateData) :
    b.toRateData.gamma = b.derivedGamma := rfl

@[simp]
theorem toRateData_occupation (b : FiniteOhmicBathRateData) :
    b.toRateData.occupation = b.occupation := rfl

/-- The coefficient multiplying `(f-N)` in the exact occupation equation.  It is
also the Lorentzian full width at half maximum in the present convention. -/
noncomputable def relaxationCoefficient (b : FiniteOhmicBathRateData) : ℝ :=
  2 * b.derivedGamma

@[simp]
theorem relaxationCoefficient_pos (b : FiniteOhmicBathRateData) :
    0 < b.relaxationCoefficient := by
  have h := derivedGamma_pos b
  unfold relaxationCoefficient
  positivity

/-- Microscopic form of the occupation-relaxation coefficient. -/
@[zil_level physical_theorem]
theorem relaxationCoefficient_eq_coupling (b : FiniteOhmicBathRateData) :
    b.relaxationCoefficient =
      Real.pi * b.couplingStrengthSq * b.shapeSum /
        (2 * b.cutoff ^ 3) := by
  unfold relaxationCoefficient derivedGamma gammaFromOhmicCoupling
  field_simp [b.cutoff_pos.ne']
  ring

/-- The existing one-level vector field with the microscopic coefficient exposed. -/
@[zil_level physical_theorem]
theorem occupationVectorField_eq_microscopic
    (b : FiniteOhmicBathRateData) (n : ℝ) :
    occupationVectorField b.toRateData n =
      b.relaxationCoefficient * (b.occupation - n) := by
  simpa [relaxationCoefficient, toRateData] using
    occupationVectorField_eq b.toRateData n

/-- Exact finite-bath frequency-renormalization shift generated by the supplied
microscopic coupling. -/
noncomputable def renormalizationShift
    (b : FiniteOhmicBathRateData) : ℝ :=
  b.couplingStrengthSq *
    ohmicReciprocalSum b.cutoff b.bathSize b.modes

/-- The finite mode sum cancels exactly, leaving the standard closed Ohmic shift
`4 γ ω_cut / π`. -/
@[zil_level physical_theorem]
theorem renormalizationShift_eq_closed
    (b : FiniteOhmicBathRateData) :
    b.renormalizationShift =
      4 * b.derivedGamma * b.cutoff / Real.pi := by
  unfold renormalizationShift
  rw [← b.couplingSq_derivedGamma]
  simpa [shapeSum] using
    coupling_reciprocalSum_cancel b.derivedGamma b.cutoff b.bathSize
      b.modes b.cutoff_pos.ne' b.bathSize_pos
      b.ohmicShapeSum_pos.ne'

/-- Renormalized oscillator frequency written directly from the microscopic
coupling and then reduced to the closed Ohmic rate expression. -/
noncomputable def renormalizedFrequencySq
    (b : FiniteOhmicBathRateData) (bareFrequency : ℝ) : ℝ :=
  bareFrequency ^ 2 - b.renormalizationShift

@[zil_level physical_theorem]
theorem renormalizedFrequencySq_eq_closed
    (b : FiniteOhmicBathRateData) (bareFrequency : ℝ) :
    b.renormalizedFrequencySq bareFrequency =
      bareFrequency ^ 2 -
        4 * b.derivedGamma * b.cutoff / Real.pi := by
  rw [renormalizedFrequencySq, b.renormalizationShift_eq_closed]

/-! ## Lorentzian linewidth selected by the same microscopic rate -/

/-- Full width at half maximum of the LDDL Lorentzian in the convention
`γ / ((ω-ε)²+γ²)`. -/
noncomputable def lorentzianFWHM (b : FiniteOhmicBathRateData) : ℝ :=
  2 * b.derivedGamma

@[simp]
theorem lorentzianFWHM_eq_relaxationCoefficient
    (b : FiniteOhmicBathRateData) :
    b.lorentzianFWHM = b.relaxationCoefficient := rfl

@[simp]
theorem lorentzianFWHM_pos (b : FiniteOhmicBathRateData) :
    0 < b.lorentzianFWHM := by
  rw [b.lorentzianFWHM_eq_relaxationCoefficient]
  exact b.relaxationCoefficient_pos

/-- Peak value at resonance. -/
theorem lorentzPeak_at_resonance
    (b : FiniteOhmicBathRateData) (epsilon : ℝ) :
    lorentzPeak b.derivedGamma epsilon epsilon =
      1 / b.derivedGamma := by
  unfold lorentzPeak
  field_simp [b.derivedGamma_pos.ne']
  ring

/-- At one derived half-width from resonance the Lorentz peak is exactly half
its resonant value. -/
@[zil_level physical_theorem]
theorem lorentzPeak_at_halfWidth
    (b : FiniteOhmicBathRateData) (epsilon : ℝ) :
    lorentzPeak b.derivedGamma epsilon (epsilon + b.derivedGamma) =
      (1 / 2 : ℝ) * lorentzPeak b.derivedGamma epsilon epsilon := by
  rw [b.lorentzPeak_at_resonance]
  unfold lorentzPeak
  field_simp [b.derivedGamma_pos.ne']
  ring

/-- Microscopic coupling expression for the Lorentzian full width. -/
@[zil_level physical_theorem]
theorem lorentzianFWHM_eq_coupling
    (b : FiniteOhmicBathRateData) :
    b.lorentzianFWHM =
      Real.pi * b.couplingStrengthSq * b.shapeSum /
        (2 * b.cutoff ^ 3) := by
  rw [b.lorentzianFWHM_eq_relaxationCoefficient,
    b.relaxationCoefficient_eq_coupling]

/-! ## Decoherence and entropic-production consequences -/

/-- The Caldeira--Leggett off-diagonal decoherence exponent uses the same
microscopically selected damping coefficient. -/
@[zil_level physical_theorem]
theorem caldeiraLeggettDecoherence_eq_relaxationCoefficient
    (b : FiniteOhmicBathRateData)
    (mass boltzmann temperature time separation : ℝ) :
    caldeiraLeggettDecoherence mass b.derivedGamma boltzmann
        temperature time separation =
      mass * b.relaxationCoefficient * boltzmann *
        temperature * time * separation ^ 2 := by
  unfold caldeiraLeggettDecoherence relaxationCoefficient
  ring

/-- The complex-saddle linear coherence-width growth is four times the LDDL
relaxation coefficient divided by inverse temperature. -/
@[zil_level physical_theorem]
theorem gammaOffdiagLinear_eq_relaxationCoefficient
    (b : FiniteOhmicBathRateData) (beta time : ℝ) :
    gammaOffdiagLinear b.derivedGamma beta time =
      4 * b.relaxationCoefficient / beta * time := by
  unfold gammaOffdiagLinear relaxationCoefficient
  ring

/-- Fully expanded microscopic coupling form of the complex-saddle coherence
width. -/
@[zil_level physical_theorem]
theorem gammaOffdiagLinear_eq_coupling
    (b : FiniteOhmicBathRateData) (beta time : ℝ)
    (hbeta : beta ≠ 0) :
    gammaOffdiagLinear b.derivedGamma beta time =
      (2 * Real.pi * b.couplingStrengthSq * b.shapeSum /
          b.cutoff ^ 3) / beta * time := by
  unfold gammaOffdiagLinear derivedGamma gammaFromOhmicCoupling
  field_simp [b.cutoff_pos.ne', hbeta]
  ring

end FiniteOhmicBathRateData

end QuantumMechanics.LindbladDrivenLeads

/- ZIL-BEGIN -/

open QuantumMechanics.LindbladDrivenLeads

zil attach QuantumMechanics.LindbladDrivenLeads.gammaFromOhmicCoupling_couplingSq where
  formalizes @ "claim:the-finite-ohmic-caldeira-leggett-coupling-law-uniquely-recovers-the-effective-dissipative-rate-by-gamma-equals-pi-c-squared-shape-over-four-cutoff-cubed",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization.couplingSq",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "inversion",
  caveat @ "claim:this-inverts-the-declared-ohmic-coupling-law-it-does-not-derive-that-law-from-a-full-continuum-system-bath-hamiltonian"

zil attach QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.occupationVectorField_eq_microscopic where
  formalizes @ "claim:under-the-finite-ohmic-rate-identification-the-one-level-lddl-occupation-vector-field-has-a-relaxation-coefficient-fixed-by-the-microscopic-coupling-cutoff-and-bath-shape",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization.coupling_reciprocalSum_cancel",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.toRateData",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  requires @ "assumption:weak-coupling-born-markov-secular-identification-between-the-ohmic-oscillator-bath-and-the-effective-one-level-lddl-rate",
  caveat @ "claim:no-observed-transition-unit-calibration-or-held-out-relaxation-data-is-supplied"

zil attach QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.lorentzianFWHM_eq_coupling where
  formalizes @ "claim:the-one-level-lorentzian-full-width-at-half-maximum-is-pi-c-squared-shape-over-two-cutoff-cubed-under-the-same-ohmic-rate-identification",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.lorentzPeak_at_halfWidth",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-lddl-lorentzian-broadening-convention-applies-to-the-identified-physical-transition"

zil attach QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.renormalizationShift_eq_closed where
  formalizes @ "claim:the-finite-ohmic-bath-frequency-renormalization-shift-computed-from-the-microscopic-coupling-equals-four-gamma-cutoff-over-pi",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization.coupling_reciprocalSum_cancel",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.gammaOffdiagLinear_eq_coupling where
  formalizes @ "claim:the-complex-saddle-off-diagonal-decoherence-width-growth-can-be-written-directly-in-terms-of-the-finite-ohmic-microscopic-coupling-cutoff-shape-and-inverse-temperature",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence.gammaOffdiagLinear",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-caldeira-leggett-and-lddl-effective-gamma-conventions-identify-the-same-physical-dissipative-scale"

/- ZIL-END -/

/- Consolidated from Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.SpectralGoldenRuleRate -/

/-!
# On-shell spectral-density origin of one-level LDDL rates

This module adds the next layer between finite microscopic bath parameters and
the effective one-level Markov generator. In the standard weak-coupling,
Born--Markov and secular convention, an on-shell bath spectral weight `J` and a
squared system--bath coupling `g²` select

`γ_GR = 2 π g² J`.

The corresponding LDDL loss/gain rates are

`λ_loss = γ_GR (1-f)`, `λ_gain = γ_GR f`,

and the occupation equation is

`Ṅ = 4 π g² J (f-N)`.

For a thermal fermionic occupation `f = 1/(exp(βΔE)+1)`, the rates satisfy the
exact detailed-balance identity

`λ_gain = exp(-βΔE) λ_loss`.

Finally, the finite-Ohmic rate from `OhmicMicroscopicRate` is represented by the
effective on-shell spectral weight

`J_eff = shapeSum / (8 cutoff³)`,

for which `2π c² J_eff` is exactly the previously derived
`π c² shapeSum/(4 cutoff³)`.

The algebraic consequences are exact. The Fermi-golden-rule rate formula and
the weak-coupling/Born--Markov/secular reduction remain explicit physical model
premises; this module does not derive them from unitary continuum dynamics.
-/

set_option autoImplicit false

open scoped Real

@[expose] public section

noncomputable section

namespace QuantumMechanics.LindbladDrivenLeads

/-- Fermi--Dirac occupation written in terms of the dimensionless gap `β ΔE`. -/
noncomputable def fermiOccupation (betaEnergyGap : ℝ) : ℝ :=
  1 / (Real.exp betaEnergyGap + 1)

@[simp]
theorem fermiOccupation_pos (betaEnergyGap : ℝ) :
    0 < fermiOccupation betaEnergyGap := by
  unfold fermiOccupation
  exact div_pos zero_lt_one (by positivity)

@[simp]
theorem fermiOccupation_lt_one (betaEnergyGap : ℝ) :
    fermiOccupation betaEnergyGap < 1 := by
  unfold fermiOccupation
  rw [div_lt_one (by positivity : 0 < Real.exp betaEnergyGap + 1)]
  nlinarith [Real.exp_pos betaEnergyGap]

/-- Complementary thermal occupation. -/
theorem one_sub_fermiOccupation (betaEnergyGap : ℝ) :
    1 - fermiOccupation betaEnergyGap =
      Real.exp betaEnergyGap / (Real.exp betaEnergyGap + 1) := by
  have hden : Real.exp betaEnergyGap + 1 ≠ 0 := by positivity
  unfold fermiOccupation
  field_simp [hden]
  ring

/-- The Fermi occupation is the Boltzmann factor times its complement. -/
theorem fermiOccupation_eq_exp_neg_mul_complement (betaEnergyGap : ℝ) :
    fermiOccupation betaEnergyGap =
      Real.exp (-betaEnergyGap) * (1 - fermiOccupation betaEnergyGap) := by
  have hexp : Real.exp betaEnergyGap ≠ 0 := Real.exp_ne_zero _
  have hden : Real.exp betaEnergyGap + 1 ≠ 0 := by positivity
  rw [one_sub_fermiOccupation]
  unfold fermiOccupation
  rw [Real.exp_neg]
  field_simp [hexp, hden]

/-- Positive on-shell spectral data entering the secular golden-rule rate. -/
structure OnShellSpectralBathData where
  /-- Squared system--bath coupling `g²`. -/
  couplingStrengthSq : ℝ
  /-- Bath spectral weight at the transition frequency. -/
  onShellSpectralWeight : ℝ
  /-- Target occupation of the transition. -/
  occupation : ℝ
  couplingStrengthSq_pos : 0 < couplingStrengthSq
  onShellSpectralWeight_pos : 0 < onShellSpectralWeight
  occupation_nonneg : 0 ≤ occupation
  occupation_le_one : occupation ≤ 1

namespace OnShellSpectralBathData

/-- Golden-rule effective half-width/rate `γ_GR = 2π g² J`. -/
noncomputable def goldenRuleGamma (b : OnShellSpectralBathData) : ℝ :=
  2 * Real.pi * b.couplingStrengthSq * b.onShellSpectralWeight

@[simp]
theorem goldenRuleGamma_pos (b : OnShellSpectralBathData) :
    0 < b.goldenRuleGamma := by
  have h1 := b.couplingStrengthSq_pos
  have h2 := b.onShellSpectralWeight_pos
  unfold goldenRuleGamma
  positivity

/-- Existing one-level rate carrier selected by the on-shell spectral data. -/
noncomputable def toRateData (b : OnShellSpectralBathData) : RateData where
  gamma := b.goldenRuleGamma
  occupation := b.occupation
  gamma_pos := b.goldenRuleGamma_pos
  occupation_nonneg := b.occupation_nonneg
  occupation_le_one := b.occupation_le_one

@[simp]
theorem toRateData_gamma (b : OnShellSpectralBathData) :
    b.toRateData.gamma = b.goldenRuleGamma := rfl

@[simp]
theorem toRateData_occupation (b : OnShellSpectralBathData) :
    b.toRateData.occupation = b.occupation := rfl

/-- Loss channel in on-shell spectral form. -/
@[zil_level physical_theorem]
theorem lossRate_eq_goldenRule (b : OnShellSpectralBathData) :
    lossRate b.toRateData =
      (2 * Real.pi * b.couplingStrengthSq * b.onShellSpectralWeight) *
        (1 - b.occupation) := by
  rfl

/-- Gain channel in on-shell spectral form. -/
@[zil_level physical_theorem]
theorem gainRate_eq_goldenRule (b : OnShellSpectralBathData) :
    gainRate b.toRateData =
      (2 * Real.pi * b.couplingStrengthSq * b.onShellSpectralWeight) *
        b.occupation := by
  rfl

/-- The total LDDL rate is the golden-rule half-width. -/
@[zil_level physical_theorem]
theorem totalRate_eq_goldenRule (b : OnShellSpectralBathData) :
    totalRate b.toRateData =
      2 * Real.pi * b.couplingStrengthSq * b.onShellSpectralWeight := by
  simpa [goldenRuleGamma] using totalRate_eq_gamma b.toRateData

/-- The occupation relaxation coefficient is `4π g² J`. -/
@[zil_level physical_theorem]
theorem occupationVectorField_eq_goldenRule
    (b : OnShellSpectralBathData) (n : ℝ) :
    occupationVectorField b.toRateData n =
      (4 * Real.pi * b.couplingStrengthSq * b.onShellSpectralWeight) *
        (b.occupation - n) := by
  rw [occupationVectorField_eq]
  unfold toRateData goldenRuleGamma
  ring

/-- Lorentzian full width selected by the on-shell spectral weight. -/
noncomputable def lorentzianFWHM (b : OnShellSpectralBathData) : ℝ :=
  2 * b.goldenRuleGamma

@[zil_level physical_theorem]
theorem lorentzianFWHM_eq_goldenRule (b : OnShellSpectralBathData) :
    b.lorentzianFWHM =
      4 * Real.pi * b.couplingStrengthSq * b.onShellSpectralWeight := by
  unfold lorentzianFWHM goldenRuleGamma
  ring

end OnShellSpectralBathData

/-- Thermal on-shell spectral data with target occupation fixed by `βΔE`. -/
structure ThermalSpectralBathData where
  couplingStrengthSq : ℝ
  onShellSpectralWeight : ℝ
  betaEnergyGap : ℝ
  couplingStrengthSq_pos : 0 < couplingStrengthSq
  onShellSpectralWeight_pos : 0 < onShellSpectralWeight

namespace ThermalSpectralBathData

/-- Convert thermal spectral data to the generic rate carrier. -/
noncomputable def toOnShellSpectralBathData
    (b : ThermalSpectralBathData) : OnShellSpectralBathData where
  couplingStrengthSq := b.couplingStrengthSq
  onShellSpectralWeight := b.onShellSpectralWeight
  occupation := fermiOccupation b.betaEnergyGap
  couplingStrengthSq_pos := b.couplingStrengthSq_pos
  onShellSpectralWeight_pos := b.onShellSpectralWeight_pos
  occupation_nonneg := (fermiOccupation_pos b.betaEnergyGap).le
  occupation_le_one := (fermiOccupation_lt_one b.betaEnergyGap).le

/-- Thermal gain/loss detailed balance in the fermionic convention. -/
@[zil_level physical_theorem]
theorem gainRate_eq_exp_neg_mul_lossRate
    (b : ThermalSpectralBathData) :
    gainRate b.toOnShellSpectralBathData.toRateData =
      Real.exp (-b.betaEnergyGap) *
        lossRate b.toOnShellSpectralBathData.toRateData := by
  unfold gainRate lossRate
  rw [show b.toOnShellSpectralBathData.toRateData.occupation
        = fermiOccupation b.betaEnergyGap from rfl]
  conv_lhs => rw [fermiOccupation_eq_exp_neg_mul_complement b.betaEnergyGap]
  ring

end ThermalSpectralBathData

namespace FiniteOhmicBathRateData

/-- Effective on-shell spectral weight representing the finite-Ohmic coupling
law in the convention `γ_GR = 2π c² J`. -/
noncomputable def effectiveOnShellSpectralWeight
    (b : FiniteOhmicBathRateData) : ℝ :=
  b.shapeSum / (8 * b.cutoff ^ 3)

@[simp]
theorem effectiveOnShellSpectralWeight_pos
    (b : FiniteOhmicBathRateData) :
    0 < b.effectiveOnShellSpectralWeight := by
  have h := b.cutoff_pos
  unfold effectiveOnShellSpectralWeight
  exact div_pos b.shapeSum_pos (by positivity)

/-- The finite-Ohmic model as an on-shell spectral golden-rule carrier. -/
noncomputable def toOnShellSpectralBathData
    (b : FiniteOhmicBathRateData) : OnShellSpectralBathData where
  couplingStrengthSq := b.couplingStrengthSq
  onShellSpectralWeight := b.effectiveOnShellSpectralWeight
  occupation := b.occupation
  couplingStrengthSq_pos := b.couplingStrengthSq_pos
  onShellSpectralWeight_pos := b.effectiveOnShellSpectralWeight_pos
  occupation_nonneg := b.occupation_nonneg
  occupation_le_one := b.occupation_le_one

/-- The on-shell golden-rule rate exactly reproduces the finite-Ohmic coupling
inversion. -/
@[zil_level physical_theorem]
theorem goldenRuleGamma_eq_derivedGamma
    (b : FiniteOhmicBathRateData) :
    b.toOnShellSpectralBathData.goldenRuleGamma = b.derivedGamma := by
  unfold toOnShellSpectralBathData
    OnShellSpectralBathData.goldenRuleGamma
    effectiveOnShellSpectralWeight derivedGamma gammaFromOhmicCoupling
  field_simp [b.cutoff_pos.ne']
  ring

/-- The golden-rule occupation equation agrees with the finite-Ohmic microscopic
relaxation equation. -/
@[zil_level physical_theorem]
theorem occupationVectorField_eq_spectralOhmic
    (b : FiniteOhmicBathRateData) (n : ℝ) :
    occupationVectorField b.toOnShellSpectralBathData.toRateData n =
      b.relaxationCoefficient * (b.occupation - n) := by
  rw [OnShellSpectralBathData.occupationVectorField_eq_goldenRule]
  rw [show b.toOnShellSpectralBathData.couplingStrengthSq
        = b.couplingStrengthSq from rfl,
    show b.toOnShellSpectralBathData.onShellSpectralWeight
        = b.effectiveOnShellSpectralWeight from rfl,
    show b.toOnShellSpectralBathData.occupation = b.occupation from rfl]
  rw [show
    4 * Real.pi * b.couplingStrengthSq *
        b.effectiveOnShellSpectralWeight = b.relaxationCoefficient by
      unfold effectiveOnShellSpectralWeight relaxationCoefficient
        derivedGamma gammaFromOhmicCoupling
      field_simp [b.cutoff_pos.ne']
      ring]

/-- Golden-rule linewidth equals the finite-Ohmic linewidth. -/
@[zil_level physical_theorem]
theorem spectralFWHM_eq_ohmicFWHM
    (b : FiniteOhmicBathRateData) :
    b.toOnShellSpectralBathData.lorentzianFWHM = b.lorentzianFWHM := by
  unfold OnShellSpectralBathData.lorentzianFWHM
  rw [b.goldenRuleGamma_eq_derivedGamma]
  rfl

end FiniteOhmicBathRateData

end QuantumMechanics.LindbladDrivenLeads

/- ZIL-BEGIN -/

open QuantumMechanics.LindbladDrivenLeads

zil attach QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.totalRate_eq_goldenRule where
  formalizes @ "claim:under-the-secular-golden-rule-convention-the-one-level-total-rate-is-two-pi-times-coupling-squared-times-the-on-shell-bath-spectral-weight",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.toRateData",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  requires @ "assumption:weak-coupling-born-markov-secular-fermi-golden-rule-rate-formula",
  caveat @ "claim:the-rate-formula-is-a-declared-reduction-law-not-yet-derived-from-unitary-continuum-system-bath-dynamics"

zil attach QuantumMechanics.LindbladDrivenLeads.ThermalSpectralBathData.gainRate_eq_exp_neg_mul_lossRate where
  formalizes @ "claim:the-thermal-fermionic-one-level-gain-and-loss-rates-satisfy-exact-boltzmann-detailed-balance",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.fermiOccupation_eq_exp_neg_mul_complement",
  epistemic_status @ "conditional-model",
  requires @ "assumption:fermi-dirac-target-occupation-and-secular-golden-rule-channel-identification"

zil attach QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.goldenRuleGamma_eq_derivedGamma where
  formalizes @ "claim:the-finite-ohmic-coupling-derived-rate-is-exactly-the-secular-golden-rule-rate-for-effective-on-shell-spectral-weight-shape-over-eight-cutoff-cubed",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.gammaFromOhmicCoupling_couplingSq",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-identifies-two-effective-rate-parameterizations-and-does-not-prove-the-continuum-weak-coupling-limit"

zil attach QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.occupationVectorField_eq_spectralOhmic where
  formalizes @ "claim:the-on-shell-spectral-golden-rule-occupation-equation-agrees-exactly-with-the-finite-ohmic-microscopic-relaxation-equation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.occupationVectorField_eq_goldenRule",
  epistemic_status @ "conditional-model",
  requires @ "assumption:weak-coupling-born-markov-secular-reduction-and-effective-spectral-weight-identification",
  refines_toward @ "target:derive-the-secular-golden-rule-generator-from-continuum-bath-correlation-dynamics"

/- ZIL-END -/

