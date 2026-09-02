/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OhmicMicroscopicRate
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelPageWootters
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
meta import Zil

/-!
# Continuum bath correlation, Markovization, and secular reduction

This module completes three interfaces between the on-shell spectral-rate layer
and a genuine reduced-dynamics derivation.

1. `BathCorrelationTransformCertificate` records an integrable one-sided bath
   correlation transform, its positive on-shell spectral weight, and controlled
   finite-window convergence.
2. `VolterraMarkovApproximation` separates discarded-memory-tail error from the
   delayed-state replacement error and proves their additive bound.
3. `secularProjection` gives the exact finite-frequency resonant projection.
   `OneLevelWeakCouplingReductionCertificate` then composes memory and secular
   errors into a bound against the existing one-level LDDL vector field.

The projection and error-composition statements are theorems.  The final
sections instantiate them for a Gaussian continuum spectral bath: multiplication
by the spectral phase is a norm-preserving unitary group, its correlation is a
Gaussian characteristic function with an evaluated on-shell transform, and the
resulting one-level channel has an explicit Stinespring collision-bath realization.
On the Davies scale the reduced unitary channel converges (in this exactly
solvable realization, agrees away from zero coupling) with the existing CPTP
`C₀` semigroup whose right generator is the concrete loss/gain GKSL operator.

This constructive collision-reservoir theorem is not relabeled as the more
general Davies theorem for a fixed Hamiltonian `H₀ + λV` and one persistent
thermodynamic bath.  That Hamiltonian-domain/thermodynamic-limit result remains
a distinct stronger target.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped Real Interval InnerProductSpace

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement

@[expose] public section

noncomputable section

namespace QuantumMechanics.LindbladDrivenLeads

/-! ## A. One-sided continuum bath-correlation transform -/

/-- Integrable one-sided bath correlation and its on-shell transform.

The convention is

`Ĉ(ω₀) = ∫_{[0,∞)} exp(i ω₀ t) C(t) dt`,

with `Re Ĉ(ω₀) = 2π J(ω₀)`. -/
structure BathCorrelationTransformCertificate where
  correlation : ℝ → ℂ
  transitionFrequency : ℝ
  transform : ℂ
  truncatedTransform : ℝ → ℂ
  spectralWeight : ℝ
  integrable_modulated : IntegrableOn
    (fun t : ℝ =>
      Complex.exp (Complex.I * ((transitionFrequency * t : ℝ) : ℂ)) * correlation t)
    (Ici 0)
  transform_integral :
    transform = ∫ t in Ici (0 : ℝ),
      Complex.exp (Complex.I * ((transitionFrequency * t : ℝ) : ℂ)) * correlation t
  transform_real_eq : transform.re = 2 * Real.pi * spectralWeight
  spectralWeight_pos : 0 < spectralWeight
  truncationError : ℝ → ℝ
  truncationError_nonneg : ∀ T, 0 ≤ T → 0 ≤ truncationError T
  truncation_bound : ∀ T, 0 ≤ T →
    ‖transform - truncatedTransform T‖ ≤ truncationError T
  truncationError_tendsto_zero : Tendsto truncationError atTop (𝓝 0)

namespace BathCorrelationTransformCertificate

noncomputable def modulatedCorrelation
    (b : BathCorrelationTransformCertificate) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((b.transitionFrequency * t : ℝ) : ℂ)) *
    b.correlation t

theorem transform_eq_integral (b : BathCorrelationTransformCertificate) :
    b.transform = ∫ t in Ici (0 : ℝ), b.modulatedCorrelation t := by
  simpa [modulatedCorrelation] using b.transform_integral

/-- Independent coupling and occupation data convert the continuum transform to
the existing on-shell spectral-rate carrier. -/
noncomputable def toOnShellSpectralBathData
    (b : BathCorrelationTransformCertificate)
    (couplingStrengthSq occupation : ℝ)
    (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) :
    OnShellSpectralBathData where
  couplingStrengthSq := couplingStrengthSq
  onShellSpectralWeight := b.spectralWeight
  occupation := occupation
  couplingStrengthSq_pos := hc
  onShellSpectralWeight_pos := b.spectralWeight_pos
  occupation_nonneg := hf0
  occupation_le_one := hf1

/-- The golden-rule half-width is coupling squared times the real continuum
correlation transform. -/
@[zil_level physical_theorem]
theorem goldenRuleGamma_eq_coupling_mul_transform_re
    (b : BathCorrelationTransformCertificate)
    (couplingStrengthSq occupation : ℝ)
    (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) :
    (b.toOnShellSpectralBathData couplingStrengthSq occupation hc hf0 hf1).goldenRuleGamma =
      couplingStrengthSq * b.transform.re := by
  unfold toOnShellSpectralBathData OnShellSpectralBathData.goldenRuleGamma
  rw [b.transform_real_eq]
  ring

/-- Every nonnegative finite window inherits the certified transform bound. -/
theorem truncatedTransform_error
    (b : BathCorrelationTransformCertificate) (T : ℝ) (hT : 0 ≤ T) :
    ‖b.transform - b.truncatedTransform T‖ ≤ b.truncationError T :=
  b.truncation_bound T hT

end BathCorrelationTransformCertificate

/-! ## A.1. Concrete Gaussian continuum spectral bath -/

/-- A continuum bath whose energy spectral measure is Gaussian, centered at
the system transition frequency, with positive on-shell weight. -/
structure GaussianContinuumBath where
  transitionFrequency : ℝ
  spectralWeight : ℝ
  spectralWeight_pos : 0 < spectralWeight

namespace GaussianContinuumBath

/-- Variance `2π` fixes the Gaussian correlation so its positive-time integral
is exactly one half before the `4πJ` normalization. -/
def variance : NNReal := ⟨2 * Real.pi, by positivity⟩

/-- The concrete continuum energy law of the bath. -/
def spectralMeasure (b : GaussianContinuumBath) : Measure ℝ :=
  gaussianReal b.transitionFrequency variance

/-- Spectral phase `exp(-i t ω)` at energy `ω`. -/
def phase (t omega : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (((t * omega : ℝ) : ℂ)))

/-- Pointwise spectral evolution on continuum bath wavefunctions. -/
def unitaryEvolution (t : ℝ) (psi : ℝ → ℂ) : ℝ → ℂ :=
  fun omega => phase t omega * psi omega

@[simp]
theorem phase_norm (t omega : ℝ) : ‖phase t omega‖ = 1 := by
  simp [phase, Complex.norm_exp]

@[simp]
theorem unitaryEvolution_zero (psi : ℝ → ℂ) :
    unitaryEvolution 0 psi = psi := by
  funext omega
  simp [unitaryEvolution, phase]

/-- The spectral evolution composes at additive times. -/
theorem unitaryEvolution_add (s t : ℝ) (psi : ℝ → ℂ) :
    unitaryEvolution (s + t) psi = unitaryEvolution s (unitaryEvolution t psi) := by
  funext omega
  simp only [unitaryEvolution, phase]
  rw [← mul_assoc]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp]
theorem unitaryEvolution_pointwise_norm (t omega : ℝ) (psi : ℝ → ℂ) :
    ‖unitaryEvolution t psi omega‖ = ‖psi omega‖ := by
  simp [unitaryEvolution]

/-- Evolution by time `-t` is the inverse of evolution by `t`. -/
theorem unitaryEvolution_inverse (t : ℝ) (psi : ℝ → ℂ) :
    unitaryEvolution (-t) (unitaryEvolution t psi) = psi := by
  rw [← unitaryEvolution_add]
  simp

/-- The pointwise phase evolution preserves the continuum `L²` energy exactly,
written without choosing representatives in the `Lp` quotient. -/
theorem unitaryEvolution_lintegral_normSq (b : GaussianContinuumBath)
    (t : ℝ) (psi : ℝ → ℂ) :
    ∫⁻ omega, ENNReal.ofReal (‖unitaryEvolution t psi omega‖ ^ 2) ∂b.spectralMeasure =
      ∫⁻ omega, ENNReal.ofReal (‖psi omega‖ ^ 2) ∂b.spectralMeasure := by
  apply lintegral_congr
  intro omega
  rw [unitaryEvolution_pointwise_norm]

/-! ## A.2. Persistent continuum-bath Hilbert evolution -/

/-- The Gaussian continuum bath as the repository's existing measurable real-energy
Schrödinger model.  Its carrier is the genuine spectral Hilbert space
`L²(ℝ, gaussianReal ω₀ 2π; ℂ)` and its Hamiltonian is multiplication by energy. -/
noncomputable def persistentBathModel (b : GaussianContinuumBath) :
    InteractingFunctionalModel ℝ where
  μ := b.spectralMeasure
  hbar := 1
  hbar_pos := one_pos
  freeEnergy := id
  interactionEnergy := 0
  measurable_freeEnergy := measurable_id
  measurable_interactionEnergy := measurable_const

@[simp] lemma persistentBathModel_totalEnergy (b : GaussianContinuumBath) (omega : ℝ) :
    b.persistentBathModel.totalEnergy omega = omega := by
  simp [persistentBathModel, InteractingFunctionalModel.totalEnergy]

/-- The generic measurable-energy Schrödinger phase is exactly the spectral phase used
in the bath correlation. -/
@[simp] lemma persistentBathModel_phase (b : GaussianContinuumBath) (t omega : ℝ) :
    b.persistentBathModel.phase t omega = phase t omega := by
  simp [persistentBathModel, InteractingFunctionalModel.phase,
    InteractingFunctionalModel.totalEnergy, phase]

/-- The actual infinite-dimensional Hilbert carrier of the persistent Gaussian bath. -/
noncomputable abbrev PersistentBathHilbert (b : GaussianContinuumBath) :=
  b.persistentBathModel.Hilbert

/-- The fixed Gaussian bath Hamiltonian generates a bundled unitary `C₀` group on its
spectral `L²` carrier.  This reuses the general diagonal Schrödinger construction. -/
noncomputable def persistentBathC0Group (b : GaussianContinuumBath) :
    ComplexC0Semigroup (K := b.PersistentBathHilbert) :=
  b.persistentBathModel.evolutionC0Group

/-- The bundled operator acts almost everywhere by the original spectral phase. -/
lemma persistentBathC0Group_apply_ae (b : GaussianContinuumBath)
    (t : ℝ) (psi : b.PersistentBathHilbert) :
    b.persistentBathC0Group.operator t psi =ᵐ[b.spectralMeasure]
      fun omega => phase t omega * psi omega := by
  change b.persistentBathModel.evolution t psi =ᵐ[b.spectralMeasure]
    fun omega => phase t omega * psi omega
  filter_upwards [b.persistentBathModel.evolution_coeFn t psi] with omega h
  rw [h, b.persistentBathModel_phase]

/-- Every time slice of the persistent bath group is an exact `L²` isometry. -/
@[zil_level physical_theorem]
lemma persistentBathC0Group_norm (b : GaussianContinuumBath)
    (t : ℝ) (psi : b.PersistentBathHilbert) :
    ‖b.persistentBathC0Group.operator t psi‖ = ‖psi‖ := by
  exact b.persistentBathModel.norm_evolution t psi

/-- The normalized constant vector selecting the Gaussian bath vacuum correlation. -/
noncomputable def vacuum (b : GaussianContinuumBath) : b.PersistentBathHilbert := by
  letI : IsProbabilityMeasure b.spectralMeasure := by
    unfold spectralMeasure
    infer_instance
  exact (memLp_const (μ := b.spectralMeasure) (1 : ℂ)).toLp
    (fun _ : ℝ => (1 : ℂ))

lemma vacuum_coeFn (b : GaussianContinuumBath) :
    b.vacuum =ᵐ[b.spectralMeasure] fun _ : ℝ => (1 : ℂ) := by
  unfold vacuum
  exact MemLp.coeFn_toLp _

/-- The characteristic function used in the rate derivation is an actual matrix
coefficient of the persistent unitary continuum-bath evolution. -/
@[zil_level bridge_theorem]
theorem vacuum_matrixCoefficient (b : GaussianContinuumBath) (t : ℝ) :
    ⟪b.vacuum, b.persistentBathC0Group.operator t b.vacuum⟫_ℂ =
      charFun b.spectralMeasure (-t) := by
  rw [MeasureTheory.L2.inner_def, charFun_apply_real]
  apply integral_congr_ae
  filter_upwards [b.vacuum_coeFn,
    b.persistentBathC0Group_apply_ae t b.vacuum] with omega hv he
  rw [hv, he, hv]
  simp only [RCLike.inner_apply, phase]
  simp
  congr 1
  ring

/-- The constant Gaussian vacuum vector is normalized because the spectral law is a
probability measure. -/
@[zil_level physical_theorem]
theorem norm_vacuum (b : GaussianContinuumBath) : ‖b.vacuum‖ = 1 := by
  letI : IsProbabilityMeasure b.spectralMeasure := by
    unfold spectralMeasure
    infer_instance
  have hinner : ⟪b.vacuum, b.vacuum⟫_ℂ = 1 := by
    calc
      ⟪b.vacuum, b.vacuum⟫_ℂ =
          ⟪b.vacuum, b.persistentBathC0Group.operator 0 b.vacuum⟫_ℂ := by
        rw [b.persistentBathC0Group.operator_zero]
        rfl
      _ = charFun b.spectralMeasure 0 := by
        simpa using b.vacuum_matrixCoefficient 0
      _ = 1 := by rw [charFun_apply_real]; simp
  have hsq : ‖b.vacuum‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    norm_num
  rw [sq_eq_one_iff] at hsq
  rcases hsq with h | h
  · exact h
  · nlinarith [norm_nonneg b.vacuum]

/-- The vacuum correlation is the spectral-unitary matrix coefficient under
the Gaussian continuum energy law. -/
def correlation (b : GaussianContinuumBath) (t : ℝ) : ℂ :=
  ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
    charFun (b.spectralMeasure) (-t)

/-- The bath correlation is an actual normalized-vacuum matrix coefficient of the
fixed persistent continuum unitary group, with the model's `4πJ` normalization. -/
@[zil_level bridge_theorem]
theorem correlation_eq_vacuum_matrixCoefficient (b : GaussianContinuumBath) (t : ℝ) :
    b.correlation t = ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
      ⟪b.vacuum, b.persistentBathC0Group.operator t b.vacuum⟫_ℂ := by
  rw [correlation, b.vacuum_matrixCoefficient]

/-- The correlation is literally the continuum integral of the unitary phase. -/
@[zil_level bridge_theorem]
theorem correlation_eq_spectralIntegral (b : GaussianContinuumBath) (t : ℝ) :
    b.correlation t = ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
      ∫ omega, phase t omega ∂b.spectralMeasure := by
  rw [correlation, charFun_apply_real]
  congr 2
  funext omega
  simp only [phase]
  congr 1
  push_cast
  ring

/-- The system-frequency-modulated bath correlation. -/
def modulatedCorrelation (b : GaussianContinuumBath) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((b.transitionFrequency * t : ℝ) : ℂ)) *
    b.correlation t

/-- Centering the Gaussian bath at the transition cancels the oscillatory
phase and leaves the real Gaussian mixing envelope. -/
theorem modulatedCorrelation_eq (b : GaussianContinuumBath) (t : ℝ) :
    b.modulatedCorrelation t =
      ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
        Complex.exp ((-(Real.pi * t ^ 2) : ℝ) : ℂ) := by
  rw [modulatedCorrelation, correlation]
  rw [show charFun b.spectralMeasure (-t) =
      Complex.exp (((-t : ℝ) : ℂ) * (b.transitionFrequency : ℂ) * Complex.I -
        (((variance : NNReal) : ℝ) : ℂ) * ((-t : ℝ) : ℂ) ^ 2 / 2) by
    simpa [spectralMeasure] using
      (charFun_gaussianReal (μ := b.transitionFrequency) (v := variance) (-t))]
  calc
    _ = ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((b.transitionFrequency * t : ℝ) : ℂ)) *
          Complex.exp (((-t : ℝ) : ℂ) * (b.transitionFrequency : ℂ) * Complex.I -
            (((variance : NNReal) : ℝ) : ℂ) * ((-t : ℝ) : ℂ) ^ 2 / 2)) := by ring
    _ = ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((b.transitionFrequency * t : ℝ) : ℂ) +
            (((-t : ℝ) : ℂ) * (b.transitionFrequency : ℂ) * Complex.I -
              (((variance : NNReal) : ℝ) : ℂ) * ((-t : ℝ) : ℂ) ^ 2 / 2)) := by
          rw [Complex.exp_add]
    _ = _ := by
      congr 2
      rw [show ((((variance : NNReal) : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) by
        norm_cast]
      push_cast
      ring

/-- The modulated Gaussian correlation is integrable on positive time. -/
theorem integrable_modulatedCorrelation (b : GaussianContinuumBath) :
    IntegrableOn b.modulatedCorrelation (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply Integrable.congr
    (Integrable.const_mul
      (integrable_cexp_neg_mul_sq
        (show 0 < (Real.pi : ℂ).re by simpa using Real.pi_pos))
      ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) |>.integrableOn)
  filter_upwards with t
  rw [b.modulatedCorrelation_eq]
  congr 2
  push_cast
  ring

/-- The evaluated positive-time on-shell transform `2πJ`. -/
def transform (b : GaussianContinuumBath) : ℂ :=
  ((2 * Real.pi * b.spectralWeight : ℝ) : ℂ)

/-- Finite-time window approximation to the correlation transform. -/
def truncatedTransform (b : GaussianContinuumBath) (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, b.modulatedCorrelation t

/-- Actual transform truncation error, rather than an independently supplied
majorant. -/
def truncationError (b : GaussianContinuumBath) (T : ℝ) : ℝ :=
  ‖b.transform - b.truncatedTransform T‖

/-- The Gaussian half-line integral evaluates the continuum transform exactly. -/
@[zil_level physical_theorem]
theorem transform_integral (b : GaussianContinuumBath) :
    b.transform = ∫ t in Ici (0 : ℝ), b.modulatedCorrelation t := by
  rw [integral_Ici_eq_integral_Ioi]
  rw [integral_congr_ae (Filter.Eventually.of_forall b.modulatedCorrelation_eq)]
  rw [integral_const_mul]
  rw [show (fun t : ℝ => Complex.exp ((-(Real.pi * t ^ 2) : ℝ) : ℂ)) =
      (fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2)) by
    funext t
    congr 1
    push_cast
    ring]
  rw [integral_gaussian_complex_Ioi
    (show 0 < (Real.pi : ℂ).re by simpa using Real.pi_pos)]
  simp [transform]
  ring

/-- Finite windows converge to the evaluated transform. -/
theorem truncatedTransform_tendsto (b : GaussianContinuumBath) :
    Tendsto b.truncatedTransform atTop (𝓝 b.transform) := by
  rw [b.transform_integral, integral_Ici_eq_integral_Ioi]
  have hint : IntegrableOn b.modulatedCorrelation (Ioi 0) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    exact b.integrable_modulatedCorrelation
  exact intervalIntegral_tendsto_integral_Ioi 0
    hint tendsto_id

/-- The actual finite-window truncation error vanishes. -/
@[zil_level bridge_theorem]
theorem truncationError_tendsto_zero (b : GaussianContinuumBath) :
    Tendsto b.truncationError atTop (𝓝 0) := by
  unfold truncationError
  have hconst : Tendsto (fun _ : ℝ => b.transform) atTop (nhds b.transform) :=
    tendsto_const_nhds
  simpa using (hconst.sub b.truncatedTransform_tendsto).norm

/-- Persistent-bath capstone: the Gaussian energy law supplies a normalized vacuum on a
genuine continuum spectral Hilbert space, a fixed unitary `C₀` group, its exact vacuum
correlation, and the evaluated on-shell positive-time transform. -/
@[zil_level bridge_theorem]
theorem persistentBath_unitaryCorrelationTransform (b : GaussianContinuumBath) :
    ‖b.vacuum‖ = 1 ∧
      (∀ s t, b.persistentBathC0Group.operator (s + t) =
        (b.persistentBathC0Group.operator s).comp
          (b.persistentBathC0Group.operator t)) ∧
      (∀ psi, Continuous fun t => b.persistentBathC0Group.operator t psi) ∧
      (∀ t psi, ‖b.persistentBathC0Group.operator t psi‖ = ‖psi‖) ∧
      (∀ t, b.correlation t =
        ((4 * Real.pi * b.spectralWeight : ℝ) : ℂ) *
          ⟪b.vacuum, b.persistentBathC0Group.operator t b.vacuum⟫_ℂ) ∧
      b.transform = ∫ t in Ici (0 : ℝ), b.modulatedCorrelation t := by
  exact ⟨b.norm_vacuum,
    b.persistentBathC0Group.operator_add,
    b.persistentBathC0Group.strong_continuous,
    b.persistentBathC0Group_norm,
    b.correlation_eq_vacuum_matrixCoefficient,
    b.transform_integral⟩

/-- The Gaussian spectral bath instantiates every field of the generic
correlation-transform certificate. -/
noncomputable def toCertificate (b : GaussianContinuumBath) :
    BathCorrelationTransformCertificate where
  correlation := b.correlation
  transitionFrequency := b.transitionFrequency
  transform := b.transform
  truncatedTransform := b.truncatedTransform
  spectralWeight := b.spectralWeight
  integrable_modulated := by
    change IntegrableOn b.modulatedCorrelation (Ici 0)
    exact b.integrable_modulatedCorrelation
  transform_integral := by
    change b.transform = ∫ t in Ici (0 : ℝ), b.modulatedCorrelation t
    exact b.transform_integral
  transform_real_eq := by simp [transform]
  spectralWeight_pos := b.spectralWeight_pos
  truncationError := b.truncationError
  truncationError_nonneg := fun _ _ => norm_nonneg _
  truncation_bound := fun _ _ => le_rfl
  truncationError_tendsto_zero := b.truncationError_tendsto_zero

/-- Independent system coupling and occupation turn the concrete bath into the
existing on-shell spectral data. -/
noncomputable def toOnShellData (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) : OnShellSpectralBathData :=
  b.toCertificate.toOnShellSpectralBathData couplingStrengthSq occupation hc hf0 hf1

/-- The concrete one-level rate selected by the Gaussian bath transform. -/
noncomputable def toRateData (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) : RateData :=
  (b.toOnShellData couplingStrengthSq occupation hc hf0 hf1).toRateData

end GaussianContinuumBath

/-! ## B. Volterra-memory to local-Markov replacement -/

/-- Two-stage approximation of a nonlocal memory term by a local Markov term. -/
structure VolterraMarkovApproximation (E : Type*) [NormedAddCommGroup E] where
  memoryTerm : ℝ → E
  truncatedMemoryTerm : ℝ → E
  markovTerm : ℝ → E
  tailError : ℝ → ℝ
  stateReplacementError : ℝ → ℝ
  tailError_nonneg : ∀ t, 0 ≤ t → 0 ≤ tailError t
  stateReplacementError_nonneg : ∀ t, 0 ≤ t → 0 ≤ stateReplacementError t
  tail_bound : ∀ t, 0 ≤ t →
    ‖memoryTerm t - truncatedMemoryTerm t‖ ≤ tailError t
  state_replacement_bound : ∀ t, 0 ≤ t →
    ‖truncatedMemoryTerm t - markovTerm t‖ ≤ stateReplacementError t

namespace VolterraMarkovApproximation

def totalError {E : Type*} [NormedAddCommGroup E]
    (c : VolterraMarkovApproximation E) (t : ℝ) : ℝ :=
  c.tailError t + c.stateReplacementError t

/-- Tail and delayed-state replacement errors add. -/
@[zil_level physical_theorem]
theorem memory_markov_bound
    {E : Type*} [NormedAddCommGroup E]
    (c : VolterraMarkovApproximation E) (t : ℝ) (ht : 0 ≤ t) :
    ‖c.memoryTerm t - c.markovTerm t‖ ≤ c.totalError t := by
  calc
    ‖c.memoryTerm t - c.markovTerm t‖ ≤
        ‖c.memoryTerm t - c.truncatedMemoryTerm t‖ +
          ‖c.truncatedMemoryTerm t - c.markovTerm t‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ c.tailError t + c.stateReplacementError t :=
      add_le_add (c.tail_bound t ht) (c.state_replacement_bound t ht)
    _ = c.totalError t := rfl

/-- Zero component errors force exact Markovization at that time. -/
theorem memoryTerm_eq_markovTerm_of_zero_errors
    {E : Type*} [NormedAddCommGroup E]
    (c : VolterraMarkovApproximation E) (t : ℝ) (ht : 0 ≤ t)
    (htail : c.tailError t = 0)
    (hstate : c.stateReplacementError t = 0) :
    c.memoryTerm t = c.markovTerm t := by
  have h := c.memory_markov_bound t ht
  rw [totalError, htail, hstate, add_zero] at h
  have hz : ‖c.memoryTerm t - c.markovTerm t‖ = 0 :=
    le_antisymm h (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end VolterraMarkovApproximation

/-! ## C. Finite-frequency secular projection -/

/-- Retain exactly the coefficient pairs with equal Bohr frequency. -/
noncomputable def secularProjection
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι) : ℂ :=
  if frequency i = frequency j then coefficient i j else 0

noncomputable def nonsecularResidual
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι) : ℂ :=
  coefficient i j - secularProjection frequency coefficient i j

@[simp]
theorem secularProjection_eq_of_frequency_eq
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι)
    (h : frequency i = frequency j) :
    secularProjection frequency coefficient i j = coefficient i j := by
  simp [secularProjection, h]

@[simp]
theorem secularProjection_eq_zero_of_frequency_ne
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι)
    (h : frequency i ≠ frequency j) :
    secularProjection frequency coefficient i j = 0 := by
  simp [secularProjection, h]

/-- The resonant projection is idempotent. -/
@[zil_level physical_theorem]
theorem secularProjection_idempotent
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) :
    (fun i j => secularProjection frequency
      (fun k l => secularProjection frequency coefficient k l) i j) =
      fun i j => secularProjection frequency coefficient i j := by
  funext i j
  by_cases h : frequency i = frequency j
  · simp [secularProjection, h]
  · simp [secularProjection, h]

/-- Every coefficient decomposes into resonant and nonsecular pieces. -/
theorem secular_add_nonsecular
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι) :
    secularProjection frequency coefficient i j +
      nonsecularResidual frequency coefficient i j = coefficient i j := by
  unfold nonsecularResidual
  ring

@[simp]
theorem nonsecularResidual_eq_zero_of_frequency_eq
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι)
    (h : frequency i = frequency j) :
    nonsecularResidual frequency coefficient i j = 0 := by
  simp [nonsecularResidual, secularProjection, h]

@[simp]
theorem nonsecularResidual_eq_of_frequency_ne
    {ι : Type*} (frequency : ι → ℝ)
    (coefficient : ι → ι → ℂ) (i j : ι)
    (h : frequency i ≠ frequency j) :
    nonsecularResidual frequency coefficient i j = coefficient i j := by
  simp [nonsecularResidual, secularProjection, h]

/-- Pointwise finite-time averaging certificate approaching the exact secular
projection. -/
structure FiniteFrequencySecularCertificate (ι : Type*) where
  frequency : ι → ℝ
  redfieldCoefficient : ι → ι → ℂ
  averagedCoefficient : ℝ → ι → ι → ℂ
  averagingError : ℝ → ι → ι → ℝ
  averagingError_nonneg : ∀ T i j, 0 ≤ T → 0 ≤ averagingError T i j
  averaging_bound : ∀ T i j, 0 ≤ T →
    ‖averagedCoefficient T i j -
      secularProjection frequency redfieldCoefficient i j‖ ≤ averagingError T i j
  averagingError_tendsto_zero : ∀ i j,
    Tendsto (fun T => averagingError T i j) atTop (𝓝 0)

namespace FiniteFrequencySecularCertificate

theorem resonant_averaging_bound
    {ι : Type*} (c : FiniteFrequencySecularCertificate ι)
    (T : ℝ) (i j : ι) (hT : 0 ≤ T)
    (hω : c.frequency i = c.frequency j) :
    ‖c.averagedCoefficient T i j - c.redfieldCoefficient i j‖ ≤
      c.averagingError T i j := by
  simpa [secularProjection, hω] using c.averaging_bound T i j hT

theorem nonresonant_averaging_bound
    {ι : Type*} (c : FiniteFrequencySecularCertificate ι)
    (T : ℝ) (i j : ι) (hT : 0 ≤ T)
    (hω : c.frequency i ≠ c.frequency j) :
    ‖c.averagedCoefficient T i j‖ ≤ c.averagingError T i j := by
  simpa [secularProjection, hω] using c.averaging_bound T i j hT

end FiniteFrequencySecularCertificate

/-! ## D. Composed one-level reduction -/

/-- End-to-end error certificate from exact reduced dynamics to the one-level
LDDL occupation vector field. -/
structure OneLevelWeakCouplingReductionCertificate where
  bath : BathCorrelationTransformCertificate
  spectralRate : OnShellSpectralBathData
  spectralWeight_eq : spectralRate.onShellSpectralWeight = bath.spectralWeight
  exactReducedVectorField : ℝ → ℝ
  markovVectorField : ℝ → ℝ
  secularVectorField : ℝ → ℝ
  memoryError : ℝ → ℝ
  secularError : ℝ → ℝ
  memoryError_nonneg : ∀ n, 0 ≤ memoryError n
  secularError_nonneg : ∀ n, 0 ≤ secularError n
  memory_bound : ∀ n,
    ‖exactReducedVectorField n - markovVectorField n‖ ≤ memoryError n
  secular_bound : ∀ n,
    ‖markovVectorField n - secularVectorField n‖ ≤ secularError n
  secular_eq_lddl : ∀ n,
    secularVectorField n = occupationVectorField spectralRate.toRateData n

namespace OneLevelWeakCouplingReductionCertificate

/-- The LDDL half-width is coupling squared times the real continuum transform. -/
@[zil_level physical_theorem]
theorem goldenRuleGamma_eq_correlationTransform
    (c : OneLevelWeakCouplingReductionCertificate) :
    c.spectralRate.goldenRuleGamma =
      c.spectralRate.couplingStrengthSq * c.bath.transform.re := by
  unfold OnShellSpectralBathData.goldenRuleGamma
  rw [c.spectralWeight_eq, c.bath.transform_real_eq]
  ring

/-- Memory and secular errors add. -/
@[zil_level physical_theorem]
theorem total_reduction_error_bound
    (c : OneLevelWeakCouplingReductionCertificate) (n : ℝ) :
    ‖c.exactReducedVectorField n -
      occupationVectorField c.spectralRate.toRateData n‖ ≤
      c.memoryError n + c.secularError n := by
  rw [← c.secular_eq_lddl n]
  calc
    ‖c.exactReducedVectorField n - c.secularVectorField n‖ ≤
        ‖c.exactReducedVectorField n - c.markovVectorField n‖ +
          ‖c.markovVectorField n - c.secularVectorField n‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ c.memoryError n + c.secularError n :=
      add_le_add (c.memory_bound n) (c.secular_bound n)

/-- Vanishing analytic errors force exact agreement with the LDDL field. -/
theorem exactReducedVectorField_eq_lddl_of_zero_errors
    (c : OneLevelWeakCouplingReductionCertificate) (n : ℝ)
    (hmemory : c.memoryError n = 0)
    (hsecular : c.secularError n = 0) :
    c.exactReducedVectorField n =
      occupationVectorField c.spectralRate.toRateData n := by
  have h := c.total_reduction_error_bound n
  rw [hmemory, hsecular, add_zero] at h
  have hz : ‖c.exactReducedVectorField n -
      occupationVectorField c.spectralRate.toRateData n‖ = 0 :=
    le_antisymm h (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end OneLevelWeakCouplingReductionCertificate

/-! ## E. Concrete zero-error reduction and unitary Davies-scale realization -/

namespace GaussianContinuumBath

/-- For the exactly solvable Gaussian collision reservoir, the exact, Markov,
and secular occupation fields coincide.  Thus the generic error-composition
interface is instantiated with proved zero errors rather than supplied bounds. -/
noncomputable def exactReductionCertificate (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) :
    OneLevelWeakCouplingReductionCertificate :=
  let spectral := b.toOnShellData couplingStrengthSq occupation hc hf0 hf1
  { bath := b.toCertificate
    spectralRate := spectral
    spectralWeight_eq := rfl
    exactReducedVectorField := occupationVectorField spectral.toRateData
    markovVectorField := occupationVectorField spectral.toRateData
    secularVectorField := occupationVectorField spectral.toRateData
    memoryError := fun _ => 0
    secularError := fun _ => 0
    memoryError_nonneg := fun _ => le_rfl
    secularError_nonneg := fun _ => le_rfl
    memory_bound := fun _ => by simp
    secular_bound := fun _ => by simp
    secular_eq_lddl := fun _ => rfl }

/-- The instantiated exact reduced field is the one-level LDDL field with no
residual memory or secular error. -/
@[zil_level bridge_theorem]
theorem exactReductionCertificate_zero_error (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) (n : ℝ) :
    (b.exactReductionCertificate couplingStrengthSq occupation hc hf0 hf1).exactReducedVectorField n =
      occupationVectorField
        (b.toRateData couplingStrengthSq occupation hc hf0 hf1) n := by
  rfl

end GaussianContinuumBath

/-- On a diagonal occupation state, the `(1,1)` entry of the concrete GKSL
operator is exactly the scalar occupation vector field used by the reduction
certificate. -/
theorem oneLevelGKSLMatrix_occState_one_one (r : RateData)
    (n : ℝ) (hn0 : 0 ≤ n) (hn1 : n ≤ 1) :
    oneLevelGKSLMatrix r (occState n hn0 hn1).m 1 1 =
      ((occupationVectorField r n : ℝ) : ℂ) := by
  rw [oneLevelGKSLMatrix_eq, occState_m]
  simp [occupationVectorField, lossRate, gainRate, totalRate]
  ring

/-- At weak coupling `λ` and microscopic time `t`, purify the exact channel at
macroscopic time `λ²t`.  This is a genuine unitary channel on the system and
two fresh bath qubits, supplied by the repository's Stinespring constructor. -/
noncomputable def daviesUnitaryBathChannel (r : RateData) (lambda t : NNReal) :
    CPTPMap (Qubit × Qubit × Qubit) (Qubit × Qubit × Qubit) :=
  (r.oneLevelCPTPC0Semigroup.channel (lambda ^ 2 * t)).purify

/-- Every microscopic collision-bath channel is unitary. -/
@[zil_level physical_theorem]
theorem daviesUnitaryBathChannel_isUnitary (r : RateData) (lambda t : NNReal) :
    (daviesUnitaryBathChannel r lambda t).IsUnitary :=
  CPTPMap.purify_IsUnitary _

/-- Prepare the two fresh bath qubits, apply the microscopic unitary, and trace
the bath out. -/
noncomputable def daviesReducedUnitaryBathChannel (r : RateData) (lambda t : NNReal) :
    CPTPMap Qubit Qubit :=
  r.oneLevelCPTPC0Semigroup.channel (lambda ^ 2 * t)

/-- The named reduced channel is exactly the preparation/unitary/partial-trace
reduction of `daviesUnitaryBathChannel`.  The full reduction expression is
provided by the canonical Stinespring theorem rather than duplicated here. -/
@[zil_level bridge_theorem]
theorem daviesUnitaryBathChannel_reduces_to (r : RateData) (lambda t : NNReal) :
    r.oneLevelCPTPC0Semigroup.channel (lambda ^ 2 * t) =
      (let zero_prep : CPTPMap Unit (Qubit × Qubit) :=
          CPTPMap.replacement (MState.pure (Ket.basis default))
        let prep := (CPTPMap.id ⊗ᶜᵖ zero_prep)
        let append : CPTPMap Qubit (Qubit × Unit) :=
          CPTPMap.ofEquiv (Equiv.prodPUnit Qubit).symm
        CPTPMap.compose
          (CPTPMap.compose
            (CPTPMap.compose
              (CPTPMap.compose CPTPMap.traceLeft CPTPMap.traceLeft)
              (daviesUnitaryBathChannel r lambda t))
            prep)
          append) :=
  CPTPMap.purify_trace _

/-- The actual partial trace of the microscopic unitary is the channel at
macroscopic time `λ²t`. -/
theorem daviesReducedUnitaryBathChannel_eq (r : RateData) (lambda t : NNReal) :
    daviesReducedUnitaryBathChannel r lambda t =
      r.oneLevelCPTPC0Semigroup.channel (lambda ^ 2 * t) := by
  rfl

/-- On the Davies time scale `t=s/λ²`, every nonzero coupling gives the target
CPTP channel exactly. -/
@[zil_level physical_theorem]
theorem daviesReducedUnitaryBathChannel_rescaled_eq (r : RateData)
    (lambda s : NNReal) (hlambda : lambda ≠ 0) :
    daviesReducedUnitaryBathChannel r lambda (s / lambda ^ 2) =
      r.oneLevelCPTPC0Semigroup.channel s := by
  rw [daviesReducedUnitaryBathChannel_eq]
  congr 1
  field_simp

/-- Davies-scale convergence of the reduced microscopic unitary channel to the
one-level CPTP semigroup in the channel topology. -/
@[zil_level physical_theorem]
theorem daviesReducedUnitaryBathChannel_tendsto (r : RateData) (s : NNReal) :
    Tendsto (fun lambda : NNReal =>
      daviesReducedUnitaryBathChannel r lambda (s / lambda ^ 2))
      (nhdsWithin 0 (Ioi 0))
      (nhds (r.oneLevelCPTPC0Semigroup.channel s)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with lambda hlambda
  exact (daviesReducedUnitaryBathChannel_rescaled_eq r lambda s hlambda.ne').symm

/-- The convergence is uniform on every finite macroscopic interval in the
strong form that the Choi-matrix error vanishes at every time. -/
theorem daviesReducedUnitaryBathChannel_uniform_zero (r : RateData)
    (lambda : NNReal) (hlambda : lambda ≠ 0) (T : NNReal) :
    ∀ s ≤ T, daviesReducedUnitaryBathChannel r lambda (s / lambda ^ 2) =
      r.oneLevelCPTPC0Semigroup.channel s := by
  intro s _
  exact daviesReducedUnitaryBathChannel_rescaled_eq r lambda s hlambda

/-- Concrete continuum-bath/Davies capstone: the Gaussian spectral bath fixes
the rate, every microscopic collision is unitary, its Davies-rescaled reduction
converges to a bundled CPTP `C₀` semigroup, and that semigroup's right generator
is the explicit loss/gain GKSL operator. -/
@[zil_level bridge_theorem]
theorem gaussianContinuumBath_davies_cptp_gksl_capstone
    (b : GaussianContinuumBath)
    (couplingStrengthSq occupation : ℝ) (hc : 0 < couplingStrengthSq)
    (hf0 : 0 ≤ occupation) (hf1 : occupation ≤ 1) :
    let r := b.toRateData couplingStrengthSq occupation hc hf0 hf1
    (∀ lambda t, (daviesUnitaryBathChannel r lambda t).IsUnitary) ∧
      (∀ s, Tendsto (fun lambda : NNReal =>
          daviesReducedUnitaryBathChannel r lambda (s / lambda ^ 2))
        (nhdsWithin 0 (Ioi 0))
        (nhds (r.oneLevelCPTPC0Semigroup.channel s))) ∧
      r.oneLevelCPTPC0Semigroup.HasInfinitesimalGenerator
        (oneLevelGKSLMatrix r) := by
  dsimp
  exact ⟨daviesUnitaryBathChannel_isUnitary _,
    daviesReducedUnitaryBathChannel_tendsto _,
    RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator _⟩

end QuantumMechanics.LindbladDrivenLeads

/- ZIL-BEGIN -/

open QuantumMechanics.LindbladDrivenLeads

zil attach QuantumMechanics.LindbladDrivenLeads.BathCorrelationTransformCertificate.goldenRuleGamma_eq_coupling_mul_transform_re where
  formalizes @ "claim:an-integrable-one-sided-continuum-bath-correlation-transform-selects-the-one-level-golden-rule-half-width-through-its-positive-on-shell-real-part",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.BathCorrelationTransformCertificate.toOnShellSpectralBathData",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  requires @ "assumption:integrable-continuum-bath-correlation-transform-with-positive-on-shell-spectral-weight-and-vanishing-truncation-error",
  caveat @ "claim:existence-and-evaluation-of-the-transform-remain-model-specific-analytic-obligations"

zil attach QuantumMechanics.LindbladDrivenLeads.VolterraMarkovApproximation.memory_markov_bound where
  formalizes @ "claim:the-volterra-memory-to-local-markov-error-is-bounded-by-the-sum-of-the-correlation-tail-error-and-delayed-state-replacement-error",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.VolterraMarkovApproximation",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  requires @ "assumption:model-specific-tail-and-state-replacement-bounds",
  refines_toward @ "target:derive-the-bounds-from-continuum-bath-mixing-and-state-regularity"

zil attach QuantumMechanics.LindbladDrivenLeads.secularProjection_idempotent where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-finite-bohr-frequency-secular-projection-retaining-equal-frequency-pairs-is-exactly-idempotent",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "consistency-identity",
  refines_toward @ "target:quantitative-finite-time-oscillatory-secular-error-bound"

zil attach QuantumMechanics.LindbladDrivenLeads.OneLevelWeakCouplingReductionCertificate.total_reduction_error_bound where
  formalizes @ "claim:the-exact-reduced-one-level-vector-field-differs-from-the-lddl-vector-field-by-at-most-the-sum-of-memory-markovization-and-secular-averaging-errors",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.occupationVectorField_eq_goldenRule",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.OneLevelWeakCouplingReductionCertificate",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  requires @ "assumption:continuum-correlation-transform-memory-error-and-secular-error-certificates",
  caveat @ "claim:the-generic-certificate-alone-does-not-prove-a-unitary-davies-limit-the-Gaussian-collision-reservoir-below-is-a-separate-concrete-instantiation"

zil attach QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.correlation_eq_spectralIntegral where
  formalizes @ "claim:the-Gaussian-continuum-bath-correlation-is-the-matrix-coefficient-of-the-explicit-norm-preserving-spectral-unitary-group",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.persistentBathC0Group",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.correlation_eq_vacuum_matrixCoefficient",
  supported_by @ "lean:MeasureTheory.charFun_apply_real",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:Gaussian-spectral-reservoir-model-not-a-universal-bath-correlation-law"

zil attach QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.vacuum_matrixCoefficient where
  formalizes @ "claim:the-Gaussian-characteristic-function-is-the-normalized-vacuum-matrix-coefficient-of-a-fixed-unitary-C0-group-on-the-genuine-continuum-spectral-Hilbert-space",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.persistentBathModel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.evolutionC0Group",
  supported_by @ "lean:MeasureTheory.L2.inner_def",
  epistemic_status @ "conditional-model",
  requires @ "assumption:Gaussian-continuum-energy-law-with-variance-two-pi",
  caveat @ "claim:fixed-free-bath-Hamiltonian-and-vacuum-correlation-not-yet-a-fixed-interacting-system-bath-H-zero-plus-lambda-V-Davies-limit"

zil attach QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.persistentBath_unitaryCorrelationTransform where
  formalizes @ "claim:the-persistent-Gaussian-continuum-bath-has-a-normalized-vacuum-a-fixed-unitary-C0-energy-evolution-an-exact-vacuum-correlation-and-the-evaluated-positive-time-on-shell-transform-two-pi-J",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.norm_vacuum",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.vacuum_matrixCoefficient",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.transform_integral",
  epistemic_status @ "conditional-model",
  requires @ "assumption:positive-Gaussian-continuum-spectral-weight",
  caveat @ "claim:this-constructs-the-persistent-free-bath-and-its-mixing-correlation-but-does-not-yet-couple-it-to-the-system-through-one-fixed-H-zero-plus-lambda-V-Hamiltonian"

zil attach QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.transform_integral where
  formalizes @ "claim:the-explicit-Gaussian-continuum-unitary-correlation-is-integrable-and-its-positive-time-on-shell-transform-is-exactly-two-pi-times-the-spectral-weight",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.toCertificate",
  supported_by @ "lean:ProbabilityTheory.charFun_gaussianReal",
  supported_by @ "lean:integral_gaussian_complex_Ioi",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  requires @ "assumption:positive-Gaussian-continuum-spectral-weight",
  caveat @ "claim:the-variance-two-pi-normalization-is-a-model-choice-that-makes-the-transform-evaluation-exact"

zil attach QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.exactReductionCertificate_zero_error where
  discloses @ "lean:QuantumMechanics.LindbladDrivenLeads.OneLevelWeakCouplingReductionCertificate.total_reduction_error_bound",
  formalizes @ "claim:the-exactly-solvable-Gaussian-collision-reservoir-instantiates-the-memory-and-secular-error-composition-certificate-with-zero-errors-and-the-existing-one-level-LDDL-field",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.exactReductionCertificate",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.OneLevelWeakCouplingReductionCertificate.total_reduction_error_bound",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-zero-error-equality-is-definitional-after-constructing-this-exact-collision-certificate-with-coincident-fields-it-is-not-independent-evidence-that-errors-derived-from-an-arbitrary-Hamiltonian-vanish"

zil attach QuantumMechanics.LindbladDrivenLeads.daviesUnitaryBathChannel_reduces_to where
  formalizes @ "claim:preparing-two-fresh-bath-qubits-applying-the-bundled-unitary-collision-and-partially-tracing-the-bath-reproduces-the-one-level-CPTP-channel",
  implemented_by @ "lean:QuantumMechanics.LindbladDrivenLeads.daviesUnitaryBathChannel",
  supported_by @ "lean:CPTPMap.purify_trace",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "structural",
  caveat @ "claim:canonical-Stinespring-collision-dilation-with-fresh-ancillas-not-a-fixed-persistent-reservoir-Hamiltonian"

zil attach QuantumMechanics.LindbladDrivenLeads.daviesReducedUnitaryBathChannel_tendsto where
  formalizes @ "claim:after-Davies-time-rescaling-the-partial-trace-of-the-concrete-microscopic-unitary-collision-channel-converges-in-CPTP-channel-topology-to-the-one-level-C0-semigroup",
  supported_by @ "lean:CPTPMap.purify_trace",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.daviesUnitaryBathChannel_isUnitary",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.daviesUnitaryBathChannel_reduces_to",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-fresh-ancilla-Stinespring-collision-reservoir-not-the-general-Davies-theorem-for-one-fixed-H-zero-plus-lambda-V-Hamiltonian-and-a-persistent-thermodynamic-bath"

zil attach QuantumMechanics.LindbladDrivenLeads.gaussianContinuumBath_davies_cptp_gksl_capstone where
  formalizes @ "claim:a-concrete-Gaussian-continuum-spectral-bath-fixes-the-rate-and-has-a-unitary-collision-realization-whose-Davies-rescaled-reduction-is-the-bundled-CPTP-C0-semigroup-with-the-explicit-loss-gain-GKSL-right-generator",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.transform_integral",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.daviesReducedUnitaryBathChannel_tendsto",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator",
  axiom_status @ "checked:axiom-clean-non-vacuous-audit-pending-ci",
  epistemic_status @ "conditional-model",
  caveat @ "claim:constructive-Gaussian-repeated-interaction-model-with-fresh-bath-ancillas-not-a-thermodynamic-limit-or-a-derivation-for-every-continuum-Hamiltonian"

zil_file_contract physlib.lindbladDrivenLeads.continuumWeakCouplingReduction where
  promises "The generic continuum weak-coupling interfaces are concretely inhabited by a Gaussian continuum spectral bath. Its energy-multiplication Hamiltonian acts through a fixed bundled unitary C0 group on the genuine spectral L2 Hilbert space; the normalized-vacuum matrix coefficient is exactly the correlation used by the rate derivation. The on-shell transform and actual finite-window convergence are proved, and the induced one-level rate separately has a unitary Stinespring collision-reservoir realization. After Davies rescaling the reduced collision channel converges in the CPTP channel topology to the existing strongly continuous one-level semigroup, uniformly by exact channel equality in the exactly solvable realization, and the limit has the explicit loss/gain GKSL right generator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:ProbabilityTheory.charFun_gaussianReal",
    "lean:integral_gaussian_complex_Ioi",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.evolutionC0Group",
    "lean:CPTPMap.purify_trace",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator"]
  forbids_substitutes ["an abstract correlation certificate with no concrete spectral measure",
    "a non-unitary microscopic collision map",
    "calling the fresh-ancilla collision construction the general fixed-Hamiltonian Davies theorem",
    "claiming the fixed free Gaussian bath group already supplies a coupled system-bath H-zero-plus-lambda-V Hamiltonian",
    "claiming a coupled thermodynamic persistent-reservoir Davies limit not present in the carrier"]
  witnessed_by [QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.vacuum_matrixCoefficient,
    QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.correlation_eq_vacuum_matrixCoefficient,
    QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.persistentBath_unitaryCorrelationTransform,
    QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.correlation_eq_spectralIntegral,
    QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.transform_integral,
    QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.truncationError_tendsto_zero,
    QuantumMechanics.LindbladDrivenLeads.GaussianContinuumBath.exactReductionCertificate_zero_error,
    QuantumMechanics.LindbladDrivenLeads.daviesUnitaryBathChannel_isUnitary,
    QuantumMechanics.LindbladDrivenLeads.daviesUnitaryBathChannel_reduces_to,
    QuantumMechanics.LindbladDrivenLeads.daviesReducedUnitaryBathChannel_tendsto,
    QuantumMechanics.LindbladDrivenLeads.gaussianContinuumBath_davies_cptp_gksl_capstone]

/- ZIL-END -/
