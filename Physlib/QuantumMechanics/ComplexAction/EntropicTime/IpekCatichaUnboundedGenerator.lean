/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
public import Physlib.QuantumMechanics.DDimensions.Operators.Multiplication
public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SelfAdjoint
public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SpectralMeasure
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ContinuumSemigroupClosure
public import Mathlib.Analysis.Complex.RealDeriv
meta import Zil

/-!
# Unbounded continuum realization of the Ipek--Caticha generator

This module promotes the lapse/shift split of the functional Schrödinger generator from a total
linear map to the repository's densely defined, closable `LinearPMap` operators.

## A. Common-core generator

The sum `N H⊥ + Nᵢ Hᵢ` is defined on the intersection of the two operator domains.  If a dense
common core lies in both domains and both pieces are symmetric, the smeared generator is symmetric,
dense, closable, and therefore an unbounded operator in the precise repository sense.

## B. Maximal multiplication realization

For continuum mode-diagonal generators on `SpaceDHilbertSpace d`, the combined real symbol defines a
maximal multiplication operator.  Existing multiplication-operator theory then proves self-adjointness,
closedness, essential self-adjointness, and reality of the spectrum.  This is a genuine infinite-
dimensional continuum result; it does not replace differential functional Hamiltonians by multiplication
operators without a diagonalization hypothesis.
-/

set_option autoImplicit false

open LinearPMap
open MeasureTheory
open ComplexConjugate
open Filter Set
open scoped Topology

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator

/-! ## A. Common-core unbounded generator -/

/-- The lapse/shift-smeared Caticha generator as a partially defined operator.  Its domain is the
intersection of the normal and tangential generator domains. -/
noncomputable def unboundedSmearedSchrodingerGenerator {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N Ni : ℝ) (Hperp Hi : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  (N : ℂ) • Hperp + (Ni : ℂ) • Hi

/-- Symmetry of the normal and tangential pieces is preserved by real lapse/shift smearing. -/
lemma unboundedSmearedSchrodingerGenerator_isSymmetric {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N Ni : ℝ) (Hperp Hi : H →ₗ.[ℂ] H)
    (hperp : Hperp.IsSymmetric) (hi : Hi.IsSymmetric) :
    (unboundedSmearedSchrodingerGenerator N Ni Hperp Hi).IsSymmetric :=
  (hperp.smul (Complex.conj_ofReal N)).add (hi.smul (Complex.conj_ofReal Ni))

/-- A dense subspace contained in both component domains is a dense domain for the smeared sum. -/
lemma unboundedSmearedSchrodingerGenerator_hasDenseDomain {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N Ni : ℝ) (Hperp Hi : H →ₗ.[ℂ] H) (E : Submodule ℂ H)
    (hE : Dense (E : Set H)) (hperp : E ≤ Hperp.domain) (hi : E ≤ Hi.domain) :
    (unboundedSmearedSchrodingerGenerator N Ni Hperp Hi).HasDenseDomain := by
  apply hE.mono
  intro ψ hψ
  exact ⟨hperp hψ, hi hψ⟩

/-- **Common-core unbounded Caticha operator.**  Symmetric component generators sharing a dense
core produce a densely defined closable smeared operator. -/
theorem unboundedSmearedSchrodingerGenerator_isUnbounded {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N Ni : ℝ) (Hperp Hi : H →ₗ.[ℂ] H) (E : Submodule ℂ H)
    (hE : Dense (E : Set H)) (hperpDomain : E ≤ Hperp.domain)
    (hiDomain : E ≤ Hi.domain) (hperp : Hperp.IsSymmetric) (hi : Hi.IsSymmetric) :
    (unboundedSmearedSchrodingerGenerator N Ni Hperp Hi).IsUnbounded := by
  have hsym := unboundedSmearedSchrodingerGenerator_isSymmetric N Ni Hperp Hi hperp hi
  exact hsym.isUnbounded_iff_hasDenseDomain.mpr
    (unboundedSmearedSchrodingerGenerator_hasDenseDomain N Ni Hperp Hi E hE
      hperpDomain hiDomain)

/-! ## B. Self-adjoint continuum multiplication realization -/

open QuantumMechanics.SpaceDHilbertSpace

/-- The continuum mode-diagonal Caticha symbol `N h⊥ + Nᵢ hᵢ`. -/
def catichaMultiplicationSymbol {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) : Space d → ℂ :=
  fun x => (N : ℂ) * hperp x + (Ni : ℂ) * hi x

/-- Measurability of both mode symbols implies measurability of their lapse/shift combination. -/
lemma catichaMultiplicationSymbol_aestronglyMeasurable {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpMeas : AEStronglyMeasurable hperp)
    (hiMeas : AEStronglyMeasurable hi) :
    AEStronglyMeasurable (catichaMultiplicationSymbol N Ni hperp hi) := by
  change AEStronglyMeasurable
    (fun x => (N : ℂ) * hperp x + (Ni : ℂ) * hi x)
  exact (hperpMeas.const_mul (N : ℂ)).add (hiMeas.const_mul (Ni : ℂ))

/-- Real-valued component symbols give a real-valued smeared symbol. -/
lemma catichaMultiplicationSymbol_conj {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpReal : conj ∘ hperp = hperp)
    (hiReal : conj ∘ hi = hi) :
    conj ∘ catichaMultiplicationSymbol N Ni hperp hi =
      catichaMultiplicationSymbol N Ni hperp hi := by
  funext x
  have hp := congrFun hperpReal x
  have hᵢ := congrFun hiReal x
  simp only [Function.comp_apply] at hp hᵢ ⊢
  change conj ((N : ℂ) * hperp x + (Ni : ℂ) * hi x) =
    (N : ℂ) * hperp x + (Ni : ℂ) * hi x
  rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    Complex.conj_ofReal, Complex.conj_ofReal, hp, hᵢ]

/-- The real frequency carried by the continuum mode-diagonal Caticha
generator.  Under the existing conjugation-fixed hypotheses its complex
embedding is exactly `catichaMultiplicationSymbol`. -/
def catichaRealFrequency {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) : Space d → ℝ :=
  fun x => (catichaMultiplicationSymbol N Ni hperp hi x).re

theorem catichaRealFrequency_ofReal_eq_symbol {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpReal : conj ∘ hperp = hperp)
    (hiReal : conj ∘ hi = hi) :
    (fun x => (catichaRealFrequency N Ni hperp hi x : ℂ)) =
      catichaMultiplicationSymbol N Ni hperp hi := by
  funext x
  exact Complex.conj_eq_iff_re.mp
    (congrFun
      (catichaMultiplicationSymbol_conj N Ni hperp hi hperpReal hiReal) x)

/-- Pointwise measurable real mode data make the explicit Caticha frequency
measurable on continuum configuration space. -/
theorem catichaRealFrequency_measurable {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpMeas : Measurable hperp)
    (hiMeas : Measurable hi) :
    Measurable (catichaRealFrequency N Ni hperp hi) := by
  unfold catichaRealFrequency catichaMultiplicationSymbol
  fun_prop

/-- The maximal continuum multiplication operator associated with the Caticha symbol. -/
noncomputable def continuumMultiplicationGenerator {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) :
    QuantumMechanics.SpaceDHilbertSpace d →ₗ.[ℂ]
      QuantumMechanics.SpaceDHilbertSpace d :=
  QuantumMechanics.SpaceDHilbertSpace.mulOperator MeasureTheory.volume
    (catichaMultiplicationSymbol N Ni hperp hi)

/-- **Concrete spectral realization of the Caticha generator.**  For real
mode symbols the existing unbounded generator is literally multiplication by
the real frequency against the canonical strong configuration PVM.  Thus the
PVM used downstream is constructed from the same continuum carrier rather
than supplied as an unrelated spectral certificate. -/
theorem continuumMultiplicationGenerator_eq_realFrequency_mulOperator
    {d : ℕ} (N Ni : ℝ) (hperp hi : Space d → ℂ)
    (hperpReal : conj ∘ hperp = hperp) (hiReal : conj ∘ hi = hi) :
    continuumMultiplicationGenerator N Ni hperp hi =
      QuantumMechanics.SpaceDHilbertSpace.mulOperator MeasureTheory.volume
        (fun x => (catichaRealFrequency N Ni hperp hi x : ℂ)) := by
  unfold continuumMultiplicationGenerator
  rw [catichaRealFrequency_ofReal_eq_symbol N Ni hperp hi hperpReal hiReal]

/-- Every measurable spectral set acts on a Caticha continuum wavefunction
by the expected indicator multiplier. -/
theorem caticha_configurationPVM_apply_ae {d : ℕ}
    {s : Set (Space d)} (hs : MeasurableSet s)
    (ψ : QuantumMechanics.SpaceDHilbertSpace d) :
    (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d
        s ψ : Space d → ℂ) =ᵐ[volume] s.indicator ψ :=
  QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure_apply_ae
    hs ψ

/-- The continuum generator acts almost everywhere by multiplication with the combined symbol. -/
lemma continuumMultiplicationGenerator_apply_ae {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ)
    (ψ : (continuumMultiplicationGenerator N Ni hperp hi).domain) :
    continuumMultiplicationGenerator N Ni hperp hi ψ =ᵐ[volume]
      catichaMultiplicationSymbol N Ni hperp hi • ψ :=
  QuantumMechanics.SpaceDHilbertSpace.mulOperator_apply_ae ψ

/-- **Self-adjoint unbounded continuum Caticha generator.**  A measurable real mode-diagonal
normal/tangential pair produces a maximal self-adjoint operator on the continuum Hilbert space. -/
theorem continuumMultiplicationGenerator_isSelfAdjoint {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpMeas : AEStronglyMeasurable hperp)
    (hiMeas : AEStronglyMeasurable hi) (hperpReal : conj ∘ hperp = hperp)
    (hiReal : conj ∘ hi = hi) :
    IsSelfAdjoint (continuumMultiplicationGenerator N Ni hperp hi) :=
  QuantumMechanics.SpaceDHilbertSpace.mulOperator_isSelfAdjoint_ofReal
    (catichaMultiplicationSymbol_aestronglyMeasurable N Ni hperp hi hperpMeas hiMeas)
    (catichaMultiplicationSymbol_conj N Ni hperp hi hperpReal hiReal)

/-- The maximal multiplication realization is densely defined and closable. -/
lemma continuumMultiplicationGenerator_isUnbounded {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpMeas : AEStronglyMeasurable hperp)
    (hiMeas : AEStronglyMeasurable hi) :
    (continuumMultiplicationGenerator N Ni hperp hi).IsUnbounded :=
  QuantumMechanics.SpaceDHilbertSpace.mulOperator_isUnbounded
    (catichaMultiplicationSymbol_aestronglyMeasurable N Ni hperp hi hperpMeas hiMeas)

/-- The self-adjoint continuum Caticha generator has real spectrum. -/
theorem continuumMultiplicationGenerator_spectrum_real {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpMeas : AEStronglyMeasurable hperp)
    (hiMeas : AEStronglyMeasurable hi) (hperpReal : conj ∘ hperp = hperp)
    (hiReal : conj ∘ hi = hi) :
    σ (continuumMultiplicationGenerator N Ni hperp hi) ⊆ Set.range Complex.ofReal :=
  LinearPMap.IsSelfAdjoint.spectrum_real
    (continuumMultiplicationGenerator_isSelfAdjoint N Ni hperp hi hperpMeas hiMeas
      hperpReal hiReal)

/-- Self-adjointness also makes the continuum realization essentially self-adjoint on its maximal
domain, so its closure is its unique self-adjoint extension. -/
lemma continuumMultiplicationGenerator_isEssentiallySelfAdjoint {d : ℕ} (N Ni : ℝ)
    (hperp hi : Space d → ℂ) (hperpMeas : AEStronglyMeasurable hperp)
    (hiMeas : AEStronglyMeasurable hi) (hperpReal : conj ∘ hperp = hperp)
    (hiReal : conj ∘ hi = hi) :
    (continuumMultiplicationGenerator N Ni hperp hi).IsEssentiallySelfAdjoint :=
  LinearPMap.IsSelfAdjoint.isEssentiallySelfAdjoint
    (continuumMultiplicationGenerator_isSelfAdjoint N Ni hperp hi hperpMeas hiMeas
      hperpReal hiReal)

/-! ## C. Maximally dissipative homogeneous CAT/EPT sector -/

/-- The resolvent characterization of maximal dissipativity used here: every positive real
resolvent has the contraction estimate and is onto. -/
def IsMaximallyDissipative {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : K →L[ℂ] K) : Prop :=
  (∀ (lambda : ℝ), 0 < lambda → ∀ x,
      lambda * ‖x‖ ≤ ‖(lambda : ℂ) • x - A x‖) ∧
    ∀ (lambda : ℝ), 0 < lambda →
      Function.Surjective (fun x => (lambda : ℂ) • x - A x)

/-- The homogeneous irreversible CAT/EPT generator `-γ I`, the exact imaginary-action
damping sector after the Hamiltonian phase has been removed. -/
noncomputable def catEptDissipativeGenerator {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (γ : ℝ) : K →L[ℂ] K :=
  -(γ : ℂ) • ContinuousLinearMap.id ℂ K

@[simp] lemma catEptDissipativeGenerator_apply {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (γ : ℝ) (x : K) :
    catEptDissipativeGenerator γ x = -(γ : ℂ) • x := by
  simp [catEptDissipativeGenerator]

/-- The nonnegative homogeneous damping generator is maximally dissipative. -/
lemma catEptDissipativeGenerator_maximallyDissipative {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (γ : ℝ) (hγ : 0 ≤ γ) :
    IsMaximallyDissipative (catEptDissipativeGenerator (K := K) γ) := by
  constructor
  · intro lambda hlambda x
    rw [catEptDissipativeGenerator_apply, neg_smul, sub_neg_eq_add, ← add_smul]
    rw [norm_smul]
    have hsum : 0 ≤ lambda + γ := add_nonneg (le_of_lt hlambda) hγ
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hγ) (norm_nonneg x)
  · intro lambda hlambda y
    have hsum : lambda + γ ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg hlambda hγ)
    refine ⟨((1 / (lambda + γ) : ℝ) : ℂ) • y, ?_⟩
    change (lambda : ℂ) • (((1 / (lambda + γ) : ℝ) : ℂ) • y) -
      catEptDissipativeGenerator (K := K) γ
        (((1 / (lambda + γ) : ℝ) : ℂ) • y) = y
    rw [catEptDissipativeGenerator_apply, neg_smul, sub_neg_eq_add,
      ← add_smul, ← mul_smul]
    convert one_smul ℂ y using 2
    rw [← Complex.ofReal_add]
    norm_cast
    simp [div_eq_mul_inv, hsum]

/-- The explicit homogeneous CAT/EPT damping evolution `exp(-γt) I`. -/
noncomputable def catEptDampingOperator {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (γ t : ℝ) : K →L[ℂ] K :=
  ((Real.exp ((-γ) * t) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ K

@[simp] lemma catEptDampingOperator_apply {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (γ t : ℝ) (x : K) :
    catEptDampingOperator γ t x =
      ((Real.exp ((-γ) * t) : ℝ) : ℂ) • x := by
  simp [catEptDampingOperator]

/-- The exact damping evolution is a strongly continuous semigroup. -/
noncomputable def catEptDampingC0Semigroup {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (γ : ℝ) :
    QuantumMechanics.LindbladDrivenLeads.ComplexC0Semigroup (K := K) :=
  { operator := catEptDampingOperator γ
    operator_zero := by
      ext x
      simp [catEptDampingOperator]
    operator_add := by
      intro s t
      ext x
      simp only [catEptDampingOperator_apply, ContinuousLinearMap.comp_apply]
      rw [show (-γ) * (s + t) = (-γ) * s + (-γ) * t by ring, Real.exp_add]
      push_cast
      rw [mul_smul]
    strong_continuous := by
      intro x
      simp only [catEptDampingOperator_apply]
      fun_prop }

/-- The operator `-γ I` is the right strong infinitesimal generator of the explicit
CAT/EPT damping semigroup. -/
lemma catEptDampingC0Semigroup_hasGenerator {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (γ : ℝ) :
    (catEptDampingC0Semigroup (K := K) γ).HasInfinitesimalGenerator
      (catEptDissipativeGenerator γ) := by
  intro x
  have hderiv :
      HasDerivAt
        (fun t : ℝ => ((Real.exp ((-γ) * t) : ℝ) : ℂ) • x)
        (-(γ : ℂ) • x) 0 := by
    have hg : HasDerivAt (fun t : ℝ => (-γ) * t) (-γ) 0 :=
      by simpa using (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul (-γ)
    have hr : HasDerivAt (fun t : ℝ => Real.exp ((-γ) * t)) (-γ) 0 := by
      simpa using hg.exp
    simpa only [Complex.ofReal_neg] using hr.ofReal_comp.smul_const x
  have hs := hderiv.tendsto_slope_zero_right
  simpa [catEptDampingC0Semigroup, catEptDampingOperator_apply,
    catEptDissipativeGenerator_apply] using hs

/-- At nonnegative times, a nonnegative entropy-production rate makes the CAT/EPT
semigroup a contraction. -/
lemma catEptDampingC0Semigroup_contracts {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (x : K) :
    ‖(catEptDampingC0Semigroup (K := K) γ).operator t x‖ ≤ ‖x‖ := by
  rw [show (catEptDampingC0Semigroup (K := K) γ).operator t x =
    ((Real.exp ((-γ) * t) : ℝ) : ℂ) • x by
      simp [catEptDampingC0Semigroup]]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg x)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) ht))

/-- **Continuum CAT/EPT semigroup capstone.**  On the actual continuum `L²` carrier,
the homogeneous imaginary-action sector is maximally dissipative, generates its
identified strongly continuous semigroup, and contracts every positive-time orbit. -/
lemma continuumCatEpt_maximalDissipative_semigroup (d : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    IsMaximallyDissipative
        (catEptDissipativeGenerator
          (K := QuantumMechanics.SpaceDHilbertSpace d) γ)
      ∧ (catEptDampingC0Semigroup
          (K := QuantumMechanics.SpaceDHilbertSpace d) γ).HasInfinitesimalGenerator
        (catEptDissipativeGenerator γ)
      ∧ ∀ t, 0 ≤ t → ∀ ψ : QuantumMechanics.SpaceDHilbertSpace d,
        ‖(catEptDampingC0Semigroup γ).operator t ψ‖ ≤ ‖ψ‖ :=
  ⟨catEptDissipativeGenerator_maximallyDissipative γ hγ,
    catEptDampingC0Semigroup_hasGenerator γ,
    fun t ht ψ => catEptDampingC0Semigroup_contracts γ t hγ ht ψ⟩

/-! ## D. Hamiltonian phase plus irreversible damping -/

/-- The homogeneous CAT/EPT complex-action generator, including the Hamiltonian phase. -/
noncomputable def catEptComplexGenerator {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (E γ : ℝ) : K →L[ℂ] K :=
  ((-γ : ℂ) - Complex.I * (E : ℂ)) • ContinuousLinearMap.id ℂ K

@[simp] lemma catEptComplexGenerator_apply {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (E γ : ℝ) (x : K) :
    catEptComplexGenerator E γ x =
      ((-γ : ℂ) - Complex.I * (E : ℂ)) • x := by
  simp [catEptComplexGenerator]

/-- Adding the skew Hamiltonian phase `-iE` preserves maximal dissipativity of the
nonnegative homogeneous damping generator. -/
lemma catEptComplexGenerator_maximallyDissipative {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (E γ : ℝ) (hγ : 0 ≤ γ) :
    IsMaximallyDissipative (catEptComplexGenerator (K := K) E γ) := by
  constructor
  · intro lambda hlambda x
    rw [catEptComplexGenerator_apply, ← sub_smul, norm_smul]
    let z : ℂ := (lambda : ℂ) - ((-γ : ℂ) - Complex.I * (E : ℂ))
    have hzre : z.re = lambda + γ := by
      simp [z, Complex.mul_re]
    have hzl : lambda ≤ ‖z‖ := by
      calc
        lambda ≤ lambda + γ := le_add_of_nonneg_right hγ
        _ = |z.re| := by rw [hzre, abs_of_nonneg (add_nonneg hlambda.le hγ)]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    exact mul_le_mul_of_nonneg_right hzl (norm_nonneg x)
  · intro lambda hlambda y
    let z : ℂ := (lambda : ℂ) - ((-γ : ℂ) - Complex.I * (E : ℂ))
    have hzre : z.re = lambda + γ := by
      simp [z, Complex.mul_re]
    have hz : z ≠ 0 := by
      intro h
      have hzero : z.re = 0 := by rw [h]; rfl
      rw [hzre] at hzero
      linarith
    refine ⟨z⁻¹ • y, ?_⟩
    dsimp only
    rw [catEptComplexGenerator_apply, ← sub_smul]
    change z • (z⁻¹ • y) = y
    rw [← mul_smul, mul_inv_cancel₀ hz, one_smul]

/-- Explicit phase-plus-damping evolution generated by `(-γ-iE)I`. -/
noncomputable def catEptComplexOperator {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (E γ t : ℝ) : K →L[ℂ] K :=
  Complex.exp (((-γ : ℂ) - Complex.I * (E : ℂ)) * (t : ℂ)) •
    ContinuousLinearMap.id ℂ K

@[simp] lemma catEptComplexOperator_apply {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (E γ t : ℝ) (x : K) :
    catEptComplexOperator E γ t x =
      Complex.exp (((-γ : ℂ) - Complex.I * (E : ℂ)) * (t : ℂ)) • x := by
  simp [catEptComplexOperator]

/-- The exact Hamiltonian-phase-plus-damping evolution is a strongly continuous semigroup. -/
noncomputable def catEptComplexC0Semigroup {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E γ : ℝ) :
    QuantumMechanics.LindbladDrivenLeads.ComplexC0Semigroup (K := K) :=
  { operator := catEptComplexOperator E γ
    operator_zero := by
      ext x
      simp [catEptComplexOperator]
    operator_add := by
      intro s t
      ext x
      simp only [catEptComplexOperator_apply, ContinuousLinearMap.comp_apply]
      rw [show (((-γ : ℂ) - Complex.I * (E : ℂ)) * ((s + t : ℝ) : ℂ)) =
          (((-γ : ℂ) - Complex.I * (E : ℂ)) * (s : ℂ)) +
          (((-γ : ℂ) - Complex.I * (E : ℂ)) * (t : ℂ)) by
            push_cast; ring,
        Complex.exp_add, mul_smul]
    strong_continuous := by
      intro x
      simp only [catEptComplexOperator_apply]
      fun_prop }

/-- `(-γ-iE)I` is the right strong infinitesimal generator of the explicit complex
CAT/EPT semigroup. -/
lemma catEptComplexC0Semigroup_hasGenerator {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E γ : ℝ) :
    (catEptComplexC0Semigroup (K := K) E γ).HasInfinitesimalGenerator
      (catEptComplexGenerator E γ) := by
  intro x
  let a : ℂ := (-γ : ℂ) - Complex.I * (E : ℂ)
  have harg : HasDerivAt (fun t : ℝ => a * (t : ℂ)) a 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul a
  have hderiv :
      HasDerivAt (fun t : ℝ => Complex.exp (a * (t : ℂ)) • x) (a • x) 0 := by
    simpa using harg.cexp.smul_const x
  have hs := hderiv.tendsto_slope_zero_right
  simpa [a, catEptComplexC0Semigroup, catEptComplexOperator_apply,
    catEptComplexGenerator_apply] using hs

/-- The Hamiltonian phase is norm-preserving, so nonnegative entropy damping makes the
full complex-action semigroup contractive at nonnegative time. -/
lemma catEptComplexC0Semigroup_contracts {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (x : K) :
    ‖(catEptComplexC0Semigroup (K := K) E γ).operator t x‖ ≤ ‖x‖ := by
  rw [show (catEptComplexC0Semigroup (K := K) E γ).operator t x =
    Complex.exp (((-γ : ℂ) - Complex.I * (E : ℂ)) * (t : ℂ)) • x by
      simp [catEptComplexC0Semigroup]]
  rw [norm_smul, Complex.norm_exp]
  have hre :
      ((((-γ : ℂ) - Complex.I * (E : ℂ)) * (t : ℂ))).re = -γ * t := by
    simp [Complex.mul_re]
  rw [hre]
  exact mul_le_of_le_one_left (norm_nonneg x)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) ht))

/-- **Full homogeneous continuum CAT/EPT semigroup capstone.**  On continuum `L²`, the
combined Hamiltonian phase and imaginary-action damping generator is maximally dissipative,
generates its explicit `C₀` semigroup, and is contractive for positive time. -/
lemma continuumCatEpt_complex_maximalDissipative_semigroup
    (d : ℕ) (E γ : ℝ) (hγ : 0 ≤ γ) :
    IsMaximallyDissipative
        (catEptComplexGenerator
          (K := QuantumMechanics.SpaceDHilbertSpace d) E γ)
      ∧ (catEptComplexC0Semigroup
          (K := QuantumMechanics.SpaceDHilbertSpace d) E γ).HasInfinitesimalGenerator
        (catEptComplexGenerator E γ)
      ∧ ∀ t, 0 ≤ t → ∀ ψ : QuantumMechanics.SpaceDHilbertSpace d,
        ‖(catEptComplexC0Semigroup E γ).operator t ψ‖ ≤ ‖ψ‖ :=
  ⟨catEptComplexGenerator_maximallyDissipative E γ hγ,
    catEptComplexC0Semigroup_hasGenerator E γ,
    fun t ht ψ => catEptComplexC0Semigroup_contracts E γ t hγ ht ψ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.unboundedSmearedSchrodingerGenerator_isUnbounded where
  supported_by @ "lean:ContinuousLinearMap.adjoint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.unboundedSmearedSchrodingerGenerator_hasDenseDomain",
  formalizes @ "claim:the-ipek-caticha-smeared-generator-on-a-dense-common-core-is-a-closable-unbounded-operator",
  caveat @ "claim:symmetry-and-a-dense-common-core-do-not-alone-imply-self-adjointness-of-an-arbitrary-operator-sum"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_isSelfAdjoint where
  formalizes @ "claim:a-real-measurable-mode-diagonal-ipek-caticha-generator-is-self-adjoint-on-continuum-l2",
  supported_by @ "paper:ipek-caticha-covariant-entropic-dynamics",
  caveat @ "claim:maximal-multiplication-realization-of-a-diagonalized-generator-not-a-diagonalization-theorem-for-general-functional-differential-operators"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_spectrum_real where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_isSelfAdjoint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.TypeIIIUnboundedDynamics.spectrum_real",
  formalizes @ "claim:the-self-adjoint-unbounded-continuum-caticha-generator-has-real-spectrum",
  requires @ "claim:a-real-measurable-mode-diagonal-ipek-caticha-generator-is-self-adjoint-on-continuum-l2"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_eq_realFrequency_mulOperator where
  formalizes @ "claim:the-real-mode-diagonal-continuum-caticha-generator-is-multiplication-by-its-explicit-real-frequency-against-the-constructed-strong-configuration-pvm",
  supported_by @ "lean:QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure",
  caveat @ "claim:this-is-the-spectral-realization-of-the-explicit-multiplication-sector-not-an-unbounded-borel-functional-calculus-for-arbitrary-self-adjoint-functional-differential-generators"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumCatEpt_maximalDissipative_semigroup where
  formalizes @ "claim:the-homogeneous-imaginary-action-sector-minus-gamma-times-identity-on-the-actual-continuum-l2-cat-ept-carrier-is-maximally-dissipative-generates-exp-minus-gamma-t-and-is-a-positive-time-contraction",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.ComplexC0Semigroup",
  caveat @ "claim:this-closes-the-homogeneous-damping-sector-not-a-lumer-phillips-generation-theorem-for-every-unbounded-functional-differential-caticha-generator"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumCatEpt_complex_maximalDissipative_semigroup where
  formalizes @ "claim:the-full-homogeneous-cat-ept-generator-minus-gamma-minus-i-e-times-identity-on-continuum-l2-is-maximally-dissipative-generates-the-exp-minus-gamma-minus-i-e-times-t-c0-semigroup-and-contracts-at-positive-time",
  supported_by @ "lean:Complex.norm_exp",
  caveat @ "claim:this-restores-the-hamiltonian-phase-in-the-bounded-homogeneous-sector-not-a-general-unbounded-lumer-phillips-theorem-for-functional-differential-caticha-generators"

zil_file_contract physlib.ipekCatichaUnboundedGenerator where
  promises "The Ipek--Caticha lapse/shift sum is a densely defined closable unbounded operator on any shared dense symmetric core. In the continuum mode-diagonal realization, measurable real component symbols define a maximal self-adjoint multiplication operator, its real frequency is explicit, and measurable spectral sets act through the constructed strong configuration PVM. On the actual continuum L2 carrier, both the homogeneous imaginary-action sector -gamma I and the full bounded complex-action sector (-gamma-iE)I are maximally dissipative and generate their explicit contraction C0 semigroups."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:LinearPMap.IsSymmetric.isUnbounded_iff_hasDenseDomain",
    "lean:QuantumMechanics.SpaceDHilbertSpace.mulOperator_isSelfAdjoint_ofReal",
    "lean:LinearPMap.IsSelfAdjoint.spectrum_real"]
  forbids_substitutes ["self-adjointness of a general sum inferred from symmetry alone",
    "a general functional differential Hamiltonian identified with a multiplication operator without diagonalization data",
    "claiming the homogeneous bounded damping proof is the general unbounded Lumer-Phillips theorem"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.unboundedSmearedSchrodingerGenerator_isUnbounded,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_isSelfAdjoint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_spectrum_real,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_eq_realFrequency_mulOperator,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.caticha_configurationPVM_apply_ae,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumCatEpt_maximalDissipative_semigroup,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumCatEpt_complex_maximalDissipative_semigroup]

/- ZIL-END -/
