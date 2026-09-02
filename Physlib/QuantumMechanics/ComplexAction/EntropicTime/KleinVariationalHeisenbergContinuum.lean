/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Distribution.SchwartzNuclear.SchwartzHermiteExpansion
public import Physlib.QuantumMechanics.OneDimension.Operators.Commutation
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator
meta import Zil

/-!
# Klein--Li variational matrix mechanics on infinite and pointwise carriers

Klein and Li, *Variational Principles and Heisenberg Matrix Mechanics*, Physica 96A (1979),
derive Heisenberg dynamics and the canonical commutation constraint in the energy representation.
In particular, their Eq. (4.8) is the matrix-entry identity

`(E_m - E_n) X_nm = i P_nm`.

This module separates that exact matrix identity from analytic upgrades supplied by existing
repository infrastructure:

* a genuine countably infinite `ℓ²(ℕ,ℂ)` energy representation, with a maximal self-adjoint
  diagonal Hamiltonian and a complete Hilbert basis;
* a genuine continuum `L²` multiplication Hamiltonian with maximal domain, self-adjointness, real
  spectrum, exact quadratic-form integral, and identification with the Ipek--Caticha generator;
* the energy-gap Heisenberg equation evaluated on every pair of continuum kernel variables;
* the canonical commutator evaluated at every continuum point on complex Schwartz space;
* real and complex infinite Hermite reconstructions converging at every point, obtained by
  continuously evaluating the already-proved convergence in the Schwartz topology;
* countable and measure-theoretic Rayleigh--Ritz inequalities expressed using summable or integrable
  weighted energies rather than a formal divergent trace.

## Honest boundary

The 1979 paper develops one-dimensional matrix mechanics, finite computational truncations, and the
large-quantum-number/WKB limit.  It explicitly lists continuum phenomena as future work.  Therefore
the pointwise Schwartz, countably infinite Hilbert-space, and measure-theoretic continuum results
below are extensions of its program, not results attributed to the paper itself.  The multiplication
Hamiltonian is a spectral realization, not a diagonalization theorem for arbitrary differential
Hamiltonians.  No unregularized `Tr H` on an infinite Hilbert space is introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry
open MeasureTheory LinearPMap ComplexConjugate
open QuantumMechanics.SpaceDHilbertSpace

/-! ## Countably infinite energy representation -/

/-- The genuine infinite energy carrier `ℓ²(ℕ,ℂ)`, not a finite matrix truncation. -/
abbrev InfiniteEnergySpace := L2Sequence ℕ

/-- The maximal diagonal Hamiltonian with prescribed real energy levels. -/
def infiniteEnergyHamiltonian (energy : ℕ → ℝ) :
    InfiniteEnergySpace →ₗ.[ℂ] InfiniteEnergySpace :=
  diagonalOperator energy

/-- A real diagonal energy family defines a self-adjoint operator on its maximal domain. -/
theorem infiniteEnergyHamiltonian_isSelfAdjoint (energy : ℕ → ℝ) :
    IsSelfAdjoint (infiniteEnergyHamiltonian energy) :=
  diagonalOperator_isSelfAdjoint energy

/-- Klein--Li Eq. (2.3) on the genuine countable energy basis. -/
theorem infiniteEnergyHamiltonian_basis (energy : ℕ → ℝ) (n : ℕ) :
    infiniteEnergyHamiltonian energy
        ⟨sequenceHilbertBasis ℕ n, sequenceHilbertBasis_mem_domain energy n⟩ =
      (energy n : ℂ) • sequenceHilbertBasis ℕ n :=
  diagonalOperator_basis energy n

/-- The countable energy basis reconstructs every vector in `ℓ²(ℕ,ℂ)`. -/
theorem infiniteEnergyBasis_complete (psi : InfiniteEnergySpace) :
    HasSum (fun n => (sequenceHilbertBasis ℕ).repr psi n •
      sequenceHilbertBasis ℕ n) psi :=
  (sequenceHilbertBasis ℕ).hasSum_repr psi

/-! ## Genuine continuum energy representation -/

/-- A real dispersion or energy function, regarded as a complex multiplication symbol. -/
def continuumEnergySymbol {d : ℕ} (energy : Space d → ℝ) : Space d → ℂ :=
  fun q => (energy q : ℂ)

/-- Measurability passes from a real continuum dispersion to its complex embedding. -/
lemma continuumEnergySymbol_aestronglyMeasurable {d : ℕ} (energy : Space d → ℝ)
    (henergy : AEStronglyMeasurable energy) :
    AEStronglyMeasurable (continuumEnergySymbol energy) := by
  exact Complex.ofRealCLM.continuous.comp_aestronglyMeasurable henergy

/-- The maximal-domain energy multiplication operator on the actual continuum Hilbert space
`L²(Space d, ℂ)`. -/
def continuumEnergyHamiltonian {d : ℕ} (energy : Space d → ℝ) :
    QuantumMechanics.SpaceDHilbertSpace d →ₗ.[ℂ]
      QuantumMechanics.SpaceDHilbertSpace d :=
  mulOperator MeasureTheory.volume (continuumEnergySymbol energy)

/-- The continuum Hamiltonian acts almost everywhere by pointwise multiplication with the energy. -/
lemma continuumEnergyHamiltonian_apply_ae {d : ℕ} (energy : Space d → ℝ)
    (psi : (continuumEnergyHamiltonian energy).domain) :
    continuumEnergyHamiltonian energy psi =ᵐ[volume]
      continuumEnergySymbol energy • psi :=
  mulOperator_apply_ae psi

/-- The continuum energy symbol is real under complex conjugation. -/
lemma continuumEnergySymbol_conj {d : ℕ} (energy : Space d → ℝ) :
    conj ∘ continuumEnergySymbol energy = continuumEnergySymbol energy := by
  funext q
  simp [continuumEnergySymbol]

/-- **Continuum Klein Hamiltonian.**  A measurable real energy dispersion gives a maximal
self-adjoint operator on genuine continuum `L²`; no discrete spectral truncation is used. -/
theorem continuumEnergyHamiltonian_isSelfAdjoint {d : ℕ} (energy : Space d → ℝ)
    (henergy : AEStronglyMeasurable energy) :
    IsSelfAdjoint (continuumEnergyHamiltonian energy) :=
  mulOperator_isSelfAdjoint_ofReal
    (continuumEnergySymbol_aestronglyMeasurable energy henergy)
    (continuumEnergySymbol_conj energy)

/-- The spectrum of the self-adjoint continuum energy Hamiltonian is real. -/
theorem continuumEnergyHamiltonian_spectrum_real {d : ℕ} (energy : Space d → ℝ)
    (henergy : AEStronglyMeasurable energy) :
    σ (continuumEnergyHamiltonian energy) ⊆ Set.range Complex.ofReal :=
  LinearPMap.IsSelfAdjoint.spectrum_real
    (continuumEnergyHamiltonian_isSelfAdjoint energy henergy)

/-- The continuum Klein energy Hamiltonian is exactly the energy-diagonal special case of the
existing Ipek--Caticha continuum generator (`N = 1`, shift `= 0`). -/
theorem continuumEnergyHamiltonian_eq_caticha {d : ℕ} (energy : Space d → ℝ) :
    continuumEnergyHamiltonian energy =
      Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator
        1 0 (continuumEnergySymbol energy) (fun _ => 0) := by
  have hsymbol :
      Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.catichaMultiplicationSymbol
          1 0 (continuumEnergySymbol energy) (fun _ => 0) =
        continuumEnergySymbol energy := by
    funext q
    simp [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.catichaMultiplicationSymbol]
  simp only [continuumEnergyHamiltonian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator,
    hsymbol]

/-- The quadratic form of the continuum Hamiltonian is the integral of the pointwise energy
density `E(q)|ψ(q)|²`.  The equality is meaningful for every vector in the maximal operator domain. -/
theorem continuumEnergy_expectation_eq_integral {d : ℕ} (energy : Space d → ℝ)
    (psi : (continuumEnergyHamiltonian energy).domain) :
    inner ℂ psi.1 (continuumEnergyHamiltonian energy psi) =
      ∫ q, ((energy q * ‖psi.1 q‖ ^ 2 : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuumEnergyHamiltonian_apply_ae energy psi] with q hq
  rw [hq]
  simp [continuumEnergySymbol, RCLike.inner_apply]
  rw [mul_assoc, Complex.mul_conj']

/-! ## Energy-representation Heisenberg equation -/

/-- The `(n,m)` coefficient of `[X,H]` when `H` is diagonal in the energy basis. -/
def energyCommutatorCoefficient (energy : ℕ → ℝ)
    (X : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ :=
  X n m * (energy m : ℂ) - (energy n : ℂ) * X n m

/-- A diagonal Hamiltonian converts the commutator coefficient into the energy gap. -/
lemma energyCommutatorCoefficient_eq_gap (energy : ℕ → ℝ)
    (X : ℕ → ℕ → ℂ) (n m : ℕ) :
    energyCommutatorCoefficient energy X n m =
      ((energy m - energy n : ℝ) : ℂ) * X n m := by
  simp [energyCommutatorCoefficient]
  ring

/-- Klein--Li Eq. (4.8): `[X,H] = iP` at one pair of countable energy indices is exactly
`(E_m-E_n)X_nm = iP_nm`. -/
theorem pointwiseHeisenberg_iff_energyGap (energy : ℕ → ℝ)
    (X P : ℕ → ℕ → ℂ) (n m : ℕ) :
    energyCommutatorCoefficient energy X n m = Complex.I * P n m ↔
      ((energy m - energy n : ℝ) : ℂ) * X n m = Complex.I * P n m := by
  rw [energyCommutatorCoefficient_eq_gap]

/-- The pointwise commutator kernel `[X,H](q,r)` for a general continuum energy carrier. -/
def continuumEnergyCommutatorKernel {A : Type*} (energy : A → ℝ)
    (X : A → A → ℂ) (q r : A) : ℂ :=
  X q r * (energy r : ℂ) - (energy q : ℂ) * X q r

/-- On every pair of continuum energy points, the commutator kernel is the energy gap times the
operator kernel. -/
lemma continuumEnergyCommutatorKernel_eq_gap {A : Type*} (energy : A → ℝ)
    (X : A → A → ℂ) (q r : A) :
    continuumEnergyCommutatorKernel energy X q r =
      ((energy r - energy q : ℝ) : ℂ) * X q r := by
  simp [continuumEnergyCommutatorKernel]
  ring

/-- **Continuum pointwise Klein--Li equation.**  The energy-representation Heisenberg equation
holds exactly at each kernel pair `(q,r)`, not only after integration or finite projection. -/
theorem continuumHeisenberg_iff_energyGap {A : Type*} (energy : A → ℝ)
    (X P : A → A → ℂ) (q r : A) :
    continuumEnergyCommutatorKernel energy X q r = Complex.I * P q r ↔
      ((energy r - energy q : ℝ) : ℂ) * X q r = Complex.I * P q r := by
  rw [continuumEnergyCommutatorKernel_eq_gap]

/-! ## Continuum pointwise canonical relation -/

open QuantumMechanics.OneDimension Constants

/-- The canonical Schwartz-space commutator holds after evaluation at every continuum point.
This is the pointwise analytic form of Klein--Li Eq. (2.2), with `ℏ` restored. -/
theorem canonicalCommutator_pointwise (psi : SchwartzMap ℝ ℂ) (x : ℝ) :
    (positionOperatorSchwartz (momentumOperatorSchwartz psi) -
      momentumOperatorSchwartz (positionOperatorSchwartz psi)) x =
      (Complex.I * ℏ) * psi x := by
  have h := positionOperatorSchwartz_commutation_momentumOperatorSchwartz psi
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f x) h

/-- Continuous evaluation at one point of a real Schwartz function. -/
def pointEvaluation (x : ℝ) : SchwartzMap ℝ ℝ →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℝ ℝ ℝ)

/-- **Infinite pointwise Hermite completeness.**  Every real Schwartz function is reconstructed at
every `x : ℝ` by its full Hermite series.  This follows from convergence in the stronger Schwartz
topology and is not a finite-cutoff statement. -/
theorem hermiteExpansion_hasSum_pointwise (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    HasSum (fun n => hermiteCoeff1D n f * hermiteFunction n x) (f x) := by
  have h := (schwartz_hermite_hasSum f).map (pointEvaluation x)
    (pointEvaluation x).continuous
  exact h.congr fun n => by
    simp [pointEvaluation, schwartzHermiteBasis1D_apply]

/-- Real part of a complex Schwartz function, retained in Schwartz space. -/
def schwartzRealPart (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f

/-- Imaginary part of a complex Schwartz function, retained in Schwartz space. -/
def schwartzImagPart (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f

/-- Complex Hermite coefficient obtained from the already-proved real and imaginary coefficients. -/
def complexHermiteCoeff1D (n : ℕ) (f : SchwartzMap ℝ ℂ) : ℂ :=
  (hermiteCoeff1D n (schwartzRealPart f) : ℂ) +
    Complex.I * (hermiteCoeff1D n (schwartzImagPart f) : ℂ)

/-- Continuous real-Schwartz point evaluation followed by complex embedding. -/
def pointEvaluationRealToComplex (x : ℝ) : SchwartzMap ℝ ℝ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((BoundedContinuousFunction.evalCLM ℝ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℝ ℝ ℝ))

/-- Continuous real-Schwartz point evaluation into the imaginary complex axis. -/
def pointEvaluationImaginary (x : ℝ) : SchwartzMap ℝ ℝ →L[ℝ] ℂ :=
  (Complex.I • Complex.ofRealCLM).comp
    ((BoundedContinuousFunction.evalCLM ℝ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℝ ℝ ℝ))

/-- **Complex infinite pointwise Hermite completeness.**  Every complex Schwartz wavefunction is
reconstructed at every continuum point by its full complex Hermite series. -/
theorem complexHermiteExpansion_hasSum_pointwise (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasSum (fun n => complexHermiteCoeff1D n f * hermiteFunction n x) (f x) := by
  have hre := (schwartz_hermite_hasSum (schwartzRealPart f)).map
    (pointEvaluationRealToComplex x) (pointEvaluationRealToComplex x).continuous
  have him := (schwartz_hermite_hasSum (schwartzImagPart f)).map
    (pointEvaluationImaginary x) (pointEvaluationImaginary x).continuous
  have hsum := hre.add him
  convert hsum using 1
  · funext n
    simp [pointEvaluationRealToComplex, pointEvaluationImaginary, complexHermiteCoeff1D,
      schwartzHermiteBasis1D_apply]
    ring
  · simp [pointEvaluationRealToComplex, pointEvaluationImaginary, schwartzRealPart,
      schwartzImagPart]
    simpa [mul_comm] using (Complex.re_add_im (f x)).symm

/-! ## Countably infinite variational bound -/

/-- A summable spectral trial expectation on an arbitrary countable or infinite index carrier. -/
def countableSpectralTrialEnergy {index : Type*}
    (p energy : index → ℝ) : ℝ :=
  ∑' i, p i * energy i

/-- **Countable Rayleigh--Ritz bound.**  A nonnegative normalized summable weight cannot have
expected energy below a common spectral lower bound.  Explicit summability replaces the formal
infinite trace appearing in a naive extension of Klein--Li's finite trace variation. -/
theorem countable_rayleighRitz {index : Type*}
    (p energy : index → ℝ) (E0 : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : HasSum p 1)
    (henergy : Summable (fun i => p i * energy i))
    (hground : ∀ i, E0 ≤ energy i) :
    E0 ≤ countableSpectralTrialEnergy p energy := by
  have hconst : Summable (fun i => p i * E0) := by
    simpa [mul_comm] using (hpSum.mul_left E0).summable
  have hle : (∑' i, p i * E0) ≤ ∑' i, p i * energy i :=
    Summable.tsum_le_tsum
      (fun i => mul_le_mul_of_nonneg_left (hground i) (hp i)) hconst henergy
  calc
    E0 = (∑' i, p i) * E0 := by rw [hpSum.tsum_eq, one_mul]
    _ = ∑' i, p i * E0 := by rw [tsum_mul_right]
    _ ≤ ∑' i, p i * energy i := hle
    _ = countableSpectralTrialEnergy p energy := rfl

/-! ## Measure-theoretic continuum variational bound -/

/-- The continuum trial energy on an arbitrary measured spectral carrier. -/
def continuumSpectralTrialEnergy {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (p energy : A → ℝ) : ℝ :=
  ∫ a, p a * energy a ∂mu

/-- **Continuum Rayleigh--Ritz bound.**  A normalized nonnegative integrable spectral density has
expectation at least the almost-everywhere lower spectral bound. -/
theorem continuum_rayleighRitz {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (p energy : A → ℝ) (E0 : ℝ)
    (hp : ∀ᵐ a ∂mu, 0 ≤ p a) (hpInt : Integrable p mu)
    (hpNorm : ∫ a, p a ∂mu = 1)
    (henergy : Integrable (fun a => p a * energy a) mu)
    (hground : ∀ᵐ a ∂mu, E0 ≤ energy a) :
    E0 ≤ continuumSpectralTrialEnergy mu p energy := by
  have hconst : Integrable (fun a => p a * E0) mu := hpInt.mul_const E0
  have hle : (∫ a, p a * E0 ∂mu) ≤ ∫ a, p a * energy a ∂mu := by
    refine integral_mono_ae hconst henergy ?_
    filter_upwards [hp, hground] with a hpa hEa
    exact mul_le_mul_of_nonneg_left hEa hpa
  calc
    E0 = (∫ a, p a ∂mu) * E0 := by rw [hpNorm, one_mul]
    _ = ∫ a, p a * E0 ∂mu := by rw [integral_mul_const]
    _ ≤ ∫ a, p a * energy a ∂mu := hle
    _ = continuumSpectralTrialEnergy mu p energy := rfl

/-- Born probability density of a represented continuum wavefunction. -/
def wavefunctionProbabilityDensity {A : Type*} (psi : A → ℂ) (a : A) : ℝ :=
  ‖psi a‖ ^ 2

lemma wavefunctionProbabilityDensity_nonneg {A : Type*} (psi : A → ℂ) (a : A) :
    0 ≤ wavefunctionProbabilityDensity psi a :=
  sq_nonneg _

/-- Rayleigh--Ritz specialized to the normalized Born density `|ψ|²` of a continuum
wavefunction representative. -/
theorem continuum_wavefunction_rayleighRitz {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (psi : A → ℂ) (energy : A → ℝ) (E0 : ℝ)
    (hpsiInt : Integrable (wavefunctionProbabilityDensity psi) mu)
    (hpsiNorm : ∫ a, wavefunctionProbabilityDensity psi a ∂mu = 1)
    (henergy : Integrable
      (fun a => wavefunctionProbabilityDensity psi a * energy a) mu)
    (hground : ∀ᵐ a ∂mu, E0 ≤ energy a) :
    E0 ≤ continuumSpectralTrialEnergy mu
      (wavefunctionProbabilityDensity psi) energy :=
  continuum_rayleighRitz mu (wavefunctionProbabilityDensity psi) energy E0
    (Filter.Eventually.of_forall (wavefunctionProbabilityDensity_nonneg psi))
    hpsiInt hpsiNorm henergy hground

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.infiniteEnergyHamiltonian_isSelfAdjoint where
  formalizes @ "claim:klein-li-energy-representation-has-a-genuine-countably-infinite-self-adjoint-diagonal-hamiltonian",
  supported_by @ "paper:klein-li-1979-variational-principles-heisenberg-matrix-mechanics",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:continuum-hilbert-space-extension-using-the-repositorys-maximal-diagonal-operator-not-a-theorem-stated-in-the-1979-paper"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.infiniteEnergyHamiltonian_basis where
  formalizes @ "claim:klein-li-energy-eigenvalue-equation-holds-on-every-countable-energy-basis-vector",
  supported_by @ "paper:klein-li-1979-variational-principles-heisenberg-matrix-mechanics",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.infiniteEnergyBasis_complete where
  formalizes @ "claim:the-countable-klein-li-energy-basis-reconstructs-every-l2-state",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:genuine-l2-hilbert-basis-completeness-not-a-finite-matrix-truncation"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_isSelfAdjoint where
  formalizes @ "claim:a-measurable-real-continuum-klein-energy-dispersion-defines-a-maximal-self-adjoint-l2-hamiltonian",
  supported_by @ "lean:QuantumMechanics.SpaceDHilbertSpace.mulOperator_isSelfAdjoint_ofReal",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:genuine-continuum-multiplication-operator-theorem-not-a-discrete-basis-or-general-diagonalization-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_spectrum_real where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_isSelfAdjoint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.TypeIIIUnboundedDynamics.spectrum_real",
  formalizes @ "claim:the-continuum-klein-energy-hamiltonian-has-real-spectrum",
  requires @ "claim:a-measurable-real-continuum-klein-energy-dispersion-defines-a-maximal-self-adjoint-l2-hamiltonian",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_eq_caticha where
  formalizes @ "claim:the-continuum-klein-energy-hamiltonian-is-the-energy-diagonal-special-case-of-the-ipek-caticha-continuum-generator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:identification-of-the-shared-multiplication-operator-carrier-not-a-diagonalization-of-an-arbitrary-functional-differential-generator"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergy_expectation_eq_integral where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_apply_ae",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-continuum-klein-hamiltonian-quadratic-form-is-the-integral-of-pointwise-energy-times-born-density",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:holds-for-vectors-in-the-maximal-multiplication-operator-domain"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.pointwiseHeisenberg_iff_energyGap where
  formalizes @ "claim:klein-li-equation-4-8-is-the-pointwise-energy-gap-form-of-the-heisenberg-equation",
  supported_by @ "paper:klein-li-1979-variational-principles-heisenberg-matrix-mechanics",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumHeisenberg_iff_energyGap where
  formalizes @ "claim:the-klein-li-energy-gap-heisenberg-equation-holds-pointwise-on-every-pair-of-continuum-energy-variables",
  supported_by @ "paper:klein-li-1979-variational-principles-heisenberg-matrix-mechanics",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:pointwise-kernel-extension-of-equation-4-8-not-an-operator-kernel-existence-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.canonicalCommutator_pointwise where
  formalizes @ "claim:the-canonical-position-momentum-commutator-holds-at-every-continuum-point-on-schwartz-space",
  supported_by @ "paper:klein-li-1979-variational-principles-heisenberg-matrix-mechanics",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:schwartz-domain-pointwise-realization-of-the-paper-kinematical-constraint"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.hermiteExpansion_hasSum_pointwise where
  formalizes @ "claim:the-full-infinite-hermite-expansion-reconstructs-every-real-schwartz-function-at-every-point",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:repository-continuum-extension-of-klein-li-completeness-and-large-n-analysis-not-a-result-claimed-in-the-paper"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.complexHermiteExpansion_hasSum_pointwise where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-full-infinite-complex-hermite-expansion-reconstructs-every-complex-schwartz-wavefunction-at-every-point",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:pointwise-complex-schwartz-convergence-derived-from-the-repositorys-schwartz-topology-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.countable_rayleighRitz where
  formalizes @ "claim:a-normalized-countable-spectral-trial-state-has-energy-at-least-the-common-spectral-lower-bound",
  supported_by @ "paper:klein-li-1979-variational-principles-heisenberg-matrix-mechanics",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:requires-summability-and-does-not-use-or-assert-an-unregularized-infinite-trace"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuum_rayleighRitz where
  formalizes @ "claim:a-normalized-nonnegative-continuum-spectral-density-has-energy-at-least-its-almost-everywhere-spectral-lower-bound",
  supported_by @ "paper:rayleigh-ritz-variational-principle",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:requires-bochner-integrability-normalization-and-an-almost-everywhere-lower-bound"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuum_wavefunction_rayleighRitz where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuum_rayleighRitz",
  formalizes @ "claim:a-normalized-continuum-born-density-has-energy-at-least-the-almost-everywhere-ground-energy",
  requires @ "claim:a-normalized-nonnegative-continuum-spectral-density-has-energy-at-least-its-almost-everywhere-spectral-lower-bound",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:wavefunction-representative-form-requires-integrability-of-the-born-and-energy-densities"

zil_file_contract physlib.kleinVariationalHeisenbergContinuum where
  promises "Klein--Li energy-representation matrix mechanics is realized both on a genuine countably infinite self-adjoint diagonal Hamiltonian and on a maximal self-adjoint continuum L2 multiplication Hamiltonian with real spectrum.  The latter is exactly the energy-diagonal Ipek--Caticha continuum generator, and its quadratic form is the integral of the pointwise energy density.  The energy-gap Heisenberg equation holds on every pair of continuum kernel variables; the canonical commutator holds at every continuum point on complex Schwartz space; full real and complex Hermite series reconstruct wavefunctions pointwise; and countable plus measure-theoretic Born-density Rayleigh--Ritz inequalities replace any formal infinite trace."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.diagonalOperator_isSelfAdjoint",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.diagonalOperator_basis",
    "lean:QuantumMechanics.SpaceDHilbertSpace.mulOperator_isSelfAdjoint_ofReal",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator",
    "lean:MeasureTheory.integral_mono_ae",
    "lean:QuantumMechanics.OneDimension.positionOperatorSchwartz_commutation_momentumOperatorSchwartz",
    "lean:schwartz_hermite_hasSum"]
  forbids_substitutes ["a finite matrix truncation relabeled as an infinite energy representation",
    "an unregularized infinite trace used as a convergent variational functional",
    "attributing the repository continuum extension to Klein and Li's 1979 paper"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.infiniteEnergyHamiltonian_isSelfAdjoint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.infiniteEnergyHamiltonian_basis,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.infiniteEnergyBasis_complete,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_isSelfAdjoint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_spectrum_real,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergyHamiltonian_eq_caticha,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumEnergy_expectation_eq_integral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.pointwiseHeisenberg_iff_energyGap,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuumHeisenberg_iff_energyGap,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.canonicalCommutator_pointwise,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.hermiteExpansion_hasSum_pointwise,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.complexHermiteExpansion_hasSum_pointwise,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.countable_rayleighRitz,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuum_rayleighRitz,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KleinVariationalHeisenbergContinuum.continuum_wavefunction_rayleighRitz]

/- ZIL-END -/
