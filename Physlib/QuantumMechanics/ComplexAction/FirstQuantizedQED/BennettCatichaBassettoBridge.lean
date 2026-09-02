/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaIntrinsicMaxwellGreen
public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly
public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bennett--Bassetto--Caticha bridge to curved-spacetime QED carriers

This module supplies the missing typed links between several distinct layers:

1. Bennett's parameterized first-quantized electrodynamics: Fourier transform
   in the invariant evolution parameter carries the integral fixed-point
   equation (Bennett, Eqs. 64--67) to an inhomogeneous Bethe--Salpeter equation.
2. Bassetto--Ciccariello--Tonin's equal-mass scalar ladder result: a
   vacuum-like Bethe--Salpeter eigenstate has a nonzero lightlike continuation
   with the same eigenvalue, subject to their analytic Fredholm construction.
3. Caticha's functional Schrödinger carrier and the repository's existing
   global intrinsic Maxwell Green/Hadamard carrier.
4. Bennett's relativistic spin--statistics result: antisymmetry is preserved
   by the parametrized two-particle evolution and its quadratic semiclassical
   current is exchange-even.
5. Rasheed's nonlinear electrodynamics coupled to a stationary black hole:
   the excitation `G = aF + b⋆F` carries the conserved charge and the
   nonlinear horizon-variation terms cancel to the usual first law.

The analytical steps are deliberately represented by explicit intertwining
data. In particular, this file does not assert that arbitrary kernels admit
the Fourier interchange used by Bennett, that arbitrary vacuum-like states
have Bassetto's analytic lightlike continuation, or that an arbitrary curved
spacetime supplies Green operators or a Hadamard state. It proves what follows
once those paper-specific hypotheses are supplied.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3,
  especially Eqs. 1--6, 47, 49--51, and 64--67.
* A. F. Bennett, *Spin-Statistics Connection for Relativistic Quantum
  Mechanics*, Found. Phys. **45** (2015) 370--390.
* D. A. Rasheed, *Non-Linear Electrodynamics: Zeroth and First Laws of
  Black Hole Mechanics*, arXiv:hep-th/9702087v2, especially Eqs.
  2.6--2.11 and 5.1--5.16.
* A. Bassetto, F. Ciccariello, and M. Tonin, *On the connection between
  vacuum-like and light-like solutions of the Bethe--Salpeter equation*
  (1965), especially Eqs. 3--9.
* A. Caticha, entropic dynamics of quantum fields and gauge coupling; the
  continuum functional and curved Maxwell carriers imported above.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle FiberBundle Filter Module
open scoped FourierTransform InnerProductSpace Manifold Topology

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge

open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly
open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction
open PseudoRiemannianMetric

universe uTau uMass uState uFc uSc uFr uSr uXi v w

/-! ## A. Bennett's invariant-parameter Fourier transform -/

/-- The algebraic form `Psi = Psi_free + K Psi` of an inhomogeneous
Bethe--Salpeter equation. Keeping this predicate independent of a particular
integral realization lets the established propagator kernels be reused. -/
def SatisfiesInhomogeneousBetheSalpeter
    {State : Type*} [AddCommGroup State] [Module ℂ State]
    (kernel : State →ₗ[ℂ] State) (free full : State) : Prop :=
  full = free + kernel full

/-- Data certifying Bennett's Eqs. 64--67: Fourier transformation in `tau`
intertwines the invariant-parameter interaction kernel with the fixed-mass
Bethe--Salpeter kernel. Analytic existence and exchange of the transform with
the integral are intentionally fields of this structure. -/
structure BennettTauFourierData
    (StateTau : Type uTau) (StateMass : Type uMass)
    [AddCommGroup StateTau] [Module ℂ StateTau]
    [AddCommGroup StateMass] [Module ℂ StateMass] where
  tauKernel : StateTau →ₗ[ℂ] StateTau
  massKernel : ℂ → StateMass →ₗ[ℂ] StateMass
  tauFourier : ℂ → StateTau →ₗ[ℂ] StateMass
  kernel_intertwines : ∀ m psi,
    tauFourier m (tauKernel psi) = massKernel m (tauFourier m psi)

/-- Evaluation at real mass `m` of the actual vector-valued Schwartz Fourier
transform in Bennett's invariant parameter `tau`. Complex masses in the
generic bridge are restricted here to their real mass slice, as in Bennett's
bound-state Fourier transform. -/
noncomputable def bennettSchwartzTauFourierAt
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (m : ℝ) : SchwartzMap ℝ State →ₗ[ℂ] State where
  toFun psi := (𝓕 psi) m
  map_add' psi phi := by simp
  map_smul' c psi := by simp

/-- A `tau`-independent continuous interaction operator acts pointwise on
Schwartz histories. This is Bennett's assumption that the electromagnetic
potential and interaction kernel have no explicit `tau` dependence. -/
noncomputable def bennettTauIndependentKernel
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℂ State]
    (kernel : State →L[ℂ] State) :
    SchwartzMap ℝ State →ₗ[ℂ] SchwartzMap ℝ State :=
  (SchwartzMap.postcompCLM kernel).toLinearMap

/-- The actual vector-valued Schwartz Fourier transform commutes with every
`tau`-independent continuous complex-linear interaction operator. The proof is
the Bochner-integral/continuous-linear-map interchange already supplied by
Mathlib, together with Schwartz integrability. -/
lemma bennettSchwartzTauFourierAt_intertwines
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    (kernel : State →L[ℂ] State) (m : ℝ) (psi : SchwartzMap ℝ State) :
    bennettSchwartzTauFourierAt m
        (bennettTauIndependentKernel kernel psi) =
      kernel (bennettSchwartzTauFourierAt m psi) := by
  change (𝓕 (SchwartzMap.postcompCLM kernel psi)) m = kernel ((𝓕 psi) m)
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_eq, Real.fourier_eq]
  rw [← kernel.integral_comp_comm
    ((Real.fourierIntegral_convergent_iff m).2 psi.integrable)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with tau
  simp

/-- A concrete `BennettTauFourierData` instance for Schwartz histories and a
`tau`-independent continuous interaction. This discharges the abstract kernel
intertwining field from existing Fourier/Bochner infrastructure. -/
noncomputable def bennettSchwartzTauFourierData
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    (kernel : State →L[ℂ] State) :
    BennettTauFourierData (SchwartzMap ℝ State) State where
  tauKernel := bennettTauIndependentKernel kernel
  massKernel := fun _ => kernel.toLinearMap
  tauFourier := fun m => bennettSchwartzTauFourierAt m.re
  kernel_intertwines := fun m psi =>
    bennettSchwartzTauFourierAt_intertwines kernel m.re psi

/-- **Bennett Eqs. 64--67.** A solution of the invariant-parameter integral
equation is carried by the certified `tau`-Fourier transform to an
inhomogeneous fixed-mass Bethe--Salpeter solution. -/
lemma bennett_tauFourier_carries_integralEquation
    {StateTau : Type uTau} {StateMass : Type uMass}
    [AddCommGroup StateTau] [Module ℂ StateTau]
    [AddCommGroup StateMass] [Module ℂ StateMass]
    (B : BennettTauFourierData StateTau StateMass)
    (free full : StateTau)
    (hfull : SatisfiesInhomogeneousBetheSalpeter B.tauKernel free full)
    (m : ℂ) :
    SatisfiesInhomogeneousBetheSalpeter (B.massKernel m)
      (B.tauFourier m free) (B.tauFourier m full) := by
  unfold SatisfiesInhomogeneousBetheSalpeter at hfull ⊢
  calc
    B.tauFourier m full = B.tauFourier m (free + B.tauKernel full) :=
      congrArg (B.tauFourier m) hfull
    _ = B.tauFourier m free + B.tauFourier m (B.tauKernel full) := map_add _ _ _
    _ = B.tauFourier m free + B.massKernel m (B.tauFourier m full) := by
      rw [B.kernel_intertwines]

/-- Concrete Bennett Eq. 64--67 for vector-valued Schwartz histories. No
Fourier-intertwining certificate is supplied by the caller: `tau` independence
of the continuous interaction operator and Bochner integration prove it. -/
lemma bennettSchwartzTauFourier_carries_integralEquation
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    (kernel : State →L[ℂ] State)
    (free full : SchwartzMap ℝ State)
    (hfull : SatisfiesInhomogeneousBetheSalpeter
      (bennettTauIndependentKernel kernel) free full)
    (m : ℝ) :
    SatisfiesInhomogeneousBetheSalpeter kernel.toLinearMap
      ((𝓕 free) m) ((𝓕 full) m) := by
  simpa [bennettSchwartzTauFourierData, bennettSchwartzTauFourierAt] using
    bennett_tauFourier_carries_integralEquation
      (bennettSchwartzTauFourierData kernel) free full hfull (m : ℂ)

/-! ## B. Bassetto's vacuum-like to lightlike continuation -/

/-- A nonzero Bethe--Salpeter state with kernel eigenvalue `lambda`. -/
def IsBetheSalpeterEigenstate
    {State : Type*} [AddCommGroup State] [Module ℂ State]
    (kernel : State →ₗ[ℂ] State) (lambda : ℂ) (psi : State) : Prop :=
  psi ≠ 0 ∧ kernel psi = lambda • psi

/-- **Bassetto Eq. 6, finite-dimensional Fredholm solvability.** A coefficient
source lies in the range of the recurrence operator exactly when it is
orthogonal to every obstruction in the kernel of the adjoint. This is the
paper's Fredholm orthogonality condition, derived from the existing
range/adjoint-kernel theorem rather than stored as a certificate field. -/
lemma bassetto_fredholmSolvability_iff
    {State : Type uState} [NormedAddCommGroup State]
    [InnerProductSpace ℂ State] [FiniteDimensional ℂ State]
    (operator : State →ₗ[ℂ] State) (source : State) :
    source ∈ operator.range ↔
      ∀ obstruction : State, operator.adjoint obstruction = 0 →
        ⟪obstruction, source⟫_ℂ = 0 := by
  calc
    source ∈ operator.range ↔ source ∈ operator.rangeᗮᗮ := by
      rw [Submodule.orthogonal_orthogonal]
    _ ↔ source ∈ operator.adjoint.kerᗮ := by
      rw [operator.orthogonal_range]
    _ ↔ ∀ obstruction : State, operator.adjoint obstruction = 0 →
        ⟪obstruction, source⟫_ℂ = 0 := by
      rw [Submodule.mem_orthogonal]
      simp only [LinearMap.mem_ker]

/-- For a compact Bethe--Salpeter kernel and nonzero spectral parameter, the
Fredholm alternative says that failure of the eigenvalue condition makes the
coefficient equation uniquely solvable for every source. This discharges the
uniqueness half of Bassetto's recurrence away from the vacuum eigenvalue. -/
lemma bassetto_uniqueCoefficient_of_compact_of_not_eigenvalue
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    (kernel : State →L[ℂ] State) (lambda : ℂ)
    (hcompact : IsCompactOperator kernel) (hlambda : lambda ≠ 0)
    (hnotEigen : ¬ Module.End.HasEigenvalue kernel.toLinearMap lambda) :
    ∀ source : State, ∃! coefficient : State,
      (lambda • (1 : State →L[ℂ] State) - kernel) coefficient = source := by
  have hres : lambda ∈ resolventSet ℂ kernel :=
    (hcompact.hasEigenvalue_or_mem_resolventSet hlambda).resolve_left hnotEigen
  have hunit : IsUnit (lambda • (1 : State →L[ℂ] State) - kernel) := by
    simpa [spectrum.mem_resolventSet_iff,
      Algebra.algebraMap_eq_smul_one] using hres
  have hbij : Function.Bijective
      (lambda • (1 : State →L[ℂ] State) - kernel) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  intro source
  obtain ⟨coefficient, hcoefficient⟩ := hbij.2 source
  refine ⟨coefficient, hcoefficient, ?_⟩
  intro other hother
  exact hbij.1 (hother.trans hcoefficient.symm)

/-- A concrete finite-mode discretization of Cutkosky's Eq. 16 kernel.  Its
matrix entries are evaluations of the existing `cutkoskyKernel`; this does
not replace the paper's continuum integral operator. -/
noncomputable def cutkoskyFiniteModeKernelOperator
    {n : ℕ} (nodes : Fin n → ℝ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin (Matrix.of fun i j =>
      ((cutkoskyKernel (nodes i) (nodes j) : ℝ) : ℂ)))

/-- The finite-mode operator acts by the expected Cutkosky-kernel matrix
sum, so the discretization is connected definitionally to Eq. 16. -/
lemma cutkoskyFiniteModeKernelOperator_apply
    {n : ℕ} (nodes : Fin n → ℝ) (psi : Fin n → ℂ) (i : Fin n) :
    cutkoskyFiniteModeKernelOperator nodes psi i =
      ∑ j, ((cutkoskyKernel (nodes i) (nodes j) : ℝ) : ℂ) * psi j := by
  simp [cutkoskyFiniteModeKernelOperator, Matrix.mulVec, dotProduct]

/-- Every concrete finite-mode Cutkosky kernel is compact because its
finite-dimensional range is locally compact.  Unlike the abstract Fredholm
theorem above, the compactness premise is discharged here. -/
lemma cutkoskyFiniteModeKernelOperator_isCompact
    {n : ℕ} (nodes : Fin n → ℝ) :
    IsCompactOperator (cutkoskyFiniteModeKernelOperator nodes) :=
  isCompactOperator_of_locallyCompactSpace_dom _

/-- The compact Fredholm alternative specialized to the concrete finite-mode
Cutkosky kernel.  Away from a nonzero eigenvalue, every discretized recurrence
source has a unique coefficient. -/
lemma cutkoskyFiniteMode_uniqueCoefficient_of_not_eigenvalue
    {n : ℕ} (nodes : Fin n → ℝ) (lambda : ℂ)
    (hlambda : lambda ≠ 0)
    (hnotEigen : ¬ Module.End.HasEigenvalue
      (cutkoskyFiniteModeKernelOperator nodes).toLinearMap lambda) :
    ∀ source : Fin n → ℂ, ∃! coefficient : Fin n → ℂ,
      (lambda • (1 : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) -
        cutkoskyFiniteModeKernelOperator nodes) coefficient = source :=
  bassetto_uniqueCoefficient_of_compact_of_not_eigenvalue
    (cutkoskyFiniteModeKernelOperator nodes) lambda
    (cutkoskyFiniteModeKernelOperator_isCompact nodes) hlambda hnotEigen

/-! ### The continuum Cutkosky operator -/

/-- Cutkosky's real Eq. 16 kernel is exactly the outer-product factorization
used by the continuum operator: `R(z, zeta) = (1+z) (1+zeta)⁻¹`.  The cast to
`ℂ` is the scalar field of the `L²` carrier. -/
lemma cutkoskyKernel_eq_separable (z zeta : ℝ) :
    ((cutkoskyKernel z zeta : ℝ) : ℂ) =
      ((1 + z : ℝ) : ℂ) * (((1 + zeta : ℝ)⁻¹ : ℝ) : ℂ) := by
  simp [cutkoskyKernel, div_eq_mul_inv]

/-- A continuum realization of Cutkosky's separable kernel on an `L²` carrier.
The two vectors are the square-integrable representatives of `1 + z` and
`1 / (1 + z)`.  Keeping the `L²` witnesses as arguments makes the genuine
analytic requirement visible: the denominator must avoid its pole and both
factors must be square integrable on the chosen measure space. -/
noncomputable def cutkoskyContinuumKernelOperator
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (numerator denominatorInv : MeasureTheory.Lp ℂ 2 mu) :
    MeasureTheory.Lp ℂ 2 mu →L[ℂ] MeasureTheory.Lp ℂ 2 mu :=
  InnerProductSpace.rankOne ℂ numerator denominatorInv

/-- The continuum Cutkosky operator has rank at most one and is compact on
`L²`, independently of the dimension of the underlying measure space.  This
is the analytic Fredholm input that the former finite-mode realization could
only obtain from finite dimensionality. -/
lemma cutkoskyContinuumKernelOperator_isCompact
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (numerator denominatorInv : MeasureTheory.Lp ℂ 2 mu) :
    IsCompactOperator
      (cutkoskyContinuumKernelOperator mu numerator denominatorInv) := by
  rw [cutkoskyContinuumKernelOperator, InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom
      (innerSL ℂ denominatorInv)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ numerator)

/-- The continuum operator acts by the expected rank-one integral
coefficient.  `L².inner_def` identifies that coefficient with the Bochner
integral of the pointwise inner product, so this is a genuine continuum
integral operator rather than a matrix discretization. -/
lemma cutkoskyContinuumKernelOperator_apply
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (numerator denominatorInv psi : MeasureTheory.Lp ℂ 2 mu) :
    cutkoskyContinuumKernelOperator mu numerator denominatorInv psi =
      (∫ x, ⟪denominatorInv x, psi x⟫_ℂ ∂mu) • numerator := by
  rw [cutkoskyContinuumKernelOperator, InnerProductSpace.rankOne_apply,
    MeasureTheory.L2.inner_def]

/- Joint continuity of the rank-one construction on an arbitrary complex
inner-product space.  Factoring this generic statement out keeps typeclass
reduction for the `L²` specialization small under Lean 4.31. -/
private lemma rankOne_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {iota : Type*} {l : Filter iota}
    (x y : iota → E) (x0 y0 : E)
    (hx : Filter.Tendsto x l (nhds x0))
    (hy : Filter.Tendsto y l (nhds y0)) :
    Filter.Tendsto (fun i => InnerProductSpace.rankOne ℂ (x i) (y i)) l
      (nhds (InnerProductSpace.rankOne ℂ x0 y0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i =>
      ‖x i - x0‖ * ‖y i‖ + ‖x0‖ * ‖y i - y0‖) (fun i => norm_nonneg
      (InnerProductSpace.rankOne ℂ (x i) (y i) -
        InnerProductSpace.rankOne ℂ x0 y0)) (fun i => ?_) ?_
  · calc
      ‖InnerProductSpace.rankOne ℂ (x i) (y i) -
          InnerProductSpace.rankOne ℂ x0 y0‖
          = ‖InnerProductSpace.rankOne ℂ (x i - x0) (y i) +
              InnerProductSpace.rankOne ℂ x0 (y i - y0)‖ := by
              congr 1
              apply ContinuousLinearMap.ext
              intro z
              simp only [InnerProductSpace.rankOne_apply, inner_sub_left,
                sub_smul, add_apply, sub_apply]
              module
      _ ≤ ‖x i - x0‖ * ‖y i‖ + ‖x0‖ * ‖y i - y0‖ := by
          simpa only [InnerProductSpace.norm_rankOne] using
            norm_add_le
              (InnerProductSpace.rankOne ℂ (x i - x0) (y i))
              (InnerProductSpace.rankOne ℂ x0 (y i - y0))
  · have hx0 : Filter.Tendsto (fun i => ‖x i - x0‖) l (nhds 0) := by
      simpa using (hx.sub
        (tendsto_const_nhds : Filter.Tendsto (fun _ : iota => x0) l (nhds x0))).norm
    have hy0 : Filter.Tendsto (fun i => ‖y i - y0‖) l (nhds 0) := by
      simpa using (hy.sub
        (tendsto_const_nhds : Filter.Tendsto (fun _ : iota => y0) l (nhds y0))).norm
    simpa using (hx0.mul hy.norm).add
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : iota => ‖x0‖) l (nhds ‖x0‖)).mul hy0)

/-- Rank-one Cutkosky operators converge in operator norm whenever their two
`L²` factors converge.  This supplies the continuum limit criterion for
quadrature or cutoff approximants: convergence is reduced to convergence of
the numerator and reciprocal-denominator factors in `L²`. -/
lemma cutkoskyContinuumKernelOperator_tendsto
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    {ι : Type*} {l : Filter ι}
    (numerator denominatorInv : ι → MeasureTheory.Lp ℂ 2 mu)
    (numeratorLimit denominatorInvLimit : MeasureTheory.Lp ℂ 2 mu)
    (hNumerator : Filter.Tendsto numerator l (nhds numeratorLimit))
    (hDenominator : Filter.Tendsto denominatorInv l (nhds denominatorInvLimit)) :
    Filter.Tendsto
      (fun i => cutkoskyContinuumKernelOperator mu
        (numerator i) (denominatorInv i)) l
      (nhds (cutkoskyContinuumKernelOperator mu
        numeratorLimit denominatorInvLimit)) := by
  exact rankOne_tendsto numerator denominatorInv numeratorLimit
    denominatorInvLimit hNumerator hDenominator

/-! ### Concrete pole-free `L²` factors -/

/-- Lebesgue measure restricted to the symmetric Cutkosky interval
`[-r,r]`.  Mathlib's locally finite Lebesgue measure makes this a finite
measure, which is the natural continuum carrier for the relative-energy
coordinate. -/
abbrev cutkoskyIntervalMeasure (r : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (-r) r)

/-- The numerator factor `z ↦ 1+z` of Cutkosky Eq. 16, cast to the complex
scalar field of the wavefunction. -/
def cutkoskyNumeratorFactorFn (z : ℝ) : ℂ :=
  ((1 + z : ℝ) : ℂ)

/-- The reciprocal denominator factor `z ↦ (1+z)⁻¹` of Cutkosky Eq. 16.
On `[-r,r]` with `r<1`, its pole at `-1` lies strictly outside the carrier. -/
def cutkoskyDenominatorInvFactorFn (z : ℝ) : ℂ :=
  (((1 + z : ℝ)⁻¹ : ℝ) : ℂ)

/-- The actual Cutkosky numerator is square-integrable on every finite
symmetric interval.  The explicit bound is `|1+z| ≤ 1+r`. -/
lemma cutkoskyNumeratorFactorFn_memLp (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.MemLp cutkoskyNumeratorFactorFn 2
      (cutkoskyIntervalMeasure r) := by
  apply MeasureTheory.MemLp.of_bound (by
    exact (Complex.ofRealCLM.continuous.comp
      (continuous_const.add continuous_id)).aestronglyMeasurable) (1 + r)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
  simp only [cutkoskyNumeratorFactorFn, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [hz.1, hz.2]

/-- The actual reciprocal denominator is square-integrable on the pole-free
interval `[-r,r]`, `0≤r<1`.  Its uniform bound is `(1-r)⁻¹`. -/
lemma cutkoskyDenominatorInvFactorFn_memLp
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    MeasureTheory.MemLp cutkoskyDenominatorInvFactorFn 2
      (cutkoskyIntervalMeasure r) := by
  apply MeasureTheory.MemLp.of_bound (by
    have hmeas : Measurable cutkoskyDenominatorInvFactorFn := by
      unfold cutkoskyDenominatorInvFactorFn
      measurability
    exact hmeas.aestronglyMeasurable)
      ((1 - r)⁻¹)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
  have hden : 0 < 1 + z := by linarith [hz.1]
  have hfloor : 0 < 1 - r := by linarith
  simp only [cutkoskyDenominatorInvFactorFn, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr hden)]
  exact (inv_le_inv₀ hden hfloor).2 (by linarith [hz.1])

/-- The concrete `L²` numerator factor obtained from the proved `MemLp`
witness. -/
noncomputable def cutkoskyNumeratorFactorL2
    (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r) :=
  (cutkoskyNumeratorFactorFn_memLp r hr).toLp cutkoskyNumeratorFactorFn

/-- The concrete pole-free `L²` reciprocal-denominator factor. -/
noncomputable def cutkoskyDenominatorInvFactorL2
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r) :=
  (cutkoskyDenominatorInvFactorFn_memLp r hr hr1).toLp
    cutkoskyDenominatorInvFactorFn

/-- The numerator `L²` class has the advertised representative almost
everywhere on the restricted interval. -/
lemma cutkoskyNumeratorFactorL2_coeFn
    (r : ℝ) (hr : 0 ≤ r) :
    cutkoskyNumeratorFactorL2 r hr =ᵐ[cutkoskyIntervalMeasure r]
      cutkoskyNumeratorFactorFn :=
  MeasureTheory.MemLp.coeFn_toLp (cutkoskyNumeratorFactorFn_memLp r hr)

/-- The denominator `L²` class has the advertised reciprocal representative
almost everywhere on the pole-free interval. -/
lemma cutkoskyDenominatorInvFactorL2_coeFn
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    cutkoskyDenominatorInvFactorL2 r hr hr1
      =ᵐ[cutkoskyIntervalMeasure r] cutkoskyDenominatorInvFactorFn :=
  MeasureTheory.MemLp.coeFn_toLp
    (cutkoskyDenominatorInvFactorFn_memLp r hr hr1)

/-- The fully instantiated continuum Cutkosky operator on the pole-free
relative-energy interval.  Unlike the generic rank-one constructor, this
definition has no caller-supplied `L²` factors. -/
noncomputable def cutkoskyPoleFreeContinuumOperator
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r) →L[ℂ]
      MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r) :=
  cutkoskyContinuumKernelOperator (cutkoskyIntervalMeasure r)
    (cutkoskyNumeratorFactorL2 r hr)
    (cutkoskyDenominatorInvFactorL2 r hr hr1)

/-- The concrete pole-free continuum Cutkosky operator is compact.  All
measure-theoretic requirements are now discharged by the preceding `MemLp`
theorems. -/
lemma cutkoskyPoleFreeContinuumOperator_isCompact
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    IsCompactOperator (cutkoskyPoleFreeContinuumOperator r hr hr1) :=
  cutkoskyContinuumKernelOperator_isCompact (cutkoskyIntervalMeasure r)
    (cutkoskyNumeratorFactorL2 r hr)
    (cutkoskyDenominatorInvFactorL2 r hr hr1)

/-- The instantiated operator acts by the actual reciprocal-denominator
`L²` inner-product integral and multiplies the actual numerator factor. -/
lemma cutkoskyPoleFreeContinuumOperator_apply
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (psi : MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r)) :
    cutkoskyPoleFreeContinuumOperator r hr hr1 psi =
      (∫ z, ⟪cutkoskyDenominatorInvFactorL2 r hr hr1 z, psi z⟫_ℂ
          ∂cutkoskyIntervalMeasure r) •
        cutkoskyNumeratorFactorL2 r hr :=
  cutkoskyContinuumKernelOperator_apply (cutkoskyIntervalMeasure r)
    (cutkoskyNumeratorFactorL2 r hr)
    (cutkoskyDenominatorInvFactorL2 r hr hr1) psi

/-- The `L²` inner-product coefficient is the ordinary integral of the actual
reciprocal-denominator function against the wavefunction representative. -/
lemma cutkoskyPoleFree_inner_eq_denominatorIntegral
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (psi : MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r)) :
    (∫ z, ⟪cutkoskyDenominatorInvFactorL2 r hr hr1 z, psi z⟫_ℂ
        ∂cutkoskyIntervalMeasure r) =
      ∫ z, cutkoskyDenominatorInvFactorFn z * psi z
        ∂cutkoskyIntervalMeasure r := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [cutkoskyDenominatorInvFactorL2_coeFn r hr hr1] with z hz
  rw [hz]
  simp [cutkoskyDenominatorInvFactorFn, mul_comm]

/-- Representative-level action of the fully instantiated operator.  Almost
everywhere on `[-r,r]`, it is exactly the continuum integral with Cutkosky's
original Eq. 16 kernel `R(z,zeta)=(1+z)/(1+zeta)`. -/
lemma cutkoskyPoleFreeContinuumOperator_ae_eq_kernelIntegral
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (psi : MeasureTheory.Lp ℂ 2 (cutkoskyIntervalMeasure r)) :
    cutkoskyPoleFreeContinuumOperator r hr hr1 psi
      =ᵐ[cutkoskyIntervalMeasure r]
        fun z => ∫ zeta,
          ((cutkoskyKernel z zeta : ℝ) : ℂ) * psi zeta
            ∂cutkoskyIntervalMeasure r := by
  rw [cutkoskyPoleFreeContinuumOperator_apply r hr hr1 psi,
    cutkoskyPoleFree_inner_eq_denominatorIntegral r hr hr1 psi]
  filter_upwards [MeasureTheory.Lp.coeFn_smul
      (∫ z, cutkoskyDenominatorInvFactorFn z * psi z
        ∂cutkoskyIntervalMeasure r)
      (cutkoskyNumeratorFactorL2 r hr),
    cutkoskyNumeratorFactorL2_coeFn r hr] with z hsmul hnum
  rw [hsmul]
  change
    (∫ z, cutkoskyDenominatorInvFactorFn z * psi z
      ∂cutkoskyIntervalMeasure r) * cutkoskyNumeratorFactorL2 r hr z = _
  rw [hnum]
  rw [← MeasureTheory.integral_mul_const]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with zeta
  rw [cutkoskyKernel_eq_separable]
  simp only [cutkoskyNumeratorFactorFn, cutkoskyDenominatorInvFactorFn]
  ring

/-- Coefficient-level form of Bassetto--Ciccariello--Tonin's analytic
Fredholm construction. Their expansion in `epsilon = p dot P` is represented
by continuous linear coefficient operators. `coefficient_intertwines` is the
recurrence/Fredholm condition, while `summable` is the analytic convergence
condition; neither is hidden in the conclusion. -/
structure BassettoAnalyticFredholmData
    (State : Type uState) [NormedAddCommGroup State] [NormedSpace ℂ State]
    (vacuumKernel lightKernel : State →L[ℂ] State) where
  totalMomentum : Lorentz.Vector 3
  totalMomentum_ne_zero : totalMomentum ≠ 0
  totalMomentum_lightLike :
    Lorentz.Vector.causalCharacter totalMomentum = .lightLike
  coefficient : ℕ → State →L[ℂ] State
  coefficient_zero : coefficient 0 = ContinuousLinearMap.id ℂ State
  coefficient_intertwines : ∀ n psi,
    lightKernel (coefficient n psi) = coefficient n (vacuumKernel psi)
  summable : ∀ (epsilon : ℂ) (psi : State),
    Summable (fun n => epsilon ^ n • coefficient n psi)

/-- The full, normalized-at-order-zero analytic Bassetto series
`sum_n epsilon^n phi_n`, rather than a finite truncation. -/
noncomputable def bassettoAnalyticLightlikeSeries
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    {vacuumKernel lightKernel : State →L[ℂ] State}
    (D : BassettoAnalyticFredholmData State vacuumKernel lightKernel)
    (epsilon : ℂ) (psi : State) : State :=
  ∑' n, epsilon ^ n • D.coefficient n psi

/-- At expansion parameter zero, the analytic continuation returns exactly
the vacuum-like state. This proves the normalization encoded by Bassetto's
zeroth coefficient instead of accepting a separate state equality. -/
lemma bassettoAnalyticLightlikeSeries_zero
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    {vacuumKernel lightKernel : State →L[ℂ] State}
    (D : BassettoAnalyticFredholmData State vacuumKernel lightKernel)
    (psi : State) :
    bassettoAnalyticLightlikeSeries D 0 psi = psi := by
  unfold bassettoAnalyticLightlikeSeries
  calc
    ∑' n, (0 : ℂ) ^ n • D.coefficient n psi =
        (0 : ℂ) ^ 0 • D.coefficient 0 psi :=
      tsum_eq_single 0 (by
        intro n hn
        simp [hn])
    _ = psi := by rw [D.coefficient_zero]; simp

/-- The convergent analytic series intertwines the vacuum and lightlike
Bethe--Salpeter kernels. Continuity moves the lightlike kernel through the
infinite sum, and the coefficient recurrence identifies every term. -/
lemma bassettoAnalyticLightlikeSeries_intertwines
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    {vacuumKernel lightKernel : State →L[ℂ] State}
    (D : BassettoAnalyticFredholmData State vacuumKernel lightKernel)
    (epsilon : ℂ) (psi : State) :
    lightKernel (bassettoAnalyticLightlikeSeries D epsilon psi) =
      bassettoAnalyticLightlikeSeries D epsilon (vacuumKernel psi) := by
  unfold bassettoAnalyticLightlikeSeries
  rw [lightKernel.map_tsum (D.summable epsilon psi)]
  apply tsum_congr
  intro n
  rw [map_smul, D.coefficient_intertwines]

/-- **Bassetto Eqs. 3--9, analytic-series form.** A nonzero value of the
convergent Fredholm series has the same eigenvalue as its vacuum-like seed.
The only remaining nonvanishing premise is necessary: an analytic vector
family can have isolated zeros away from its normalized value at zero. -/
lemma bassettoAnalyticSeries_preserves_eigenvalue
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    {vacuumKernel lightKernel : State →L[ℂ] State}
    (D : BassettoAnalyticFredholmData State vacuumKernel lightKernel)
    (epsilon lambda : ℂ) (psi : State)
    (hpsi : IsBetheSalpeterEigenstate vacuumKernel.toLinearMap lambda psi)
    (hseries : bassettoAnalyticLightlikeSeries D epsilon psi ≠ 0) :
    IsBetheSalpeterEigenstate lightKernel.toLinearMap lambda
      (bassettoAnalyticLightlikeSeries D epsilon psi) := by
  refine ⟨hseries, ?_⟩
  have hvacuum : vacuumKernel psi = lambda • psi := hpsi.2
  rw [show lightKernel.toLinearMap
      (bassettoAnalyticLightlikeSeries D epsilon psi) =
      lightKernel (bassettoAnalyticLightlikeSeries D epsilon psi) from rfl,
    bassettoAnalyticLightlikeSeries_intertwines D epsilon psi, hvacuum]
  unfold bassettoAnalyticLightlikeSeries
  calc
    ∑' n, epsilon ^ n • D.coefficient n (lambda • psi) =
        ∑' n, lambda • (epsilon ^ n • D.coefficient n psi) := by
          apply tsum_congr
          intro n
          rw [map_smul]
          exact smul_comm _ _ _
    _ = lambda • ∑' n, epsilon ^ n • D.coefficient n psi :=
      tsum_const_smul'' lambda

/-- The analytic-series result together with Bassetto's explicit nonzero null
momentum. This is the paper's vacuum-like-to-light-like conclusion with the
analytic construction exposed coefficient by coefficient. -/
lemma bassettoAnalytic_vacuumLike_implies_lightLike_sameEigenvalue
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    {vacuumKernel lightKernel : State →L[ℂ] State}
    (D : BassettoAnalyticFredholmData State vacuumKernel lightKernel)
    (epsilon lambda : ℂ) (psi : State)
    (hpsi : IsBetheSalpeterEigenstate vacuumKernel.toLinearMap lambda psi)
    (hseries : bassettoAnalyticLightlikeSeries D epsilon psi ≠ 0) :
    D.totalMomentum ≠ 0 ∧
      Lorentz.Vector.minkowskiProduct D.totalMomentum D.totalMomentum = 0 ∧
      IsBetheSalpeterEigenstate lightKernel.toLinearMap lambda
        (bassettoAnalyticLightlikeSeries D epsilon psi) := by
  refine ⟨D.totalMomentum_ne_zero, ?_,
    bassettoAnalyticSeries_preserves_eigenvalue D epsilon lambda psi hpsi hseries⟩
  exact (Lorentz.Vector.lightLike_iff_norm_sq_zero D.totalMomentum).mp
    D.totalMomentum_lightLike

/-- Bennett's bound-state specialization of Eq. 66. If the transformed free
term vanishes and the transformed full state is nonzero, the inhomogeneous
fixed-point equation becomes a homogeneous Bethe--Salpeter eigen-equation with
eigenvalue one. -/
lemma bennett_boundState_is_massKernel_eigenstate
    {StateTau : Type uTau} {StateMass : Type uMass}
    [AddCommGroup StateTau] [Module ℂ StateTau]
    [AddCommGroup StateMass] [Module ℂ StateMass]
    (B : BennettTauFourierData StateTau StateMass)
    (free full : StateTau)
    (hfull : SatisfiesInhomogeneousBetheSalpeter B.tauKernel free full)
    (m : ℂ) (hfree : B.tauFourier m free = 0)
    (hstate : B.tauFourier m full ≠ 0) :
    IsBetheSalpeterEigenstate (B.massKernel m) 1
      (B.tauFourier m full) := by
  have hmass := bennett_tauFourier_carries_integralEquation B free full hfull m
  unfold SatisfiesInhomogeneousBetheSalpeter at hmass
  refine ⟨hstate, ?_⟩
  rw [hfree, zero_add] at hmass
  simpa using hmass.symm

/-- Concrete Schwartz-space bound-state corollary of Bennett Eq. 66. The only
remaining hypotheses are the parameter-space fixed-point equation, vanishing
of the transformed free term, and nontriviality of the transformed state. -/
lemma bennettSchwartz_boundState_is_massKernel_eigenstate
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    (kernel : State →L[ℂ] State)
    (free full : SchwartzMap ℝ State)
    (hfull : SatisfiesInhomogeneousBetheSalpeter
      (bennettTauIndependentKernel kernel) free full)
    (m : ℝ) (hfree : (𝓕 free) m = 0) (hstate : (𝓕 full) m ≠ 0) :
    IsBetheSalpeterEigenstate kernel.toLinearMap 1 ((𝓕 full) m) := by
  simpa [bennettSchwartzTauFourierData, bennettSchwartzTauFourierAt] using
    bennett_boundState_is_massKernel_eigenstate
      (bennettSchwartzTauFourierData kernel) free full hfull
      (m : ℂ) hfree hstate

/-! ### Bennett Eqs. 2 and 6: local continuity to concatenated current -/

/-- Bennett's finite-parameter concatenation of a current. The paper uses the
whole real line; the finite interval is the exact object to which the
fundamental theorem of calculus applies, and the full concatenation follows
by an improper-integral limit when that limit exists. -/
noncomputable def bennettConcatenatedCurrent
    {Current : Type*} [NormedAddCommGroup Current] [NormedSpace ℝ Current]
    (a b : ℝ) (current : ℝ → Current) : Current :=
  ∫ tau in a..b, current tau

/-- Concatenation commutes with every continuous linear spacetime operation.
This is the analytic interchange needed to move a divergence through
Bennett's `tau` integral; it is supplied by the existing Bochner-integral
infrastructure, not postulated by the bridge. -/
lemma bennettConcatenatedCurrent_map
    {Current Div : Type*}
    [NormedAddCommGroup Current] [NormedSpace ℝ Current] [CompleteSpace Current]
    [NormedAddCommGroup Div] [NormedSpace ℝ Div] [CompleteSpace Div]
    (D : Current →L[ℝ] Div) (a b : ℝ) (current : ℝ → Current)
    (hcurrent : IntervalIntegrable current MeasureTheory.volume a b) :
    bennettConcatenatedCurrent a b (fun tau => D (current tau)) =
      D (bennettConcatenatedCurrent a b current) := by
  exact D.intervalIntegral_comp_comm hcurrent

/-- **Bennett Eq. 2 integrated in `tau`.** If the local five-current obeys
`partial_tau rho + div_x j = 0`, then the spacetime divergence of the
concatenated current is exactly the endpoint flux `rho(a) - rho(b)`. This is
the non-circular analytical content behind the passage from Eq. 2 to Eq. 6. -/
lemma bennett_integrated_continuity_eq_boundaryFlux
    {Charge : Type*} [NormedAddCommGroup Charge] [NormedSpace ℝ Charge]
    [CompleteSpace Charge]
    (rho dTauRho spacetimeDiv : ℝ → Charge) (a b : ℝ)
    (hderiv : ∀ tau ∈ Set.uIcc a b, HasDerivAt rho (dTauRho tau) tau)
    (hintegrable : IntervalIntegrable dTauRho MeasureTheory.volume a b)
    (hcontinuity : ∀ tau, dTauRho tau + spacetimeDiv tau = 0) :
    bennettConcatenatedCurrent a b spacetimeDiv = rho a - rho b := by
  have hdiv : ∀ tau, spacetimeDiv tau = -dTauRho tau := by
    intro tau
    exact eq_neg_of_add_eq_zero_right (hcontinuity tau)
  rw [show bennettConcatenatedCurrent a b spacetimeDiv =
      bennettConcatenatedCurrent a b (fun tau => -dTauRho tau) by
        apply intervalIntegral.integral_congr
        intro tau _
        exact hdiv tau]
  rw [bennettConcatenatedCurrent, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable,
    neg_sub]

/-- **Bennett Eq. 6.** Vanishing (or matching periodic) endpoint density makes
the concatenated four-current divergence-free. Unlike a declaration of
conservation, this conclusion is derived from local continuity and the
fundamental theorem of calculus. -/
lemma bennett_concatenatedCurrent_conserved
    {Charge : Type*} [NormedAddCommGroup Charge] [NormedSpace ℝ Charge]
    [CompleteSpace Charge]
    (rho dTauRho spacetimeDiv : ℝ → Charge) (a b : ℝ)
    (hderiv : ∀ tau ∈ Set.uIcc a b, HasDerivAt rho (dTauRho tau) tau)
    (hintegrable : IntervalIntegrable dTauRho MeasureTheory.volume a b)
    (hcontinuity : ∀ tau, dTauRho tau + spacetimeDiv tau = 0)
    (hboundary : rho a = rho b) :
    bennettConcatenatedCurrent a b spacetimeDiv = 0 := by
  rw [bennett_integrated_continuity_eq_boundaryFlux rho dTauRho spacetimeDiv
    a b hderiv hintegrable hcontinuity, hboundary, sub_self]

/-- The Maxwell current constructed from a `tau`-indexed Faraday tensor stays
conserved after Bennett concatenation. This combines the repository's actual
antisymmetric-tensor proof of `partial_mu J^mu = 0` with finite-sum/Bochner
integration; no separate current-conservation premise is accepted. -/
lemma bennett_concatenatedMaxwellCurrent_conserved
    (k : Fin 4 → ℝ) (potential : ℝ → Fin 4 → ℝ) (a b : ℝ)
    (hintegrable : ∀ nu, IntervalIntegrable
      (fun tau => fourCurrent k (potential tau) nu) MeasureTheory.volume a b) :
    ∑ nu, k nu * bennettConcatenatedCurrent a b
      (fun tau => fourCurrent k (potential tau) nu) = 0 := by
  calc
    ∑ nu, k nu * bennettConcatenatedCurrent a b
        (fun tau => fourCurrent k (potential tau) nu) =
        ∑ nu, ∫ tau in a..b,
          k nu * fourCurrent k (potential tau) nu := by
            apply Finset.sum_congr rfl
            intro nu _
            rw [bennettConcatenatedCurrent,
              intervalIntegral.integral_const_mul]
    _ = ∫ tau in a..b,
        ∑ nu, k nu * fourCurrent k (potential tau) nu := by
          rw [intervalIntegral.integral_finsetSum]
          intro nu _
          exact (hintegrable nu).const_mul (k nu)
    _ = 0 := by
      simp_rw [fourCurrent_conserved]
      simp

/-! ### Bennett's whole-line concatenation and two-particle marginalization -/

/-- Bennett's Eq. 6 current integrated over the complete invariant-parameter
line. This is distinct from `bennettConcatenatedCurrent`, which is the finite
interval approximation used above. -/
noncomputable def bennettWholeLineConcatenatedCurrent
    {Current : Type*} [NormedAddCommGroup Current] [NormedSpace ℝ Current]
    (current : ℝ → Current) : Current :=
  ∫ tau, current tau

/-- **Bennett Eqs. 2 and 6 on the whole real line.** The divergence of the
concatenated current is the difference between the incoming and outgoing
parameter-boundary densities. This closes the improper-integral gap left by
the finite-interval theorem using Mathlib's whole-line fundamental theorem of
calculus. -/
lemma bennett_wholeLine_continuity_eq_boundaryFlux
    {Charge : Type*} [NormedAddCommGroup Charge] [NormedSpace ℝ Charge]
    [CompleteSpace Charge]
    (rho dTauRho spacetimeDiv : ℝ → Charge) (rhoMinus rhoPlus : Charge)
    (hderiv : ∀ tau, HasDerivAt rho (dTauRho tau) tau)
    (hintegrable : MeasureTheory.Integrable dTauRho)
    (hcontinuity : ∀ tau, dTauRho tau + spacetimeDiv tau = 0)
    (hminus : Filter.Tendsto rho Filter.atBot (nhds rhoMinus))
    (hplus : Filter.Tendsto rho Filter.atTop (nhds rhoPlus)) :
    bennettWholeLineConcatenatedCurrent spacetimeDiv = rhoMinus - rhoPlus := by
  have hdiv : spacetimeDiv = fun tau => -dTauRho tau := by
    funext tau
    exact eq_neg_of_add_eq_zero_right (hcontinuity tau)
  rw [bennettWholeLineConcatenatedCurrent, hdiv, MeasureTheory.integral_neg,
    MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hintegrable
      hminus hplus,
    neg_sub]

/-- **Bennett Eq. 6 with the paper's boundary condition.** If the scalar
density vanishes at both invariant-parameter ends, the actual whole-line
concatenated current is divergence-free. -/
lemma bennett_wholeLine_concatenatedCurrent_conserved
    {Charge : Type*} [NormedAddCommGroup Charge] [NormedSpace ℝ Charge]
    [CompleteSpace Charge]
    (rho dTauRho spacetimeDiv : ℝ → Charge)
    (hderiv : ∀ tau, HasDerivAt rho (dTauRho tau) tau)
    (hintegrable : MeasureTheory.Integrable dTauRho)
    (hcontinuity : ∀ tau, dTauRho tau + spacetimeDiv tau = 0)
    (hminus : Filter.Tendsto rho Filter.atBot (nhds 0))
    (hplus : Filter.Tendsto rho Filter.atTop (nhds 0)) :
    bennettWholeLineConcatenatedCurrent spacetimeDiv = 0 := by
  simpa using bennett_wholeLine_continuity_eq_boundaryFlux
    rho dTauRho spacetimeDiv 0 0 hderiv hintegrable hcontinuity hminus hplus

/-- Bennett's concatenation followed by marginalization over the unobserved
particle coordinate, the integration pattern in Eqs. 50--51. -/
noncomputable def bennettMarginalConcatenatedCurrent
    {Y : Type*} [MeasurableSpace Y] (mu : MeasureTheory.Measure Y)
    (jointCurrent : ℝ → Y → ℂ) : ℂ :=
  ∫ tau, ∫ y, jointCurrent tau y ∂mu

/-- **Bennett Eqs. 50--53.** For a distinguishable factorized two-particle
state, marginalizing a normalized spectator density reduces the joint current
to the concatenated one-particle current. This proves the reduction rather
than declaring the marginal to be the one-particle expression. -/
lemma bennett_factorized_marginalCurrent_eq_oneParticle
    {Y : Type*} [MeasurableSpace Y] (mu : MeasureTheory.Measure Y)
    (oneParticleCurrent : ℝ → ℂ) (spectatorDensity : Y → ℂ)
    (hnormalized : ∫ y, spectatorDensity y ∂mu = 1) :
    bennettMarginalConcatenatedCurrent mu
        (fun tau y => oneParticleCurrent tau * spectatorDensity y) =
      ∫ tau, oneParticleCurrent tau := by
  simp [bennettMarginalConcatenatedCurrent,
    MeasureTheory.integral_const_mul, hnormalized]

/-- Swapping an antisymmetric two-fermion state multiplies it by `-1`, but
every quadratic current is unchanged. This is the algebraic core of Bennett's
statement after Eqs. 50--51 that the marginalized currents and semiclassical
potential are bosonic under permutation of the two one-particle states. -/
lemma bennett_quadraticCurrent_neg_invariant
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State) (psi : State) :
    ⟪-psi, currentOperator (-psi)⟫_ℂ =
      ⟪psi, currentOperator psi⟫_ℂ := by
  simp

/-- The quadratic current carried by a state and a continuous linear current
operator.  For the Dirac current, the operator is the appropriate gamma
matrix (with the Dirac adjoint absorbed by the inner product carrier). -/
noncomputable def bennettQuadraticCurrent
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State) (psi : State) : ℂ :=
  ⟪psi, currentOperator psi⟫_ℂ

/-- **Bennett Eqs. 50--53 with an operator current.**  A factorized
two-particle spinor current `⟨psi,A psi⟩ |χ|^2` reduces after spectator
marginalization to the one-particle quadratic current whenever the spectator
wave packet is normalized.  This is the operator-valued specialization of
the scalar marginal theorem above, not a second integration argument. -/
lemma bennett_factorized_operatorCurrent_marginal_eq_oneParticle
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    {Y : Type*} [MeasurableSpace Y] (mu : MeasureTheory.Measure Y)
    (currentOperator : State →L[ℂ] State) (psi : ℝ → State)
    (spectatorAmplitude : Y → ℂ)
    (hnormalized : ∫ y, starRingEnd ℂ (spectatorAmplitude y) * spectatorAmplitude y ∂mu = 1) :
    bennettMarginalConcatenatedCurrent mu
        (fun tau y => bennettQuadraticCurrent currentOperator (psi tau) *
          (starRingEnd ℂ (spectatorAmplitude y) * spectatorAmplitude y)) =
      ∫ tau, bennettQuadraticCurrent currentOperator (psi tau) := by
  exact bennett_factorized_marginalCurrent_eq_oneParticle mu
    (fun tau => bennettQuadraticCurrent currentOperator (psi tau))
    (fun y => starRingEnd ℂ (spectatorAmplitude y) * spectatorAmplitude y)
    hnormalized

/-- **Bennett Eq. 48, interference resolved.**  The quadratic current of the
antisymmetrized two-fermion state `direct - exchange` is the two diagonal
currents minus the two exchange/interference terms.  Thus the entangled case
is not silently reduced to the factorized marginal of Eqs. 52--53. -/
lemma bennett_antisymmetrized_quadraticCurrent_expansion
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State) (direct exchange : State) :
    bennettQuadraticCurrent currentOperator (direct - exchange) =
      bennettQuadraticCurrent currentOperator direct +
        bennettQuadraticCurrent currentOperator exchange -
        ⟪direct, currentOperator exchange⟫_ℂ -
        ⟪exchange, currentOperator direct⟫_ℂ := by
  simp only [bennettQuadraticCurrent, map_sub, inner_sub_left, inner_sub_right]
  ring

/-- Swapping the two one-particle factors negates Bennett's antisymmetrized
Eq. 48 state and therefore leaves its full quadratic current, including the
exchange terms, invariant. -/
lemma bennett_antisymmetrized_quadraticCurrent_swap_invariant
    {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State) (direct exchange : State) :
    bennettQuadraticCurrent currentOperator (exchange - direct) =
      bennettQuadraticCurrent currentOperator (direct - exchange) := by
  have hswap : exchange - direct = -(direct - exchange) := by abel
  rw [hswap]
  simpa [bennettQuadraticCurrent] using
    bennett_quadraticCurrent_neg_invariant currentOperator (direct - exchange)

/-! ### Concrete four-component Dirac currents -/

/-- The canonical four-component complex Hilbert carrier.  This is the
`L²` topology on the same `Fin 4 → ℂ` components used by the repository's
gamma matrices. -/
abbrev BennettDiracSpinor := EuclideanSpace ℂ (Fin 4)

/-- The canonical gamma matrix as a bounded operator on the four-component
spinor Hilbert carrier.  This is the concrete Clifford action before a
spacetime coframe supplies the tangent-vector components. -/
noncomputable def bennettGammaOperator (mu : Fin 4) :
    BennettDiracSpinor →L[ℂ] BennettDiracSpinor :=
  (EuclideanSpace.equiv (Fin 4) ℂ).symm.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin (spaceTime.γ mu))).comp
      (EuclideanSpace.equiv (Fin 4) ℂ).toContinuousLinearMap)

/-- The canonical bounded gamma operators satisfy the complete indexed
Clifford relation on the four-spinor Hilbert carrier.  This transports
`spaceTime.γ.anticommutation` through the Euclidean-space equivalence rather
than checking spinor components a second time. -/
lemma bennettGammaOperator_anticomm (mu nu : Fin 4) :
    (bennettGammaOperator mu).toLinearMap.comp
          (bennettGammaOperator nu).toLinearMap +
        (bennettGammaOperator nu).toLinearMap.comp
          (bennettGammaOperator mu).toLinearMap =
      if mu = nu then
        (2 * spaceTime.γ.diracMetricDiagonal mu) • LinearMap.id
      else 0 := by
  apply LinearMap.ext
  intro psi
  apply (EuclideanSpace.equiv (Fin 4) ℂ).injective
  simp [bennettGammaOperator, EuclideanSpace.equiv,
    PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv,
    Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  change
    Matrix.mulVec
      (spaceTime.γ mu * spaceTime.γ nu +
        spaceTime.γ nu * spaceTime.γ mu) psi.ofLp =
      ((if mu = nu then
          (2 * spaceTime.γ.diracMetricDiagonal mu) • LinearMap.id
        else 0) psi).ofLp
  rw [spaceTime.γ.anticommutation]
  split_ifs <;> simp_all [Matrix.smul_mulVec]

/-- Contract the canonical Dirac matrices with an arbitrary complex
four-vector.  This local slash matrix is derived from the shared indexed
Clifford representation without changing the widely imported core module. -/
noncomputable def bennettGammaContractMatrix (v : Fin 4 → ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ mu : Fin 4, v mu • spaceTime.γ mu

/-- The complex-bilinear Minkowski pairing in the canonical
`(+,-,-,-)` frame used by the Bennett slash matrix. -/
def bennettMinkowskiPair (v w : Fin 4 → ℂ) : ℂ :=
  ∑ mu : Fin 4, spaceTime.γ.diracMetricDiagonal mu * v mu * w mu

set_option maxHeartbeats 400000 in
/-- Contracted gamma matrices satisfy
`{v slash, w slash} = 2 eta(v,w) 1` for arbitrary complex four-vectors. -/
lemma bennettGammaContractMatrix_anticommutation (v w : Fin 4 → ℂ) :
    bennettGammaContractMatrix v * bennettGammaContractMatrix w +
        bennettGammaContractMatrix w * bennettGammaContractMatrix v =
      (2 * bennettMinkowskiPair v w) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bennettGammaContractMatrix, bennettMinkowskiPair,
      Fin.sum_univ_four, spaceTime.γ, spaceTime.γ0, spaceTime.γ1,
      spaceTime.γ2, spaceTime.γ3, spaceTime.γ.diracMetricDiagonal] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- Reorder two concrete gamma matrices using the indexed Clifford law. -/
lemma bennettGamma_mul_swap (a b : Fin 4) :
    spaceTime.γ a * spaceTime.γ b =
      -(spaceTime.γ b * spaceTime.γ a) +
        if a = b then
          (2 * spaceTime.γ.diracMetricDiagonal a) •
            (1 : Matrix (Fin 4) (Fin 4) ℂ)
        else 0 := by
  calc
    spaceTime.γ a * spaceTime.γ b =
        (spaceTime.γ a * spaceTime.γ b +
          spaceTime.γ b * spaceTime.γ a) -
            spaceTime.γ b * spaceTime.γ a := by abel
    _ = (if a = b then
          (2 * spaceTime.γ.diracMetricDiagonal a) •
            (1 : Matrix (Fin 4) (Fin 4) ℂ)
        else 0) - spaceTime.γ b * spaceTime.γ a := by
          rw [spaceTime.γ.anticommutation]
    _ = -(spaceTime.γ b * spaceTime.γ a) +
        if a = b then
          (2 * spaceTime.γ.diracMetricDiagonal a) •
            (1 : Matrix (Fin 4) (Fin 4) ℂ)
        else 0 := by abel

/-- The gamma-bivector commutator derived from the indexed Clifford law. -/
lemma bennettGamma_bivector_commutator (a b d : Fin 4) :
    (spaceTime.γ a * spaceTime.γ b) * spaceTime.γ d -
        spaceTime.γ d * (spaceTime.γ a * spaceTime.γ b) =
      (if b = d then
          (2 * spaceTime.γ.diracMetricDiagonal b) • spaceTime.γ a
        else 0) -
      (if a = d then
          (2 * spaceTime.γ.diracMetricDiagonal a) • spaceTime.γ b
        else 0) := by
  rw [Matrix.mul_assoc, bennettGamma_mul_swap b d]
  simp only [Matrix.mul_add, Matrix.mul_neg]
  rw [← Matrix.mul_assoc, bennettGamma_mul_swap a d]
  by_cases hbd : b = d <;> by_cases had : a = d <;>
    simp [hbd, had, Matrix.mul_assoc, Matrix.add_mul]

/-- The arbitrary complex four-vector contraction of Bennett's concrete
gamma operators.  It is defined through the shared contracted gamma matrix;
the following theorem identifies it with the corresponding operator sum. -/
noncomputable def bennettGammaContractLinearMap (v : Fin 4 → ℂ) :
    BennettDiracSpinor →ₗ[ℂ] BennettDiracSpinor :=
  (EuclideanSpace.equiv (Fin 4) ℂ).symm.toLinearMap.comp
    ((Matrix.mulVecLin (bennettGammaContractMatrix v)).comp
      (EuclideanSpace.equiv (Fin 4) ℂ).toLinearMap)

lemma bennettGammaContractLinearMap_eq_sum (v : Fin 4 → ℂ) :
    bennettGammaContractLinearMap v =
      ∑ mu : Fin 4, v mu • (bennettGammaOperator mu).toLinearMap := by
  apply LinearMap.ext
  intro psi
  apply (EuclideanSpace.equiv (Fin 4) ℂ).injective
  simp [bennettGammaContractLinearMap, bennettGammaOperator,
    EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv,
    PiLp.coe_symm_continuousLinearEquiv, bennettGammaContractMatrix]

/-- The contracted Bennett gamma operators satisfy the full arbitrary-vector
Clifford law on the concrete spinor Hilbert carrier. -/
lemma bennettGammaContractLinearMap_anticomm (v w : Fin 4 → ℂ) :
    (bennettGammaContractLinearMap v).comp
          (bennettGammaContractLinearMap w) +
        (bennettGammaContractLinearMap w).comp
          (bennettGammaContractLinearMap v) =
      (2 * bennettMinkowskiPair v w) •
        (LinearMap.id : BennettDiracSpinor →ₗ[ℂ] BennettDiracSpinor) := by
  apply LinearMap.ext
  intro psi
  apply (EuclideanSpace.equiv (Fin 4) ℂ).injective
  simp [bennettGammaContractLinearMap, EuclideanSpace.equiv,
    PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv,
    Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  change
    Matrix.mulVec
        (bennettGammaContractMatrix v * bennettGammaContractMatrix w +
          bennettGammaContractMatrix w * bennettGammaContractMatrix v)
        psi.ofLp =
      (2 * bennettMinkowskiPair v w) • psi.ofLp
  rw [bennettGammaContractMatrix_anticommutation]
  simp [Matrix.smul_mulVec]

/-- The concrete Dirac vector-current operator `gamma0 gamma^mu` on the
repository's canonical four-component spinor carrier.  The `gamma0` converts
the Hilbert inner product into the Dirac-adjoint pairing. -/
noncomputable def bennettDiracCurrentOperator (mu : Fin 4) :
    BennettDiracSpinor →L[ℂ] BennettDiracSpinor :=
  (EuclideanSpace.equiv (Fin 4) ℂ).symm.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap
      (Matrix.mulVecLin (spaceTime.γ0 * spaceTime.γ mu))).comp
        (EuclideanSpace.equiv (Fin 4) ℂ).toContinuousLinearMap)

/-- Bennett's concrete four-vector current
`j^mu = psiBar gamma^mu psi = psi† gamma0 gamma^mu psi`. -/
noncomputable def bennettDiracVectorCurrent
    (mu : Fin 4) (psi : BennettDiracSpinor) : ℂ :=
  bennettQuadraticCurrent (bennettDiracCurrentOperator mu) psi

/-- The concrete carrier reduces exactly to the canonical gamma-matrix
quadratic form; no abstract state/operator identification remains. -/
lemma bennettDiracVectorCurrent_eq_gammaQuadratic
    (mu : Fin 4) (psi : BennettDiracSpinor) :
    bennettDiracVectorCurrent mu psi =
      ⟪psi, (EuclideanSpace.equiv (Fin 4) ℂ).symm
        (Matrix.mulVec (spaceTime.γ0 * spaceTime.γ mu)
          ((EuclideanSpace.equiv (Fin 4) ℂ) psi))⟫_ℂ := by
  rfl

/-- **Bennett Eqs. 48 and 50--51 on concrete Dirac spinors.**  After
concatenating in `tau` and marginalizing the unobserved coordinate, the full
antisymmetrized current is the integral of both diagonal currents and both
exchange/interference terms.  No factorization premise is used. -/
lemma bennett_dirac_antisymmetrized_marginalCurrent_expansion
    {Y : Type*} [MeasurableSpace Y] (measure : MeasureTheory.Measure Y)
    (mu : Fin 4) (direct exchange : ℝ → Y → BennettDiracSpinor) :
    bennettMarginalConcatenatedCurrent measure
        (fun tau y => bennettDiracVectorCurrent mu
          (direct tau y - exchange tau y)) =
      ∫ tau, ∫ y,
        bennettDiracVectorCurrent mu (direct tau y) +
          bennettDiracVectorCurrent mu (exchange tau y) -
          ⟪direct tau y,
            bennettDiracCurrentOperator mu (exchange tau y)⟫_ℂ -
          ⟪exchange tau y,
            bennettDiracCurrentOperator mu (direct tau y)⟫_ℂ ∂measure := by
  unfold bennettMarginalConcatenatedCurrent
  apply MeasureTheory.integral_congr_ae
  filter_upwards with tau
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  exact bennett_antisymmetrized_quadraticCurrent_expansion
    (bennettDiracCurrentOperator mu) (direct tau y) (exchange tau y)

/-! ### Exact interacting two-particle Dirac evolution -/

/-- The concrete 16-component carrier for two four-component Dirac spinors.
The two `Fin 4` indices are retained separately so fermion exchange is an
actual linear operation rather than an informal relabeling. -/
abbrev BennettTwoDiracState := Fin 4 × Fin 4 → ℂ

/-- Exchange of the two spinor indices on the two-particle Dirac carrier. -/
def bennettTwoDiracExchange :
    BennettTwoDiracState →ₗ[ℂ] BennettTwoDiracState where
  toFun psi := fun index => psi (index.2, index.1)
  map_add' psi phi := by ext index; rfl
  map_smul' c psi := by ext index; rfl

/-- The fermionic sector consists of states odd under exchange. -/
def IsBennettTwoDiracAntisymmetric (psi : BennettTwoDiracState) : Prop :=
  bennettTwoDiracExchange psi = -psi

/-- The scalar central-interaction energy of two Dirac modes.  `E1 + E2` is
the free two-particle energy and `V` is the interaction shift.  This is the
exactly solvable central channel, not a claim about an arbitrary spacetime-
dependent photon-exchange potential. -/
def bennettTwoDiracCentralEnergy (E1 E2 V : ℝ) : ℝ :=
  E1 + E2 + V

/-- Exact invariant-parameter evolution for the interacting central channel.
The solution is a phase multiplying the complete 16-component initial state,
so it includes arbitrary entangled and antisymmetric spin components. -/
noncomputable def bennettTwoDiracCentralSolution
    (E1 E2 V : ℝ) (psi0 : BennettTwoDiracState) (tau : ℂ) :
    BennettTwoDiracState :=
  Complex.exp (tau *
    (-Complex.I * (bennettTwoDiracCentralEnergy E1 E2 V : ℂ))) • psi0

/-- The exact interacting solution has the prescribed initial condition. -/
@[simp] lemma bennettTwoDiracCentralSolution_zero
    (E1 E2 V : ℝ) (psi0 : BennettTwoDiracState) :
    bennettTwoDiracCentralSolution E1 E2 V psi0 0 = psi0 := by
  simp [bennettTwoDiracCentralSolution]

/-- The central-interaction solution is differentiable and solves the
two-particle Dirac/Schrödinger evolution equation
`i dPsi/dtau = (E1 + E2 + V) Psi` exactly.  No solution or eigenstate is an
input premise. -/
lemma bennettTwoDiracCentralSolution_schrodinger
    (E1 E2 V : ℝ) (psi0 : BennettTwoDiracState) (tau : ℂ) :
    ∃ dpsi : BennettTwoDiracState,
      HasDerivAt (bennettTwoDiracCentralSolution E1 E2 V psi0) dpsi tau ∧
      Complex.I • dpsi =
        (bennettTwoDiracCentralEnergy E1 E2 V : ℂ) •
          bennettTwoDiracCentralSolution E1 E2 V psi0 tau := by
  let generator : ℂ :=
    -Complex.I * (bennettTwoDiracCentralEnergy E1 E2 V : ℂ)
  let dpsi : BennettTwoDiracState :=
    generator • bennettTwoDiracCentralSolution E1 E2 V psi0 tau
  refine ⟨dpsi, ?_, ?_⟩
  · have hphase : HasDerivAt (fun t : ℂ => Complex.exp (t * generator))
        (Complex.exp (tau * generator) * generator) tau := by
      have hlinear : HasDerivAt (fun t : ℂ => t * generator) generator tau := by
        simpa using (hasDerivAt_id tau).mul_const generator
      exact (Complex.hasDerivAt_exp (tau * generator)).comp tau hlinear
    have hstate := hphase.smul_const psi0
    change HasDerivAt (fun t : ℂ => Complex.exp (t * generator) • psi0)
      (generator • (Complex.exp (tau * generator) • psi0)) tau
    simpa [smul_smul, mul_comm] using hstate
  · unfold dpsi generator
    rw [smul_smul]
    congr 1
    push_cast
    calc
      Complex.I * (-Complex.I *
          (bennettTwoDiracCentralEnergy E1 E2 V : ℂ)) =
          -(Complex.I * Complex.I) *
            (bennettTwoDiracCentralEnergy E1 E2 V : ℂ) := by ring
      _ = (bennettTwoDiracCentralEnergy E1 E2 V : ℂ) := by
        rw [Complex.I_mul_I]
        ring

/-- A scalar central interaction commutes with fermion exchange, so the exact
interacting evolution preserves the antisymmetric two-Dirac sector for all
invariant parameter values. -/
lemma bennettTwoDiracCentralSolution_preserves_antisymmetry
    (E1 E2 V : ℝ) (psi0 : BennettTwoDiracState)
    (hpsi0 : IsBennettTwoDiracAntisymmetric psi0) (tau : ℂ) :
    IsBennettTwoDiracAntisymmetric
      (bennettTwoDiracCentralSolution E1 E2 V psi0 tau) := by
  unfold IsBennettTwoDiracAntisymmetric at hpsi0 ⊢
  rw [bennettTwoDiracCentralSolution, map_smul, hpsi0]
  simp

/-- The interaction is visible at generator level: the full central energy is
the free two-particle energy plus the potential shift.  Thus setting `V = 0`
recovers the free evolution, while nonzero `V` is not definitionally erased. -/
lemma bennettTwoDiracCentralEnergy_free_add_interaction
    (E1 E2 V : ℝ) :
    bennettTwoDiracCentralEnergy E1 E2 V = (E1 + E2) + V := by
  rfl

/-! ### Bennett spin--statistics current to Rasheed NLED black-hole mechanics

This section relates the two Bennett papers to Rasheed without changing their
scope.  Bennett supplies the exchange-odd two-fermion state and its
exchange-even quadratic, concatenated semiclassical current.  Rasheed supplies
the nonlinear constitutive excitation and the stationary-horizon variation
identities.  The bridge proves that the fermionic sign disappears before an
arbitrary nonlinear response is applied, so the resulting flux charge and
black-hole first law are permutation invariant.

No black-hole solution, horizon, or constitutive coefficients are inferred
from a Dirac wavefunction.  Source compatibility and the flux extraction are
kept visible as the physical carrier maps. -/

/-- **Rasheed Eq. (2.11), pointwise.**  In four dimensions the nonlinear
excitation has the form `G = aF + b⋆F`, with `a,b` scalar functions of the two
electromagnetic invariants.  Here they are their values at one spacetime
point. -/
noncomputable def rasheedNLEDExcitation
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  a • F + b • hodgeStar2 F

/-- The Rasheed excitation is an antisymmetric two-form whenever `F` is.
The proof expands the existing Hodge-star definition and reuses the public
Levi-Civita antisymmetry theorem. -/
theorem rasheedNLEDExcitation_antisymmetric
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ mu nu, F mu nu = -F nu mu) :
    ∀ mu nu,
      rasheedNLEDExcitation a b F mu nu =
        -rasheedNLEDExcitation a b F nu mu := by
  intro mu nu
  have hstar :
      hodgeStar2 F mu nu = -hodgeStar2 F nu mu := by
    change (1 / 2 : ℝ) *
        ∑ i, ∑ j,
          ((Physlib.QFT.Lattice.LatticeTopologicalCharge.leviCivita4
            mu nu i j : ℤ) : ℝ) * F i j =
      -((1 / 2 : ℝ) *
        ∑ i, ∑ j,
          ((Physlib.QFT.Lattice.LatticeTopologicalCharge.leviCivita4
            nu mu i j : ℤ) : ℝ) * F i j)
    rw [← mul_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Physlib.QFT.Lattice.LatticeTopologicalCharge.leviCivita4_swap_12]
    push_cast
    ring
  simp only [rasheedNLEDExcitation, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hF mu nu, hstar]
  ring

/-- The weak-field Maxwell constitutive law is the `a=1,b=0` slice. -/
@[simp] theorem rasheedNLEDExcitation_maxwell
    (F : Matrix (Fin 4) (Fin 4) ℝ) :
    rasheedNLEDExcitation 1 0 F = F := by
  simp [rasheedNLEDExcitation]

/-- The Fourier-symbol divergence current of Rasheed's nonlinear
excitation.  Rasheed's source-free exterior equation (2.7) sets this
four-vector to zero; a sourced matter-region extension instead equates it
to a matter current. -/
noncomputable def rasheedNLEDSource
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  maxwellCurrent (rasheedNLEDExcitation a b F) k

/-- **Rasheed Eq. (2.7)** in the repository's Fourier-symbol carrier:
the divergence current of the nonlinear excitation vanishes in the
source-free electrovac exterior. -/
def SatisfiesRasheedSourceFreeNLED
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) : Prop :=
  rasheedNLEDSource a b F k = 0

/-- The divergence current constructed from the NLED excitation is conserved
because the excitation is antisymmetric.  This reuses the repository's
Maxwell-continuity contraction theorem; the constitutive response itself may
be nonlinear in `F`.

This identity is `k · J = 0`.  It does not replace Rasheed's stronger
source-free exterior equation `J = 0`, represented separately by
`SatisfiesRasheedSourceFreeNLED`. -/
theorem rasheedNLEDSource_conserved
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ)
    (hF : ∀ mu nu, F mu nu = -F nu mu) :
    ∑ mu, k mu * rasheedNLEDSource a b F k mu = 0 := by
  exact maxwell_current_conserved (rasheedNLEDExcitation a b F) k
    (rasheedNLEDExcitation_antisymmetric a b F hF)

/-- Bennett's Eq. (6) concatenation retained componentwise as a
four-vector. -/
noncomputable def bennettWholeLineVectorCurrent
    (current : ℝ → Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun mu => bennettWholeLineConcatenatedCurrent (fun tau => current tau mu)

/-- **Bennett Eqs. (2) and (6)** in the same Fourier-symbol conservation
form as the NLED excitation source.  Local five-current continuity and
vanishing parameter-endpoint density derive conservation of the actual
whole-line four-current. -/
theorem bennett_wholeLine_vectorCurrent_conserved
    (rho dTauRho : ℝ → ℝ) (current : ℝ → Fin 4 → ℝ)
    (k : Fin 4 → ℝ)
    (hderiv : ∀ tau, HasDerivAt rho (dTauRho tau) tau)
    (hdensity : MeasureTheory.Integrable dTauRho)
    (hcurrent : ∀ mu, MeasureTheory.Integrable (fun tau => current tau mu))
    (hcontinuity :
      ∀ tau, dTauRho tau + ∑ mu, k mu * current tau mu = 0)
    (hminus : Filter.Tendsto rho Filter.atBot (nhds 0))
    (hplus : Filter.Tendsto rho Filter.atTop (nhds 0)) :
    ∑ mu, k mu * bennettWholeLineVectorCurrent current mu = 0 := by
  have hconcatenated :
      bennettWholeLineConcatenatedCurrent
        (fun tau => ∑ mu, k mu * current tau mu) = 0 :=
    bennett_wholeLine_concatenatedCurrent_conserved
      rho dTauRho (fun tau => ∑ mu, k mu * current tau mu)
      hderiv hdensity hcontinuity hminus hplus
  calc
    ∑ mu, k mu * bennettWholeLineVectorCurrent current mu =
        ∑ mu, ∫ tau, k mu * current tau mu := by
          apply Finset.sum_congr rfl
          intro mu _
          simp [bennettWholeLineVectorCurrent,
            bennettWholeLineConcatenatedCurrent,
            MeasureTheory.integral_const_mul]
    _ = ∫ tau, ∑ mu, k mu * current tau mu := by
      rw [MeasureTheory.integral_finsetSum]
      intro mu _
      exact (hcurrent mu).const_mul (k mu)
    _ = 0 := hconcatenated

/-- Compatibility of Bennett's concatenated semiclassical source with the
sourced extension of Rasheed's nonlinear excitation equation in a matter
region.  This is the physical source-to-field identification, not a
definitional equality.  Matching that region to Rasheed's source-free
electrovac exterior remains separate geometric data. -/
def BennettRasheedNLEDSourceCompatible
    (current : ℝ → Fin 4 → ℝ)
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) : Prop :=
  bennettWholeLineVectorCurrent current = rasheedNLEDSource a b F k

/-- Under source compatibility, Bennett's concatenated current and
Rasheed's nonlinear excitation are one conserved four-current. -/
theorem bennett_rasheed_commonSource_conserved
    (current : ℝ → Fin 4 → ℝ)
    (a b : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ)
    (hF : ∀ mu nu, F mu nu = -F nu mu)
    (hcompatible :
      BennettRasheedNLEDSourceCompatible current a b F k) :
    ∑ mu, k mu * bennettWholeLineVectorCurrent current mu = 0 := by
  rw [hcompatible]
  exact rasheedNLEDSource_conserved a b F k hF

/-- A horizon electric charge extracted from Bennett's quadratic current
through an arbitrary, possibly nonlinear, NLED response and a flux map.
The response includes the solve for `F`, the constitutive `F ↦ G`, and any
required horizon restriction; `horizonFlux` represents Rasheed Eq. (5.4). -/
noncomputable def bennettRasheedElectricCharge
    {State Field : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State)
    (nledResponse : ℂ → Field) (horizonFlux : Field → ℝ)
    (psi : State) : ℝ :=
  horizonFlux (nledResponse
    (bennettQuadraticCurrent currentOperator psi))

/-- The fermionic sign cancels before the arbitrary nonlinear response is
applied: every charge extracted from a Bennett quadratic current is invariant
under `psi ↦ -psi`. -/
theorem bennettRasheedElectricCharge_neg_invariant
    {State Field : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State)
    (nledResponse : ℂ → Field) (horizonFlux : Field → ℝ)
    (psi : State) :
    bennettRasheedElectricCharge currentOperator nledResponse horizonFlux
        (-psi) =
      bennettRasheedElectricCharge currentOperator nledResponse horizonFlux
        psi := by
  unfold bennettRasheedElectricCharge
  rw [show bennettQuadraticCurrent currentOperator (-psi) =
      bennettQuadraticCurrent currentOperator psi by
        simpa [bennettQuadraticCurrent] using
          bennett_quadraticCurrent_neg_invariant currentOperator psi]

/-- Exchanging the two one-particle factors negates Bennett's
antisymmetrized state but leaves the NLED horizon charge unchanged. -/
theorem bennettRasheedElectricCharge_swap_invariant
    {State Field : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State)
    (nledResponse : ℂ → Field) (horizonFlux : Field → ℝ)
    (direct exchange : State) :
    bennettRasheedElectricCharge currentOperator nledResponse horizonFlux
        (exchange - direct) =
      bennettRasheedElectricCharge currentOperator nledResponse horizonFlux
        (direct - exchange) := by
  have hswap : exchange - direct = -(direct - exchange) := by abel
  rw [hswap]
  exact bennettRasheedElectricCharge_neg_invariant
    currentOperator nledResponse horizonFlux (direct - exchange)

/-- Electric-charge variation between two Bennett states. -/
noncomputable def bennettRasheedElectricChargeVariation
    {State Field : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State)
    (nledResponse : ℂ → Field) (horizonFlux : Field → ℝ)
    (initial final : State) : ℝ :=
  bennettRasheedElectricCharge currentOperator nledResponse horizonFlux final -
    bennettRasheedElectricCharge currentOperator nledResponse horizonFlux initial

/-- The complete charge variation is invariant when both endpoint
antisymmetrized states are represented with the opposite exchange order. -/
theorem bennettRasheedElectricChargeVariation_swap_invariant
    {State Field : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State)
    (nledResponse : ℂ → Field) (horizonFlux : Field → ℝ)
    (initialDirect initialExchange finalDirect finalExchange : State) :
    bennettRasheedElectricChargeVariation currentOperator nledResponse
        horizonFlux (initialExchange - initialDirect)
        (finalExchange - finalDirect) =
      bennettRasheedElectricChargeVariation currentOperator nledResponse
        horizonFlux (initialDirect - initialExchange)
        (finalDirect - finalExchange) := by
  unfold bennettRasheedElectricChargeVariation
  rw [bennettRasheedElectricCharge_swap_invariant currentOperator
      nledResponse horizonFlux finalDirect finalExchange,
    bennettRasheedElectricCharge_swap_invariant currentOperator
      nledResponse horizonFlux initialDirect initialExchange]

/-- **Rasheed Eq. (5.16)** in the paper's geometric units:
`δM = κ δA/(8π) + Ω_H δJ + Φ_H δQ + Ψ_H δP`. -/
def SatisfiesRasheedNLEDFirstLaw
    (dM kappa dArea omegaH dJ phiH dQ psiH dP : ℝ) : Prop :=
  dM = kappa / (8 * Real.pi) * dArea +
    omegaH * dJ + phiH * dQ + psiH * dP

/-- **Rasheed Eqs. (5.1), (5.5), and (5.15).**  The electric-potential
variation cancels, and the `δΩ_H I₃` term missing from some earlier
derivations cancels exactly against the NLED Lagrangian variation.  The
usual first law Eq. (5.16) follows without assuming a Smarr homogeneity
formula. -/
theorem rasheed_nledFirstLaw_from_surfaceVariations
    (dM kappa dArea omegaH dJ phiH dQ q dPhi psiH dP
      dOmegaH I3 dI1 dAI2 : ℝ)
    (hraw :
      dM = kappa / (8 * Real.pi) * dArea + omegaH * dJ -
        dI1 - dAI2 + dOmegaH * I3)
    (hI1 : dI1 = -(dPhi * q + phiH * dQ))
    (hI2 : dAI2 = q * dPhi - psiH * dP + dOmegaH * I3) :
    SatisfiesRasheedNLEDFirstLaw
      dM kappa dArea omegaH dJ phiH dQ psiH dP := by
  unfold SatisfiesRasheedNLEDFirstLaw
  rw [hraw, hI1, hI2]
  ring

/-- The Rasheed first law is independent of which exchange ordering is used
to represent Bennett's antisymmetrized two-fermion states, even when the
current-to-field response is nonlinear. -/
theorem bennettRasheed_nledFirstLaw_exchange_iff
    {State Field : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℂ State]
    (currentOperator : State →L[ℂ] State)
    (nledResponse : ℂ → Field) (horizonFlux : Field → ℝ)
    (initialDirect initialExchange finalDirect finalExchange : State)
    (dM kappa dArea omegaH dJ phiH psiH dP : ℝ) :
    SatisfiesRasheedNLEDFirstLaw dM kappa dArea omegaH dJ phiH
        (bennettRasheedElectricChargeVariation currentOperator nledResponse
          horizonFlux (initialExchange - initialDirect)
          (finalExchange - finalDirect)) psiH dP ↔
      SatisfiesRasheedNLEDFirstLaw dM kappa dArea omegaH dJ phiH
        (bennettRasheedElectricChargeVariation currentOperator nledResponse
          horizonFlux (initialDirect - initialExchange)
          (finalDirect - finalExchange)) psiH dP := by
  rw [bennettRasheedElectricChargeVariation_swap_invariant]

/-! ### Bennett's massive axial current and the one-loop anomaly -/

/-- The invariant-parameter derivative term in Bennett Eq. 85 on a sharp
mass mode.  The two signs come from differentiating the mode and its adjoint,
respectively. -/
def bennettSharpMassAxialTauTerm (m : ℝ) (pseudoscalar : ℂ) : ℂ :=
  (Complex.I * (m : ℂ)) * pseudoscalar -
    ((-Complex.I) * (m : ℂ)) * pseudoscalar

/-- The sharp-mass `tau` term is exactly `2 i m` times the pseudoscalar
bilinear.  This is the algebraic step from Bennett Eq. 85 to Eq. 87. -/
lemma bennett_sharpMass_axialTauTerm
    (m : ℝ) (pseudoscalar : ℂ) :
    bennettSharpMassAxialTauTerm m pseudoscalar =
      2 * Complex.I * (m : ℂ) * pseudoscalar := by
  unfold bennettSharpMassAxialTauTerm
  ring

/-- Bennett Eq. 85 written with its sharp-mass mode made explicit: the
parameter derivative term plus the four-dimensional axial divergence
vanishes. -/
def SatisfiesBennettSharpMassAxialContinuity
    (m : ℝ) (pseudoscalar axialDivergence : ℂ) : Prop :=
  bennettSharpMassAxialTauTerm m pseudoscalar + axialDivergence = 0

/-- **Bennett Eq. 87, pointwise.**  The local five-current identity Eq. 85
and sharp-mass `tau` dependence imply
`partial_mu J5^mu = -2 i m (psiBar gamma5 psi)`.  The continuity identity is
an explicit premise; the mass factor is derived rather than postulated. -/
lemma bennett_sharpMass_axialDivergence
    (m : ℝ) (pseudoscalar axialDivergence : ℂ)
    (hcontinuity : SatisfiesBennettSharpMassAxialContinuity
      m pseudoscalar axialDivergence) :
    axialDivergence =
      -(2 * Complex.I * (m : ℂ)) * pseudoscalar := by
  unfold SatisfiesBennettSharpMassAxialContinuity at hcontinuity
  rw [bennett_sharpMass_axialTauTerm] at hcontinuity
  linear_combination hcontinuity

/-- **Bennett Eq. 87 after concatenation.**  Integrating the pointwise
sharp-mass axial identity over the full invariant-parameter line pulls out
the constant `-2 i m`. -/
lemma bennett_sharpMass_axialDivergence_concatenated
    (m : ℝ) (pseudoscalar axialDivergence : ℝ → ℂ)
    (hcontinuity : ∀ tau, SatisfiesBennettSharpMassAxialContinuity
      m (pseudoscalar tau) (axialDivergence tau)) :
    ∫ tau, axialDivergence tau =
      -(2 * Complex.I * (m : ℂ)) * ∫ tau, pseudoscalar tau := by
  have hpoint : axialDivergence =
      fun tau => -(2 * Complex.I * (m : ℂ)) * pseudoscalar tau := by
    funext tau
    exact bennett_sharpMass_axialDivergence m _ _ (hcontinuity tau)
  rw [hpoint, MeasureTheory.integral_const_mul]

/-- Bennett Eq. 88's electromagnetic Adler--Bell--Jackiw coefficient
`-e^2/(4 pi)^2`.  The one-loop triangle identity itself is kept separate
from this normalization. -/
noncomputable def bennettABJNormalization (e : ℝ) : ℝ :=
  -(e ^ 2) / (4 * Real.pi) ^ 2

/-- Bennett's Eq. 88 normalization is exactly charge squared times the
repository's existing Chern--Simons/Pontryagin normalization, with the axial
sign.  This reuses the topological-density carrier instead of defining a
second incompatible `1/(16 pi^2)` convention. -/
lemma bennettABJNormalization_eq_chargeSq_mul_pontryaginNormalization
    (e : ℝ) :
    bennettABJNormalization e =
      -(e ^ 2) * chernSimonsPontryaginNormalization := by
  unfold bennettABJNormalization chernSimonsPontryaginNormalization
  field_simp [Real.pi_ne_zero]
  ring

/-- The electromagnetic Pontryagin pseudoscalar `F_{mu nu} (*F)_{mu nu}`
built from the repository's actual four-dimensional Hodge star. -/
noncomputable def bennettElectromagneticPontryaginDensity
    (F : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ mu, ∑ nu, F mu nu * hodgeStar2 F mu nu

/-- Bennett Eq. 88 as an explicit proposition.  The relation is the output
of the one-loop triangle calculation and is intentionally data, while its
field-strength density and normalization are concrete repository objects. -/
def SatisfiesBennettABJAnomaly
    (e : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (axialDivergence : ℝ) : Prop :=
  axialDivergence = bennettABJNormalization e *
    bennettElectromagneticPontryaginDensity F

/-- **Bennett Eq. 88 in the shared Pontryagin convention.**  Once the
one-loop ABJ relation is supplied, its right-hand side is exactly
`-e^2/(16 pi^2)` times the concrete `F · *F` density. -/
lemma bennettABJAnomaly_eq_chargeSq_pontryaginDensity
    (e : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (axialDivergence : ℝ)
    (hABJ : SatisfiesBennettABJAnomaly e F axialDivergence) :
    axialDivergence =
      (-(e ^ 2) * chernSimonsPontryaginNormalization) *
        bennettElectromagneticPontryaginDensity F := by
  rw [SatisfiesBennettABJAnomaly,
    bennettABJNormalization_eq_chargeSq_mul_pontryaginNormalization] at hABJ
  exact hABJ

/-- The concrete ABJ topological source is gauge invariant for a Faraday
field: shifting `A` by the momentum-space gradient `chi k` leaves `F`, its
Hodge dual, and hence `F · *F` unchanged. -/
lemma bennettElectromagneticPontryaginDensity_faraday_gauge_invariant
    (k A : Fin 4 → ℝ) (chi : ℝ) :
    bennettElectromagneticPontryaginDensity
        (faraday k (fun rho => A rho + chi * k rho)) =
      bennettElectromagneticPontryaginDensity (faraday k A) := by
  rw [faraday_gauge_invariant]

/-! ### The regulated one-loop origin of the ABJ coefficient -/

/-- The parity-odd renormalized one-loop effective action already constructed
in `QEDYukawaOneLoopEffectiveAction` differentiates, along the dimensionless
chiral direction `P = M theta`, to the ABJ density.  Unlike
`SatisfiesBennettABJAnomaly`, this theorem has no anomaly equation as a
premise: it derives the coefficient from the analytic derivative of the
repository's arctangent one-loop action.

The remaining scope boundary is explicit.  The renormalized odd effective
Lagrangian is the paper-level one-loop input; this theorem does not reconstruct
the underlying regularized fermion determinant or prove interacting QED. -/
lemma bennettABJ_from_renormalizedOddOneLoopAction
    (e M : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ) (hM : M ≠ 0) :
    HasDerivAt
      (fun theta : ℝ => qedYukawaOddEffectiveLagrangian e
        (bennettElectromagneticPontryaginDensity F) M (M * theta))
      (-bennettABJNormalization e *
        bennettElectromagneticPontryaginDensity F) 0 := by
  have hP : HasDerivAt (fun theta : ℝ => M * theta) M 0 :=
    by simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℝ) |>.const_mul M)
  have hloop := qedYukawaOdd_hasDerivAt_pseudoscalar e
    (bennettElectromagneticPontryaginDensity F) M 0 hM
  have hloopAt : HasDerivAt
      (fun P => qedYukawaOddEffectiveLagrangian e
        (bennettElectromagneticPontryaginDensity F) M P)
      (qedYukawaOddCurrentRationalFactor e
        (bennettElectromagneticPontryaginDensity F) M 0) (M * 0) := by
    simpa using hloop
  have hcomp : HasDerivAt
      (fun theta : ℝ => qedYukawaOddEffectiveLagrangian e
        (bennettElectromagneticPontryaginDensity F) M (M * theta))
      (qedYukawaOddCurrentRationalFactor e
        (bennettElectromagneticPontryaginDensity F) M 0 * M) 0 := by
    exact hloopAt.comp 0 hP
  convert hcomp using 1
  unfold qedYukawaOddCurrentRationalFactor bennettABJNormalization
  field_simp [hM, Real.pi_ne_zero]
  ring

/-- The one-loop-derived ABJ response is gauge invariant on a Faraday field.
Both sides use the same concrete Hodge-star density, and gauge invariance is
inherited from the already-proved invariance of `faraday`. -/
lemma bennettABJ_oneLoopResponse_faraday_gauge_invariant
    (e M : ℝ) (k A : Fin 4 → ℝ) (chi : ℝ) :
    -bennettABJNormalization e *
        bennettElectromagneticPontryaginDensity
          (faraday k (fun rho => A rho + chi * k rho)) =
      -bennettABJNormalization e *
        bennettElectromagneticPontryaginDensity (faraday k A) := by
  rw [bennettElectromagneticPontryaginDensity_faraday_gauge_invariant]

/-- Certified content of Bassetto--Ciccariello--Tonin's analytic Fredholm
construction for the equal-mass scalar ladder equation. `lift` is the analytic
continuation from the vacuum-like `P = 0` sector to a specified nonzero null
total momentum. Kernel intertwining records the recurrence and Fredholm
solvability conditions of their Eqs. 3--9. -/
structure BassettoLadderLiftData
    (State : Type uState) [AddCommGroup State] [Module ℂ State]
    (vacuumKernel lightKernel : State →ₗ[ℂ] State) where
  totalMomentum : Lorentz.Vector 3
  totalMomentum_ne_zero : totalMomentum ≠ 0
  totalMomentum_lightLike :
    Lorentz.Vector.causalCharacter totalMomentum = .lightLike
  lift : State →ₗ[ℂ] State
  lift_injective : Function.Injective lift
  kernel_intertwines : ∀ psi,
    lightKernel (lift psi) = lift (vacuumKernel psi)

/-- Bassetto's lightlike sector has vanishing Minkowski norm, while nonzero
momentum is retained separately because the repository's causal classifier
also calls the zero vector lightlike. -/
lemma bassetto_lightlike_momentum_sq_zero
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    {vacuumKernel lightKernel : State →ₗ[ℂ] State}
    (L : BassettoLadderLiftData State vacuumKernel lightKernel) :
    Lorentz.Vector.minkowskiProduct
      L.totalMomentum L.totalMomentum = 0 :=
  (Lorentz.Vector.lightLike_iff_norm_sq_zero L.totalMomentum).mp
    L.totalMomentum_lightLike

/-- **Bassetto Eqs. 3--9.** The certified analytic lift sends a nonzero
vacuum-like Bethe--Salpeter eigenstate to a nonzero state at nonzero null total
momentum with the same kernel eigenvalue. -/
lemma bassetto_vacuumLike_implies_lightLike_sameEigenvalue
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    {vacuumKernel lightKernel : State →ₗ[ℂ] State}
    (L : BassettoLadderLiftData State vacuumKernel lightKernel)
    {lambda : ℂ} {psi : State}
    (hpsi : IsBetheSalpeterEigenstate vacuumKernel lambda psi) :
    L.totalMomentum ≠ 0 ∧
      Lorentz.Vector.minkowskiProduct
        L.totalMomentum L.totalMomentum = 0 ∧
      IsBetheSalpeterEigenstate lightKernel lambda (L.lift psi) := by
  have hlift_ne : L.lift psi ≠ 0 := by
    intro hzero
    apply hpsi.1
    apply L.lift_injective
    simpa using hzero
  refine ⟨L.totalMomentum_ne_zero,
    bassetto_lightlike_momentum_sq_zero L, hlift_ne, ?_⟩
  rw [L.kernel_intertwines, hpsi.2, map_smul]

/-- The same continuation preserves the repository's Wick--Cutkosky value
`N(N+1)`, explicitly linking Bassetto's equal-eigenvalue statement to the
existing Bethe--Salpeter spectrum rather than defining a second spectrum. -/
lemma bassetto_preserves_cutkoskyEigenvalue
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    {vacuumKernel lightKernel : State →ₗ[ℂ] State}
    (L : BassettoLadderLiftData State vacuumKernel lightKernel)
    (N : ℕ) {psi : State}
    (hpsi : IsBetheSalpeterEigenstate vacuumKernel
      ((cutkoskyEigenvalue N : ℝ) : ℂ) psi) :
    IsBetheSalpeterEigenstate lightKernel
      ((cutkoskyEigenvalue N : ℝ) : ℂ) (L.lift psi) :=
  (bassetto_vacuumLike_implies_lightLike_sameEigenvalue L hpsi).2.2

/-! ## C. Transport to Caticha's continuum functional carrier -/

/-- An explicit intertwiner from a lightlike Bethe--Salpeter state carrier to
Caticha's continuum functional Schrödinger carrier. This is the required
carrier identification; it is not inferred from matching notation. -/
structure BassettoCatichaIntertwiner
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    {𝒯c : Type uFc} {𝒾c : Type uSc}
    [AddCommGroup 𝒯c] [Module ℂ 𝒯c]
    [AddCommGroup 𝒾c] [Module ℂ 𝒾c]
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (lightKernel : State →ₗ[ℂ] State) where
  stateMap : State →ₗ[ℂ] 𝒯c
  stateMap_injective : Function.Injective stateMap
  generator_intertwines : ∀ psi,
    continuumSmearedSchrodingerGenerator D.lapse D.shift D.Hperp D.Hi
        (stateMap psi) =
      stateMap (lightKernel psi)

/-- A lightlike Bethe--Salpeter eigenstate becomes a nonzero eigenmode of
Caticha's continuum lapse/shift-smeared functional generator. -/
lemma lightlike_eigenstate_to_caticha
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    {𝒯c : Type uFc} {𝒾c : Type uSc}
    [AddCommGroup 𝒯c] [Module ℂ 𝒯c]
    [AddCommGroup 𝒾c] [Module ℂ 𝒾c]
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    {lightKernel : State →ₗ[ℂ] State}
    (C : BassettoCatichaIntertwiner D lightKernel)
    {lambda : ℂ} {psi : State}
    (hpsi : IsBetheSalpeterEigenstate lightKernel lambda psi) :
    C.stateMap psi ≠ 0 ∧
      continuumSmearedSchrodingerGenerator D.lapse D.shift D.Hperp D.Hi
          (C.stateMap psi) = lambda • C.stateMap psi := by
  have hstate_ne : C.stateMap psi ≠ 0 := by
    intro hzero
    apply hpsi.1
    apply C.stateMap_injective
    simpa using hzero
  refine ⟨hstate_ne, ?_⟩
  rw [C.generator_intertwines, hpsi.2, map_smul]

/-- Concrete analytic-series route from Bennett's Schwartz parameter history,
through Bassetto's coefficientwise Fredholm continuation, to Caticha's
functional Schrödinger generator. This strengthens the earlier abstract lift:
the Fourier transform and infinite series are both actual constructions, and
only the paper-specific recurrence, summability, and carrier map remain data. -/
lemma bennettSchwartz_bassettoAnalytic_to_caticha
    {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
    [CompleteSpace State]
    (kernel lightKernel : State →L[ℂ] State)
    (free full : SchwartzMap ℝ State)
    (hfull : SatisfiesInhomogeneousBetheSalpeter
      (bennettTauIndependentKernel kernel) free full)
    (m : ℝ) (hfree : (𝓕 free) m = 0) (hstate : (𝓕 full) m ≠ 0)
    (B : BassettoAnalyticFredholmData State kernel lightKernel)
    (epsilon : ℂ)
    (hseries : bassettoAnalyticLightlikeSeries B epsilon ((𝓕 full) m) ≠ 0)
    {𝒯c : Type uFc} {𝒾c : Type uSc}
    [AddCommGroup 𝒯c] [Module ℂ 𝒯c]
    [AddCommGroup 𝒾c] [Module ℂ 𝒾c]
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (C : BassettoCatichaIntertwiner D lightKernel.toLinearMap) :
    B.totalMomentum ≠ 0 ∧
      Lorentz.Vector.minkowskiProduct B.totalMomentum B.totalMomentum = 0 ∧
      IsBetheSalpeterEigenstate lightKernel.toLinearMap 1
        (bassettoAnalyticLightlikeSeries B epsilon ((𝓕 full) m)) ∧
      C.stateMap (bassettoAnalyticLightlikeSeries B epsilon ((𝓕 full) m)) ≠ 0 ∧
      continuumSmearedSchrodingerGenerator D.lapse D.shift D.Hperp D.Hi
          (C.stateMap
            (bassettoAnalyticLightlikeSeries B epsilon ((𝓕 full) m))) =
        (1 : ℂ) • C.stateMap
          (bassettoAnalyticLightlikeSeries B epsilon ((𝓕 full) m)) := by
  have hvacuum := bennettSchwartz_boundState_is_massKernel_eigenstate
    kernel free full hfull m hfree hstate
  have hlight := bassettoAnalytic_vacuumLike_implies_lightLike_sameEigenvalue
    B epsilon 1 ((𝓕 full) m) hvacuum hseries
  have hcaticha := lightlike_eigenstate_to_caticha D C hlight.2.2
  exact ⟨hlight.1, hlight.2.1, hlight.2.2, hcaticha.1, hcaticha.2⟩

/-- The same transported functional state may be evaluated by any complex
linear readout, and Caticha's minimally coupled derivative then obeys the
existing exact gauge-covariance theorem. -/
lemma bennett_bassetto_catichaQED_gauge_covariant
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    {𝒯c : Type uFc} {𝒾c : Type uSc}
    [AddCommGroup 𝒯c] [Module ℂ 𝒯c]
    [AddCommGroup 𝒾c] [Module ℂ 𝒾c]
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    {lightKernel : State →ₗ[ℂ] State}
    (C : BassettoCatichaIntertwiner D lightKernel)
    (readout : 𝒯c →ₗ[ℂ] ℂ) (psi : State)
    {ι : Type*} (Dpsi : ι → ℂ) (q hbar c : ℝ)
    (A dxi : ι → ℝ) (u : ℂ) :
    catichaQEDCovariantDerivative
        (fun a => u * (Dpsi a + Complex.I * ((q / (hbar * c)) * dxi a : ℝ) *
          readout (C.stateMap psi)))
        q hbar c (fun a => A a + dxi a) (u * readout (C.stateMap psi)) =
      fun a => u * catichaQEDCovariantDerivative Dpsi q hbar c A
        (readout (C.stateMap psi)) a :=
  catichaQEDCovariantDerivative_gauge_covariant Dpsi q hbar c A dxi
    (readout (C.stateMap psi)) u

/-! ## D. Conditional curved-spacetime QED capstone -/

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

variable {𝒯c : Type uFc} {𝒾c : Type uSc}
variable [AddCommGroup 𝒯c] [Module ℂ 𝒯c]
variable [AddCommGroup 𝒾c] [Module ℂ 𝒾c]
variable {𝒯fr : Type uFr} {𝒬er : Type uSr}
variable [AddCommGroup 𝒯fr] [Module ℝ 𝒯fr]
variable [AddCommGroup 𝒬er] [Module ℝ 𝒬er]

variable {d : ℕ}
variable {g : PseudoRiemannianMetric E H M n I}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {sign : Fin d → ℝ}
variable {frame : Fin d → ∀ x : M, TangentSpace I x}

/-- The final identification needed to place a transported Bassetto state on
the already established Caticha--intrinsic-Maxwell causal carrier. The source
assignment and equality are explicit because neither cited paper constructs a
canonical map between these unlike state spaces. -/
structure BennettBassettoCatichaMaxwellAdapter
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (lightKernel : State →ₗ[ℂ] State) where
  caticha : BassettoCatichaIntertwiner D lightKernel
  maxwellSource : State → 𝒬er
  causalState_compat : ∀ psi,
    caticha.stateMap psi =
      A.fieldMap (IntrinsicMaxwellGreenData.causalPropagator I G (maxwellSource psi))

/-- **Bennett--Bassetto--Caticha curved-QED chain.** Bennett's mass-sector
Bethe--Salpeter state, after the certified Bassetto lightlike continuation, is
a Caticha functional-generator eigenmode on the same declared carrier as a
global homogeneous intrinsic Maxwell causal field. The accompanying two-point
carrier is Hermitian, positive, CCR compatible, and microlocal/Hadamard.

This is a conditional free-field/common-carrier theorem. Bassetto analyticity,
the state/source identification, global Green data, and Hadamard data remain
premises; no interacting curved-spacetime QED construction is claimed. -/
lemma bennett_bassetto_caticha_curvedQED_chain
    {StateTau : Type uTau} [AddCommGroup StateTau] [Module ℂ StateTau]
    {State : Type uState} [AddCommGroup State] [Module ℂ State]
    (Bennett : BennettTauFourierData StateTau State)
    (freeTau fullTau : StateTau)
    (hfull : SatisfiesInhomogeneousBetheSalpeter
      Bennett.tauKernel freeTau fullTau)
    (m : ℂ)
    (hfree : Bennett.tauFourier m freeTau = 0)
    (hstate : Bennett.tauFourier m fullTau ≠ 0)
    {lightKernel : State →ₗ[ℂ] State}
    (L : BassettoLadderLiftData State (Bennett.massKernel m) lightKernel)
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (B : BennettBassettoCatichaMaxwellAdapter I D G A lightKernel)
    {Ξ : Type uXi} (Q : ContinuumHadamardTwoPoint 𝒯c Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport Q.positiveFrequencyCone
      Q.positiveFrequencyCone) :
    SatisfiesInhomogeneousBetheSalpeter (Bennett.massKernel m)
        (Bennett.tauFourier m freeTau) (Bennett.tauFourier m fullTau) ∧
      L.totalMomentum ≠ 0 ∧
      Lorentz.Vector.minkowskiProduct
        L.totalMomentum L.totalMomentum = 0 ∧
      IsBetheSalpeterEigenstate lightKernel 1
        (L.lift (Bennett.tauFourier m fullTau)) ∧
      B.caticha.stateMap (L.lift (Bennett.tauFourier m fullTau)) ≠ 0 ∧
      continuumSmearedSchrodingerGenerator D.lapse D.shift D.Hperp D.Hi
          (B.caticha.stateMap (L.lift (Bennett.tauFourier m fullTau))) =
        (1 : ℂ) • B.caticha.stateMap (L.lift (Bennett.tauFourier m fullTau)) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField
          (IntrinsicMaxwellGreenData.causalPropagator I G
            (B.maxwellSource (L.lift (Bennett.tauFourier m fullTau))))) 0 ∧
      B.caticha.stateMap (L.lift (Bennett.tauFourier m fullTau)) =
        D.causalPropagator
          (A.sourceMap
            (B.maxwellSource (L.lift (Bennett.tauFourier m fullTau)))) ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift D.Hperp D.Hi
            (D.causalPropagator
              (A.sourceMap
                (B.maxwellSource
                  (L.lift (Bennett.tauFourier m fullTau)))))) = 0 ∧
      IsHermitianTwoPoint
        (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsPositiveTwoPoint
        (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsCCRCompatibleTwoPoint
        (D.causalHadamardCarrier Q transport hcone).twoPoint
        (D.causalHadamardCarrier Q transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (D.causalHadamardCarrier Q transport hcone).wavefront
        (D.causalHadamardCarrier Q transport hcone).positiveFrequencyCone := by
  have hbennett :=
    bennett_tauFourier_carries_integralEquation Bennett freeTau fullTau hfull m
  have hpsi :=
    bennett_boundState_is_massKernel_eigenstate Bennett freeTau fullTau
      hfull m hfree hstate
  have hlight := bassetto_vacuumLike_implies_lightLike_sameEigenvalue L hpsi
  have hcaticha := lightlike_eigenstate_to_caticha D B.caticha hlight.2.2
  have hcurved :=
    ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_chain
      I D G A
        (B.maxwellSource (L.lift (Bennett.tauFourier m fullTau)))
        Q transport hcone
  refine ⟨hbennett, hlight.1, hlight.2.1, hlight.2.2, hcaticha.1, hcaticha.2,
    hcurved.1, ?_, hcurved.2.2.1, hcurved.2.2.2.1,
    hcurved.2.2.2.2.1, hcurved.2.2.2.2.2.1, hcurved.2.2.2.2.2.2⟩
  rw [B.causalState_compat]
  exact hcurved.2.1

universe uSpin uDS uDF uMS uMF

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter

/-! ## E. Intrinsic curved parameterized Dirac carrier -/

section CurvedParameterizedDirac

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M]
variable {d : ℕ}
variable (Spinor : M → Type uSpin)
variable [∀ x, NormedAddCommGroup (Spinor x)]
variable [∀ x, InnerProductSpace ℂ (Spinor x)]

/-- A Bennett wavefunction is a spinor section on spacetime carrying an
additional independent real evolution parameter. -/
abbrev CurvedBennettSection := ∀ x : M, ℝ → Spinor x

/-- A real electromagnetic one-form on the spacetime tangent bundle. -/
abbrev CurvedBennettPotential (M : Type w) [TopologicalSpace M]
    [ChartedSpace H M] :=
  ∀ x : M, TangentSpace I x → ℝ

/-- The tangent-vector current before concatenation in Bennett's invariant
parameter. -/
abbrev CurvedBennettCurrent (M : Type w) [TopologicalSpace M]
    [ChartedSpace H M] :=
  ∀ x : M, ℝ → TangentSpace I x

/-- A global four-frame and its dual coframe on the selected spacetime.  This
is the precise geometric datum needed to turn the repository's canonical
gamma matrices into a tangent-vector Clifford action. -/
structure CurvedFourCoframe where
  frame : Fin 4 → ∀ x : M, TangentSpace I x
  components : ∀ x : M, TangentSpace I x →ₗ[ℝ] (Fin 4 → ℝ)
  dual : ∀ (x : M) (mu nu : Fin 4),
    components x (frame mu x) nu = if mu = nu then 1 else 0

/-- The concrete four-spinor Clifford action obtained by expanding a tangent
vector in the dual coframe and applying the existing Dirac gamma matrices. -/
noncomputable def coframeCliffordAction
    (F : CurvedFourCoframe (M := M) I) (x : M) (v : TangentSpace I x) :
    BennettDiracSpinor →ₗ[ℂ] BennettDiracSpinor :=
  ∑ mu : Fin 4,
    ((F.components x v mu : ℝ) : ℂ) • (bennettGammaOperator mu).toLinearMap

/-- On a dual frame vector the constructed Clifford action is exactly the
repository's canonical gamma operator `gamma^mu`. -/
lemma coframeCliffordAction_frame
    (F : CurvedFourCoframe (M := M) I) (x : M) (mu : Fin 4) :
    coframeCliffordAction I F x (F.frame mu x) =
      (bennettGammaOperator mu).toLinearMap := by
  classical
  unfold coframeCliffordAction
  rw [Finset.sum_eq_single mu]
  · rw [F.dual]
    simp
  · intro nu _ hne
    rw [F.dual]
    simp [hne.symm]
  · simp

/-- **The selected curved coframe realizes the Minkowski Clifford law.**
On every pair of frame vectors the constructed action has anticommutator
`2 η^{mu nu}` times the identity.  Thus `coframeCliffordAction` is not merely
a named tangent action: it reduces to the repository's proved gamma algebra. -/
lemma coframeCliffordAction_frame_anticomm
    (F : CurvedFourCoframe (M := M) I) (x : M) (mu nu : Fin 4) :
    (coframeCliffordAction I F x (F.frame mu x)).comp
          (coframeCliffordAction I F x (F.frame nu x)) +
        (coframeCliffordAction I F x (F.frame nu x)).comp
          (coframeCliffordAction I F x (F.frame mu x)) =
      if mu = nu then
        (2 * spaceTime.γ.diracMetricDiagonal mu) • LinearMap.id
      else 0 := by
  rw [coframeCliffordAction_frame, coframeCliffordAction_frame]
  exact bennettGammaOperator_anticomm mu nu

/-- The complex-bilinear Minkowski pairing induced on tangent vectors by the
selected dual coframe. -/
def coframeMinkowskiPair
    (F : CurvedFourCoframe (M := M) I) (x : M)
    (v w : TangentSpace I x) : ℂ :=
  bennettMinkowskiPair
    (fun mu => ((F.components x v mu : ℝ) : ℂ))
    (fun mu => ((F.components x w mu : ℝ) : ℂ))

/-- **Full tangent-vector Clifford law.**  The coframe action satisfies the
Minkowski anticommutator for arbitrary tangent vectors, not only selected
frame vectors. -/
lemma coframeCliffordAction_anticomm
    (F : CurvedFourCoframe (M := M) I) (x : M)
    (v w : TangentSpace I x) :
    (coframeCliffordAction I F x v).comp
          (coframeCliffordAction I F x w) +
        (coframeCliffordAction I F x w).comp
          (coframeCliffordAction I F x v) =
      (2 * coframeMinkowskiPair I F x v w) • LinearMap.id := by
  unfold coframeCliffordAction
  rw [← bennettGammaContractLinearMap_eq_sum,
    ← bennettGammaContractLinearMap_eq_sum]
  exact bennettGammaContractLinearMap_anticomm _ _

/-- The spin representation of a rigid orthonormal tetrad connection,
`Omega_c = (1/4) sum_ab Gamma_abc gamma^a gamma^b`, on Bennett's concrete
four-spinor carrier.  The connection coefficients are the existing
`TetradConnection`, whose `rigid` field is metric compatibility. -/
noncomputable def bennettTetradSpinConnectionMatrix
    (T : TetradConnection (Fin 4)) (c : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    ((1 / 4 : ℂ) * ((T.Γ a b c : ℝ) : ℂ)) •
      (spaceTime.γ a * spaceTime.γ b)

/-- Operator realization of the tetrad spin-connection matrix. -/
noncomputable def bennettTetradSpinConnectionOperator
    (T : TetradConnection (Fin 4)) (c : Fin 4) :
    BennettDiracSpinor →ₗ[ℂ] BennettDiracSpinor :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    ((1 / 4 : ℂ) * ((T.Γ a b c : ℝ) : ℂ)) •
      ((bennettGammaOperator a).toLinearMap.comp
        (bennettGammaOperator b).toLinearMap)

/-- The rigid tetrad spin-connection matrix is compatible with Clifford
multiplication.  With the repository's all-lowered connection convention,
`[Omega_c, gamma^d] = eta_dd sum_a Gamma_adc gamma^a`.

The proof uses `bennettGamma_bivector_commutator` and the metric-compatibility
antisymmetry `T.rigid`; it is not a componentwise gamma-matrix postulate. -/
lemma bennettTetradSpinConnectionMatrix_comm_gamma
    (T : TetradConnection (Fin 4)) (c d : Fin 4) :
    bennettTetradSpinConnectionMatrix T c * spaceTime.γ d -
        spaceTime.γ d * bennettTetradSpinConnectionMatrix T c =
      spaceTime.γ.diracMetricDiagonal d •
        (∑ a : Fin 4,
          ((T.Γ a d c : ℝ) : ℂ) • spaceTime.γ a) := by
  simp only [bennettTetradSpinConnectionMatrix, Finset.sum_mul,
    Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub,
    bennettGamma_bivector_commutator]
  simp only [smul_sub, Finset.sum_sub_distrib]
  simp
  simp_rw [T.rigid d]
  simp only [Complex.ofReal_neg, mul_neg, neg_smul]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  module

/-- The vector-representation connection action on a gamma direction. -/
noncomputable def bennettTetradVectorConnectionOperator
    (T : TetradConnection (Fin 4)) (c d : Fin 4) :
    BennettDiracSpinor →ₗ[ℂ] BennettDiracSpinor :=
  spaceTime.γ.diracMetricDiagonal d •
    (∑ a : Fin 4,
      ((T.Γ a d c : ℝ) : ℂ) •
        (bennettGammaOperator a).toLinearMap)

/-- **Concrete spin/Clifford compatibility.**  The commutator of Bennett's
spin connection with `gamma^d` is exactly the induced vector-connection
action. -/
lemma bennettTetradSpinConnectionOperator_comm_gamma
    (T : TetradConnection (Fin 4)) (c d : Fin 4) :
    (bennettTetradSpinConnectionOperator T c).comp
          (bennettGammaOperator d).toLinearMap -
        (bennettGammaOperator d).toLinearMap.comp
          (bennettTetradSpinConnectionOperator T c) =
      bennettTetradVectorConnectionOperator T c d := by
  classical
  have mulVec_sum
      (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ) :
      Matrix.mulVec (∑ i, A i) v = ∑ i, Matrix.mulVec (A i) v := by
    simp [Fin.sum_univ_four, Matrix.add_mulVec]
  apply LinearMap.ext
  intro psi
  apply (EuclideanSpace.equiv (Fin 4) ℂ).injective
  simp [bennettTetradSpinConnectionOperator,
    bennettTetradVectorConnectionOperator, bennettGammaOperator,
    EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv,
    PiLp.coe_symm_continuousLinearEquiv, Matrix.mulVec_mulVec]
  have h := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℂ => Matrix.mulVec A psi.ofLp)
    (bennettTetradSpinConnectionMatrix_comm_gamma T c d)
  simpa [bennettTetradSpinConnectionMatrix, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mulVec,
    Matrix.smul_mulVec, mulVec_sum] using h

/-- The spin connection is determined by the tetrad commutator coefficients
through the already proved Koszul/Levi--Civita identity.  This is the explicit
coefficient-level Levi--Civita content of the Bennett spin derivative. -/
lemma bennettTetradSpinConnectionOperator_eq_koszul
    (T : TetradConnection (Fin 4)) (c : Fin 4) :
    bennettTetradSpinConnectionOperator T c =
      ∑ a : Fin 4, ∑ b : Fin 4,
        ((1 / 4 : ℂ) *
          ((((T.commCoeff c a b + T.commCoeff b a c -
            T.commCoeff a b c) / 2 : ℝ)) : ℂ)) •
          ((bennettGammaOperator a).toLinearMap.comp
            (bennettGammaOperator b).toLinearMap) := by
  unfold bennettTetradSpinConnectionOperator
  simp_rw [T.koszul]

/-- Contract the tetrad spin connection with an arbitrary tangent vector by
the selected dual coframe. -/
noncomputable def coframeSpinConnectionAction
    (F : CurvedFourCoframe (M := M) I)
    (T : M → TetradConnection (Fin 4))
    (x : M) (v : TangentSpace I x) :
    BennettDiracSpinor →ₗ[ℂ] BennettDiracSpinor :=
  ∑ c : Fin 4,
    ((F.components x v c : ℝ) : ℂ) •
      bennettTetradSpinConnectionOperator (T x) c

/-- On a selected frame vector, coframe contraction recovers exactly the
corresponding tetrad spin-connection operator. -/
lemma coframeSpinConnectionAction_frame
    (F : CurvedFourCoframe (M := M) I)
    (T : M → TetradConnection (Fin 4))
    (x : M) (c : Fin 4) :
    coframeSpinConnectionAction I F T x (F.frame c x) =
      bennettTetradSpinConnectionOperator (T x) c := by
  classical
  unfold coframeSpinConnectionAction
  rw [Finset.sum_eq_single c]
  · rw [F.dual]
    simp
  · intro b _ hbc
    rw [F.dual]
    simp [hbc.symm]
  · simp

/-- The concrete curved spin derivative
`nabla_v psi = partial_v psi + Omega(v) psi`.  It upgrades the previously
abstract spin-derivative slot to a reusable constructor from a directional
derivative, a dual coframe, and the repository's Levi--Civita tetrad
connection. -/
noncomputable def coframeSpinCovariantDerivative
    (F : CurvedFourCoframe (M := M) I)
    (T : M → TetradConnection (Fin 4))
    (ordinaryDerivative :
      CurvedBennettSection (fun _ : M => BennettDiracSpinor) →ₗ[ℂ]
        (∀ x : M, ℝ → TangentSpace I x → BennettDiracSpinor)) :
    CurvedBennettSection (fun _ : M => BennettDiracSpinor) →ₗ[ℂ]
      (∀ x : M, ℝ → TangentSpace I x → BennettDiracSpinor) where
  toFun psi x tau v :=
    ordinaryDerivative psi x tau v +
      coframeSpinConnectionAction I F T x v (psi x tau)
  map_add' psi phi := by
    funext x tau v
    simp
    abel
  map_smul' z psi := by
    funext x tau v
    simp

/-- In a coframe direction the constructed covariant derivative is the
ordinary directional derivative plus the Koszul-determined spin connection. -/
lemma coframeSpinCovariantDerivative_frame
    (F : CurvedFourCoframe (M := M) I)
    (T : M → TetradConnection (Fin 4))
    (ordinaryDerivative :
      CurvedBennettSection (fun _ : M => BennettDiracSpinor) →ₗ[ℂ]
        (∀ x : M, ℝ → TangentSpace I x → BennettDiracSpinor))
    (psi : CurvedBennettSection (fun _ : M => BennettDiracSpinor))
    (x : M) (tau : ℝ) (c : Fin 4) :
    coframeSpinCovariantDerivative I F T ordinaryDerivative
        psi x tau (F.frame c x) =
      ordinaryDerivative psi x tau (F.frame c x) +
        bennettTetradSpinConnectionOperator (T x) c (psi x tau) := by
  change
    ordinaryDerivative psi x tau (F.frame c x) +
        coframeSpinConnectionAction I F T x (F.frame c x) (psi x tau) =
      ordinaryDerivative psi x tau (F.frame c x) +
        bennettTetradSpinConnectionOperator (T x) c (psi x tau)
  rw [coframeSpinConnectionAction_frame]

/-- Geometric and analytic data for Bennett's parameterized Dirac operator on
a curved spinor carrier. The local Noether identity is recorded independently
of the field equation; current conservation will be derived from the equation. -/
structure CurvedParametrizedDiracData where
  /-- Global frame used to contract the spin covariant derivative. -/
  frame : Fin d → ∀ x : M, TangentSpace I x
  /-- Clifford action of tangent vectors on each spinor fiber. -/
  cliffordAction :
    ∀ x : M, TangentSpace I x → Spinor x →ₗ[ℂ] Spinor x
  /-- Derivative in the independent Bennett parameter. -/
  parameterDerivative :
    CurvedBennettSection Spinor →ₗ[ℂ] CurvedBennettSection Spinor
  /-- Spin covariant derivative in spacetime directions. -/
  spinCovariantDerivative :
    CurvedBennettSection Spinor →ₗ[ℂ]
      (∀ x : M, ℝ → TangentSpace I x → Spinor x)
  /-- Derivative of the scalar density in the invariant parameter. -/
  densityTauDerivative :
    CurvedBennettSection Spinor → M → ℝ → ℂ
  /-- Covariant spacetime divergence of a tangent-current history. -/
  currentDivergence : CurvedBennettCurrent I M → M → ℝ → ℂ
  /-- The curved Dirac Noether identity. This is a compatibility law of the
  spin connection and Clifford pairing, not an assumed conservation law. -/
  noetherIdentity : ∀ (q : ℝ) (A : CurvedBennettPotential I M)
      (psi : CurvedBennettSection Spinor) (x : M) (tau : ℝ),
    densityTauDerivative psi x tau +
        currentDivergence
          (fun y s => ∑ a,
            (⟪psi y s,
              cliffordAction y (frame a y) (psi y s)⟫_ℂ).re • frame a y)
          x tau =
      ⟪psi x tau,
        parameterDerivative psi x tau +
          ∑ a, cliffordAction x (frame a x)
            (spinCovariantDerivative psi x tau (frame a x) +
              (Complex.I * ((q * A x (frame a x) : ℝ) : ℂ)) • psi x tau)⟫_ℂ +
      ⟪parameterDerivative psi x tau +
          ∑ a, cliffordAction x (frame a x)
            (spinCovariantDerivative psi x tau (frame a x) +
              (Complex.I * ((q * A x (frame a x) : ℝ) : ℂ)) • psi x tau),
        psi x tau⟫_ℂ

namespace CurvedParametrizedDiracData

variable {I Spinor}

/-- The minimally coupled curved Bennett operator
`∂_tau + gamma^a (nabla_a + i q A_a)`. -/
def operator
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A : CurvedBennettPotential I M) :
    CurvedBennettSection Spinor → CurvedBennettSection Spinor :=
  fun psi x tau =>
    D.parameterDerivative psi x tau +
      ∑ a, D.cliffordAction x (D.frame a x)
        (D.spinCovariantDerivative psi x tau (D.frame a x) +
          (Complex.I * ((q * A x (D.frame a x) : ℝ) : ℂ)) • psi x tau)

/-- The real tangent current `j = sum_a Re <psi,gamma(e_a)psi> e_a`. -/
def vectorCurrent
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (psi : CurvedBennettSection Spinor) : CurvedBennettCurrent I M :=
  fun x tau => ∑ a,
    (⟪psi x tau,
      D.cliffordAction x (D.frame a x) (psi x tau)⟫_ℂ).re • D.frame a x

/-- Local five-current continuity for a solution of the curved parameterized
Dirac equation. It is a consequence of the Noether identity. -/
lemma localContinuity_of_solves
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A : CurvedBennettPotential I M)
    (psi : CurvedBennettSection Spinor)
    (hpsi : D.operator q A psi = 0) (x : M) (tau : ℝ) :
    D.densityTauDerivative psi x tau +
      D.currentDivergence (D.vectorCurrent psi) x tau = 0 := by
  change D.densityTauDerivative psi x tau +
    D.currentDivergence
      (fun y s => ∑ a,
        (⟪psi y s, D.cliffordAction y (D.frame a y) (psi y s)⟫_ℂ).re •
          D.frame a y) x tau = 0
  rw [D.noetherIdentity q A psi x tau]
  have hzero := congrFun (congrFun hpsi x) tau
  simp only [Pi.zero_apply] at hzero
  change ⟪psi x tau, D.operator q A psi x tau⟫_ℂ +
    ⟪D.operator q A psi x tau, psi x tau⟫_ℂ = 0
  rw [hzero]
  simp

/-- Gauge transformation data at the derivative level. These are precisely
the two product rules needed to prove covariance of the full Dirac operator. -/
structure GaugeTransformation
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A A' : CurvedBennettPotential I M) where
  phase : M → ℂ
  phase_norm : ∀ x, ‖phase x‖ = 1
  parameterDerivative_compat :
    ∀ psi x tau,
      D.parameterDerivative (fun y s => phase y • psi y s) x tau =
        phase x • D.parameterDerivative psi x tau
  covariantDerivative_compat :
    ∀ psi x tau a,
      D.spinCovariantDerivative (fun y s => phase y • psi y s)
          x tau (D.frame a x) +
          (Complex.I * ((q * A' x (D.frame a x) : ℝ) : ℂ)) •
            (phase x • psi x tau) =
        phase x •
          (D.spinCovariantDerivative psi x tau (D.frame a x) +
            (Complex.I * ((q * A x (D.frame a x) : ℝ) : ℂ)) • psi x tau)

/-- The full curved parameterized Dirac operator is gauge covariant whenever
the spin and parameter derivatives obey their geometric product rules. -/
lemma operator_gauge_covariant
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A A' : CurvedBennettPotential I M)
    (G : D.GaugeTransformation q A A')
    (psi : CurvedBennettSection Spinor) :
    D.operator q A' (fun x tau => G.phase x • psi x tau) =
      fun x tau => G.phase x • D.operator q A psi x tau := by
  funext x tau
  simp only [operator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [G.parameterDerivative_compat]
  simp_rw [G.covariantDerivative_compat, map_smul]
  simp only [smul_add, Finset.smul_sum]

/-- The curved vector current is invariant under unit-norm spinor gauge
phases. -/
lemma vectorCurrent_gauge_invariant
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A A' : CurvedBennettPotential I M)
    (G : D.GaugeTransformation q A A')
    (psi : CurvedBennettSection Spinor) :
    D.vectorCurrent (fun x tau => G.phase x • psi x tau) =
      D.vectorCurrent psi := by
  funext x tau
  apply Finset.sum_congr rfl
  intro a ha
  simp only [vectorCurrent, map_smul]
  rw [inner_smul_left, inner_smul_right]
  have hnormSq : starRingEnd ℂ (G.phase x) * G.phase x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      G.phase_norm, one_pow]
    norm_num
  rw [← mul_assoc, hnormSq, one_mul]

/-- Gauge covariance transports every solution of the curved parameterized
Dirac equation to a solution in the transformed potential.  This is a
conclusion of the two derivative product rules in `GaugeTransformation`, not
an additional equation-of-motion premise. -/
lemma GaugeTransformation.maps_solution
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A A' : CurvedBennettPotential I M)
    (G : D.GaugeTransformation q A A')
    (psi : CurvedBennettSection Spinor)
    (hpsi : D.operator q A psi = 0) :
    D.operator q A' (fun x tau => G.phase x • psi x tau) = 0 := by
  rw [D.operator_gauge_covariant q A A' G psi, hpsi]
  funext x tau
  simp

/-- The gauge-transported solution satisfies the same local five-current
continuity law and has exactly the original vector current. -/
lemma GaugeTransformation.transported_solution_continuity_and_current
    (D : CurvedParametrizedDiracData (d := d) I Spinor)
    (q : ℝ) (A A' : CurvedBennettPotential I M)
    (G : D.GaugeTransformation q A A')
    (psi : CurvedBennettSection Spinor)
    (hpsi : D.operator q A psi = 0) (x : M) (tau : ℝ) :
    D.densityTauDerivative (fun y s => G.phase y • psi y s) x tau +
        D.currentDivergence
          (D.vectorCurrent (fun y s => G.phase y • psi y s)) x tau = 0 ∧
      D.vectorCurrent (fun y s => G.phase y • psi y s) =
        D.vectorCurrent psi := by
  refine ⟨D.localContinuity_of_solves q A'
    (fun y s => G.phase y • psi y s) (G.maps_solution D q A A' psi hpsi) x tau, ?_⟩
  exact D.vectorCurrent_gauge_invariant q A A' G psi

end CurvedParametrizedDiracData

end CurvedParameterizedDirac

/-! ## F. Dirac Green operators derived from causal Cauchy well-posedness -/

section CurvedDiracGreen

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M]
variable {d : ℕ}
variable {Spinor : M → Type uSpin}
variable [∀ x, NormedAddCommGroup (Spinor x)]
variable [∀ x, InnerProductSpace ℂ (Spinor x)]
variable (D : CurvedParametrizedDiracData (d := d) I Spinor)
variable (q : ℝ) (A : CurvedBennettPotential I M)

variable {𝒮 : Type uDS} {𝒟 : Type uDF}
variable [AddCommGroup 𝒮] [Module ℂ 𝒮]
variable [AddCommGroup 𝒟] [Module ℂ 𝒟]

/-- Analytic Green data for the curved parameterized Dirac operator. -/
structure CurvedParametrizedDiracGreenData where
  realizeField : 𝒟 →ₗ[ℂ] CurvedBennettSection Spinor
  realizeSource : 𝒮 →ₗ[ℂ] CurvedBennettSection Spinor
  realizeSource_injective : Function.Injective realizeSource
  diracOperator : 𝒟 →ₗ[ℂ] 𝒮
  retarded : 𝒮 →ₗ[ℂ] 𝒟
  advanced : 𝒮 →ₗ[ℂ] 𝒟
  realizes_dirac : ∀ field,
    realizeSource (diracOperator field) =
      D.operator q A (realizeField field)
  dirac_retarded : Function.RightInverse retarded diracOperator
  dirac_advanced : Function.RightInverse advanced diracOperator
  retardedSector : Submodule ℂ 𝒟
  advancedSector : Submodule ℂ 𝒟
  retarded_mem : ∀ source, retarded source ∈ retardedSector
  advanced_mem : ∀ source, advanced source ∈ advancedSector
  dirac_injectiveOn_retarded : Set.InjOn diracOperator retardedSector
  dirac_injectiveOn_advanced : Set.InjOn diracOperator advancedSector

/-- Causal Cauchy existence and uniqueness before linearity of the solution
selectors has been derived. -/
structure WellPosedCurvedParametrizedDiracCauchyData where
  realizeField : 𝒟 →ₗ[ℂ] CurvedBennettSection Spinor
  realizeSource : 𝒮 →ₗ[ℂ] CurvedBennettSection Spinor
  realizeSource_injective : Function.Injective realizeSource
  diracOperator : 𝒟 →ₗ[ℂ] 𝒮
  retardedSolution : 𝒮 → 𝒟
  advancedSolution : 𝒮 → 𝒟
  realizes_dirac : ∀ field,
    realizeSource (diracOperator field) =
      D.operator q A (realizeField field)
  dirac_retarded : Function.RightInverse retardedSolution diracOperator
  dirac_advanced : Function.RightInverse advancedSolution diracOperator
  retardedSector : Submodule ℂ 𝒟
  advancedSector : Submodule ℂ 𝒟
  retarded_mem : ∀ source, retardedSolution source ∈ retardedSector
  advanced_mem : ∀ source, advancedSolution source ∈ advancedSector
  dirac_injectiveOn_retarded : Set.InjOn diracOperator retardedSector
  dirac_injectiveOn_advanced : Set.InjOn diracOperator advancedSector

namespace WellPosedCurvedParametrizedDiracCauchyData

variable {I D q A}

lemma retardedSolution_add
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    (f h : 𝒮) :
    C.retardedSolution (f + h) =
      C.retardedSolution f + C.retardedSolution h := by
  apply C.dirac_injectiveOn_retarded
  · exact C.retarded_mem _
  · exact C.retardedSector.add_mem (C.retarded_mem _) (C.retarded_mem _)
  · rw [C.dirac_retarded, map_add, C.dirac_retarded, C.dirac_retarded]

lemma retardedSolution_smul
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    (c : ℂ) (f : 𝒮) :
    C.retardedSolution (c • f) = c • C.retardedSolution f := by
  apply C.dirac_injectiveOn_retarded
  · exact C.retarded_mem _
  · exact C.retardedSector.smul_mem c (C.retarded_mem _)
  · rw [C.dirac_retarded, map_smul, C.dirac_retarded]

def retarded
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) : 𝒮 →ₗ[ℂ] 𝒟 where
  toFun := C.retardedSolution
  map_add' := C.retardedSolution_add
  map_smul' := C.retardedSolution_smul

lemma advancedSolution_add
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    (f h : 𝒮) :
    C.advancedSolution (f + h) =
      C.advancedSolution f + C.advancedSolution h := by
  apply C.dirac_injectiveOn_advanced
  · exact C.advanced_mem _
  · exact C.advancedSector.add_mem (C.advanced_mem _) (C.advanced_mem _)
  · rw [C.dirac_advanced, map_add, C.dirac_advanced, C.dirac_advanced]

lemma advancedSolution_smul
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    (c : ℂ) (f : 𝒮) :
    C.advancedSolution (c • f) = c • C.advancedSolution f := by
  apply C.dirac_injectiveOn_advanced
  · exact C.advanced_mem _
  · exact C.advancedSector.smul_mem c (C.advanced_mem _)
  · rw [C.dirac_advanced, map_smul, C.dirac_advanced]

def advanced
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) : 𝒮 →ₗ[ℂ] 𝒟 where
  toFun := C.advancedSolution
  map_add' := C.advancedSolution_add
  map_smul' := C.advancedSolution_smul

/-- Causal existence and uniqueness construct complex-linear Dirac Green
operators; their linearity is not an additional premise. -/
def toGreenData
    (C : WellPosedCurvedParametrizedDiracCauchyData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) :
    CurvedParametrizedDiracGreenData I D q A (𝒮 := 𝒮) (𝒟 := 𝒟) where
  realizeField := C.realizeField
  realizeSource := C.realizeSource
  realizeSource_injective := C.realizeSource_injective
  diracOperator := C.diracOperator
  retarded := C.retarded
  advanced := C.advanced
  realizes_dirac := C.realizes_dirac
  dirac_retarded := C.dirac_retarded
  dirac_advanced := C.dirac_advanced
  retardedSector := C.retardedSector
  advancedSector := C.advancedSector
  retarded_mem := C.retarded_mem
  advanced_mem := C.advanced_mem
  dirac_injectiveOn_retarded := C.dirac_injectiveOn_retarded
  dirac_injectiveOn_advanced := C.dirac_injectiveOn_advanced

end WellPosedCurvedParametrizedDiracCauchyData

namespace CurvedParametrizedDiracGreenData

variable {I D q A}

/-- The retarded Green field solves the actual section-valued curved Bennett
equation. -/
lemma retarded_solves
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) (source : 𝒮) :
    D.operator q A (G.realizeField (G.retarded source)) =
      G.realizeSource source := by
  calc
    D.operator q A (G.realizeField (G.retarded source)) =
        G.realizeSource (G.diracOperator (G.retarded source)) :=
      (G.realizes_dirac _).symm
    _ = G.realizeSource source := by rw [G.dirac_retarded]

/-- Retarded minus advanced is the curved Dirac causal propagator. -/
def causalPropagator
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) : 𝒮 →ₗ[ℂ] 𝒟 :=
  G.retarded - G.advanced

lemma dirac_causalPropagator_eq_zero
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) (source : 𝒮) :
    G.diracOperator (G.causalPropagator source) = 0 := by
  rw [causalPropagator, LinearMap.sub_apply, map_sub,
    G.dirac_retarded, G.dirac_advanced, sub_self]

/-- The causal Green difference is a homogeneous solution of the geometric
curved parameterized Dirac equation. -/
lemma causalPropagator_solves_homogeneous
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) (source : 𝒮) :
    D.operator q A (G.realizeField (G.causalPropagator source)) = 0 := by
  rw [← G.realizes_dirac]
  rw [G.dirac_causalPropagator_eq_zero, map_zero]

/-- The causal Dirac propagator is not only a homogeneous solution: its
section-valued field obeys Bennett's local five-current continuity equation.
This closes the Green/Noether link without assuming conservation separately. -/
lemma causalPropagator_localContinuity
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) (source : 𝒮) (x : M) (tau : ℝ) :
    D.densityTauDerivative
        (G.realizeField (G.causalPropagator source)) x tau +
      D.currentDivergence
        (D.vectorCurrent
          (G.realizeField (G.causalPropagator source))) x tau = 0 :=
  D.localContinuity_of_solves q A
    (G.realizeField (G.causalPropagator source))
    (G.causalPropagator_solves_homogeneous source) x tau

/-- The curved Dirac causal solution and a distributionally proved Hadamard
two-point function coexist on the selected continuum carrier.  The exact
wavefront equality follows from separate localized-Fourier regularity and
singularity theorems rather than from a bundled certificate field. -/
lemma causal_hadamard_chain
    [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟)) (source : 𝒮)
    {V : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Xi]
    (W : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ)
    (symp : 𝒟 →ₗ[ℝ] 𝒟 →ₗ[ℝ] ℝ)
    (hHermitian : IsHermitianSesquilinearTwoPoint W)
    (hPositive : IsPositiveSesquilinearTwoPoint W)
    (hCCR : IsCCRSesquilinearTwoPoint W symp)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒟) (V := V) (X := X) (Ξ := Xi) (W := W))
    (hregular : Dhad.IsRegularOutsideCone)
    (hsingular : Dhad.IsSingularOnCone) :
    D.operator q A (G.realizeField (G.causalPropagator source)) = 0 ∧
      (ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems
        W symp hHermitian hPositive hCCR Dhad hregular hsingular).wavefront =
          Dhad.hadamardCone :=
  ⟨G.causalPropagator_solves_homogeneous source,
    ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_wavefront_eq
      W symp hHermitian hPositive hCCR Dhad hregular hsingular⟩

/-- Pull an already established sesquilinear Hadamard carrier on Dirac fields
back to source space through the *constructed* retarded-minus-advanced Dirac
propagator.  The CCR symplectic pullback and positive-cone transport remain
explicit, while Hermiticity, positivity, CCR compatibility, and microlocal
support are derived by the shared AQFT pullback constructor. -/
noncomputable def causalSesquilinearHadamardCarrier
    [Module ℝ 𝒮] [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    {Xi : Type*}
    (H2 : ContinuumSesquilinearHadamardTwoPoint 𝒟 Xi)
    (symp : 𝒮 →ₗ[ℝ] 𝒮 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ phi psi,
      symp phi psi =
        H2.symplecticForm (G.causalPropagator phi) (G.causalPropagator psi))
    (transport : Xi → Xi)
    (hcone : Set.MapsTo transport H2.positiveFrequencyCone
      H2.positiveFrequencyCone) :
    ContinuumSesquilinearHadamardTwoPoint 𝒮 Xi :=
  H2.pullback G.causalPropagator symp symp_pullback transport hcone

/-- All four quasifree/Hadamard laws inherited by the Dirac causal pullback. -/
lemma causalSesquilinearHadamardCarrier_properties
    [Module ℝ 𝒮] [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    {Xi : Type*}
    (H2 : ContinuumSesquilinearHadamardTwoPoint 𝒟 Xi)
    (symp : 𝒮 →ₗ[ℝ] 𝒮 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ phi psi,
      symp phi psi =
        H2.symplecticForm (G.causalPropagator phi) (G.causalPropagator psi))
    (transport : Xi → Xi)
    (hcone : Set.MapsTo transport H2.positiveFrequencyCone
      H2.positiveFrequencyCone) :
    IsHermitianSesquilinearTwoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).twoPoint ∧
      IsPositiveSesquilinearTwoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).twoPoint ∧
      IsCCRSesquilinearTwoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).twoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).wavefront
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).positiveFrequencyCone :=
  H2.pullback_properties G.causalPropagator symp
    symp_pullback transport hcone

/-- Package the analytic transport from a field Hadamard distribution to the
source two-point function pulled back through the causal Dirac propagator.
The target distribution and probes may live on a different Schwartz test
space and use a different probe index type. -/
def causalDistributionalHadamardTransport
    [Module ℝ 𝒮] [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒟) (V := V) (X := X) (Ξ := Xi) (W := W))
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒮 → 𝒮 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint G.causalPropagator W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    Dhad.Transport (𝒟 := 𝒮) (V' := V')
      (W' := pullbackSesquilinearTwoPoint G.causalPropagator W) where
  distribution := sourceDistribution
  smearing := sourceSmearing
  represents := represents
  probe := sourceProbe
  probeTransport := probeTransport

/-- Package the source distributional realization obtained through the
causal Dirac pullback.  This contains only data; its Hadamard theorem is
derived separately from microlocal estimates and probe transport. -/
def causalDistributionalHadamardData
    [Module ℝ 𝒮] [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒟) (V := V) (X := X) (Ξ := Xi) (W := W))
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒮 → 𝒮 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint G.causalPropagator W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    DistributionalHadamardData
      (𝒜 := 𝒮) (V := V') (X := X) (Ξ := Xi)
      (W := pullbackSesquilinearTwoPoint G.causalPropagator W) :=
  (G.causalDistributionalHadamardTransport W Dhad sourceDistribution
    sourceSmearing represents sourceProbe probeTransport).toData

/-- **Distributional causal Dirac--Hadamard propagation.**  The causal Green
difference is a homogeneous curved Dirac solution, and the distribution
representing its source-space two-point pullback has exactly the field
Hadamard wavefront cone whenever independent field/source probe families
cover the same base and conic regions and their evaluated pairings agree in
both directions.  The conclusion is a theorem of the Hadamard transport API, not
an abstract image-of-cone declaration. -/
lemma causal_dirac_distributional_hadamard_propagation
    [Module ℝ 𝒮] [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    (source : 𝒮)
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒟) (V := V) (X := X) (Ξ := Xi) (W := W))
    (hregular : Dhad.IsRegularOutsideCone)
    (hsingular : Dhad.IsSingularOnCone)
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒮 → 𝒮 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint G.causalPropagator W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    D.operator q A (G.realizeField (G.causalPropagator source)) = 0 ∧
      Physlib.Distribution.distributionalWavefrontSet
          sourceDistribution sourceProbe = Dhad.hadamardCone := by
  refine ⟨G.causalPropagator_solves_homogeneous source, ?_⟩
  exact (G.causalDistributionalHadamardTransport W Dhad
    sourceDistribution sourceSmearing represents sourceProbe
    probeTransport).wavefront_eq hregular hsingular

/-- **Causal Dirac--Hadamard propagation.**  The same causal Green difference
is simultaneously a homogeneous curved Bennett--Dirac solution and the field
map pulling a corrected quasifree Hadamard carrier to sources.  Unlike the
older conjunction with an unrelated certificate, the two-point carrier is
now constructed through `G.causalPropagator` itself.

The theorem is intentionally conditional on the field Hadamard carrier, the
symplectic pullback identity, and a cone-preserving covector transport; it does
not infer global hyperbolicity or propagation of singularities from algebra. -/
lemma causal_dirac_hadamard_propagation
    [Module ℝ 𝒮] [Module ℝ 𝒟]
    (G : CurvedParametrizedDiracGreenData I D q A
      (𝒮 := 𝒮) (𝒟 := 𝒟))
    (source : 𝒮)
    {Xi : Type*}
    (H2 : ContinuumSesquilinearHadamardTwoPoint 𝒟 Xi)
    (symp : 𝒮 →ₗ[ℝ] 𝒮 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ phi psi,
      symp phi psi =
        H2.symplecticForm (G.causalPropagator phi) (G.causalPropagator psi))
    (transport : Xi → Xi)
    (hcone : Set.MapsTo transport H2.positiveFrequencyCone
      H2.positiveFrequencyCone) :
    D.operator q A (G.realizeField (G.causalPropagator source)) = 0 ∧
      IsHermitianSesquilinearTwoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).twoPoint ∧
      IsPositiveSesquilinearTwoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).twoPoint ∧
      IsCCRSesquilinearTwoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).twoPoint
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).wavefront
        (G.causalSesquilinearHadamardCarrier H2 symp
          symp_pullback transport hcone).positiveFrequencyCone := by
  refine ⟨G.causalPropagator_solves_homogeneous source, ?_⟩
  exact G.causalSesquilinearHadamardCarrier_properties
    H2 symp symp_pullback transport hcone

end CurvedParametrizedDiracGreenData

end CurvedDiracGreen

/-! ## G. Self-consistent curved Maxwell--Dirac fixed point -/

section SelfConsistentMaxwellDirac

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M]
variable [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
variable {d : ℕ}
variable {Spinor : M → Type uSpin}
variable [∀ x, NormedAddCommGroup (Spinor x)]
variable [∀ x, InnerProductSpace ℂ (Spinor x)]
variable (D : CurvedParametrizedDiracData (d := d) I Spinor)
variable (q : ℝ)

variable {g : PseudoRiemannianMetric E H M n I}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {sign : Fin d → ℝ}
variable {frame : Fin d → ∀ x : M, TangentSpace I x}

variable {𝒟S : Type uDS} {𝒟F : Type uDF}
variable [AddCommGroup 𝒟S] [Module ℂ 𝒟S]
variable [NormedAddCommGroup 𝒟F] [NormedSpace ℂ 𝒟F] [CompleteSpace 𝒟F]
variable {ℳS : Type uMS} {ℳF : Type uMF}
variable [NormedAddCommGroup ℳS] [NormedSpace ℝ ℳS]
variable [NormedAddCommGroup ℳF] [NormedSpace ℝ ℳF] [CompleteSpace ℳF]

/-- The whole-line Bennett current on a curved spacetime, using the already
formalized Bochner concatenation in the invariant parameter. -/
def curvedBennettConcatenatedCurrent
    (psi : CurvedBennettSection Spinor) :
    ∀ x : M, TangentSpace I x :=
  fun x => ∑ a,
    bennettWholeLineConcatenatedCurrent
      (fun tau =>
        (⟪psi x tau,
          D.cliffordAction x (D.frame a x) (psi x tau)⟫_ℂ).re) •
      D.frame a x

/-- Data coupling a family of curved Dirac Green problems to one intrinsic
Maxwell Green problem. The nonlinear current is the actual whole-line
concatenation of the section-valued Dirac current. -/
structure CurvedMaxwellDiracCoupling
    (MG : IntrinsicMaxwellGreenData I g cov sign frame ℳS ℳF) where
  potentialOf : ℳF → CurvedBennettPotential I M
  realizeDiracField : 𝒟F →ₗ[ℂ] CurvedBennettSection Spinor
  diracGreen : ∀ potential : ℳF,
    CurvedParametrizedDiracGreenData I D q (potentialOf potential)
      (𝒮 := 𝒟S) (𝒟 := 𝒟F)
  diracGreen_realizeField : ∀ potential,
    (diracGreen potential).realizeField = realizeDiracField
  externalDiracSource : 𝒟S
  currentSource : 𝒟F → ℳS
  currentSource_realizes : ∀ psi,
    MG.realizeSource (currentSource psi) =
      curvedBennettConcatenatedCurrent I D (realizeDiracField psi)

namespace CurvedMaxwellDiracCoupling

variable (MG : IntrinsicMaxwellGreenData I g cov sign frame ℳS ℳF)

/-- One Picard step: solve Dirac in the current Maxwell potential, then solve
Maxwell with the whole-line concatenated Dirac current. -/
def update
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F)) : 𝒟F × ℳF → 𝒟F × ℳF :=
  fun state =>
    ((C.diracGreen state.2).retarded C.externalDiracSource,
      MG.retarded (C.currentSource state.1))

/-- A fixed point together with the two geometric field equations it
satisfies. -/
def IsSelfConsistentSolution
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F)) (state : 𝒟F × ℳF) : Prop :=
  update I D q MG C state = state ∧
    D.operator q (C.potentialOf state.2) (C.realizeDiracField state.1) =
      (C.diracGreen state.2).realizeSource C.externalDiracSource ∧
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
      (MG.realizeField state.2)
      (curvedBennettConcatenatedCurrent I D (C.realizeDiracField state.1))

/-- Componentwise analytic estimates for the nonlinear Maxwell--Dirac Picard
map.  The Dirac response is Lipschitz in the potential, the exact
whole-line current source is Lipschitz in the Dirac field, and the Maxwell
retarded Green map is represented by a bounded linear operator.  These are
the estimates a concrete PDE model must prove; the coupled contraction below
is derived from them. -/
structure ResponseBounds
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F)) where
  diracConstant : NNReal
  currentConstant : NNReal
  diracResponse_lipschitz :
    LipschitzWith diracConstant
      (fun potential : ℳF =>
        (C.diracGreen potential).retarded C.externalDiracSource)
  currentSource_lipschitz :
    LipschitzWith currentConstant C.currentSource
  maxwellRetarded : ℳS →L[ℝ] ℳF
  maxwellRetarded_eq : ∀ source,
    maxwellRetarded source = MG.retarded source

namespace ResponseBounds

/-- The Maxwell response to the exact concatenated Dirac current has
Lipschitz constant `‖G_ret‖ K_J`. -/
lemma maxwellResponse_lipschitz
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : ResponseBounds I D q MG C) :
    LipschitzWith (‖B.maxwellRetarded‖₊ * B.currentConstant)
      (fun psi : 𝒟F => MG.retarded (C.currentSource psi)) := by
  have h := B.maxwellRetarded.lipschitz.comp B.currentSource_lipschitz
  have heq :
      (fun psi : 𝒟F => MG.retarded (C.currentSource psi)) =
        B.maxwellRetarded ∘ C.currentSource := by
    funext psi
    exact (B.maxwellRetarded_eq (C.currentSource psi)).symm
  rw [heq]
  exact h

/-- The product update is Lipschitz with the maximum of the Dirac response
constant and the bounded Maxwell-current response constant. -/
lemma update_lipschitz
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : ResponseBounds I D q MG C) :
    LipschitzWith
      (max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant))
      (update I D q MG C) := by
  have hDirac : LipschitzWith B.diracConstant
      (fun state : 𝒟F × ℳF =>
        (C.diracGreen state.2).retarded C.externalDiracSource) := by
    intro state₁ state₂
    exact (B.diracResponse_lipschitz state₁.2 state₂.2).trans
      (mul_right_mono (le_max_right _ _))
  have hMaxwell :
      LipschitzWith (‖B.maxwellRetarded‖₊ * B.currentConstant)
        (fun state : 𝒟F × ℳF =>
          MG.retarded (C.currentSource state.1)) := by
    intro state₁ state₂
    exact ((B.maxwellResponse_lipschitz I D q MG C) state₁.1 state₂.1).trans
      (mul_right_mono (le_max_left _ _))
  change LipschitzWith
    (max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant))
    (fun state : 𝒟F × ℳF =>
      ((C.diracGreen state.2).retarded C.externalDiracSource,
        MG.retarded (C.currentSource state.1)))
  exact hDirac.prodMk hMaxwell

/-- A numerical small-response bound constructs the contraction certificate;
the whole coupled map is no longer assumed contracting as a black box. -/
lemma contractingWith_update
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : ResponseBounds I D q MG C)
    (hsmall :
      max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant) < 1) :
    ContractingWith
      (max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant))
      (update I D q MG C) :=
  ⟨hsmall, B.update_lipschitz I D q MG C⟩

end ResponseBounds

/-- Differential estimates from which the componentwise response bounds are
constructed by the Banach-space mean-value theorem.  This interface matches
the form in which resolvent and nonlinear-current estimates are normally
proved: differentiability plus a uniform operator-norm bound. -/
structure DifferentialResponseBounds
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F)) where
  diracConstant : NNReal
  currentConstant : NNReal
  diracResponse_differentiable :
    Differentiable ℝ
      (fun potential : ℳF =>
        (C.diracGreen potential).retarded C.externalDiracSource)
  diracResponse_fderiv_bound : ∀ potential,
    ‖fderiv ℝ
      (fun A : ℳF =>
        (C.diracGreen A).retarded C.externalDiracSource) potential‖₊ ≤
      diracConstant
  currentSource_differentiable : Differentiable ℝ C.currentSource
  currentSource_fderiv_bound : ∀ psi,
    ‖fderiv ℝ C.currentSource psi‖₊ ≤ currentConstant
  maxwellRetarded : ℳS →L[ℝ] ℳF
  maxwellRetarded_eq : ∀ source,
    maxwellRetarded source = MG.retarded source

namespace DifferentialResponseBounds

/-- Uniform Fréchet-derivative bounds construct the exact `ResponseBounds`
consumed by the Maxwell--Dirac contraction theorem. -/
noncomputable def toResponseBounds
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : DifferentialResponseBounds I D q MG C) :
    ResponseBounds I D q MG C where
  diracConstant := B.diracConstant
  currentConstant := B.currentConstant
  diracResponse_lipschitz :=
    lipschitzWith_of_nnnorm_fderiv_le
      B.diracResponse_differentiable B.diracResponse_fderiv_bound
  currentSource_lipschitz :=
    lipschitzWith_of_nnnorm_fderiv_le
      B.currentSource_differentiable B.currentSource_fderiv_bound
  maxwellRetarded := B.maxwellRetarded
  maxwellRetarded_eq := B.maxwellRetarded_eq

end DifferentialResponseBounds

/-- A contraction of the coupled Green update constructs a unique
self-consistent curved Maxwell--Dirac solution. Both equations are conclusions
at the fixed point, not fields of the coupling data. -/
theorem existsUnique_selfConsistentSolution
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F)) (K : NNReal)
    (hcontract : ContractingWith K (update I D q MG C)) :
    ∃! state : 𝒟F × ℳF, IsSelfConsistentSolution I D q MG C state := by
  let state := hcontract.fixedPoint
  have hfix : update I D q MG C state = state := hcontract.fixedPoint_isFixedPt
  have hpsi : (C.diracGreen state.2).retarded C.externalDiracSource = state.1 :=
    congrArg Prod.fst hfix
  have hA : MG.retarded (C.currentSource state.1) = state.2 :=
    congrArg Prod.snd hfix
  have hdirac :=
    (C.diracGreen state.2).retarded_solves C.externalDiracSource
  rw [hpsi, C.diracGreen_realizeField] at hdirac
  have hmaxwell := IntrinsicMaxwellGreenData.retarded_solves
    I MG (C.currentSource state.1)
  rw [hA, C.currentSource_realizes] at hmaxwell
  refine ⟨state, ⟨hfix, hdirac, hmaxwell⟩, ?_⟩
  intro other hother
  exact hcontract.fixedPoint_unique hother.1

/-- Explicit component response estimates plus the small-coupling inequality
construct the unique self-consistent curved Maxwell--Dirac solution.  In
particular, this theorem does not take `ContractingWith` as an independent
premise. -/
theorem existsUnique_selfConsistentSolution_of_responseBounds
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : ResponseBounds I D q MG C)
    (hsmall :
      max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant) < 1) :
    ∃! state : 𝒟F × ℳF, IsSelfConsistentSolution I D q MG C state :=
  existsUnique_selfConsistentSolution I D q MG C _
    (B.contractingWith_update I D q MG C hsmall)

/-- Uniform Fréchet-derivative estimates and the explicit small-response
inequality construct the unique self-consistent curved Maxwell--Dirac
solution.  The component Lipschitz assumptions are conclusions of the
Banach-space mean-value theorem. -/
theorem existsUnique_selfConsistentSolution_of_differentialBounds
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : DifferentialResponseBounds I D q MG C)
    (hsmall :
      max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant) < 1) :
    ∃! state : 𝒟F × ℳF, IsSelfConsistentSolution I D q MG C state :=
  existsUnique_selfConsistentSolution_of_responseBounds I D q MG C
    (B.toResponseBounds I D q MG C) hsmall

/-- The response-bounded Maxwell--Dirac Picard iteration converges from every
seed to a self-consistent solution.  Both the geometric a priori error and
the computable a posteriori error are exposed, so the fixed-point theorem is
an approximation procedure rather than only an existence result. -/
theorem picard_converges_to_selfConsistentSolution
    (C : CurvedMaxwellDiracCoupling I D q MG
      (𝒟S := 𝒟S) (𝒟F := 𝒟F))
    (B : ResponseBounds I D q MG C)
    (hsmall :
      max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant) < 1)
    (seed : 𝒟F × ℳF) :
    ∃ state : 𝒟F × ℳF,
      IsSelfConsistentSolution I D q MG C state ∧
      Tendsto
        (fun n => (update I D q MG C)^[n] seed) atTop (𝓝 state) ∧
      ∀ n,
        dist ((update I D q MG C)^[n] seed) state ≤
            dist seed (update I D q MG C seed) *
              (max B.diracConstant
                (‖B.maxwellRetarded‖₊ * B.currentConstant) : ℝ) ^ n /
              (1 - max B.diracConstant
                (‖B.maxwellRetarded‖₊ * B.currentConstant)) ∧
          dist ((update I D q MG C)^[n] seed) state ≤
            dist ((update I D q MG C)^[n] seed)
              ((update I D q MG C)^[n + 1] seed) /
              (1 - max B.diracConstant
                (‖B.maxwellRetarded‖₊ * B.currentConstant)) := by
  let K : NNReal :=
    max B.diracConstant (‖B.maxwellRetarded‖₊ * B.currentConstant)
  have hcontract : ContractingWith K (update I D q MG C) :=
    B.contractingWith_update I D q MG C hsmall
  refine ⟨hcontract.fixedPoint, ?_, hcontract.tendsto_iterate_fixedPoint seed, ?_⟩
  · rcases existsUnique_selfConsistentSolution I D q MG C K hcontract with
      ⟨state, hstate, _⟩
    have heq : state = hcontract.fixedPoint :=
      hcontract.fixedPoint_unique hstate.1
    rw [← heq]
    exact hstate
  · intro n
    exact ⟨hcontract.apriori_dist_iterate_fixedPoint_le seed n,
      hcontract.aposteriori_dist_iterate_fixedPoint_le seed n⟩

end CurvedMaxwellDiracCoupling

end SelfConsistentMaxwellDirac
end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge

end

end
