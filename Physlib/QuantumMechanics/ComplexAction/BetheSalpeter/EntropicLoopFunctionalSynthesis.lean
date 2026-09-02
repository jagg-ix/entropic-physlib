/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.ODE.ExistUnique
public import Physlib.Mathematics.DataStructures.Matrix.LieTrace
public import Physlib.QFT.PerturbationTheory.WickContraction.IsFull
public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius
public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.MixedBFOneLoopGraphs
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.QuantumMechanics.NonHermitian.Propagator
meta import Zil

/-!
# Entropic resonance modes across Schrödinger, thermal, loop, and Wilson lanes

This module connects the explicit four-dimensional Hermite Bethe--Salpeter
resonance carrier to analytical structures that were previously formalized in
separate files.

* the norm of the `n`th Nagao--Nielsen resonance coupling is exactly the
  Matsubara weight `exp (-beta E_n)` for `E_n = n gamma / beta`;
* the rank-one decoherence functional of the resonance modes has the product
  of those thermal weights as its exact norm and their square on the Born
  diagonal;
* the same damping dresses the Gel'fand--Yaglom one-loop wave function;
* the complex resonance operator is a continuum Caticha functional
  Schrödinger generator diagonalized by the explicit Hermite basis;
* the two-mode complex projective Riccati field is the exact resonance
  eigenvalue gap;
* a resonance coupling is a bounded constant Wilson observable in Witten's
  finite-measure functional-integral API;
* in the chiral Chern--Simons graph sector only, the existing graph
  classification excludes every two-loop-or-higher contribution.

The last item is deliberately sector-specific.  It does not assert that a
general interacting QED or gravitational expansion has no two-loop term.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields
open Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius
open Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.NonHermitian.Propagator

/-! ## A. Resonance damping is a Matsubara weight -/

/-- The full phase-carrying coupling used as a scalar history/Wilson weight. -/
def resonanceModeWeight
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) : ℂ :=
  K.toComplexAction.coupling n

/-- The resonance energy corresponding to inverse temperature `beta`.
The nonzero-temperature premise is explicit because this is the exact
reparametrization `beta E_n = n gamma`. -/
def resonanceMatsubaraEnergy
    (K : DiagonalComplexActionResonanceFamily) (beta : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * K.dampingRate / beta

/-- The norm of every complex Hermite resonance coupling is exactly its
Matsubara/Boltzmann weight.  The real action phase drops out, while the
imaginary-action gap supplies `beta E_n = n gamma`. -/
theorem resonanceModeWeight_norm_eq_matsubara
    (K : DiagonalComplexActionResonanceFamily) (beta : ℝ) (hbeta : beta ≠ 0)
    (n : ℕ) :
    ‖resonanceModeWeight K n‖ =
      matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) := by
  rw [resonanceModeWeight,
    K.toComplexAction.norm_coupling_eq_edTransitionWeight]
  have hdamp : edTransitionWeight 2 0
      (Real.sqrt ((n : ℝ) * K.dampingRate)) =
      Real.exp (-((n : ℝ) * K.dampingRate)) := by
    have h := K.toHermitian.coupling_eq_exp n
    change edTransitionWeight 2 0
        (Real.sqrt ((n : ℝ) * K.dampingRate)) =
      Real.exp (-((n : ℝ) * K.dampingRate)) at h
    exact h
  change edTransitionWeight 2 0
      (Real.sqrt ((n : ℝ) * K.dampingRate)) = _
  rw [hdamp]
  unfold matsubaraBoltzmannWeight resonanceMatsubaraEnergy
  congr 1
  field_simp

/-! ## B. Exact decoherence/Born weights on the resonance basis -/

/-- The Sorkin--Johnston rank-one decoherence functional carried by the
complex resonance-mode weights. -/
def resonanceDecoherenceFunctional
    (K : DiagonalComplexActionResonanceFamily) : ℕ → ℕ → ℂ :=
  decoherenceFunctional (resonanceModeWeight K)

/-- Off-diagonal decoherence has exactly the product of the two Matsubara
damping factors. -/
theorem resonanceDecoherenceFunctional_norm_eq_matsubara_mul
    (K : DiagonalComplexActionResonanceFamily) (beta : ℝ) (hbeta : beta ≠ 0)
    (n m : ℕ) :
    ‖resonanceDecoherenceFunctional K n m‖ =
      matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) *
        matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta m) := by
  rw [resonanceDecoherenceFunctional, decoherenceFunctional_apply, norm_mul,
    RCLike.norm_conj, resonanceModeWeight_norm_eq_matsubara K beta hbeta n,
    resonanceModeWeight_norm_eq_matsubara K beta hbeta m]

/-- The Born diagonal is the square of the same Matsubara weight. -/
theorem resonanceDecoherenceFunctional_diag_re_eq_matsubara_sq
    (K : DiagonalComplexActionResonanceFamily) (beta : ℝ) (hbeta : beta ≠ 0)
    (n : ℕ) :
    (resonanceDecoherenceFunctional K n n).re =
      matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) ^ 2 := by
  rw [resonanceDecoherenceFunctional, decoherenceFunctional_diag_re,
    Complex.normSq_eq_norm_sq,
    resonanceModeWeight_norm_eq_matsubara K beta hbeta n]

/-! ## C. One-loop determinant dressing and honest loop-order scope -/

/-- The Gel'fand--Yaglom one-loop wave function evaluated on the `n`th
resonance action has norm equal to its Matsubara damping times the positive
one-loop determinant prefactor. -/
theorem resonance_oneLoopWaveFunction_norm_eq_matsubara
    (K : DiagonalComplexActionResonanceFamily) (beta D : ℝ)
    (hbeta : beta ≠ 0) (hD : 0 < D) (n : ℕ) :
    ‖oneLoopWaveFunction (K.phaseAction n)
        ((n : ℝ) * K.dampingRate) 1 D‖ =
      matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) *
        oneLoopPrefactor D := by
  rw [oneLoopWaveFunction_norm (K.phaseAction n)
    ((n : ℝ) * K.dampingRate) 1 D (by norm_num) hD]
  unfold PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight
  unfold matsubaraBoltzmannWeight resonanceMatsubaraEnergy
  congr 2
  field_simp

/-- In the one-loop-exact chiral Chern--Simons sector, the resonance-damped
one-loop norm formula coexists with the graph-theoretic exclusion of every
second-loop-or-higher graph.  The exclusion is not exported to general QED. -/
theorem chiral_resonance_oneLoop_and_no_second_loop
    (K : DiagonalComplexActionResonanceFamily) (beta D : ℝ)
    (hbeta : beta ≠ 0) (hD : 0 < D) (n : ℕ)
    (Gamma : OneLoopExactGraphShape) :
    ‖oneLoopWaveFunction (K.phaseAction n)
        ((n : ℝ) * K.dampingRate) 1 D‖ =
        matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) *
          oneLoopPrefactor D
      ∧ ¬ 2 ≤ Gamma.loopNumber :=
  ⟨resonance_oneLoopWaveFunction_norm_eq_matsubara K beta D hbeta hD n,
    Gamma.no_two_loop_or_higher⟩

/-! ## D. Complex functional Schrödinger and projective Riccati evolution -/

/-- With unit lapse and zero shift, the complex resonance operator is an
Ipek--Caticha continuum functional Schrödinger generator, and every explicit
four-dimensional Hermite mode is its eigenfunctional. -/
theorem resonanceBasis_continuumFunctionalSchrodinger
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) :
    continuumSmearedSchrodingerGenerator 1 0
        K.resonanceOperator.toLinearMap 0 (K.basis n) =
      K.toComplexAction.coupling n • K.basis n := by
  rw [continuumSmearedSchrodinger_apply]
  simpa using K.resonanceOperator_apply_basis n

/-- The projective Riccati vector field of two diagonal complex resonance
modes is multiplication by their exact complex eigenvalue gap.  Combined
with `projective_schrodinger_riccati`, this is the ray equation for any two
components satisfying their diagonal Schrödinger equations. -/
theorem resonanceProjectiveRiccatiFlow_eq_eigenvalueGap
    (K : DiagonalComplexActionResonanceFamily) (n m : ℕ) (w : ℂ) :
    riccatiFlow (K.toComplexAction.coupling n) 0 0
        (K.toComplexAction.coupling m) w =
      (K.toComplexAction.coupling n - K.toComplexAction.coupling m) * w := by
  simp [riccatiFlow]

/-! ## E. Resonance weights as rigorous constant Wilson observables -/

/-- On a finite reference measure, each complex resonance-mode coupling is a
measurable bounded constant Wilson observable.  Witten's analytic functional
integral therefore exists, and its norm bound is exactly the mode's Matsubara
damping times the partition function. -/
theorem resonanceMode_constantWilson_supplies_witten_FK
    {Field : Type*} [MeasurableSpace Field]
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (K : DiagonalComplexActionResonanceFamily) (beta : ℝ)
    (hbeta : beta ≠ 0) (n : ℕ) :
    let value : Unit → ℂ := fun _ => resonanceModeWeight K n
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model (fun q _ => value q) H
    Integrable (fun A => W.wilsonObservable () A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral ()‖ ≤
        matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) *
          W.partitionFunction := by
  let value : Unit → ℂ := fun _ => resonanceModeWeight K n
  let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
  let W :=
    wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
      model (fun q _ => value q) H
  have h := complexActionFiniteMeasure_constantWilson_supplies_witten_FK
    (model := model) (value := value) ()
  refine ⟨h.1, ?_⟩
  rw [show ‖value ()‖ =
      matsubaraBoltzmannWeight beta (resonanceMatsubaraEnergy K beta n) by
    simpa [value] using resonanceModeWeight_norm_eq_matsubara K beta hbeta n] at h
  exact h.2

/-! ## F. Global bounded-operator and projective resonance evolution -/

/-- The bounded non-Hermitian resonance operator has a globally defined
operator exponential on the full four-dimensional Bethe--Salpeter Hilbert
space.  This construction does not require finite dimensionality. -/
def resonancePropagator
    (K : DiagonalComplexActionResonanceFamily) (t : ℝ) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  propagator K.resonanceOperator 1 t

/-- The full infinite-dimensional bounded resonance propagator solves its
operator ODE at every real time.  This removes the finite-dimensional
restriction carried by the older convenience theorem while reusing exactly
the same Banach-algebra exponential. -/
theorem resonancePropagator_hasDerivAt
    (K : DiagonalComplexActionResonanceFamily) (t : ℝ) :
    HasDerivAt (resonancePropagator K)
      (schrodingerGenerator K.resonanceOperator 1 * resonancePropagator K t) t := by
  unfold resonancePropagator propagator
  exact hasDerivAt_exp_smul_const' (schrodingerGenerator K.resonanceOperator 1) t

/-- The same global propagator is an exact time-translation semigroup on the
infinite-dimensional carrier. -/
theorem resonancePropagator_add
    (K : DiagonalComplexActionResonanceFamily) (s t : ℝ) :
    resonancePropagator K (s + t) =
      resonancePropagator K s * resonancePropagator K t := by
  haveI : NormedAlgebra ℚ (BetheSalpeterL2 →L[ℂ] BetheSalpeterL2) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  unfold resonancePropagator propagator
  let G := schrodingerGenerator K.resonanceOperator 1
  have hadd : (s + t) • G = s • G + t • G := add_smul s t G
  change NormedSpace.exp ((s + t) • G) =
    NormedSpace.exp (s • G) * NormedSpace.exp (t • G)
  rw [hadd]
  have hs : Commute (s • G) G := (Commute.refl G).smul_left s
  have hst : Commute (s • G) (t • G) := hs.smul_right t
  exact NormedSpace.exp_add_of_commute hst

/-- The explicit global scalar evolution of the `n`th diagonal resonance
mode. -/
def resonanceModeEvolution
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * K.toComplexAction.coupling n)

/-- Every diagonal resonance mode is a global entire solution of its complex
scalar Schrödinger equation. -/
theorem resonanceModeEvolution_hasDerivAt
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) (t : ℝ) :
    HasDerivAt (resonanceModeEvolution K n)
      (K.toComplexAction.coupling n * resonanceModeEvolution K n t) t := by
  unfold resonanceModeEvolution
  rw [Complex.exp_eq_exp_ℂ]
  simpa [smul_eq_mul, Function.comp_def] using
    HasDerivAt.scomp t
      (hasDerivAt_exp_smul_const' (𝕂 := ℂ)
        (K.toComplexAction.coupling n) (t : ℂ))
      (Complex.ofRealCLM.hasDerivAt (x := t))

/-- The quotient of any two explicit resonance-mode solutions is a global
solution of the corresponding complex projective Riccati equation.  The
denominator never vanishes because it is an exponential.  This is genuine
existence for the diagonal resonance sector, not a general nonlinear
operator-Riccati well-posedness theorem. -/
theorem resonanceModeRatio_hasDerivAt_riccati
    (K : DiagonalComplexActionResonanceFamily) (n m : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s ↦ resonanceModeEvolution K n s / resonanceModeEvolution K m s)
      (riccatiFlow (K.toComplexAction.coupling n) 0 0
        (K.toComplexAction.coupling m)
        (resonanceModeEvolution K n t / resonanceModeEvolution K m t)) t := by
  exact projective_schrodinger_riccati
    (resonanceModeEvolution K n) (resonanceModeEvolution K m)
    (K.toComplexAction.coupling n) 0 0 (K.toComplexAction.coupling m) t
    (by simpa using resonanceModeEvolution_hasDerivAt K n t)
    (by simpa using resonanceModeEvolution_hasDerivAt K m t)
    (Complex.exp_ne_zero _)

/-! ## G. Field-dependent abelian Wilson holonomy -/

/-- The `U(1)` Wilson holonomy obtained by exponentiating a real circulation
functional.  Unlike the earlier charge-sector constant, this observable
depends on the gauge-field configuration through `circulation L A`. -/
def abelianWilsonHolonomy {Field Link : Type*}
    (charge : Link → ℝ) (circulation : Link → Field → ℝ) :
    Link → Field → ℂ :=
  fun L A ↦ Complex.exp
    (Complex.I * ((charge L * circulation L A : ℝ) : ℂ))

/-- A measurable circulation produces a measurable field-dependent Wilson
holonomy. -/
theorem abelianWilsonHolonomy_measurable
    {Field Link : Type*} [MeasurableSpace Field]
    (charge : Link → ℝ) (circulation : Link → Field → ℝ)
    (hcirculation : ∀ L, Measurable (circulation L)) (L : Link) :
    Measurable (abelianWilsonHolonomy charge circulation L) := by
  apply Complex.continuous_exp.measurable.comp
  exact measurable_const.mul
    ((measurable_const.mul (hcirculation L)).complex_ofReal)

/-- The abelian Wilson holonomy has unit norm pointwise by construction. -/
theorem abelianWilsonHolonomy_norm
    {Field Link : Type*}
    (charge : Link → ℝ) (circulation : Link → Field → ℝ)
    (L : Link) (A : Field) :
    ‖abelianWilsonHolonomy charge circulation L A‖ = 1 := by
  rw [abelianWilsonHolonomy, Complex.norm_exp]
  simp

/-- A measurable field-dependent abelian holonomy on a finite reference
measure supplies Witten's rigorous complex Feynman--Kac integral and the sharp
partition-function norm bound. -/
theorem abelianWilsonHolonomy_supplies_witten_FK
    {Field Link : Type*} [MeasurableSpace Field]
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (charge : Link → ℝ) (circulation : Link → Field → ℝ)
    (hcirculation : ∀ L, Measurable (circulation L)) (L : Link) :
    let wilson := abelianWilsonHolonomy charge circulation
    let H := WilsonObservableAnalyticObligations.ofNormLeOne
      (model := model) (wilsonObservable := wilson)
      (abelianWilsonHolonomy_measurable charge circulation hcirculation)
      (fun q A ↦ by rw [abelianWilsonHolonomy_norm charge circulation q A])
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model wilson H
    Integrable (fun A ↦ W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.partitionFunction := by
  simpa using complexActionFiniteMeasure_normOneWilson_supplies_witten_FK
    model (abelianWilsonHolonomy charge circulation)
      (abelianWilsonHolonomy_measurable charge circulation hcirculation)
      (fun q A ↦ by rw [abelianWilsonHolonomy_norm charge circulation q A]) L

/-! ## H. Finite nonabelian path ordering and normalized Wilson trace -/

/-- The ordered product of finitely many unitary parallel transports.
`List.ofFn` fixes the path order, so no commutativity premise is introduced. -/
def finitePathOrderedHolonomy {Field : Type*} (segments d : ℕ)
    (transport : Fin segments → Field → Matrix.unitaryGroup (Fin d) ℂ)
    (A : Field) : Matrix.unitaryGroup (Fin d) ℂ :=
  (List.ofFn fun k ↦ transport k A).prod

/-- The finite-dimensional nonabelian Wilson observable: normalized trace of
the ordered unitary holonomy. -/
def finitePathOrderedWilson {Field : Type*} (segments d : ℕ)
    (transport : Fin segments → Field → Matrix.unitaryGroup (Fin d) ℂ)
    (A : Field) : ℂ :=
  normTrace ((finitePathOrderedHolonomy segments d transport A :
    Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)

/-- Unitarity bounds the normalized trace of every finite nonabelian ordered
holonomy by one. -/
lemma finitePathOrderedWilson_norm_le_one {Field : Type*} (segments d : ℕ)
    (hd : 0 < d)
    (transport : Fin segments → Field → Matrix.unitaryGroup (Fin d) ℂ)
    (A : Field) :
    ‖finitePathOrderedWilson segments d transport A‖ ≤ 1 := by
  let U := finitePathOrderedHolonomy segments d transport A
  have htrace : ‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ d := by
    calc
      ‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖
          ≤ ∑ i : Fin d, ‖(U : Matrix (Fin d) (Fin d) ℂ) i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, 1 := Finset.sum_le_sum fun i _ ↦
        entry_norm_bound_of_unitary U.property i i
      _ = d := by simp
  rw [finitePathOrderedWilson, normTrace, norm_mul, norm_inv]
  simp only [Complex.norm_natCast, Fintype.card_fin]
  change (d : ℝ)⁻¹ * ‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1
  calc
    (d : ℝ)⁻¹ * ‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖
        ≤ (d : ℝ)⁻¹ * d := by gcongr
    _ = 1 := by exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))

/-- Continuous segment transports give a continuous, hence measurable,
finite nonabelian Wilson observable. -/
lemma finitePathOrderedWilson_continuous {Field : Type*} [TopologicalSpace Field]
    (segments d : ℕ)
    (transport : Fin segments → Field → Matrix.unitaryGroup (Fin d) ℂ)
    (htransport : ∀ k, Continuous (transport k)) :
    Continuous (finitePathOrderedWilson segments d transport) := by
  have hhol : Continuous (finitePathOrderedHolonomy segments d transport) := by
    unfold finitePathOrderedHolonomy
    simpa only [List.ofFn_eq_map] using
      continuous_list_prod (List.finRange segments) (fun k _ ↦ htransport k)
  have hmatrix : Continuous fun A ↦
      (finitePathOrderedHolonomy segments d transport A : Matrix (Fin d) (Fin d) ℂ) :=
    continuous_subtype_val.comp hhol
  unfold finitePathOrderedWilson normTrace
  exact continuous_const.mul hmatrix.matrix_trace

/-- The normalized ordered Wilson trace is invariant under a global unitary
change of frame, by cyclicity of matrix trace. -/
lemma finitePathOrderedWilson_globalGauge_invariant {Field : Type*}
    (segments d : ℕ)
    (transport : Fin segments → Field → Matrix.unitaryGroup (Fin d) ℂ)
    (A : Field) (G : Matrix.unitaryGroup (Fin d) ℂ) :
    normTrace ((G : Matrix (Fin d) (Fin d) ℂ) *
        (finitePathOrderedHolonomy segments d transport A : Matrix (Fin d) (Fin d) ℂ) *
        star (G : Matrix (Fin d) (Fin d) ℂ)) =
      finitePathOrderedWilson segments d transport A := by
  rw [finitePathOrderedWilson, normTrace, normTrace, Matrix.trace_unitary_conj]

/-- A continuous finite family of nonabelian unitary transports supplies
Witten's finite-measure complex Feynman--Kac integral with the sharp
partition-function bound.  This is finite path ordering, not a continuum
path-ordered exponential. -/
lemma finitePathOrderedWilson_supplies_witten_FK
    {Field Link : Type*} [MeasurableSpace Field] [TopologicalSpace Field]
    [BorelSpace Field]
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (segments d : ℕ) (hd : 0 < d)
    (transport : Link → Fin segments → Field → Matrix.unitaryGroup (Fin d) ℂ)
    (htransport : ∀ L k, Continuous (transport L k)) (L : Link) :
    let wilson := fun q ↦ finitePathOrderedWilson segments d (transport q)
    let H := WilsonObservableAnalyticObligations.ofNormLeOne
      (model := model) (wilsonObservable := wilson)
      (fun q ↦ (finitePathOrderedWilson_continuous segments d (transport q)
        (htransport q)).measurable)
      (fun q A ↦ finitePathOrderedWilson_norm_le_one segments d hd (transport q) A)
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model wilson H
    Integrable (fun A ↦ W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.partitionFunction := by
  simpa using complexActionFiniteMeasure_normOneWilson_supplies_witten_FK
    model (fun q ↦ finitePathOrderedWilson segments d (transport q))
      (fun q ↦ (finitePathOrderedWilson_continuous segments d (transport q)
        (htransport q)).measurable)
      (fun q A ↦ finitePathOrderedWilson_norm_le_one segments d hd (transport q) A) L

/-! ## I. Endpoint-local gauge covariance of discrete parallel transport -/

/-- Two finite transport paths are related by vertex-local gauge changes when
each transformed edge is `g_source * U * g_target⁻¹`.  The endpoints are
recorded explicitly, so the same relation covers both open Wilson lines and
closed Wilson loops. -/
inductive GaugeRelatedPath {G : Type*} [Group G] :
    G → G → List G → List G → Prop
  | nil (g : G) : GaugeRelatedPath g g [] []
  | cons {g₀ g₁ gₙ U U' : G} {Us Us' : List G}
      (hU : U' = g₀ * U * g₁⁻¹)
      (hUs : GaugeRelatedPath g₁ gₙ Us Us') :
      GaugeRelatedPath g₀ gₙ (U :: Us) (U' :: Us')

/-- Vertex-local gauge changes telescope through a path-ordered product,
leaving only the source and target gauge factors. -/
lemma GaugeRelatedPath.prod_eq_endpoint_conjugation
    {G : Type*} [Group G] {g₀ gₙ : G} {Us Us' : List G}
    (h : GaugeRelatedPath g₀ gₙ Us Us') :
    Us'.prod = g₀ * Us.prod * gₙ⁻¹ := by
  induction h with
  | nil g => simp
  | cons hU hUs ih =>
      rw [List.prod_cons, hU, List.prod_cons, ih]
      simp [mul_assoc]

/-- For a closed discrete path, arbitrary vertex-local gauge changes reduce
to conjugation by the base-point gauge. -/
lemma GaugeRelatedPath.closed_prod_eq_conjugation
    {G : Type*} [Group G] {g : G} {Us Us' : List G}
    (h : GaugeRelatedPath g g Us Us') :
    Us'.prod = g * Us.prod * g⁻¹ :=
  h.prod_eq_endpoint_conjugation

/-- The normalized Wilson trace of a finite closed path is invariant under
vertex-local unitary gauge transformations.  Unlike the earlier global-frame
lemma, the gauge element may vary at every path vertex; only the two endpoint
values must agree because the path is closed. -/
lemma finitePathOrderedWilson_localGauge_invariant
    (d : ℕ) (g : Matrix.unitaryGroup (Fin d) ℂ)
    (Us Us' : List (Matrix.unitaryGroup (Fin d) ℂ))
    (h : GaugeRelatedPath g g Us Us') :
    normTrace ((Us'.prod : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) =
    normTrace ((Us.prod : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) := by
  rw [h.closed_prod_eq_conjugation]
  change normTrace ((g : Matrix (Fin d) (Fin d) ℂ) *
      (Us.prod : Matrix (Fin d) (Fin d) ℂ) * star (g : Matrix (Fin d) (Fin d) ℂ)) =
    normTrace ((Us.prod : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)
  rw [normTrace, normTrace, Matrix.trace_unitary_conj]

/-! ## J. Wick contraction, Dyson order, and general loop counting -/

/-- The cycle-rank loop number of a connected vacuum contraction with a
declared number of interaction vertices. -/
def connectedVacuumLoopNumber {fields : ℕ}
    (vertices : ℕ) (c : WickContraction fields) : ℕ :=
  c.1.card - vertices + 1

/-- A full Wick contraction of `fields` insertions contains exactly
`fields / 2` propagator edges.  This is the reusable combinatorial bridge
from Wick fullness to Feynman-graph edge counting. -/
lemma fullWickContraction_edgeCount {fields : ℕ}
    (c : WickContraction fields) (hfull : c.IsFull) :
    c.1.card = fields / 2 := by
  have hcard := c.pair_card_mul_two_eq_of_isFull hfull
  omega

/-- For a regular `valence`-field interaction at `vertices` vertices, a full
vacuum Wick contraction has the expected connected cycle rank
`vertices * valence / 2 - vertices + 1`.  Connectivity is represented by the
use of cycle rank rather than inferred from fullness. -/
lemma regularInteraction_fullVacuum_loopNumber
    (vertices valence fields : ℕ) (hfields : fields = vertices * valence)
    (c : WickContraction fields) (hfull : c.IsFull) :
    connectedVacuumLoopNumber vertices c =
      vertices * valence / 2 - vertices + 1 := by
  rw [connectedVacuumLoopNumber, fullWickContraction_edgeCount c hfull, hfields]

/-- For the second Dyson order of a cubic interaction, a full vacuum
contraction has two vertices and six fields.  Its connected cycle rank is
`E - V + 1`. -/
def secondDysonVacuumLoopNumber
    (c : WickContraction 6) : ℕ :=
  connectedVacuumLoopNumber 2 c

/-- A six-field contraction connects the two cubic vertices when a contracted
pair crosses from positions `0,1,2` to positions `3,4,5`. -/
def secondDysonVerticesConnected
    (c : WickContraction 6) : Prop :=
  ∃ p ∈ c.1, ∃ i ∈ p, ∃ j ∈ p, i.val < 3 ∧ 3 ≤ j.val

/-- The combinatorial premises for a connected, second-Dyson-order cubic
vacuum graph.  They are deliberately separate from the analytic Dyson
coefficient proved in `PoincareGroupFields`. -/
structure SecondDysonConnectedVacuum
    (c : WickContraction 6) : Prop where
  full : c.IsFull
  verticesConnected : secondDysonVerticesConnected c

/-- A full six-field contraction has three Wick edges, hence its connected
two-vertex cycle rank is exactly two. -/
lemma secondDyson_fullVacuum_loopNumber_two
    (c : WickContraction 6)
    (hfull : c.IsFull) : secondDysonVacuumLoopNumber c = 2 := by
  simpa [secondDysonVacuumLoopNumber] using
    regularInteraction_fullVacuum_loopNumber 2 3 6 (by norm_num) c hfull

/-- The explicit Wick criterion upgrades second Dyson order to a genuine
two-loop statement only in the connected, full, cubic vacuum sector. -/
lemma secondDyson_connectedVacuum_is_two_loop
    (c : WickContraction 6)
    (h : SecondDysonConnectedVacuum c) :
    secondDysonVerticesConnected c ∧ secondDysonVacuumLoopNumber c = 2 :=
  ⟨h.verticesConnected, secondDyson_fullVacuum_loopNumber_two c h.full⟩

/-! ## K. Local nonlinear and global affine bounded-operator Riccati evolution -/

/-- The bounded-operator Riccati vector field associated with a block
generator `[[A,B],[C,D]]`. -/
def operatorRiccatiField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B C D : E →L[ℂ] E) (X : E →L[ℂ] E) : E →L[ℂ] E :=
  B + A * X - X * D - X * C * X

/-- The bounded operator-Riccati field is continuously differentiable as a
real Banach-space vector field. -/
lemma operatorRiccatiField_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B C D : E →L[ℂ] E) :
    ContDiff ℝ 1 (operatorRiccatiField A B C D) := by
  unfold operatorRiccatiField
  fun_prop

/-- Picard--Lindelöf gives a local solution for every initial bounded
operator.  This is nonlinear operator-Riccati existence on a Banach space;
no global no-blowup claim is made. -/
lemma exists_local_operatorRiccati_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A B C D X0 : E →L[ℂ] E) (t0 : ℝ) :
    ∃ X : ℝ → (E →L[ℂ] E), X t0 = X0 ∧ ∃ epsilon > 0,
      ∀ t ∈ Set.Ioo (t0 - epsilon) (t0 + epsilon),
        HasDerivAt X (operatorRiccatiField A B C D (X t)) t := by
  exact (operatorRiccatiField_contDiff A B C D).contDiffAt
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t0

/-- Any two local bounded operator-Riccati solutions with the same initial
operator agree near the initial time.  Together with
`exists_local_operatorRiccati_solution`, this is local well-posedness. -/
lemma operatorRiccati_solution_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A B C D X0 : E →L[ℂ] E) (t0 : ℝ)
    (X Y : ℝ → (E →L[ℂ] E))
    (hX0 : X t0 = X0) (hY0 : Y t0 = X0)
    (hX : ∀ᶠ t in 𝓝 t0,
      HasDerivAt X (operatorRiccatiField A B C D (X t)) t)
    (hY : ∀ᶠ t in 𝓝 t0,
      HasDerivAt Y (operatorRiccatiField A B C D (Y t)) t) :
    X =ᶠ[𝓝 t0] Y := by
  obtain ⟨K, s, hs, hlip⟩ :=
    (operatorRiccatiField_contDiff A B C D).contDiffAt.exists_lipschitzOnWith
  have hXat := hX.self_of_nhds
  have hYat := hY.self_of_nhds
  have hXs : ∀ᶠ t in 𝓝 t0, X t ∈ s :=
    hXat.continuousAt.eventually (hX0.symm ▸ hs)
  have hYs : ∀ᶠ t in 𝓝 t0, Y t ∈ s :=
    hYat.continuousAt.eventually (hY0.symm ▸ hs)
  apply ODE_solution_unique_of_eventually
    (v := fun _ ↦ operatorRiccatiField A B C D)
    (s := fun _ ↦ s) (K := K)
    (Filter.Eventually.of_forall fun _ ↦ hlip)
    (hX.and hXs) (hY.and hYs)
  exact hX0.trans hY0.symm

/-- The globally defined solution of the affine Riccati sector
`A = C = D = 0`, where the equation reduces to `X' = B`. -/
def affineOperatorRiccatiSolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B X0 : E →L[ℂ] E) (t0 t : ℝ) : E →L[ℂ] E :=
  X0 + (t - t0) • B

/-- The affine operator-Riccati solution has the prescribed initial value. -/
@[simp] lemma affineOperatorRiccatiSolution_initial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B X0 : E →L[ℂ] E) (t0 : ℝ) :
    affineOperatorRiccatiSolution B X0 t0 t0 = X0 := by
  simp [affineOperatorRiccatiSolution]

/-- The affine formula is a global solution of the bounded operator-Riccati
equation at every real time.  This supplies a genuine no-blowup sector while
making no such claim for the quadratic `C ≠ 0` equation. -/
lemma affineOperatorRiccatiSolution_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B X0 : E →L[ℂ] E) (t0 t : ℝ) :
    HasDerivAt (affineOperatorRiccatiSolution B X0 t0)
      (operatorRiccatiField 0 B 0 0
        (affineOperatorRiccatiSolution B X0 t0 t)) t := by
  have hderiv : HasDerivAt (affineOperatorRiccatiSolution B X0 t0) B t := by
    change HasDerivAt (fun s : ℝ ↦ X0 + (s - t0) • B) B t
    simpa using ((hasDerivAt_id t).sub_const t0).smul_const B |>.const_add X0
  simpa [operatorRiccatiField] using hderiv

/-- The global affine solution is unique among global solutions with the
same initial operator. -/
lemma affineOperatorRiccatiSolution_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (B X0 : E →L[ℂ] E) (t0 : ℝ) (X : ℝ → (E →L[ℂ] E))
    (hX0 : X t0 = X0)
    (hX : ∀ t, HasDerivAt X (operatorRiccatiField 0 B 0 0 (X t)) t) :
    X = affineOperatorRiccatiSolution B X0 t0 := by
  apply ODE_solution_unique_univ
    (v := fun _ ↦ operatorRiccatiField 0 B 0 0)
    (s := fun _ ↦ Set.univ) (K := 0) (t₀ := t0)
  · intro t
    have hfield : operatorRiccatiField 0 B 0 0 =
        fun _ : E →L[ℂ] E ↦ B := by
      funext Y
      simp [operatorRiccatiField]
    rw [hfield]
    exact (LipschitzWith.const B).lipschitzOnWith
  · intro t
    exact ⟨hX t, Set.mem_univ _⟩
  · intro t
    exact ⟨affineOperatorRiccatiSolution_hasDerivAt B X0 t0 t, Set.mem_univ _⟩
  · simpa using hX0

/- ZIL-BEGIN -/

zil attach resonanceModeWeight_norm_eq_matsubara where
  formalizes @ "claim:four-dimensional-complex-resonance-damping-is-exactly-a-matsubara-weight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.ComplexActionDampedQEDModeFamily.norm_coupling_eq_edTransitionWeight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight",
  requires @ "claim:nonzero-inverse-temperature-and-linear-mode-imaginary-action-gap",
  caveat @ "claim:energy-n-gamma-over-beta-is-the-explicit-thermal-reparametrization-not-an-independent-spectrum-prediction"

zil attach resonanceDecoherenceFunctional_norm_eq_matsubara_mul where
  formalizes @ "claim:resonance-decoherence-matrix-norm-is-product-of-matsubara-mode-dampings",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston.decoherenceFunctional_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara",
  caveat @ "claim:rank-one-consistent-history-functional-on-the-diagonal-hermite-resonance-sector"

zil attach resonanceDecoherenceFunctional_diag_re_eq_matsubara_sq where
  formalizes @ "claim:resonance-born-diagonal-is-the-square-of-the-matsubara-mode-damping",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston.decoherenceFunctional_diag_re",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara",
  caveat @ "claim:born-diagonal-of-the-rank-one-hermite-resonance-history-functional"

zil attach resonance_oneLoopWaveFunction_norm_eq_matsubara where
  formalizes @ "claim:gelfand-yaglom-one-loop-resonance-wavefunction-is-matsubara-damping-times-determinant-prefactor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara",
  requires @ "claim:positive-gelfand-yaglom-determinant",
  caveat @ "claim:one-loop-gaussian-dressing-not-a-renormalized-all-orders-amplitude"

zil attach chiral_resonance_oneLoop_and_no_second_loop where
  formalizes @ "claim:chiral-cs-resonance-sector-has-one-loop-dressing-and-no-two-loop-or-higher-graph-shape",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.OneLoopExactGraphShape.no_two_loop_or_higher",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonance_oneLoopWaveFunction_norm_eq_matsubara",
  caveat @ "claim:no-second-loop-result-is-specific-to-the-one-loop-exact-chiral-chern-simons-graph-classification-not-general-qed"

zil attach resonanceBasis_continuumFunctionalSchrodinger where
  formalizes @ "claim:explicit-four-dimensional-hermite-resonances-diagonalize-a-complex-caticha-functional-schrodinger-generator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.resonanceOperator_apply_basis",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodinger_apply",
  caveat @ "claim:unit-lapse-zero-shift-specialization-on-the-constructed-diagonal-resonance-operator"

zil attach resonanceProjectiveRiccatiFlow_eq_eigenvalueGap where
  formalizes @ "claim:two-mode-complex-resonance-projective-riccati-field-is-the-eigenvalue-gap",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius.projective_schrodinger_riccati",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.resonanceOperator_apply_basis",
  caveat @ "claim:vector-field-specialization-uses-the-existing-quotient-derivative-theorem-and-is-not-an-ode-existence-result"

zil attach resonanceMode_constantWilson_supplies_witten_FK where
  formalizes @ "claim:complex-resonance-mode-is-a-bounded-constant-wilson-observable-with-matsubara-witten-fk-bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_constantWilson_supplies_witten_FK",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara",
  requires @ "claim:finite-reference-field-measure",
  caveat @ "claim:constant-charge-sector-wilson-observable-not-a-field-dependent-holonomy-construction"

zil attach resonancePropagator_hasDerivAt where
  formalizes @ "claim:bounded-four-dimensional-resonance-operator-has-global-operator-exponential-evolution",
  supported_by @ "lean:hasDerivAt_exp_smul_const'",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.resonanceOperator",
  caveat @ "claim:bounded-operator-evolution-on-the-constructed-l2-carrier-not-an-unbounded-hamiltonian-domain-theorem"

zil attach resonancePropagator_add where
  formalizes @ "claim:four-dimensional-resonance-operator-exponential-is-a-global-time-translation-semigroup",
  supported_by @ "lean:NormedSpace.exp_add_of_commute",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_hasDerivAt",
  caveat @ "claim:nonunitary-semigroup-unless-additional-self-adjointness-conditions-hold"

zil attach resonanceModeRatio_hasDerivAt_riccati where
  formalizes @ "claim:any-two-diagonal-resonance-mode-exponentials-give-a-global-complex-projective-riccati-solution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius.projective_schrodinger_riccati",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeEvolution_hasDerivAt",
  caveat @ "claim:global-existence-for-explicit-diagonal-mode-ratios-not-general-infinite-dimensional-operator-riccati-well-posedness"

zil attach abelianWilsonHolonomy_supplies_witten_FK where
  formalizes @ "claim:measurable-field-dependent-u1-holonomy-supplies-the-witten-complex-feynman-kac-integral",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_normOneWilson_supplies_witten_FK",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.abelianWilsonHolonomy_norm",
  requires @ "claim:measurable-real-circulation-functional-and-finite-reference-field-measure",
  caveat @ "claim:abelian-exponentiated-circulation-not-nonabelian-path-ordered-holonomy"

zil attach finitePathOrderedWilson_supplies_witten_FK where
  formalizes @ "claim:finite-nonabelian-path-ordered-unitary-holonomy-has-a-normalized-wilson-trace-and-witten-fk-bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_norm_le_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_continuous",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_normOneWilson_supplies_witten_FK",
  requires @ "claim:positive-finite-representation-dimension-continuous-segment-transports-and-finite-reference-field-measure",
  caveat @ "claim:finite-ordered-product-of-segment-transports-not-a-continuum-nonabelian-path-ordered-exponential"

zil attach finitePathOrderedWilson_localGauge_invariant where
  formalizes @ "claim:finite-closed-nonabelian-wilson-trace-is-invariant-under-vertex-local-gauge-transformations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.GaugeRelatedPath.prod_eq_endpoint_conjugation",
  supported_by @ "lean:Matrix.trace_unitary_conj",
  requires @ "claim:closed-discrete-path-with-equal-source-and-target-gauge-values",
  caveat @ "claim:exact-discrete-local-gauge-covariance-not-yet-a-continuum-connection-parallel-transport-theorem"

zil attach secondDyson_connectedVacuum_is_two_loop where
  formalizes @ "claim:second-dyson-order-of-a-cubic-interaction-is-two-loop-exactly-for-a-full-connected-six-field-vacuum-wick-contraction",
  supported_by @ "lean:WickContraction.pair_card_mul_two_eq_of_isFull",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonTerm_two_eq_timeOrderedSquare",
  requires @ "claim:full-wick-pairing-and-a-contracted-edge-connecting-the-two-cubic-vertices",
  caveat @ "claim:combinatorial-connected-vacuum-sector-criterion-not-a-claim-that-every-second-dyson-order-term-is-two-loop"

zil attach regularInteraction_fullVacuum_loopNumber where
  formalizes @ "claim:full-wick-contractions-of-arbitrary-regular-interactions-have-the-standard-edge-count-and-connected-cycle-rank-formula",
  supported_by @ "lean:WickContraction.pair_card_mul_two_eq_of_isFull",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.fullWickContraction_edgeCount",
  requires @ "claim:declared-regular-vertex-valence-and-full-vacuum-contraction",
  caveat @ "claim:cycle-rank-formula-does-not-infer-graph-connectivity-from-wick-fullness"

zil attach exists_local_operatorRiccati_solution where
  formalizes @ "claim:bounded-nonlinear-operator-riccati-evolution-has-a-local-banach-space-solution-for-every-initial-operator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccatiField_contDiff",
  supported_by @ "lean:ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀",
  caveat @ "claim:local-bounded-operator-picard-lindelof-existence-not-global-no-blowup-or-unbounded-domain-control"

zil attach operatorRiccati_solution_eventuallyEq where
  formalizes @ "claim:bounded-operator-riccati-solutions-with-the-same-initial-operator-are-locally-unique",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccatiField_contDiff",
  supported_by @ "lean:ODE_solution_unique_of_eventually",
  caveat @ "claim:local-uniqueness-near-the-initial-time-not-global-existence"

zil attach affineOperatorRiccatiSolution_unique where
  formalizes @ "claim:the-affine-bounded-operator-riccati-sector-has-a-unique-global-no-blowup-solution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.affineOperatorRiccatiSolution_hasDerivAt",
  supported_by @ "lean:ODE_solution_unique_univ",
  requires @ "claim:affine-sector-a-equals-c-equals-d-equals-zero",
  caveat @ "claim:global-affine-solution-not-global-well-posedness-for-the-quadratic-c-nonzero-operator-riccati-equation"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis

end

end
