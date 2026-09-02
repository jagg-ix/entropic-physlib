/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
public import Physlib.Thermodynamics.QuantumRelativeEntropyArrow
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# Finite Spohn variational H-theorem

This module combines the reusable finite Gibbs variational carrier with the existing nonnegative
GKLS jump rate. The analytical identification

`d/dt (F(ρ_t) - F_Gibbs) = -gklsEntropicRate L ρ_t`

is an explicit hypothesis: the repository's `gklsEntropicRate` is a nonnegative jump-intensity
functional, and its nonnegativity alone does not prove the Spohn derivative identity. Once a model
supplies that identity, Mathlib's derivative criterion upgrades the local sign to global antitonicity
of both the free-energy gap and relative entropy.

The finite Gibbs layer is diagonal.  The operator-facing interface below is more general: it records
an actual density-matrix witness for a finite Umegaki relative-entropy gap and an exact derivative
law.  It does not manufacture that derivative, detailed balance, convergence to a unique steady
state, or a logarithmic Sobolev rate; concrete channels must discharge those obligations.

`IsFiniteDifferentialSpohnTrajectoryOn` is the model-facing interface: it accepts the actual
entropy-production density on an explicit time domain. The older `IsFiniteSpohnTrajectory` remains
as a backward-compatible specialization to `gklsEntropicRate`; the theorem below proving that this
jump intensity is nonzero at equilibrium explains why the generic interface is necessary.

The symmetric qubit NESS makes the distinction concrete. It is a genuine steady state of the
repository's full GKLS generator, but `gklsEntropicRate` equals `1` there. Consequently that functional
cannot be minus the derivative of a state-dependent free-energy gap along the constant steady orbit.
The obstruction is proved rather than silently identifying jump intensity with Spohn entropy production.
The final section then supplies the honest continuous-time interfaces: a `C₀` CPTP carrier has the
repository's GKLS generator only under an explicit right-difference-quotient hypothesis, and a finite
interval production approaches the instantaneous rate only along an `IsFiniteSpohnTrajectory`.

The last section records the classical control case extracted from Harold Grad's 1958
*Principles of the Kinetic Theory of Gases*. It reuses the repository's proved collision
log-balance inequality to obtain Grad's H-production kernel, then solves the homogeneous
BGK relaxation exactly as a strongly continuous affine semigroup. Its quadratic
near-Maxwellian entropy has an exact exponential decay law, a non-positive derivative,
and a finite-interval production whose derivative at zero is computed explicitly. This
does not formalize the Boltzmann--Grad limit or propagation of molecular chaos.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem

open Physlib.QuantumMechanics.Lindblad
open Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open QuantumInfo.Finite

variable {State Jump d : Type*} [Fintype State] [Fintype Jump]
  [Fintype d] [DecidableEq d]

/-! ## A. Conditional local-to-global Spohn theorem -/

/-- The finite free-energy deficit above the Gibbs variational minimum. -/
noncomputable def finiteGibbsFreeEnergyGap
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ) : ℝ :=
  finiteTrialFreeEnergy p G.energy G.beta - gibbsFreeEnergy G.partition G.beta

/-- The free-energy deficit is exactly `D(p ‖ p_Gibbs)/β`. -/
theorem finiteGibbsFreeEnergyGap_eq_relativeEntropy_div
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    finiteGibbsFreeEnergyGap G p = finiteRelativeEntropy p G.gibbsWeight / G.beta :=
  G.freeEnergy_gap_eq_relativeEntropy_div p hp hnorm

/-- Every positive normalized state has a nonnegative free-energy deficit. -/
theorem finiteGibbsFreeEnergyGap_nonneg
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    0 ≤ finiteGibbsFreeEnergyGap G p :=
  G.freeEnergy_gap_nonneg p hp hnorm

/-- A finite Spohn trajectory is precisely one for which the derivative of the Gibbs free-energy
gap is minus the repository's GKLS entropic rate. Keeping this as a predicate makes the missing
detailed-balance/operator-calculus obligation visible to downstream models. -/
def IsFiniteSpohnTrajectory
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : ℝ → MState d) : Prop :=
  ∀ t, HasDerivAt (fun s => finiteGibbsFreeEnergyGap G (p s))
    (-gklsEntropicRate L (ρ t)) t

/-- The honest differential Spohn interface for a supplied entropy-production
density `σ` on a physical time domain `D`.  Unlike `IsFiniteSpohnTrajectory`,
this carrier does not hard-wire `gklsEntropicRate`, which is a jump intensity
and is proved below not to vanish at a steady state.  Concrete models should
instantiate this predicate with the derivative of their relative-entropy or
free-energy deficit. -/
def IsFiniteDifferentialSpohnTrajectoryOn
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (σ : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ t ∈ D, HasDerivAt (fun s => finiteGibbsFreeEnergyGap G (p s)) (-σ t) t

/-- Operator-valued differential Spohn interface.  `gap` is not merely given
an operator interpretation in prose: at every physical time it must equal the
finite Umegaki relative entropy of an actual mixed state to the fixed reference
state.  The second field is the exact pointwise derivative law. -/
structure IsOperatorDifferentialSpohnTrajectoryOn
    (σref : MState d) (gap production : ℝ → ℝ) (D : Set ℝ) : Prop where
  operatorWitness : ∀ t ∈ D, ∃ ρ : MState d,
    entropicProperTime ρ σref ≠ ⊤ ∧
      gap t = (entropicProperTime ρ σref).toReal
  hasDerivAt : ∀ t ∈ D, HasDerivAt gap (-production t) t

/-- Local-to-global differential Spohn theorem at the scalar-gap level.  Both
the finite Gibbs and operator Umegaki interfaces delegate to this result. -/
theorem differential_spohn_gap_antitoneOn
    (gap production : ℝ → ℝ) (D : Set ℝ) (hD : Convex ℝ D)
    (hflow : ∀ t ∈ D, HasDerivAt gap (-production t) t)
    (hproduction : ∀ t ∈ D, 0 ≤ production t) :
    AntitoneOn gap D := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos hD
  · intro t ht
    exact (hflow t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hflow t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact neg_nonpos.mpr (hproduction t (interior_subset ht))

/-- The original jump-intensity predicate is a specialization of the generic
differential interface.  This is a compatibility bridge, not a claim that the
jump intensity is the correct production density for every GKSL model. -/
theorem isFiniteDifferentialSpohnTrajectoryOn_of_isFiniteSpohnTrajectory
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : ℝ → MState d)
    (hflow : IsFiniteSpohnTrajectory G p L ρ) :
    IsFiniteDifferentialSpohnTrajectoryOn G p
      (fun t => gklsEntropicRate L (ρ t)) Set.univ := by
  intro t _
  exact hflow t

/-- **Generic differential finite H-theorem.**  On a convex time domain, a
nonnegative supplied production density makes the Gibbs free-energy deficit
antitone.  This is the reusable local-to-global theorem appropriate both to
classical diagonal reductions and to future operator Spohn functionals. -/
theorem finite_differential_spohn_freeEnergyGap_antitoneOn
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (σ : ℝ → ℝ) (D : Set ℝ) (hD : Convex ℝ D)
    (hflow : IsFiniteDifferentialSpohnTrajectoryOn G p σ D)
    (hσ : ∀ t ∈ D, 0 ≤ σ t) :
    AntitoneOn (fun t => finiteGibbsFreeEnergyGap G (p t)) D :=
  differential_spohn_gap_antitoneOn _ σ D hD hflow hσ

/-- An operator differential Spohn trajectory with nonnegative production has
an antitone Umegaki gap on every convex physical time domain. -/
theorem operator_differential_spohn_gap_antitoneOn
    (σref : MState d) (gap production : ℝ → ℝ) (D : Set ℝ)
    (hD : Convex ℝ D)
    (hflow : IsOperatorDifferentialSpohnTrajectoryOn σref gap production D)
    (hproduction : ∀ t ∈ D, 0 ≤ production t) :
    AntitoneOn gap D :=
  differential_spohn_gap_antitoneOn gap production D hD hflow.hasDerivAt hproduction

/-- **[Global finite H-theorem]** A trajectory satisfying the Spohn derivative identity has an
antitone free-energy gap. This is the local-to-global step missing from rate nonnegativity alone. -/
theorem finite_spohn_freeEnergyGap_antitone
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : ℝ → MState d)
    (hflow : IsFiniteSpohnTrajectory G p L ρ) :
    Antitone (fun t => finiteGibbsFreeEnergyGap G (p t)) := by
  apply antitone_of_hasDerivAt_nonpos hflow
  intro t
  exact neg_nonpos.mpr (gklsEntropicRate_nonneg L (ρ t))

/-- Under positivity and normalization, the relative entropy to the Gibbs state is globally
antitone along a finite Spohn trajectory. -/
theorem finite_spohn_relativeEntropy_antitone
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : ℝ → MState d)
    (hp : ∀ t i, 0 < p t i) (hnorm : ∀ t, ∑ i, p t i = 1)
    (hflow : IsFiniteSpohnTrajectory G p L ρ) :
    Antitone (fun t => finiteRelativeEntropy (p t) G.gibbsWeight) := by
  have hgap := finite_spohn_freeEnergyGap_antitone G p L ρ hflow
  have heq : ∀ t, finiteRelativeEntropy (p t) G.gibbsWeight =
      G.beta * finiteGibbsFreeEnergyGap G (p t) := by
    intro t
    have h := finiteGibbsFreeEnergyGap_eq_relativeEntropy_div G (p t) (hp t) (hnorm t)
    calc
      finiteRelativeEntropy (p t) G.gibbsWeight =
          finiteGibbsFreeEnergyGap G (p t) * G.beta :=
        ((eq_div_iff G.beta_pos.ne').mp h).symm
      _ = G.beta * finiteGibbsFreeEnergyGap G (p t) := mul_comm _ _
  intro s t hst
  change finiteRelativeEntropy (p t) G.gibbsWeight ≤
    finiteRelativeEntropy (p s) G.gibbsWeight
  rw [heq t, heq s]
  exact mul_le_mul_of_nonneg_left (hgap hst) G.beta_pos.le

/-- The packaged finite Spohn result: free energy and relative entropy are antitone, while the
free-energy gap remains nonnegative at every time. -/
theorem finite_spohn_H_theorem
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : ℝ → MState d)
    (hp : ∀ t i, 0 < p t i) (hnorm : ∀ t, ∑ i, p t i = 1)
    (hflow : IsFiniteSpohnTrajectory G p L ρ) :
    Antitone (fun t => finiteGibbsFreeEnergyGap G (p t)) ∧
      Antitone (fun t => finiteRelativeEntropy (p t) G.gibbsWeight) ∧
      ∀ t, 0 ≤ finiteGibbsFreeEnergyGap G (p t) :=
  ⟨finite_spohn_freeEnergyGap_antitone G p L ρ hflow,
    finite_spohn_relativeEntropy_antitone G p L ρ hp hnorm hflow,
    fun t => finiteGibbsFreeEnergyGap_nonneg G (p t) (hp t) (hnorm t)⟩

/-! ## B. Jump intensity is not Spohn entropy production -/

/-- The maximally mixed qubit matrix is exactly the symmetric `XYZ` nonequilibrium
steady state used by `ZenoLiouvillianSpectrum`. -/
lemma uniformQubitMatrix_eq_symmetricNess :
    (MState.uniform : MState (Fin 2)).m = nessState 0 := by
  have hu : (MState.uniform : MState (Fin 2)).m =
      Matrix.diagonal (fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ)) := by
    have h : (MState.uniform : MState (Fin 2)).m =
        (HermitianMat.diagonal ℂ
          (fun x : Fin 2 => (ProbDistribution.uniform x : ℝ))).mat := rfl
    rw [h, HermitianMat.diagonal_mat]
    congr 1
  rw [hu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, nessState, eSS, ePP, Matrix.add_apply]

/-- The repository's `gklsEntropicRate`, evaluated on the two symmetric qubit
jump operators at the maximally mixed NESS, is exactly `1`. Thus it measures
jump intensity and does not vanish at equilibrium. -/
lemma symmetricNess_gklsJumpIntensity_eq_one :
    gklsEntropicRate ![eSP, ePS] (MState.uniform : MState (Fin 2)) = 1 := by
  unfold gklsEntropicRate
  rw [Fin.sum_univ_two]
  (simp [eSP, ePS, MState.uniform, MState.ofClassical, MState.m,
    HermitianMat.diagonal, ProbDistribution.uniform_def, Matrix.mul_apply,
    Matrix.trace, Fin.sum_univ_two, Matrix.conjTranspose_apply];
    norm_num)

/-- A constant state/free-energy trajectory cannot satisfy the current Spohn
derivative predicate whenever the supplied jump intensity is nonzero. The
derivative of the constant free-energy gap is zero, whereas the predicate asks
for its derivative to be minus that nonzero intensity. -/
lemma constant_not_isFiniteSpohnTrajectory_of_jumpIntensity_ne_zero
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : MState d)
    (hrate : gklsEntropicRate L ρ ≠ 0) :
    ¬ IsFiniteSpohnTrajectory G (fun _ => p) L (fun _ => ρ) := by
  intro h
  have ht := h 0
  have hc : HasDerivAt (fun _ : ℝ => finiteGibbsFreeEnergyGap G p) 0 0 :=
    hasDerivAt_const 0 _
  have heq : -gklsEntropicRate L ρ = 0 := ht.unique hc
  exact hrate (neg_eq_zero.mp heq)

/-- **Concrete scope obstruction for the current Spohn carrier.** The symmetric
qubit NESS is a genuine steady state of the full GKLS generator, yet the current
`gklsEntropicRate` is `1` and therefore cannot supply the derivative identity
for the constant equilibrium trajectory. A genuine Spohn theorem must use a
different entropy-production functional that vanishes at equilibrium. -/
lemma symmetricNess_isSteady_but_not_currentSpohnTrajectory
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ) (ℏ : ℝ) :
    IsGKLSSteady (0 : Matrix (Fin 2) (Fin 2) ℂ) ![eSP, ePS] ℏ
        (MState.uniform : MState (Fin 2)).m ∧
      gklsEntropicRate ![eSP, ePS] (MState.uniform : MState (Fin 2)) = 1 ∧
      ¬ IsFiniteSpohnTrajectory G (fun _ => p) ![eSP, ePS]
        (fun _ => (MState.uniform : MState (Fin 2))) := by
  refine ⟨?_, symmetricNess_gklsJumpIntensity_eq_one, ?_⟩
  · rw [uniformQubitMatrix_eq_symmetricNess]
    exact symmetric_ness_isGKLSSteady ℏ
  · apply constant_not_isFiniteSpohnTrajectory_of_jumpIntensity_ne_zero
    rw [symmetricNess_gklsJumpIntensity_eq_one]
    norm_num

/-! ## C. `C₀` semigroup generator and interval-to-rate bridges -/

open Physlib.Thermodynamics.QuantumRelativeEntropyArrow

/-- A strongly continuous CPTP semigroup has the repository's GKLS generator
when its right matrix difference quotient converges to `gklsGenerator` on every
mixed state.  This keeps generator identification as an explicit analytical
property of the channel family. -/
def HasGKLSGenerator (S : CPTPC0Semigroup d) (H : Matrix d d ℂ)
    (L : Jump → Matrix d d ℂ) (ℏ : ℝ) : Prop :=
  S.HasInfinitesimalGenerator (gklsGenerator H L ℏ)

/-- If a `C₀` CPTP semigroup has the GKLS generator, then every state fixed by
the full channel family is a GKLS steady state.  This connects the global flow
notion of equilibrium to the existing infinitesimal predicate. -/
lemma fixedPoint_isGKLSSteady (S : CPTPC0Semigroup d) (H : Matrix d d ℂ)
    (L : Jump → Matrix d d ℂ) (ℏ : ℝ) (hgen : HasGKLSGenerator S H L ℏ)
    (ρ : MState d) (hfix : S.toCPTPPositiveTimeSemigroup.IsFixedPoint ρ) :
    IsGKLSSteady H L ℏ ρ.m :=
  S.generator_eq_zero_of_fixedPoint (gklsGenerator H L ℏ) hgen ρ hfix

/-- Free-energy production over a finite interval `[s,t]`: the decrease of the
finite Gibbs free-energy gap between the two endpoints. -/
noncomputable def finiteSpohnIntervalProduction
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (s t : ℝ) : ℝ :=
  finiteGibbsFreeEnergyGap G (p s) - finiteGibbsFreeEnergyGap G (p t)

/-- **Controlled interval-to-rate limit.** Along a finite Spohn trajectory,
the production over `[0,t]`, divided by `t`, converges from the right to the
instantaneous entropy-production rate at zero.  This is the precise analytical
bridge between the finite-interval ledger and the derivative predicate; it
does not identify the repository's jump intensity with Spohn production unless
the supplied trajectory actually satisfies `IsFiniteSpohnTrajectory`. -/
lemma finiteSpohnIntervalProduction_rate_tendsto
    (G : FiniteGibbsVariationalSystem State) (p : ℝ → State → ℝ)
    (L : Jump → Matrix d d ℂ) (ρ : ℝ → MState d)
    (hflow : IsFiniteSpohnTrajectory G p L ρ) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ * finiteSpohnIntervalProduction G p 0 t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (gklsEntropicRate L (ρ 0))) := by
  have hslope := (hflow 0).tendsto_slope_zero_right.neg
  convert hslope using 1
  · funext t
    simp only [finiteSpohnIntervalProduction, zero_add]
    ring_nf
  · ring_nf

/-! ## D. Grad's collision H-kernel and homogeneous BGK `C₀` control model

Grad's equations (18.4--18.5) reduce the Boltzmann H-theorem to
`(a-b) log(a/b) ≥ 0`, with equality precisely at detailed balance. Equations
(32.1--32.3) replace the collision operator by BGK relaxation toward the
matching Maxwellian. For a fixed homogeneous equilibrium and collision
frequency, the solution is an affine `C₀` semigroup. The quadratic functional
below is the diagonal Hermite entropy from Grad's Section 30, restricted to one
nonconserved mode.

Reference: H. Grad, *Principles of the Kinetic Theory of Gases* (1958),
especially Sections 18, 30, and 32. -/

open Physlib.Thermodynamics.SecondLawQuantumBoltzmann

/-- Grad's per-collision H-production kernel
`(a-b) log(a/b)` for outgoing and incoming positive occupation products. -/
def gradCollisionProduction (outProd inProd : ℝ) : ℝ :=
  (outProd - inProd) * Real.log (outProd / inProd)

/-- Grad's collision kernel is exactly the log-balance expression already
proved for the repository's classical/quantum Boltzmann collision quartet. -/
lemma gradCollisionProduction_eq_logBalance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gradCollisionProduction a b =
      (Real.log a - Real.log b) * (a - b) := by
  rw [gradCollisionProduction, Real.log_div ha.ne' hb.ne']
  ring

/-- **Grad H-theorem kernel.** Every positive binary collision channel has
nonnegative entropy production. -/
lemma gradCollisionProduction_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ gradCollisionProduction a b := by
  rw [gradCollisionProduction_eq_logBalance ha hb]
  exact entropyProduction_term_nonneg ha hb

/-- Grad's production vanishes exactly when incoming and outgoing occupation
products satisfy detailed balance. -/
lemma gradCollisionProduction_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gradCollisionProduction a b = 0 ↔ a = b := by
  rw [gradCollisionProduction_eq_logBalance ha hb]
  exact entropyProduction_term_eq_zero_iff ha hb

/-- The exact homogeneous BGK relaxation toward a fixed Maxwellian coordinate:
`f_t = f_eq + exp(-νt) (f_in - f_eq)`. -/
def gradBGKRelaxation (ν equilibrium t initial : ℝ) : ℝ :=
  equilibrium + Real.exp (-ν * t) * (initial - equilibrium)

/-- The BGK relaxation starts at the supplied initial coordinate. -/
@[simp] lemma gradBGKRelaxation_zero (ν equilibrium initial : ℝ) :
    gradBGKRelaxation ν equilibrium 0 initial = initial := by
  simp [gradBGKRelaxation]

/-- **BGK semigroup law.** Relaxing for `s+t` equals relaxation for `s`
followed by relaxation for `t`. -/
lemma gradBGKRelaxation_add (ν equilibrium s t initial : ℝ) :
    gradBGKRelaxation ν equilibrium (s + t) initial =
      gradBGKRelaxation ν equilibrium t (gradBGKRelaxation ν equilibrium s initial) := by
  simp only [gradBGKRelaxation]
  rw [show -ν * (s + t) = -ν * s + -ν * t by ring, Real.exp_add]
  ring

/-- Every scalar BGK orbit is continuous, giving the strong-continuity part of
the homogeneous finite-mode `C₀` carrier. -/
lemma gradBGKRelaxation_continuous (ν equilibrium initial : ℝ) :
    Continuous (fun t => gradBGKRelaxation ν equilibrium t initial) := by
  unfold gradBGKRelaxation
  fun_prop

/-- **BGK generator equation.** The exact relaxation orbit solves
`d f_t / dt = ν (f_eq - f_t)` at every time. -/
lemma gradBGKRelaxation_hasDerivAt (ν equilibrium initial t : ℝ) :
    HasDerivAt (fun s => gradBGKRelaxation ν equilibrium s initial)
      (ν * (equilibrium - gradBGKRelaxation ν equilibrium t initial)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -ν * s) (-ν) t := by
    simpa using (hasDerivAt_id t).const_mul (-ν)
  have h := (hlin.exp.mul_const (initial - equilibrium)).const_add equilibrium
  have hderiv : Real.exp (-ν * t) * -ν * (initial - equilibrium) =
      ν * (equilibrium -
        (equilibrium + Real.exp (-ν * t) * (initial - equilibrium))) := by
    ring
  simpa only [gradBGKRelaxation] using h.congr_deriv hderiv

/-- One-mode quadratic part of Grad's near-equilibrium Hermite entropy. -/
def gradLinearizedEntropy (equilibrium state : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (state - equilibrium) ^ 2

/-- The quadratic Hermite entropy defect is nonnegative. -/
lemma gradLinearizedEntropy_nonneg (equilibrium state : ℝ) :
    0 ≤ gradLinearizedEntropy equilibrium state :=
  mul_nonneg (by norm_num) (sq_nonneg _)

/-- The quadratic entropy defect of the BGK mode decays exactly as
`exp(-2νt)`. -/
lemma gradLinearizedEntropy_along_bgk (ν equilibrium initial t : ℝ) :
    gradLinearizedEntropy equilibrium (gradBGKRelaxation ν equilibrium t initial) =
      Real.exp (-2 * ν * t) * gradLinearizedEntropy equilibrium initial := by
  unfold gradLinearizedEntropy gradBGKRelaxation
  rw [show -2 * ν * t = -ν * t + -ν * t by ring, Real.exp_add]
  ring

/-- The exact differential H-balance along homogeneous BGK relaxation. -/
lemma gradLinearizedEntropy_hasDerivAt (ν equilibrium initial t : ℝ) :
    HasDerivAt
      (fun s => gradLinearizedEntropy equilibrium (gradBGKRelaxation ν equilibrium s initial))
      (-2 * ν * gradLinearizedEntropy equilibrium
        (gradBGKRelaxation ν equilibrium t initial)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -2 * ν * s) (-2 * ν) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 * ν)
  have h := hlin.exp.mul_const (gradLinearizedEntropy equilibrium initial)
  rw [show
    (fun s => gradLinearizedEntropy equilibrium (gradBGKRelaxation ν equilibrium s initial)) =
      (fun s => Real.exp (-2 * ν * s) * gradLinearizedEntropy equilibrium initial) by
        funext s
        exact gradLinearizedEntropy_along_bgk ν equilibrium initial s]
  rw [gradLinearizedEntropy_along_bgk]
  exact h.congr_deriv (by ring)

/-- For nonnegative collision frequency, the quadratic H derivative is
nonpositive, matching Grad's sign convention `dH/dt = -G`. -/
lemma gradLinearizedEntropy_deriv_nonpos (ν equilibrium initial t : ℝ) (hν : 0 ≤ ν) :
    -2 * ν * gradLinearizedEntropy equilibrium
      (gradBGKRelaxation ν equilibrium t initial) ≤ 0 := by
  have hH := gradLinearizedEntropy_nonneg equilibrium
    (gradBGKRelaxation ν equilibrium t initial)
  nlinarith

/-- Finite-interval BGK production is the loss of quadratic H between two
times, directly parallel to `finiteSpohnIntervalProduction`. -/
def gradBGKIntervalProduction (ν equilibrium initial s t : ℝ) : ℝ :=
  gradLinearizedEntropy equilibrium (gradBGKRelaxation ν equilibrium s initial) -
    gradLinearizedEntropy equilibrium (gradBGKRelaxation ν equilibrium t initial)

/-- The finite-interval BGK production is nonnegative on forward intervals. -/
lemma gradBGKIntervalProduction_nonneg (ν equilibrium initial s t : ℝ)
    (hν : 0 ≤ ν) (hst : s ≤ t) :
    0 ≤ gradBGKIntervalProduction ν equilibrium initial s t := by
  rw [gradBGKIntervalProduction, gradLinearizedEntropy_along_bgk,
    gradLinearizedEntropy_along_bgk]
  have hexp : Real.exp (-2 * ν * t) ≤ Real.exp (-2 * ν * s) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hH := gradLinearizedEntropy_nonneg equilibrium initial
  nlinarith

/-- The initial rate of finite-interval BGK production is exactly
`2ν H_quad(f_initial)`, giving an unconditional classical control example for
the conditional Spohn interval-to-rate interface above. -/
lemma gradBGKIntervalProduction_hasDerivAt_zero (ν equilibrium initial : ℝ) :
    HasDerivAt (fun t => gradBGKIntervalProduction ν equilibrium initial 0 t)
      (2 * ν * gradLinearizedEntropy equilibrium initial) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => -2 * ν * t) (-2 * ν) 0 := by
    simpa using (hasDerivAt_id 0).const_mul (-2 * ν)
  have hdecay := hlin.exp.mul_const (gradLinearizedEntropy equilibrium initial)
  have h := hdecay.neg.const_add (gradLinearizedEntropy equilibrium initial)
  simpa only [gradBGKIntervalProduction, gradLinearizedEntropy_along_bgk,
    mul_zero, Real.exp_zero, one_mul, Pi.neg_apply, sub_eq_add_neg] using
      h.congr_deriv (by simp)

/- ZIL-BEGIN -/

zil attach differential_spohn_gap_antitoneOn where
  formalizes @ "claim:any-exact-differential-spohn-gap-law-gap-prime-equals-minus-a-nonnegative-production-density-implies-antitonicity-on-a-convex-time-domain",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:antitoneOn_of_hasDerivWithinAt_nonpos",
  caveat @ "claim:the-concrete-model-must-supply-both-the-exact-derivative-identity-and-production-nonnegativity"

zil attach operator_differential_spohn_gap_antitoneOn where
  formalizes @ "claim:an-operator-differential-spohn-trajectory-with-actual-finite-umegaki-density-operator-witnesses-and-nonnegative-production-has-an-antitone-relative-entropy-gap",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.differential_spohn_gap_antitoneOn",
  caveat @ "claim:abstract-interface-not-by-itself-a-construction-of-the-operator-relative-entropy-derivative-for-a-specific-channel"

zil attach finite_differential_spohn_freeEnergyGap_antitoneOn where
  formalizes @ "claim:a-nonnegative-model-supplied-spohn-production-density-implies-antitone-finite-gibbs-free-energy-on-every-convex-time-domain",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:antitoneOn_of_hasDerivWithinAt_nonpos",
  caveat @ "claim:the-production-density-and-its-exact-derivative-identity-are-model-data-this-theorem-does-not-identify-the-repository-jump-intensity-with-spohn-production"

zil attach finite_spohn_freeEnergyGap_antitone where
  formalizes @ "claim:spohn-derivative-identity-and-nonnegative-gkls-rate-imply-global-free-energy-descent",
  epistemic_status @ "risky",
  supported_by @ "paper:spohn-1978-entropy-production",
  caveat @ "claim:requires-explicit-derivative-identification-not-derived-from-jump-rate-nonnegativity-alone"

zil attach finite_spohn_relativeEntropy_antitone where
  formalizes @ "claim:finite-relative-entropy-to-gibbs-state-is-antitone-along-a-spohn-trajectory",
  supported_by @ "paper:spohn-lebowitz-1983-irreversible-thermodynamics-quantum-systems",
  epistemic_status @ "risky",
  requires @ "claim:spohn-derivative-identity-and-nonnegative-gkls-rate-imply-global-free-energy-descent",
  caveat @ "claim:finite-diagonal-relative-entropy-not-operator-data-processing-or-type-iii-araki-monotonicity"

zil attach finite_spohn_H_theorem where
  formalizes @ "claim:finite-gkls-spohn-flow-has-nonnegative-antitone-gibbs-free-energy-deficit",
  epistemic_status @ "risky",
  supported_by @ "paper:lindblad-1976-quantum-dynamical-semigroups",
  supported_by @ "paper:spohn-1978-entropy-production",
  caveat @ "claim:no-detailed-balance-unique-steady-state-convergence-or-log-sobolev-rate-without-further-data"

zil_theorem_intent symmetricNess_gklsJumpIntensity_eq_one where
  at_level toy_model
  must_mention [gklsEntropicRate,
    Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.eSP,
    Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.ePS]

zil attach symmetricNess_gklsJumpIntensity_eq_one where
  formalizes @ "claim:current-gkls-entropic-rate-is-positive-jump-intensity-at-the-symmetric-qubit-ness",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.symmetric_ness_isGKLSSteady",
  caveat @ "claim:exact-counterexample-to-interpreting-jump-intensity-as-spohn-entropy-production-not-a-failure-of-the-gkls-master-equation"

zil_theorem_intent constant_not_isFiniteSpohnTrajectory_of_jumpIntensity_ne_zero where
  at_level structural
  must_mention [IsFiniteSpohnTrajectory, finiteGibbsFreeEnergyGap, gklsEntropicRate]

zil attach constant_not_isFiniteSpohnTrajectory_of_jumpIntensity_ne_zero where
  formalizes @ "claim:nonzero-jump-intensity-cannot-be-minus-the-free-energy-derivative-on-a-constant-state-trajectory",
  epistemic_status @ "risky",
  supported_by @ "lean:HasDerivAt.unique",
  caveat @ "claim:structural-no-go-for-the-current-rate-functional-not-for-a-genuine-spohn-relative-entropy-production-functional"

zil_theorem_intent symmetricNess_isSteady_but_not_currentSpohnTrajectory where
  at_level bridge_theorem
  must_mention [IsGKLSSteady, IsFiniteSpohnTrajectory, gklsEntropicRate]

zil attach symmetricNess_isSteady_but_not_currentSpohnTrajectory where
  formalizes @ "claim:symmetric-qubit-ness-is-gkls-steady-but-cannot-satisfy-the-current-jump-intensity-spohn-derivative-predicate",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.symmetric_ness_isGKLSSteady",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.symmetricNess_gklsJumpIntensity_eq_one",
  caveat @ "claim:the-correct-remedy-is-a-relative-entropy-production-functional-vanishing-at-equilibrium-not-removal-of-the-lindblad-dynamics"

zil_theorem_intent gradCollisionProduction_nonneg where
  at_level bridge_theorem
  must_mention [gradCollisionProduction]

zil attach gradCollisionProduction_nonneg where
  formalizes @ "claim:positive-binary-collision-products-have-nonnegative-boltzmann-h-production",
  epistemic_status @ "risky",
  supported_by @ "paper:grad-1958-principles-kinetic-theory-gases-eq-18-4",
  supported_by @ "lean:Physlib.Thermodynamics.SecondLawQuantumBoltzmann.entropyProduction_term_nonneg",
  caveat @ "claim:exact-collision-log-balance-kernel-not-the-boltzmann-grad-limit-propagation-of-chaos-or-a-continuum-collision-integral"

zil attach gradCollisionProduction_eq_zero_iff where
  formalizes @ "claim:binary-collision-h-production-vanishes-exactly-at-detailed-balance",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.SecondLawQuantumBoltzmann.entropyProduction_term_eq_zero_iff",
  caveat @ "claim:equality-characterization-for-one-positive-collision-channel-not-the-global-maxwellian-characterization"

zil_theorem_intent gradCollisionProduction_eq_zero_iff where
  at_level bridge_theorem
  must_mention [gradCollisionProduction]

zil_theorem_intent gradBGKRelaxation_add where
  at_level structural
  must_mention [gradBGKRelaxation]

zil attach gradBGKRelaxation_add where
  formalizes @ "claim:homogeneous-fixed-equilibrium-bgk-relaxation-obeys-the-semigroup-composition-law",
  epistemic_status @ "risky",
  supported_by @ "paper:grad-1958-principles-kinetic-theory-gases-eq-32-1",
  caveat @ "claim:scalar-one-mode-affine-semigroup-not-the-inhomogeneous-nonlinear-bgk-or-full-boltzmann-flow"

zil_theorem_intent gradBGKRelaxation_hasDerivAt where
  at_level bridge_theorem
  must_mention [gradBGKRelaxation]

zil attach gradBGKRelaxation_hasDerivAt where
  formalizes @ "claim:the-exact-homogeneous-bgk-semigroup-has-generator-nu-times-equilibrium-minus-state",
  epistemic_status @ "risky",
  supported_by @ "lean:HasDerivAt.exp",
  caveat @ "claim:explicit-generator-of-the-fixed-equilibrium-scalar-bgk-control-model-not-a-construction-of-the-boltzmann-collision-generator"

zil attach gradLinearizedEntropy_along_bgk where
  formalizes @ "claim:one-hermite-mode-quadratic-entropy-defect-decays-as-exp-minus-two-nu-t",
  epistemic_status @ "risky",
  supported_by @ "paper:grad-1958-principles-kinetic-theory-gases-section-30-entropy-expansion",
  caveat @ "claim:exact-one-mode-quadratic-near-equilibrium-identity-not-the-full-nonlinear-f-log-f-entropy"

zil_theorem_intent gradLinearizedEntropy_along_bgk where
  at_level bridge_theorem
  must_mention [gradLinearizedEntropy, gradBGKRelaxation]

zil_theorem_intent gradBGKIntervalProduction_nonneg where
  at_level bridge_theorem
  must_mention [gradBGKIntervalProduction]

zil attach gradBGKIntervalProduction_nonneg where
  formalizes @ "claim:forward-bgk-intervals-have-nonnegative-quadratic-h-production",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradLinearizedEntropy_along_bgk",
  caveat @ "claim:homogeneous-linearized-bgk-control-theorem-not-unconditional-spohn-production-or-the-full-boltzmann-h-theorem"

zil_theorem_intent gradBGKIntervalProduction_hasDerivAt_zero where
  at_level bridge_theorem
  must_mention [gradBGKIntervalProduction, gradLinearizedEntropy]

zil attach gradBGKIntervalProduction_hasDerivAt_zero where
  formalizes @ "claim:the-initial-bgk-interval-production-rate-is-two-nu-times-the-quadratic-entropy-defect",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradLinearizedEntropy_hasDerivAt",
  caveat @ "claim:unconditional-rate-only-for-the-explicit-homogeneous-bgk-control-orbit-not-for-an-arbitrary-gkls-or-boltzmann-trajectory"

zil_file_contract physlib.spohnVariationalHTheorem where
  promises "A reusable finite Gibbs free-energy gap equal to relative entropy divided by beta, plus the rigorous local-to-global H-theorem whenever a model supplies its derivative identity; a concrete symmetric-qubit NESS obstruction proving that the repository's current positive jump-intensity functional cannot itself be the Spohn entropy-production derivative; and Grad's classical control case, comprising the exact binary collision H-kernel, an explicit homogeneous BGK C0 affine semigroup and generator, and its quadratic Hermite entropy interval/rate identities."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Lindblad.gklsEntropicRate_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.FiniteGibbsVariationalSystem.freeEnergy_gap_eq_relativeEntropy_div",
    "lean:Physlib.Thermodynamics.SecondLawQuantumBoltzmann.entropyProduction_term_nonneg",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKRelaxation_hasDerivAt"
  ]
  forbids_substitutes [
    "claiming the repository jump-rate functional is automatically the derivative of operator relative entropy",
    "claiming operator data processing, detailed balance, convergence to a unique steady state, or an infinite-dimensional Spohn theorem",
    "calling conditional antitonicity an unconditional theorem for every Lindblad evolution",
    "calling the nonnegative jump-count intensity Spohn entropy production after the proved steady-state counterexample",
    "claiming the scalar homogeneous bgk control model proves the nonlinear boltzmann-grad limit or propagation of molecular chaos",
    "calling the one-mode quadratic hermite entropy the full nonlinear f-log-f entropy functional"
  ]
  witnessed_by [finiteGibbsFreeEnergyGap_eq_relativeEntropy_div,
    finite_spohn_freeEnergyGap_antitone, finite_spohn_relativeEntropy_antitone,
    finite_spohn_H_theorem, symmetricNess_gklsJumpIntensity_eq_one,
    constant_not_isFiniteSpohnTrajectory_of_jumpIntensity_ne_zero,
    symmetricNess_isSteady_but_not_currentSpohnTrajectory,
    gradCollisionProduction_nonneg, gradCollisionProduction_eq_zero_iff,
    gradBGKRelaxation_add, gradBGKRelaxation_hasDerivAt,
    gradLinearizedEntropy_along_bgk, gradBGKIntervalProduction_nonneg,
    gradBGKIntervalProduction_hasDerivAt_zero]

/- ZIL-END -/

end Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem

end
