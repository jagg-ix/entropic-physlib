/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
public import Mathlib.Analysis.Calculus.Deriv.Shift
meta import Zil

/-!
# Continuum ADM constraint propagation

This module instantiates the repository's nonlinear `G`-free Einstein Cauchy
problem on an actual infinite-dimensional metric--momentum--matter carrier:
finite tensor components whose entries lie in the completed continuum
Fourier `Ḣ¹(ℝ³)` energy coordinate. Hamiltonian and momentum residuals live
in the dual `Ḣ⁻¹` carrier.

A bounded linear homogeneous residual evolution is the ADM/Bianchi subsidiary
system.  The constraint map has a Fréchet derivative whose value on the ADM
vector field is the subsidiary generator applied to the residual.  The chain
rule derives the residual evolution along every solution, and ODE uniqueness
then proves that zero initial constraints remain zero.  This discharges
`GFreeNonlinearEinsteinCauchyProblem.fieldEquation_propagates` instead of
copying either it or a trajectory-level propagation law as a premise.  The
pointwise Bianchi/ADM tangency identity remains explicit analytic data.

The local Cauchy result has simultaneous weak Hamiltonian and momentum
constraint propagation.  The globally Lipschitz hypothesis already stored in
the concrete datum gives a uniform local lifespan at every phase-space point;
compatible Picard--Lindelöf solutions therefore patch to a unique
all-real-time development without a separate uniform vector-field bound.
Global Lipschitz regularity on the entire gauge-reduced Banach phase space is
still a strong explicit analytic premise, not a theorem for arbitrary
Einstein initial data or a maximal globally hyperbolic development.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation

open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

abbrev ADMSpatialTensorField : Type :=
  (Fin 3 × Fin 3) → FourierDotHOneThree

abbrev ADMMatterCauchyField : Type :=
  Fin 4 → FourierDotHOneThree

abbrev ADMMetricMomentumMatterPhaseSpace : Type :=
  ADMSpatialTensorField × (ADMSpatialTensorField × ADMMatterCauchyField)

abbrev ADMWeakConstraintResidual : Type :=
  FourierDotHMinusOneThree × (Fin 3 → FourierDotHMinusOneThree)

def metricField (state : ADMMetricMomentumMatterPhaseSpace) : ADMSpatialTensorField :=
  state.1

def momentumField (state : ADMMetricMomentumMatterPhaseSpace) : ADMSpatialTensorField :=
  state.2.1

def matterField (state : ADMMetricMomentumMatterPhaseSpace) : ADMMatterCauchyField :=
  state.2.2

private lemma odeSolutionOn_piecewise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (K : ℝ≥0) (hlip : LipschitzWith K f)
    {γ γ' : ℝ → E} {a b a' b' t₀ : ℝ}
    (hγ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (f (γ t)) t)
    (hγ' : ∀ t ∈ Set.Ioo a' b', HasDerivAt γ' (f (γ' t)) t)
    (ht₀ : t₀ ∈ Set.Ioo a b ∩ Set.Ioo a' b')
    (heq : γ t₀ = γ' t₀) :
    ∀ t ∈ Set.Ioo a b ∪ Set.Ioo a' b',
      HasDerivAt (Set.piecewise (Set.Ioo a b) γ γ')
        (f (Set.piecewise (Set.Ioo a b) γ γ' t)) t := by
  have hoverlap :
      Set.EqOn γ γ' (Set.Ioo (max a a') (min b b')) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ => f) (s := fun _ => Set.univ)
      (K := K) (t₀ := t₀)
    · intro _ _
      exact hlip.lipschitzOnWith
    · exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
    · intro t ht
      exact ⟨hγ t
          ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
            lt_of_lt_of_le ht.2 (min_le_left _ _)⟩,
        Set.mem_univ _⟩
    · intro t ht
      exact ⟨hγ' t
          ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
            lt_of_lt_of_le ht.2 (min_le_right _ _)⟩,
        Set.mem_univ _⟩
    · exact heq
  intro t ht
  by_cases hmem : t ∈ Set.Ioo a b
  · have hevent :
        Set.piecewise (Set.Ioo a b) γ γ' =ᶠ[𝓝 t] γ := by
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with y hy
      simp [Set.piecewise, hy]
    simpa [hevent.eq_of_nhds] using
      (hγ t hmem).congr_of_eventuallyEq hevent
  · have ht' : t ∈ Set.Ioo a' b' := ht.resolve_left hmem
    have heqOn :
        Set.EqOn (Set.piecewise (Set.Ioo a b) γ γ') γ'
          (Set.Ioo a' b') := by
      intro y hy
      by_cases hyab : y ∈ Set.Ioo a b
      · rw [Set.piecewise, if_pos hyab]
        exact hoverlap
          ⟨max_lt hyab.1 hy.1, lt_min hyab.2 hy.2⟩
      · simp [Set.piecewise, hyab]
    have hevent :
        Set.piecewise (Set.Ioo a b) γ γ' =ᶠ[𝓝 t] γ' := by
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with y hy
      exact heqOn hy
    simpa [hevent.eq_of_nhds] using
      (hγ' t ht').congr_of_eventuallyEq hevent

private theorem exists_global_solution_of_uniform_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (x₀ : E) (K : ℝ≥0)
    (hlip : LipschitzWith K f) (ε : ℝ) (hε : 0 < ε)
    (hlocal : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt γ (f (γ t)) t) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  let s : Set ℝ := {a | ∃ γ : ℝ → E, γ 0 = x₀ ∧
    ∀ t ∈ Set.Ioo (-a) a, HasDerivAt γ (f (γ t)) t}
  suffices hbdd : ¬ BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    have hfamily :
        ∀ a : ℝ, ∃ γ : ℝ → E, γ 0 = x₀ ∧
          ∀ t ∈ Set.Ioo (-a) a, HasDerivAt γ (f (γ t)) t := by
      intro a
      obtain ⟨b, hb, hab⟩ := hbdd a
      obtain ⟨γ, hγ0, hγ⟩ := hb
      exact ⟨γ, hγ0, fun t ht =>
        hγ t (Set.Ioo_subset_Ioo (by linarith) (by linarith) ht)⟩
    choose γ hγ0 hγ using hfamily
    have hnested :
        ∀ {a b : ℝ}, 0 < a → a ≤ b →
          Set.EqOn (γ a) (γ b) (Set.Ioo (-a) a) := by
      intro a b ha hab
      apply ODE_solution_unique_of_mem_Ioo
        (v := fun _ => f) (s := fun _ => Set.univ)
        (K := K) (t₀ := 0)
      · intro _ _
        exact hlip.lipschitzOnWith
      · constructor <;> linarith
      · intro t ht
        exact ⟨hγ a t ht, Set.mem_univ _⟩
      · intro t ht
        exact ⟨hγ b t
          (Set.Ioo_subset_Ioo (by linarith) (by linarith) ht), Set.mem_univ _⟩
      · rw [hγ0 a, hγ0 b]
    let global : ℝ → E := fun t => γ (|t| + 1) t
    have hglobal_eq :
        ∀ {a : ℝ}, 0 < a →
          Set.EqOn global (γ a) (Set.Ioo (-a) a) := by
      intro a ha t ht
      by_cases hlt : |t| + 1 < a
      · exact hnested (by positivity) hlt.le
          (by
            rw [Set.mem_Ioo, ← abs_lt]
            exact lt_add_one _)
      · exact (hnested ha (le_of_not_gt hlt) ht).symm
    refine ⟨global, ?_, ?_⟩
    · exact hglobal_eq (a := 1) (by norm_num) (by simp) |>.trans (hγ0 1)
    · intro t
      let a : ℝ := |t| + 1
      have ha : 0 < a := by positivity
      have ht : t ∈ Set.Ioo (-a) a := by
        rw [Set.mem_Ioo, ← abs_lt]
        exact lt_add_one _
      have hevent : global =ᶠ[𝓝 t] γ a := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
        exact hglobal_eq ha hy
      exact (hγ a t ht).congr_of_eventuallyEq hevent
  intro hbdd
  set asup := sSup s with hasup
  have hsnonempty : s.Nonempty := ⟨ε, hlocal x₀⟩
  obtain ⟨a, ha, hlt⟩ :=
    Real.add_neg_lt_sSup hsnonempty (ε := -(ε / 2))
      (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [Set.mem_setOf_eq] at ha
  rw [← hasup, ← sub_eq_add_neg] at hlt
  obtain ⟨γ, hγ0, hγ⟩ := ha
  obtain ⟨γ1Aux, hγ1Aux0, hγ1Aux⟩ :=
    hlocal (γ (-(asup - ε / 2)))
  let γ1 : ℝ → E := fun t => γ1Aux (t + (asup - ε / 2))
  have hγ1eq :
      γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by
    simp [γ1, hγ1Aux0]
  have hγ1 :
      ∀ t ∈ Set.Ioo (-(asup + ε / 2)) (-(asup - 3 * ε / 2)),
        HasDerivAt γ1 (f (γ1 t)) t := by
    intro t ht
    apply HasDerivAt.comp_add_const t (asup - ε / 2)
    apply hγ1Aux
    constructor <;> nlinarith [ht.1, ht.2]
  obtain ⟨γ2Aux, hγ2Aux0, hγ2Aux⟩ :=
    hlocal (γ (asup - ε / 2))
  let γ2 : ℝ → E := fun t => γ2Aux (t - (asup - ε / 2))
  have hγ2eq :
      γ2 (asup - ε / 2) = γ (asup - ε / 2) := by
    simp [γ2, hγ2Aux0]
  have hγ2 :
      ∀ t ∈ Set.Ioo (asup - 3 * ε / 2) (asup + ε / 2),
        HasDerivAt γ2 (f (γ2 t)) t := by
    intro t ht
    apply HasDerivAt.comp_sub_const t (asup - ε / 2)
    apply hγ2Aux
    constructor <;> nlinarith [ht.1, ht.2]
  have hεle : ε ≤ asup := le_csSup hbdd (hlocal x₀)
  let γleft : ℝ → E := Set.piecewise (Set.Ioo (-a) a) γ γ1
  let γext : ℝ → E :=
    Set.piecewise (Set.Ioo (-(asup + ε / 2)) a) γleft γ2
  have hγleft :
      ∀ t ∈ Set.Ioo (-a) a ∪
          Set.Ioo (-(asup + ε / 2)) (-(asup - 3 * ε / 2)),
        HasDerivAt γleft (f (γleft t)) t := by
    exact odeSolutionOn_piecewise (t₀ := -(asup - ε / 2))
      f K hlip hγ hγ1
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩ hγ1eq.symm
  have hγleft0 : γleft 0 = x₀ := by
    simp [γleft, show (0 : ℝ) ∈ Set.Ioo (-a) a by
      constructor <;> linarith, hγ0]
  have hγext0 : γext 0 = x₀ := by
    change Set.piecewise (Set.Ioo (-(asup + ε / 2)) a)
      γleft γ2 0 = x₀
    rw [Set.piecewise, if_pos (show (0 : ℝ) ∈
      Set.Ioo (-(asup + ε / 2)) a by
        constructor <;> linarith)]
    exact hγleft0
  have hγleftCore :
      ∀ t ∈ Set.Ioo (-(asup + ε / 2)) a,
        HasDerivAt γleft (f (γleft t)) t := by
    intro t ht
    apply hγleft t
    by_cases hta : t ∈ Set.Ioo (-a) a
    · exact Or.inl hta
    · right
      constructor
      · exact ht.1
      · have htaLeft : t ≤ -a := by
          apply le_of_not_gt
          intro htaRight
          exact hta ⟨htaRight, ht.2⟩
        linarith
  have hγext :
      ∀ t ∈ Set.Ioo (-(asup + ε / 2)) a ∪
          Set.Ioo (asup - 3 * ε / 2) (asup + ε / 2),
        HasDerivAt γext (f (γext t)) t := by
    exact odeSolutionOn_piecewise (t₀ := asup - ε / 2)
      f K hlip hγleftCore hγ2
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by
        simp only [γleft, Set.piecewise,
          if_pos (show asup - ε / 2 ∈ Set.Ioo (-a) a by
            constructor <;> linarith)]
        exact hγ2eq.symm)
  have hext :
      ∀ t ∈ Set.Ioo (-(asup + ε / 2)) (asup + ε / 2),
        HasDerivAt γext (f (γext t)) t := by
    intro t ht
    apply hγext t
    by_cases hta : t < a
    · exact Or.inl ⟨ht.1, hta⟩
    · exact Or.inr ⟨by linarith, ht.2⟩
  exact (not_lt.mpr
    (le_csSup hbdd ⟨γext, hγext0, hext⟩))
      (lt_add_of_pos_right asup (half_pos hε))

/-- Every globally Lipschitz autonomous vector field on a complete real
normed space has a solution for every real time.  Picard--Lindelöf gives a
uniform local lifespan after scaling the state-centred ball by
`‖f x‖ + 1`; ODE uniqueness then patches the local curves globally. -/
@[zil_level bridge_theorem]
theorem exists_global_solution_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (x₀ : E) (K : ℝ≥0)
    (hlip : LipschitzWith K f) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  apply exists_global_solution_of_uniform_local f x₀ K hlip ε hε
  intro x
  let radius : ℝ≥0 := ⟨‖f x‖ + 1, by positivity⟩
  let L : ℝ≥0 := ⟨((K : ℝ) + 1) * (radius : ℝ), by positivity⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (-ε) ε := by
    constructor <;> linarith
  let t₀ : Set.Icc (-ε) ε := ⟨0, hzero⟩
  have hnorm : ∀ y ∈ Metric.closedBall x radius, ‖f y‖ ≤ L := by
    intro y hy
    have hd : ‖y - x‖ ≤ (radius : ℝ) := by
      simpa [dist_eq_norm] using hy
    calc
      ‖f y‖ ≤ ‖f y - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖y - x‖ + ‖f x‖ := by
        gcongr
        exact hlip.norm_sub_le y x
      _ ≤ (K : ℝ) * (radius : ℝ) + ‖f x‖ := by
        gcongr
      _ ≤ ((K : ℝ) + 1) * (radius : ℝ) := by
        change (K : ℝ) * (‖f x‖ + 1) + ‖f x‖ ≤
          ((K : ℝ) + 1) * (‖f x‖ + 1)
        nlinarith [norm_nonneg (f x), K.coe_nonneg]
      _ = (L : ℝ) := rfl
  have hmul :
      (L : ℝ) * max (ε - (t₀ : ℝ)) ((t₀ : ℝ) - (-ε)) ≤
        (radius : ℝ) - (0 : ℝ) := by
    simp only [t₀, sub_zero, zero_sub, neg_neg, max_self, sub_zero]
    change (((K : ℝ) + 1) * (‖f x‖ + 1)) *
        (1 / (2 * ((K : ℝ) + 1))) ≤ ‖f x‖ + 1
    calc
      (((K : ℝ) + 1) * (‖f x‖ + 1)) *
          (1 / (2 * ((K : ℝ) + 1))) =
          (‖f x‖ + 1) / 2 := by
            field_simp
      _ ≤ ‖f x‖ + 1 := by nlinarith [norm_nonneg (f x)]
  have hpl : IsPicardLindelof
      (tmin := -ε) (tmax := ε) (fun _ : ℝ => f) t₀ x radius 0 L K :=
    IsPicardLindelof.of_time_independent hnorm hlip.lipschitzOnWith hmul
  obtain ⟨γ, hγ0, hγ⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  exact (hγ t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Compatibility corollary for the earlier bounded interface.  A globally
Lipschitz autonomous vector field already has an all-time trajectory on a
complete real Banach space; the uniform bound is retained only for API
compatibility. -/
@[zil_level bridge_theorem]
theorem exists_global_solution_of_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (x₀ : E) (K L : ℝ≥0)
    (hlip : LipschitzWith K f) (_hbound : ∀ x, ‖f x‖ ≤ L) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  exact exists_global_solution_of_lipschitz f x₀ K hlip

@[zil_level bridge_theorem]
theorem zero_of_linear_constraint_evolution
    (A : ADMWeakConstraintResidual →L[ℝ] ADMWeakConstraintResidual)
    (residual : ℝ → ADMWeakConstraintResidual) (ε : ℝ) (hε : 0 < ε)
    (hzero : residual 0 = 0)
    (hevolution : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt residual (A (residual t)) t) :
    ∀ t ∈ Set.Ioo (-ε) ε, residual t = 0 := by
  have hzeroEvolution :
      ∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt (fun _ : ℝ => (0 : ADMWeakConstraintResidual))
          (A ((fun _ : ℝ => (0 : ADMWeakConstraintResidual)) t)) t := by
    intro t _
    simpa using (hasDerivAt_const (x := t) (c := (0 : ADMWeakConstraintResidual)))
  have heq :
      Set.EqOn residual (fun _ : ℝ => (0 : ADMWeakConstraintResidual))
        (Set.Ioo (-ε) ε) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ => A) (s := fun _ => Set.univ)
      (K := ‖A‖₊) (t₀ := 0)
    · intro _ _
      exact A.lipschitz.lipschitzOnWith
    · constructor <;> linarith
    · intro t ht
      exact ⟨hevolution t ht, Set.mem_univ _⟩
    · intro t ht
      exact ⟨hzeroEvolution t ht, Set.mem_univ _⟩
    · simp [hzero]
  intro t ht
  exact heq ht

/-- Global counterpart of `zero_of_linear_constraint_evolution`: a
homogeneous bounded linear subsidiary system that starts at zero vanishes
for every real time. -/
@[zil_level bridge_theorem]
theorem zero_of_global_linear_constraint_evolution
    (A : ADMWeakConstraintResidual →L[ℝ] ADMWeakConstraintResidual)
    (residual : ℝ → ADMWeakConstraintResidual)
    (hzero : residual 0 = 0)
    (hevolution : ∀ t, HasDerivAt residual (A (residual t)) t) :
    ∀ t, residual t = 0 := by
  have hzeroEvolution :
      ∀ t, HasDerivAt (fun _ : ℝ => (0 : ADMWeakConstraintResidual))
        (A ((fun _ : ℝ => (0 : ADMWeakConstraintResidual)) t)) t := by
    intro t
    simpa using
      (hasDerivAt_const (x := t) (c := (0 : ADMWeakConstraintResidual)))
  have heq :
      residual = fun _ : ℝ => (0 : ADMWeakConstraintResidual) := by
    apply ODE_solution_unique_univ
      (v := fun _ => A) (s := fun _ => Set.univ)
      (K := ‖A‖₊) (t₀ := 0)
    · intro _
      exact A.lipschitz.lipschitzOnWith
    · intro t
      exact ⟨hevolution t, Set.mem_univ _⟩
    · intro t
      exact ⟨hzeroEvolution t, Set.mem_univ _⟩
    · simpa using hzero
  intro t
  exact congrFun heq t

/-- Concrete geometric, analytic, and subsidiary-system data on the
continuum ADM metric--momentum--matter phase space. -/
structure ConcreteADMGFreeCauchyData
    (ħ c σ₀ : ℝ) (initialState : ADMMetricMomentumMatterPhaseSpace) where
  vectorField :
    ADMMetricMomentumMatterPhaseSpace → ADMMetricMomentumMatterPhaseSpace
  realEinsteinTensor :
    ADMMetricMomentumMatterPhaseSpace → Matrix (Fin 4) (Fin 4) ℝ
  entropicCurvature :
    ADMMetricMomentumMatterPhaseSpace → Matrix (Fin 4) (Fin 4) ℝ
  stressEnergy :
    ADMMetricMomentumMatterPhaseSpace → Matrix (Fin 4) (Fin 4) ℝ
  entropicStress :
    ADMMetricMomentumMatterPhaseSpace → Matrix (Fin 4) (Fin 4) ℝ
  spatialScalarCurvature : ADMMetricMomentumMatterPhaseSpace → ℝ
  extrinsicCurvature :
    ADMMetricMomentumMatterPhaseSpace → Matrix (Fin 3) (Fin 3) ℝ
  extrinsicNormSq : ADMMetricMomentumMatterPhaseSpace → ℝ
  energyDensity : ADMMetricMomentumMatterPhaseSpace → ℝ
  momentumDivergence : ADMMetricMomentumMatterPhaseSpace → Fin 3 → ℝ
  matterMomentumDensity : ADMMetricMomentumMatterPhaseSpace → Fin 3 → ℝ
  weakHamiltonianResidual :
    ADMMetricMomentumMatterPhaseSpace → FourierDotHMinusOneThree
  weakMomentumResidual :
    ADMMetricMomentumMatterPhaseSpace → Fin 3 → FourierDotHMinusOneThree
  hamiltonianProbe : FourierDotHOneThree
  momentumProbe : Fin 3 → FourierDotHOneThree
  weakHamiltonian_probe :
    ∀ state,
      (weakHamiltonianResidual state hamiltonianProbe).re =
        hamiltonianConstraint
            (spatialScalarCurvature state) (extrinsicNormSq state)
            (extrinsicCurvature state)
          - inferenceEinsteinCoupling ħ c σ₀ * energyDensity state
  weakMomentum_probe :
    ∀ state i,
      (weakMomentumResidual state i (momentumProbe i)).re =
        momentumDivergence state i -
          inferenceEinsteinCoupling ħ c σ₀ * matterMomentumDensity state i
  initial_weakHamiltonian : weakHamiltonianResidual initialState = 0
  initial_weakMomentum : weakMomentumResidual initialState = 0
  constraintPropagation :
    ADMWeakConstraintResidual →L[ℝ] ADMWeakConstraintResidual
  constraintResidualDerivative :
    ADMMetricMomentumMatterPhaseSpace →
      ADMMetricMomentumMatterPhaseSpace →L[ℝ] ADMWeakConstraintResidual
  constraintResidual_hasFDerivAt :
    ∀ state,
      HasFDerivAt
        (fun s => (weakHamiltonianResidual s, weakMomentumResidual s))
        (constraintResidualDerivative state) state
  constraintResidualDerivative_vectorField :
    ∀ state,
      constraintResidualDerivative state (vectorField state) =
        constraintPropagation
          (weakHamiltonianResidual state, weakMomentumResidual state)
  fieldEquation_iff_weakConstraints :
    ∀ state,
      complexEinsteinFieldEquation
          (realEinsteinTensor state) (entropicCurvature state)
          (stressEnergy state) (entropicStress state)
          (inferenceEinsteinCoupling ħ c σ₀)
        ↔ weakHamiltonianResidual state = 0 ∧ weakMomentumResidual state = 0
  lipschitzConstant : ℝ≥0
  vectorField_contDiffAt : ContDiffAt ℝ 1 vectorField initialState
  vectorField_lipschitz : LipschitzWith lipschitzConstant vectorField

namespace ConcreteADMGFreeCauchyData

variable {ħ c σ₀ : ℝ} {initialState : ADMMetricMomentumMatterPhaseSpace}

def constraintResidual
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) : ADMWeakConstraintResidual :=
  (D.weakHamiltonianResidual state, D.weakMomentumResidual state)

def FieldEquation
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) : Prop :=
  complexEinsteinFieldEquation
    (D.realEinsteinTensor state) (D.entropicCurvature state)
    (D.stressEnergy state) (D.entropicStress state)
    (inferenceEinsteinCoupling ħ c σ₀)

/-- The gauge-reduced continuum ADM constraint surface: both the weak
Hamiltonian residual and all three weak momentum residuals vanish. -/
def constraintSurface
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) :
    Set ADMMetricMomentumMatterPhaseSpace :=
  {state | D.weakHamiltonianResidual state = 0 ∧
    D.weakMomentumResidual state = 0}

theorem initial_constraintResidual
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) :
    D.constraintResidual initialState = 0 := by
  apply Prod.ext
  · exact D.initial_weakHamiltonian
  · exact D.initial_weakMomentum

/-- The ADM/Bianchi subsidiary evolution along a Cauchy trajectory is derived
from the Fréchet chain rule and the pointwise tangency of the ADM vector field
to the constraint map.  No trajectory-level propagation certificate is
assumed. -/
@[zil_level bridge_theorem]
theorem constraintResidual_hasDerivAt_along
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace) (t : ℝ)
    (hevolution :
      HasDerivAt trajectory (D.vectorField (trajectory t)) t) :
    HasDerivAt
      ((fun state => (D.weakHamiltonianResidual state,
        D.weakMomentumResidual state)) ∘ trajectory)
      (D.constraintPropagation
        (D.weakHamiltonianResidual (trajectory t),
          D.weakMomentumResidual (trajectory t))) t := by
  have hchain :=
    (D.constraintResidual_hasFDerivAt (trajectory t)).comp_hasDerivAt
      t hevolution
  rw [D.constraintResidualDerivative_vectorField] at hchain
  exact hchain

/-- A chosen all-real-time integral curve through an arbitrary point of the
ADM phase space.  Uniqueness below makes every theorem about this choice
independent of the choice operator. -/
noncomputable def globalTrajectory
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) :
    ℝ → ADMMetricMomentumMatterPhaseSpace :=
  Classical.choose
    (exists_global_solution_of_lipschitz
      D.vectorField state D.lipschitzConstant D.vectorField_lipschitz)

private theorem globalTrajectory_spec
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) :
    D.globalTrajectory state 0 = state ∧
      ∀ t, HasDerivAt (D.globalTrajectory state)
        (D.vectorField (D.globalTrajectory state t)) t := by
  exact Classical.choose_spec
    (exists_global_solution_of_lipschitz
      D.vectorField state D.lipschitzConstant D.vectorField_lipschitz)

/-- The canonical global ADM flow associated with the declared globally
Lipschitz gauge-reduced vector field. -/
noncomputable def globalFlow
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (t : ℝ) (state : ADMMetricMomentumMatterPhaseSpace) :
    ADMMetricMomentumMatterPhaseSpace :=
  D.globalTrajectory state t

@[simp]
theorem globalFlow_zero
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) :
    D.globalFlow 0 state = state :=
  (D.globalTrajectory_spec state).1

theorem globalFlow_hasDerivAt
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) (t : ℝ) :
    HasDerivAt (fun s => D.globalFlow s state)
      (D.vectorField (D.globalFlow t state)) t :=
  (D.globalTrajectory_spec state).2 t

/-- The selected global trajectories form an additive real flow.  This is
not an extra choice principle: ODE uniqueness identifies the time-shifted
trajectory with the trajectory restarted at the shifted state. -/
@[zil_level bridge_theorem]
theorem globalFlow_add
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (s t : ℝ) (state : ADMMetricMomentumMatterPhaseSpace) :
    D.globalFlow (s + t) state =
      D.globalFlow s (D.globalFlow t state) := by
  have heq :
      (fun u => D.globalFlow (u + t) state) =
        (fun u => D.globalFlow u (D.globalFlow t state)) := by
    apply ODE_solution_unique_univ
      (v := fun _ => D.vectorField) (s := fun _ => Set.univ)
      (K := D.lipschitzConstant) (t₀ := 0)
    · intro _
      exact D.vectorField_lipschitz.lipschitzOnWith
    · intro u
      refine ⟨?_, Set.mem_univ _⟩
      exact (D.globalFlow_hasDerivAt state (u + t)).comp_add_const u t
    · intro u
      exact ⟨D.globalFlow_hasDerivAt (D.globalFlow t state) u,
        Set.mem_univ _⟩
    · simp
  exact congrFun heq s

/-- Negative time is a left inverse of positive time for the global ADM
flow. -/
@[simp]
theorem globalFlow_neg_apply
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (t : ℝ) (state : ADMMetricMomentumMatterPhaseSpace) :
    D.globalFlow (-t) (D.globalFlow t state) = state := by
  simpa using (D.globalFlow_add (-t) t state).symm

/-- Negative time is also a right inverse of positive time. -/
@[simp]
theorem globalFlow_apply_neg
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (t : ℝ) (state : ADMMetricMomentumMatterPhaseSpace) :
    D.globalFlow t (D.globalFlow (-t) state) = state := by
  simpa using (D.globalFlow_add t (-t) state).symm

/-- Every fixed-time ADM flow map is a bijection, with inverse given by the
negative-time flow. -/
@[zil_level bridge_theorem]
theorem globalFlow_bijective
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) (t : ℝ) :
    Function.Bijective (D.globalFlow t) := by
  constructor
  · intro x y hxy
    calc
      x = D.globalFlow (-t) (D.globalFlow t x) :=
        (D.globalFlow_neg_apply t x).symm
      _ = D.globalFlow (-t) (D.globalFlow t y) := congrArg _ hxy
      _ = y := D.globalFlow_neg_apply t y
  · intro y
    exact ⟨D.globalFlow (-t) y, D.globalFlow_apply_neg t y⟩

/-- Forward-time Grönwall stability of the global ADM flow with respect to
its initial state. -/
@[zil_level bridge_theorem]
theorem globalFlow_dist_le_of_nonneg
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (t : ℝ) (ht : 0 ≤ t)
    (x y : ADMMetricMomentumMatterPhaseSpace) :
    dist (D.globalFlow t x) (D.globalFlow t y) ≤
      dist x y * Real.exp ((D.lipschitzConstant : ℝ) * t) := by
  have hcont (state : ADMMetricMomentumMatterPhaseSpace) :
      Continuous (fun s => D.globalFlow s state) :=
    continuous_iff_continuousAt.mpr fun s =>
      (D.globalFlow_hasDerivAt state s).continuousAt
  have hbound :=
    dist_le_of_trajectories_ODE
      (v := fun _ => D.vectorField)
      (K := D.lipschitzConstant)
      (a := 0) (b := t)
      (fun _ => D.vectorField_lipschitz)
      (hcont x).continuousOn
      (fun s _ => (D.globalFlow_hasDerivAt x s).hasDerivWithinAt)
      (hcont y).continuousOn
      (fun s _ => (D.globalFlow_hasDerivAt y s).hasDerivWithinAt)
      (show dist (D.globalFlow 0 x) (D.globalFlow 0 y) ≤ dist x y by
        simp) t ⟨ht, le_rfl⟩
  simpa using hbound

/-- Two-sided continuous dependence of the global ADM flow on its initial
state.  The negative-time estimate applies the same Grönwall theorem to the
reversed vector field. -/
@[zil_level bridge_theorem]
theorem globalFlow_dist_le
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (t : ℝ) (x y : ADMMetricMomentumMatterPhaseSpace) :
    dist (D.globalFlow t x) (D.globalFlow t y) ≤
      dist x y * Real.exp ((D.lipschitzConstant : ℝ) * |t|) := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using D.globalFlow_dist_le_of_nonneg t ht x y
  · have htneg : t < 0 := lt_of_not_ge ht
    have hrevLip :
        LipschitzWith D.lipschitzConstant
          (fun state => -D.vectorField state) := by
      simpa [Function.comp_def] using
        LipschitzWith.id.neg.comp D.vectorField_lipschitz
    have hrevDeriv (state : ADMMetricMomentumMatterPhaseSpace) (s : ℝ) :
        HasDerivAt (fun u => D.globalFlow (-u) state)
          (-D.vectorField (D.globalFlow (-s) state)) s := by
      have hbase : HasDerivAt (D.globalTrajectory state)
          (D.vectorField (D.globalTrajectory state (-s))) (0 - s) := by
        simpa using (D.globalTrajectory_spec state).2 (-s)
      simpa [globalFlow] using hbase.comp_const_sub 0 s
    have hcont (state : ADMMetricMomentumMatterPhaseSpace) :
        Continuous (fun s => D.globalFlow (-s) state) :=
      continuous_iff_continuousAt.mpr fun s =>
        (hrevDeriv state s).continuousAt
    have hbound :=
      dist_le_of_trajectories_ODE
        (v := fun _ state => -D.vectorField state)
        (K := D.lipschitzConstant)
        (a := 0) (b := -t)
        (fun _ => hrevLip)
        (hcont x).continuousOn
        (fun s _ => (hrevDeriv x s).hasDerivWithinAt)
        (hcont y).continuousOn
        (fun s _ => (hrevDeriv y s).hasDerivWithinAt)
        (show dist (D.globalFlow (-0) x) (D.globalFlow (-0) y) ≤
            dist x y by simp)
        (-t) ⟨neg_nonneg.mpr (le_of_lt htneg), le_rfl⟩
    simpa [abs_of_neg htneg] using hbound

/-- Each fixed-time ADM flow map is globally Lipschitz, hence continuous,
with the explicit two-sided Grönwall constant `exp(K |t|)`. -/
@[zil_level bridge_theorem]
theorem globalFlow_lipschitz
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) (t : ℝ) :
    LipschitzWith
      ⟨Real.exp ((D.lipschitzConstant : ℝ) * |t|), Real.exp_nonneg _⟩
      (D.globalFlow t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (D.globalFlow t x) (D.globalFlow t y) ≤
    Real.exp ((D.lipschitzConstant : ℝ) * |t|) * dist x y
  rw [mul_comm]
  exact D.globalFlow_dist_le t x y

/-- Two-sided Grönwall control of the phase-space norm.  The forcing term is
the vector field at the origin; this is the standard affine growth estimate
for a globally Lipschitz autonomous vector field. -/
@[zil_level physical_theorem]
theorem globalFlow_norm_le
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (t : ℝ) (state : ADMMetricMomentumMatterPhaseSpace) :
    ‖D.globalFlow t state‖ ≤
      gronwallBound ‖state‖ (D.lipschitzConstant : ℝ)
        ‖D.vectorField 0‖ |t| := by
  by_cases ht : 0 ≤ t
  · have hcont :
        Continuous (fun s => D.globalFlow s state) :=
      continuous_iff_continuousAt.mpr fun s =>
        (D.globalFlow_hasDerivAt state s).continuousAt
    have hbound :=
      dist_le_of_approx_trajectories_ODE
        (v := fun _ => D.vectorField)
        (K := D.lipschitzConstant)
        (f := fun s => D.globalFlow s state)
        (g := fun _ => (0 : ADMMetricMomentumMatterPhaseSpace))
        (f' := fun s => D.vectorField (D.globalFlow s state))
        (g' := fun _ => (0 : ADMMetricMomentumMatterPhaseSpace))
        (εf := 0) (εg := ‖D.vectorField 0‖)
        (a := 0) (b := t)
        (fun _ => D.vectorField_lipschitz)
        hcont.continuousOn
        (fun s _ => (D.globalFlow_hasDerivAt state s).hasDerivWithinAt)
        (fun _ _ => by simp)
        continuous_const.continuousOn
        (fun s _ => (hasDerivAt_const
          (x := s) (c := (0 : ADMMetricMomentumMatterPhaseSpace))).hasDerivWithinAt)
        (fun _ _ => by simp [dist_eq_norm])
        (show dist (D.globalFlow 0 state) 0 ≤ ‖state‖ by simp)
        t ⟨ht, le_rfl⟩
    simpa [abs_of_nonneg ht, dist_eq_norm] using hbound
  · have htneg : t < 0 := lt_of_not_ge ht
    have hrevLip :
        LipschitzWith D.lipschitzConstant
          (fun x => -D.vectorField x) := by
      simpa [Function.comp_def] using
        LipschitzWith.id.neg.comp D.vectorField_lipschitz
    have hrevDeriv (s : ℝ) :
        HasDerivAt (fun u => D.globalFlow (-u) state)
          (-D.vectorField (D.globalFlow (-s) state)) s := by
      have hbase : HasDerivAt (D.globalTrajectory state)
          (D.vectorField (D.globalTrajectory state (-s))) (0 - s) := by
        simpa using (D.globalTrajectory_spec state).2 (-s)
      simpa [globalFlow] using hbase.comp_const_sub 0 s
    have hcont :
        Continuous (fun s => D.globalFlow (-s) state) :=
      continuous_iff_continuousAt.mpr fun s =>
        (hrevDeriv s).continuousAt
    have hbound :=
      dist_le_of_approx_trajectories_ODE
        (v := fun _ x => -D.vectorField x)
        (K := D.lipschitzConstant)
        (f := fun s => D.globalFlow (-s) state)
        (g := fun _ => (0 : ADMMetricMomentumMatterPhaseSpace))
        (f' := fun s => -D.vectorField (D.globalFlow (-s) state))
        (g' := fun _ => (0 : ADMMetricMomentumMatterPhaseSpace))
        (εf := 0) (εg := ‖D.vectorField 0‖)
        (a := 0) (b := -t)
        (fun _ => hrevLip)
        hcont.continuousOn
        (fun s _ => (hrevDeriv s).hasDerivWithinAt)
        (fun _ _ => by simp)
        continuous_const.continuousOn
        (fun s _ => (hasDerivAt_const
          (x := s) (c := (0 : ADMMetricMomentumMatterPhaseSpace))).hasDerivWithinAt)
        (fun _ _ => by simp [dist_eq_norm])
        (show dist (D.globalFlow (-0) state) 0 ≤ ‖state‖ by simp)
        (-t) ⟨neg_nonneg.mpr (le_of_lt htneg), le_rfl⟩
    simpa [abs_of_neg htneg, dist_eq_norm] using hbound

/-- Every finite time slab has an explicit uniform phase-norm bound. -/
@[zil_level physical_theorem]
theorem globalFlow_norm_le_on_timeSlab
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (T : ℝ) (state : ADMMetricMomentumMatterPhaseSpace)
    (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
    ‖D.globalFlow t state‖ ≤
      gronwallBound ‖state‖ (D.lipschitzConstant : ℝ)
        ‖D.vectorField 0‖ T := by
  calc
    ‖D.globalFlow t state‖ ≤
        gronwallBound ‖state‖ (D.lipschitzConstant : ℝ)
          ‖D.vectorField 0‖ |t| :=
      D.globalFlow_norm_le t state
    _ ≤ gronwallBound ‖state‖ (D.lipschitzConstant : ℝ)
          ‖D.vectorField 0‖ T :=
      (gronwallBound_mono (norm_nonneg _) (norm_nonneg _)
        D.lipschitzConstant.coe_nonneg) (abs_le.mpr ht)

/-- At every real time the global ADM evolution is a homeomorphism of the
complete continuum phase space; its inverse is evolution by negative time. -/
noncomputable def globalFlowHomeomorph
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) (t : ℝ) :
    ADMMetricMomentumMatterPhaseSpace ≃ₜ
      ADMMetricMomentumMatterPhaseSpace where
  toFun := D.globalFlow t
  invFun := D.globalFlow (-t)
  left_inv := D.globalFlow_neg_apply t
  right_inv := D.globalFlow_apply_neg t
  continuous_toFun := (D.globalFlow_lipschitz t).continuous
  continuous_invFun := (D.globalFlow_lipschitz (-t)).continuous

@[zil_level physical_theorem]
theorem weak_constraints_propagate
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace) (ε : ℝ)
    (hε : 0 < ε) (hzero : trajectory 0 = initialState)
    (hevolution : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory (D.vectorField (trajectory t)) t) :
    ∀ t ∈ Set.Ioo (-ε) ε,
      D.weakHamiltonianResidual (trajectory t) = 0 ∧
        D.weakMomentumResidual (trajectory t) = 0 := by
  have hresidual :
      ∀ t ∈ Set.Ioo (-ε) ε,
        (D.weakHamiltonianResidual (trajectory t),
          D.weakMomentumResidual (trajectory t)) = 0 := by
    apply zero_of_linear_constraint_evolution D.constraintPropagation
      ((fun state => (D.weakHamiltonianResidual state,
        D.weakMomentumResidual state)) ∘ trajectory) ε hε
    · change
        (D.weakHamiltonianResidual (trajectory 0),
          D.weakMomentumResidual (trajectory 0)) = 0
      rw [hzero]
      apply Prod.ext
      · exact D.initial_weakHamiltonian
      · exact D.initial_weakMomentum
    · intro t ht
      exact D.constraintResidual_hasDerivAt_along trajectory t
        (hevolution t ht)
  intro t ht
  have h := hresidual t ht
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem sourcedHamiltonianConstraint_of_weak
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace)
    (hweak : D.weakHamiltonianResidual state = 0) :
    sourcedHamiltonianConstraint
      (D.spatialScalarCurvature state) (D.extrinsicNormSq state)
      (D.energyDensity state) (inferenceEinsteinCoupling ħ c σ₀)
      (D.extrinsicCurvature state) := by
  have hp := D.weakHamiltonian_probe state
  rw [hweak] at hp
  simp only [zero_apply, Complex.zero_re] at hp
  unfold sourcedHamiltonianConstraint
  linarith

theorem sourcedMomentumConstraint_of_weak
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace)
    (hweak : D.weakMomentumResidual state = 0) :
    ∀ i,
      D.momentumDivergence state i =
        inferenceEinsteinCoupling ħ c σ₀ * D.matterMomentumDensity state i := by
  intro i
  have hp := D.weakMomentum_probe state i
  rw [hweak] at hp
  simp only [Pi.zero_apply, zero_apply, Complex.zero_re] at hp
  linarith

@[zil_level physical_theorem]
theorem adm_constraints_propagate
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace) (ε : ℝ)
    (hε : 0 < ε) (hzero : trajectory 0 = initialState)
    (hevolution : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory (D.vectorField (trajectory t)) t) :
    ∀ t ∈ Set.Ioo (-ε) ε,
      sourcedHamiltonianConstraint
        (D.spatialScalarCurvature (trajectory t))
        (D.extrinsicNormSq (trajectory t))
        (D.energyDensity (trajectory t))
        (inferenceEinsteinCoupling ħ c σ₀)
        (D.extrinsicCurvature (trajectory t))
      ∧ (∀ i,
        D.momentumDivergence (trajectory t) i =
          inferenceEinsteinCoupling ħ c σ₀ *
            D.matterMomentumDensity (trajectory t) i) := by
  intro t ht
  have hw := D.weak_constraints_propagate trajectory ε hε hzero hevolution t ht
  exact ⟨D.sourcedHamiltonianConstraint_of_weak _ hw.1,
    D.sourcedMomentumConstraint_of_weak _ hw.2⟩

noncomputable def toGFreeNonlinearEinsteinCauchyProblem
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) :
    GFreeNonlinearEinsteinCauchyProblem
      (X := ADMMetricMomentumMatterPhaseSpace) (ι := Fin 4)
      ħ c σ₀ initialState where
  vectorField := D.vectorField
  realEinsteinTensor := D.realEinsteinTensor
  entropicCurvature := D.entropicCurvature
  stressEnergy := D.stressEnergy
  entropicStress := D.entropicStress
  lipschitzConstant := D.lipschitzConstant
  vectorField_contDiffAt := D.vectorField_contDiffAt
  vectorField_lipschitz := D.vectorField_lipschitz
  initial_fieldEquation :=
    (D.fieldEquation_iff_weakConstraints initialState).2
      ⟨D.initial_weakHamiltonian, D.initial_weakMomentum⟩
  fieldEquation_propagates := by
    intro trajectory ε hzero hevolution t ht
    have hε : 0 < ε := by
      rcases ht with ⟨htl, htr⟩
      linarith
    exact (D.fieldEquation_iff_weakConstraints (trajectory t)).2
      (D.weak_constraints_propagate trajectory ε
        hε hzero hevolution t ht)

@[zil_level physical_theorem]
theorem exists_local_constrained_evolution
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) :
    ∃ trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace,
      trajectory 0 = initialState ∧
      ∃ ε > 0,
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt trajectory (D.vectorField (trajectory t)) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          D.FieldEquation (trajectory t)
            ∧ sourcedHamiltonianConstraint
              (D.spatialScalarCurvature (trajectory t))
              (D.extrinsicNormSq (trajectory t))
              (D.energyDensity (trajectory t))
              (inferenceEinsteinCoupling ħ c σ₀)
              (D.extrinsicCurvature (trajectory t))
            ∧ (∀ i,
              D.momentumDivergence (trajectory t) i =
                inferenceEinsteinCoupling ħ c σ₀ *
                  D.matterMomentumDensity (trajectory t) i)) := by
  let G := D.toGFreeNonlinearEinsteinCauchyProblem
  obtain ⟨trajectory, hzero, ε, hε, hevolution, hfield⟩ :=
    G.exists_local_evolution
  refine ⟨trajectory, hzero, ε, hε, ?_, ?_⟩
  · simpa [G, toGFreeNonlinearEinsteinCauchyProblem] using hevolution
  · intro t ht
    have hevolutionD :
        ∀ s ∈ Set.Ioo (-ε) ε,
          HasDerivAt trajectory (D.vectorField (trajectory s)) s := by
      simpa [G, toGFreeNonlinearEinsteinCauchyProblem] using hevolution
    have hconstraints :=
      D.adm_constraints_propagate trajectory ε hε hzero hevolutionD t ht
    have hfieldD : D.FieldEquation (trajectory t) := by
      simpa [G, toGFreeNonlinearEinsteinCauchyProblem,
        GFreeNonlinearEinsteinCauchyProblem.FieldEquation, FieldEquation] using
        hfield t ht
    exact ⟨hfieldD, hconstraints⟩

@[zil_level physical_theorem]
theorem local_constrained_evolution_unique
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    {trajectory₁ trajectory₂ : ℝ → ADMMetricMomentumMatterPhaseSpace}
    {ε : ℝ} (hε : 0 < ε)
    (hzero₁ : trajectory₁ 0 = initialState)
    (hzero₂ : trajectory₂ 0 = initialState)
    (hevol₁ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₁ (D.vectorField (trajectory₁ t)) t)
    (hevol₂ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₂ (D.vectorField (trajectory₂ t)) t) :
    Set.EqOn trajectory₁ trajectory₂ (Set.Ioo (-ε) ε) := by
  exact D.toGFreeNonlinearEinsteinCauchyProblem.local_evolution_unique
    hε hzero₁ hzero₂ hevol₁ hevol₂

/-- The entire weak ADM constraint surface is invariant under every global
integral curve of the declared vector field, not only under the trajectory
through the structure's distinguished initial datum. -/
@[zil_level physical_theorem]
theorem constraintSurface_invariant_global
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace)
    (state : ADMMetricMomentumMatterPhaseSpace)
    (hzero : trajectory 0 = state)
    (hstate : state ∈ D.constraintSurface)
    (hevolution : ∀ t,
      HasDerivAt trajectory (D.vectorField (trajectory t)) t) :
    ∀ t, trajectory t ∈ D.constraintSurface := by
  have hresidual :
      ∀ t,
        (D.weakHamiltonianResidual (trajectory t),
          D.weakMomentumResidual (trajectory t)) = 0 := by
    apply zero_of_global_linear_constraint_evolution D.constraintPropagation
      ((fun x => (D.weakHamiltonianResidual x,
        D.weakMomentumResidual x)) ∘ trajectory)
    · change
        (D.weakHamiltonianResidual (trajectory 0),
          D.weakMomentumResidual (trajectory 0)) = 0
      rw [hzero]
      apply Prod.ext
      · exact hstate.1
      · exact hstate.2
    · intro t
      exact D.constraintResidual_hasDerivAt_along trajectory t
        (hevolution t)
  intro t
  have h := hresidual t
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The weak Hamiltonian and momentum constraints propagate for every real
time along a global solution of the concrete ADM evolution equation. -/
@[zil_level physical_theorem]
theorem weak_constraints_propagate_global
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace)
    (hzero : trajectory 0 = initialState)
    (hevolution : ∀ t,
      HasDerivAt trajectory (D.vectorField (trajectory t)) t) :
    ∀ t,
      D.weakHamiltonianResidual (trajectory t) = 0 ∧
        D.weakMomentumResidual (trajectory t) = 0 := by
  exact D.constraintSurface_invariant_global trajectory initialState hzero
    ⟨D.initial_weakHamiltonian, D.initial_weakMomentum⟩ hevolution

/-- The globally Lipschitz ADM vector field already stored in the concrete
Cauchy datum generates an all-real-time development in this Banach carrier.
Consequently the complex Einstein equation and all sourced ADM constraints
hold for every real time. -/
@[zil_level physical_theorem]
theorem exists_global_constrained_evolution
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) :
    ∃ trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace,
      trajectory 0 = initialState ∧
      (∀ t, HasDerivAt trajectory (D.vectorField (trajectory t)) t) ∧
      (∀ t,
        D.FieldEquation (trajectory t)
          ∧ sourcedHamiltonianConstraint
            (D.spatialScalarCurvature (trajectory t))
            (D.extrinsicNormSq (trajectory t))
            (D.energyDensity (trajectory t))
            (inferenceEinsteinCoupling ħ c σ₀)
            (D.extrinsicCurvature (trajectory t))
          ∧ (∀ i,
            D.momentumDivergence (trajectory t) i =
              inferenceEinsteinCoupling ħ c σ₀ *
                D.matterMomentumDensity (trajectory t) i)) := by
  obtain ⟨trajectory, hzero, hevolution⟩ :=
    exists_global_solution_of_lipschitz
      D.vectorField initialState D.lipschitzConstant D.vectorField_lipschitz
  refine ⟨trajectory, hzero, hevolution, ?_⟩
  have hweak :=
    D.weak_constraints_propagate_global trajectory hzero hevolution
  intro t
  have hw := hweak t
  exact ⟨(D.fieldEquation_iff_weakConstraints (trajectory t)).2 hw,
    D.sourcedHamiltonianConstraint_of_weak _ hw.1,
    D.sourcedMomentumConstraint_of_weak _ hw.2⟩

/-- The canonical all-time ADM flow preserves the weak constraint surface. -/
@[zil_level physical_theorem]
theorem globalFlow_preserves_constraintSurface
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    {state : ADMMetricMomentumMatterPhaseSpace}
    (hstate : state ∈ D.constraintSurface) (t : ℝ) :
    D.globalFlow t state ∈ D.constraintSurface := by
  exact D.constraintSurface_invariant_global
    (fun s => D.globalFlow s state) state
    (D.globalFlow_zero state) hstate
    (fun s => D.globalFlow_hasDerivAt state s) t

/-- The fixed-time ADM homeomorphism restricts to a homeomorphism of the
weak constraint surface. -/
noncomputable def constrainedGlobalFlowHomeomorph
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) (t : ℝ) :
    D.constraintSurface ≃ₜ D.constraintSurface where
  toFun state :=
    ⟨D.globalFlow t state, D.globalFlow_preserves_constraintSurface state.2 t⟩
  invFun state :=
    ⟨D.globalFlow (-t) state,
      D.globalFlow_preserves_constraintSurface state.2 (-t)⟩
  left_inv state := by
    apply Subtype.ext
    exact D.globalFlow_neg_apply t state
  right_inv state := by
    apply Subtype.ext
    exact D.globalFlow_apply_neg t state
  continuous_toFun :=
    ((D.globalFlow_lipschitz t).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((D.globalFlow_lipschitz (-t)).continuous.comp continuous_subtype_val).subtype_mk _

/-- Every constrained initial state evolves under the canonical global flow
through states satisfying the complex Einstein equation, the sourced
Hamiltonian constraint, and all three sourced momentum constraints. -/
@[zil_level physical_theorem]
theorem globalFlow_fieldEquation_and_admConstraints
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    {state : ADMMetricMomentumMatterPhaseSpace}
    (hstate : state ∈ D.constraintSurface) (t : ℝ) :
    D.FieldEquation (D.globalFlow t state)
      ∧ sourcedHamiltonianConstraint
        (D.spatialScalarCurvature (D.globalFlow t state))
        (D.extrinsicNormSq (D.globalFlow t state))
        (D.energyDensity (D.globalFlow t state))
        (inferenceEinsteinCoupling ħ c σ₀)
        (D.extrinsicCurvature (D.globalFlow t state))
      ∧ (∀ i,
        D.momentumDivergence (D.globalFlow t state) i =
          inferenceEinsteinCoupling ħ c σ₀ *
            D.matterMomentumDensity (D.globalFlow t state) i) := by
  have hw := D.globalFlow_preserves_constraintSurface hstate t
  exact ⟨(D.fieldEquation_iff_weakConstraints (D.globalFlow t state)).2 hw,
    D.sourcedHamiltonianConstraint_of_weak _ hw.1,
    D.sourcedMomentumConstraint_of_weak _ hw.2⟩

/-- **Global-in-time constrained ADM evolution with finite-time norm
control.**  The canonical trajectory exists for every real time, satisfies
the complex Einstein equation and all sourced ADM constraints, and is
uniformly bounded on every finite time slab by an explicit Grönwall bound.

This rules out finite-time blow-up in the declared completed
metric--momentum--matter phase norm under the global-Lipschitz premise.  It
does not assert curvature-geodesic completeness or singularity avoidance for
arbitrary Einstein data. -/
@[zil_level physical_theorem]
theorem exists_global_constrained_evolution_with_no_finite_norm_blowup
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState) :
    ∃ trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace,
      trajectory 0 = initialState
      ∧ (∀ t,
        HasDerivAt trajectory (D.vectorField (trajectory t)) t)
      ∧ (∀ t,
        D.FieldEquation (trajectory t)
          ∧ sourcedHamiltonianConstraint
            (D.spatialScalarCurvature (trajectory t))
            (D.extrinsicNormSq (trajectory t))
            (D.energyDensity (trajectory t))
            (inferenceEinsteinCoupling ħ c σ₀)
            (D.extrinsicCurvature (trajectory t))
          ∧ (∀ i,
            D.momentumDivergence (trajectory t) i =
              inferenceEinsteinCoupling ħ c σ₀ *
                D.matterMomentumDensity (trajectory t) i))
      ∧ (∀ T : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc (-T) T,
        ‖trajectory t‖ ≤ C) := by
  let trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace :=
    fun t => D.globalFlow t initialState
  refine ⟨trajectory, D.globalFlow_zero initialState, ?_, ?_, ?_⟩
  · intro t
    exact D.globalFlow_hasDerivAt initialState t
  · intro t
    exact D.globalFlow_fieldEquation_and_admConstraints
      ⟨D.initial_weakHamiltonian, D.initial_weakMomentum⟩ t
  · intro T
    refine ⟨gronwallBound ‖initialState‖ (D.lipschitzConstant : ℝ)
      ‖D.vectorField 0‖ T, ?_⟩
    intro t ht
    exact D.globalFlow_norm_le_on_timeSlab T initialState t ht

/-- Global ADM developments with the same initial datum are unique whenever
they solve the declared globally Lipschitz evolution equation. -/
@[zil_level physical_theorem]
theorem global_constrained_evolution_unique
    (D : ConcreteADMGFreeCauchyData ħ c σ₀ initialState)
    {trajectory₁ trajectory₂ : ℝ → ADMMetricMomentumMatterPhaseSpace}
    (hzero₁ : trajectory₁ 0 = initialState)
    (hzero₂ : trajectory₂ 0 = initialState)
    (hevol₁ : ∀ t,
      HasDerivAt trajectory₁ (D.vectorField (trajectory₁ t)) t)
    (hevol₂ : ∀ t,
      HasDerivAt trajectory₂ (D.vectorField (trajectory₂ t)) t) :
    trajectory₁ = trajectory₂ := by
  apply ODE_solution_unique_univ
    (v := fun _ => D.vectorField) (s := fun _ => Set.univ)
    (K := D.lipschitzConstant) (t₀ := 0)
  · intro _
    exact D.vectorField_lipschitz.lipschitzOnWith
  · intro t
    exact ⟨hevol₁ t, Set.mem_univ _⟩
  · intro t
    exact ⟨hevol₂ t, Set.mem_univ _⟩
  · rw [hzero₁, hzero₂]

/- ZIL-BEGIN -/

zil attach zero_of_linear_constraint_evolution where
  formalizes @ "claim:a-bounded-linear-homogeneous-adm-subsidiary-system-with-zero-initial-hamiltonian-and-momentum-residuals-remains-zero-on-the-cauchy-interval",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ODE_solution_unique_of_mem_Ioo",
  caveat @ "scope:the-proof-is-on-the-genuine-continuum-h-minus-one-residual-banach-carrier-the-subsidiary-system-derivative-law-remains-explicit-analytic-data"

zil attach exists_global_solution_of_lipschitz where
  formalizes @ "claim:every-globally-lipschitz-autonomous-vector-field-on-a-complete-real-normed-space-has-a-solution-on-all-real-times",
  epistemic_status @ "risky",
  supported_by @ "lean:IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀",
  supported_by @ "lean:ODE_solution_unique_of_mem_Ioo",
  caveat @ "scope:global-lipschitz-control-on-the-whole-banach-space-is-the-explicit-continuation-hypothesis-and-is-not-derived-for-arbitrary-einstein-initial-data"

zil attach exists_global_solution_of_lipschitz_bounded where
  formalizes @ "claim:a-uniformly-bounded-globally-lipschitz-autonomous-vector-field-on-a-complete-real-normed-space-has-a-solution-on-all-real-times",
  epistemic_status @ "risky",
  supported_by @ "lean:IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀",
  supported_by @ "lean:ODE_solution_unique_of_mem_Ioo",
  caveat @ "compatibility-corollary:the-uniform-bound-is-stronger-than-needed-because-global-lipschitz-control-alone-now-supplies-the-global-solution"

zil attach zero_of_global_linear_constraint_evolution where
  formalizes @ "claim:a-global-bounded-linear-homogeneous-adm-subsidiary-system-with-zero-initial-residual-vanishes-for-all-real-times",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ODE_solution_unique_univ",
  caveat @ "scope:the-global-subsidiary-system-derivative-identity-is-proved-separately-by-the-frechet-chain-rule-from-the-pointwise-adm-tangency-datum"

zil attach ConcreteADMGFreeCauchyData.constraintResidual_hasDerivAt_along where
  formalizes @ "claim:the-frechet-derivative-of-the-continuum-adm-constraint-map-and-pointwise-bianchi-tangency-derive-the-homogeneous-subsidiary-system-along-every-cauchy-trajectory",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:HasFDerivAt.comp_hasDerivAt",
  caveat @ "premise:the-pointwise-frechet-derivative-and-its-value-on-the-adm-vector-field-are-explicit-analytic-data-the-trajectory-level-propagation-law-is-not-assumed"

zil attach ConcreteADMGFreeCauchyData.globalFlow_add where
  formalizes @ "claim:the-globally-lipschitz-continuum-adm-vector-field-generates-an-additive-real-time-flow",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ODE_solution_unique_univ",
  caveat @ "scope:the-flow-is-on-the-declared-gauge-reduced-banach-phase-space-and-does-not-assert-maximal-global-hyperbolicity-of-the-associated-spacetime"

zil attach ConcreteADMGFreeCauchyData.globalFlow_bijective where
  formalizes @ "claim:every-fixed-time-continuum-adm-flow-map-is-bijective-with-negative-time-as-its-two-sided-inverse",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_add",
  caveat @ "scope:reversibility-is-for-the-declared-autonomous-gauge-reduced-flow-and-does-not-remove-the-global-lipschitz-premise"

zil attach ConcreteADMGFreeCauchyData.globalFlow_dist_le where
  formalizes @ "claim:perturbations-of-continuum-adm-initial-data-grow-by-at-most-exp-k-abs-t-under-the-global-flow",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:dist_le_of_trajectories_ODE",
  caveat @ "premise:the-explicit-gronwall-rate-uses-the-declared-global-lipschitz-constant-for-the-full-gauge-reduced-vector-field"

zil attach ConcreteADMGFreeCauchyData.globalFlow_lipschitz where
  formalizes @ "claim:each-fixed-time-continuum-adm-flow-map-is-globally-lipschitz-with-constant-exp-k-abs-t",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_dist_le",
  caveat @ "scope:this-is-continuous-dependence-in-the-completed-banach-phase-metric-not-a-spacetime-curvature-or-geodesic-stability-theorem"

zil attach ConcreteADMGFreeCauchyData.globalFlow_norm_le where
  formalizes @ "claim:the-global-continuum-adm-flow-has-an-explicit-two-sided-gronwall-phase-norm-bound-with-affine-forcing-norm-f-zero",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:dist_le_of_approx_trajectories_ODE",
  caveat @ "premise:the-bound-uses-global-lipschitz-control-on-the-entire-gauge-reduced-banach-phase-space-and-controls-that-phase-norm-not-curvature-invariants"

zil attach ConcreteADMGFreeCauchyData.globalFlow_norm_le_on_timeSlab where
  formalizes @ "claim:every-finite-time-slab-of-the-global-continuum-adm-flow-has-an-explicit-uniform-phase-norm-bound",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:gronwallBound_mono",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_norm_le",
  caveat @ "scope:no-finite-time-blowup-is-in-the-declared-completed-phase-norm-under-the-global-lipschitz-premise"

zil attach ConcreteADMGFreeCauchyData.globalFlowHomeomorph where
  formalizes @ "claim:each-fixed-time-adm-evolution-is-a-homeomorphism-of-the-complete-continuum-phase-space-with-negative-time-inverse",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_bijective",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_lipschitz",
  caveat @ "scope:fixed-time-homeomorphism-on-the-gauge-reduced-banach-carrier-not-yet-a-jointly-continuous-mathlib-flow-or-maximal-spacetime-development"

zil attach ConcreteADMGFreeCauchyData.weak_constraints_propagate where
  formalizes @ "claim:weak-distributional-hamiltonian-and-momentum-constraints-propagate-on-the-continuum-adm-metric-momentum-matter-phase-space",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.zero_of_linear_constraint_evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.constraintResidual_hasDerivAt_along",
  caveat @ "premise:the-bounded-linear-subsidiary-generator-and-pointwise-bianchi-tangency-identity-are-explicit-the-trajectory-law-and-zero-constraint-propagation-are-derived"

zil attach ConcreteADMGFreeCauchyData.adm_constraints_propagate where
  formalizes @ "claim:the-propagated-weak-residuals-imply-lusannas-sourced-adm-hamiltonian-constraint-and-all-three-momentum-constraint-components-at-the-g-free-einstein-coupling",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity.sourcedHamiltonianConstraint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.weak_constraints_propagate",
  caveat @ "premise:the-declared-continuous-probes-identify-the-weak-h-minus-one-residuals-with-the-scalar-and-vector-adm-constraint-values"

zil attach ConcreteADMGFreeCauchyData.exists_local_constrained_evolution where
  formalizes @ "claim:the-repositorys-g-free-nonlinear-einstein-cauchy-problem-is-instantiated-on-the-continuum-adm-metric-momentum-matter-phase-space-and-has-a-local-solution-satisfying-the-complex-field-equation-and-propagated-scalar-vector-constraints",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.adm_constraints_propagate",
  caveat @ "scope:local-banach-space-cauchy-existence-not-a-maximal-globally-hyperbolic-development-global-continuation-or-singularity-control-theorem"

zil attach ConcreteADMGFreeCauchyData.local_constrained_evolution_unique where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique",
  formalizes @ "claim:the-concrete-continuum-adm-cauchy-development-is-unique-on-the-common-local-interval",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique",
  caveat @ "premise:the-gauge-reduced-adm-evolution-vector-field-has-the-declared-global-lipschitz-bound"

zil attach ConcreteADMGFreeCauchyData.weak_constraints_propagate_global where
  formalizes @ "claim:weak-distributional-hamiltonian-and-momentum-constraints-propagate-for-all-real-times-along-a-global-continuum-adm-solution",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.zero_of_global_linear_constraint_evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.constraintResidual_hasDerivAt_along",
  caveat @ "premise:pointwise-bianchi-tangency-is-explicit-the-global-trajectory-law-is-derived-by-chain-rule-and-the-zero-residual-by-ode-uniqueness"

zil attach ConcreteADMGFreeCauchyData.constraintSurface_invariant_global where
  formalizes @ "claim:every-global-integral-curve-starting-on-the-continuum-weak-adm-constraint-surface-remains-on-that-surface-for-all-real-times",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.zero_of_global_linear_constraint_evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.constraintResidual_hasDerivAt_along",
  caveat @ "premise:the-pointwise-bianchi-tangency-and-global-lipschitz-vector-field-are-explicit-the-invariance-theorem-is-not-a-maximal-development-result"

zil attach ConcreteADMGFreeCauchyData.exists_global_constrained_evolution where
  formalizes @ "claim:the-declared-globally-lipschitz-continuum-adm-vector-field-generates-an-all-real-time-development-satisfying-the-complex-einstein-equation-and-propagated-scalar-vector-constraints",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.exists_global_solution_of_lipschitz",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.weak_constraints_propagate_global",
  caveat @ "scope:this-is-genuine-global-in-time-existence-in-the-completed-continuum-carrier-under-the-datums-strong-global-lipschitz-premise-not-a-proof-that-general-einstein-data-avoid-singularities-or-form-a-maximal-globally-hyperbolic-development"

zil attach ConcreteADMGFreeCauchyData.globalFlow_preserves_constraintSurface where
  formalizes @ "claim:the-canonical-all-time-adm-flow-restricts-to-the-continuum-weak-constraint-surface",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_add",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.constraintSurface_invariant_global",
  caveat @ "scope:invariance-is-for-the-declared-gauge-reduced-flow-under-global-lipschitz-and-pointwise-bianchi-tangency-premises"

zil attach ConcreteADMGFreeCauchyData.constrainedGlobalFlowHomeomorph where
  formalizes @ "claim:the-fixed-time-adm-homeomorphism-restricts-to-a-homeomorphism-of-the-continuum-weak-constraint-surface",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlowHomeomorph",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_preserves_constraintSurface",
  caveat @ "premise:the-pointwise-bianchi-tangency-identity-makes-the-constraint-subtype-invariant-in-both-time-directions"

zil attach ConcreteADMGFreeCauchyData.globalFlow_fieldEquation_and_admConstraints where
  formalizes @ "claim:every-constrained-initial-state-under-the-canonical-global-flow-satisfies-the-complex-einstein-equation-the-sourced-hamiltonian-constraint-and-all-three-sourced-momentum-constraints-at-every-real-time",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_preserves_constraintSurface",
  caveat @ "premise:the-field-equation-iff-weak-constraints-and-continuous-probe-identities-are-part-of-the-concrete-datum-the-theorem-does-not-construct-a-maximal-globally-hyperbolic-spacetime"

zil attach ConcreteADMGFreeCauchyData.exists_global_constrained_evolution_with_no_finite_norm_blowup where
  formalizes @ "claim:the-continuum-adm-model-has-an-all-real-time-trajectory-satisfying-the-complex-einstein-equation-all-sourced-adm-constraints-and-an-explicit-uniform-bound-on-every-finite-time-slab",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_fieldEquation_and_admConstraints",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.globalFlow_norm_le_on_timeSlab",
  caveat @ "scope:this-closes-global-in-time-existence-and-finite-time-phase-norm-control-for-the-declared-globally-lipschitz-gauge-reduced-model-not-maximal-global-hyperbolicity-geodesic-completeness-or-singularity-avoidance-for-arbitrary-einstein-data"

zil attach ConcreteADMGFreeCauchyData.global_constrained_evolution_unique where
  formalizes @ "claim:all-real-time-continuum-adm-developments-with-the-same-initial-data-are-unique",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ODE_solution_unique_univ",
  caveat @ "premise:the-gauge-reduced-adm-vector-field-has-the-declared-global-lipschitz-bound"

zil_file_contract physlib.continuumADMConstraintPropagation where
  promises "The public spine contains an actual infinite-dimensional ADM metric-momentum-matter phase space built from the completed Fourier homogeneous-H1 energy carrier, with Hamiltonian and momentum residuals in H-minus-one. The Frechet derivative of the constraint map and its pointwise Bianchi tangency to the ADM vector field derive the bounded homogeneous subsidiary system along every trajectory by the chain rule; ODE uniqueness then propagates zero weak constraints. Continuous probes recover Lusanna's sourced scalar constraint and all momentum components. These results instantiate the G-free nonlinear Einstein Cauchy problem and prove local constrained existence and uniqueness. Global Lipschitz control gives a uniform state-centred Picard lifespan, so compatible local solutions glue to a unique additive real-time flow. Gronwall control bounds perturbation growth by exp(K abs(t)); every fixed-time map is a homeomorphism with negative-time inverse. The entire weak constraint surface is invariant under those homeomorphisms, and every constrained orbit satisfies the complex Einstein equation and all sourced ADM constraints. A second affine Gronwall estimate gives an explicit phase-norm bound on every finite time slab and packages global-in-time constrained evolution with no finite-time blow-up in that norm."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.FourierDotHOneThree",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.FourierDotHMinusOneThree",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity.sourcedHamiltonianConstraint",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution"
  ]
  forbids_substitutes [
    "a-finite-dimensional-matrix-state-relabeled-as-a-continuum-adm-phase-space",
    "copying-fieldEquation_propagates-as-a-premise-instead-of-proving-it-from-the-constraint-subsidiary-system",
    "supplying-a-trajectory-level-constraint-derivative-law-instead-of-deriving-it-from-frechet-chain-rule-and-pointwise-adm-tangency",
    "claiming-maximal-global-hyperbolicity-or-unconditional-singularity-control-from-the-globally-lipschitz-gauge-reduced-continuation-sector",
    "claiming-that-global-hyperbolicity-alone-constructs-maxwell-green-operators-without-the-separate-pde-existence-support-and-uniqueness-theorem"
  ]
  witnessed_by [
    zero_of_linear_constraint_evolution,
    ConcreteADMGFreeCauchyData.constraintResidual_hasDerivAt_along,
    ConcreteADMGFreeCauchyData.globalFlow_add,
    ConcreteADMGFreeCauchyData.globalFlow_bijective,
    ConcreteADMGFreeCauchyData.globalFlow_dist_le,
    ConcreteADMGFreeCauchyData.globalFlow_lipschitz,
    ConcreteADMGFreeCauchyData.globalFlow_norm_le,
    ConcreteADMGFreeCauchyData.globalFlow_norm_le_on_timeSlab,
    ConcreteADMGFreeCauchyData.weak_constraints_propagate,
    ConcreteADMGFreeCauchyData.adm_constraints_propagate,
    ConcreteADMGFreeCauchyData.exists_local_constrained_evolution,
    ConcreteADMGFreeCauchyData.local_constrained_evolution_unique,
    exists_global_solution_of_lipschitz,
    exists_global_solution_of_lipschitz_bounded,
    zero_of_global_linear_constraint_evolution,
    ConcreteADMGFreeCauchyData.constraintSurface_invariant_global,
    ConcreteADMGFreeCauchyData.weak_constraints_propagate_global,
    ConcreteADMGFreeCauchyData.exists_global_constrained_evolution,
    ConcreteADMGFreeCauchyData.globalFlow_preserves_constraintSurface,
    ConcreteADMGFreeCauchyData.globalFlow_fieldEquation_and_admConstraints,
    ConcreteADMGFreeCauchyData.exists_global_constrained_evolution_with_no_finite_norm_blowup,
    ConcreteADMGFreeCauchyData.global_constrained_evolution_unique
  ]

#zil_formalization_lint physlib.continuumADMConstraintPropagation

/- ZIL-END -/

end ConcreteADMGFreeCauchyData

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation

end
