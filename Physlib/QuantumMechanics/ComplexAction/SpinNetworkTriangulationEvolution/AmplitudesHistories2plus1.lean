/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
public import Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution.DualCellsAnd2plus1Moves

/-! # SpinNetworkTriangulationEvolution — part `AmplitudesHistories2plus1`. Full docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop

/-! ## Section 3: local amplitudes and histories in 2+1 -/

/-- The four local amplitude functions denoted `J`, `J'`, `P`, and `P'` in
the paper.  A spacetime tetrahedron has six spin labels. -/
structure TwoPlusOneAmplitudeData where
  J : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ
  J' : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ
  P : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ
  P' : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ

/-- Evaluate the local 2+1 amplitude selected by a move. -/
noncomputable def localAmplitude21 (A : TwoPlusOneAmplitudeData) :
    Move21 -> (Fin 6 -> SpinLabel) -> ℂ
  | Move21.oneToThree, ℓ => A.J (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)
  | Move21.threeToOne, ℓ => A.J' (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)
  | Move21.twoToTwo, ℓ => A.P (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)
  | Move21.twoToTwoPrime, ℓ => A.P' (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)

/-! ### Directed amplitude symmetries -/

/-- Labels for a directed `1-3` or `3-1` tetrahedron amplitude, separated
into future/new and past/old triples.  Keeping the triples as separate fields
prevents the Regge-Ponzano full tetrahedral symmetry from being assumed. -/
structure Split13Labels where
  newLabel : Fin 3 -> SpinLabel
  oldLabel : Fin 3 -> SpinLabel

/-- Allowed directed symmetry for `J` and `J'`: permute the new triple and
the old triple independently, without mixing future and past labels. -/
def permuteSplit13Labels (σ τ : Equiv.Perm (Fin 3)) (L : Split13Labels) : Split13Labels where
  newLabel i := L.newLabel (σ i)
  oldLabel i := L.oldLabel (τ i)

@[simp] lemma permuteSplit13Labels_refl (L : Split13Labels) :
    permuteSplit13Labels 1 1 L = L := by
  cases L
  rfl

/-- A `1-3`/`3-1` amplitude has exactly the directed split symmetry proposed
in the paper when it is invariant under independent permutations of the new
and old triples. -/
def DirectedSplitSymmetric (F : Split13Labels -> ℂ) : Prop :=
  ∀ (σ τ : Equiv.Perm (Fin 3)) (L : Split13Labels),
    F (permuteSplit13Labels σ τ L) = F L

/-- Labels for a directed `2-2` recoupling amplitude `P(m; i j k l; n)`:
the new internal edge, the four unchanged outside labels, and the old internal
edge are kept in separate slots. -/
structure Recoupling22Labels where
  newEdge : SpinLabel
  outerLabel : Fin 4 -> SpinLabel
  oldEdge : SpinLabel

/-- Allowed directed symmetry for `P` and `P'`: permute only the four outside
labels, leaving the old and new internal edges distinguished. -/
def permuteRecoupling22Labels (σ : Equiv.Perm (Fin 4))
    (L : Recoupling22Labels) : Recoupling22Labels where
  newEdge := L.newEdge
  outerLabel i := L.outerLabel (σ i)
  oldEdge := L.oldEdge

@[simp] lemma permuteRecoupling22Labels_refl (L : Recoupling22Labels) :
    permuteRecoupling22Labels 1 L = L := by
  cases L
  rfl

/-- A `2-2` amplitude has the directed recoupling symmetry proposed in the
paper when only the four unchanged outside labels may be permuted. -/
def DirectedRecouplingSymmetric (F : Recoupling22Labels -> ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (L : Recoupling22Labels),
    F (permuteRecoupling22Labels σ L) = F L

namespace TwoPlusOneAmplitudeData

/-- A 2+1 amplitude package in which the two `2-2` recoupling orientations are
assigned the same weight, as suggested in the paper before the amplitudes are
otherwise left unresolved. -/
noncomputable def withEqualRecouplings
    (J Jinv P : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ) :
    TwoPlusOneAmplitudeData where
  J := J
  J' := Jinv
  P := P
  P' := P

end TwoPlusOneAmplitudeData

/-- The two `2-2` recoupling moves have the same local weight for the explicit
equal-recouping constructor. -/
@[simp] lemma withEqualRecouplings_sameWeight
    (J Jinv P : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ)
    (ℓ : Fin 6 -> SpinLabel) :
    localAmplitude21 (TwoPlusOneAmplitudeData.withEqualRecouplings J Jinv P)
        Move21.twoToTwo ℓ
      = localAmplitude21 (TwoPlusOneAmplitudeData.withEqualRecouplings J Jinv P)
        Move21.twoToTwoPrime ℓ := by
  rfl

/-- Predicate form of the paper's equal-weight condition for the two `2-2`
recoupling orientations. -/
def RecouplingsSameWeight (A : TwoPlusOneAmplitudeData) : Prop :=
  ∀ ℓ : Fin 6 -> SpinLabel,
    localAmplitude21 A Move21.twoToTwo ℓ = localAmplitude21 A Move21.twoToTwoPrime ℓ

/-- The explicit equal-recouping constructor satisfies the predicate form. -/
lemma withEqualRecouplings_has_sameWeight
    (J Jinv P : SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> SpinLabel -> ℂ) :
    RecouplingsSameWeight (TwoPlusOneAmplitudeData.withEqualRecouplings J Jinv P) := by
  intro ℓ
  simp

/-- Local normalization sum over the four possible 2+1 placements for fixed
local spin labels.  The paper flags normalization as a later analytic task;
this definition isolates the finite algebraic quantity that must be controlled. -/
noncomputable def localAmplitudeNormSqSum21 (A : TwoPlusOneAmplitudeData)
    (ℓ : Fin 6 -> SpinLabel) : ℝ :=
  ∑ m : Move21, ‖localAmplitude21 A m ℓ‖ ^ 2

/-- The local 2+1 normalization sum is nonnegative, independent of any choice
of analytic amplitudes. -/
lemma localAmplitudeNormSqSum21_nonnegative (A : TwoPlusOneAmplitudeData)
    (ℓ : Fin 6 -> SpinLabel) :
    0 ≤ localAmplitudeNormSqSum21 A ℓ := by
  classical
  unfold localAmplitudeNormSqSum21
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Predicate for the paper's deferred local normalization problem. -/
def LocallyNormalized21 (A : TwoPlusOneAmplitudeData) : Prop :=
  ∀ ℓ : Fin 6 -> SpinLabel, localAmplitudeNormSqSum21 A ℓ = 1

/-- One time step: each site has a local move and six local spin labels. -/
structure EvolutionStep21 (Site : Type*) where
  move : Site -> Move21
  labels : Site -> Fin 6 -> SpinLabel

/-- Markopoulou's one-step amplitude: product of local amplitudes over sites
in the triangulation dual to the initial spin network. -/
noncomputable def stepAmplitude21 {Site : Type*} [Fintype Site]
    (A : TwoPlusOneAmplitudeData) (step : EvolutionStep21 Site) : ℂ :=
  ∏ site : Site, localAmplitude21 A (step.move site) (step.labels site)

/-- Total node-count change across all active local moves of one 2+1 step. -/
noncomputable def totalNodeCountChange21 {Site : Type*} [Fintype Site]
    (step : EvolutionStep21 Site) : ℤ :=
  ∑ site : Site, (step.move site).nodeCountChange

/-- If a whole 2+1 step omits the `3-1` contraction at every site, the total
node-count change cannot be negative. -/
lemma totalNodeCountChange21_nonnegative_without_threeToOne {Site : Type*}
    [Fintype Site] (step : EvolutionStep21 Site)
    (h : ∀ site : Site, step.move site ≠ Move21.threeToOne) :
    0 ≤ totalNodeCountChange21 step := by
  classical
  unfold totalNodeCountChange21
  exact Finset.sum_nonneg (fun site _ =>
    Move21.nodeCountChange_nonnegative_without_threeToOne (step.move site) (h site))

/-- One `1-3` expansion and one `3-1` contraction cancel exactly at the level
of node-count change. -/
lemma oneToThree_threeToOne_nodeChange_cancel :
    Move21.nodeCountChange Move21.oneToThree + Move21.nodeCountChange Move21.threeToOne = 0 := by
  norm_num

@[simp] lemma stepAmplitude21_empty {Site : Type*} [Fintype Site] [IsEmpty Site]
    (A : TwoPlusOneAmplitudeData) (step : EvolutionStep21 Site) :
    stepAmplitude21 A step = 1 := by
  simp [stepAmplitude21]

@[simp] lemma stepAmplitude21_unit (A : TwoPlusOneAmplitudeData)
    (step : EvolutionStep21 PUnit) :
    stepAmplitude21 A step =
      localAmplitude21 A (step.move PUnit.unit) (step.labels PUnit.unit) := by
  simp [stepAmplitude21]

/-- Active sites for non-maximal/multifingered evolution. -/
structure SiteActivation (Site : Type*) where
  active : Site -> Bool

/-- Maximal evolution: every site of the current triangulation is updated. -/
def IsMaximalEvolution {Site : Type*} (act : SiteActivation Site) : Prop :=
  ∀ site : Site, act.active site = true

/-- Non-maximal evolution: at least one site is not updated in this time step. -/
def IsNonMaximalEvolution {Site : Type*} (act : SiteActivation Site) : Prop :=
  ∃ site : Site, act.active site = false

/-- The all-active activation pattern. -/
def fullActivation (Site : Type*) : SiteActivation Site where
  active _ := true

@[simp] lemma fullActivation_isMaximal (Site : Type*) :
    IsMaximalEvolution (fullActivation Site) := by
  intro site
  rfl

/-- A maximal evolution pattern is not non-maximal. -/
lemma not_nonMaximal_of_maximal {Site : Type*} (act : SiteActivation Site) :
    IsMaximalEvolution act -> ¬ IsNonMaximalEvolution act := by
  intro hmax hnon
  rcases hnon with ⟨site, hsite⟩
  rw [hmax site] at hsite
  exact Bool.false_ne_true hsite.symm

/-- Non-maximality is exactly failure of maximality for Boolean site
activation. -/
lemma nonMaximal_iff_not_maximal {Site : Type*} (act : SiteActivation Site) :
    IsNonMaximalEvolution act ↔ ¬ IsMaximalEvolution act := by
  constructor
  · intro hnon hmax
    exact not_nonMaximal_of_maximal act hmax hnon
  · intro hnot
    by_contra hnone
    apply hnot
    intro site
    cases hsite : act.active site with
    | false =>
        exfalso
        exact hnone ⟨site, hsite⟩
    | true => rfl

/-- Non-maximal one-step amplitude: product only over active sites. -/
noncomputable def partialStepAmplitude21 {Site : Type*} [Fintype Site]
    (A : TwoPlusOneAmplitudeData) (step : EvolutionStep21 Site)
    (act : SiteActivation Site) : ℂ :=
  ∏ site : Site,
    if act.active site = true then localAmplitude21 A (step.move site) (step.labels site) else 1

/-- The non-maximal product specializes to the full site product for maximal
all-active evolution. -/
@[simp] lemma partialStepAmplitude21_fullActivation {Site : Type*} [Fintype Site]
    (A : TwoPlusOneAmplitudeData) (step : EvolutionStep21 Site) :
    partialStepAmplitude21 A step (fullActivation Site) = stepAmplitude21 A step := by
  classical
  simp [partialStepAmplitude21, stepAmplitude21, fullActivation]

/-- If no site is active, the non-maximal evolution step is the empty product. -/
@[simp] lemma partialStepAmplitude21_noActive {Site : Type*} [Fintype Site]
    (A : TwoPlusOneAmplitudeData) (step : EvolutionStep21 Site)
    (act : SiteActivation Site) (h : ∀ site : Site, act.active site = false) :
    partialStepAmplitude21 A step act = 1 := by
  classical
  simp [partialStepAmplitude21, h]

/-! ### Directed-percolation control layer -/

/-- The percolation-node probabilities described in Section 4: two symmetric
single-arrow cases with weight `p1`, one two-arrow case with weight `p2`, and
one no-arrow case with weight `p3`, normalized by `2*p1 + p2 + p3 = 1`. -/
structure DirectedPercolationNodeWeights where
  p1 : ℝ
  p2 : ℝ
  p3 : ℝ
  p1_nonneg : 0 ≤ p1
  p2_nonneg : 0 ≤ p2
  p3_nonneg : 0 ≤ p3
  total : 2 * p1 + p2 + p3 = 1

namespace DirectedPercolationNodeWeights

/-- The four configuration probabilities add to one. -/
lemma fourConfiguration_total (W : DirectedPercolationNodeWeights) :
    W.p1 + W.p1 + W.p2 + W.p3 = 1 := by
  linarith [W.total]

/-- The two single-arrow configurations together have probability `2*p1`. -/
lemma two_singleArrow_total (W : DirectedPercolationNodeWeights) :
    W.p1 + W.p1 = 2 * W.p1 := by
  ring

/-- The probability of turning on at least one arrow is `2*p1 + p2`. -/
def atLeastOneArrow (W : DirectedPercolationNodeWeights) : ℝ :=
  2 * W.p1 + W.p2

/-- The probability of at least one arrow is nonnegative. -/
lemma atLeastOneArrow_nonnegative (W : DirectedPercolationNodeWeights) :
    0 ≤ W.atLeastOneArrow := by
  unfold atLeastOneArrow
  nlinarith [W.p1_nonneg, W.p2_nonneg]

/-- The probability of at least one arrow is bounded above by one. -/
lemma atLeastOneArrow_le_one (W : DirectedPercolationNodeWeights) :
    W.atLeastOneArrow ≤ 1 := by
  unfold atLeastOneArrow
  linarith [W.total, W.p3_nonneg]

end DirectedPercolationNodeWeights


end Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
