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
public import Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution.AmplitudesHistories2plus1

/-! # SpinNetworkTriangulationEvolution — part `Moves3plus1CausalLinks`. Full docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop

/-! ## Section 4: fixed and varying triangulation histories -/

/-- A history represented only by its step amplitudes.  This is exactly the
level needed for the paper's product-over-time formula. -/
structure AmplitudeHistory (Step : Type*) where
  stepAmplitude : Step -> ℂ

/-- Fixed-triangulation amplitude: product of amplitudes over time steps. -/
noncomputable def fixedTriangulationAmplitude {Step : Type*} [Fintype Step]
    (H : AmplitudeHistory Step) : ℂ :=
  ∏ I : Step, H.stepAmplitude I

@[simp] lemma fixedTriangulationAmplitude_empty {Step : Type*} [Fintype Step]
    [IsEmpty Step] (H : AmplitudeHistory Step) :
    fixedTriangulationAmplitude H = 1 := by
  simp [fixedTriangulationAmplitude]

@[simp] lemma fixedTriangulationAmplitude_unit (H : AmplitudeHistory PUnit) :
    fixedTriangulationAmplitude H = H.stepAmplitude PUnit.unit := by
  simp [fixedTriangulationAmplitude]

/-- Variable-triangulation amplitude: sum over possible spacetime
triangulations/histories. -/
noncomputable def varyingTriangulationAmplitude {Triangulation : Type*}
    [Fintype Triangulation] (amp : Triangulation -> ℂ) : ℂ :=
  ∑ T : Triangulation, amp T

@[simp] lemma varyingTriangulationAmplitude_empty {Triangulation : Type*}
    [Fintype Triangulation] [IsEmpty Triangulation]
    (amp : Triangulation -> ℂ) :
    varyingTriangulationAmplitude amp = 0 := by
  simp [varyingTriangulationAmplitude]

@[simp] lemma varyingTriangulationAmplitude_unit (amp : PUnit -> ℂ) :
    varyingTriangulationAmplitude amp = amp PUnit.unit := by
  simp [varyingTriangulationAmplitude]

/-! ## Section 5: 3+1-dimensional 4-simplex moves -/

set_option backward.isDefEq.respectTransparency false in
/-- The local 3+1-dimensional Pachner moves from a spacetime 4-simplex. -/
inductive Move31 where
  | oneToFour
  | fourToOne
  | twoToThree
  | threeToTwo
deriving DecidableEq, Fintype, Repr

namespace Move31

/-- Number of past tetrahedra in the boundary of the 4-simplex. -/
def pastNodeCount : Move31 -> ℕ
  | oneToFour => 1
  | fourToOne => 4
  | twoToThree => 2
  | threeToTwo => 3

/-- Number of future tetrahedra in the boundary of the 4-simplex. -/
def futureNodeCount : Move31 -> ℕ
  | oneToFour => 4
  | fourToOne => 1
  | twoToThree => 3
  | threeToTwo => 2

/-- Each 3+1 move partitions the five boundary tetrahedra of one 4-simplex. -/
lemma past_add_future_eq_five (m : Move31) :
    m.pastNodeCount + m.futureNodeCount = 5 := by
  cases m <;> rfl

lemma past_positive (m : Move31) : 0 < m.pastNodeCount := by
  cases m <;> decide

lemma future_positive (m : Move31) : 0 < m.futureNodeCount := by
  cases m <;> decide

/-- Node-count change across a local 3+1 move. -/
def nodeCountChange (m : Move31) : ℤ :=
  (m.futureNodeCount : ℤ) - (m.pastNodeCount : ℤ)

@[simp] lemma nodeCountChange_oneToFour : nodeCountChange oneToFour = 3 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

@[simp] lemma nodeCountChange_fourToOne : nodeCountChange fourToOne = -3 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

@[simp] lemma nodeCountChange_twoToThree : nodeCountChange twoToThree = 1 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

@[simp] lemma nodeCountChange_threeToTwo : nodeCountChange threeToTwo = -1 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

/-- If a 3+1 step omits both contracting Pachner moves, every elementary
node-count change is nonnegative. -/
lemma nodeCountChange_nonnegative_without_contractions (m : Move31)
    (h41 : m ≠ fourToOne) (h32 : m ≠ threeToTwo) : 0 ≤ m.nodeCountChange := by
  cases m <;> simp [nodeCountChange, pastNodeCount, futureNodeCount] at h41 h32 ⊢

/-- The `1-4` and `4-1` Pachner moves cancel exactly at node-count level. -/
lemma oneToFour_fourToOne_nodeChange_cancel :
    nodeCountChange oneToFour + nodeCountChange fourToOne = 0 := by
  norm_num

/-- The `2-3` and `3-2` Pachner moves cancel exactly at node-count level. -/
lemma twoToThree_threeToTwo_nodeChange_cancel :
    nodeCountChange twoToThree + nodeCountChange threeToTwo = 0 := by
  norm_num

end Move31

/-- The positive splits of the five boundary tetrahedra of a 4-simplex are
exactly the 3+1 Pachner split counts. -/
lemma positive_split_of_five_tetrahedra {past future : ℕ}
    (h : past + future = 5) (hp : 0 < past) (hf : 0 < future) :
    (past = 1 ∧ future = 4)
      ∨ (past = 2 ∧ future = 3)
      ∨ (past = 3 ∧ future = 2)
      ∨ (past = 4 ∧ future = 1) := by
  omega

/-- A 4-simplex has ten triangular spin-labelled faces and five
intertwiner-labelled boundary tetrahedra, so a local 3+1 amplitude can be
represented as a 15j-type carrier. -/
structure ThreePlusOneAmplitudeData where
  A14 : (Fin 10 -> SpinLabel) -> (Fin 5 -> IntertwinerLabel) -> ℂ
  A41 : (Fin 10 -> SpinLabel) -> (Fin 5 -> IntertwinerLabel) -> ℂ
  A23 : (Fin 10 -> SpinLabel) -> (Fin 5 -> IntertwinerLabel) -> ℂ
  A32 : (Fin 10 -> SpinLabel) -> (Fin 5 -> IntertwinerLabel) -> ℂ

/-- Evaluate the 3+1 local amplitude selected by a Pachner split. -/
noncomputable def localAmplitude31 (A : ThreePlusOneAmplitudeData) :
    Move31 -> (Fin 10 -> SpinLabel) -> (Fin 5 -> IntertwinerLabel) -> ℂ
  | Move31.oneToFour, spins, intertwiners => A.A14 spins intertwiners
  | Move31.fourToOne, spins, intertwiners => A.A41 spins intertwiners
  | Move31.twoToThree, spins, intertwiners => A.A23 spins intertwiners
  | Move31.threeToTwo, spins, intertwiners => A.A32 spins intertwiners

/-- Local normalization sum over the four possible 3+1 Pachner placements for
fixed 4-simplex labels. -/
noncomputable def localAmplitudeNormSqSum31 (A : ThreePlusOneAmplitudeData)
    (spins : Fin 10 -> SpinLabel) (intertwiners : Fin 5 -> IntertwinerLabel) : ℝ :=
  ∑ m : Move31, ‖localAmplitude31 A m spins intertwiners‖ ^ 2

/-- The local 3+1 normalization sum is nonnegative. -/
lemma localAmplitudeNormSqSum31_nonnegative (A : ThreePlusOneAmplitudeData)
    (spins : Fin 10 -> SpinLabel) (intertwiners : Fin 5 -> IntertwinerLabel) :
    0 ≤ localAmplitudeNormSqSum31 A spins intertwiners := by
  classical
  unfold localAmplitudeNormSqSum31
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Predicate for the deferred 15j-type local normalization problem in 3+1. -/
def LocallyNormalized31 (A : ThreePlusOneAmplitudeData) : Prop :=
  ∀ (spins : Fin 10 -> SpinLabel) (intertwiners : Fin 5 -> IntertwinerLabel),
    localAmplitudeNormSqSum31 A spins intertwiners = 1

/-- One 3+1 time step: each site has a 4-simplex Pachner move, ten spin
labels, and five intertwiner labels. -/
structure EvolutionStep31 (Site : Type*) where
  move : Site -> Move31
  spins : Site -> Fin 10 -> SpinLabel
  intertwiners : Site -> Fin 5 -> IntertwinerLabel

/-- Product-over-sites amplitude for one 3+1 time step. -/
noncomputable def stepAmplitude31 {Site : Type*} [Fintype Site]
    (A : ThreePlusOneAmplitudeData) (step : EvolutionStep31 Site) : ℂ :=
  ∏ site : Site, localAmplitude31 A (step.move site) (step.spins site) (step.intertwiners site)

/-- Total node-count change across all local 3+1 Pachner moves of one step. -/
noncomputable def totalNodeCountChange31 {Site : Type*} [Fintype Site]
    (step : EvolutionStep31 Site) : ℤ :=
  ∑ site : Site, (step.move site).nodeCountChange

/-- If a 3+1 step omits both contracting moves at every site, its total
node-count change is nonnegative. -/
lemma totalNodeCountChange31_nonnegative_without_contractions {Site : Type*}
    [Fintype Site] (step : EvolutionStep31 Site)
    (h41 : ∀ site : Site, step.move site ≠ Move31.fourToOne)
    (h32 : ∀ site : Site, step.move site ≠ Move31.threeToTwo) :
    0 ≤ totalNodeCountChange31 step := by
  classical
  unfold totalNodeCountChange31
  exact Finset.sum_nonneg (fun site _ =>
    Move31.nodeCountChange_nonnegative_without_contractions (step.move site) (h41 site) (h32 site))

@[simp] lemma stepAmplitude31_empty {Site : Type*} [Fintype Site] [IsEmpty Site]
    (A : ThreePlusOneAmplitudeData) (step : EvolutionStep31 Site) :
    stepAmplitude31 A step = 1 := by
  simp [stepAmplitude31]

/-! ## Section 6: causal slicing and null-edge duplication -/

/-- Incidence and past/future orientation data for faces of spacetime
simplices. -/
structure SimplexFaceCausality (Simplex Face : Type*) where
  incident : Face -> Simplex -> Prop
  isPast : Face -> Simplex -> Prop
  isFuture : Face -> Simplex -> Prop

/-- A local causal update rule: future labels are functions only of the labels
on the past boundary of the same spacetime simplex. -/
structure LocalCausalUpdate (Past Future : Type*) where
  update : (Past -> SpinLabel) -> Future -> SpinLabel

/-- If two local past boundaries have the same labels, a local causal update
produces the same future label.  This is the formal dependence-only-on-local-
past statement used by the paper. -/
lemma LocalCausalUpdate.ext_of_same_past {Past Future : Type*}
    (U : LocalCausalUpdate Past Future) {oldLabels oldLabels' : Past -> SpinLabel}
    (h : ∀ p : Past, oldLabels p = oldLabels' p) (future : Future) :
    U.update oldLabels future = U.update oldLabels' future := by
  have hfun : oldLabels = oldLabels' := funext h
  rw [hfun]

/-- A spacelike slice does not contain both a past and a future face of the
same spacetime simplex. -/
def SpacelikeSlice {Simplex Face : Type*}
    (C : SimplexFaceCausality Simplex Face) (contains : Face -> Prop) : Prop :=
  ∀ (σ : Simplex) (pastFace futureFace : Face),
    contains pastFace -> contains futureFace ->
      C.isPast pastFace σ -> C.isFuture futureFace σ -> False

/-- A timelike surface contains a past and a future face of the same spacetime
simplex. -/
def TimelikeSurface {Simplex Face : Type*}
    (C : SimplexFaceCausality Simplex Face) (contains : Face -> Prop) : Prop :=
  ∃ (σ : Simplex) (pastFace futureFace : Face),
    contains pastFace ∧ contains futureFace ∧ C.isPast pastFace σ ∧ C.isFuture futureFace σ

/-- Spacelike and timelike, in the above paper sense, are mutually exclusive. -/
lemma spacelike_not_timelike {Simplex Face : Type*}
    (C : SimplexFaceCausality Simplex Face) (contains : Face -> Prop) :
    SpacelikeSlice C contains -> ¬ TimelikeSurface C contains := by
  intro hspace htime
  rcases htime with ⟨σ, pastFace, futureFace, hpast, hfuture, hp, hf⟩
  exact hspace σ pastFace futureFace hpast hfuture hp hf

/-- A varying foliation is represented as a family of slices, each satisfying
the spacelike condition. -/
structure SpacelikeFoliation (Slice Simplex Face : Type*)
    (C : SimplexFaceCausality Simplex Face) where
  contains : Slice -> Face -> Prop
  spacelike : ∀ slice : Slice, SpacelikeSlice C (contains slice)

/-- Every slice in a spacelike foliation excludes the paper's timelike wrapping
condition around a spacetime simplex. -/
lemma SpacelikeFoliation.slice_not_timelike {Slice Simplex Face : Type*}
    {C : SimplexFaceCausality Simplex Face}
    (F : SpacelikeFoliation Slice Simplex Face C) (slice : Slice) :
    ¬ TimelikeSurface C (F.contains slice) :=
  spacelike_not_timelike C (F.contains slice) (F.spacelike slice)

/-- The null-edge labels of the original causal spin-network picture are not
new labels in the dual triangulation; each is copied from a spatial edge. -/
structure NullEdgeDuplication (NullEdge SpatialEdge : Type*) where
  source : NullEdge -> SpatialEdge
  nullSpin : NullEdge -> SpinLabel
  spatialSpin : SpatialEdge -> SpinLabel
  duplicates : ∀ edge : NullEdge, nullSpin edge = spatialSpin (source edge)

lemma nullEdgeSpin_is_spatial {NullEdge SpatialEdge : Type*}
    (D : NullEdgeDuplication NullEdge SpatialEdge) (edge : NullEdge) :
    D.nullSpin edge = D.spatialSpin (D.source edge) :=
  D.duplicates edge

/-- Every null-edge spin label lies in the range of spatial spin labels; null
edges add causal bookkeeping, not new independent spin labels. -/
lemma nullEdgeSpin_has_spatial_source {NullEdge SpatialEdge : Type*}
    (D : NullEdgeDuplication NullEdge SpatialEdge) (edge : NullEdge) :
    ∃ spatial : SpatialEdge, D.nullSpin edge = D.spatialSpin spatial :=
  ⟨D.source edge, D.duplicates edge⟩

/-! ## Section 7: links to existing physlib carriers -/

/-- The SU(2) spin labels used in spin networks are compatible with the
existing physlib spin-half double-cover theorem. -/
lemma spinNetwork_su2_spinHalf_doubleCover
    (X : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    Hopf.SpinHalfDoubleCover.spinHalfRotation (2 * Real.pi) = -1
      ∧ Hopf.SpinHalfDoubleCover.spinHalfRotation (4 * Real.pi) = 1
      ∧ Hopf.SpinHalfDoubleCover.spinHalfRotation (θ + 2 * Real.pi)
          * X * Hopf.SpinHalfDoubleCover.spinHalfRotation (θ + 2 * Real.pi)
        = Hopf.SpinHalfDoubleCover.spinHalfRotation θ * X * Hopf.SpinHalfDoubleCover.spinHalfRotation θ :=
  Hopf.SpinHalfDoubleCover.spin_half_double_cover X θ

/-- Local spin-network update projectors can reuse the existing weak-Hopf
tensor-network algebra: two commuting idempotent site projectors multiply to
an idempotent update projector. -/
lemma spinNetwork_siteProjectors_idempotent {A : Type*} [Monoid A] {p q : A}
    (hp : AlgebraicQFT.WeakHopfTensorNetworkHaagDuality.IsIdempotent p)
    (hq : AlgebraicQFT.WeakHopfTensorNetworkHaagDuality.IsIdempotent q)
    (hpq : AlgebraicQFT.WeakHopfTensorNetworkHaagDuality.Commute p q) :
    AlgebraicQFT.WeakHopfTensorNetworkHaagDuality.IsIdempotent (p * q) :=
  mul_idempotent_of_commuting_idempotents hp hq hpq

/-- Wilson-loop/Hopf fusion is available as the algebraic charge-composition
carrier for spin-network labels when they are specialized to a finite charge
lattice. -/
lemma spinNetwork_labels_reuse_hopf_wilson_fusion
    (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    Hopf.ChargeConjugationRibbonTwist.chargeState (a.val : ℤ)
        * Hopf.ChargeConjugationRibbonTwist.chargeState (b.val : ℤ)
        = Hopf.ChargeConjugationRibbonTwist.chargeState ((a.val : ℤ) + (b.val : ℤ))
      ∧ ChernSimons.VerlindeConvolution.cswConvolution (Pi.single a 1) (Pi.single b (1 : ℂ))
        = Pi.single (a + b) 1 :=
  hopf_charge_addition_matches_wilson_fusion k hk a b


end Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
