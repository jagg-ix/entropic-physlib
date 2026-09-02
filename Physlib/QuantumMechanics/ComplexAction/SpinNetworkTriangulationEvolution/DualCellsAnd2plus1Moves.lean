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

/-! # SpinNetworkTriangulationEvolution — part `DualCellsAnd2plus1Moves`. Full docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop

/-! ## Section 1: dual dictionary -/

/-- Spin-network edge labels in the paper: irreducible SU(2) spin labels,
represented here by their nonnegative integer label carrier. -/
abbrev SpinLabel := ℕ

/-- A finite name for an intertwiner label at a spin-network node. -/
structure IntertwinerLabel where
  id : ℕ
deriving DecidableEq, Repr

/-- The two spatial dimensions treated explicitly in the paper. -/
inductive SpatialDimension where
  /-- 2-dimensional space, 2+1-dimensional spacetime. -/
  | two
  /-- 3-dimensional space, 3+1-dimensional spacetime. -/
  | three
deriving DecidableEq, Repr

namespace SpatialDimension

/-- Spin-network node valence dual to a spatial simplex. -/
def nodeValence : SpatialDimension -> ℕ
  | two => 3
  | three => 4

/-- Number of codimension-one boundary simplices of a spatial simplex:
three sides for a triangle, four faces for a tetrahedron. -/
def spatialBoundaryCount : SpatialDimension -> ℕ
  | two => 3
  | three => 4

/-- Number of boundary spatial simplices of one spacetime simplex:
four triangle faces for a tetrahedron in 2+1, five tetrahedral faces for a
4-simplex in 3+1. -/
def spacetimeBoundaryCount : SpatialDimension -> ℕ
  | two => 4
  | three => 5

/-- The spin-network valence equals the number of boundary faces of the dual
spatial simplex. -/
lemma nodeValence_eq_spatialBoundaryCount (d : SpatialDimension) :
    d.nodeValence = d.spatialBoundaryCount := by
  cases d <;> rfl

@[simp] lemma nodeValence_two : nodeValence two = 3 := rfl
@[simp] lemma nodeValence_three : nodeValence three = 4 := rfl
@[simp] lemma spacetimeBoundaryCount_two : spacetimeBoundaryCount two = 4 := rfl
@[simp] lemma spacetimeBoundaryCount_three : spacetimeBoundaryCount three = 5 := rfl

end SpatialDimension

/-- A finite spin network skeleton with a fixed valence.  This is deliberately
minimal: the paper's checked claims use only node/edge finiteness, valence,
edge spin labels, and node intertwiners. -/
structure SpinNetworkSkeleton where
  nodeCount : ℕ
  edgeCount : ℕ
  valence : ℕ
  edgeSpin : Fin edgeCount -> SpinLabel
  nodeIntertwiner : Fin nodeCount -> IntertwinerLabel

/-- A skeleton is dual to a 2-dimensional spatial triangulation exactly when
its nodes are trivalent. -/
def IsDualToTwoDimensionalTriangulation (Γ : SpinNetworkSkeleton) : Prop :=
  Γ.valence = SpatialDimension.nodeValence SpatialDimension.two

/-- A skeleton is dual to a 3-dimensional spatial triangulation exactly when
its nodes are four-valent. -/
def IsDualToThreeDimensionalTriangulation (Γ : SpinNetworkSkeleton) : Prop :=
  Γ.valence = SpatialDimension.nodeValence SpatialDimension.three

lemma dual_two_dimensional_iff_trivalent (Γ : SpinNetworkSkeleton) :
    IsDualToTwoDimensionalTriangulation Γ ↔ Γ.valence = 3 := by
  rfl

lemma dual_three_dimensional_iff_fourValent (Γ : SpinNetworkSkeleton) :
    IsDualToThreeDimensionalTriangulation Γ ↔ Γ.valence = 4 := by
  rfl

/-! ## Section 1A: labelled dual cells -/

/-- The elementary spin-network cells used by the dual dictionary. -/
inductive SpinNetworkCell where
  | node
  | edge
deriving DecidableEq, Repr

/-- The elementary spatial cells dual to nodes and edges in the two dimensions
treated by the paper. -/
inductive SpatialDualCell where
  | triangle
  | triangleSide
  | tetrahedron
  | tetrahedronFace
deriving DecidableEq, Repr

/-- The paper's cell-level duality: in 2D, nodes are triangles and edges are
triangle sides; in 3D, nodes are tetrahedra and edges are tetrahedron faces. -/
def dualCell : SpatialDimension -> SpinNetworkCell -> SpatialDualCell
  | SpatialDimension.two, SpinNetworkCell.node => SpatialDualCell.triangle
  | SpatialDimension.two, SpinNetworkCell.edge => SpatialDualCell.triangleSide
  | SpatialDimension.three, SpinNetworkCell.node => SpatialDualCell.tetrahedron
  | SpatialDimension.three, SpinNetworkCell.edge => SpatialDualCell.tetrahedronFace

@[simp] lemma dualCell_two_node :
    dualCell SpatialDimension.two SpinNetworkCell.node = SpatialDualCell.triangle := rfl

@[simp] lemma dualCell_two_edge :
    dualCell SpatialDimension.two SpinNetworkCell.edge = SpatialDualCell.triangleSide := rfl

@[simp] lemma dualCell_three_node :
    dualCell SpatialDimension.three SpinNetworkCell.node = SpatialDualCell.tetrahedron := rfl

@[simp] lemma dualCell_three_edge :
    dualCell SpatialDimension.three SpinNetworkCell.edge = SpatialDualCell.tetrahedronFace := rfl

/-- Number of spin-labelled boundary cells of a spatial simplex: three sides of
a triangle, four faces of a tetrahedron. -/
def spatialSpinLabelCount : SpatialDimension -> ℕ
  | SpatialDimension.two => 3
  | SpatialDimension.three => 4

/-- Number of nontrivial intertwiner labels on one spatial simplex in this
paper's SU(2) convention: the triangle face label is omitted, while a 3D
tetrahedron carries one intertwiner. -/
def nontrivialSpatialIntertwinerCount : SpatialDimension -> ℕ
  | SpatialDimension.two => 0
  | SpatialDimension.three => 1

@[simp] lemma twoDimensional_su2_intertwiner_omitted :
    nontrivialSpatialIntertwinerCount SpatialDimension.two = 0 := rfl

@[simp] lemma threeDimensional_tetrahedron_has_one_intertwiner :
    nontrivialSpatialIntertwinerCount SpatialDimension.three = 1 := rfl

/-- A 2D spatial simplex has exactly the three spin labels of a trivalent node
and no nontrivial SU(2) intertwiner label in this convention. -/
lemma twoDimensional_simplex_label_counts :
    spatialSpinLabelCount SpatialDimension.two = 3
      ∧ nontrivialSpatialIntertwinerCount SpatialDimension.two = 0 := by
  simp [spatialSpinLabelCount]

set_option backward.isDefEq.respectTransparency false in
/-- A 3D spatial simplex has four spin-labelled faces and one intertwiner
label, matching a four-valent spin-network node. -/
lemma threeDimensional_simplex_label_counts :
    spatialSpinLabelCount SpatialDimension.three = 4
      ∧ nontrivialSpatialIntertwinerCount SpatialDimension.three = 1 := by
  simp [spatialSpinLabelCount]

/-! ## Section 2: 2+1-dimensional tetrahedron moves -/

set_option backward.isDefEq.respectTransparency false in
/-- The local 2+1-dimensional moves obtained by placing a spacetime
tetrahedron on a trivalent spin network.  The two `2-2` constructors encode
the two recoupling orientations denoted `P` and `P'` in the paper. -/
inductive Move21 where
  | oneToThree
  | threeToOne
  | twoToTwo
  | twoToTwoPrime
deriving DecidableEq, Fintype, Repr

namespace Move21

/-- Number of past spin-network nodes/faces in the local tetrahedron move. -/
def pastNodeCount : Move21 -> ℕ
  | oneToThree => 1
  | threeToOne => 3
  | twoToTwo => 2
  | twoToTwoPrime => 2

/-- Number of future spin-network nodes/faces in the local tetrahedron move. -/
def futureNodeCount : Move21 -> ℕ
  | oneToThree => 3
  | threeToOne => 1
  | twoToTwo => 2
  | twoToTwoPrime => 2

/-- Each 2+1 move partitions the four triangular faces of one spacetime
tetrahedron into past and future faces. -/
lemma past_add_future_eq_four (m : Move21) :
    m.pastNodeCount + m.futureNodeCount = 4 := by
  cases m <;> rfl

/-- Past and future sides are both nonempty: no local move is all-past or
all-future. -/
lemma past_positive (m : Move21) : 0 < m.pastNodeCount := by
  cases m <;> decide

lemma future_positive (m : Move21) : 0 < m.futureNodeCount := by
  cases m <;> decide

/-- The node-count change across a local 2+1 move. -/
def nodeCountChange (m : Move21) : ℤ :=
  (m.futureNodeCount : ℤ) - (m.pastNodeCount : ℤ)

@[simp] lemma nodeCountChange_oneToThree : nodeCountChange oneToThree = 2 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

@[simp] lemma nodeCountChange_threeToOne : nodeCountChange threeToOne = -2 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

@[simp] lemma nodeCountChange_twoToTwo : nodeCountChange twoToTwo = 0 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

@[simp] lemma nodeCountChange_twoToTwoPrime : nodeCountChange twoToTwoPrime = 0 := by
  norm_num [nodeCountChange, pastNodeCount, futureNodeCount]

/-- Omitting the `3-1` move leaves no negative elementary node-count change;
this is the formal version of the growth issue discussed in Section 4. -/
lemma nodeCountChange_nonnegative_without_threeToOne (m : Move21)
    (h : m ≠ threeToOne) : 0 ≤ m.nodeCountChange := by
  cases m <;> simp [nodeCountChange, pastNodeCount, futureNodeCount] at h ⊢

/-- The missing `3-1` move is exactly the elementary contraction by two nodes. -/
lemma threeToOne_is_negative_growth : nodeCountChange threeToOne < 0 := by
  norm_num

/-- The `1-3` move is exactly the elementary expansion by two nodes. -/
lemma oneToThree_is_positive_growth : 0 < nodeCountChange oneToThree := by
  norm_num

end Move21

/-- The positive splits of the four faces of a tetrahedron are exactly
`1+3`, `2+2`, and `3+1`. -/
lemma positive_split_of_four_faces {past future : ℕ}
    (h : past + future = 4) (hp : 0 < past) (hf : 0 < future) :
    (past = 1 ∧ future = 3)
      ∨ (past = 2 ∧ future = 2)
      ∨ (past = 3 ∧ future = 1) := by
  omega

/-- Conversely, every 2+1 move realizes one of the positive splits of four
tetrahedron faces. -/
lemma move21_realizes_positive_split (m : Move21) :
    (m.pastNodeCount = 1 ∧ m.futureNodeCount = 3)
      ∨ (m.pastNodeCount = 2 ∧ m.futureNodeCount = 2)
      ∨ (m.pastNodeCount = 3 ∧ m.futureNodeCount = 1) := by
  cases m <;> simp [Move21.pastNodeCount, Move21.futureNodeCount]


end Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
