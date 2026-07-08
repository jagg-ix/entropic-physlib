/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
public import Physlib.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
public import Physlib.QFT.PerturbationTheory.Koszul.KoszulSignInsert

/-!
# Tensor networks for complex quantum systems

This file formalizes the repository-facing content of

* R. Orus, *Tensor networks for complex quantum systems*, Nat. Rev. Phys. 1,
  538-550 (2019), arXiv:1812.04011v2.

The paper is a review, so the formalization separates three layers:

* checked taxonomy for the tensor-network families listed in Table I;
* checked cost and bond-dimension consequences that can be stated algebraically;
* a precise interface from MPO-injective/topological PEPS data to the existing
  weak-Hopf tensor-network Haag-duality bridge.

Analytic inputs such as the existence of a concrete PEPS contraction scheme, a
parent Hamiltonian, or local topological order remain named fields in the imported
weak-Hopf package.  No new axioms are introduced here.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.TwoDimensionalSpinHaagDuality
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open FieldStatistic
open scoped FieldStatistic

/-! ## Network families and Table-I structural data -/

/-- Tensor-network families emphasized in the review. -/
inductive TensorNetworkKind where
  | MPS
  | PEPS2D
  | TTN
  | MERA1D
  | BranchingMERA1D
  | MPO
  | PEPO2D
  | MPDO
  | ContinuousMPS
  | ContinuousMERA
  | ContinuousPEPS
  deriving DecidableEq, Repr

/-- Entanglement-entropy growth class used in the review table. -/
inductive EntropyScaling where
  | constant
  | logarithmic
  | boundaryLinear
  | volumeLinear
  | modelDependent
  deriving DecidableEq, Repr

/-- Whether local expectation values are evaluated exactly or through a contraction
approximation at the level of the review's structural table. -/
inductive ExpectationEvaluation where
  | exact
  | approximate
  | modelDependent
  deriving DecidableEq, Repr

/-- Correlation-length status in the review's coarse classification. -/
inductive CorrelationLengthClass where
  | finite
  | canBeInfinite
  | modelDependent
  deriving DecidableEq, Repr

/-- Local tensor constraints used by common ansatz families. -/
inductive TensorConstraint where
  | arbitrary
  | unitaryOrIsometric
  | positiveByConstruction
  | modelDependent
  deriving DecidableEq, Repr

/-- Canonical-form status for the network family.  Loop-free networks admit the
standard sequential-SVD canonical form; loopy PEPS-type networks do not have an
exact general canonical form. -/
inductive CanonicalFormStatus where
  | available
  | openBoundaryOrInfiniteOnly
  | unavailableForLoops
  | notApplicable
  deriving DecidableEq, Repr

/-- Checked profile corresponding to the qualitative entries in the review. -/
structure TensorNetworkProfile where
  spatialDimension : Nat
  entropyScaling : EntropyScaling
  expectationEvaluation : ExpectationEvaluation
  correlationLength : CorrelationLengthClass
  tensorConstraint : TensorConstraint
  canonicalForm : CanonicalFormStatus
  deriving Repr

/-- Table-I-style profile for the basic tensor-network families. -/
def tensorNetworkProfile : TensorNetworkKind -> TensorNetworkProfile
  | .MPS =>
      { spatialDimension := 1
        entropyScaling := .constant
        expectationEvaluation := .exact
        correlationLength := .finite
        tensorConstraint := .arbitrary
        canonicalForm := .openBoundaryOrInfiniteOnly }
  | .PEPS2D =>
      { spatialDimension := 2
        entropyScaling := .boundaryLinear
        expectationEvaluation := .approximate
        correlationLength := .canBeInfinite
        tensorConstraint := .arbitrary
        canonicalForm := .unavailableForLoops }
  | .TTN =>
      { spatialDimension := 1
        entropyScaling := .constant
        expectationEvaluation := .exact
        correlationLength := .finite
        tensorConstraint := .arbitrary
        canonicalForm := .available }
  | .MERA1D =>
      { spatialDimension := 1
        entropyScaling := .logarithmic
        expectationEvaluation := .exact
        correlationLength := .canBeInfinite
        tensorConstraint := .unitaryOrIsometric
        canonicalForm := .unavailableForLoops }
  | .BranchingMERA1D =>
      { spatialDimension := 1
        entropyScaling := .volumeLinear
        expectationEvaluation := .exact
        correlationLength := .canBeInfinite
        tensorConstraint := .unitaryOrIsometric
        canonicalForm := .unavailableForLoops }
  | .MPO =>
      { spatialDimension := 1
        entropyScaling := .modelDependent
        expectationEvaluation := .exact
        correlationLength := .modelDependent
        tensorConstraint := .arbitrary
        canonicalForm := .openBoundaryOrInfiniteOnly }
  | .PEPO2D =>
      { spatialDimension := 2
        entropyScaling := .modelDependent
        expectationEvaluation := .approximate
        correlationLength := .modelDependent
        tensorConstraint := .arbitrary
        canonicalForm := .unavailableForLoops }
  | .MPDO =>
      { spatialDimension := 1
        entropyScaling := .modelDependent
        expectationEvaluation := .exact
        correlationLength := .modelDependent
        tensorConstraint := .positiveByConstruction
        canonicalForm := .openBoundaryOrInfiniteOnly }
  | .ContinuousMPS =>
      { spatialDimension := 1
        entropyScaling := .constant
        expectationEvaluation := .modelDependent
        correlationLength := .modelDependent
        tensorConstraint := .modelDependent
        canonicalForm := .notApplicable }
  | .ContinuousMERA =>
      { spatialDimension := 1
        entropyScaling := .logarithmic
        expectationEvaluation := .modelDependent
        correlationLength := .canBeInfinite
        tensorConstraint := .unitaryOrIsometric
        canonicalForm := .notApplicable }
  | .ContinuousPEPS =>
      { spatialDimension := 2
        entropyScaling := .boundaryLinear
        expectationEvaluation := .modelDependent
        correlationLength := .modelDependent
        tensorConstraint := .modelDependent
        canonicalForm := .notApplicable }

theorem mps_entropyScaling_constant :
    (tensorNetworkProfile .MPS).entropyScaling = .constant := rfl

theorem peps2d_entropyScaling_boundaryLinear :
    (tensorNetworkProfile .PEPS2D).entropyScaling = .boundaryLinear := rfl

theorem ttn_expectation_exact :
    (tensorNetworkProfile .TTN).expectationEvaluation = .exact := rfl

theorem mera1d_entropyScaling_logarithmic :
    (tensorNetworkProfile .MERA1D).entropyScaling = .logarithmic := rfl

theorem branchingMera1d_entropyScaling_volumeLinear :
    (tensorNetworkProfile .BranchingMERA1D).entropyScaling = .volumeLinear := rfl

theorem peps2d_no_exact_general_canonical_form :
    (tensorNetworkProfile .PEPS2D).canonicalForm = .unavailableForLoops := rfl

theorem mera1d_tensors_unitaryOrIsometric :
    (tensorNetworkProfile .MERA1D).tensorConstraint = .unitaryOrIsometric := rfl

/-! ## SVD, loops, and canonical form -/

/-- Minimal graph-level distinction behind canonical forms in the review:
loop-free networks can be put in canonical form by successive SVDs, whereas loopy
networks such as PEPS lack a general exact canonical form. -/
structure TensorNetworkGraph where
  hasLoop : Bool

/-- The review's loop-free canonical-form criterion. -/
def LoopFreeCanonicalCriterion (G : TensorNetworkGraph) : Prop :=
  G.hasLoop = false

theorem loopFreeCanonicalCriterion_iff (G : TensorNetworkGraph) :
    LoopFreeCanonicalCriterion G <-> G.hasLoop = false :=
  Iff.rfl

/-- Data identifying the SVD rank with the Schmidt rank across a bipartition. -/
structure SchmidtSVDData where
  schmidtRank : Nat
  singularValueCount : Nat
  rank_eq_singularValueCount : schmidtRank = singularValueCount

theorem schmidtRank_eq_singularValueCount (D : SchmidtSVDData) :
    D.schmidtRank = D.singularValueCount :=
  D.rank_eq_singularValueCount

/-! ## Bond dimension and entropy bounds -/

/-- Area-law-type entropy bound stated with only the scalar data used by the review:
entropy is bounded by boundary size times `log chi`. -/
structure BondDimensionEntropyBound where
  entropy : Real
  boundarySize : Nat
  bondDimension : Nat
  bound : entropy <= (boundarySize : Real) * Real.log (bondDimension : Real)

/-- Bond dimension one is the product/separable limit in the tensor-network review. -/
def BondDimensionOne (B : BondDimensionEntropyBound) : Prop :=
  B.bondDimension = 1

/-- In the bond-dimension-one limit, the area-law upper bound collapses to zero. -/
theorem entropy_bound_nonpositive_of_bondDimensionOne
    (B : BondDimensionEntropyBound) (hB : BondDimensionOne B) :
    B.entropy <= 0 := by
  unfold BondDimensionOne at hB
  have hbound := B.bound
  rw [hB] at hbound
  simpa [Real.log_one] using hbound

/-- Standard MPS/Schmidt bound for one cut, kept as a named interface because the
Shannon entropy proof is not re-developed in this module. -/
structure SchmidtEntropyCutBound where
  entropy : Real
  bondDimension : Nat
  positiveBondDimension : 0 < bondDimension
  schmidt_bound : entropy <= Real.log (bondDimension : Real)

theorem schmidtEntropyCutBound_le_logChi (B : SchmidtEntropyCutBound) :
    B.entropy <= Real.log (B.bondDimension : Real) :=
  B.schmidt_bound

/-! ## Algorithmic costs recorded by the review -/

/-- Open-boundary MPS canonical manipulations and TEBD/VUMPS cubic scaling. -/
def mpsCubicCost (chi : Nat) : Nat := chi ^ 3

/-- Exact periodic-boundary MPS contraction without approximation. -/
def periodicMPSExactCost (chi : Nat) : Nat := chi ^ 5

/-- Binary MERA contraction/update exponent quoted in the review. -/
def binaryMERACost (chi : Nat) : Nat := chi ^ 9

/-- Ternary MERA contraction/update exponent quoted in the review. -/
def ternaryMERACost (chi : Nat) : Nat := chi ^ 8

/-- Simple-update PEPS local cost in the review. -/
def pepsSimpleUpdateCost (D : Nat) : Nat := D ^ 5

/-- Full-update/CTM-type leading PEPS cost recorded by the review. -/
def pepsFullUpdateLeadingCost (chi D : Nat) : Nat := chi ^ 3 * D ^ 6

theorem tebd_and_vumps_share_mps_cubic_cost (chi : Nat) :
    mpsCubicCost chi = chi ^ 3 := rfl

theorem periodic_mps_exact_cost (chi : Nat) :
    periodicMPSExactCost chi = chi ^ 5 := rfl

theorem binary_mera_cost_exponent (chi : Nat) :
    binaryMERACost chi = chi ^ 9 := rfl

theorem ternary_mera_cost_exponent (chi : Nat) :
    ternaryMERACost chi = chi ^ 8 := rfl

theorem peps_simple_update_cost_exponent (D : Nat) :
    pepsSimpleUpdateCost D = D ^ 5 := rfl

theorem peps_full_update_leading_cost (chi D : Nat) :
    pepsFullUpdateLeadingCost chi D = chi ^ 3 * D ^ 6 := rfl

theorem periodic_mps_exact_cost_dominates_open_cost
    (chi : Nat) (hchi : 1 <= chi) :
    mpsCubicCost chi <= periodicMPSExactCost chi := by
  unfold mpsCubicCost periodicMPSExactCost
  exact Nat.pow_le_pow_right hchi (by norm_num)

theorem binary_mera_cost_dominates_ternary_cost
    (chi : Nat) (hchi : 1 <= chi) :
    ternaryMERACost chi <= binaryMERACost chi := by
  unfold ternaryMERACost binaryMERACost
  exact Nat.pow_le_pow_right hchi (by norm_num)

/-! ## Fermionic tensor-network crossing signs -/

/-- Fermionic tensor-network line crossing sign: only an odd/odd crossing contributes
the parity sign. -/
def fermionCrossingSign (leftOdd rightOdd : Bool) : Int :=
  if leftOdd && rightOdd then -1 else 1

/-- Boolean tensor-network parity as the standard QFT field statistic. -/
def tensorFieldStatistic (odd : Bool) : FieldStatistic :=
  if odd then fermionic else bosonic

/-- Crossings are unordered for the local two-line tensor-network sign convention,
so the Koszul insertion sign takes its exchange branch. -/
def tensorCrossingOrder (_ _ : Bool) : Prop :=
  False

instance tensorCrossingOrderDecidableRel : DecidableRel tensorCrossingOrder := by
  intro _ _
  exact isFalse (by intro h; cases h)

theorem fermionCrossingSign_odd_odd :
    fermionCrossingSign true true = -1 := rfl

theorem fermionCrossingSign_even_left (rightOdd : Bool) :
    fermionCrossingSign false rightOdd = 1 := by
  cases rightOdd <;> rfl

theorem fermionCrossingSign_even_right (leftOdd : Bool) :
    fermionCrossingSign leftOdd false = 1 := by
  cases leftOdd <;> rfl

/-- The tensor-network crossing sign is exactly the QFT exchange sign for the
corresponding bosonic/fermionic field statistics. -/
theorem fermionCrossingSign_eq_exchangeSign (leftOdd rightOdd : Bool) :
    ((fermionCrossingSign leftOdd rightOdd : Int) : ℂ) =
      𝓢(tensorFieldStatistic leftOdd, tensorFieldStatistic rightOdd) := by
  cases leftOdd <;> cases rightOdd <;>
    norm_num [fermionCrossingSign, tensorFieldStatistic, exchangeSign]

/-- The tensor-network crossing sign is also the unordered branch of the standard
Koszul insertion sign used by the perturbative QFT library. -/
theorem fermionCrossingSign_eq_koszulSignCons (leftOdd rightOdd : Bool) :
    ((fermionCrossingSign leftOdd rightOdd : Int) : ℂ) =
      Wick.koszulSignCons tensorFieldStatistic tensorCrossingOrder leftOdd rightOdd := by
  rw [fermionCrossingSign_eq_exchangeSign]
  rw [Wick.koszulSignCons_eq_exchangeSign
    (q := tensorFieldStatistic) (le := tensorCrossingOrder)]
  simp [tensorCrossingOrder]

/-! ## Link to topological PEPS, weak Hopf data, and Haag duality -/

variable {A Region Plaquette Boundary LocalObs : Type*}

/-- Orus-style topological PEPS data linked to the existing weak-Hopf Haag package.
The nontrivial analytic/topological input is the imported package; this structure
records that it is specifically being used as a 2D PEPS/topological-order instance. -/
structure MPOInjectivePEPSHaagInterface [Ring A] [Preorder Region]
    (N : LocalNet A Region) where
  pepsProfile : tensorNetworkProfile .PEPS2D =
    { spatialDimension := 2
      entropyScaling := .boundaryLinear
      expectationEvaluation := .approximate
      correlationLength := .canBeInfinite
      tensorConstraint := .arbitrary
      canonicalForm := .unavailableForLoops }
  mpoInjective : Prop
  hasParentHamiltonian : Prop
  hasLocalTopologicalOrder : Prop
  weakHopfPackage :
    WeakHopfTensorNetworkHaagPackage
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N
  hypotheses_verified :
    mpoInjective ∧ hasParentHamiltonian ∧ hasLocalTopologicalOrder

theorem pepsProfile_is_tableI :
    tensorNetworkProfile .PEPS2D =
      { spatialDimension := 2
        entropyScaling := .boundaryLinear
        expectationEvaluation := .approximate
        correlationLength := .canBeInfinite
        tensorConstraint := .arbitrary
        canonicalForm := .unavailableForLoops } := rfl

/-- MPO-injective/topological PEPS data feeds the exact Haag-duality bridge. -/
theorem mpoInjectivePEPS_exactHaagDualityOn [Ring A] [Preorder Region]
    {N : LocalNet A Region}
    (P : MPOInjectivePEPSHaagInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N) :
    ExactHaagDualityOn N P.weakHopfPackage.geometry.ConeLike :=
  tensorNetwork_exactHaagDualityOn P.weakHopfPackage

/-- The PEPS hypotheses are stated together with the exact Haag-duality output.
This is the theorem downstream files should use when they need both the
topological tensor-network assumptions and the imported weak-Hopf conclusion. -/
theorem mpoInjectivePEPS_hypotheses_and_exactHaagDualityOn [Ring A] [Preorder Region]
    {N : LocalNet A Region}
    (P : MPOInjectivePEPSHaagInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N) :
    P.mpoInjective ∧ P.hasParentHamiltonian ∧ P.hasLocalTopologicalOrder ∧
      ExactHaagDualityOn N P.weakHopfPackage.geometry.ConeLike := by
  exact ⟨P.hypotheses_verified.1, P.hypotheses_verified.2.1,
    P.hypotheses_verified.2.2, mpoInjectivePEPS_exactHaagDualityOn P⟩

/-- The same tensor-network data produces approximate Haag duality once a
cone-deformation system is supplied. -/
theorem mpoInjectivePEPS_approximateHaagDuality [Ring A] [Preorder Region]
    {N : LocalNet A Region}
    (P : MPOInjectivePEPSHaagInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N)
    (Fatten : Region -> Region -> Region)
    (D : ConeDeformationSystem N P.weakHopfPackage.geometry.ConeLike Fatten) :
    ApproximateHaagDuality N Fatten :=
  tensorNetwork_approximateHaagDuality P.weakHopfPackage Fatten D

/-- Coarse-graining preserves the exact cone-like Haag-duality conclusion when the
coarse regions map to cone-like fine regions. -/
theorem mpoInjectivePEPS_coarseGrainedHaagDualityOn [Ring A] [Preorder Region]
    {CoarseRegion : Type*} [Preorder CoarseRegion]
    (Ncoarse : LocalNet A CoarseRegion) {Nfine : LocalNet A Region}
    (P : MPOInjectivePEPSHaagInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) Nfine)
    (B : CoarseGrainingMap Ncoarse Nfine)
    (CoarseCone : CoarseRegion -> Prop)
    (maps_to_coneLike :
      forall O : CoarseRegion, CoarseCone O ->
        P.weakHopfPackage.geometry.ConeLike (B.toFine O)) :
    ExactHaagDualityOn Ncoarse CoarseCone :=
  tensorNetwork_coarseGrainedHaagDualityOn Ncoarse P.weakHopfPackage B
    CoarseCone maps_to_coneLike

end Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems

end
