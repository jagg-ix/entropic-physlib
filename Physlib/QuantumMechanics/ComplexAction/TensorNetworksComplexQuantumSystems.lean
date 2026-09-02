/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
public import Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution.DualCellsAnd2plus1Moves
public import Physlib.QFT.Lattice.WilsonLoopAreaLaw
public import Physlib.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
public import Physlib.QFT.PerturbationTheory.Koszul.KoszulSignInsert
public import Mathlib.Data.Finsupp.Basic

meta import Zil

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

It also formalizes the finite-dimensional, tensor-network-local content of

* X. Chen and A. Vishwanath, *Towards Gauging Time-Reversal Symmetry:
  A Tensor Network Approach*, Phys. Rev. X **5**, 041034 (2015).
* D. Vaid, *Gauging Time Reversal Symmetry in Quantum Gravity: Arrow of
  Time from a Confinement--Deconfinement Transition*, arXiv:2605.16316v1
  (2026).

For Chen--Vishwanath this file proves the local MPS time-reversal action
(their Eqs. 6--7), exact cancellation of virtual transformations in the
interior of a finite segment, the projective twist composition
`M* M = beta I` (Eqs. 14 and 18), and invariance of `beta` under MPS gauge
change (Eq. 19).  The nontrivial class is instantiated by the repository's
Dirac antiunitary `T = i gamma1 gamma3 K`, whose square is `-1`.
The remaining paper-level layer records the two independent 2D
`Z₂ × Z₂ᵀ` SPT invariants, the resulting three SET classes after gauging
the unitary subgroup, the absence of an individual `T²` label for exchanged
double-semion defects, and the stated linear-depth obstruction in 3D.

Because Chen--Vishwanath explicitly leave dynamical time-reversal gauging
open, the infinite locally finite, continuous-time Markov gauge-orbit model
at the end of this file is labelled as a repository extension.  It is not
attributed to the paper and is not called a continuum antiunitary quantum
gauge theory.

The Vaid layer closes the finite dynamical-gauging problem by putting a
`ZMod 2` edge field on the imported spin-network skeleton.  The cellular
identity `boundary_boundary_zero` proves the local gauge action, plaquette
flux invariance, Wilson-loop invariance, gauge invariance of the action and
finite geometry-weighted partition sum, and the orientation response of a
three-dimensional triad.  The paper's confinement transition, cosmological
running of the coupling, and derivation of that coupling from spin-foam
amplitudes remain explicitly outside these finite algebraic theorems.

Analytic inputs such as the existence of a concrete PEPS contraction scheme,
a parent Hamiltonian, or local topological order remain named fields in the
imported weak-Hopf package. -/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.TwoDimensionalSpinHaagDuality
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
open Physlib.QFT.Lattice.WilsonLoopAreaLaw
open FieldStatistic
open scoped BigOperators FieldStatistic

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

lemma mps_entropyScaling_constant :
    (tensorNetworkProfile .MPS).entropyScaling = .constant := rfl

lemma peps2d_entropyScaling_boundaryLinear :
    (tensorNetworkProfile .PEPS2D).entropyScaling = .boundaryLinear := rfl

lemma ttn_expectation_exact :
    (tensorNetworkProfile .TTN).expectationEvaluation = .exact := rfl

lemma mera1d_entropyScaling_logarithmic :
    (tensorNetworkProfile .MERA1D).entropyScaling = .logarithmic := rfl

lemma branchingMera1d_entropyScaling_volumeLinear :
    (tensorNetworkProfile .BranchingMERA1D).entropyScaling = .volumeLinear := rfl

lemma peps2d_no_exact_general_canonical_form :
    (tensorNetworkProfile .PEPS2D).canonicalForm = .unavailableForLoops := rfl

lemma mera1d_tensors_unitaryOrIsometric :
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

lemma loopFreeCanonicalCriterion_iff (G : TensorNetworkGraph) :
    LoopFreeCanonicalCriterion G <-> G.hasLoop = false :=
  Iff.rfl

/-- Data identifying the SVD rank with the Schmidt rank across a bipartition. -/
structure SchmidtSVDData where
  schmidtRank : Nat
  singularValueCount : Nat
  rank_eq_singularValueCount : schmidtRank = singularValueCount

lemma schmidtRank_eq_singularValueCount (D : SchmidtSVDData) :
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
lemma entropy_bound_nonpositive_of_bondDimensionOne
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

lemma schmidtEntropyCutBound_le_logChi (B : SchmidtEntropyCutBound) :
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

lemma tebd_and_vumps_share_mps_cubic_cost (chi : Nat) :
    mpsCubicCost chi = chi ^ 3 := rfl

lemma periodic_mps_exact_cost (chi : Nat) :
    periodicMPSExactCost chi = chi ^ 5 := rfl

lemma binary_mera_cost_exponent (chi : Nat) :
    binaryMERACost chi = chi ^ 9 := rfl

lemma ternary_mera_cost_exponent (chi : Nat) :
    ternaryMERACost chi = chi ^ 8 := rfl

lemma peps_simple_update_cost_exponent (D : Nat) :
    pepsSimpleUpdateCost D = D ^ 5 := rfl

lemma peps_full_update_leading_cost (chi D : Nat) :
    pepsFullUpdateLeadingCost chi D = chi ^ 3 * D ^ 6 := rfl

lemma periodic_mps_exact_cost_dominates_open_cost
    (chi : Nat) (hchi : 1 <= chi) :
    mpsCubicCost chi <= periodicMPSExactCost chi := by
  unfold mpsCubicCost periodicMPSExactCost
  exact Nat.pow_le_pow_right hchi (by norm_num)

lemma binary_mera_cost_dominates_ternary_cost
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

lemma fermionCrossingSign_odd_odd :
    fermionCrossingSign true true = -1 := rfl

lemma fermionCrossingSign_even_left (rightOdd : Bool) :
    fermionCrossingSign false rightOdd = 1 := by
  cases rightOdd <;> rfl

lemma fermionCrossingSign_even_right (leftOdd : Bool) :
    fermionCrossingSign leftOdd false = 1 := by
  cases leftOdd <;> rfl

/-- The tensor-network crossing sign is exactly the QFT exchange sign for the
corresponding bosonic/fermionic field statistics. -/
lemma fermionCrossingSign_eq_exchangeSign (leftOdd rightOdd : Bool) :
    ((fermionCrossingSign leftOdd rightOdd : Int) : ℂ) =
      𝓢(tensorFieldStatistic leftOdd, tensorFieldStatistic rightOdd) := by
  cases leftOdd <;> cases rightOdd <;>
    norm_num [fermionCrossingSign, tensorFieldStatistic, exchangeSign]

/-- The tensor-network crossing sign is also the unordered branch of the standard
Koszul insertion sign used by the perturbative QFT library. -/
lemma fermionCrossingSign_eq_koszulSignCons (leftOdd rightOdd : Bool) :
    ((fermionCrossingSign leftOdd rightOdd : Int) : ℂ) =
      Wick.koszulSignCons tensorFieldStatistic tensorCrossingOrder leftOdd rightOdd := by
  rw [fermionCrossingSign_eq_exchangeSign]
  rw [Wick.koszulSignCons_eq_exchangeSign
    (q := tensorFieldStatistic) (le := tensorCrossingOrder)]
  simp [tensorCrossingOrder]

/-! ## Chen--Vishwanath local time reversal on matrix-product states -/

open Matrix Complex
open scoped BigOperators

/-- A one-dimensional MPS local tensor: one `D x D` virtual matrix for
each physical basis index. -/
abbrev MPSLocalTensor (physicalDim bondDim : Nat) :=
  Fin physicalDim → Matrix (Fin bondDim) (Fin bondDim) ℂ

/-- **Chen--Vishwanath Eq. (6).** Local time reversal first takes
entrywise complex conjugation of the MPS tensor and then applies the
physical time-reversal matrix `U`. -/
def timeReversedMPSTensor {physicalDim bondDim : Nat}
    (U : Matrix (Fin physicalDim) (Fin physicalDim) ℂ)
    (A : MPSLocalTensor physicalDim bondDim) :
    MPSLocalTensor physicalDim bondDim :=
  fun i => ∑ j, U i j • (A j).map star

/-- The virtual similarity transformation appearing in
Chen--Vishwanath Eq. (7). -/
def virtualGaugeTransform {bondDim : Nat}
    (M Minv A : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
    Matrix (Fin bondDim) (Fin bondDim) ℂ :=
  M * A * Minv

/-- Adjacent virtual transformations cancel in the interior of an MPS
segment. This is the algebraic step behind the boundary twists in
Chen--Vishwanath Eqs. (8)--(9). -/
theorem virtualGaugeTransform_mul {bondDim : Nat}
    (M Minv A B : Matrix (Fin bondDim) (Fin bondDim) ℂ)
    (hleft : Minv * M = 1) :
    virtualGaugeTransform M Minv A * virtualGaugeTransform M Minv B =
      virtualGaugeTransform M Minv (A * B) := by
  unfold virtualGaugeTransform
  rw [show (M * A * Minv) * (M * B * Minv) =
    M * A * (Minv * M) * B * Minv by noncomm_ring, hleft]
  simp [Matrix.mul_assoc]

/-- Apply the same virtual transformation to every tensor matrix in a
finite MPS segment. -/
def gaugeTransformSegment {bondDim : Nat}
    (M Minv : Matrix (Fin bondDim) (Fin bondDim) ℂ)
    (As : List (Matrix (Fin bondDim) (Fin bondDim) ℂ)) :
    Matrix (Fin bondDim) (Fin bondDim) ℂ :=
  (As.map (virtualGaugeTransform M Minv)).prod

/-- **Bulk cancellation / boundary localization.** On an arbitrary
finite segment, every internal `M⁻¹ M` pair cancels and only the two
boundary insertions remain. -/
theorem gaugeTransformSegment_eq_boundary {bondDim : Nat}
    (M Minv : Matrix (Fin bondDim) (Fin bondDim) ℂ)
    (hleft : Minv * M = 1) (hright : M * Minv = 1)
    (As : List (Matrix (Fin bondDim) (Fin bondDim) ℂ)) :
    gaugeTransformSegment M Minv As = M * As.prod * Minv := by
  induction As with
  | nil =>
      simp [gaugeTransformSegment, hright]
  | cons A As ih =>
      simp only [gaugeTransformSegment, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]
      change virtualGaugeTransform M Minv A *
          virtualGaugeTransform M Minv As.prod =
        virtualGaugeTransform M Minv (A * As.prod)
      exact virtualGaugeTransform_mul M Minv A As.prod hleft

/-- Injective-MPS time-reversal covariance data from
Chen--Vishwanath Eqs. (6)--(7). The local physical antiunitary action
is represented virtually by the invertible boundary twist `M`. -/
structure TimeReversalSymmetricMPSData (physicalDim bondDim : Nat) where
  tensor : MPSLocalTensor physicalDim bondDim
  physicalTimeReversal : Matrix (Fin physicalDim) (Fin physicalDim) ℂ
  virtualTwist : Matrix (Fin bondDim) (Fin bondDim) ℂ
  virtualTwistInv : Matrix (Fin bondDim) (Fin bondDim) ℂ
  inverse_left : virtualTwistInv * virtualTwist = 1
  inverse_right : virtualTwist * virtualTwistInv = 1
  local_covariance :
    ∀ i, timeReversedMPSTensor physicalTimeReversal tensor i =
      virtualGaugeTransform virtualTwist virtualTwistInv (tensor i)

/-- Ordered virtual-matrix product for a finite physical word. -/
def mpsSegment {physicalDim bondDim : Nat}
    (A : MPSLocalTensor physicalDim bondDim)
    (word : List (Fin physicalDim)) :
    Matrix (Fin bondDim) (Fin bondDim) ℂ :=
  (word.map A).prod

/-- **Chen--Vishwanath boundary-twist theorem.** Local time reversal on
every physical site of a finite MPS segment changes the segment only by
`M` at its left boundary and `M⁻¹` at its right boundary. -/
theorem timeReversed_segment_eq_boundary {physicalDim bondDim : Nat}
    (D : TimeReversalSymmetricMPSData physicalDim bondDim)
    (word : List (Fin physicalDim)) :
    mpsSegment
        (timeReversedMPSTensor D.physicalTimeReversal D.tensor) word =
      D.virtualTwist * mpsSegment D.tensor word * D.virtualTwistInv := by
  rw [mpsSegment, show
    word.map (timeReversedMPSTensor D.physicalTimeReversal D.tensor) =
      (word.map D.tensor).map
        (virtualGaugeTransform D.virtualTwist D.virtualTwistInv) by
      simp only [List.map_map]
      exact List.map_congr_left (fun i _ => D.local_covariance i)]
  exact gaugeTransformSegment_eq_boundary _ _
    D.inverse_left D.inverse_right _

/-! ### The projective `Z2` time-reversal invariant -/

/-- `M* M`, with `M*` denoting entrywise complex conjugation rather
than the adjoint. This is the invariant in Chen--Vishwanath Eq. (14). -/
def chenProjectiveSquare {bondDim : Nat}
    (M : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
    Matrix (Fin bondDim) (Fin bondDim) ℂ :=
  M.map star * M

/-- The two projective time-reversal classes: `+1` for the trivial
class and `-1` for the Kramers/nontrivial class. -/
def chenProjectivePhase : Bool → ℂ
  | false => 1
  | true => -1

lemma chenProjectivePhase_sq (nontrivial : Bool) :
    chenProjectivePhase nontrivial ^ 2 = 1 := by
  cases nontrivial <;> norm_num [chenProjectivePhase]

/-- A virtual time-reversal twist with its checked projective class. -/
structure ChenTimeReversalTwist (bondDim : Nat) where
  matrix : Matrix (Fin bondDim) (Fin bondDim) ℂ
  nontrivial : Bool
  projective_square :
    chenProjectiveSquare matrix = chenProjectivePhase nontrivial • 1

/-- Insert the left-boundary time-reversal twist of
Chen--Vishwanath Eq. (17). -/
def insertChenTwist {bondDim : Nat}
    (M A : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
    Matrix (Fin bondDim) (Fin bondDim) ℂ :=
  M * A

/-- **Chen--Vishwanath Eq. (18).** Two antiunitary twists compose to
the identity twist times the universal phase `beta = ±1`. -/
theorem insertChenTwist_twice {bondDim : Nat}
    (T : ChenTimeReversalTwist bondDim)
    (A : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
    T.matrix.map star * insertChenTwist T.matrix A =
      chenProjectivePhase T.nontrivial • A := by
  rw [insertChenTwist, ← Matrix.mul_assoc, ← chenProjectiveSquare,
    T.projective_square]
  simp

/-- MPS gauge change of a time-reversal twist:
`M ↦ N* M N⁻¹`, as in Chen--Vishwanath Eq. (19). -/
def chenGaugeChange {bondDim : Nat}
    (N Ninv M : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
    Matrix (Fin bondDim) (Fin bondDim) ℂ :=
  N.map star * M * Ninv

lemma matrix_map_star_mul {bondDim : Nat}
    (A B : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

/-- **Chen--Vishwanath Eq. (19).** The projective phase is invariant
under an arbitrary invertible change of MPS virtual gauge. -/
theorem chenProjectiveSquare_gauge_invariant {bondDim : Nat}
    (N Ninv M : Matrix (Fin bondDim) (Fin bondDim) ℂ)
    (hleft : Ninv * N = 1) (hright : N * Ninv = 1)
    (β : ℂ) (hM : chenProjectiveSquare M = β • 1) :
    chenProjectiveSquare (chenGaugeChange N Ninv M) = β • 1 := by
  change M.map star * M = β • 1 at hM
  have hstar : Ninv.map star * N.map star = 1 := by
    have hc := congrArg
      (fun A : Matrix (Fin bondDim) (Fin bondDim) ℂ =>
        A.map (starRingEnd ℂ)) hleft
    rw [Matrix.map_mul] at hc
    simpa using hc
  unfold chenProjectiveSquare chenGaugeChange
  have hstarstar (A : Matrix (Fin bondDim) (Fin bondDim) ℂ) :
      (A.map star).map star = A := by
    ext i j
    simp
  have hmap :
      (N.map star * M * Ninv).map star =
        N * M.map star * Ninv.map star := by
    calc
      (N.map star * M * Ninv).map star =
          (N.map star).map star * M.map star * Ninv.map star := by
            rw [matrix_map_star_mul, matrix_map_star_mul]
      _ = N * M.map star * Ninv.map star := by rw [hstarstar]
  rw [hmap]
  rw [show (N * M.map star * Ninv.map star) *
      (N.map star * M * Ninv) =
      N * M.map star * (Ninv.map star * N.map star) * M * Ninv by
      noncomm_ring, hstar]
  simp only [Matrix.mul_one]
  rw [show N * M.map star * M * Ninv =
      N * (M.map star * M) * Ninv by noncomm_ring]
  rw [hM]
  rw [show
    N * (β • (1 : Matrix (Fin bondDim) (Fin bondDim) ℂ)) * Ninv =
      β • (N * Ninv) by simp]
  rw [hright]

/-! ### Concrete nontrivial class from the Dirac antiunitary -/

open
  Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
open spaceTime

/-- The existing spin-`1/2` Dirac time-reversal matrix supplies a
concrete nontrivial Chen projective twist. -/
def diracChenTwist : ChenTimeReversalTwist 4 where
  matrix := I • (γ1 * γ3)
  nontrivial := true
  projective_square := by
    unfold chenProjectiveSquare chenProjectivePhase
    rw [Iγ1γ3_map_star, neg_mul, IgammaT_sq]
    simp

theorem diracChenTwist_projectiveSquare :
    chenProjectiveSquare diracChenTwist.matrix =
      (-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  diracChenTwist.projective_square

/-- Two Chen boundary twists act by `-1` for the concrete Dirac
spinor class. -/
theorem diracChenTwist_twice (A : Matrix (Fin 4) (Fin 4) ℂ) :
    diracChenTwist.matrix.map star *
        insertChenTwist diracChenTwist.matrix A = -A := by
  simpa [diracChenTwist, chenProjectivePhase] using
    insertChenTwist_twice diracChenTwist A

/-- The same projective `-1` is the repository's already-proved
antiunitary spinor law `T² = -1`; this identifies Chen's nontrivial
virtual class with the Bennett/Dirac Kramers class. -/
theorem diracChenTwist_spinorAction_sq (ψ : Fin 4 → ℂ) :
    timeReversal (timeReversal ψ) = -ψ :=
  timeReversal_sq ψ

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

/-- Linear energy assigned to a static confined time-reversal twist of
length `L`. This is deliberately an interface for the confined twists
constructed by Chen--Vishwanath, not a dynamical gauge-field action. -/
def confinedTimeReversalTwistEnergy (tension : ℝ) (L : Nat) : ℝ :=
  tension * L

lemma confinedTimeReversalTwistEnergy_pos
    {tension : ℝ} (htension : 0 < tension) {L : Nat} (hL : 0 < L) :
    0 < confinedTimeReversalTwistEnergy tension L := by
  exact mul_pos htension (Nat.cast_pos.mpr hL)

/-- A 2D Chen--Vishwanath static time-reversal twist carried by an
existing MPO-injective/topological PEPS. Positivity of the tension
records confinement. The imported weak-Hopf package supplies the
separate Haag-duality conclusion. -/
structure ChenConfinedTimeReversalPEPSInterface [Ring A] [Preorder Region]
    (N : LocalNet A Region) where
  peps : MPOInjectivePEPSHaagInterface
    (A := A) (Region := Region) (Plaquette := Plaquette)
    (Boundary := Boundary) (LocalObs := LocalObs) N
  twistTension : ℝ
  twistTension_pos : 0 < twistTension

lemma pepsProfile_is_tableI :
    tensorNetworkProfile .PEPS2D =
      { spatialDimension := 2
        entropyScaling := .boundaryLinear
        expectationEvaluation := .approximate
        correlationLength := .canBeInfinite
        tensorConstraint := .arbitrary
        canonicalForm := .unavailableForLoops } := rfl

/-- MPO-injective/topological PEPS data feeds the exact Haag-duality bridge. -/
lemma mpoInjectivePEPS_exactHaagDualityOn [Ring A] [Preorder Region]
    {N : LocalNet A Region}
    (P : MPOInjectivePEPSHaagInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N) :
    ExactHaagDualityOn N P.weakHopfPackage.geometry.ConeLike :=
  tensorNetwork_exactHaagDualityOn P.weakHopfPackage

/-- The PEPS hypotheses are carried together with the exact Haag-duality output.
This is the theorem downstream files should use when they need both the
topological tensor-network assumptions and the imported weak-Hopf conclusion. -/
lemma mpoInjectivePEPS_hypotheses_and_exactHaagDualityOn [Ring A] [Preorder Region]
    {N : LocalNet A Region}
    (P : MPOInjectivePEPSHaagInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N) :
    P.mpoInjective ∧ P.hasParentHamiltonian ∧ P.hasLocalTopologicalOrder ∧
      ExactHaagDualityOn N P.weakHopfPackage.geometry.ConeLike := by
  exact ⟨P.hypotheses_verified.1, P.hypotheses_verified.2.1,
    P.hypotheses_verified.2.2, mpoInjectivePEPS_exactHaagDualityOn P⟩

/-- The honest 2D Chen adapter: every positive-length static twist has
positive confinement energy, while the underlying topological PEPS
retains exact cone-like Haag duality. No deconfined or dynamical
time-reversal gauge field is inferred. -/
theorem chenConfinedPEPS_energy_and_exactHaagDualityOn
    [Ring A] [Preorder Region]
    {N : LocalNet A Region}
    (P : ChenConfinedTimeReversalPEPSInterface
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N)
    {L : Nat} (hL : 0 < L) :
    0 < confinedTimeReversalTwistEnergy P.twistTension L ∧
      ExactHaagDualityOn N P.peps.weakHopfPackage.geometry.ConeLike := by
  exact ⟨confinedTimeReversalTwistEnergy_pos P.twistTension_pos hL,
    mpoInjectivePEPS_exactHaagDualityOn P.peps⟩

/-- The same tensor-network data produces approximate Haag duality once a
cone-deformation system is supplied. -/
lemma mpoInjectivePEPS_approximateHaagDuality [Ring A] [Preorder Region]
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
lemma mpoInjectivePEPS_coarseGrainedHaagDualityOn [Ring A] [Preorder Region]
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

/-! ## Finite dynamical gauging of time reversal

The paper's edge signs are written additively as `ZMod 2` cochains.  Under
the character `z2Sign`, addition becomes multiplication of the physical
signs `±1`.  This makes the cellular equation `∂² = 0` the one structural
input from which the gauge-invariance theorems follow. -/

/-- A finite spin-network two-complex carrying a dynamical `ZMod 2` edge
field.  `boundary_boundary_zero` is the cellular identity `∂² = 0`: the
boundary of every plaquette boundary vanishes at every vertex. -/
structure DynamicalTimeReversalGaugeComplex where
  skeleton : SpinNetworkSkeleton
  plaquetteCount : Nat
  plaquetteCount_pos : 0 < plaquetteCount
  edgeBoundary :
    Fin skeleton.edgeCount → Fin skeleton.nodeCount → ZMod 2
  plaquetteBoundary :
    Fin plaquetteCount → Fin skeleton.edgeCount → ZMod 2
  boundary_boundary_zero :
    ∀ p v, ∑ e, plaquetteBoundary p e * edgeBoundary e v = 0

/-- A binary orientation variable on every spin-network edge. -/
abbrev TimeReversalEdgeConfiguration
    (G : DynamicalTimeReversalGaugeComplex) :=
  Fin G.skeleton.edgeCount → ZMod 2

/-- A local binary gauge parameter at every spin-network vertex. -/
abbrev TimeReversalVertexGauge
    (G : DynamicalTimeReversalGaugeComplex) :=
  Fin G.skeleton.nodeCount → ZMod 2

/-- Vaid's local gauge transformation
`σ_e ↦ τ_source σ_e τ_target`, written in additive cochain notation. -/
def timeReversalGaugeTransform (G : DynamicalTimeReversalGaugeComplex)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    TimeReversalEdgeConfiguration G :=
  fun e => σ e + ∑ v, G.edgeBoundary e v * τ v

@[simp] theorem timeReversalGaugeTransform_zero
    (G : DynamicalTimeReversalGaugeComplex)
    (σ : TimeReversalEdgeConfiguration G) :
    timeReversalGaugeTransform G 0 σ = σ := by
  funext e
  simp [timeReversalGaugeTransform]

/-- Local gauge transformations compose by pointwise `ZMod 2` addition. -/
theorem timeReversalGaugeTransform_add
    (G : DynamicalTimeReversalGaugeComplex)
    (τ₁ τ₂ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    timeReversalGaugeTransform G τ₁
        (timeReversalGaugeTransform G τ₂ σ) =
      timeReversalGaugeTransform G (τ₁ + τ₂) σ := by
  funext e
  simp only [timeReversalGaugeTransform, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  abel

/-- Every binary local gauge transformation is its own inverse. -/
@[simp] theorem timeReversalGaugeTransform_self
    (G : DynamicalTimeReversalGaugeComplex)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    timeReversalGaugeTransform G τ
        (timeReversalGaugeTransform G τ σ) = σ := by
  rw [timeReversalGaugeTransform_add]
  have hτ : τ + τ = 0 := by
    funext v
    exact CharTwo.add_self_eq_zero (τ v)
  rw [hτ]
  exact timeReversalGaugeTransform_zero G σ

/-- The local gauge action as an involutive equivalence of configurations. -/
def timeReversalGaugeEquiv (G : DynamicalTimeReversalGaugeComplex)
    (τ : TimeReversalVertexGauge G) :
    TimeReversalEdgeConfiguration G ≃
      TimeReversalEdgeConfiguration G where
  toFun := timeReversalGaugeTransform G τ
  invFun := timeReversalGaugeTransform G τ
  left_inv := timeReversalGaugeTransform_self G τ
  right_inv := timeReversalGaugeTransform_self G τ

/-- Additive `ZMod 2` flux through a plaquette.  Under `z2Sign` this is
the product `∏_{e ∈ ∂p} σ_e` in Vaid Eq. (48). -/
def timeReversalPlaquetteFlux
    (G : DynamicalTimeReversalGaugeComplex)
    (σ : TimeReversalEdgeConfiguration G)
    (p : Fin G.plaquetteCount) : ZMod 2 :=
  ∑ e, G.plaquetteBoundary p e * σ e

/-- **Local gauge invariance of plaquette flux.**  This is derived from
`∂² = 0`, rather than stored as a separate certificate. -/
theorem timeReversalPlaquetteFlux_gauge_invariant
    (G : DynamicalTimeReversalGaugeComplex)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G)
    (p : Fin G.plaquetteCount) :
    timeReversalPlaquetteFlux G
        (timeReversalGaugeTransform G τ σ) p =
      timeReversalPlaquetteFlux G σ p := by
  unfold timeReversalPlaquetteFlux timeReversalGaugeTransform
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hzero :
      (∑ e, G.plaquetteBoundary p e *
          ∑ v, G.edgeBoundary e v * τ v) = 0 := by
    calc
      (∑ e, G.plaquetteBoundary p e *
          ∑ v, G.edgeBoundary e v * τ v) =
          ∑ e, ∑ v, G.plaquetteBoundary p e *
            (G.edgeBoundary e v * τ v) := by
              apply Finset.sum_congr rfl
              intro e _
              rw [Finset.mul_sum]
      _ = ∑ v, ∑ e, G.plaquetteBoundary p e *
            (G.edgeBoundary e v * τ v) := Finset.sum_comm
      _ = ∑ v, (∑ e, G.plaquetteBoundary p e *
            G.edgeBoundary e v) * τ v := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro e _
              ring
      _ = 0 := by simp [G.boundary_boundary_zero]
  rw [hzero, add_zero]

/-- The multiplicative real character `ZMod 2 → {+1,-1}`. -/
def z2TimeReversalSign (x : ZMod 2) : ℝ :=
  if x = 0 then 1 else -1

@[simp] theorem z2TimeReversalSign_zero :
    z2TimeReversalSign 0 = 1 := by
  simp [z2TimeReversalSign]

@[simp] theorem z2TimeReversalSign_sq (x : ZMod 2) :
    z2TimeReversalSign x ^ 2 = 1 := by
  by_cases hx : x = 0 <;> simp [z2TimeReversalSign, hx]

/-- The additive binary flux becomes the product of physical signs. -/
@[simp] theorem z2TimeReversalSign_add (x y : ZMod 2) :
    z2TimeReversalSign (x + y) =
      z2TimeReversalSign x * z2TimeReversalSign y := by
  have binary (a : ZMod 2) : a = 0 ∨ a = 1 := by
    have ha := ZMod.val_lt a
    interval_cases hval : a.val
    · left
      rw [← ZMod.natCast_zmod_val a, hval]
      norm_num
    · right
      rw [← ZMod.natCast_zmod_val a, hval]
      norm_num
  rcases binary x with rfl | rfl <;>
    rcases binary y with rfl | rfl <;>
    simp [z2TimeReversalSign, CharTwo.add_self_eq_zero]

theorem z2TimeReversalSign_le_one (x : ZMod 2) :
    z2TimeReversalSign x ≤ 1 := by
  by_cases hx : x = 0 <;> simp [z2TimeReversalSign, hx]

@[simp] theorem abs_z2TimeReversalSign (x : ZMod 2) :
    |z2TimeReversalSign x| = 1 := by
  by_cases hx : x = 0 <;> simp [z2TimeReversalSign, hx]

/-- Multiplicative plaquette holonomy `∏_{e ∈ ∂p} σ_e`. -/
def timeReversalPlaquetteSign
    (G : DynamicalTimeReversalGaugeComplex)
    (σ : TimeReversalEdgeConfiguration G)
    (p : Fin G.plaquetteCount) : ℝ :=
  z2TimeReversalSign (timeReversalPlaquetteFlux G σ p)

theorem timeReversalPlaquetteSign_gauge_invariant
    (G : DynamicalTimeReversalGaugeComplex)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G)
    (p : Fin G.plaquetteCount) :
    timeReversalPlaquetteSign G
        (timeReversalGaugeTransform G τ σ) p =
      timeReversalPlaquetteSign G σ p := by
  simp [timeReversalPlaquetteSign,
    timeReversalPlaquetteFlux_gauge_invariant]

/-- The dynamical binary gauge-field action
`S_Z2 = -K ∑_p ∏_{e∈∂p} σ_e` from Vaid Eq. (48). -/
def dynamicalTimeReversalGaugeAction
    (G : DynamicalTimeReversalGaugeComplex)
    (K : ℝ) (σ : TimeReversalEdgeConfiguration G) : ℝ :=
  -K * ∑ p, timeReversalPlaquetteSign G σ p

/-- The full finite gauge-field action is locally gauge invariant. -/
theorem dynamicalTimeReversalGaugeAction_gauge_invariant
    (G : DynamicalTimeReversalGaugeComplex)
    (K : ℝ) (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    dynamicalTimeReversalGaugeAction G K
        (timeReversalGaugeTransform G τ σ) =
      dynamicalTimeReversalGaugeAction G K σ := by
  unfold dynamicalTimeReversalGaugeAction
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact timeReversalPlaquetteSign_gauge_invariant G τ σ p

/-- The constant-shifted, nonnegative Wilson convention reusing the
repository's existing single-plaquette `wilsonAction`. -/
noncomputable def shiftedDynamicalTimeReversalWilsonAction
    (G : DynamicalTimeReversalGaugeComplex)
    (K : ℝ) (σ : TimeReversalEdgeConfiguration G) : ℝ :=
  ∑ p, wilsonAction K (timeReversalPlaquetteSign G σ p)

theorem shiftedDynamicalTimeReversalWilsonAction_nonneg
    (G : DynamicalTimeReversalGaugeComplex)
    {K : ℝ} (hK : 0 ≤ K)
    (σ : TimeReversalEdgeConfiguration G) :
    0 ≤ shiftedDynamicalTimeReversalWilsonAction G K σ := by
  apply Finset.sum_nonneg
  intro p _
  exact wilsonAction_nonneg hK (z2TimeReversalSign_le_one _)

theorem shiftedDynamicalTimeReversalWilsonAction_gauge_invariant
    (G : DynamicalTimeReversalGaugeComplex)
    (K : ℝ) (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    shiftedDynamicalTimeReversalWilsonAction G K
        (timeReversalGaugeTransform G τ σ) =
      shiftedDynamicalTimeReversalWilsonAction G K σ := by
  unfold shiftedDynamicalTimeReversalWilsonAction
  apply Finset.sum_congr rfl
  intro p _
  simp only [timeReversalPlaquetteSign_gauge_invariant]

/-- The shifted Wilson convention differs from Eq. (48) only by the
configuration-independent constant `K * numberOfPlaquettes`. -/
theorem shiftedDynamicalTimeReversalWilsonAction_eq_action_add_constant
    (G : DynamicalTimeReversalGaugeComplex)
    (K : ℝ) (σ : TimeReversalEdgeConfiguration G) :
    shiftedDynamicalTimeReversalWilsonAction G K σ =
      dynamicalTimeReversalGaugeAction G K σ +
        K * G.plaquetteCount := by
  simp only [shiftedDynamicalTimeReversalWilsonAction, wilsonAction,
    dynamicalTimeReversalGaugeAction, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  have hneg :
      (∑ p, -K * timeReversalPlaquetteSign G σ p) =
        -(∑ p, K * timeReversalPlaquetteSign G σ p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hneg]
  ring

/-- A closed edge chain: its cellular boundary vanishes at every vertex. -/
structure TimeReversalEdgeCycle
    (G : DynamicalTimeReversalGaugeComplex) where
  incidence : Fin G.skeleton.edgeCount → ZMod 2
  boundary_zero :
    ∀ v, ∑ e, incidence e * G.edgeBoundary e v = 0

/-- Additive flux along a closed Wilson cycle. -/
def timeReversalWilsonFlux
    (G : DynamicalTimeReversalGaugeComplex)
    (C : TimeReversalEdgeCycle G)
    (σ : TimeReversalEdgeConfiguration G) : ZMod 2 :=
  ∑ e, C.incidence e * σ e

/-- Closed-cycle flux is invariant under every local vertex gauge change. -/
theorem timeReversalWilsonFlux_gauge_invariant
    (G : DynamicalTimeReversalGaugeComplex)
    (C : TimeReversalEdgeCycle G)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    timeReversalWilsonFlux G C
        (timeReversalGaugeTransform G τ σ) =
      timeReversalWilsonFlux G C σ := by
  unfold timeReversalWilsonFlux timeReversalGaugeTransform
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hzero :
      (∑ e, C.incidence e *
          ∑ v, G.edgeBoundary e v * τ v) = 0 := by
    calc
      (∑ e, C.incidence e *
          ∑ v, G.edgeBoundary e v * τ v) =
          ∑ e, ∑ v, C.incidence e *
            (G.edgeBoundary e v * τ v) := by
              apply Finset.sum_congr rfl
              intro e _
              rw [Finset.mul_sum]
      _ = ∑ v, ∑ e, C.incidence e *
            (G.edgeBoundary e v * τ v) := Finset.sum_comm
      _ = ∑ v, (∑ e, C.incidence e *
            G.edgeBoundary e v) * τ v := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro e _
              ring
      _ = 0 := by simp [C.boundary_zero]
  rw [hzero, add_zero]

/-- The real Wilson-loop observable `W(C)=∏_{e∈C}σ_e`. -/
def dynamicalTimeReversalWilsonLoop
    (G : DynamicalTimeReversalGaugeComplex)
    (C : TimeReversalEdgeCycle G)
    (σ : TimeReversalEdgeConfiguration G) : ℝ :=
  z2TimeReversalSign (timeReversalWilsonFlux G C σ)

/-- **Wilson-loop gauge invariance**, the nonlocal observable in Vaid Eq. (50). -/
theorem dynamicalTimeReversalWilsonLoop_gauge_invariant
    (G : DynamicalTimeReversalGaugeComplex)
    (C : TimeReversalEdgeCycle G)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    dynamicalTimeReversalWilsonLoop G C
        (timeReversalGaugeTransform G τ σ) =
      dynamicalTimeReversalWilsonLoop G C σ := by
  simp [dynamicalTimeReversalWilsonLoop,
    timeReversalWilsonFlux_gauge_invariant]

/-- Geometry-coupled finite dynamical-gauging data for Vaid Eq. (49).
The geometry factor is positive and locally gauge invariant. -/
structure DynamicalTimeReversalGaugeModel
    (G : DynamicalTimeReversalGaugeComplex) where
  coupling : ℝ
  coupling_nonneg : 0 ≤ coupling
  geometryWeight : TimeReversalEdgeConfiguration G → ℝ
  geometryWeight_pos : ∀ σ, 0 < geometryWeight σ
  geometryWeight_gauge_invariant :
    ∀ τ σ, geometryWeight (timeReversalGaugeTransform G τ σ) =
      geometryWeight σ

/-- The geometry-weighted Boltzmann summand in Vaid Eq. (49). -/
noncomputable def DynamicalTimeReversalGaugeModel.weight
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (σ : TimeReversalEdgeConfiguration G) : ℝ :=
  Real.exp (-dynamicalTimeReversalGaugeAction G M.coupling σ) *
    M.geometryWeight σ

theorem DynamicalTimeReversalGaugeModel.weight_pos
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (σ : TimeReversalEdgeConfiguration G) :
    0 < M.weight σ :=
  mul_pos (Real.exp_pos _) (M.geometryWeight_pos σ)

theorem DynamicalTimeReversalGaugeModel.weight_gauge_invariant
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (τ : TimeReversalVertexGauge G)
    (σ : TimeReversalEdgeConfiguration G) :
    M.weight (timeReversalGaugeTransform G τ σ) = M.weight σ := by
  simp [DynamicalTimeReversalGaugeModel.weight,
    dynamicalTimeReversalGaugeAction_gauge_invariant,
    M.geometryWeight_gauge_invariant]

/-- The complete finite configuration sum
`Z = ∑_σ exp(-S_Z2[σ]) Z_geom[σ]` from Vaid Eq. (49). -/
noncomputable def DynamicalTimeReversalGaugeModel.partition
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G) : ℝ :=
  ∑ σ : TimeReversalEdgeConfiguration G, M.weight σ

/-- The finite geometry-coupled partition function is strictly positive. -/
theorem DynamicalTimeReversalGaugeModel.partition_pos
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G) :
    0 < M.partition := by
  unfold DynamicalTimeReversalGaugeModel.partition
  exact Finset.sum_pos (fun σ _ => M.weight_pos σ)
    ⟨0, Finset.mem_univ (0 : TimeReversalEdgeConfiguration G)⟩

/-- The finite configuration sum is invariant under reindexing by any
local gauge transformation. -/
theorem DynamicalTimeReversalGaugeModel.partition_gauge_reindex
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (τ : TimeReversalVertexGauge G) :
    (∑ σ : TimeReversalEdgeConfiguration G,
        M.weight (timeReversalGaugeTransform G τ σ)) =
      M.partition := by
  unfold DynamicalTimeReversalGaugeModel.partition
  change (∑ σ, M.weight ((timeReversalGaugeEquiv G τ) σ)) =
    ∑ σ, M.weight σ
  exact (timeReversalGaugeEquiv G τ).sum_comp M.weight

/-- Unnormalized Wilson-loop expectation numerator. -/
noncomputable def DynamicalTimeReversalGaugeModel.wilsonNumerator
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (C : TimeReversalEdgeCycle G) : ℝ :=
  ∑ σ : TimeReversalEdgeConfiguration G,
    M.weight σ * dynamicalTimeReversalWilsonLoop G C σ

/-- Normalized finite Wilson-loop expectation from Vaid Eq. (50). -/
noncomputable def DynamicalTimeReversalGaugeModel.wilsonExpectation
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (C : TimeReversalEdgeCycle G) : ℝ :=
  M.wilsonNumerator C / M.partition

theorem DynamicalTimeReversalGaugeModel.abs_wilsonNumerator_le_partition
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (C : TimeReversalEdgeCycle G) :
    |M.wilsonNumerator C| ≤ M.partition := by
  calc
    |M.wilsonNumerator C| ≤
        ∑ σ : TimeReversalEdgeConfiguration G,
          |M.weight σ * dynamicalTimeReversalWilsonLoop G C σ| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ = M.partition := by
      unfold DynamicalTimeReversalGaugeModel.partition
      apply Finset.sum_congr rfl
      intro σ _
      rw [abs_mul, abs_of_pos (M.weight_pos σ)]
      simp [dynamicalTimeReversalWilsonLoop]

/-- Every normalized finite Wilson-loop expectation lies in `[-1,1]`. -/
theorem DynamicalTimeReversalGaugeModel.abs_wilsonExpectation_le_one
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (C : TimeReversalEdgeCycle G) :
    |M.wilsonExpectation C| ≤ 1 := by
  rw [DynamicalTimeReversalGaugeModel.wilsonExpectation, abs_div,
    abs_of_pos M.partition_pos]
  exact (div_le_one M.partition_pos).2
    (M.abs_wilsonNumerator_le_partition C)

/-! ### Finite Elitzur cancellation -/

/-- Unnormalized expectation numerator for an arbitrary finite observable. -/
noncomputable def DynamicalTimeReversalGaugeModel.observableNumerator
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (observable : TimeReversalEdgeConfiguration G → ℝ) : ℝ :=
  ∑ σ : TimeReversalEdgeConfiguration G,
    M.weight σ * observable σ

/-- **Finite Elitzur theorem.**  If one local gauge transformation makes an
observable odd, its complete gauge-invariant configuration-sum numerator
vanishes exactly. -/
theorem
    DynamicalTimeReversalGaugeModel.observableNumerator_eq_zero_of_gaugeOdd
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (observable : TimeReversalEdgeConfiguration G → ℝ)
    (τ : TimeReversalVertexGauge G)
    (hodd : ∀ σ,
      observable (timeReversalGaugeTransform G τ σ) = -observable σ) :
    M.observableNumerator observable = 0 := by
  have hreindex :
      M.observableNumerator observable =
        ∑ σ : TimeReversalEdgeConfiguration G,
          M.weight (timeReversalGaugeTransform G τ σ) *
            observable (timeReversalGaugeTransform G τ σ) := by
    unfold DynamicalTimeReversalGaugeModel.observableNumerator
    exact ((timeReversalGaugeEquiv G τ).sum_comp
      (fun σ => M.weight σ * observable σ)).symm
  have hneg :
      M.observableNumerator observable =
        -M.observableNumerator observable := by
    calc
      M.observableNumerator observable =
          ∑ σ : TimeReversalEdgeConfiguration G,
            M.weight (timeReversalGaugeTransform G τ σ) *
              observable (timeReversalGaugeTransform G τ σ) := hreindex
      _ = ∑ σ : TimeReversalEdgeConfiguration G,
          -(M.weight σ * observable σ) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [M.weight_gauge_invariant, hodd]
            ring
      _ = -M.observableNumerator observable := by
            rw [Finset.sum_neg_distrib]
            rfl
  linarith

@[simp] theorem z2TimeReversalSign_one :
    z2TimeReversalSign 1 = -1 := by
  norm_num [z2TimeReversalSign]

/-- The gauge-variant orientation sign on one edge. -/
def dynamicalTimeReversalEdgeSign
    (G : DynamicalTimeReversalGaugeComplex)
    (e : Fin G.skeleton.edgeCount)
    (σ : TimeReversalEdgeConfiguration G) : ℝ :=
  z2TimeReversalSign (σ e)

/-- A local gauge parameter with unit coboundary on an edge reverses that
edge's orientation observable. -/
theorem dynamicalTimeReversalEdgeSign_gauge_flip
    (G : DynamicalTimeReversalGaugeComplex)
    (e : Fin G.skeleton.edgeCount)
    (τ : TimeReversalVertexGauge G)
    (hflip : ∑ v, G.edgeBoundary e v * τ v = 1)
    (σ : TimeReversalEdgeConfiguration G) :
    dynamicalTimeReversalEdgeSign G e
        (timeReversalGaugeTransform G τ σ) =
      -dynamicalTimeReversalEdgeSign G e σ := by
  simp [dynamicalTimeReversalEdgeSign, timeReversalGaugeTransform,
    hflip, z2TimeReversalSign_add]

/-- Concrete Elitzur cancellation: whenever a local gauge transformation
flips an edge, the full finite expectation numerator of that edge sign is
zero. -/
theorem DynamicalTimeReversalGaugeModel.edgeSignNumerator_eq_zero
    {G : DynamicalTimeReversalGaugeComplex}
    (M : DynamicalTimeReversalGaugeModel G)
    (e : Fin G.skeleton.edgeCount)
    (τ : TimeReversalVertexGauge G)
    (hflip : ∑ v, G.edgeBoundary e v * τ v = 1) :
    M.observableNumerator (dynamicalTimeReversalEdgeSign G e) = 0 := by
  exact M.observableNumerator_eq_zero_of_gaugeOdd
    (dynamicalTimeReversalEdgeSign G e) τ
    (dynamicalTimeReversalEdgeSign_gauge_flip G e τ hflip)

/-! ### Triad orientation and lapse bookkeeping -/

/-- Edge time reversal multiplies every component of a three-triad by
the physical sign `±1`, as in Vaid Eq. (45). -/
def timeReversedTriad (orientation : ZMod 2)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  z2TimeReversalSign orientation • E

/-- The spatial metric generated by a real three-triad. -/
def metricFromTriad (E : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  E.transpose * E

/-- The triad orientation flip leaves the induced spatial metric unchanged. -/
theorem metricFromTriad_timeReversal_invariant
    (orientation : ZMod 2)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    metricFromTriad (timeReversedTriad orientation E) =
      metricFromTriad E := by
  ext i j
  simp only [metricFromTriad, timeReversedTriad, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ x, (z2TimeReversalSign orientation * E x i) *
        (z2TimeReversalSign orientation * E x j)) =
      z2TimeReversalSign orientation ^ 2 *
        ∑ x, E x i * E x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ x, E x i * E x j := by
      rw [z2TimeReversalSign_sq, one_mul]

/-- In three dimensions the triad determinant carries the orientation
sign, because the sign appears to the odd power three (Vaid Eq. (46)). -/
theorem det_timeReversedTriad (orientation : ZMod 2)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.det (timeReversedTriad orientation E) =
      z2TimeReversalSign orientation * Matrix.det E := by
  rw [timeReversedTriad, Matrix.det_smul, Fintype.card_fin]
  congr 1
  calc
    z2TimeReversalSign orientation ^ 3 =
        z2TimeReversalSign orientation ^ 2 *
          z2TimeReversalSign orientation := by ring
    _ = z2TimeReversalSign orientation := by
      rw [z2TimeReversalSign_sq, one_mul]

/-- If both the lapse and the spatial triad orientation reverse, the
factorized four-tetrad determinant `N * det(e)` is unchanged. -/
theorem simultaneous_lapse_triad_reversal_preserves_tetradDet
    (orientation : ZMod 2) (lapse triadDet : ℝ) :
    (z2TimeReversalSign orientation * lapse) *
        (z2TimeReversalSign orientation * triadDet) =
      lapse * triadDet := by
  calc
    (z2TimeReversalSign orientation * lapse) *
        (z2TimeReversalSign orientation * triadDet) =
      z2TimeReversalSign orientation ^ 2 *
        (lapse * triadDet) := by ring
    _ = lapse * triadDet := by
      rw [z2TimeReversalSign_sq, one_mul]

/-- With the lapse fixed, reversing only the spatial triad orientation
reverses the four-tetrad determinant.  This and the preceding theorem
separate the two lapse/orientation conventions that the paper discusses. -/
theorem fixed_lapse_triad_reversal_flips_tetradDet
    (orientation : ZMod 2) (lapse triadDet : ℝ) :
    lapse * (z2TimeReversalSign orientation * triadDet) =
      z2TimeReversalSign orientation * (lapse * triadDet) := by
  ring

/-! ## Remaining Chen--Vishwanath 2D classification data

This section records only the invariants and identifications stated in the
2015 paper.  It does not promote the static twist construction to a
dynamical gauge theory. -/

/-- The two independent `Z₂` labels of the paper's 2D
`Z₂ × Z₂ᵀ` SPT classification: the unitary-twist composition class and the
time-reversal square on a unitary `Z₂` defect. -/
structure ChenTwoDSPTClass where
  unitaryTwistNontrivial : Bool
  timeReversalDefectKramers : Bool
  deriving DecidableEq

/-- The pair of complex phases `±1` representing the two 2D SPT labels. -/
def ChenTwoDSPTClass.twistInvariant
    (C : ChenTwoDSPTClass) : ℂ × ℂ :=
  (chenProjectivePhase C.unitaryTwistNontrivial,
    chenProjectivePhase C.timeReversalDefectKramers)

/-- The sign-valued projective phase remembers its binary label. -/
theorem chenProjectivePhase_injective :
    Function.Injective chenProjectivePhase := by
  intro a b h
  cases a <;> cases b
  · rfl
  · have hr := congrArg Complex.re h
    norm_num [chenProjectivePhase] at hr
  · have hr := congrArg Complex.re h
    norm_num [chenProjectivePhase] at hr
  · rfl

/-- **Four-class completeness for the recorded invariants.**  The pair of
twist phases separates the four `Z₂ × Z₂` labels. -/
theorem ChenTwoDSPTClass.twistInvariant_injective :
    Function.Injective ChenTwoDSPTClass.twistInvariant := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only [ChenTwoDSPTClass.twistInvariant, Prod.mk.injEq] at h
  have h₁ := chenProjectivePhase_injective h.1
  have h₂ := chenProjectivePhase_injective h.2
  cases h₁
  cases h₂
  rfl

theorem ChenTwoDSPTClass.eq_iff_twistInvariants_eq
    (C D : ChenTwoDSPTClass) :
    C = D ↔ C.twistInvariant = D.twistInvariant :=
  ⟨fun h => congrArg _ h, fun h => C.twistInvariant_injective h⟩

/-- The two `Z₂` topological orders considered after gauging the unitary
subgroup. -/
inductive ChenZ2GaugeOrder where
  | toricCode
  | doubleSemion
  deriving DecidableEq

/-- The three time-reversal enriched topological orders found in the paper:
two toric-code classes and one double-semion class. -/
inductive ChenTimeReversalSETClass where
  | toricKramersEven
  | toricKramersOdd
  | doubleSemion
  deriving DecidableEq

/-- The paper's post-gauging classification map.  The defect Kramers label
distinguishes toric-code SETs but collapses in the double-semion order. -/
def chenGaugedSETClass
    (order : ChenZ2GaugeOrder) (kramersOdd : Bool) :
    ChenTimeReversalSETClass :=
  match order, kramersOdd with
  | .toricCode, false => .toricKramersEven
  | .toricCode, true => .toricKramersOdd
  | .doubleSemion, _ => .doubleSemion

@[simp] theorem chenGaugedSETClass_toric_even :
    chenGaugedSETClass .toricCode false = .toricKramersEven := rfl

@[simp] theorem chenGaugedSETClass_toric_odd :
    chenGaugedSETClass .toricCode true = .toricKramersOdd := rfl

/-- The two toric-code SET classes remain distinct after gauging. -/
theorem chenGaugedSETClass_toric_distinct :
    chenGaugedSETClass .toricCode false ≠
      chenGaugedSETClass .toricCode true := by decide

/-- `T²` on a defect is defined for the two toric-code defects.  It is
deliberately `none` for double semions because time reversal exchanges the
semion and anti-semion, so neither defect is individually invariant. -/
def chenDefectTimeReversalSquare :
    ChenTimeReversalSETClass → Option ℂ
  | .toricKramersEven => some 1
  | .toricKramersOdd => some (-1)
  | .doubleSemion => none

@[simp] theorem chenDefectTimeReversalSquare_toric (η : Bool) :
    chenDefectTimeReversalSquare
      (chenGaugedSETClass .toricCode η) =
        some (chenProjectivePhase η) := by
  cases η <;> rfl

@[simp] theorem chenDefectTimeReversalSquare_doubleSemion
    (η : Bool) :
    chenDefectTimeReversalSquare
      (chenGaugedSETClass .doubleSemion η) = none := by
  cases η <;> rfl

/-- An invertible virtual gauge change cannot turn a nonzero twist matrix
into zero.  This is the non-vacuity part of the paper's tensor-gauge
independence statement. -/
theorem chenGaugeChange_ne_zero {bondDim : Nat}
    (N Ninv M : Matrix (Fin bondDim) (Fin bondDim) ℂ)
    (hleft : Ninv * N = 1)
    (hM : M ≠ 0) :
    chenGaugeChange N Ninv M ≠ 0 := by
  intro hzero
  have hstar : Ninv.map star * N.map star = 1 := by
    have hc := congrArg
      (fun A : Matrix (Fin bondDim) (Fin bondDim) ℂ =>
        A.map (starRingEnd ℂ)) hleft
    rw [Matrix.map_mul] at hc
    simpa using hc
  apply hM
  have hrecover :
      Ninv.map star * chenGaugeChange N Ninv M * N = M := by
    unfold chenGaugeChange
    rw [show
      Ninv.map star * (N.map star * M * Ninv) * N =
        (Ninv.map star * N.map star) * M * (Ninv * N) by
          noncomm_ring]
    rw [hstar, hleft]
    simp
  rw [hzero] at hrecover
  simpa using hrecover.symm

/-! ### The paper's 3D finite-depth obstruction -/

/-- A size-indexed circuit family has uniformly finite depth when one bound
works at every system size. -/
def HasUniformFiniteDepth (depth : Nat → Nat) : Prop :=
  ∃ bound, ∀ size, depth size ≤ bound

/-- A circuit depth bounded below by system size cannot be uniformly finite.
This isolates the obstruction used by the paper for the beyond-cohomology
3D surface, without asserting the open membrane construction. -/
theorem no_uniformFiniteDepth_of_linearLowerBound
    (depth : Nat → Nat) (hlinear : ∀ size, size ≤ depth size) :
    ¬ HasUniformFiniteDepth depth := by
  rintro ⟨bound, hbound⟩
  have h₁ := hlinear (bound + 1)
  have h₂ := hbound (bound + 1)
  omega

/-! ## Infinite locally finite dynamical extension

Chen--Vishwanath explicitly leave a dynamical time-reversal gauge field as
an open question.  The following is therefore a repository extension, not a
theorem attributed to the paper.  It constructs a controlled answer on an
arbitrary (possibly infinite) cell complex whose individual boundaries have
finite support.  Time is continuous, but the spatial carrier remains a
locally finite lattice.

The evolution below is the positive unital Markov semigroup on one binary
gauge orbit.  It is not presented as the full antiunitary Hamiltonian quantum
gauge theory left open by the paper. -/

variable {Vertex Edge Plaquette : Type*}
  [DecidableEq Vertex] [DecidableEq Edge]

/-- Pair a finitely supported `Z₂` chain with an arbitrary `Z₂` cochain. -/
def z2LocalPairing {I : Type*} [DecidableEq I]
    (chain : I →₀ ZMod 2) (cochain : I → ZMod 2) : ZMod 2 :=
  chain.sum fun i coefficient => coefficient * cochain i

theorem z2LocalPairing_add_right {I : Type*} [DecidableEq I]
    (chain : I →₀ ZMod 2) (f g : I → ZMod 2) :
    z2LocalPairing chain (f + g) =
      z2LocalPairing chain f + z2LocalPairing chain g := by
  classical
  simp [z2LocalPairing, Finsupp.sum, mul_add, Finset.sum_add_distrib]

/-- A possibly infinite cellular `Z₂` gauge carrier with finite edge and
plaquette boundaries.  `boundary_boundary_zero` is the dual form of
`∂² = 0`, strong enough for arbitrary (not necessarily finitely supported)
vertex gauge parameters. -/
structure LocallyFiniteTimeReversalGaugeComplex
    (Vertex Edge Plaquette : Type*)
    [DecidableEq Vertex] [DecidableEq Edge] where
  edgeBoundary : Edge → Vertex →₀ ZMod 2
  plaquetteBoundary : Plaquette → Edge →₀ ZMod 2
  boundary_boundary_zero :
    ∀ p τ, z2LocalPairing (plaquetteBoundary p)
      (fun e => z2LocalPairing (edgeBoundary e) τ) = 0

/-- An edge configuration on a possibly infinite complex. -/
abbrev InfiniteEdgeConfiguration
    (_G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette) :=
  Edge → ZMod 2

/-- A vertex gauge parameter on a possibly infinite complex. -/
abbrev InfiniteVertexGauge
    (_G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette) :=
  Vertex → ZMod 2

/-- The local `Z₂` coboundary action on an infinite edge configuration. -/
def infiniteGaugeTransform
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G) :
    InfiniteEdgeConfiguration G :=
  fun e => σ e + z2LocalPairing (G.edgeBoundary e) τ

@[simp] theorem infiniteGaugeTransform_zero
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (σ : InfiniteEdgeConfiguration G) :
    infiniteGaugeTransform G 0 σ = σ := by
  funext e
  simp [infiniteGaugeTransform, z2LocalPairing]

/-- Infinite-volume gauge transformations compose pointwise. -/
theorem infiniteGaugeTransform_add
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ₁ τ₂ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G) :
    infiniteGaugeTransform G τ₁ (infiniteGaugeTransform G τ₂ σ) =
      infiniteGaugeTransform G (τ₁ + τ₂) σ := by
  funext e
  rw [infiniteGaugeTransform, infiniteGaugeTransform,
    infiniteGaugeTransform, z2LocalPairing_add_right]
  abel

/-- Every binary gauge transformation remains involutive at infinite
volume because every evaluated boundary is finitely supported. -/
@[simp] theorem infiniteGaugeTransform_self
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G) :
    infiniteGaugeTransform G τ (infiniteGaugeTransform G τ σ) = σ := by
  rw [infiniteGaugeTransform_add]
  have hτ : τ + τ = 0 := by
    funext v
    exact CharTwo.add_self_eq_zero (τ v)
  rw [hτ]
  exact infiniteGaugeTransform_zero G σ

/-- Locally finite flux through one plaquette. -/
def infinitePlaquetteFlux
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (σ : InfiniteEdgeConfiguration G) (p : Plaquette) : ZMod 2 :=
  z2LocalPairing (G.plaquetteBoundary p) σ

/-- Plaquette flux is gauge invariant on an arbitrary infinite carrier. -/
theorem infinitePlaquetteFlux_gauge_invariant
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G)
    (p : Plaquette) :
    infinitePlaquetteFlux G (infiniteGaugeTransform G τ σ) p =
      infinitePlaquetteFlux G σ p := by
  unfold infinitePlaquetteFlux infiniteGaugeTransform
  change z2LocalPairing (G.plaquetteBoundary p)
      (σ + fun e => z2LocalPairing (G.edgeBoundary e) τ) =
    z2LocalPairing (G.plaquetteBoundary p) σ
  rw [z2LocalPairing_add_right, G.boundary_boundary_zero, add_zero]

/-- Real multiplicative sign of a locally finite plaquette flux. -/
def infinitePlaquetteSign
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (σ : InfiniteEdgeConfiguration G) (p : Plaquette) : ℝ :=
  z2TimeReversalSign (infinitePlaquetteFlux G σ p)

theorem infinitePlaquetteSign_gauge_invariant
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G)
    (p : Plaquette) :
    infinitePlaquetteSign G (infiniteGaugeTransform G τ σ) p =
      infinitePlaquetteSign G σ p := by
  simp [infinitePlaquetteSign, infinitePlaquetteFlux_gauge_invariant]

/-- The action in an arbitrary finite plaquette window of an infinite
configuration.  No divergent infinite sum is introduced. -/
def finiteVolumeInfiniteGaugeAction
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (volume : Finset Plaquette) (K : ℝ)
    (σ : InfiniteEdgeConfiguration G) : ℝ :=
  -K * ∑ p ∈ volume, infinitePlaquetteSign G σ p

theorem finiteVolumeInfiniteGaugeAction_gauge_invariant
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (volume : Finset Plaquette) (K : ℝ)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G) :
    finiteVolumeInfiniteGaugeAction G volume K
        (infiniteGaugeTransform G τ σ) =
      finiteVolumeInfiniteGaugeAction G volume K σ := by
  unfold finiteVolumeInfiniteGaugeAction
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact infinitePlaquetteSign_gauge_invariant G τ σ p

/-- A finitely supported closed edge chain in an infinite complex. -/
structure LocallyFiniteEdgeCycle
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette) where
  incidence : Edge →₀ ZMod 2
  boundary_zero :
    ∀ τ, z2LocalPairing incidence
      (fun e => z2LocalPairing (G.edgeBoundary e) τ) = 0

/-- Flux through a finitely supported cycle. -/
def infiniteWilsonFlux
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (C : LocallyFiniteEdgeCycle G) (σ : InfiniteEdgeConfiguration G) :
    ZMod 2 :=
  z2LocalPairing C.incidence σ

theorem infiniteWilsonFlux_gauge_invariant
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (C : LocallyFiniteEdgeCycle G)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G) :
    infiniteWilsonFlux G C (infiniteGaugeTransform G τ σ) =
      infiniteWilsonFlux G C σ := by
  unfold infiniteWilsonFlux infiniteGaugeTransform
  change z2LocalPairing C.incidence
      (σ + fun e => z2LocalPairing (G.edgeBoundary e) τ) =
    z2LocalPairing C.incidence σ
  rw [z2LocalPairing_add_right, C.boundary_zero, add_zero]

/-- Wilson-loop sign on a finitely supported cycle of an infinite complex. -/
def infiniteWilsonLoop
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (C : LocallyFiniteEdgeCycle G) (σ : InfiniteEdgeConfiguration G) : ℝ :=
  z2TimeReversalSign (infiniteWilsonFlux G C σ)

theorem infiniteWilsonLoop_gauge_invariant
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (C : LocallyFiniteEdgeCycle G)
    (τ : InfiniteVertexGauge G) (σ : InfiniteEdgeConfiguration G) :
    infiniteWilsonLoop G C (infiniteGaugeTransform G τ σ) =
      infiniteWilsonLoop G C σ := by
  simp [infiniteWilsonLoop, infiniteWilsonFlux_gauge_invariant]

/-! ### Continuous-time Markov dynamics on a binary gauge orbit -/

/-- Probability of remaining at the current representative at time `t`. -/
noncomputable def gaugeStayCoefficient (t : ℝ) : ℝ :=
  (1 + Real.exp (-2 * t)) / 2

/-- Probability of moving to the gauge-related representative at time `t`. -/
noncomputable def gaugeFlipCoefficient (t : ℝ) : ℝ :=
  (1 - Real.exp (-2 * t)) / 2

theorem gaugeStayCoefficient_add_mix (s t : ℝ) :
    gaugeStayCoefficient (s + t) =
      gaugeStayCoefficient s * gaugeStayCoefficient t +
        gaugeFlipCoefficient s * gaugeFlipCoefficient t := by
  rw [gaugeStayCoefficient, gaugeStayCoefficient,
    gaugeStayCoefficient, gaugeFlipCoefficient, gaugeFlipCoefficient]
  rw [show -2 * (s + t) = -2 * s + -2 * t by ring, Real.exp_add]
  ring

theorem gaugeFlipCoefficient_add_mix (s t : ℝ) :
    gaugeFlipCoefficient (s + t) =
      gaugeStayCoefficient s * gaugeFlipCoefficient t +
        gaugeFlipCoefficient s * gaugeStayCoefficient t := by
  rw [gaugeStayCoefficient, gaugeStayCoefficient,
    gaugeFlipCoefficient, gaugeFlipCoefficient, gaugeFlipCoefficient]
  rw [show -2 * (s + t) = -2 * s + -2 * t by ring, Real.exp_add]
  ring

@[simp] theorem gaugeStayCoefficient_zero :
    gaugeStayCoefficient 0 = 1 := by
  norm_num [gaugeStayCoefficient]

@[simp] theorem gaugeFlipCoefficient_zero :
    gaugeFlipCoefficient 0 = 0 := by
  norm_num [gaugeFlipCoefficient]

/-- The two transition probabilities sum to one. -/
theorem gaugeStayCoefficient_add_flip (t : ℝ) :
    gaugeStayCoefficient t + gaugeFlipCoefficient t = 1 := by
  rw [gaugeStayCoefficient, gaugeFlipCoefficient]
  ring

theorem gaugeStayCoefficient_nonneg {t : ℝ} (_ht : 0 ≤ t) :
    0 ≤ gaugeStayCoefficient t := by
  have hexp := Real.exp_pos (-2 * t)
  rw [gaugeStayCoefficient]
  positivity

theorem gaugeFlipCoefficient_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gaugeFlipCoefficient t := by
  rw [gaugeFlipCoefficient]
  have hle : Real.exp (-2 * t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  positivity

/-- The positive-time Markov evolution of real observables on the two-point
orbit generated by one local binary gauge transformation. -/
noncomputable def gaugeOrbitMarkovEvolution
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (t : ℝ)
    (observable : InfiniteEdgeConfiguration G → ℝ) :
    InfiniteEdgeConfiguration G → ℝ :=
  fun σ =>
    observable σ * gaugeStayCoefficient t +
      observable (infiniteGaugeTransform G τ σ) * gaugeFlipCoefficient t

@[simp] theorem gaugeOrbitMarkovEvolution_zero
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G)
    (observable : InfiniteEdgeConfiguration G → ℝ) :
    gaugeOrbitMarkovEvolution G τ 0 observable = observable := by
  funext σ
  simp [gaugeOrbitMarkovEvolution]

/-- Exact semigroup composition for all real parameters; positivity is used
only on the physical half-line `t ≥ 0`. -/
theorem gaugeOrbitMarkovEvolution_add
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (s t : ℝ)
    (observable : InfiniteEdgeConfiguration G → ℝ) :
    gaugeOrbitMarkovEvolution G τ (s + t) observable =
      gaugeOrbitMarkovEvolution G τ s
        (gaugeOrbitMarkovEvolution G τ t observable) := by
  funext σ
  simp only [gaugeOrbitMarkovEvolution, infiniteGaugeTransform_self]
  rw [gaugeStayCoefficient_add_mix, gaugeFlipCoefficient_add_mix]
  ring

/-- The evolution is unital. -/
theorem gaugeOrbitMarkovEvolution_preserves_one
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (t : ℝ) :
    gaugeOrbitMarkovEvolution G τ t (fun _ => 1) = fun _ => 1 := by
  funext σ
  simp [gaugeOrbitMarkovEvolution, gaugeStayCoefficient_add_flip]

/-- The evolution preserves pointwise nonnegativity for positive time. -/
theorem gaugeOrbitMarkovEvolution_nonneg
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) {t : ℝ} (ht : 0 ≤ t)
    (observable : InfiniteEdgeConfiguration G → ℝ)
    (hobs : ∀ σ, 0 ≤ observable σ) :
    ∀ σ, 0 ≤ gaugeOrbitMarkovEvolution G τ t observable σ := by
  intro σ
  exact add_nonneg
    (mul_nonneg (hobs σ) (gaugeStayCoefficient_nonneg ht))
    (mul_nonneg (hobs (infiniteGaugeTransform G τ σ))
      (gaugeFlipCoefficient_nonneg ht))

/-- Gauge-invariant observables are fixed points of the orbit evolution. -/
theorem gaugeOrbitMarkovEvolution_fixed_of_gaugeInvariant
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (t : ℝ)
    (observable : InfiniteEdgeConfiguration G → ℝ)
    (hinv : ∀ σ, observable (infiniteGaugeTransform G τ σ) = observable σ) :
    gaugeOrbitMarkovEvolution G τ t observable = observable := by
  funext σ
  rw [gaugeOrbitMarkovEvolution, hinv, ← mul_add,
    gaugeStayCoefficient_add_flip, mul_one]

/-- Every finite-window action is fixed by the continuous-time gauge-orbit
evolution. -/
theorem gaugeOrbitMarkovEvolution_fixes_finiteVolumeAction
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (t : ℝ)
    (volume : Finset Plaquette) (K : ℝ) :
    gaugeOrbitMarkovEvolution G τ t
        (finiteVolumeInfiniteGaugeAction G volume K) =
      finiteVolumeInfiniteGaugeAction G volume K :=
  gaugeOrbitMarkovEvolution_fixed_of_gaugeInvariant G τ t _ fun σ =>
    finiteVolumeInfiniteGaugeAction_gauge_invariant G volume K τ σ

/-- Every locally finite Wilson loop is fixed by the gauge-orbit evolution. -/
theorem gaugeOrbitMarkovEvolution_fixes_infiniteWilsonLoop
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G) (t : ℝ)
    (C : LocallyFiniteEdgeCycle G) :
    gaugeOrbitMarkovEvolution G τ t (infiniteWilsonLoop G C) =
      infiniteWilsonLoop G C :=
  gaugeOrbitMarkovEvolution_fixed_of_gaugeInvariant G τ t _ fun σ =>
    infiniteWilsonLoop_gauge_invariant G C τ σ

/-- Pointwise continuity in time on the full infinite configuration space. -/
theorem gaugeOrbitMarkovEvolution_pointwise_continuous
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G)
    (observable : InfiniteEdgeConfiguration G → ℝ)
    (σ : InfiniteEdgeConfiguration G) :
    Continuous (fun t : ℝ => gaugeOrbitMarkovEvolution G τ t observable σ) := by
  unfold gaugeOrbitMarkovEvolution gaugeStayCoefficient gaugeFlipCoefficient
  fun_prop

/-- The exact right infinitesimal generator is the bounded gauge-orbit
difference `f(gτ·σ) - f(σ)`. -/
theorem gaugeOrbitMarkovEvolution_hasGenerator
    (G : LocallyFiniteTimeReversalGaugeComplex Vertex Edge Plaquette)
    (τ : InfiniteVertexGauge G)
    (observable : InfiniteEdgeConfiguration G → ℝ)
    (σ : InfiniteEdgeConfiguration G) :
    HasDerivAt
      (fun t : ℝ => gaugeOrbitMarkovEvolution G τ t observable σ)
      (observable (infiniteGaugeTransform G τ σ) - observable σ) 0 := by
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (-2) 0 := by
    convert ((hasDerivAt_id (x := 0)).const_mul (-2)).exp using 1 <;> norm_num
  have hstay :
      HasDerivAt gaugeStayCoefficient (-1) 0 := by
    change HasDerivAt
      (fun t : ℝ => (1 + Real.exp (-2 * t)) / 2) (-1) 0
    simpa [Pi.add_apply] using
      ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add hexp).div_const 2
  have hflip :
      HasDerivAt gaugeFlipCoefficient 1 0 := by
    change HasDerivAt
      (fun t : ℝ => (1 - Real.exp (-2 * t)) / 2) 1 0
    simpa [Pi.sub_apply] using
      ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub hexp).div_const 2
  have hsum := (hstay.const_mul (observable σ)).add
      (hflip.const_mul (observable (infiniteGaugeTransform G τ σ)))
  change HasDerivAt
    ((fun t => observable σ * gaugeStayCoefficient t) +
      fun t => observable (infiniteGaugeTransform G τ σ) *
        gaugeFlipCoefficient t)
    (observable (infiniteGaugeTransform G τ σ) - observable σ) 0
  simpa only [mul_neg, mul_one, sub_eq_add_neg, add_comm] using hsum

end Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversed_segment_eq_boundary where
  formalizes @ "claim:local-time-reversal-on-every-site-of-a-finite-symmetric-mps-segment-cancels-on-all-interior-virtual-bonds-and-leaves-only-M-and-M-inverse-at-the-boundaries",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-local-time-reversed-mps-tensor-is-related-to-the-original-by-the-supplied-invertible-virtual-twist",
  supported_by @ "paper:chen-vishwanath-2015-equations-6-9",
  caveat @ "claim:this-is-a-finite-injective-mps-boundary-cancellation-theorem-not-a-construction-of-a-time-reversal-gauge-field"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.insertChenTwist_twice where
  formalizes @ "claim:two-antiunitary-mps-time-reversal-twists-compose-to-the-zero-twist-times-the-projective-phase-beta-plus-or-minus-one",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:the-virtual-twist-carries-a-checked-projective-square-M-star-M-equals-beta-I",
  supported_by @ "paper:chen-vishwanath-2015-equations-14-and-18",
  caveat @ "claim:the-composition-law-extracts-the-projective-class-from-a-supplied-symmetric-mps-it-does-not-prove-that-an-arbitrary-state-has-such-an-mps-representation"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenProjectiveSquare_gauge_invariant where
  formalizes @ "claim:the-chen-vishwanath-projective-time-reversal-phase-is-invariant-under-every-invertible-change-of-mps-virtual-gauge",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:N-inverse-is-a-two-sided-matrix-inverse",
  supported_by @ "paper:chen-vishwanath-2015-equation-19"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.diracChenTwist_projectiveSquare where
  formalizes @ "claim:the-dirac-spin-one-half-time-reversal-matrix-i-gamma-one-gamma-three-realizes-the-nontrivial-chen-projective-class-M-star-M-equals-minus-I",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:chen-vishwanath-2015-equation-14",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary.IgammaT_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary.Iγ1γ3_map_star"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.diracChenTwist_spinorAction_sq where
  formalizes @ "claim:the-nontrivial-chen-virtual-twist-class-is-the-same-minus-one-projective-square-as-the-repository-dirac-antiunitary-time-reversal-on-spinors",
  epistemic_status @ "bridge-theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary.timeReversal_sq",
  caveat @ "claim:this-identifies-the-projective-algebra-it-does-not-identify-a-specific-many-body-mps-ground-state-with-a-relativistic-dirac-field"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenConfinedPEPS_energy_and_exactHaagDualityOn where
  formalizes @ "claim:a-positive-length-static-time-reversal-twist-with-positive-tension-has-positive-confinement-energy-while-the-underlying-mpo-injective-peps-retains-exact-cone-like-haag-duality",
  epistemic_status @ "conditional-model-theorem",
  requires @ "assumption:a-positive-tension-confined-time-reversal-twist-is-supplied-on-an-mpo-injective-topological-peps-with-the-existing-weak-hopf-haag-package",
  supported_by @ "paper:chen-vishwanath-2015-static-confined-time-reversal-twists",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality.tensorNetwork_exactHaagDualityOn",
  caveat @ "claim:this-does-not-construct-a-deconfined-or-dynamical-antiunitary-gauge-field-which-chen-and-vishwanath-explicitly-leave-open"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.ChenTwoDSPTClass.twistInvariant_injective where
  formalizes @ "claim:the-unitary-twist-composition-sign-and-the-time-reversal-square-on-the-orthogonal-z2-defect-separate-the-four-z2-times-z2-time-reversal-spt-labels",
  epistemic_status @ "classification-theorem",
  supported_by @ "paper:chen-vishwanath-2015-equations-35-37-and-section-III",
  caveat @ "claim:this-formalizes-injectivity-of-the-two-paper-invariants-on-the-stated-four-label-carrier-not-completeness-of-an-arbitrary-continuum-many-body-phase-classification"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenGaugedSETClass_toric_distinct where
  formalizes @ "claim:gauging-the-unitary-z2-subgroup-leaves-two-distinct-toric-code-time-reversal-enriched-orders-distinguished-by-defect-T-square-plus-or-minus-one",
  epistemic_status @ "classification-theorem",
  supported_by @ "paper:chen-vishwanath-2015-section-IV",
  caveat @ "claim:the-map-records-the-paper-classification-it-does-not-construct-a-dynamical-antiunitary-gauge-hamiltonian"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenGaugeChange_ne_zero where
  formalizes @ "claim:an-invertible-virtual-tensor-gauge-change-preserves-nonvanishing-of-the-time-reversal-twist",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-supplied-left-inverse-is-exact",
  supported_by @ "paper:chen-vishwanath-2015-equation-19",
  caveat @ "claim:this-is-the-non-vacuity-part-of-gauge-choice-independence-not-an-existence-theorem-for-a-tensor-network-representation"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.no_uniformFiniteDepth_of_linearLowerBound where
  formalizes @ "claim:a-circuit-family-whose-depth-is-at-least-the-linear-system-size-cannot-be-a-uniform-finite-depth-inner-symmetry",
  epistemic_status @ "obstruction-theorem",
  requires @ "assumption:the-paper-surface-time-reversal-implementation-has-the-stated-linear-depth-lower-bound",
  supported_by @ "paper:chen-vishwanath-2015-three-dimensional-beyond-cohomology-discussion",
  caveat @ "claim:this-is-only-the-finite-depth-obstruction-the-paper-explicitly-leaves-the-detailed-three-dimensional-twist-membrane-study-open"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.infinitePlaquetteFlux_gauge_invariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.z2LocalPairing_add_right",
  formalizes @ "extension:a-locally-finite-z2-cell-complex-supports-gauge-invariant-plaquette-flux-at-every-plaquette-even-when-the-global-vertex-edge-and-plaquette-types-are-infinite",
  epistemic_status @ "repository-extension",
  requires @ "assumption:each-cell-boundary-has-finite-support-and-the-supplied-cellular-boundary-squares-to-zero",
  motivated_by @ "open-question:chen-vishwanath-2015-dynamical-time-reversal-gauge-field",
  caveat @ "claim:this-is-an-infinite-locally-finite-lattice-extension-not-a-continuum-spacetime-field-or-a-theorem-claimed-in-the-2015-paper"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_add where
  formalizes @ "extension:the-explicit-binary-gauge-orbit-evolution-is-an-exact-continuous-time-semigroup-on-real-observables-over-the-infinite-configuration-space",
  epistemic_status @ "repository-extension",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.infiniteGaugeTransform_self",
  motivated_by @ "open-question:chen-vishwanath-2015-quantum-dynamics-of-a-time-reversal-gauge-field",
  caveat @ "claim:this-is-a-classical-positive-unital-Markov-orbit-semigroup-not-the-full-antiunitary-Hamiltonian-quantum-gauge-theory-left-open-by-the-paper"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_hasGenerator where
  formalizes @ "extension:the-pointwise-infinitesimal-generator-of-the-gauge-orbit-semigroup-is-exactly-the-bounded-difference-f-of-gauge-transform-minus-f",
  epistemic_status @ "repository-extension",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_add",
  motivated_by @ "open-question:chen-vishwanath-2015-quantum-dynamics-of-a-time-reversal-gauge-field",
  caveat @ "claim:the-derivative-is-pointwise-on-real-observables-and-does-not-assert-norm-C-zero-closure-a-quantum-Hamiltonian-or-a-continuum-spacetime-generator"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_fixes_finiteVolumeAction where
  formalizes @ "extension:every-finite-window-action-and-every-locally-finite-Wilson-loop-is-fixed-by-the-continuous-time-gauge-orbit-semigroup",
  epistemic_status @ "repository-extension",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.finiteVolumeInfiniteGaugeAction_gauge_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_fixes_infiniteWilsonLoop",
  caveat @ "claim:fixed-gauge-invariant-observables-do-not-prove-deconfinement-an-area-law-or-the-full-dynamical-gauging-left-open-in-2015"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversalGaugeTransform_add where
  formalizes @ "claim:local-z2-time-reversal-gauge-transformations-on-a-finite-spin-network-compose-by-pointwise-z2-addition-and-each-transformation-is-involutive",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:vaid-2026-edge-gauge-transformation-after-equation-48",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution.SpinNetworkSkeleton",
  caveat @ "claim:this-is-the-finite-cellular-gauge-action-not-a-construction-of-the-paper-cosmological-running-coupling-or-full-spin-foam-history"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversalPlaquetteFlux_gauge_invariant where
  formalizes @ "claim:the-z2-flux-through-every-plaquette-is-invariant-under-every-local-vertex-time-reversal-gauge-transformation",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-supplied-finite-spin-network-two-complex-satisfies-the-cellular-boundary-of-boundary-zero-identity",
  supported_by @ "paper:vaid-2026-equation-48-and-local-gauge-invariance",
  caveat @ "claim:gauge-invariance-is-proved-from-boundary-squared-zero-but-the-two-complex-and-its-incidence-maps-are-input-data"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.dynamicalTimeReversalGaugeAction_gauge_invariant where
  formalizes @ "claim:the-finite-dynamical-time-reversal-action-S-z2-equals-minus-K-times-the-sum-of-plaquette-signs-is-locally-gauge-invariant",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:vaid-2026-equation-48",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversalPlaquetteFlux_gauge_invariant",
  caveat @ "claim:this-proves-invariance-for-every-real-K-it-does-not-derive-K-from-spin-foam-amplitudes"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.shiftedDynamicalTimeReversalWilsonAction_eq_action_add_constant where
  formalizes @ "claim:the-repository-nonnegative-Wilson-action-convention-differs-from-the-paper-dynamical-time-reversal-action-only-by-K-times-the-number-of-plaquettes",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:vaid-2026-equation-48",
  supported_by @ "lean:Physlib.QFT.Lattice.WilsonLoopAreaLaw.wilsonAction",
  caveat @ "claim:the-constant-shift-preserves-normalized-observables-but-is-not-a-proof-of-a-confinement-deconfinement-phase-transition"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.dynamicalTimeReversalWilsonLoop_gauge_invariant where
  formalizes @ "claim:every-closed-z2-Wilson-loop-observable-is-invariant-under-local-time-reversal-gauge-transformations",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-supplied-edge-chain-has-zero-cellular-boundary-at-every-vertex",
  supported_by @ "paper:vaid-2026-equation-50",
  caveat @ "claim:this-is-exact-finite-gauge-invariance-not-the-paper-cited-area-law-or-perimeter-law"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.partition_pos where
  formalizes @ "claim:the-finite-geometry-coupled-configuration-sum-Z-equals-sum-over-sigma-of-exp-minus-S-z2-times-Z-geometry-is-strictly-positive",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-supplied-finite-geometry-weight-is-strictly-positive-and-locally-gauge-invariant",
  supported_by @ "paper:vaid-2026-equation-49",
  caveat @ "claim:this-constructs-and-bounds-the-finite-partition-sum-not-a-continuum-or-spin-foam-measure"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.abs_wilsonExpectation_le_one where
  formalizes @ "claim:the-normalized-finite-Wilson-loop-expectation-for-the-dynamical-time-reversal-gauge-model-has-absolute-value-at-most-one",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:vaid-2026-equation-50",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.partition_pos",
  caveat @ "claim:boundedness-and-gauge-invariance-do-not-supply-the-confined-area-law-or-deconfined-perimeter-law-which-remain-phase-inputs"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.edgeSignNumerator_eq_zero where
  formalizes @ "claim:finite-Elitzur-cancellation-a-local-edge-orientation-observable-that-is-flipped-by-a-local-gauge-transformation-has-zero-full-configuration-sum-expectation-numerator",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:there-exists-a-supplied-local-vertex-gauge-parameter-whose-coboundary-is-one-on-the-selected-edge",
  supported_by @ "paper:vaid-2026-section-9-1-Elitzur-theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.weight_gauge_invariant",
  caveat @ "claim:this-is-an-exact-finite-cancellation-theorem-for-a-gauge-odd-observable-not-spontaneous-breaking-of-a-local-gauge-symmetry"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.metricFromTriad_timeReversal_invariant where
  formalizes @ "claim:multiplying-a-real-three-triad-by-the-z2-orientation-sign-leaves-its-induced-spatial-metric-E-transpose-E-unchanged",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:vaid-2026-equation-45",
  caveat @ "claim:this-is-the-pointwise-three-by-three-triad-identity-not-a-global-tetrad-bundle-or-spin-foam-dynamics-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.det_timeReversedTriad where
  formalizes @ "claim:time-reversing-a-three-dimensional-triad-multiplies-its-determinant-by-the-z2-orientation-sign",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:vaid-2026-equation-46"

zil attach Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.simultaneous_lapse_triad_reversal_preserves_tetradDet where
  formalizes @ "claim:simultaneously-reversing-the-lapse-sign-and-spatial-triad-orientation-preserves-the-factorized-four-tetrad-determinant",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:vaid-2026-section-9-2-lapse-and-orientation-discussion",
  caveat @ "claim:with-fixed-lapse-only-the-four-tetrad-determinant-flips-as-proved-separately-so-the-two-conventions-must-not-be-conflated"

zil_file_contract physlib.tensorNetworksComplexQuantumSystems where
  promises "Tensor-network-local and dynamical time-reversal infrastructure with explicit epistemic separation: the Chen-Vishwanath 2015 layer proves finite MPS cancellation, projective-twist gauge independence, the four 2D SPT labels, the three post-gauging SET classes, and the stated 3D finite-depth obstruction; the finite Vaid layer proves cellular action, partition-sum, Wilson-loop, and Elitzur identities; and a separately labelled repository extension constructs an infinite locally finite spatial carrier with a continuous-time positive unital gauge-orbit semigroup, its pointwise generator, and fixed gauge-invariant finite-window observables."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.TimeReversalSymmetricMPSData",
    "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.ChenTimeReversalTwist",
    "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.MPOInjectivePEPSHaagInterface",
    "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.ChenTwoDSPTClass",
    "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeComplex",
    "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel",
    "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.LocallyFiniteTimeReversalGaugeComplex",
    "lean:Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution.SpinNetworkSkeleton",
    "lean:Physlib.QFT.Lattice.WilsonLoopAreaLaw.wilsonAction",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary.timeReversal"]
  forbids_substitutes ["calling entrywise complex conjugation a unitary local action",
    "claiming the projective composition identity constructs a symmetric MPS for an arbitrary many-body state",
    "claiming finite gauge invariance derives the confinement-deconfinement transition or its critical coupling",
    "claiming the coupling K or its cosmological running has been derived from spin-foam amplitudes",
    "claiming the finite geometry weight is a constructed continuum or spin-foam path-integral measure",
    "attributing the infinite-lattice continuous-time Markov extension to Chen-Vishwanath 2015",
    "calling the gauge-orbit Markov semigroup a full antiunitary Hamiltonian quantum gauge theory or a continuum spacetime construction",
    "claiming the 3D linear-depth obstruction supplies the twist-membrane construction that the paper leaves open",
    "conflating reversal of the spatial triad at fixed lapse with simultaneous reversal of both lapse and triad",
    "identifying the virtual Dirac projective class with a concrete relativistic many-body ground state without a carrier map",
    "presenting the double-semion collapse of the Kramers label as derived, when chenGaugedSETClass transcribes the paper's classification table and its double-semion arm ignores the label by construction"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.virtualGaugeTransform_mul,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeTransformSegment_eq_boundary,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversed_segment_eq_boundary,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenProjectivePhase_sq,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.insertChenTwist_twice,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenProjectiveSquare_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.diracChenTwist_projectiveSquare,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.diracChenTwist_twice,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.diracChenTwist_spinorAction_sq,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.confinedTimeReversalTwistEnergy_pos,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenConfinedPEPS_energy_and_exactHaagDualityOn,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.ChenTwoDSPTClass.twistInvariant_injective,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenGaugedSETClass_toric_distinct,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.chenGaugeChange_ne_zero,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.no_uniformFiniteDepth_of_linearLowerBound,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversalGaugeTransform_add,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversalGaugeTransform_self,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.timeReversalPlaquetteFlux_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.dynamicalTimeReversalGaugeAction_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.shiftedDynamicalTimeReversalWilsonAction_nonneg,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.shiftedDynamicalTimeReversalWilsonAction_eq_action_add_constant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.dynamicalTimeReversalWilsonLoop_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.partition_pos,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.partition_gauge_reindex,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.abs_wilsonExpectation_le_one,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.observableNumerator_eq_zero_of_gaugeOdd,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.dynamicalTimeReversalEdgeSign_gauge_flip,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.edgeSignNumerator_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.metricFromTriad_timeReversal_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.det_timeReversedTriad,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.simultaneous_lapse_triad_reversal_preserves_tetradDet,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.fixed_lapse_triad_reversal_flips_tetradDet,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.infiniteGaugeTransform_add,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.infinitePlaquetteFlux_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.finiteVolumeInfiniteGaugeAction_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.infiniteWilsonLoop_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_add,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_preserves_one,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_nonneg,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_fixes_finiteVolumeAction,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_fixes_infiniteWilsonLoop,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_pointwise_continuous,
    Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.gaugeOrbitMarkovEvolution_hasGenerator]

/- ZIL-END -/
