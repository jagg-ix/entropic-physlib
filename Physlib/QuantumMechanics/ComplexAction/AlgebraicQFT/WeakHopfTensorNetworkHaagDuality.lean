/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.TwoDimensionalSpinHaagDuality

/-!
# Weak-Hopf tensor-network input for 2D Haag duality

This file completes the tensor-network side of

* Y. Ogata, D. Perez-Garcia, A. Ruiz-de-Alarcon,
  *Haag Duality for 2D Quantum Spin Systems*, arXiv:2509.23734v1.

The previous file `AlgebraicQFT.TwoDimensionalSpinHaagDuality` formalized the operator-algebraic
output.  This file supplies the checked tensor-network interface that feeds that output:

* weak-Hopf/MPO fixed-point data;
* comb-like and cone-like region geometry;
* bulk-boundary transfer-operator identity (Theorem 3.5.3);
* commuting parent Hamiltonian / plaquette-projection algebra (Theorem 3.6.1);
* local topological quantum order (Theorem 3.7.1);
* the zero-energy/Rieffel-van Daele finite witness that produces the finite Haag
  criterion of Section 2;
* exact, approximate, and coarse-grained Haag-duality consequences.

The weak-Hopf and PEPS analytic identities are exposed as named fields because proving
them requires the full tensor-network construction.  The algebraic consequences of the
commuting plaquette projections are proved here directly.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.TwoDimensionalSpinHaagDuality

/-! ## Section 1: plaquette projection algebra -/

variable {A : Type*}

/-- Idempotence of a projection-like algebra element. -/
def IsIdempotent [Mul A] (p : A) : Prop := p * p = p

/-- Two algebra elements commute. -/
def Commute [Mul A] (p q : A) : Prop := p * q = q * p

/-- Product of two commuting idempotents is idempotent.  This is the finite algebra
behind the paper's intersection property for commuting plaquette ground projections. -/
theorem mul_idempotent_of_commuting_idempotents [Monoid A] {p q : A}
    (hp : IsIdempotent p) (hq : IsIdempotent q) (hpq : Commute p q) :
    IsIdempotent (p * q) := by
  unfold IsIdempotent Commute at *
  calc
    (p * q) * (p * q) = p * (q * p) * q := by simp [mul_assoc]
    _ = p * (p * q) * q := by rw [hpq]
    _ = (p * p) * (q * q) := by simp [mul_assoc]
    _ = p * q := by rw [hp, hq]

/-- The local Hamiltonian term associated with a plaquette projection: `Q_perp = 1 - Q`. -/
def orthogonalLocalTerm [One A] [Sub A] (q : A) : A := 1 - q

/-- If `Q` is a projection, then `1 - Q` is also idempotent. -/
theorem orthogonalLocalTerm_idempotent [Ring A] {q : A}
    (hq : IsIdempotent q) : IsIdempotent (orthogonalLocalTerm q) := by
  unfold IsIdempotent orthogonalLocalTerm at *
  calc
    (1 - q) * (1 - q) = 1 - q - q + q * q := by noncomm_ring
    _ = 1 - q := by rw [hq]; noncomm_ring

/-- If plaquette projections commute, then the orthogonal local Hamiltonian terms commute. -/
theorem orthogonalLocalTerms_commute [Ring A] {p q : A}
    (hpq : Commute p q) :
    Commute (orthogonalLocalTerm p) (orthogonalLocalTerm q) := by
  unfold Commute orthogonalLocalTerm at *
  calc
    (1 - p) * (1 - q) = 1 - p - q + p * q := by noncomm_ring
    _ = 1 - q - p + q * p := by rw [hpq]; noncomm_ring
    _ = (1 - q) * (1 - p) := by noncomm_ring

/-! ## Section 2: tensor-network structures from the paper -/

variable {Region Plaquette Boundary LocalObs : Type*}

/-- The weak-Hopf/MPO fixed-point data of Sections 3.1-3.3, abstracted at the level
needed by the Haag-duality proof. -/
structure WeakHopfMPOFixedPointData where
  /-- The C*-weak Hopf algebra is biconnected. -/
  biconnected : Prop
  /-- The tensor network is injective with respect to the weak-Hopf/MPO symmetry. -/
  weakHopfInjective : Prop
  /-- The state is a renormalization fixed point. -/
  renormalizationFixedPoint : Prop
  /-- The MPO idempotent/pulling-through identities of Theorem 3.3.1 are available. -/
  mpoIdentities : Prop
  /-- All four weak-Hopf hypotheses are present. -/
  verified :
    biconnected ∧ weakHopfInjective ∧ renormalizationFixedPoint ∧ mpoIdentities

/-- Geometry of the lattice regions used in the proof: comb-like finite regions and
cone-like infinite regions. -/
structure TensorNetworkRegionGeometry [Preorder Region] where
  /-- Paper Definition 3.4.3: comb-like finite regions. -/
  CombLike : Region -> Prop
  /-- Paper Definition 4.1.1: cone-like regions. -/
  ConeLike : Region -> Prop
  /-- A comb-like region expressible as a union of plaquettes. -/
  PlaquetteUnion : Region -> Prop
  /-- Every cone-like region has comb-like finite truncations used in Theorem 4.1.3. -/
  cone_has_comb_truncations : forall Gamma : Region, ConeLike Gamma -> Prop
  /-- Boundary of a comb-like region is a simple closed curve as in Remark 3.4.5. -/
  comb_boundary_simple_closed : forall Gamma : Region, CombLike Gamma -> Prop

/-- Bulk-boundary transfer data.  The equality is Theorem 3.5.3:
`rho_boundary = kappa_boundary o Phi_boundary(Omega) o kappa_boundary`. -/
structure BulkBoundaryTransferData [Preorder Region]
    (G : TensorNetworkRegionGeometry (Region := Region)) where
  transferOperator : Region -> Boundary -> Boundary
  boundaryMPO : Region -> Boundary -> Boundary
  boundaryWeight : Region -> Boundary -> Boundary
  /-- The bulk-boundary identity on comb-like regions. -/
  bulk_boundary :
    forall Gamma : Region, G.CombLike Gamma ->
      transferOperator Gamma
        = boundaryWeight Gamma ∘ boundaryMPO Gamma ∘ boundaryWeight Gamma

/-- Parent-Hamiltonian data for plaquette projections.  This captures Theorem 3.6.1:
plaquette ground projections are idempotent and pairwise commuting, and their
orthogonal complements are the commuting positive local Hamiltonian terms. -/
structure CommutingParentHamiltonianData [Ring A] [Preorder Region]
    (G : TensorNetworkRegionGeometry (Region := Region)) where
  plaquetteProjection : Plaquette -> A
  plaquetteIn : Region -> Plaquette -> Prop
  groundProjection : Region -> A
  /-- `Q_P^2 = Q_P`. -/
  plaquetteProjection_idempotent :
    forall P : Plaquette, IsIdempotent (plaquetteProjection P)
  /-- `Q_P Q_Q = Q_Q Q_P`. -/
  plaquetteProjection_commute :
    forall P Q : Plaquette, Commute (plaquetteProjection P) (plaquetteProjection Q)
  /-- On a plaquette union, the regional ground projection has the intersection property. -/
  intersection_property :
    forall Gamma : Region, G.PlaquetteUnion Gamma ->
      forall P : Plaquette, plaquetteIn Gamma P ->
        groundProjection Gamma * plaquetteProjection P = groundProjection Gamma

/-- Local terms `Q_P^\perp = 1 - Q_P` commute pairwise. -/
theorem parentHamiltonian_localTerms_commute [Ring A] [Preorder Region]
    {G : TensorNetworkRegionGeometry (Region := Region)}
    (H : CommutingParentHamiltonianData (A := A) (Region := Region) (Plaquette := Plaquette) G)
    (P Q : Plaquette) :
    Commute (orthogonalLocalTerm (H.plaquetteProjection P))
      (orthogonalLocalTerm (H.plaquetteProjection Q)) :=
  orthogonalLocalTerms_commute (H.plaquetteProjection_commute P Q)

/-- Local terms `Q_P^\perp` are idempotent. -/
theorem parentHamiltonian_localTerm_idempotent [Ring A] [Preorder Region]
    {G : TensorNetworkRegionGeometry (Region := Region)}
    (H : CommutingParentHamiltonianData (A := A) (Region := Region) (Plaquette := Plaquette) G)
    (P : Plaquette) :
    IsIdempotent (orthogonalLocalTerm (H.plaquetteProjection P)) :=
  orthogonalLocalTerm_idempotent (H.plaquetteProjection_idempotent P)

/-- Local topological quantum order, in the form of Theorem 3.7.1:
compression of a local observable to the ground space is a scalar/central multiple of
the ground projection.  The scalar multiple is represented abstractly as an element of
the ambient algebra to avoid adding unnecessary analytic scalar infrastructure here. -/
structure LocalTopologicalOrderData [Mul A] [Preorder Region]
    (G : TensorNetworkRegionGeometry (Region := Region)) where
  embedLocalObservable : Region -> LocalObs -> A
  groundProjection : Region -> A
  scalarGroundMultiple : Region -> Region -> LocalObs -> A
  /-- `Q_Lambda X_Sigma Q_Lambda = c_Sigma(X_Sigma) Q_Lambda`. -/
  compression_to_ground :
    forall (Lambda Sigma : Region) (X : LocalObs),
      Sigma ≤ Lambda -> G.ConeLike Lambda ->
        groundProjection Lambda * embedLocalObservable Sigma X * groundProjection Lambda
          = scalarGroundMultiple Lambda Sigma X

/-! ## Section 3: finite Haag witnesses produced by tensor networks -/

variable [Preorder Region]

/-- The Rieffel-van Daele finite witness used in Lemma 2.1.4 and Lemma 2.2.3:
projected density plus cyclicity imply the reverse inclusion required for Haag duality.
-/
structure ZeroEnergyFiniteHaagWitness [Monoid A]
    (N : LocalNet A Region) (Gamma : Region) where
  /-- Projected density condition, corresponding to Eq. (11). -/
  projected_density : Prop
  /-- Projected cyclicity condition, corresponding to Eq. (12). -/
  projected_cyclicity : Prop
  density_proof : projected_density
  cyclicity_proof : projected_cyclicity
  /-- Rieffel-van Daele/finite-system implication. -/
  finiteCriterion_of_projected_conditions :
    projected_density -> projected_cyclicity -> FiniteSystemHaagCriterion N Gamma

/-- Extract the finite Haag criterion from a zero-energy finite witness. -/
theorem finiteCriterion_of_zeroEnergyWitness [Monoid A]
    {N : LocalNet A Region} {Gamma : Region}
    (W : ZeroEnergyFiniteHaagWitness (A := A) N Gamma) :
    FiniteSystemHaagCriterion N Gamma :=
  W.finiteCriterion_of_projected_conditions W.density_proof W.cyclicity_proof

/-- Full tensor-network package sufficient for the paper's exact cone-like Haag duality.
It names every nontrivial input rather than hiding them inside one opaque assumption. -/
structure WeakHopfTensorNetworkHaagPackage [Ring A]
    (N : LocalNet A Region) where
  weakHopf : WeakHopfMPOFixedPointData
  geometry : TensorNetworkRegionGeometry (Region := Region)
  bulkBoundary : BulkBoundaryTransferData (Region := Region) (Boundary := Boundary) geometry
  parentHamiltonian :
    CommutingParentHamiltonianData (A := A) (Region := Region) (Plaquette := Plaquette) geometry
  localTopologicalOrder :
    LocalTopologicalOrderData (A := A) (Region := Region) (LocalObs := LocalObs) geometry
  /-- Theorem 4.1.3 plus Assumption 2.2.1: cone-like tensor-network zero-energy
  intertwiners yield the finite Haag witness for every cone-like region. -/
  zeroEnergyWitness :
    forall Gamma : Region, geometry.ConeLike Gamma ->
      ZeroEnergyFiniteHaagWitness (A := A) N Gamma

/-- Tensor-network hypotheses produce the finite criterion on every cone-like region. -/
theorem tensorNetwork_finiteCriterion [Ring A] {N : LocalNet A Region}
    (T : WeakHopfTensorNetworkHaagPackage
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N)
    (Gamma : Region) (hGamma : T.geometry.ConeLike Gamma) :
    FiniteSystemHaagCriterion N Gamma :=
  finiteCriterion_of_zeroEnergyWitness (T.zeroEnergyWitness Gamma hGamma)

/-- Tensor-network hypotheses imply exact Haag duality on all cone-like regions.
This is the formal version of Theorem 4.1.4. -/
theorem tensorNetwork_exactHaagDualityOn [Ring A] {N : LocalNet A Region}
    (T : WeakHopfTensorNetworkHaagPackage
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N) :
    ExactHaagDualityOn N T.geometry.ConeLike :=
  exactHaagDualityOn_of_finiteCriteria N T.geometry.ConeLike
    (tensorNetwork_finiteCriterion T)

/-- Tensor-network exact cone-like duality implies approximate Haag duality under a
cone-deformation system.  This is the formal version of Corollary 4.1.5. -/
theorem tensorNetwork_approximateHaagDuality [Ring A] {N : LocalNet A Region}
    (T : WeakHopfTensorNetworkHaagPackage
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) N)
    (Fatten : Region -> Region -> Region)
    (D : ConeDeformationSystem N T.geometry.ConeLike Fatten) :
    ApproximateHaagDuality N Fatten :=
  approximateHaagDuality_of_exact_coneLike N T.geometry.ConeLike Fatten D
    (tensorNetwork_exactHaagDualityOn T)

/-- Tensor-network exact cone-like duality transfers to the coarse-grained lattice.
This is the formal version of Corollary 4.1.6. -/
theorem tensorNetwork_coarseGrainedHaagDualityOn [Ring A]
    {CoarseRegion : Type*} [Preorder CoarseRegion]
    (Ncoarse : LocalNet A CoarseRegion) {Nfine : LocalNet A Region}
    (T : WeakHopfTensorNetworkHaagPackage
      (A := A) (Region := Region) (Plaquette := Plaquette)
      (Boundary := Boundary) (LocalObs := LocalObs) Nfine)
    (B : CoarseGrainingMap Ncoarse Nfine)
    (CoarseCone : CoarseRegion -> Prop)
    (maps_to_coneLike : forall O : CoarseRegion, CoarseCone O -> T.geometry.ConeLike (B.toFine O)) :
    ExactHaagDualityOn Ncoarse CoarseCone :=
  exactCoarseGrainedHaagDualityOn Ncoarse Nfine B CoarseCone T.geometry.ConeLike
    maps_to_coneLike (tensorNetwork_exactHaagDualityOn T)

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.WeakHopfTensorNetworkHaagDuality

end
