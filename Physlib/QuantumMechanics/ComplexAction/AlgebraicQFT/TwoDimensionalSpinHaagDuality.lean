/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KalnayLocalAQFTCompleteness

/-!
# Haag duality for two-dimensional quantum spin systems

Formalizes the operator-algebraic skeleton of

* Y. Ogata, D. Perez-Garcia, A. Ruiz-de-Alarcon,
  *Haag Duality for 2D Quantum Spin Systems*, arXiv:2509.23734v1.

The paper proves Haag duality for cone-like regions in two-dimensional weak-Hopf
tensor-network spin systems, derives approximate Haag duality for geometric cones by a
finite cone deformation, and obtains exact Haag duality on a coarse-grained lattice.

The analytic/tensor-network part of the paper is not compressed into a fake finite
matrix proof here.  Instead this file captures the checked local-net content that the
paper uses downstream:

* exact Haag duality is the equality `R(Gamma^c)' = R(Gamma)`;
* the finite-system/Rieffel-van Daele criterion is represented by the reverse inclusion
  needed to saturate locality;
* exact duality on cone-like regions implies approximate cone duality after a finite
  cone deformation;
* exact duality transfers across a coarse-graining map whose local algebras and
  complement algebras agree with the fine model;
* the result is linked to the repo's Verch/Kalnay local-AQFT completeness package.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.TwoDimensionalSpinHaagDuality

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KalnayLocalAQFTCompleteness

variable {A : Type*} [Monoid A]
variable {Region : Type*} [Preorder Region]

/-! ## Section 1: exact Haag duality and the finite-system criterion -/

/-- Exact Haag duality on a selected class of regions, e.g. the paper's cone-like lattice
regions `Gamma`. -/
def ExactHaagDualityOn (N : LocalNet A Region) (RegionClass : Region -> Prop) : Prop :=
  forall Gamma : Region, RegionClass Gamma -> HaagDuality N Gamma

/-- The finite-system/zero-energy entanglement criterion of Section 2 reduced to the
operator-algebraic conclusion it supplies: the reverse inclusion
`R(Gamma^c)' subset R(Gamma)`.  Locality already gives the other inclusion. -/
def FiniteSystemHaagCriterion (N : LocalNet A Region) (Gamma : Region) : Prop :=
  commutant (N.alg (N.compl Gamma)) ⊆ N.alg Gamma

/-- The finite-system criterion is exactly the missing half of Haag duality: combined
with ordinary locality of the net, it yields `R(Gamma^c)' = R(Gamma)`. -/
theorem finiteSystemCriterion_implies_haagDuality
    (N : LocalNet A Region) (Gamma : Region)
    (hcrit : FiniteSystemHaagCriterion N Gamma) :
    HaagDuality N Gamma :=
  (haagDuality_iff N).2 hcrit

/-- Conversely, exact Haag duality supplies the finite-system reverse inclusion. -/
theorem haagDuality_implies_finiteSystemCriterion
    (N : LocalNet A Region) (Gamma : Region)
    (hdual : HaagDuality N Gamma) :
    FiniteSystemHaagCriterion N Gamma :=
  (haagDuality_iff N).1 hdual

/-- The paper's finite criterion, when available on all cone-like regions, gives exact
Haag duality on all cone-like regions. -/
theorem exactHaagDualityOn_of_finiteCriteria
    (N : LocalNet A Region) (ConeLike : Region -> Prop)
    (hcrit : forall Gamma : Region, ConeLike Gamma -> FiniteSystemHaagCriterion N Gamma) :
    ExactHaagDualityOn N ConeLike :=
  fun Gamma hGamma => finiteSystemCriterion_implies_haagDuality N Gamma (hcrit Gamma hGamma)

/-! ## Section 2: cone deformations and approximate Haag duality -/

/-- A cone-deformation system as in Appendix A of the paper.  For each geometric cone
`Lambda` and allowed fattening parameter `eps`, it chooses a cone-like lattice region
`approxRegion Lambda eps` between `Lambda` and its fattening.  The last field records
the complement-side monotonicity needed to pass from `R(Lambda^c)'` to
`R(approxRegion^c)'`. -/
structure ConeDeformationSystem
    (N : LocalNet A Region) (ConeLike : Region -> Prop)
    (Fatten : Region -> Region -> Region) where
  /-- The cone-like region `Gamma_{eps,Lambda}` used to approximate `Lambda`. -/
  approxRegion : Region -> Region -> Region
  /-- The chosen approximation is cone-like. -/
  cone_like : forall Lambda eps : Region, ConeLike (approxRegion Lambda eps)
  /-- The approximation lies inside the fattened cone. -/
  approx_le_fatten : forall Lambda eps : Region, approxRegion Lambda eps ≤ Fatten Lambda eps
  /-- Complement-side monotonicity for the commutants:
  `R(Lambda^c)' subset R(Gamma_{eps,Lambda}^c)'`. -/
  complement_commutant_mono :
    forall Lambda eps : Region,
      commutant (N.alg (N.compl Lambda))
        ⊆ commutant (N.alg (N.compl (approxRegion Lambda eps)))

/-- Approximate Haag duality in the identity-unitary, zero-error form obtained in
Appendix A: every observable commuting with the complement of `Lambda` is contained in
the algebra of a fattened cone.  The paper phrases this as approximate Haag duality with
`U_{Lambda,eps} = 1`, `R = 0`, and error function `f = 0`. -/
def ApproximateHaagDuality
    (N : LocalNet A Region) (Fatten : Region -> Region -> Region) : Prop :=
  forall Lambda eps : Region,
    commutant (N.alg (N.compl Lambda)) ⊆ N.alg (Fatten Lambda eps)

/-- Exact Haag duality on cone-like approximants implies approximate Haag duality for
geometric cones.  This is the abstract local-net content of Appendix A and Corollary
4.1.5. -/
theorem approximateHaagDuality_of_exact_coneLike
    (N : LocalNet A Region) (ConeLike : Region -> Prop)
    (Fatten : Region -> Region -> Region)
    (D : ConeDeformationSystem N ConeLike Fatten)
    (hdual : ExactHaagDualityOn N ConeLike) :
    ApproximateHaagDuality N Fatten := by
  intro Lambda eps x hx
  have hxApprox :
      x ∈ commutant (N.alg (N.compl (D.approxRegion Lambda eps))) :=
    D.complement_commutant_mono Lambda eps hx
  have hGamma : HaagDuality N (D.approxRegion Lambda eps) :=
    hdual (D.approxRegion Lambda eps) (D.cone_like Lambda eps)
  have hxGamma : x ∈ N.alg (D.approxRegion Lambda eps) := by
    rw [← hGamma]
    exact hxApprox
  exact N.isotony (D.approx_le_fatten Lambda eps) hxGamma

/-! ## Section 3: coarse-grained exact Haag duality -/

/-- A coarse-graining map from a coarse lattice net to a fine lattice net.  The paper's
Corollary 4.1.6 uses that cones in the blocked lattice correspond to cone-like regions
in the original lattice. -/
structure CoarseGrainingMap
    (Ncoarse : LocalNet A Region) {FineRegion : Type*} [Preorder FineRegion]
    (Nfine : LocalNet A FineRegion) where
  /-- A coarse region represented as a fine cone-like region. -/
  toFine : Region -> FineRegion
  /-- Local algebras agree after blocking. -/
  alg_eq : forall O : Region, Ncoarse.alg O = Nfine.alg (toFine O)
  /-- Complement algebras agree after blocking. -/
  compl_alg_eq :
    forall O : Region,
      Ncoarse.alg (Ncoarse.compl O) = Nfine.alg (Nfine.compl (toFine O))

/-- Exact Haag duality transfers from the fine cone-like model to the coarse-grained
model whenever the local algebras and complement algebras match under blocking. -/
theorem coarseGrained_haagDuality
    {FineRegion : Type*} [Preorder FineRegion]
    (Ncoarse : LocalNet A Region) (Nfine : LocalNet A FineRegion)
    (B : CoarseGrainingMap Ncoarse Nfine) (O : Region)
    (hfine : HaagDuality Nfine (B.toFine O)) :
    HaagDuality Ncoarse O := by
  unfold HaagDuality
  rw [B.compl_alg_eq O, B.alg_eq O]
  exact hfine

/-- If every blocked cone maps to a fine cone-like region satisfying exact Haag duality,
then the coarse-grained lattice satisfies exact Haag duality on every coarse cone. -/
theorem exactCoarseGrainedHaagDualityOn
    {FineRegion : Type*} [Preorder FineRegion]
    (Ncoarse : LocalNet A Region) (Nfine : LocalNet A FineRegion)
    (B : CoarseGrainingMap Ncoarse Nfine)
    (CoarseCone : Region -> Prop) (FineConeLike : FineRegion -> Prop)
    (maps_to_coneLike : forall O : Region, CoarseCone O -> FineConeLike (B.toFine O))
    (hfine : ExactHaagDualityOn Nfine FineConeLike) :
    ExactHaagDualityOn Ncoarse CoarseCone :=
  fun O hO => coarseGrained_haagDuality Ncoarse Nfine B O
    (hfine (B.toFine O) (maps_to_coneLike O hO))

/-! ## Section 4: links to Verch/Kalnay local AQFT completeness -/

variable {B : Type*} [Ring B] [StarRing B]
variable {Z : Set B} {containsPoint : Region -> Prop}

/-- The Verch/Kalnay complete local-AQFT package supplies exact Haag duality on any
chosen region class. -/
theorem localAQFTCompleteness_exactHaagDualityOn
    (C : LocalAQFTCompleteness (A := B) (ι := Region) Z containsPoint)
    (RegionClass : Region -> Prop) :
    ExactHaagDualityOn C.obsNet RegionClass :=
  fun Gamma _hGamma => C.haag_duality Gamma

/-- Consequently, the complete local-AQFT package gives approximate Haag duality for
any cone-deformation system. -/
theorem localAQFTCompleteness_approximateHaagDuality
    (C : LocalAQFTCompleteness (A := B) (ι := Region) Z containsPoint)
    (ConeLike : Region -> Prop) (Fatten : Region -> Region -> Region)
    (D : ConeDeformationSystem C.obsNet ConeLike Fatten) :
    ApproximateHaagDuality C.obsNet Fatten :=
  approximateHaagDuality_of_exact_coneLike C.obsNet ConeLike Fatten D
    (localAQFTCompleteness_exactHaagDualityOn C ConeLike)

/-- Under Haag duality, the local algebra is maximal: this is the paper's physical
reading that no observable can be added to a cone algebra without breaking independence
from the complement. -/
theorem spinHaagDuality_maximality
    (N : LocalNet A Region) (Gamma : Region) {S : Set A}
    (hdual : HaagDuality N Gamma)
    (hS : S ⊆ commutant (N.alg (N.compl Gamma))) :
    S ⊆ N.alg Gamma :=
  haagDuality_maximal N hdual hS

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.TwoDimensionalSpinHaagDuality

end
