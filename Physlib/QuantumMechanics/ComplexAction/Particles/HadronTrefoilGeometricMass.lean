/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour
public import Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
public import Physlib.QuantumMechanics.ComplexAction.WittenAnalyticContinuationChernSimons.GeneralEq531AndStokes
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SorkinJohnstonCausalDiamond
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen

/-!
# Hadron mass composition linked to Nagao-Nielsen, Pauli geometry, and Witten trefoils

This bridge connects the repo's existing mass and topology carriers without claiming a
new first-principles QCD mass calculation.

The checked chain is:

* the `u,d,d` current masses are the real parts of the Yukawa complex fermion masses in
  the Nagao-Nielsen complex-mass slot;
* the neutron mass is the current `u,d,d` mass plus the explicit strong residual from
  `Particles.NeutronProperties`;
* the neutron is a three-quark fermionic, colour-centre-trivial composite;
* the three fermionic constituents have the Pauli/geometric-entanglement carrier
  `pauliRegionSize 3 cell = 3 * cell`, and the density-derived size law is reused;
* Witten's trefoil data supplies the Wilson/Jones invariant, chirality, and the
  Picard-Lefschetz/Stokes flow carrier;
* the Hopf/Wilson layer supplies charge fusion by the same addition law.
* the Sorkin-Johnston causal-diamond layer supplies the region-local two-point
  vacuum carrier used by the AQFT/quasifree side of the repo.
* the causal Green/Feynman layer supplies the link from region two-point kernels
  to the existing complex Schrodinger propagator, scalar complex Green kernel,
  Lorentzian path-integral propagator, and connected path-integral functional.

The residual mass is intentionally left as the strong-sector residual. The theorem
below proves that this residual is linked to the available colour, Pauli, Hopf/Wilson,
and Witten-trefoil structures; it does not replace Yang-Mills dynamics with a
dimensionless knot invariant.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties
open Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour
open Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SorkinJohnstonCausalDiamond
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HadronTrefoilGeometricMass

/-! ## A. Local carriers for the Witten and Hopf/Wilson pieces -/

/-- The Witten/Wilson trefoil invariant equation reused by the hadron bridge. -/
def trefoilWilsonInvariantEquation (A : ℂ) : Prop :=
  kauffmanClosure (kauffmanLoopValue A) (tlMul (kauffmanLoopValue A) (crossingTL A)
      (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
    = electronJones A

/-- The trefoil Wilson-loop equation is exactly the existing CSW/Jones theorem. -/
lemma trefoilWilsonInvariantEquation_checked (A : ℂ) (hA : A ≠ 0) :
    trefoilWilsonInvariantEquation A :=
  by simpa [trefoilWilsonInvariantEquation] using electron_csw_invariant A hA

/-- The common Hopf/Wilson charge-fusion carrier: Hopf charge multiplication and
Wilson/Verlinde convolution both add charges. -/
def HasHopfWilsonFusionCarrier : Prop :=
  ∀ (k : ℕ) (_hk : 0 < k) (a b : Fin k),
    chargeState (a.val : ℤ) * chargeState (b.val : ℤ)
        = chargeState ((a.val : ℤ) + (b.val : ℤ))
      ∧ cswConvolution (Pi.single a 1) (Pi.single b (1 : ℂ)) = Pi.single (a + b) 1

/-- The Hopf/Wilson fusion carrier is already proved in the Chern-Simons bridge. -/
lemma hopfWilsonFusionCarrier_checked : HasHopfWilsonFusionCarrier := by
  intro k hk a b
  exact hopf_charge_addition_matches_wilson_fusion k hk a b

/-! ## B. Nagao-Nielsen current-quark mass bridge -/

/-- The current `u,d` quark masses used in the neutron are the real parts of the
Yukawa complex fermion masses placed in the Nagao-Nielsen complex-mass carrier. -/
def HasNagaoNielsenCurrentQuarkMass
    (yUp yDown v omega0 hbar c : ℝ) : Prop :=
  (yukawaComplexFermionMass yUp v omega0 hbar c).re = currentQuarkMass yUp v
    ∧ (yukawaComplexFermionMass yDown v omega0 hbar c).re = currentQuarkMass yDown v
    ∧ neutronCurrentQuarkMass yUp yDown v = currentQuarkMass yUp v + 2 * currentQuarkMass yDown v

/-- The Nagao-Nielsen current-quark bridge follows from the existing Yukawa complex-mass
real-part theorem and the neutron `udd` current-mass definition. -/
lemma nagaoNielsenCurrentQuarkMass_checked
    (yUp yDown v omega0 hbar c : ℝ) :
    HasNagaoNielsenCurrentQuarkMass yUp yDown v omega0 hbar c :=
  ⟨by simp [currentQuarkMass],
    by simp [currentQuarkMass],
    rfl⟩

/-- The current `u,d` quark masses used in the proton are the real parts of the
Yukawa complex fermion masses placed in the same Nagao-Nielsen complex-mass
carrier. -/
def HasNagaoNielsenProtonCurrentQuarkMass
    (yUp yDown v omega0 hbar c : ℝ) : Prop :=
  (yukawaComplexFermionMass yUp v omega0 hbar c).re = currentQuarkMass yUp v
    ∧ (yukawaComplexFermionMass yDown v omega0 hbar c).re = currentQuarkMass yDown v
    ∧ protonCurrentQuarkMass yUp yDown v = 2 * currentQuarkMass yUp v + currentQuarkMass yDown v

/-- The proton Nagao-Nielsen current-quark bridge follows from the existing
Yukawa complex-mass real-part theorem and the proton `uud` current-mass
definition. -/
lemma nagaoNielsenProtonCurrentQuarkMass_checked
    (yUp yDown v omega0 hbar c : ℝ) :
    HasNagaoNielsenProtonCurrentQuarkMass yUp yDown v omega0 hbar c :=
  ⟨by simp [currentQuarkMass],
    by simp [currentQuarkMass],
    rfl⟩

/-! ## C. Causal Green propagation bridges for nucleon particle models -/

/-- The neutron particle package can use the Sorkin-Johnston causal-diamond
carrier and the causal Green/Feynman bridge to the complex Schrodinger and
path-integral Green-functional layers. This is the propagation/field-theory side
of the same particle object, not a new neutron equation. -/
def HasNeutronCausalGreenPropagation : Prop :=
  HasNeutronParticleModel
    ∧ HasSorkinJohnstonCausalDiamondCarrier
    ∧ HasCausalGreenComplexSchrodingerFunctionalBridge.{0, 0, 0, 0}

/-- The neutron particle model is linked to the region-local SJ vacuum and the
complex Schrodinger/Feynman Green-functional stack. -/
lemma neutronCausalGreenPropagation_checked :
    HasNeutronCausalGreenPropagation :=
  ⟨neutronParticleModel_checked,
    sorkinJohnstonCausalDiamondCarrier_checked,
    causalGreen_complexSchrodinger_functional_bridge_checked⟩

/-- The proton particle package can use the same region-local
Sorkin-Johnston carrier and causal Green/Feynman bridge as the neutron package.
This is the propagation/field-theory side of the proton object, not a new proton
equation. -/
def HasProtonCausalGreenPropagation : Prop :=
  HasProtonParticleModel
    ∧ HasSorkinJohnstonCausalDiamondCarrier
    ∧ HasCausalGreenComplexSchrodingerFunctionalBridge.{0, 0, 0, 0}

/-- The proton particle model is linked to the region-local SJ vacuum and the
complex Schrodinger/Feynman Green-functional stack. -/
lemma protonCausalGreenPropagation_checked :
    HasProtonCausalGreenPropagation :=
  ⟨protonParticleModel_checked,
    sorkinJohnstonCausalDiamondCarrier_checked,
    causalGreen_complexSchrodinger_functional_bridge_checked⟩

/-! ## D. Neutron/hadron mass composition with trefoil geometry -/

/-- Repo-facing bridge for the neutron as a hadron with complex current masses,
strong residual mass, Pauli geometric-entanglement size, and Witten trefoil data.

The theorem keeps the strong residual explicit: topology and geometry supply the
sector carriers, while the numerical QCD residual remains the strong-sector term. -/
def HasHadronTrefoilGeometricMass
    (yUp yDown v omega0 hbar c rho V0 eps0 cell : ℝ) (n y : ℂ) : Prop :=
  HasNagaoNielsenCurrentQuarkMass yUp yDown v omega0 hbar c
    ∧ HasNeutronMassDecomposition yUp yDown v
    ∧ neutronMass = neutronCurrentQuarkMass yUp yDown v + neutronStrongResidualMass yUp yDown v
    ∧ (0 < neutronStrongResidualMass yUp yDown v → neutronCurrentQuarkMass yUp yDown v < neutronMass)
    ∧ compositeTwist 3 = -1
    ∧ cubeRoot ^ neutronTotalWinding = 1
    ∧ pauliRegionSize 3 cell = 3 * cell
    ∧ entangledRegionSize rho V0 eps0 cell = rho * (V0 * cell / eps0)
    ∧ electronJones 2 ≠ positronJones 2
    ∧ (∀ A : ℂ, A ≠ 0 → trefoilWilsonInvariantEquation A)
    ∧ Nonempty
      (OperatorAlgebra.PicardLefschetzMorseContour.ChernSimonsGradientFlowLine
        (trefoilBirthStokesConnection n y))
    ∧ HasNeutronCausalGreenPropagation
    ∧ HasHopfWilsonFusionCarrier

/-- The checked bridge: neutron mass composition, Nagao-Nielsen/Yukawa current
masses, colour-singlet baryon statistics, Pauli geometric-entanglement size, Witten
trefoil chirality/invariant/flow, and Hopf/Wilson charge fusion are available from
the existing repository infrastructure. -/
lemma hadronTrefoilGeometricMass_checked
    (yUp yDown v omega0 hbar c rho V0 eps0 cell : ℝ) (n y : ℂ) :
    HasHadronTrefoilGeometricMass yUp yDown v omega0 hbar c rho V0 eps0 cell n y := by
  refine ⟨nagaoNielsenCurrentQuarkMass_checked yUp yDown v omega0 hbar c,
    neutronMassDecomposition_checked yUp yDown v,
    neutronMass_eq_currentQuarkMass_plus_strongResidual yUp yDown v,
    ?_,
    baryon_is_fermion,
    neutron_colourCentre_trivial,
    rfl,
    entangledRegionSize_eq rho V0 eps0 cell,
    trefoil_chiral_distinguishes,
    ?_,
    trefoil_birth_gradientFlowLine_exists n y,
    neutronCausalGreenPropagation_checked,
    hopfWilsonFusionCarrier_checked⟩
  · intro hres
    exact neutronMass_gt_currentQuarkMass_of_residual_pos yUp yDown v hres
  · intro A hA
    exact trefoilWilsonInvariantEquation_checked A hA

/-! ## E. Nucleon bridge: neutron plus proton on the same carriers -/

/-- Nucleon-level extension of the hadron trefoil bridge. The neutron bridge
continues to carry the original trefoil/topology package, while the proton is
added through the same shared hadron particle model, the same Yukawa current-mass
carrier, the same colour-centre criterion, and the same causal Green/Feynman
propagation stack. -/
def HasNucleonTrefoilGeometricMass
    (yUp yDown v omega0 hbar c rho V0 eps0 cell : ℝ) (n y : ℂ) : Prop :=
  HasHadronTrefoilGeometricMass yUp yDown v omega0 hbar c rho V0 eps0 cell n y
    ∧ HasNagaoNielsenProtonCurrentQuarkMass yUp yDown v omega0 hbar c
    ∧ HasProtonMassDecomposition yUp yDown v
    ∧ protonMass = protonCurrentQuarkMass yUp yDown v + protonStrongResidualMass yUp yDown v
    ∧ (0 < protonStrongResidualMass yUp yDown v → protonCurrentQuarkMass yUp yDown v < protonMass)
    ∧ cubeRoot ^ protonTotalWinding = 1
    ∧ HasProtonCausalGreenPropagation

/-- The checked nucleon bridge: the proton now reuses the neutron's hadron
particle pattern and the already-linked trefoil/SJ/Green carriers without
duplicating the neutron equations. -/
lemma nucleonTrefoilGeometricMass_checked
    (yUp yDown v omega0 hbar c rho V0 eps0 cell : ℝ) (n y : ℂ) :
    HasNucleonTrefoilGeometricMass yUp yDown v omega0 hbar c rho V0 eps0 cell n y := by
  refine ⟨hadronTrefoilGeometricMass_checked yUp yDown v omega0 hbar c rho V0 eps0 cell n y,
    nagaoNielsenProtonCurrentQuarkMass_checked yUp yDown v omega0 hbar c,
    protonMassDecomposition_checked yUp yDown v,
    protonMass_eq_currentQuarkMass_plus_strongResidual yUp yDown v,
    ?_,
    proton_colourCentre_trivial,
    protonCausalGreenPropagation_checked⟩
  intro hres
  exact protonMass_gt_currentQuarkMass_of_residual_pos yUp yDown v hres

end Physlib.QuantumMechanics.ComplexAction.Particles.HadronTrefoilGeometricMass

end

end
