/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ElectronZitterbewegung
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
public import Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties
public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling
meta import Zil

/-!
# CPT invariance across the whole particle zoo

The CPT laws established for the electron (`ComptonClock.ElectronZitterbewegung`) and positron (`Particles.PositronModel`) are
not electron-specific — each is **universally quantified** and so applies to every particle in the zoo:

* **Charge conjugation `C` annihilates pairs.** `pair_annihilates q : q + Cq = vacuum` holds for *any*
  `QuantumNumbers` `q` (`zoo_pair_annihilates`) — every particle (baryon, lepton, …) annihilates its
  antiparticle. `C` is an involution (`zoo_conjugate_involutive`).
* **The proton and neutron models are named and checked.** `ProtonProperties.HasProtonParticleModel`
  packages the charged `uud` flavor computation, three-quark fermion exchange phase,
  antiproton cancellation, finite radius, stability, and Yukawa-current/strong-residual mass split;
  `NeutronProperties.HasNeutronParticleModel` packages the neutral `udd` flavor computation,
  beta-decay conservation law, nonzero magnetic moment, and neutron-proton mass window.
* **`C` reverses charge for any winding.** `windingCharge (−n) = −windingCharge n` for *any* `n`
  (`zoo_charge_conjugation`) — so every quark flavor's antiquark has the opposite charge
  (`quark_antiparticle_charge`, parametric over all six `QuarkFlavor`s).
* **The Dirac dynamics is CPT-invariant for any mass.** `A·D(−p)·A⁻¹ = D(p)` for *any* mass `m`
  (`zoo_dirac_cpt`) — so every spin-½ fermion (every quark, every charged lepton) sits in CPT-invariant
  dynamics.

§B instantiates these on named particles — `proton_cpt`, `neutron_cpt`, `electron_cpt`, `neutrino_cpt`
(each annihilates its antiparticle), `quark_antiparticle_charge` (all six flavors), and `photon_cpt` (the
photon is its own antiparticle). §C is the main result `zoo_cpt_invariance`: for *any* particle, *any* quark
flavor, *any* winding, *any* fermion mass, CPT holds.

**Honest layering.** Every theorem here is an instance or re-export of an already-proved universal CPT law
(`AntiparticleConjugation.pair_annihilates`/`conjugate_involutive`/`photon_selfConjugate`,
`Winding.QuarkChargeWinding.windingCharge_neg`, `PTSymmetricQFT.CPTDiracDynamics.cpt_diracOp_invariant`). The content
is that these laws are *zoo-wide*: CPT is a symmetry of the whole model, not of one particle.

## References

* The CPT theorem (charge conjugation, particle–antiparticle pairing, CPT-invariant Dirac dynamics).
  `Physlib` (`AntiparticleConjugation`, `Winding.QuarkChargeWinding`, `PTSymmetricQFT.CPTDiracDynamics`,
  `Particles.HadronFlavorModel`, `ComptonClock.ElectronZitterbewegung`).


-/

set_option autoImplicit false

open spaceTime
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT


/-- **[Every particle annihilates its antiparticle]** `q + Cq = vacuum` for any `QuantumNumbers` `q`. -/
lemma zoo_pair_annihilates (q : QuantumNumbers) : q + conjugate q = ⟨0, 0, 0⟩ :=
  pair_annihilates q

/-- **[Charge conjugation is an involution]** `C(Cq) = q` — applying `C` twice returns the particle. -/
lemma zoo_conjugate_involutive (q : QuantumNumbers) : conjugate (conjugate q) = q :=
  conjugate_involutive q

/-- **[`C` reverses charge for any winding]** `Q(−n) = −Q(n)` — every winding particle's antiparticle has the
opposite electric charge. -/
lemma zoo_charge_conjugation (n : ℤ) : windingCharge (-n) = - windingCharge n :=
  windingCharge_neg n

/-- **[Every fermion's Dirac dynamics is CPT-invariant]** `A·D(−p)·A⁻¹ = D(p)` with `A = (−i)γ⁵`, for any
mass `m` — so it holds for every spin-½ flavor (Greaves-Thomas). -/
lemma zoo_dirac_cpt (m : ℝ) (p : Fin 4 → ℝ) :
    ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  cpt_diracOp_invariant p m


/-- **[Proton]** `p + p̄ = vacuum`. -/
lemma proton_cpt : proton + conjugate proton = ⟨0, 0, 0⟩ := pair_annihilates proton

/-- **[Neutron]** `n + n̄ = vacuum`. -/
lemma neutron_cpt : neutron + conjugate neutron = ⟨0, 0, 0⟩ := pair_annihilates neutron

/-- **[Electron]** `e⁻ + e⁺ = vacuum`. -/
lemma electron_cpt : electron + conjugate electron = ⟨0, 0, 0⟩ := pair_annihilates electron

/-- **[Neutrino]** `ν + ν̄ = vacuum`. -/
lemma neutrino_cpt : muonNeutrino + conjugate muonNeutrino = ⟨0, 0, 0⟩ :=
  pair_annihilates muonNeutrino

/-- **[Every quark flavor's antiquark has opposite charge]** `Q(q̄) = −Q(q)` for all six `QuarkFlavor`s —
the charge-conjugation law applied to the winding `n = q.windingNumber`. -/
lemma quark_antiparticle_charge (f : Particles.HadronFlavorModel.QuarkFlavor) :
    windingCharge (- f.windingNumber) = - f.electricCharge :=
  windingCharge_neg f.windingNumber

/-- **[The photon is its own antiparticle]** `C(γ) = γ` — a self-conjugate neutral gauge boson. -/
lemma photon_cpt : conjugate photon = photon := photon_selfConjugate


/-- **[CPT holds across the whole zoo]** for *any* particle `q`, *any* quark flavor `f`, *any* winding `n`,
and *any* fermion mass `m`: (i) the particle annihilates its antiparticle; (ii) `C` is an involution;
(iii) `C` reverses charge; (iv) the flavor's antiquark has the opposite charge; (v) the photon is
self-conjugate; (vi) the Dirac dynamics is CPT-invariant. CPT is a symmetry of the entire model. -/
lemma zoo_cpt_invariance (q : QuantumNumbers) (f : Particles.HadronFlavorModel.QuarkFlavor) (n : ℤ) (m : ℝ)
    (p : Fin 4 → ℝ) :
    q + conjugate q = ⟨0, 0, 0⟩
      ∧ conjugate (conjugate q) = q
      ∧ windingCharge (-n) = - windingCharge n
      ∧ windingCharge (- f.windingNumber) = - f.electricCharge
      ∧ conjugate photon = photon
      ∧ ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  ⟨pair_annihilates q, conjugate_involutive q, windingCharge_neg n,
    windingCharge_neg f.windingNumber, photon_selfConjugate, cpt_diracOp_invariant p m⟩


/-- Named hadron flavor computations and zoo-wide CPT facts are available
together: the same hadron sector that computes proton/neutron/hyperon charges
also sits inside the universal particle-antiparticle and charge-conjugation
laws. -/
def HasHadronSectorCPTBridge : Prop :=
  Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.HasNamedHadronComputations
    ∧ proton + conjugate proton = ⟨0, 0, 0⟩
    ∧ neutron + conjugate neutron = ⟨0, 0, 0⟩
    ∧ (∀ f : Particles.HadronFlavorModel.QuarkFlavor,
      windingCharge (- f.windingNumber) = - f.electricCharge)
    ∧ conjugate photon = photon
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.HasProtonParticleModel
    ∧ Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.HasNeutronParticleModel

/-- The named hadron sector is linked to the existing zoo-wide CPT laws without
recomputing flavor charges or redefining charge conjugation. -/
lemma hadronSector_cpt_bridge_checked : HasHadronSectorCPTBridge :=
  ⟨Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.namedHadronComputations_checked,
    proton_cpt,
    neutron_cpt,
    quark_antiparticle_charge,
    photon_selfConjugate,
    Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.protonParticleModel_checked,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutronParticleModel_checked⟩

/-- The main zoo-wide CPT theorem and the named hadron sector bridge can be used
as one checked capability. -/
lemma zoo_cpt_invariance_with_hadron_sector
    (q : QuantumNumbers) (f : Particles.HadronFlavorModel.QuarkFlavor) (n : ℤ) (m : ℝ)
    (p : Fin 4 → ℝ) :
    (q + conjugate q = ⟨0, 0, 0⟩
      ∧ conjugate (conjugate q) = q
      ∧ windingCharge (-n) = - windingCharge n
      ∧ windingCharge (- f.windingNumber) = - f.electricCharge
      ∧ conjugate photon = photon
      ∧ ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m)
      ∧ HasHadronSectorCPTBridge :=
  ⟨zoo_cpt_invariance q f n m p, hadronSector_cpt_bridge_checked⟩


/-- The particle-zoo bridge now includes the topological quasiparticle sector:
named hadrons and CPT are available together with the generated anyon models,
half-filled FQHE anyon, bulk-edge, CSW modular, and semion-fusion bundle. -/
def HasParticleZooHadronFQHEBridge : Prop :=
  HasHadronSectorCPTBridge
    ∧ HasDataDrivenAnyonModels
    ∧ HasFQHECoreFormalization
    ∧ HasHalfFillingCompleteTopologicalOrder
    ∧ HasHalfFillingSemionChernSimonsBridge

/-- Under the explicit CSW item-9 package, the particle zoo can call the
completed half-filled FQHE sector without duplicating any particle, Hall, or
Wilson-loop equations. -/
lemma particleZoo_hadron_fqhe_bridge_checked
    (G : CSWGeometricQuantizationPackage 2 (by norm_num)) :
    HasParticleZooHadronFQHEBridge :=
  ⟨hadronSector_cpt_bridge_checked,
    dataDrivenAnyonModels_checked,
    fqhe_core_formalization_checked,
    halfFilling_completeTopologicalOrder_checked G,
    halfFilling_semion_csw_bridge_checked⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.zoo_cpt_invariance where
  formalizes @ "claim:cpt-is-a-symmetry-of-the-whole-particle-zoo-for-any-particle-flavor-winding-and-fermion-mass-pair-annihilation-charge-conjugation-and-cpt-invariant-dirac-dynamics-all-hold",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics.cpt_diracOp_invariant"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.hadronSector_cpt_bridge_checked where
  supported_by @ "lean:QuarkYukawaCouplings.namedHadronComputations_checked",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.neutronParticleModel_checked",
  formalizes @ "claim:the-named-hadron-sector-that-computes-proton-neutron-and-hyperon-charges-sits-inside-the-universal-particle-antiparticle-and-charge-conjugation-laws-without-recomputing-flavor-charges",
  requires @ "claim:cpt-is-a-symmetry-of-the-whole-particle-zoo-for-any-particle-flavor-winding-and-fermion-mass-pair-annihilation-charge-conjugation-and-cpt-invariant-dirac-dynamics-all-hold"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.particleZoo_hadron_fqhe_bridge_checked where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.hadronSector_cpt_bridge_checked",
  formalizes @ "claim:the-particle-zoo-bridge-includes-the-topological-quasiparticle-sector-named-hadrons-and-cpt-available-together-with-the-half-filled-fqhe-anyon-and-semion-chern-simons-bundle",
  requires @ "claim:the-named-hadron-sector-that-computes-proton-neutron-and-hyperon-charges-sits-inside-the-universal-particle-antiparticle-and-charge-conjugation-laws-without-recomputing-flavor-charges"

zil_file_contract physlib.particleZooCPT where
  promises "CPT invariance across the whole particle zoo: the charge-conjugation, particle-antiparticle pairing and CPT-invariant Dirac-dynamics laws established for the electron and positron are each universally quantified, hence zoo-wide -- for any particle, any of the six quark flavors, any winding and any fermion mass, the particle annihilates its antiparticle, charge conjugation is an involution reversing charge, the photon is self-conjugate, and the Dirac operator satisfies A D(-p) A^{-1} = D(p). These are bridged to the named hadron sector (proton/neutron/hyperon charge computations, proton and neutron particle models) and to the topological quasiparticle sector (half-filled FQHE anyon, semion-Chern-Simons bundle) as one checked capability, without recomputing any flavor charge or redefining charge conjugation."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics.cpt_diracOp_invariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.HasNamedHadronComputations",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutronProperties.HasNeutronParticleModel"]
  forbids_substitutes ["an electron-specific CPT statement, whereas the content is that CPT is zoo-wide",
    "a recomputation of flavor charges or a redefinition of charge conjugation inside the bridge"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.zoo_cpt_invariance,
    Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.zoo_cpt_invariance_with_hadron_sector,
    Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.hadronSector_cpt_bridge_checked,
    Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT.particleZoo_hadron_fqhe_bridge_checked]

/- ZIL-END -/
