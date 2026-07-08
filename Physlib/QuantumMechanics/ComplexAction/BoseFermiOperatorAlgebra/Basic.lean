/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseFermiField
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
public import Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.FirstLawVariational
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium
public import Physlib.Relativity.Special.QuantumInertialFrameUnruh
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.SaitoBogoliubovBoseFermiStatistics
public import Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStructureCount
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity
public import Physlib.QuantumMechanics.ComplexAction.Fermion.NetObservableLocality
public import Physlib.Mathematics.SO3.Basic

/-!
# Kálnay Bose/Fermi operator-algebra bridge

This file links the Kálnay Bose-bilinear fermion-field bridge to the operator-algebraic infrastructure that
already exists in the repository:

* Verch quasifree/Hadamard and Klein-Gordon continuity (`AlgebraicQFT.SchmidtVerchQuasifree`,
  `AlgebraicQFTQuasifree.KleinGordonProgram`);
* Tomita-Takesaki modular generation (`δ_K = [K, -]`), with an explicit obligation representative for the heavier
  operator statements `Δ = S* S`, `K = -log Δ`, and the full modular automorphism;
* KMS thermal occupation and causal-diamond/QIF zeroth-law bridges;
* Weyl CCR, Bloch sphere, Bogoliubov Bose/Fermi statistics, and the spin-1/2 double cover;
* the current region-level status: some structures exist, but CAR-on-region and Haag duality remain explicit
  obligations.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open FieldSpecification.FieldOpFreeAlgebra
open Matrix

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseFermiField
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.FirstLawVariational
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere
open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.SaitoBogoliubovBoseFermiStatistics
open Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStructureCount
open Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity
open Physlib.QuantumMechanics.ComplexAction.Fermion.NetObservableLocality
open Physlib.QuantumMechanics.RelationalTime

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## §A — the Kálnay Bose/Fermi field statement as a reusable predicate -/

/-- The reusable statement supplied by `BoseFermiOperatorAlgebra.BoseFermiField`: the fermion field generator is mapped to
Bose-bilinear words, and the represented annihilation/creation pair satisfies the CAR. -/
abbrev KalnayBoseFermiFieldStatement (p : Momentum 3) : Prop :=
  kalnayBosonizationHom (ofCrAnOpF (kalnayFermionAnnihil p)) = boseBilinearAnnihilAsymptotic p
    ∧ kalnayBosonizationHom (ofCrAnOpF (kalnayFermionCreate p)) = boseBilinearCreateAsymptotic p
    ∧ kalnayFermionRepHom (ofCrAnOpF (kalnayFermionAnnihil p)) = boseBilinear
    ∧ kalnayFermionRepHom
      (ofCrAnOpF (kalnayFermionAnnihil p) * ofCrAnOpF (kalnayFermionCreate p)
        + ofCrAnOpF (kalnayFermionCreate p) * ofCrAnOpF (kalnayFermionAnnihil p)) = 1

/-- The last formalization is now available as a named predicate for downstream bridge files. -/
theorem kalnay_bose_fermi_field_statement (p : Momentum 3) :
    KalnayBoseFermiFieldStatement p :=
  kalnay_fermion_field_from_bose_fields p

/-! ## §B — links into Verch quasifree/Hadamard and Klein-Gordon continuity -/

/-- Kálnay's Bose-bilinear fermion field and the Schmidt-Verch quasifree/Hadamard bridge are compatible
assembled inputs: the finite CAR field can be used alongside the Verch quasifree state data. -/
theorem kalnay_verch_quasifree_hadamard_link
    (p : Momentum 3) (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) (φ : Fin 2 → ℝ) :
    KalnayBoseFermiFieldStatement p
      ∧ Symplectomorphism (thermoBogoliubov η)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) φ = Real.tanh η
      ∧ quasifreeWeight (fun _ _ => (0 : ℝ)) φ = 1
      ∧ sympForm * sympForm = -1 := by
  let hV := schmidt_quasifree_bridge ħ η hħ hη φ
  exact ⟨kalnay_bose_fermi_field_statement p, hV.1, hV.2.1, hV.2.2.1, hV.2.2.2⟩

/-- Kálnay's finite Bose/Fermi bridge can be transported next to the Verch Klein-Gordon continuity program:
`μ₁ = |r| μ₀`, symplectic continuity, and the Liouvillian/modular superoperator identity. -/
theorem kalnay_kleinGordon_continuity_link
    (p : Momentum 3) (M Mi : Mat2R) (hsymp : Symplectomorphism M) (hinv : M * Mi = 1)
    (Mμ : Mat2R) (r : ℝ) (φ ψ : Fin 2 → ℝ) (X : Mat2C) :
    KalnayBoseFermiFieldStatement p
      ∧ muInterp Mμ r 1 φ ψ = |r| * muInterp Mμ r 0 φ ψ
      ∧ Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ
      ∧ modularGenerator (sympForm.map Complex.ofReal) X = liouvillian (sympForm.map Complex.ofReal) X := by
  let hKG := kleinGordon_continuity_program M Mi hsymp hinv Mμ r φ ψ X
  exact ⟨kalnay_bose_fermi_field_statement p, hKG.1, hKG.2.1, hKG.2.2⟩

/-! ## §C — Tomita-Takesaki and modular first-law obligation interfaces -/

/-- A lightweight representative for the heavy Tomita-Takesaki obligations that are not proved by the finite
matrix layer: `Δ = S* S`, the full modular automorphism, and `K = -log Δ`. -/
structure TomitaOperatorObligationLayer (A : Type*) [Ring A] [Star A] where
  /-- The Tomita operator `S`. -/
  S : A
  /-- The modular operator `Δ`. -/
  Delta : A
  /-- The modular Hamiltonian `K`. -/
  K : A
  /-- The intended modular automorphism family. -/
  sigma : ℝ → A → A
  /-- The formal Tomita identity `Δ = S* S`. -/
  delta_eq_star_mul : Delta = star S * S
  /-- Obligation: `K = -log Δ`, in a functional-calculus-capable operator algebra. -/
  modularHamiltonian_is_neg_log_Delta : Prop
  /-- Obligation: `sigma` is the full Tomita-Takesaki modular automorphism. -/
  sigma_is_modular_automorphism : Prop

/-- The part of Tomita-Takesaki already present in the repo: the modular generator is the commutator
superoperator `collisionStar K`. -/
theorem tomita_obligation_modular_generator {A : Type*} [Ring A] [Star A]
    (T : TomitaOperatorObligationLayer A) (a : A) :
    modularGenerator T.K a = collisionStar T.K a := rfl

/-- A minimal representative for the entanglement first law `δS = δ⟨K⟩`. This records the interface needed by
downstream region-algebra files without asserting an operator-analytic derivation here. -/
structure ModularFirstLawCarrier where
  /-- Entropy variation `δS`. -/
  entropyVariation : ℝ
  /-- Modular-energy variation `δ⟨K⟩`. -/
  modularEnergyVariation : ℝ
  /-- The first-law relation. -/
  firstLaw : entropyVariation = modularEnergyVariation

/-- Kálnay's field statement can be paired with the concrete modular generator identity. -/
theorem kalnay_tomita_modular_generator_link (p : Momentum 3) (K X : Mat2C) :
    KalnayBoseFermiFieldStatement p ∧ modularGenerator K X = collisionStar K X :=
  ⟨kalnay_bose_fermi_field_statement p, rfl⟩

/-! ## §D — KMS, first-law, QIF/Unruh, and zeroth-law links -/

/-- The Kálnay fermion mode is compatible with the repository's KMS/Fermi-Dirac occupation layer and the
Euclidean/Lorentzian KMS-scale inversion. -/
theorem kalnay_kms_thermal_occupation_link (p : Momentum 3) (β ε : ℝ) (K : KMSScale) :
    KalnayBoseFermiFieldStatement p
      ∧ gibbsOccupation β ε = fermiDirac (β * ε)
      ∧ (0 ≤ gibbsOccupation β ε ∧ gibbsOccupation β ε ≤ 1)
      ∧ K.planckianPeriod * K.thermalRate = 1 := by
  let hFD := fermion_modular_thermal_occupation β ε
  exact ⟨kalnay_bose_fermi_field_statement p, hFD.1, ⟨hFD.2.1, hFD.2.2⟩,
    KMSScale.planckianPeriod_mul_thermalRate K⟩

/-- Kálnay's field bridge can be stated together with the causal-diamond first law. This is the geometric
first-law side of the modular `δS = δ⟨K⟩` interface. -/
theorem kalnay_causalDiamond_firstLaw_link
    (p : Momentum 3) (κ k Vζ G δA δV δΛ dHtot dHmatter dHmTilde : ℝ)
    (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + dHmatter)
    (hMatterSplit : dHmatter = dHmTilde + cosmoHamiltonianVar Vζ G δΛ) :
    KalnayBoseFermiFieldStatement p
      ∧ dHmTilde = 1 / (8 * Real.pi * G) * (-(κ * δA) + κ * k * δV - Vζ * δΛ) :=
  ⟨kalnay_bose_fermi_field_statement p,
    firstLaw_causalDiamond κ k Vζ G δA δV δΛ dHtot dHmatter dHmTilde hπ hG
      hWald hSplit hMatterSplit⟩

/-- Kálnay's fermion construction links to the QIF/Unruh zeroth-law statement: equal surface gravities give
equal entropic rates and equal Hawking/Unruh temperatures. -/
theorem kalnay_qif_unruh_zerothLaw_link
    (p : Momentum 3) (ℏ κ κ' c kB : ℝ) (h : κ = κ') :
    KalnayBoseFermiFieldStatement p
      ∧ qifEntropicRate κ c = qifEntropicRate κ' c
      ∧ hawkingTemperature ℏ κ c kB = hawkingTemperature ℏ κ' c kB
      ∧ unruhTemperature ℏ κ c kB = unruhTemperature ℏ κ' c kB := by
  let hQ := qif_zerothLaw_equilibrium ℏ κ κ' c kB h
  exact ⟨kalnay_bose_fermi_field_statement p, hQ.1, hQ.2.1, hQ.2.2⟩

/-! ## §E — Weyl CCR, Bloch sphere, Bogoliubov statistics, and the spin double cover -/

/-- The Kálnay field bridge can be used with the Weyl CCR/Bogoliubov automorphism layer. -/
theorem kalnay_weyl_ccr_bogoliubov_link {A : Type*} [Ring A] [Algebra ℂ A]
    (p : Momentum 3) (w : WeylSystem (A := A) symplecticPairing) (θ : ℝ) (φ ψ : Fin 2 → ℝ) :
    KalnayBoseFermiFieldStatement p
      ∧ w.W (thermoBogoliubov θ *ᵥ φ) * w.W (thermoBogoliubov θ *ᵥ ψ)
          = Complex.exp (-(Complex.I * (symplecticPairing φ ψ : ℂ)) / 2)
              • w.W (thermoBogoliubov θ *ᵥ (φ + ψ))
      ∧ w.W (fermiBogoliubov θ *ᵥ φ) * w.W (fermiBogoliubov θ *ᵥ ψ)
          = Complex.exp (-(Complex.I * (symplecticPairing φ ψ : ℂ)) / 2)
              • w.W (fermiBogoliubov θ *ᵥ (φ + ψ)) :=
  ⟨kalnay_bose_fermi_field_statement p, thermoBogoliubov_weyl_automorphism w θ φ ψ,
    fermiBogoliubov_weyl_automorphism w θ φ ψ⟩

/-- The finite Kálnay field statement is now wired to the Bloch/Poincare sphere, Bose/Fermi Bogoliubov
normalization dichotomy, and spin-1/2 double cover. -/
theorem kalnay_bloch_bogoliubov_spin_link
    (p : Momentum 3) (χ : Fin 2 → ℂ) (θ ξ Δ : ℝ) (X : Mat2C) :
    KalnayBoseFermiFieldStatement p
      ∧ stokesS (Sum.inr 0) χ ^ 2 + stokesS (Sum.inr 1) χ ^ 2 + stokesS (Sum.inr 2) χ ^ 2
          = stokesS (Sum.inl 0) χ ^ 2
      ∧ spinExpectation (sympForm.map Complex.ofReal) χ = Complex.I * stokesS (Sum.inr 1) χ
      ∧ Real.cosh θ ^ 2 - Real.sinh θ ^ 2 = 1
      ∧ bogoliubovU2 ξ Δ + bogoliubovV2 ξ Δ = 1
      ∧ spinHalfRotation (2 * Real.pi) = -1
      ∧ spinHalfRotation (4 * Real.pi) = 1
      ∧ spinHalfRotation (θ + 2 * Real.pi) * X * spinHalfRotation (θ + 2 * Real.pi)
          = spinHalfRotation θ * X * spinHalfRotation θ := by
  let hB := pure_state_poincare_sphere χ
  let hBF := bose_fermi_dichotomy θ ξ Δ
  let hSpin := spin_half_double_cover X θ
  exact ⟨kalnay_bose_fermi_field_statement p, hB.1, hB.2, hBF.1, hBF.2,
    hSpin.1, hSpin.2.1, hSpin.2.2⟩

/-! ## §F — verified region-level status and gaps -/

/-- Coarse status flags for the requested operator-algebra gaps. `verifiedCarrier` means the repo contains
a usable formal interface, but not necessarily the final region-level theorem. -/
inductive GapStatus where
  | verifiedCarrier : GapStatus
  | obligation : GapStatus
deriving DecidableEq

/-- The requested gap checklist as an explicit object. The status is intentionally conservative:
Kálnay, split-property, spin-statistics, and spin-structure structures now exist; CAR-on-region and Haag duality
remain obligations, and the split/spin structures have not been promoted to a full regional CAR/duality theorem. -/
structure RegionOperatorGapChecklist where
  carOnRegion : GapStatus
  kalnayBoseFermiBridge : GapStatus
  splitPropertyCarrier : GapStatus
  haagDuality : GapStatus
  spinStatisticsCarrier : GapStatus
  spinStructureCounting : GapStatus

/-- Current status after linking the Kálnay Bose/Fermi field bridge into the repo. -/
def currentRegionOperatorGapChecklist : RegionOperatorGapChecklist where
  carOnRegion := GapStatus.obligation
  kalnayBoseFermiBridge := GapStatus.verifiedCarrier
  splitPropertyCarrier := GapStatus.verifiedCarrier
  haagDuality := GapStatus.obligation
  spinStatisticsCarrier := GapStatus.verifiedCarrier
  spinStructureCounting := GapStatus.verifiedCarrier

theorem current_gap_status_carOnRegion :
    currentRegionOperatorGapChecklist.carOnRegion = GapStatus.obligation := rfl

theorem current_gap_status_kalnay :
    currentRegionOperatorGapChecklist.kalnayBoseFermiBridge = GapStatus.verifiedCarrier := rfl

theorem current_gap_status_haagDuality :
    currentRegionOperatorGapChecklist.haagDuality = GapStatus.obligation := rfl

/-- The existing split-property structure remains available to downstream regional algebra work. -/
theorem split_property_carrier_link {A ι : Type*} [Monoid A] [Preorder ι]
    {N : LocalNet A ι} {O O₁ : ι}
    (h : HasSplitProperty N O O₁) :
    ∃ M : Set A, commutant (N.alg O₁) ⊆ commutant M ∧ commutant M ⊆ commutant (N.alg O) :=
  split_commutant_nest h

/-- The existing spin-structure count is exposed from the synthesis layer for regional fermion work. -/
theorem spin_structure_counting_carrier_link (g : ℕ) (hg : 1 ≤ g) :
    numEvenSpinStructures g + numOddSpinStructures g = 4 ^ g
      ∧ numEvenSpinStructures g - numOddSpinStructures g = 2 ^ g
      ∧ modularT oddTorusSpinStructure = oddTorusSpinStructure
      ∧ modularS oddTorusSpinStructure = oddTorusSpinStructure :=
  fermion_region_spin_structures g hg

/-- The existing spin-statistics structure can be applied to the Kálnay sector fermion mode. -/
theorem kalnay_spin_statistics_carrier_link (G : Mat2C) :
    spinRotation G (2 * Real.pi) = -1
      ∧ fermionParity boseBilinear * fermionParity boseBilinear = 1
      ∧ fermionParity boseBilinear * boseBilinear = -(boseBilinear * fermionParity boseBilinear) :=
  spin_statistics_connection G boseBilinear boseBilinear_isFermionMode

/-- The observable-locality structure remains separated from full Haag duality: it proves locality of the
number/parity observables under an anticommuting-pair hypothesis. -/
theorem fermion_observable_locality_carrier_link {A : Type*} [Ring A] [StarRing A] (f g : A)
    (h : AnticommutingFermionModes f g) :
    fermionNumber f * fermionNumber g = fermionNumber g * fermionNumber f
      ∧ fermionParity f * fermionParity g = fermionParity g * fermionParity f :=
  fermion_observable_net_locality f g h

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic

end
