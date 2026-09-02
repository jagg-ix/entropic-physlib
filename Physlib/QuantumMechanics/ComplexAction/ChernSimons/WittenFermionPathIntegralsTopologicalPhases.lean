/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction
public import Physlib.QuantumMechanics.ComplexAction.Fermion.ContinuumPartition
public import Physlib.QuantumMechanics.ComplexAction.TorusFourier.TorusFermionicPartition
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStructureCount
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FermionicBogoliubovCAR
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

@[expose] public section

/-!
# Fermion Path Integrals and Topological Phases

Finite algebraic carriers for Witten, "Fermion Path Integrals And Topological
Phases" (arXiv:1508.04715v2).  The file isolates the statements that are
formal at the current Physlib level:

* one-mode Pfaffian/determinant identities for Majorana and U(1)-charged
  fermions;
* mod-two spectral-flow signs for Dirac and Majorana path integrals;
* conditional Dai-Freed/APS cancellation theorems for eta-invariant phases;
* finite cyclic stacking laws for 3+1d topological superconductors and the
  0+1d Majorana-chain bulk phase;
* explicit reuse of the repository's fermionic partition, spin-structure,
  CAR, Clifford/Pin, and complex-action path-integral infrastructure.

The analytic index theorem and eta-invariant quantization are kept as named
hypotheses in the cancellation statements.  Lean checks the algebraic
consequences of those hypotheses without pretending to prove the analytic
inputs here.
-/

namespace Physlib
namespace QuantumMechanics
namespace ComplexAction
namespace ChernSimons.WittenFermionPathIntegralsTopologicalPhases

open Complex Matrix
open Physlib.QFT.PathIntegral
open Physlib.QFT.Matsubara.PathIntegral
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-- Local bibliographic anchor for the formalized source. -/
structure SourceAnchor where
  title : String
  arxiv : String
  equation : String
  meaning : String
deriving Repr, DecidableEq

/-- Witten, "Fermion Path Integrals And Topological Phases",
arXiv:1508.04715v2. -/
def witten2015 (equation meaning : String) : SourceAnchor where
  title := "Fermion Path Integrals And Topological Phases"
  arxiv := "1508.04715v2"
  equation := equation
  meaning := meaning

/-- Eq. (2.55): a Majorana path integral is a Pfaffian. -/
def eq255_majoranaPfaffian : SourceAnchor :=
  witten2015 "(2.55)" "Majorana path integral Pf(D)"

/-- Eq. (2.56)-(2.57): a charged block has Pfaffian equal to determinant. -/
def eq256_eq257_pfaffianDeterminant : SourceAnchor :=
  witten2015 "(2.56)-(2.57)" "U(1)-charged Majorana block: Pf(D)=det(D)"

/-- Eq. (2.61)-(2.62): a doubled eigenmode contributes one Pfaffian factor. -/
def eq261_eq262_pairedEigenmode : SourceAnchor :=
  witten2015 "(2.61)-(2.62)" "paired eigenmode 2x2 block"

/-- Eq. (2.11)-(2.12): spectral flow changes the Dirac sign by `(-1)^I`. -/
def eq211_eq212_diracSpectralFlow : SourceAnchor :=
  witten2015 "(2.11)-(2.12)" "Dirac spectral-flow sign"

/-- Eq. (2.64)-(2.65): Majorana spectral flow changes by `(-1)^(I/2)`. -/
def eq264_eq265_majoranaSpectralFlow : SourceAnchor :=
  witten2015 "(2.64)-(2.65)" "Majorana spectral-flow sign"

/-- Eq. (2.26)-(2.27): Dirac boundary eta phase cancels against a bulk phase. -/
def eq226_eq227_diracDaiFreed : SourceAnchor :=
  witten2015 "(2.26)-(2.27)" "Dirac Dai-Freed bulk-boundary cancellation"

/-- Eq. (2.72)-(2.73): Majorana boundary eta phase cancels against a bulk phase. -/
def eq272_eq273_majoranaDaiFreed : SourceAnchor :=
  witten2015 "(2.72)-(2.73)" "Majorana Dai-Freed bulk-boundary cancellation"

/-- Eq. (4.10): the Pin+ boundary Pfaffian combined with the eta phase. -/
def eq410_pinPlusPartition : SourceAnchor :=
  witten2015 "(4.10)" "Pin+ topological-superconductor partition"

/-- Eq. (4.15): eight copies detect `w4`; sixteen copies are trivial in the
full Pin+ bulk classification. -/
def eq415_pinPlusEightSixteen : SourceAnchor :=
  witten2015 "(4.15)" "nu=8 mapping-torus detector and nu=16 triviality"

/-- Section 5: the 0+1d Majorana-chain bulk phase is eight-periodic. -/
def sec5_majoranaChain : SourceAnchor :=
  witten2015 "Section 5" "Majorana-chain phase and eightfold periodicity"

/-! ## One-mode Pfaffian carriers -/

/-- Pfaffian of a 2x2 antisymmetric matrix in the convention
`[[0,a],[-a,0]] ↦ a`. -/
def pfaffian2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  M 0 1

/-- Canonical Majorana paired-eigenmode block, matching the sign convention
used for `pfaffian2x2`. -/
def majoranaPairBlock (lambda : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, lambda; -lambda, 0]

/-- Eq. (2.61)-(2.62), finite one-pair form: the Pfaffian contributes one
eigenvalue from the doubled pair. -/
lemma pfaffian2x2_majoranaPairBlock (lambda : ℂ) :
    pfaffian2x2 (majoranaPairBlock lambda) = lambda := by
  simp [pfaffian2x2, majoranaPairBlock]

/-- The determinant of the same paired Majorana block is the square of the
Pfaffian contribution. -/
lemma det_majoranaPairBlock (lambda : ℂ) :
    (majoranaPairBlock lambda).det = lambda ^ 2 := by
  simp [majoranaPairBlock, Matrix.det_fin_two]
  ring

/-- One-dimensional charged Dirac determinant carrier. -/
def chargedOneModeDeterminant (d : ℂ) : ℂ :=
  d

/-- U(1)-charged Majorana block used in Eq. (2.56)-(2.57). -/
def chargedMajoranaBlock (d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, d; -d, 0]

/-- Eq. (2.56)-(2.57), one-mode charged form: the Pfaffian of the
antisymmetric real block is the determinant of the charged Dirac block. -/
lemma pfaffian2x2_chargedMajoranaBlock_eq_det (d : ℂ) :
    pfaffian2x2 (chargedMajoranaBlock d) = chargedOneModeDeterminant d := by
  simp [pfaffian2x2, chargedMajoranaBlock, chargedOneModeDeterminant]

/-! ## Spectral-flow signs -/

/-- A mod-two index parity, used to express `(-1)^I` without introducing the
analytic index theorem as a local assumption. -/
def paritySign (p : Bool) : ℤ :=
  if p then -1 else 1

/-- Complex version of the parity sign. -/
def paritySignC (p : Bool) : ℂ :=
  (paritySign p : ℂ)

@[simp] lemma paritySign_false : paritySign false = 1 := rfl
@[simp] lemma paritySign_true : paritySign true = -1 := rfl

@[simp] lemma paritySignC_false : paritySignC false = 1 := by
  simp [paritySignC]

@[simp] lemma paritySignC_true : paritySignC true = -1 := by
  simp [paritySignC]

/-- The sign representation is multiplicative for addition of mod-two
spectral-flow parities. -/
lemma paritySignC_xor (p q : Bool) :
    paritySignC (Bool.xor p q) = paritySignC p * paritySignC q := by
  cases p <;> cases q <;> norm_num [paritySignC, paritySign, Bool.xor]

/-- Two identical Dirac copies remove the mod-two sign ambiguity; this is the
finite algebraic content behind Eq. (2.8) versus Eq. (2.9). -/
lemma twoDiracCopies_sign_trivial (p : Bool) :
    paritySignC p * paritySignC p = 1 := by
  cases p <;> norm_num [paritySignC, paritySign]

/-- Dirac spectral-flow transform from Eq. (2.11)-(2.12). -/
def diracSpectralFlowTransform (Z : ℂ) (indexParity : Bool) : ℂ :=
  Z * paritySignC indexParity

/-- Eq. (2.12): spectral flow by parity `I` multiplies the Dirac path integral
by `(-1)^I`. -/
lemma diracSpectralFlowTransform_eq (Z : ℂ) (indexParity : Bool) :
    diracSpectralFlowTransform Z indexParity = Z * paritySignC indexParity := rfl

/-- Majorana spectral-flow transform from Eq. (2.64)-(2.65), using the parity
of the half-index `I/2`. -/
def majoranaSpectralFlowTransform (Pf : ℂ) (halfIndexParity : Bool) : ℂ :=
  Pf * paritySignC halfIndexParity

/-- Eq. (2.65): Majorana spectral flow multiplies the Pfaffian by
`(-1)^(I/2)`. -/
lemma majoranaSpectralFlowTransform_eq (Pf : ℂ) (halfIndexParity : Bool) :
    majoranaSpectralFlowTransform Pf halfIndexParity =
      Pf * paritySignC halfIndexParity := rfl

/-! ## Eta phases and Dai-Freed cancellation -/

/-- Dirac eta-invariant boundary phase `exp(-i*pi*eta/2)`, Eq. (2.16). -/
noncomputable def diracEtaBoundaryPhase (eta : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((Real.pi * eta / 2 : ℝ) : ℂ)))

/-- Majorana eta-invariant boundary phase `exp(-i*pi*eta/4)`, Eq. (2.67). -/
noncomputable def majoranaEtaBoundaryPhase (eta : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((Real.pi * eta / 4 : ℝ) : ℂ)))

/-- Generic bulk theta phase.  In Eq. (2.26) the parameter is `P - Ahat(R)`;
in Eq. (2.72) it is `Ahat(R)/2` with the appropriate sign convention. -/
noncomputable def bulkThetaPhase (theta : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi * theta : ℝ) : ℂ))

/-- Dirac Dai-Freed cancellation: once the APS/index input supplies the
bulk-boundary phase identity, the regulated boundary partition is a signed
absolute partition function.  This is Eq. (2.26)-(2.27) as a checked algebraic
consequence. -/
lemma dirac_bulk_boundary_cancellation
    (absZ theta eta : ℝ) (indexParity : Bool)
    (hAPS :
      diracEtaBoundaryPhase eta * bulkThetaPhase theta =
        paritySignC indexParity) :
    ((absZ : ℂ) * diracEtaBoundaryPhase eta) * bulkThetaPhase theta =
      (absZ : ℂ) * paritySignC indexParity := by
  rw [mul_assoc, hAPS]

/-- Majorana Dai-Freed cancellation: Eq. (2.72)-(2.73) with the APS/index
input isolated as the named hypothesis. -/
lemma majorana_bulk_boundary_cancellation
    (absPf theta eta : ℝ) (halfIndexParity : Bool)
    (hAPS :
      majoranaEtaBoundaryPhase eta * bulkThetaPhase theta =
        paritySignC halfIndexParity) :
    ((absPf : ℂ) * majoranaEtaBoundaryPhase eta) * bulkThetaPhase theta =
      (absPf : ℂ) * paritySignC halfIndexParity := by
  rw [mul_assoc, hAPS]

/-- Pin+ topological-superconductor eta phase for `nu` Majorana fermions,
matching the multiplicative form used around Eq. (4.7)-(4.10). -/
noncomputable def pinPlusEtaPhase (nu : ℕ) (eta : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (((nu : ℝ) * Real.pi * eta / 2 : ℝ) : ℂ)))

/-- Eq. (4.10), written as the combined finite carrier: the absolute
Pfaffian times the Pin+ eta phase. -/
noncomputable def pinPlusCombinedPartition (absPf : ℝ) (nu : ℕ) (eta : ℝ) : ℂ :=
  (absPf : ℂ) * pinPlusEtaPhase nu eta

lemma pinPlusCombinedPartition_eq (absPf : ℝ) (nu : ℕ) (eta : ℝ) :
    pinPlusCombinedPartition absPf nu eta =
      (absPf : ℂ) * pinPlusEtaPhase nu eta := rfl

/-! ## Finite stacking classifications -/

/-- The 3+1d Pin+ topological-superconductor stacking class.  The analytic
paper identifies this as the 16-periodic interacting classification. -/
abbrev PinPlusStackingClass := ZMod 16

/-- Stacking class of `nu` identical Pin+ Majorana cones. -/
def pinPlusStackingClass (nu : ℕ) : PinPlusStackingClass :=
  nu

/-- Stacking adds the number of Majorana cones. -/
lemma pinPlusStackingClass_add (nu mu : ℕ) :
    pinPlusStackingClass (nu + mu) =
      pinPlusStackingClass nu + pinPlusStackingClass mu := by
  simp [pinPlusStackingClass, Nat.cast_add]

/-- Sixteen copies are trivial in the Pin+ stacking class. -/
lemma pinPlusStackingClass_sixteen_trivial :
    pinPlusStackingClass 16 = 0 := by
  change (16 : ZMod 16) = 0
  exact ZMod.natCast_self 16

/-- Periodicity of the Pin+ stacking class. -/
lemma pinPlusStackingClass_period_sixteen (nu : ℕ) :
    pinPlusStackingClass (nu + 16) = pinPlusStackingClass nu := by
  rw [pinPlusStackingClass_add, pinPlusStackingClass_sixteen_trivial, add_zero]

/-- The `nu=8` class is order two: it is detected on mapping tori by the
`w4` sign in Eq. (4.15), while two such stacks are trivial in the full
16-periodic class. -/
lemma pinPlusStackingClass_eight_order_two :
    pinPlusStackingClass 8 + pinPlusStackingClass 8 = 0 := by
  decide

/-- The Majorana-chain bulk phase in Section 5 is eight-periodic. -/
abbrev MajoranaChainStackingClass := ZMod 8

/-- Stacking class of `nu` Majorana chains. -/
def majoranaChainStackingClass (nu : ℕ) : MajoranaChainStackingClass :=
  nu

/-- Stacking adds Majorana-chain phases. -/
lemma majoranaChainStackingClass_add (nu mu : ℕ) :
    majoranaChainStackingClass (nu + mu) =
      majoranaChainStackingClass nu + majoranaChainStackingClass mu := by
  simp [majoranaChainStackingClass, Nat.cast_add]

/-- Eight Majorana chains have trivial bulk phase. -/
lemma majoranaChainStackingClass_eight_trivial :
    majoranaChainStackingClass 8 = 0 := by
  change (8 : ZMod 8) = 0
  exact ZMod.natCast_self 8

/-- Periodicity of the Majorana-chain phase. -/
lemma majoranaChainStackingClass_period_eight (nu : ℕ) :
    majoranaChainStackingClass (nu + 8) = majoranaChainStackingClass nu := by
  rw [majoranaChainStackingClass_add, majoranaChainStackingClass_eight_trivial, add_zero]

/-! ## Links to existing Physlib infrastructure -/

open Fermion.PartitionFunction
open Fermion.SpinStructureCount

/-- The Witten path-integral layer reuses the already-formalized finite
fermionic Fock trace: one mode contributes `1 + exp(-beta E)`, and this
absolute partition factor is positive. -/
lemma witten_reuses_finite_fermion_partition (E beta : ℝ) :
    (fermionicPartition E beta =
        ∑ n : Fin 2, Real.exp (-(beta * E * (n : ℝ)))) ∧
      0 < fermionicPartition E beta := by
  exact ⟨fermionicPartition_eq_fock_trace E beta, fermionicPartition_pos E beta⟩

/-- Spin structures used by the Witten eta/Pfaffian story are the same finite
spin-structure counters already present in the repository. -/
lemma witten_reuses_torus_spin_structure_count :
    numEvenSpinStructures 1 = 3 ∧
      numOddSpinStructures 1 = 1 ∧
      numEvenSpinStructures 1 + numOddSpinStructures 1 = 4 := by
  exact ⟨torus_spin_structure_count.1, torus_spin_structure_count.2,
    by norm_num [numEvenSpinStructures, numOddSpinStructures]⟩

/-- On a genus-`g` region, the same spin-structure counter supplies the
`2^(2g)` sectors over which fermionic path integrals are summed. -/
lemma witten_reuses_region_spin_structures (g : ℕ) (hg : 0 < g) :
    numEvenSpinStructures g + numOddSpinStructures g = 4 ^ g ∧
      numEvenSpinStructures g - numOddSpinStructures g = 2 ^ g ∧
      modularT oddTorusSpinStructure = oddTorusSpinStructure ∧
      modularS oddTorusSpinStructure = oddTorusSpinStructure := by
  exact fermion_region_spin_structures g hg

/-- The finite CAR model used for fermionic modes is available from
`Bogoliubov.FermionicBogoliubovCAR`: the one-mode creation/annihilation anticommutator is
the identity matrix. -/
lemma witten_reuses_finite_CAR :
    Bogoliubov.FermionicBogoliubovCAR.anticomm Bogoliubov.FermionicBogoliubovCAR.aOp
        Bogoliubov.FermionicBogoliubovCAR.aDagOp =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  exact Bogoliubov.FermionicBogoliubovCAR.car_a_aDag

/-- The Pin/Clifford reflection infrastructure supplies the real Lorentzian
quadratic form used by the Pin+ discussion. -/
lemma witten_reuses_pin_reflection_isometry
    (v x : Fin 4 → ℝ) (hv : PTSymmetricQFT.CliffordPinReflection.minkBilin v v ≠ 0) :
    spaceTime.γ.diracForm
        (PTSymmetricQFT.CliffordPinReflection.reflect v x) =
      spaceTime.γ.diracForm x := by
  exact PTSymmetricQFT.CliffordPinReflection.reflect_preserves_diracForm v x hv

/-- The complex-action path-integral weight file already supplies the common
master weight.  Witten's eta phases plug into the same "phase times damping"
architecture rather than introducing a second path-integral convention. -/
lemma witten_reuses_complex_action_master_weight
    (realAction imaginaryAction hbar : ℝ) (hhbar : hbar ≠ 0) :
    PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsenComplexActionWeight
        realAction imaginaryAction hbar =
      PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight
        realAction imaginaryAction hbar := by
  exact PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsen_eq_master realAction imaginaryAction hbar hhbar

/-! ## Feynman-Kac, Matsubara, Lorentzian, and QED path-integral links -/

/-- The charged one-mode Witten Pfaffian/determinant identity is the same
finite Grassmann/Berezin determinant used by the QED functional-integral
construction. -/
lemma witten_chargedPfaffian_eq_qed_berezin_det (m : ℝ) :
    pfaffian2x2 (chargedMajoranaBlock (m : ℂ)) =
      (((!![m] : Matrix (Fin 1) (Fin 1) ℝ).det : ℝ) : ℂ) := by
  calc
    pfaffian2x2 (chargedMajoranaBlock (m : ℂ)) = (m : ℂ) := by
      simp [pfaffian2x2, chargedMajoranaBlock]
    _ = (PathIntegral.QEDFunctionalIntegralConstruction.berezin
          (PathIntegral.QEDFunctionalIntegralConstruction.fermionGaussian m) : ℂ) := by
      rfl
    _ = (((!![m] : Matrix (Fin 1) (Fin 1) ℝ).det : ℝ) : ℂ) := by
      rw [PathIntegral.QEDFunctionalIntegralConstruction.berezin_gaussian_eq_det]

/-- The Dirac eta boundary phase is a Lorentzian unit-modulus kernel at
`hbar = 1`, with zero imaginary action. -/
lemma diracEtaBoundaryPhase_eq_lorentzianKernel_unit (eta : ℝ) :
    diracEtaBoundaryPhase eta =
      lorentzianKernel (-(Real.pi * eta / 2)) 0 1 := by
  unfold diracEtaBoundaryPhase lorentzianKernel
  congr 1
  push_cast
  ring

/-- The Majorana eta boundary phase is the analogous Lorentzian unit-modulus
kernel with the Majorana quarter-eta coefficient. -/
lemma majoranaEtaBoundaryPhase_eq_lorentzianKernel_unit (eta : ℝ) :
    majoranaEtaBoundaryPhase eta =
      lorentzianKernel (-(Real.pi * eta / 4)) 0 1 := by
  unfold majoranaEtaBoundaryPhase lorentzianKernel
  congr 1
  push_cast
  ring

/-- The Pin+ `nu`-Majorana eta phase is a Lorentzian phase-only kernel at
`hbar = 1`. -/
lemma pinPlusEtaPhase_eq_lorentzianKernel_unit (nu : ℕ) (eta : ℝ) :
    pinPlusEtaPhase nu eta =
      lorentzianKernel (-((nu : ℝ) * Real.pi * eta / 2)) 0 1 := by
  unfold pinPlusEtaPhase lorentzianKernel
  congr 1
  push_cast
  ring

/-- Witten's Dirac eta phase has unit norm, proved through the existing
Lorentzian-kernel damping theorem. -/
lemma diracEtaBoundaryPhase_norm (eta : ℝ) :
    ‖diracEtaBoundaryPhase eta‖ = 1 := by
  rw [diracEtaBoundaryPhase_eq_lorentzianKernel_unit,
    lorentzianKernel_norm_is_damping]
  norm_num

/-- Witten's Majorana eta phase also has unit norm, since it is a pure
Lorentzian phase. -/
lemma majoranaEtaBoundaryPhase_norm (eta : ℝ) :
    ‖majoranaEtaBoundaryPhase eta‖ = 1 := by
  rw [majoranaEtaBoundaryPhase_eq_lorentzianKernel_unit,
    lorentzianKernel_norm_is_damping]
  norm_num

/-- The Lorentzian kernel modulus is exactly the Feynman-Kac weight under the
constant-potential identification `S_I = V * T * hbar`. -/
lemma witten_lorentzianKernel_norm_eq_feynmanKac_weight
    (S_R S_I V T hbar : ℝ) (hhbar : 0 < hbar)
    (hSI : S_I = V * T * hbar) :
    ‖lorentzianKernel S_R S_I hbar‖ =
      feynman_kac_weight (fun _ : Unit => V) T () := by
  rw [lorentzianKernel_norm_is_damping]
  exact fk_euclidean_entropic_damping_correspondence V T hbar hhbar S_I hSI

/-- The same Lorentzian modulus is the path-integral damping scalar from the
Wick-clock bridge. -/
lemma witten_lorentzianKernel_modulus_is_pathIntegralDamping
    (S_R S_I hbar : ℝ) :
    ‖lorentzianKernel S_R S_I hbar‖ = path_integral_damping hbar S_I := by
  exact lorentzianKernel_modulus_invariant_under_wick S_R S_I hbar

/-- The single-mode Witten/Fock fermion partition is the Feynman-Kac weight
plus the empty state. -/
lemma witten_fermionicPartition_eq_feynmanKac_weight
    (E : ℝ) (T : ThermalCircle) :
    fermionicPartition E T.beta =
      1 + feynman_kac_weight (fun _ : Unit => E) T.beta () := by
  unfold fermionicPartition feynman_kac_weight
  ring_nf

/-- The Matsubara weight is the same real scalar as the constant-potential
Feynman-Kac weight. -/
lemma witten_matsubaraWeight_re_eq_feynmanKac_weight
    (E : ℝ) (T : ThermalCircle) :
    (Physlib.QFT.Matsubara.PathIntegral.matsubaraWeight E T).re =
      Physlib.QFT.PathIntegral.feynman_kac_weight
        (fun _ : Unit => E) T.beta () := by
  unfold Physlib.QFT.Matsubara.PathIntegral.matsubaraWeight
    Physlib.QFT.PathIntegral.feynman_kac_weight
  rw [Complex.ofReal_re]
  ring_nf

/-- Witten's fermion thermal trace reuses the repository Matsubara/FK bridge:
the nonempty fermion occupation contribution is simultaneously the Matsubara
weight and the Feynman-Kac weight. -/
lemma witten_fermionicPartition_matsubara_feynmanKac
    (E : ℝ) (T : ThermalCircle) :
    fermionicPartition E T.beta =
      1 + (Physlib.QFT.Matsubara.PathIntegral.matsubaraWeight E T).re ∧
    (Physlib.QFT.Matsubara.PathIntegral.matsubaraWeight E T).re =
      Physlib.QFT.PathIntegral.feynman_kac_weight
        (fun _ : Unit => E) T.beta () := by
  exact ⟨fermionicPartition_eq_matsubara E T,
    witten_matsubaraWeight_re_eq_feynmanKac_weight E T⟩

/-- The fermionic Matsubara/KMS antiperiodicity used by Witten's fermion
path-integral signs is the existing Matsubara theorem. -/
lemma witten_reuses_fermionic_matsubara_antiperiodicity
    (T : ThermalCircle) (n : ℤ) (tau : ℝ) :
    matsubaraModeFermion T n (tau + T.period) =
      -matsubaraModeFermion T n tau := by
  exact matsubaraModeFermion_antiperiodic T n tau

/-- The Matsubara weight is the one-period Wick rotation of the reversible
Lorentzian phase, using the repo's Wick-clock bridge. -/
lemma witten_matsubaraWeight_eq_wickRotate
    (E : ℝ) (T : ThermalCircle) :
    Physlib.QFT.Matsubara.PathIntegral.matsubaraWeight E T =
      reversiblePhaseC E T.hbar
        (Physlib.QFT.PathIntegral.wickRotate T.period) := by
  exact Physlib.QFT.PathIntegral.matsubaraWeight_eq_wickRotate E T

/-- The entropically damped QED exchange path integral used elsewhere in the
repo is a finite Bochner integral; Witten's fermionic path-integral layer can
therefore feed into the same measure-valid complex QED carrier. -/
lemma witten_reuses_qed_amplitude_bochner_finite
    (hbar HI1 HI2 : ℝ) (hhbar : 0 < hbar) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖((PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel hbar HI1 HI2 hhbar h1 h2).complexFKExpectation
        (fun _ => 1))‖
      ≤ 1 * (PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel hbar HI1 HI2 hhbar h1 h2).partitionFunction := by
  exact PathIntegral.QEDPathIntegralMeasureValid.qed_amplitude_bochner_finite hbar HI1 HI2 hhbar h1 h2

/-- The QED renormalization/regularization scalar is the same entropic damping
that appears as the Lorentzian-kernel modulus and the Feynman-Kac weight. -/
lemma witten_reuses_qed_entropic_regulator (S_I hbar : ℝ) :
    Real.exp (-(S_I / hbar)) =
      entropyDamping S_I hbar := by
  exact PathIntegral.QEDFunctionalIntegralConstruction.renorm_regulator_is_entropic S_I hbar

end ChernSimons.WittenFermionPathIntegralsTopologicalPhases
end ComplexAction
end QuantumMechanics
end Physlib
