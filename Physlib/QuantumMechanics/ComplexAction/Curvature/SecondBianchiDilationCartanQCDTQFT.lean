/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBianchiIntegrability
public import Physlib.QuantumMechanics.ComplexAction.Particles.QCDFundamentalBCJRelations
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ConcreteSynthesis
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
meta import Zil

/-!
# Second Bianchi under dilations, and its Cartan/QCD/TQFT faces

This module supplies the missing typed composition among four existing sectors.

* `dilateBianchiTensor` is the multiplicative dilation-group action on the covariant-curvature
  derivative carrier.  Identity and composition are proved, and `secondBianchi_dilation_iff`
  proves that the differential second Bianchi identity is invariant under every nonzero dilation.
* `dilateDifferentialForm` carries the same group action to continuum forms.  The
  Mayr--Stieberger Green--Schwarz three-form is equivariant, its Pontryagin-sourced modified
  Bianchi equation is dilation covariant, and `stringScale_dilationGroup` intertwines the bundled
  dilation action with the Planck-to-string scale map at fixed dimensionless `Re S`.
* `secondBianchi_greenSchwarz_dilation` proves that one dilation preserves the gravitational and
  antisymmetric-tensor Bianchi equations simultaneously without identifying the two equations.
* `continuumPontryagin` instantiates the Chern--Weil source with the repository's normalized
  continuum wedge constructor: `F ∧ F`.  Weight-one curvature gives a weight-two four-form.  The
  weighted Green--Schwarz theorem then keeps `k` fixed, and the conservation capstone uses the
  contracted second Bianchi plus the Einstein equation to derive `divT = 0`.
* `secondBianchi_dilation_einsteinCartan` uses the *same* dilation element on the curvature carrier
  and on the axial current.  The second Bianchi constraint survives while the inverse-square
  coupling weight preserves the eliminated Hehl--Datta contact density.
* `qcd_bcj_secondBianchi_conservation` places the fundamental primitive-QCD BCJ relation beside the
  existing BCJ dual-Bianchi carrier.  The QCD input supplies both amplitude relations; the gravity
  second Bianchi plus Einstein equation supplies stress-energy conservation.
* `secondBianchi_cartan_qcd_tqft_faces` assembles the differential gravity identity, the Cartan
  gauge-Jacobi identity, primitive-QCD BCJ relations, and the finite Chern--Simons flat/gauge-Bianchi
  sector without identifying these distinct identities definitionally.

## Honest scope

The dilation is constant; a position-dependent Weyl factor would add derivative-of-scale terms to
the form equation.  The Einstein--Cartan statement uses the already explicit algebraic
current/coupling weights; it does not infer a spinor conformal weight.  QCD BCJ data does not by
itself prove the gravitational second Bianchi identity: both enter the checked double-copy
compatibility theorem through visible hypotheses.  The TQFT result is the repository's finite local
Chern--Simons/trivial-bundle carrier plus its Maxwell--Faraday gauge shadow; it is not a global
non-abelian Chern--Weil theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations
open Physlib.QuantumMechanics.ComplexAction.EinsteinCartanAxialTorsion
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBianchiIntegrability
open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.Particles.QCDFundamentalBCJRelations
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.Mathematics.LovelockRund
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT

/-! ## A. The dilation-group action on the differential-curvature carrier -/

/-- A nonzero real dilation acts on the covariant-curvature derivative by scalar multiplication. -/
def dilateBianchiTensor {κ : Type*} (r : ℝˣ)
    (D : κ → κ → κ → κ → κ → ℝ) : κ → κ → κ → κ → κ → ℝ :=
  fun a b c d e => (r : ℝ) * D a b c d e

/-- The identity dilation fixes the differential-curvature carrier. -/
@[zil_level bridge_theorem]
lemma dilateBianchiTensor_one {κ : Type*}
    (D : κ → κ → κ → κ → κ → ℝ) :
    dilateBianchiTensor (1 : ℝˣ) D = D := by
  funext a b c d e
  simp [dilateBianchiTensor]

/-- Multiplication in `ℝˣ` is composition of the dilation action. -/
@[zil_level bridge_theorem]
lemma dilateBianchiTensor_mul {κ : Type*} (r s : ℝˣ)
    (D : κ → κ → κ → κ → κ → ℝ) :
    dilateBianchiTensor (r * s) D =
      dilateBianchiTensor r (dilateBianchiTensor s D) := by
  funext a b c d e
  simp [dilateBianchiTensor]
  ring

/-- Applying a dilation followed by its inverse recovers the original carrier. -/
@[zil_level bridge_theorem]
lemma dilateBianchiTensor_inv_apply {κ : Type*} (r : ℝˣ)
    (D : κ → κ → κ → κ → κ → ℝ) :
    dilateBianchiTensor r⁻¹ (dilateBianchiTensor r D) = D := by
  rw [← dilateBianchiTensor_mul]
  simpa using dilateBianchiTensor_one D

/-- **The differential second Bianchi identity is dilation invariant.**  Because the group element
is nonzero, the cyclic sum vanishes after dilation exactly when it vanished before dilation. -/
@[zil_level physical_theorem]
theorem secondBianchi_dilation_iff {κ : Type*} (r : ℝˣ)
    (D : κ → κ → κ → κ → κ → ℝ) :
    SecondBianchi (dilateBianchiTensor r D) ↔ SecondBianchi D := by
  constructor
  · intro h a b c d e
    have hs := h a b c d e
    simp only [cyclicSum, dilateBianchiTensor] at hs
    have hr : (r : ℝ) * (D a b c d e + D a b d e c + D a b e c d) = 0 := by
      linarith
    exact (mul_eq_zero.mp hr).resolve_left r.ne_zero
  · intro h a b c d e
    simp only [cyclicSum, dilateBianchiTensor]
    have hh := h a b c d e
    simp only [cyclicSum] at hh
    linear_combination (r : ℝ) * hh

/-! ## A.1. The same dilation on the Mayr--Stieberger tensor sector -/

/-- The nonzero-real dilation group acts on genuine differential forms by scalar multiplication.
This is the form-valued representation corresponding to the repository's bundled coordinate-vector
`dilationGroup`. -/
def dilateDifferentialForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ}
    (r : ℝˣ) (omega : DifferentialForm ℝ E ℝ n) : DifferentialForm ℝ E ℝ n :=
  (r : ℝ) • omega

/-- The identity dilation fixes every differential form. -/
@[zil_level bridge_theorem]
lemma dilateDifferentialForm_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ}
    (omega : DifferentialForm ℝ E ℝ n) :
    dilateDifferentialForm (1 : ℝˣ) omega = omega := by
  simp [dilateDifferentialForm]

/-- Multiplication in `ℝˣ` is composition on differential forms. -/
@[zil_level bridge_theorem]
lemma dilateDifferentialForm_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ}
    (r s : ℝˣ) (omega : DifferentialForm ℝ E ℝ n) :
    dilateDifferentialForm (r * s) omega =
      dilateDifferentialForm r (dilateDifferentialForm s omega) := by
  simp [dilateDifferentialForm, smul_smul]

/-- The inverse group element undoes the dilation of a differential form. -/
@[zil_level bridge_theorem]
lemma dilateDifferentialForm_inv_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ}
    (r : ℝˣ) (omega : DifferentialForm ℝ E ℝ n) :
    dilateDifferentialForm r⁻¹ (dilateDifferentialForm r omega) = omega := by
  rw [← dilateDifferentialForm_mul]
  simpa using dilateDifferentialForm_one omega

/-- The Green--Schwarz field-strength construction is equivariant for the same constant dilation:
scaling both `B` and its Chern--Simons transgression scales `H = dB - k omega3` once. -/
@[zil_level physical_theorem]
theorem greenSchwarzTensorFieldStrength_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝˣ) (B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ) :
    greenSchwarzTensorFieldStrength (dilateDifferentialForm r B)
        (dilateDifferentialForm r omega3) k =
      dilateDifferentialForm r (greenSchwarzTensorFieldStrength B omega3 k) := by
  funext x
  rw [show greenSchwarzTensorFieldStrength (dilateDifferentialForm r B)
      (dilateDifferentialForm r omega3) k x =
      extDeriv ((r : ℝ) • B) x + (-k) • ((r : ℝ) • omega3) x by rfl]
  rw [extDeriv_smul]
  simp only [Pi.smul_apply, dilateDifferentialForm]
  rw [show greenSchwarzTensorFieldStrength B omega3 k x =
      extDeriv B x + (-k) • omega3 x by rfl]
  module

/-- The Pontryagin-sourced Green--Schwarz Bianchi equation is dilation covariant.  Unlike a
position-dependent Weyl rescaling, the constant group element commutes with `extDeriv`. -/
@[zil_level physical_theorem]
theorem greenSchwarz_modifiedBianchi_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝˣ) (B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3)
    (P4 : DifferentialForm ℝ E ℝ 4) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) = (-k) • P4) :
    extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm r B)
        (dilateDifferentialForm r omega3) k) =
      (-k) • dilateDifferentialForm r P4 := by
  rw [greenSchwarzTensorFieldStrength_dilation]
  funext x
  simp only [dilateDifferentialForm]
  rw [extDeriv_smul]
  rw [congrFun hH x]
  simp only [Pi.smul_apply]
  module

/-- The Mayr--Stieberger Planck/string scale relation intertwines the repository's bundled
coordinate-vector dilation group.  The dilaton `Re S` is dimensionless and therefore held fixed. -/
@[zil_level bridge_theorem]
theorem stringScale_dilationGroup (r : ℝˣ) (MPlanck dilaton : ℝ) :
    stringScale (dilationGroup Unit r (fun _ => MPlanck) ()) dilaton =
      dilationGroup Unit r (fun _ => stringScale MPlanck dilaton) () := by
  rw [dilationGroup_apply, dilationGroup_apply]
  simp only [Pi.smul_apply]
  simp [stringScale]
  ring

/-- **Second-Bianchi/Green--Schwarz dilation bridge.**  One nonzero-real group element preserves
both distinct cyclic structures: the gravitational differential second Bianchi identity and the
Pontryagin-sourced antisymmetric-tensor Bianchi equation.  They are simultaneous consequences, not
identified definitionally. -/
@[zil_level physical_theorem]
theorem secondBianchi_greenSchwarz_dilation
    {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : κ → κ → κ → κ → κ → ℝ) (hD : SecondBianchi D) (r : ℝˣ)
    (B : DifferentialForm ℝ E ℝ 2) (omega3 : DifferentialForm ℝ E ℝ 3)
    (P4 : DifferentialForm ℝ E ℝ 4) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) = (-k) • P4) :
    SecondBianchi (dilateBianchiTensor r D) ∧
      extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm r B)
          (dilateDifferentialForm r omega3) k) =
        (-k) • dilateDifferentialForm r P4 :=
  ⟨(secondBianchi_dilation_iff r D).2 hD,
    greenSchwarz_modifiedBianchi_dilation r B omega3 P4 k hH⟩

/-! ## A.2. Quadratic Pontryagin weight and contracted conservation -/

/-- The quadratic four-form produced from a curvature two-form by a bundled bilinear pairing.
This generic interface remains useful for traced or Lie-algebra-valued pairings; the scalar-valued
continuum wedge is instantiated below by `continuumPontryagin`. -/
def quadraticPontryagin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pairing : DifferentialForm ℝ E ℝ 2 →ₗ[ℝ]
      DifferentialForm ℝ E ℝ 2 →ₗ[ℝ] DifferentialForm ℝ E ℝ 4)
    (F : DifferentialForm ℝ E ℝ 2) : DifferentialForm ℝ E ℝ 4 :=
  pairing F F

/-- A weight-one dilation of curvature gives the quadratic Pontryagin four-form weight two. -/
@[zil_level physical_theorem]
theorem quadraticPontryagin_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pairing : DifferentialForm ℝ E ℝ 2 →ₗ[ℝ]
      DifferentialForm ℝ E ℝ 2 →ₗ[ℝ] DifferentialForm ℝ E ℝ 4)
    (r : ℝˣ) (F : DifferentialForm ℝ E ℝ 2) :
    quadraticPontryagin pairing (dilateDifferentialForm r F) =
      dilateDifferentialForm (r ^ 2) (quadraticPontryagin pairing F) := by
  simp [quadraticPontryagin, dilateDifferentialForm, smul_smul, pow_two]

/-- The concrete scalar-valued Pontryagin four-form `F ∧ F`, formed using the normalized continuum
wedge on continuous alternating maps. -/
def continuumPontryagin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : DifferentialForm ℝ E ℝ 2) : DifferentialForm ℝ E ℝ 4 :=
  continuumWedge F F

/-- The concrete constructor is an instance of the generic quadratic pairing, rather than a new
parallel definition of the exterior product. -/
@[zil_level bridge_theorem]
theorem continuumPontryagin_eq_quadraticPontryagin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : DifferentialForm ℝ E ℝ 2) :
    continuumPontryagin F =
      quadraticPontryagin (continuumWedgeBilinear 2 2) F :=
  rfl

/-- A weight-one dilation of curvature gives the concrete continuum `F ∧ F` source weight two. -/
@[zil_level physical_theorem]
theorem continuumPontryagin_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝˣ) (F : DifferentialForm ℝ E ℝ 2) :
    continuumPontryagin (dilateDifferentialForm r F) =
      dilateDifferentialForm (r ^ 2) (continuumPontryagin F) := by
  simpa [continuumPontryagin, quadraticPontryagin] using
    quadraticPontryagin_dilation (continuumWedgeBilinear 2 2) r F

/-- Polarization of the concrete continuum Pontryagin source.  Even-degree graded commutativity
combines the two cross terms into `2 (F ∧ G)`. -/
@[zil_level physical_theorem]
theorem continuumPontryagin_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : DifferentialForm ℝ E ℝ 2) :
    continuumPontryagin (F + G) =
      continuumPontryagin F + 2 • continuumWedge F G + continuumPontryagin G := by
  unfold continuumPontryagin
  rw [show continuumWedge (F + G) (F + G) =
      continuumWedge F F + continuumWedge F G +
        (continuumWedge G F + continuumWedge G G) by
    change continuumWedgeBilinear 2 2 (F + G) (F + G) = _
    rw [map_add]
    change continuumWedge (F + G) F + continuumWedge (F + G) G = _
    rw [show continuumWedge (F + G) F =
        continuumWedge F F + continuumWedge G F by
      change continuumWedgeBilinear 2 2 (F + G) F = _
      rw [map_add]
      rfl]
    rw [show continuumWedge (F + G) G =
        continuumWedge F G + continuumWedge G G by
      change continuumWedgeBilinear 2 2 (F + G) G = _
      rw [map_add]
      rfl]
    abel]
  rw [continuumWedge_two_comm G F]
  module

/-- The concrete continuum Pontryagin source is natural under pullback. -/
@[zil_level physical_theorem]
theorem pullbackForm_continuumPontryagin
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (F : DifferentialForm ℝ E ℝ 2) (f : E' → E) :
    pullbackForm (continuumPontryagin F) f =
      continuumPontryagin (pullbackForm F f) := by
  simpa [continuumPontryagin] using pullbackForm_continuumWedge F F f

/-- With `P4 = pairing F F`, curvature has dilation weight one while `B`, `omega3`, and `H`
have weight two.  The Green--Schwarz coupling `k` therefore remains unchanged. -/
@[zil_level physical_theorem]
theorem greenSchwarz_quadraticPontryagin_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pairing : DifferentialForm ℝ E ℝ 2 →ₗ[ℝ]
      DifferentialForm ℝ E ℝ 2 →ₗ[ℝ] DifferentialForm ℝ E ℝ 4)
    (r : ℝˣ) (F B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) =
      (-k) • quadraticPontryagin pairing F) :
    extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm (r ^ 2) B)
        (dilateDifferentialForm (r ^ 2) omega3) k) =
      (-k) • quadraticPontryagin pairing (dilateDifferentialForm r F) := by
  rw [quadraticPontryagin_dilation]
  exact greenSchwarz_modifiedBianchi_dilation (r ^ 2) B omega3
    (quadraticPontryagin pairing F) k hH

/-- The Green--Schwarz modified Bianchi equation with the *constructed* continuum `F ∧ F` source is
dilation covariant.  This closes the former abstract-pairing boundary for scalar-valued curvature
forms. -/
@[zil_level physical_theorem]
theorem greenSchwarz_continuumPontryagin_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝˣ) (F B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) =
      (-k) • continuumPontryagin F) :
    extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm (r ^ 2) B)
        (dilateDifferentialForm (r ^ 2) omega3) k) =
      (-k) • continuumPontryagin (dilateDifferentialForm r F) := by
  simpa [continuumPontryagin, quadraticPontryagin] using
    greenSchwarz_quadraticPontryagin_dilation (continuumWedgeBilinear 2 2)
      r F B omega3 k hH

/-- The same group element preserves the gravitational second Bianchi identity and the weighted
Green--Schwarz equation, while exposing the independently proved quadratic source scaling. -/
@[zil_level physical_theorem]
theorem secondBianchi_greenSchwarz_quadraticPontryagin_dilation
    {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : κ → κ → κ → κ → κ → ℝ) (hD : SecondBianchi D)
    (pairing : DifferentialForm ℝ E ℝ 2 →ₗ[ℝ]
      DifferentialForm ℝ E ℝ 2 →ₗ[ℝ] DifferentialForm ℝ E ℝ 4)
    (r : ℝˣ) (F B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) =
      (-k) • quadraticPontryagin pairing F) :
    SecondBianchi (dilateBianchiTensor r D) ∧
      quadraticPontryagin pairing (dilateDifferentialForm r F) =
        dilateDifferentialForm (r ^ 2) (quadraticPontryagin pairing F) ∧
      extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm (r ^ 2) B)
          (dilateDifferentialForm (r ^ 2) omega3) k) =
        (-k) • quadraticPontryagin pairing (dilateDifferentialForm r F) :=
  ⟨(secondBianchi_dilation_iff r D).2 hD,
    quadraticPontryagin_dilation pairing r F,
    greenSchwarz_quadraticPontryagin_dilation pairing r F B omega3 k hH⟩

/-- Concrete continuum-wedge capstone: one dilation preserves the gravitational second Bianchi
identity and transports both `F ∧ F` and the resulting Green--Schwarz Bianchi equation with their
proved weights. -/
@[zil_level physical_theorem]
theorem secondBianchi_greenSchwarz_continuumPontryagin_dilation
    {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : κ → κ → κ → κ → κ → ℝ) (hD : SecondBianchi D)
    (r : ℝˣ) (F B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) =
      (-k) • continuumPontryagin F) :
    SecondBianchi (dilateBianchiTensor r D) ∧
      continuumPontryagin (dilateDifferentialForm r F) =
        dilateDifferentialForm (r ^ 2) (continuumPontryagin F) ∧
      extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm (r ^ 2) B)
          (dilateDifferentialForm (r ^ 2) omega3) k) =
        (-k) • continuumPontryagin (dilateDifferentialForm r F) :=
  ⟨(secondBianchi_dilation_iff r D).2 hD,
    continuumPontryagin_dilation r F,
    greenSchwarz_continuumPontryagin_dilation r F B omega3 k hH⟩

/-- **Weighted Bianchi/conservation capstone.**  In addition to both dilation-covariant Bianchi
faces, the contracted gravitational second Bianchi identity and the Einstein equation force
stress-energy conservation.  The uncontracted-to-contracted metric contraction remains the
repository's explicitly separate input `hContracted`. -/
@[zil_level physical_theorem]
theorem secondBianchi_greenSchwarz_dilation_conservation
    {κ E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (D : κ → κ → κ → κ → κ → ℝ) (hD : SecondBianchi D)
    (pairing : DifferentialForm ℝ E ℝ 2 →ₗ[ℝ]
      DifferentialForm ℝ E ℝ 2 →ₗ[ℝ] DifferentialForm ℝ E ℝ 4)
    (r : ℝˣ) (F B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ)
    (hH : extDeriv (greenSchwarzTensorFieldStrength B omega3 k) =
      (-k) • quadraticPontryagin pairing F)
    (divRicci gradScalar divT : ι → ℝ) (einsteinCoupling : ℝ)
    (hCoupling : einsteinCoupling ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-einsteinCoupling) • divT)
    (hContracted : contractedSecondBianchi divRicci gradScalar) :
    SecondBianchi (dilateBianchiTensor r D) ∧
      extDeriv (greenSchwarzTensorFieldStrength (dilateDifferentialForm (r ^ 2) B)
          (dilateDifferentialForm (r ^ 2) omega3) k) =
        (-k) • quadraticPontryagin pairing (dilateDifferentialForm r F) ∧
      divT = 0 :=
  ⟨(secondBianchi_dilation_iff r D).2 hD,
    greenSchwarz_quadraticPontryagin_dilation pairing r F B omega3 k hH,
    bianchi_validates_fieldEquation divRicci gradScalar divT einsteinCoupling
      hCoupling hField hContracted⟩

/-! ## B. The same dilation in Einstein--Cartan theory -/

/-- The same group element preserves the second-Bianchi constraint and, after the explicit
`κ ↦ κ/r²` compensation, the eliminated Einstein--Cartan contact density. -/
@[zil_level physical_theorem]
theorem secondBianchi_dilation_einsteinCartan {κ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : κ → κ → κ → κ → κ → ℝ) (hD : SecondBianchi D)
    (kappa : ℝ) (r : ℝˣ) (J5 : ι → ℝ) :
    SecondBianchi (dilateBianchiTensor r D)
      ∧ hehlDattaContactDensity (kappa / (r : ℝ) ^ 2) (dilationGroup ι r J5) =
        hehlDattaContactDensity kappa J5 :=
  ⟨(secondBianchi_dilation_iff r D).2 hD,
    hehlDattaContactDensity_compensated_dilation_invariant kappa r J5⟩

/-! ## C. QCD/BCJ and the contracted gravity identity -/

/-- Primitive-QCD fundamental BCJ data supplies both equivalent amplitude relations.  Independently,
the gravity-side second Bianchi hypothesis, transported through the existing BCJ dual-Bianchi
carrier and Einstein equation, forces stress-energy conservation. -/
@[zil_level physical_theorem]
theorem qcd_bcj_secondBianchi_conservation
    {Insertion : Type*} [Fintype Insertion]
    (Q : QCDPrimitiveBCJInput Insertion)
    (kappa : ℝ) (hk : kappa ≠ 0) (divG divT : Fin 4 → ℝ)
    (hEin : divG = kappa • divT) (hSecond : divG = 0) :
    forwardBCJSum Q.weights Q.primitive.amplitude = 0
      ∧ backwardBCJSum Q.weights Q.primitive.amplitude = 0
      ∧ (bcjDualBianchi kappa hk divG divT hEin).firstBianchi
      ∧ divT = 0 :=
  ⟨Q.forward_relation,
    qcdPrimitiveBCJ_backward_relation Q,
    bcjDualBianchi_firstBianchi kappa hk divG divT hEin,
    contracted_bianchi_conservation kappa hk divG divT hEin hSecond⟩

/-! ## D. Cartan, QCD, and Chern--Simons/TQFT faces -/

/-- **Cross-sector Bianchi capstone.**  One theorem records the compatible consequences actually
proved by the repository: dilation invariance of the gravity second Bianchi; the Cartan
covariant-Bianchi Jacobi core; both primitive-QCD BCJ relations; and, in the finite flat local
Chern--Simons sector, vanishing complex CSW action together with gauge invariance and the homogeneous
Faraday Bianchi identity.  The explicit hypotheses prevent this compatibility result from being
misread as a derivation of gravity from a generic QCD amplitude. -/
@[zil_level physical_theorem]
theorem secondBianchi_cartan_qcd_tqft_faces
    {κ X ι 𝔤 Insertion : Type*} [LieRing 𝔤] [Fintype Insertion]
    (D : κ → κ → κ → κ → κ → ℝ) (hD : SecondBianchi D) (r : ℝˣ)
    (cartanA : GaugePotential X ι 𝔤) (x : X) (μ ν ρ : ι)
    (Q : QCDPrimitiveBCJInput Insertion)
    {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n)
    (hP : LocalCSFlat P.1) (hPbar : LocalCSFlat P.2)
    (q A : Fin 4 → ℝ) (χ : ℝ) :
    SecondBianchi (dilateBianchiTensor r D)
      ∧ ⁅cartanA x ρ, ⁅cartanA x μ, cartanA x ν⁆⁆
          + ⁅cartanA x μ, ⁅cartanA x ν, cartanA x ρ⁆⁆
          + ⁅cartanA x ν, ⁅cartanA x ρ, cartanA x μ⁆⁆ = 0
      ∧ forwardBCJSum Q.weights Q.primitive.amplitude = 0
      ∧ backwardBCJSum Q.weights Q.primitive.amplitude = 0
      ∧ localComplexCSWAction c P = 0
      ∧ faraday q (fun α => A α + χ * q α) = faraday q A
      ∧ ∀ lam μ' ν',
        q lam * faraday q A μ' ν' + q μ' * faraday q A ν' lam
          + q ν' * faraday q A lam μ' = 0 :=
  ⟨(secondBianchi_dilation_iff r D).2 hD,
    frame_jacobi (cartanA x ρ) (cartanA x μ) (cartanA x ν),
    Q.forward_relation,
    qcdPrimitiveBCJ_backward_relation Q,
    localComplexCSWAction_eq_zero_of_flat c P hP hPbar,
    (faraday_gauge_invariant_and_bianchi q A χ).1,
    (faraday_gauge_invariant_and_bianchi q A χ).2⟩

end Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT

zil attach secondBianchi_dilation_iff where
  formalizes @ "claim:the-differential-second-bianchi-identity-is-invariant-under-the-nonzero-real-dilation-group-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily.SecondBianchi",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-dilation-is-a-constant-nonzero-scalar-action-on-the-covariant-curvature-derivative-carrier"

zil attach dilateDifferentialForm_mul where
  formalizes @ "claim:nonzero-real-dilation-multiplication-is-composition-on-continuum-differential-forms",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.dilationGroup"

zil attach greenSchwarzTensorFieldStrength_dilation where
  formalizes @ "claim:the-mayr-stieberger-green-schwarz-three-form-is-equivariant-under-the-nonzero-real-dilation-group",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.greenSchwarzTensorFieldStrength",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-dilation-is-constant-and-scales-b-and-the-chern-simons-three-form-with-the-same-weight"

zil attach greenSchwarz_modifiedBianchi_dilation where
  formalizes @ "claim:the-pontryagin-sourced-green-schwarz-modified-bianchi-identity-is-covariant-under-constant-nonzero-real-dilations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.extDeriv_greenSchwarzTensorFieldStrength",
  caveat @ "claim:a-position-dependent-weyl-rescaling-would-produce-derivative-of-scale-terms-and-is-not-claimed"

zil attach stringScale_dilationGroup where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.dilationGroup_apply",
  formalizes @ "claim:the-mayr-stieberger-planck-to-string-scale-map-intertwines-the-bundled-dilation-group-when-re-s-is-fixed",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:re-s-is-held-fixed-as-a-dimensionless-parameter-and-no-dilaton-vacuum-value-is-predicted"

zil attach secondBianchi_greenSchwarz_dilation where
  formalizes @ "claim:one-nonzero-real-dilation-simultaneously-preserves-the-gravitational-second-bianchi-and-green-schwarz-pontryagin-bianchi-equations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.secondBianchi_dilation_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.greenSchwarz_modifiedBianchi_dilation",
  caveat @ "claim:the-gravitational-and-gauge-tensor-bianchi-identities-are-preserved-together-not-identified-definitionally"

zil attach quadraticPontryagin_dilation where
  supported_by @ "lean:ProbDistribution.normalized",
  formalizes @ "claim:a-weight-one-curvature-two-form-produces-a-weight-two-quadratic-pontryagin-four-form-under-the-nonzero-real-dilation-group",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-generic-interface-also-allows-traced-or-lie-algebra-valued-pairings-the-scalar-continuum-wedge-is-instantiated-separately"

zil attach continuumPontryagin_dilation where
  formalizes @ "claim:the-constructed-continuum-pontryagin-source-f-wedge-f-has-dilation-weight-two-when-curvature-has-weight-one",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.continuumWedgeBilinear",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.continuumWedge_smul_smul",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-scalar-valued-continuous-alternating-form-wedge-a-nonabelian-trace-pairing-remains-an-explicit-additional-map"

zil attach continuumPontryagin_add where
  formalizes @ "claim:the-constructed-continuum-pontryagin-source-polarizes-with-cross-term-two-f-wedge-g",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.continuumWedge_two_comm",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-factor-two-follows-from-even-degree-graded-commutativity-not-from-a-dynamical-field-equation"

zil attach pullbackForm_continuumPontryagin where
  formalizes @ "claim:the-constructed-continuum-pontryagin-source-is-natural-under-differential-form-pullback",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.pullbackForm_continuumWedge",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-pullback-naturality-of-the-scalar-form-source-and-does-not-add-a-nonabelian-trace"

zil attach greenSchwarz_quadraticPontryagin_dilation where
  formalizes @ "claim:the-green-schwarz-bianchi-equation-is-dilation-covariant-with-curvature-weight-one-and-b-tensor-weight-two",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.quadraticPontryagin_dilation",
  caveat @ "claim:the-green-schwarz-coupling-is-held-fixed-and-the-common-bilinear-pairing-is-explicit"

zil attach greenSchwarz_continuumPontryagin_dilation where
  formalizes @ "claim:the-green-schwarz-modified-bianchi-equation-with-the-constructed-continuum-f-wedge-f-source-is-dilation-covariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.continuumPontryagin_dilation",
  caveat @ "claim:the-result-closes-the-abstract-pairing-boundary-for-scalar-valued-curvature-forms"

zil attach secondBianchi_greenSchwarz_quadraticPontryagin_dilation where
  formalizes @ "claim:one-dilation-preserves-the-gravitational-second-bianchi-and-the-weighted-green-schwarz-pontryagin-bianchi-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.secondBianchi_dilation_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.greenSchwarz_quadraticPontryagin_dilation"

zil attach secondBianchi_greenSchwarz_continuumPontryagin_dilation where
  formalizes @ "claim:one-dilation-preserves-the-gravitational-second-bianchi-identity-and-transports-the-constructed-continuum-f-wedge-f-green-schwarz-source",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.secondBianchi_dilation_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT.greenSchwarz_continuumPontryagin_dilation",
  caveat @ "claim:the-two-bianchi-equations-remain-distinct-and-the-wedge-constructor-does-not-supply-a-nonabelian-trace"

zil attach secondBianchi_greenSchwarz_dilation_conservation where
  formalizes @ "claim:the-dilation-covariant-gravity-and-green-schwarz-bianchi-equations-plus-contracted-bianchi-and-einstein-field-equation-force-stress-energy-conservation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation.bianchi_validates_fieldEquation",
  caveat @ "claim:the-metric-contraction-from-the-uncontracted-to-contracted-second-bianchi-remains-the-visible-h-contracted-input"

zil attach secondBianchi_dilation_einsteinCartan where
  formalizes @ "claim:one-compensated-dilation-preserves-both-the-second-bianchi-constraint-and-the-einstein-cartan-hehl-datta-contact-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations.hehlDattaContactDensity_compensated_dilation_invariant",
  caveat @ "claim:the-inverse-square-coupling-weight-and-axial-current-rescaling-are-explicit-input-transformations-not-a-derived-spinor-conformal-law"

zil attach qcd_bcj_secondBianchi_conservation where
  formalizes @ "claim:primitive-qcd-fundamental-bcj-relations-and-the-gravity-second-bianchi-conservation-law-fit-the-existing-dual-bianchi-contract",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.QCDFundamentalBCJRelations.qcdPrimitiveBCJ_backward_relation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation.contracted_bianchi_conservation",
  caveat @ "claim:qcd-bcj-data-does-not-derive-the-gravity-second-bianchi-identity-which-remains-a-visible-hypothesis"

zil attach secondBianchi_cartan_qcd_tqft_faces where
  formalizes @ "claim:gravity-second-bianchi-cartan-gauge-jacobi-qcd-bcj-and-flat-chern-simons-tqft-bianchi-data-form-one-typed-cross-sector-compatibility-result",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBianchiIntegrability.nccBianchi_bracket_jacobi",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.faraday_gauge_invariant_and_bianchi",
  caveat @ "claim:the-tqft-component-is-the-finite-local-trivial-bundle-chern-simons-carrier-not-a-global-nonabelian-chern-weil-construction",
  caveat @ "claim:the-distinct-gravity-gauge-amplitude-and-topological-bianchi-faces-are-compatible-not-definitionally-identical"

zil_file_contract physlib.secondBianchiDilationCartanQCDTQFT where
  promises "The nonzero-real dilation group acts on covariant-curvature derivative tensors and continuum differential forms with identity composition and inverse. It preserves the differential second Bianchi identity, intertwines the Mayr-Stieberger Planck/string scale relation, and carries the Green-Schwarz Pontryagin-sourced modified Bianchi equation covariantly. The normalized continuum wedge on continuous alternating forms constructs the scalar Pontryagin source F wedge F, proves even-degree commutativity, pullback naturality, polarization, and dilation weight two; the generic bundled pairing remains available for traced or Lie-algebra-valued extensions. With B and the Chern-Simons three-form at weight two the Green-Schwarz coupling stays fixed. The contracted second Bianchi plus the Einstein field equation then forces stress-energy conservation. The same compensated dilation preserves the existing Einstein-Cartan Hehl-Datta contact density. Primitive-QCD fundamental BCJ relations share the checked dual-Bianchi surface with gravity-side contracted conservation, while the conformal-Cartan Jacobi core and finite local Chern-Simons flat/gauge-Bianchi sector are assembled in a single explicitly conditional cross-sector theorem."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily.SecondBianchi",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.dilationGroup",
    "lean:Physlib.Mathematics.LovelockRund.continuumWedgeBilinear",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.greenSchwarzTensorFieldStrength",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.QCDFundamentalBCJRelations.QCDPrimitiveBCJInput",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.LocalCSFlat"
  ]
  forbids_substitutes [
    "claiming that a generic qcd amplitude proves the gravitational second bianchi identity",
    "identifying the gravity differential bianchi identity with the gauge bianchi identity definitionally",
    "promoting a finite local chern-simons carrier to a global nonabelian tqft theorem",
    "using a position-dependent Weyl dilation or inferring a spinor conformal weight"
  ]
  witnessed_by [
    secondBianchi_dilation_iff,
    dilateDifferentialForm_mul,
    greenSchwarzTensorFieldStrength_dilation,
    greenSchwarz_modifiedBianchi_dilation,
    stringScale_dilationGroup,
    secondBianchi_greenSchwarz_dilation,
    quadraticPontryagin_dilation,
    continuumPontryagin_dilation,
    continuumPontryagin_add,
    pullbackForm_continuumPontryagin,
    greenSchwarz_quadraticPontryagin_dilation,
    greenSchwarz_continuumPontryagin_dilation,
    secondBianchi_greenSchwarz_quadraticPontryagin_dilation,
    secondBianchi_greenSchwarz_continuumPontryagin_dilation,
    secondBianchi_greenSchwarz_dilation_conservation,
    secondBianchi_dilation_einsteinCartan,
    qcd_bcj_secondBianchi_conservation,
    secondBianchi_cartan_qcd_tqft_faces
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.secondBianchiDilationCartanQCDTQFT
