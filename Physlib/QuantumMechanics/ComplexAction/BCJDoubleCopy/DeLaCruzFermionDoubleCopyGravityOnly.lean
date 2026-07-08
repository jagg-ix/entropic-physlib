/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic

/-!
# Fermion double copies as gravity-only matter

This file formalizes the algebraic core of de la Cruz, Kniss, and Weinzierl,
*Double Copies of Fermions as Matter that Interacts Only Gravitationally* (PRL 116, 201601, 2016).

The paper extends the usual BCJ/KLT double copy from pure Yang-Mills gluons to QCD-like primitive
amplitudes with flavored fermion pairs. The gravity-side external states include double copies of fermions;
these matter states are computed from gauge-theory amplitudes but have only gravitational interactions in the
double-copied theory.

This module recognizes and reuses the initial double-copy work already present in the repo:

* `BCJDoubleCopy.ColorKinematicsDoubleCopy`: BCJ triples, gauge amplitudes, and `gravity = gauge^2` amplitudes;
* `BCJDoubleCopy.SecondBianchiConservation`: the Bianchi/conservation side of the gravity double copy;
* `ComplexEinstein.SuperoperatorComplexEinsteinBCJSector`: entropic Einstein-source factorization as a BCJ double copy;
* `BoseFermiOperatorAlgebra.Basic`: a concrete finite fermion-field structure that can supply the
  external fermion mode used by the new amplitude layer.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DeLaCruzFermionDoubleCopyGravityOnly

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic

/-! ## §A — flavored-amplitude bookkeeping and the generalized KLT kernel -/

/-- Number of independent primitive QCD amplitudes in the de la Cruz-Kniss-Weinzierl basis.

For no flavored pair or one flavored pair this is `(n - 3)!`. For `nq >= 2`, written here as `k + 2`, it is
`2^(nq - 1) * nq! * (n - 3)!`, the Dyck-word/flavor-count factor from the paper. -/
def flavoredBasisCount (n : Nat) : Nat → Nat
  | 0 => Nat.factorial (n - 3)
  | 1 => Nat.factorial (n - 3)
  | k + 2 => 2 ^ (k + 1) * Nat.factorial (n - 3) * Nat.factorial (k + 2)

@[simp] theorem flavoredBasisCount_noFlavor (n : Nat) :
    flavoredBasisCount n 0 = Nat.factorial (n - 3) := rfl

@[simp] theorem flavoredBasisCount_onePair (n : Nat) :
    flavoredBasisCount n 1 = Nat.factorial (n - 3) := rfl

@[simp] theorem flavoredBasisCount_multiPair (n k : Nat) :
    flavoredBasisCount n (k + 2)
      = 2 ^ (k + 1) * Nat.factorial (n - 3) * Nat.factorial (k + 2) := rfl

/-- A generalized KLT kernel for a flavored basis `B`: the double-ordered scalar-amplitude matrix `m` and
the momentum kernel `S = m^{-1}`. -/
structure GeneralizedFlavorKLTKernel (B : Type*) [Fintype B] [DecidableEq B] where
  /-- Double-ordered scalar amplitude matrix `m(w, wtilde)`. -/
  scalarAmplitude : Matrix B B ℂ
  /-- Momentum kernel `S = m^{-1}`. -/
  momentumKernel : Matrix B B ℂ
  /-- Right inverse property `m S = 1`. -/
  scalar_mul_kernel : scalarAmplitude * momentumKernel = 1
  /-- Left inverse property `S m = 1`. -/
  kernel_mul_scalar : momentumKernel * scalarAmplitude = 1

/-- Generalized KLT gravity amplitude: `M = -i sum_w,wtilde A(w) S(w,wtilde) Atilde(wtilde)`. -/
def generalizedKLTGravityAmplitude {B : Type*} [Fintype B]
    (A Atilde : B → ℂ) (S : Matrix B B ℂ) : ℂ :=
  -Complex.I * ∑ w, ∑ wtilde, A w * S w wtilde * Atilde wtilde

/-- The generalized KLT amplitude is the gauge-kernel-gauge bilinear used in the paper. -/
theorem generalizedKLTGravityAmplitude_eq {B : Type*} [Fintype B]
    (A Atilde : B → ℂ) (S : Matrix B B ℂ) :
    generalizedKLTGravityAmplitude A Atilde S
      = -Complex.I * ∑ w, ∑ wtilde, A w * S w wtilde * Atilde wtilde := rfl

/-! ## §B — reuse of the existing BCJ double-copy infrastructure -/

/-- The de la Cruz color-kinematics method is exactly the repo's existing BCJ double-copy amplitude. -/
abbrev deLaCruzBCJGravityAmplitude : List BCJTriple → List BCJTriple → ℝ :=
  bcjDoubleCopyAmplitude

theorem deLaCruzBCJGravityAmplitude_eq_existing (ts1 ts2 : List BCJTriple) :
    deLaCruzBCJGravityAmplitude ts1 ts2 = bcjDoubleCopyAmplitude ts1 ts2 := rfl

/-- A representative for the paper's claim that the color-kinematics and generalized-KLT methods compute the same
gravity amplitude. The paper verifies this equality for the relevant tree amplitudes; downstream files can
instantiate the structure when they have a concrete proof. -/
structure ColorKinematicsKLTAgreement where
  /-- Gravity amplitude computed by color-kinematics double copy. -/
  colorKinematicsAmplitude : ℂ
  /-- Gravity amplitude computed by generalized KLT. -/
  generalizedKLTAmplitude : ℂ
  /-- Agreement of the two methods. -/
  agreement : colorKinematicsAmplitude = generalizedKLTAmplitude

/-- The Maxwell/Faraday Bianchi identity already supplies the BCJ kinematic Jacobi in the existing repo. -/
theorem deLaCruz_kinematic_jacobi_reuses_existing_first_bianchi
    (k A : Fin 4 → ℝ) (lam mu nu : Fin 4) (c_s c_t c_u : ℝ)
    (hc : c_s + c_t + c_u = 0) :
    (faradayBCJDuality k A lam mu nu c_s c_t c_u hc).n_s
      + (faradayBCJDuality k A lam mu nu c_s c_t c_u hc).n_t
      + (faradayBCJDuality k A lam mu nu c_s c_t c_u hc).n_u = 0 :=
  bcj_kinematic_jacobi_is_first_bianchi k A lam mu nu c_s c_t c_u hc

/-- The double-copy path-integral/Feynman-Kac factorization is already present in the BCJ sector. -/
theorem deLaCruz_doubleCopy_weight_factorizes (S1 S2 : ℝ) :
    Real.exp (-(S1 + S2)) = Real.exp (-S1) * Real.exp (-S2) :=
  bcj_doublecopy_fk_factorization S1 S2

/-- The gravity-side Bianchi/conservation implication already present in the repo supplies the conservation
law for the gravity-only matter sector. -/
theorem deLaCruz_gravityOnly_conservation_link (kappa : ℝ) (hkappa : kappa ≠ 0)
    (divG divT : Fin 4 → ℝ) (hEin : divG = kappa • divT) (hBianchi : divG = 0) :
    divT = 0 :=
  contracted_bianchi_conservation kappa hkappa divG divT hEin hBianchi

/-! ## §C — double copies of fermion polarizations -/

/-- A double-copy fermion polarization is a pair of fermion spinor polarizations, one from each gauge copy. -/
structure FermionDoubleCopyPolarization (SpinorLeft SpinorRight : Type*) where
  /-- Spinor from the first gauge-theory copy. -/
  left : SpinorLeft
  /-- Spinor from the second gauge-theory copy. -/
  right : SpinorRight

/-- Equal-spin and opposite-spin choices give four spin labels. -/
abbrev FermionDoubleCopySpinState := Bool × Bool

/-- The four spin states of a fermion double copy: `++`, `--`, `+-`, and `-+`. -/
theorem fermionDoubleCopy_spinState_card : Fintype.card FermionDoubleCopySpinState = 4 := by
  native_decide

/-- The recent Kálnay Bose-bilinear formalization can supply a finite CAR fermion field for the external
fermion line used in the de la Cruz amplitude layer. -/
theorem deLaCruz_external_fermion_can_be_kalnay_field (p : Momentum 3) :
    KalnayBoseFermiFieldStatement p :=
  kalnay_bose_fermi_field_statement p

/-! ## §D — the two four-point amplitudes and pole cancellation -/

/-- Four-point double-copy amplitude with one fermion-antifermion pair and two gluon double copies.

The variables `s12`, `s23`, and `s13` stand for the Lorentz invariants `2 p1.p2`, `2 p2.p3`, and `2 p1.p3`;
`A` and `Atilde` are the two primitive QCD amplitudes. -/
def M4_oneFermionPair (s12 s23 s13 A Atilde : ℂ) : ℂ :=
  -Complex.I * (s12 * s23 / s13) * A * Atilde

theorem M4_oneFermionPair_eq (s12 s23 s13 A Atilde : ℂ) :
    M4_oneFermionPair s12 s23 s13 A Atilde
      = -Complex.I * (s12 * s23 / s13) * A * Atilde := rfl

/-- Four-point double-copy amplitude with two nonidentical fermion-antifermion pairs. Here `s23` stands for
`2 p2.p3`, and `massTerm` stands for `2 m'^2`. -/
def M4_twoFermionPairs (s23 massTerm A Atilde : ℂ) : ℂ :=
  Complex.I * (s23 + massTerm) * A * Atilde

theorem M4_twoFermionPairs_eq (s23 massTerm A Atilde : ℂ) :
    M4_twoFermionPairs s23 massTerm A Atilde = Complex.I * (s23 + massTerm) * A * Atilde := rfl

/-- The one-pair KLT prefactor cancels one copy of each squared gauge pole, leaving only simple poles. -/
theorem oneFermionPair_kernel_cancels_double_poles
    (s12 s23 s13 R Rtilde : ℂ) :
    (s12 * s23 / s13) * (R / (s12 * s23)) * (Rtilde / (s12 * s23))
      = R * Rtilde / (s13 * s12 * s23) := by
  by_cases h12 : s12 = 0
  · subst s12
    simp
  by_cases h23 : s23 = 0
  · subst s23
    simp
  by_cases h13 : s13 = 0
  · subst s13
    simp
  field_simp [h12, h23, h13]

/-- The two-pair KLT kernel `P = s23 + 2m'^2` cancels one copy of the squared gauge pole. -/
theorem twoFermionPair_kernel_cancels_double_pole (P R Rtilde : ℂ) :
    P * (R / P) * (Rtilde / P) = R * Rtilde / P := by
  by_cases hP : P = 0
  · subst P
    simp
  field_simp [hP]

/-! ## §E — gravity-only matter and the nonrelativistic cross-section factor -/

/-- Gravity-only matter on the double-copy side: gauge amplitudes may be used computationally, but the
physical matter state has no gauge interaction and only the gravity-side amplitude is retained. -/
structure GravityOnlyDoubleCopyMatter where
  /-- First computational primitive gauge amplitude. -/
  computationalGaugeLeft : ℂ
  /-- Second computational primitive gauge amplitude. -/
  computationalGaugeRight : ℂ
  /-- Physical gauge amplitude of the double-copied matter state. -/
  physicalGaugeAmplitude : ℂ
  /-- Physical gravitational amplitude of the double-copied matter state. -/
  gravitationalAmplitude : ℂ
  /-- The double-copied matter state has no physical gauge interaction. -/
  no_physical_gauge_interaction : physicalGaugeAmplitude = 0

/-- Build a gravity-only matter amplitude from the double-copy gravity amplitude. -/
def gravityOnlyMatterFromAmplitude (A Atilde M : ℂ) : GravityOnlyDoubleCopyMatter where
  computationalGaugeLeft := A
  computationalGaugeRight := Atilde
  physicalGaugeAmplitude := 0
  gravitationalAmplitude := M
  no_physical_gauge_interaction := rfl

theorem gravityOnlyMatterFromAmplitude_noGauge (A Atilde M : ℂ) :
    (gravityOnlyMatterFromAmplitude A Atilde M).physicalGaugeAmplitude = 0 := rfl

/-- De la Cruz-Kniss-Weinzierl nonrelativistic differential cross section when all four double-copy spin
states are summed. -/
def deLaCruzNonrelCrossSection (GN m mPrime E z : ℝ) : ℝ :=
  (2 * Real.pi * GN ^ 2 * m ^ 2 * mPrime ^ 2) / (E ^ 2 * (z + 1) ^ 2)

/-- Classical gravitational Rutherford cross section for comparison. -/
def gravitationalRutherfordCrossSection (GN m mPrime E z : ℝ) : ℝ :=
  (2 * Real.pi * GN ^ 2 * m ^ 2 * mPrime ^ 2) / (4 * E ^ 2 * (z + 1) ^ 2)

/-- With all four spin states included, the paper's nonrelativistic cross section is four times the
Rutherford value, away from the zero-flux and forward-singular denominators. -/
theorem deLaCruz_nonrel_crossSection_eq_four_rutherford (GN m mPrime E z : ℝ)
    (hE : E ≠ 0) (hz : z + 1 ≠ 0) :
    deLaCruzNonrelCrossSection GN m mPrime E z
      = 4 * gravitationalRutherfordCrossSection GN m mPrime E z := by
  unfold deLaCruzNonrelCrossSection gravitationalRutherfordCrossSection
  field_simp [hE, hz]

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DeLaCruzFermionDoubleCopyGravityOnly

end
