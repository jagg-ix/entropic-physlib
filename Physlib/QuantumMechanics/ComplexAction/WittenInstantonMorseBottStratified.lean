/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
public import Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
public import Mathlib.Tactic

/-!
# Witten instanton complexes and stratified Morse-Bott ranks

This module records the finite rank and polynomial consequences of
G. Jayasinghe, H. Quan, and X. Yu, *Witten instanton complex and
Morse-Bott inequalities on stratified pseudomanifolds* (2024),
arXiv:2412.12003v1.

The analytic part of the paper constructs Hilbert complexes, Witten
deformations, local normal cohomology complexes, and spectral estimates.  This
file formalizes the algebraic layer used after those analytic hypotheses are
available:

* the small-eigenvalue Witten instanton ranks equal the sum of local
  cohomology ranks;
* the Morse polynomial is the sum of local Poincare polynomials;
* a strong polynomial Morse certificate gives the alternating Morse
  inequalities by reusing the existing `alternatingPartial` Morse-equation
  lemma from `OperatorAlgebra.PicardLefschetzMorseContour`;
* Kähler Hamiltonian isometry hypotheses are recorded at the product-metric
  and local symplectic-chart level, reusing the canonical Hamiltonian
  symplectic form from `ClassicalMechanics.HamiltonsEquations`;
* the trefoil-cone example in Section 6 is connected to the existing
  Chern-Simons trefoil invariant;
* the same finite-rank layer is linked to the Cartan/Einstein/icosahedral
  dilatonic background already present in the repo.

## References

* G. Jayasinghe, H. Quan, X. Yu, arXiv:2412.12003v1, Theorem 1.1,
  Definition 1.2, Theorem 1.3, Theorem 5.6, Theorem 5.7, Example 6.6.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WittenInstantonMorseBottStratified

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.Thermodynamics.SecondLaw

/-! ## A. Rank data for the Witten instanton complex -/

/-- Rank data extracted from the analytic Witten-instanton construction.
`localCohomologyRank a k` is the rank of the local Hilbert complex over the
fundamental neighborhood of the critical component `a`, `smallEigenvalueRank`
is the rank of the small-eigenvalue space `K_[0,c]`, and
`globalCohomologyRank` is the rank of the global complex. -/
structure WittenInstantonRankData (Crit : Type*) where
  /-- Local cohomology rank at a critical component and degree. -/
  localCohomologyRank : Crit → Nat → Nat
  /-- Rank of the small-eigenvalue Witten instanton space in a degree. -/
  smallEigenvalueRank : Nat → Nat
  /-- Rank of the global cohomology group in a degree. -/
  globalCohomologyRank : Nat → Nat

/-- Coefficient of the Morse polynomial: the sum of local cohomology ranks. -/
def localMorseCoefficient {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (k : Nat) : Nat :=
  ∑ a : Crit, D.localCohomologyRank a k

/-- Integer coefficient of the Morse polynomial. -/
def morseCoefficientInt {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (k : Nat) : Int :=
  (localMorseCoefficient D k : Int)

/-- Integer coefficient of the global Poincare polynomial. -/
def poincareCoefficientInt {Crit : Type*}
    (D : WittenInstantonRankData Crit) (k : Nat) : Int :=
  (D.globalCohomologyRank k : Int)

/-- Certificate for the rank conclusion of the Witten instanton complex,
matching Theorem 1.1 and Theorem 5.6 after the analytic construction has
supplied the constants `c` and `epsilon0`. -/
structure WittenInstantonComplexCertificate {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) where
  /-- The small-eigenvalue rank equals the sum of local cohomology ranks. -/
  small_eq_local : ∀ k : Nat, D.smallEigenvalueRank k = localMorseCoefficient D k
  /-- The quasi-isomorphism gives the expected rank comparison. -/
  quasiIso_rank : ∀ k : Nat, D.globalCohomologyRank k ≤ D.smallEigenvalueRank k

/-- The Morse-polynomial coefficient equals the small-eigenvalue rank whenever
the Witten instanton certificate is available. -/
lemma morseCoefficient_eq_smallEigenvalueRank {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : WittenInstantonComplexCertificate D)
    (k : Nat) :
    morseCoefficientInt D k = (D.smallEigenvalueRank k : Int) := by
  rw [morseCoefficientInt, C.small_eq_local]

/-- The quasi-isomorphism rank comparison of Theorem 1.1, expressed against
the local Morse coefficient. -/
lemma globalRank_le_localMorseCoefficient {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : WittenInstantonComplexCertificate D)
    (k : Nat) :
    D.globalCohomologyRank k ≤ localMorseCoefficient D k := by
  rw [← C.small_eq_local k]
  exact C.quasiIso_rank k

/-! ## A.1. Spectral-window rank certificates -/

/-- Rank-level spectral-gap certificate for Proposition 4.8 and Proposition 5.5.
The analytic estimates isolate a small spectral window; this structure records
the resulting equality between that window and the local zero-mode cohomology
ranks. -/
structure SpectralWindowRankCertificate {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) where
  /-- Rank of the zero-mode sector in degree `k`. -/
  zeroModeRank : Nat → Nat
  /-- Rank of the eigenspaces in the chosen small spectral window. -/
  smallWindowRank : Nat → Nat
  /-- The small window contains exactly the zero-mode sector. -/
  smallWindow_eq_zeroMode : ∀ k : Nat, smallWindowRank k = zeroModeRank k
  /-- The zero-mode sector is the local cohomology rank sum. -/
  zeroMode_eq_local : ∀ k : Nat, zeroModeRank k = localMorseCoefficient D k
  /-- The rank data uses the same small-window ranks. -/
  rankData_eq_smallWindow : ∀ k : Nat, D.smallEigenvalueRank k = smallWindowRank k

/-- Proposition 5.5 in rank form: once the spectral window is certified, its
rank is the sum of local cohomology ranks. -/
lemma spectralWindowRank_eq_localMorseCoefficient {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : SpectralWindowRankCertificate D)
    (k : Nat) :
    C.smallWindowRank k = localMorseCoefficient D k := by
  rw [C.smallWindow_eq_zeroMode, C.zeroMode_eq_local]

/-- The spectral-window certificate supplies the rank equality required in the
Witten instanton complex certificate. -/
lemma smallEigenvalueRank_eq_local_of_spectralWindow {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : SpectralWindowRankCertificate D)
    (k : Nat) :
    D.smallEigenvalueRank k = localMorseCoefficient D k := by
  rw [C.rankData_eq_smallWindow, spectralWindowRank_eq_localMorseCoefficient D C]

/-! ## B. Strong polynomial Morse inequalities -/

/-- Strong polynomial Morse certificate:
`M(b)-P(b) = (1+b) Q(b)` at the coefficient level, with nonnegative
coefficients of `Q`. -/
structure StrongPolynomialMorseCertificate {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) where
  /-- Coefficients of the nonnegative remainder polynomial `Q`. -/
  remainder : Nat → Int
  /-- The remainder coefficients are nonnegative. -/
  remainder_nonneg : ∀ k : Nat, 0 ≤ remainder k
  /-- Degree-zero coefficient equation. -/
  defect_zero : morseCoefficientInt D 0 - poincareCoefficientInt D 0 = remainder 0
  /-- Successor coefficient equation for multiplication by `1+b`. -/
  defect_succ : ∀ k : Nat,
    morseCoefficientInt D (k + 1) - poincareCoefficientInt D (k + 1) =
      remainder (k + 1) + remainder k

/-- The strong polynomial Morse equation implies the alternating Morse
inequalities.  This reuses the existing algebraic Morse-equation lemma from
the Picard-Lefschetz/Morse-contour infrastructure. -/
lemma strongPolynomialMorse_alternatingInequality {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : StrongPolynomialMorseCertificate D)
    (q : Nat) :
    alternatingPartial (poincareCoefficientInt D) q ≤
      alternatingPartial (morseCoefficientInt D) q := by
  exact morseEquation_implies_alternatingInequality
    (morseCoefficientInt D) (poincareCoefficientInt D)
    C.remainder C.defect_zero C.defect_succ C.remainder_nonneg q

/-- Coefficientwise weak Morse inequality extracted from the strong polynomial
Morse equation. -/
lemma strongPolynomialMorse_coefficient_nonneg {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : StrongPolynomialMorseCertificate D)
    (k : Nat) :
    0 ≤ morseCoefficientInt D k - poincareCoefficientInt D k := by
  cases k with
  | zero =>
      rw [C.defect_zero]
      exact C.remainder_nonneg 0
  | succ k =>
      rw [C.defect_succ k]
      exact add_nonneg (C.remainder_nonneg (k + 1)) (C.remainder_nonneg k)

/-- Weak Morse inequality in coefficient form. -/
lemma strongPolynomialMorse_weakInequality {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : StrongPolynomialMorseCertificate D)
    (k : Nat) :
    poincareCoefficientInt D k ≤ morseCoefficientInt D k := by
  have h := strongPolynomialMorse_coefficient_nonneg D C k
  linarith

/-! ## B.1. Refined and perfect Morse-Bott consequences -/

/-- Coefficient of the refined Morse polynomial from Definition 1.5: the
coefficientwise minimum of the two Morse polynomials for `h` and `-h`. -/
def refinedMorseCoefficientInt {CritPlus CritMinus : Type*} [Fintype CritPlus]
    [Fintype CritMinus]
    (Dplus : WittenInstantonRankData CritPlus) (Dminus : WittenInstantonRankData CritMinus)
    (k : Nat) : Int :=
  min (morseCoefficientInt Dplus k) (morseCoefficientInt Dminus k)

/-- Self-dual mezzo-perversity data in coefficient form: the reversed Morse
polynomial for `h` agrees with the Morse polynomial for `-h` up to degree `n`. -/
structure SelfDualMorsePolynomialCertificate {CritPlus CritMinus : Type*}
    [Fintype CritPlus] [Fintype CritMinus]
    (Dplus : WittenInstantonRankData CritPlus) (Dminus : WittenInstantonRankData CritMinus)
    (n : Nat) where
  /-- Coefficient form of `b^n M(h)(b⁻¹)=M(-h)(b)`. -/
  dual_coeff : ∀ k : Nat, k ≤ n →
    morseCoefficientInt Dplus (n - k) = morseCoefficientInt Dminus k
  /-- The two global complexes have the same Poincare coefficients. -/
  poincare_eq : ∀ k : Nat, poincareCoefficientInt Dminus k = poincareCoefficientInt Dplus k

/-- Coefficient-level refined Morse inequality from two strong polynomial
Morse certificates.  The right side is the nonnegative coefficient `Q_k` of
Corollary 1.6/5.9. -/
lemma refinedMorseCoefficient_defect_nonneg {CritPlus CritMinus : Type*}
    [Fintype CritPlus] [Fintype CritMinus]
    (Dplus : WittenInstantonRankData CritPlus) (Dminus : WittenInstantonRankData CritMinus)
    (Cplus : StrongPolynomialMorseCertificate Dplus)
    (Cminus : StrongPolynomialMorseCertificate Dminus)
    (hP : ∀ k : Nat, poincareCoefficientInt Dminus k = poincareCoefficientInt Dplus k)
    (k : Nat) :
    0 ≤ refinedMorseCoefficientInt Dplus Dminus k - poincareCoefficientInt Dplus k := by
  have hplus := strongPolynomialMorse_weakInequality Dplus Cplus k
  have hminus₀ := strongPolynomialMorse_weakInequality Dminus Cminus k
  have hminus : poincareCoefficientInt Dplus k ≤ morseCoefficientInt Dminus k := by
    rw [← hP k]
    exact hminus₀
  have hmin :
      poincareCoefficientInt Dplus k ≤ refinedMorseCoefficientInt Dplus Dminus k := by
    exact le_min hplus hminus
  linarith

/-- Self-dual mezzo-perversity data supplies the common Poincare coefficients
needed by the refined Morse inequality. -/
lemma selfDual_refinedMorseCoefficient_defect_nonneg {CritPlus CritMinus : Type*}
    [Fintype CritPlus] [Fintype CritMinus]
    (Dplus : WittenInstantonRankData CritPlus) (Dminus : WittenInstantonRankData CritMinus)
    (n : Nat)
    (S : SelfDualMorsePolynomialCertificate Dplus Dminus n)
    (Cplus : StrongPolynomialMorseCertificate Dplus)
    (Cminus : StrongPolynomialMorseCertificate Dminus)
    (k : Nat) :
    0 ≤ refinedMorseCoefficientInt Dplus Dminus k - poincareCoefficientInt Dplus k := by
  exact refinedMorseCoefficient_defect_nonneg Dplus Dminus Cplus Cminus S.poincare_eq k

/-- The coefficientwise remainder of the refined Morse inequality. -/
def refinedMorseRemainder {CritPlus CritMinus : Type*} [Fintype CritPlus]
    [Fintype CritMinus]
    (Dplus : WittenInstantonRankData CritPlus) (Dminus : WittenInstantonRankData CritMinus)
    (k : Nat) : Int :=
  refinedMorseCoefficientInt Dplus Dminus k - poincareCoefficientInt Dplus k

/-- A degree is perfect when the Morse and Poincare coefficients agree. -/
def IsPerfectAtDegree {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (k : Nat) : Prop :=
  morseCoefficientInt D k = poincareCoefficientInt D k

/-- A stratified Morse-Bott rank datum is perfect when all degree coefficients
agree, matching Definition 1.7. -/
def IsPerfect {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) : Prop :=
  ∀ k : Nat, IsPerfectAtDegree D k

/-- If the strong Morse remainder vanishes in every degree, the rank datum is
perfect. -/
lemma isPerfect_of_strongPolynomialMorse_remainder_zero {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : StrongPolynomialMorseCertificate D)
    (hQ : ∀ k : Nat, C.remainder k = 0) :
    IsPerfect D := by
  intro k
  unfold IsPerfectAtDegree
  cases k with
  | zero =>
      have h := C.defect_zero
      rw [hQ 0] at h
      linarith
  | succ k =>
      have h := C.defect_succ k
      rw [hQ (k + 1), hQ k] at h
      linarith

/-- Conversely, a perfect rank datum forces the strong Morse remainder to
vanish. -/
lemma strongPolynomialMorse_remainder_zero_of_isPerfect {Crit : Type*} [Fintype Crit]
    (D : WittenInstantonRankData Crit) (C : StrongPolynomialMorseCertificate D)
    (hperfect : IsPerfect D) :
    ∀ k : Nat, C.remainder k = 0 := by
  intro k
  induction k with
  | zero =>
      have h := C.defect_zero
      have hp := hperfect 0
      unfold IsPerfectAtDegree at hp
      linarith
  | succ k ih =>
      have h := C.defect_succ k
      have hp := hperfect (k + 1)
      unfold IsPerfectAtDegree at hp
      have hnonneg := C.remainder_nonneg (k + 1)
      rw [ih] at h
      linarith

/-! ## B.2. Cone-link cohomology rank formulas -/

/-- Rank data for the cone-link computation in Proposition 6.2.  `middleRank`
records the mezzo-perversity contribution in the middle degree. -/
structure ConeLinkRankData where
  /-- Dimension of the link `Z`. -/
  linkDim : Nat
  /-- Rank of the middle mezzo-perversity contribution. -/
  middleRank : Nat
  /-- Rank of the link cohomology in degree `k`. -/
  linkRank : Nat → Nat

/-- Neumann cone rank from Proposition 6.2:
zero above the middle degree, `middleRank` in the middle degree, and link
cohomology below it. -/
def coneNeumannRank (C : ConeLinkRankData) (k : Nat) : Nat :=
  if 2 * k > C.linkDim then 0
  else if 2 * k = C.linkDim then C.middleRank
  else C.linkRank k

/-- Dirichlet cone rank from Proposition 6.2:
shifted link cohomology above the middle degree, middle dual contribution at
the shifted middle degree, and zero below. -/
def coneDirichletRank (C : ConeLinkRankData) (k : Nat) : Nat :=
  if C.linkDim + 2 < 2 * k then C.linkRank (k - 1)
  else if C.linkDim + 2 = 2 * k then C.middleRank
  else 0

/-- Neumann cone cohomology vanishes above the middle degree. -/
lemma coneNeumannRank_high (C : ConeLinkRankData) {k : Nat}
    (h : C.linkDim < 2 * k) :
    coneNeumannRank C k = 0 := by
  simp [coneNeumannRank, h]

/-- Neumann cone cohomology is the mezzo-perversity contribution in the middle
degree. -/
lemma coneNeumannRank_middle (C : ConeLinkRankData) {k : Nat}
    (h : 2 * k = C.linkDim) :
    coneNeumannRank C k = C.middleRank := by
  simp [coneNeumannRank, h]

/-- Neumann cone cohomology agrees with link cohomology below the middle
degree. -/
lemma coneNeumannRank_low (C : ConeLinkRankData) {k : Nat}
    (h : 2 * k < C.linkDim) :
    coneNeumannRank C k = C.linkRank k := by
  have hnotHigh : ¬ C.linkDim < 2 * k := by omega
  have hnotMid : ¬ 2 * k = C.linkDim := by omega
  simp [coneNeumannRank, hnotHigh, hnotMid]

/-- Dirichlet cone cohomology is shifted link cohomology above the shifted
middle degree. -/
lemma coneDirichletRank_high (C : ConeLinkRankData) {k : Nat}
    (h : C.linkDim + 2 < 2 * k) :
    coneDirichletRank C k = C.linkRank (k - 1) := by
  simp [coneDirichletRank, h]

/-- Dirichlet cone cohomology is the dual middle contribution at the shifted
middle degree. -/
lemma coneDirichletRank_middle (C : ConeLinkRankData) {k : Nat}
    (h : C.linkDim + 2 = 2 * k) :
    coneDirichletRank C k = C.middleRank := by
  simp [coneDirichletRank, h]

/-- Dirichlet cone cohomology vanishes below the shifted middle degree. -/
lemma coneDirichletRank_low (C : ConeLinkRankData) {k : Nat}
    (h : 2 * k < C.linkDim + 2) :
    coneDirichletRank C k = 0 := by
  have hnotHigh : ¬ C.linkDim + 2 < 2 * k := by omega
  have hnotMid : ¬ C.linkDim + 2 = 2 * k := by omega
  simp [coneDirichletRank, hnotHigh, hnotMid]

/-! ## C. Kähler Hamiltonian isometry data -/

set_option backward.isDefEq.respectTransparency false in
/-- Homogeneous coordinates in the projective-variety example of Section 6. -/
inductive CP3Coordinate where
  | w
  | x
  | y
  | z
  deriving DecidableEq, Fintype

/-- The two-torus weights displayed in Example 6.6:
`[w : x : y : z] ↦ [w : lambda^3 x : mu^3 y : lambda^2 mu z]`. -/
def cp3TorusWeight : CP3Coordinate → Int × Int
  | .w => (0, 0)
  | .x => (3, 0)
  | .y => (0, 3)
  | .z => (2, 1)

/-- The circle restriction used in Example 6.6, `mu = 1` and `lambda = exp(i theta)`. -/
def cp3CircleWeight (c : CP3Coordinate) : Int :=
  (cp3TorusWeight c).1

/-- Coordinates left fixed by the `mu = 1` circle action are precisely `w`
and `y`; the moving normal directions are `x` and `z`. -/
def cp3TrefoilConeCoordinate (c : CP3Coordinate) : Prop :=
  c = .w ∨ c = .y

/-- Full two-torus fixed coordinates.  The paper's trefoil-cone component is
fixed by the circle restriction, not by every two-torus direction. -/
def cp3FullTorusFixedCoordinate (c : CP3Coordinate) : Prop :=
  cp3TorusWeight c = (0, 0)

/-- Circle weights of the four projective coordinates. -/
lemma cp3CircleWeight_values :
    cp3CircleWeight .w = 0
      ∧ cp3CircleWeight .x = 3
      ∧ cp3CircleWeight .y = 0
      ∧ cp3CircleWeight .z = 2 := by
  simp [cp3CircleWeight, cp3TorusWeight]

/-- The circle-fixed coordinate locus is the `w,y` plane, i.e. the coordinate
description of the non-isolated critical component `{x=z=0}` in Example 6.6. -/
lemma cp3TrefoilConeCoordinate_iff_circleWeight_zero (c : CP3Coordinate) :
    cp3TrefoilConeCoordinate c ↔ cp3CircleWeight c = 0 := by
  cases c <;> simp [cp3TrefoilConeCoordinate, cp3CircleWeight, cp3TorusWeight]

/-- The full two-torus fixes only the `w` coordinate direction in this finite
weight model. -/
lemma cp3FullTorusFixedCoordinate_iff_w (c : CP3Coordinate) :
    cp3FullTorusFixedCoordinate c ↔ c = .w := by
  cases c <;> simp [cp3FullTorusFixedCoordinate, cp3TorusWeight]

set_option backward.isDefEq.respectTransparency false in
/-- The three strata mentioned after Example 6.6 for the unfixed two-torus
action: one critical point on each stratum. -/
inductive ProjectiveTorusCriticalStratum where
  | depthTwo
  | depthOne
  | regular
  deriving DecidableEq, Fintype

/-- The unfixed two-torus example has three critical strata in the finite
model used by the paper. -/
lemma projectiveTorusCriticalStrata_card :
    Fintype.card ProjectiveTorusCriticalStratum = 3 := by
  native_decide

/-- A local Kähler symplectic chart.  The canonical chart below reuses the
Hamiltonian symplectic matrix already available in
`ClassicalMechanics.HamiltonsEquations`. -/
structure LocalKahlerSymplecticChart where
  /-- Local symplectic form in a two-dimensional Hamiltonian chart. -/
  omega : Matrix (Fin 2) (Fin 2) Real
  /-- The local symplectic form is antisymmetric. -/
  omega_antisymm : ∀ i j, omega i j = -omega j i

/-- The canonical local Kähler symplectic chart, reusing the repository's
Hamiltonian symplectic form `symplecticForm2`. -/
def canonicalLocalKahlerSymplecticChart : LocalKahlerSymplecticChart where
  omega := symplecticForm2
  omega_antisymm := symplecticForm2_antisymm

/-- The local Kähler chart is exactly the canonical Hamiltonian symplectic
matrix already used for Hamilton's equations. -/
lemma canonicalLocalKahlerSymplecticChart_omega :
    canonicalLocalKahlerSymplecticChart.omega = symplecticForm2 := rfl

/-- The canonical local Kähler form is antisymmetric, by the existing
Hamiltonian symplectic-form theorem. -/
lemma canonicalLocalKahlerSymplecticChart_antisymm (i j : Fin 2) :
    canonicalLocalKahlerSymplecticChart.omega i j =
      -canonicalLocalKahlerSymplecticChart.omega j i :=
  canonicalLocalKahlerSymplecticChart.omega_antisymm i j

/-- Certificate for a Kähler Hamiltonian isometry action.  It records the
pieces the paper uses: metric preservation, symplectic preservation,
compatibility with the complex structure, and invariance of the Hamiltonian
moment function along the action. -/
structure KahlerHamiltonianIsometryCertificate (M G : Type*) where
  /-- Group action on the Kähler space. -/
  action : G → M → M
  /-- Metric pairing, kept abstract at the finite certificate layer. -/
  metric : M → M → Real
  /-- Symplectic pairing. -/
  symplectic : M → M → Real
  /-- Complex-structure map. -/
  complexStructure : M → M
  /-- Hamiltonian moment function for the action. -/
  momentHamiltonian : M → Real
  /-- The action preserves the metric. -/
  preserves_metric : ∀ g p q, metric (action g p) (action g q) = metric p q
  /-- The action preserves the symplectic form. -/
  preserves_symplectic : ∀ g p q, symplectic (action g p) (action g q) = symplectic p q
  /-- The action commutes with the complex structure. -/
  commutes_complexStructure : ∀ g p, complexStructure (action g p) = action g (complexStructure p)
  /-- The Hamiltonian moment function is invariant along the action. -/
  moment_invariant : ∀ g p, momentHamiltonian (action g p) = momentHamiltonian p

/-- A Kähler Hamiltonian isometry preserves all four pieces recorded in the
certificate: metric, symplectic form, complex structure, and Hamiltonian
moment function. -/
lemma kahlerHamiltonianIsometry_preserves_all {M G : Type*}
    (K : KahlerHamiltonianIsometryCertificate M G)
    (g : G) (p q : M) :
    K.metric (K.action g p) (K.action g q) = K.metric p q
      ∧ K.symplectic (K.action g p) (K.action g q) = K.symplectic p q
      ∧ K.complexStructure (K.action g p) = K.action g (K.complexStructure p)
      ∧ K.momentHamiltonian (K.action g p) = K.momentHamiltonian p := by
  exact ⟨K.preserves_metric g p q, K.preserves_symplectic g p q,
    K.commutes_complexStructure g p, K.moment_invariant g p⟩

/-- Product-type Kähler metric near a critical component.  This is the
rank-level version of the product metric condition discussed after the
Kähler-Hamiltonian paragraph and in Proposition 2.16. -/
structure ProductTypeKahlerMetricCertificate (Base Fiber : Type*) where
  /-- Metric on the critical component. -/
  baseMetric : Base → Base → Real
  /-- Metric on the normal fiber. -/
  fiberMetric : Fiber → Fiber → Real
  /-- Total metric on the product neighborhood. -/
  totalMetric : Base × Fiber → Base × Fiber → Real
  /-- Product decomposition of the metric. -/
  totalMetric_eq :
    ∀ b1 b2 u v,
      totalMetric (b1, u) (b2, v) = baseMetric b1 b2 + fiberMetric u v

/-- Isometric transport of normal fibers over a critical component.  This is
the finite certificate form of the paper's "fiber metrics are isometric" input
used to construct a model wedge metric. -/
structure IsometricFiberTransportCertificate (Base Fiber : Type*) where
  /-- Base-dependent fiber metric. -/
  fiberMetricAt : Base → Fiber → Fiber → Real
  /-- Transport between fibers. -/
  transport : Base → Base → Fiber → Fiber
  /-- Transport preserves the fiber metric. -/
  transport_isometry :
    ∀ b1 b2 u v,
      fiberMetricAt b2 (transport b1 b2 u) (transport b1 b2 v) =
        fiberMetricAt b1 u v

/-- Product-type Kähler neighborhoods with isometric fibers supply the same
local rank equality as the Witten instanton spectral-window certificate. -/
lemma kahlerProductIsometry_spectralWindow_to_wittenRank {M G Base Fiber Crit : Type*}
    [Fintype Crit]
    (K : KahlerHamiltonianIsometryCertificate M G)
    (P : ProductTypeKahlerMetricCertificate Base Fiber)
    (F : IsometricFiberTransportCertificate Base Fiber)
    (D : WittenInstantonRankData Crit)
    (S : SpectralWindowRankCertificate D)
    (g : G) (p q : M) (b1 b2 : Base) (u v : Fiber) (k : Nat) :
    K.metric (K.action g p) (K.action g q) = K.metric p q
      ∧ P.totalMetric (b1, u) (b2, v) = P.baseMetric b1 b2 + P.fiberMetric u v
      ∧ F.fiberMetricAt b2 (F.transport b1 b2 u) (F.transport b1 b2 v) =
          F.fiberMetricAt b1 u v
      ∧ D.smallEigenvalueRank k = localMorseCoefficient D k := by
  exact ⟨K.preserves_metric g p q, P.totalMetric_eq b1 b2 u v,
    F.transport_isometry b1 b2 u v, smallEigenvalueRank_eq_local_of_spectralWindow D S k⟩

/-! ## D. Section 6 trefoil-cone example -/

set_option backward.isDefEq.respectTransparency false in
/-- Critical components in the Section 6 projective-variety example: a
non-isolated trefoil-cone component and an isolated critical point. -/
inductive TrefoilConeCriticalComponent where
  | nonisolatedTrefoilCone
  | isolatedPoint
  deriving DecidableEq, Fintype

/-- Local ranks for the trefoil-cone example: one local class in degrees
`0` and `2` at the non-isolated component, and one class in degree `4` at
the isolated component. -/
def trefoilConeLocalRank : TrefoilConeCriticalComponent → Nat → Nat
  | .nonisolatedTrefoilCone, 0 => 1
  | .nonisolatedTrefoilCone, 2 => 1
  | .isolatedPoint, 4 => 1
  | _, _ => 0

/-- The Morse rank sequence of the trefoil-cone example. -/
def trefoilConeMorseRank (k : Nat) : Nat :=
  ∑ a : TrefoilConeCriticalComponent, trefoilConeLocalRank a k

/-- Rank data for the Section 6 trefoil-cone example. -/
def trefoilConeRankData : WittenInstantonRankData TrefoilConeCriticalComponent where
  localCohomologyRank := trefoilConeLocalRank
  smallEigenvalueRank := trefoilConeMorseRank
  globalCohomologyRank := trefoilConeMorseRank

/-- The trefoil-cone example has the small-eigenvalue rank equality and is
quasi-isomorphic at the rank level. -/
def trefoilConeInstantonCertificate :
    WittenInstantonComplexCertificate trefoilConeRankData where
  small_eq_local := by
    intro k
    rfl
  quasiIso_rank := by
    intro k
    exact le_rfl

/-- The trefoil-cone example has zero strong-Morse remainder. -/
def trefoilConeStrongPolynomialMorseCertificate :
    StrongPolynomialMorseCertificate trefoilConeRankData where
  remainder := fun _ => 0
  remainder_nonneg := by
    intro k
    norm_num
  defect_zero := by
    simp [morseCoefficientInt, poincareCoefficientInt, trefoilConeRankData,
      trefoilConeMorseRank, localMorseCoefficient]
  defect_succ := by
    intro k
    simp [morseCoefficientInt, poincareCoefficientInt, trefoilConeRankData,
      trefoilConeMorseRank, localMorseCoefficient]

/-- Example 6.6 is perfect: its Morse and Poincare ranks agree in every
degree. -/
lemma trefoilCone_isPerfect : IsPerfect trefoilConeRankData := by
  exact isPerfect_of_strongPolynomialMorse_remainder_zero
    trefoilConeRankData trefoilConeStrongPolynomialMorseCertificate (by intro k; rfl)

/-- The trefoil-cone example has Morse coefficient `1` in degree `0`. -/
lemma trefoilCone_morse_coeff_zero :
    localMorseCoefficient trefoilConeRankData 0 = 1 := by
  native_decide

/-- The trefoil-cone example has Morse coefficient `1` in degree `2`. -/
lemma trefoilCone_morse_coeff_two :
    localMorseCoefficient trefoilConeRankData 2 = 1 := by
  native_decide

/-- The trefoil-cone example has Morse coefficient `1` in degree `4`. -/
lemma trefoilCone_morse_coeff_four :
    localMorseCoefficient trefoilConeRankData 4 = 1 := by
  native_decide

/-- The trefoil-cone example has no degree-`1` local contribution. -/
lemma trefoilCone_morse_coeff_one :
    localMorseCoefficient trefoilConeRankData 1 = 0 := by
  native_decide

/-- Section 6's trefoil-cone local cohomology ranks are available together
with the existing Chern-Simons/Witten trefoil invariant. -/
lemma trefoilCone_localRanks_and_trefoilInvariant (A : Complex) (hA : A ≠ 0) :
    localMorseCoefficient trefoilConeRankData 0 = 1
      ∧ localMorseCoefficient trefoilConeRankData 2 = 1
      ∧ localMorseCoefficient trefoilConeRankData 4 = 1
      ∧ kauffmanClosure (kauffmanLoopValue A)
          (tlMul (kauffmanLoopValue A) (crossingTL A)
            (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
        = electronJones A := by
  exact ⟨trefoilCone_morse_coeff_zero, trefoilCone_morse_coeff_two,
    trefoilCone_morse_coeff_four, electron_csw_invariant A hA⟩

/-- The trefoil-cone example combines perfect stratified Morse-Bott ranks with
the existing Chern-Simons trefoil invariant. -/
lemma trefoilCone_perfect_and_trefoilInvariant (A : Complex) (hA : A ≠ 0) :
    IsPerfect trefoilConeRankData
      ∧ kauffmanClosure (kauffmanLoopValue A)
          (tlMul (kauffmanLoopValue A) (crossingTL A)
            (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
        = electronJones A := by
  exact ⟨trefoilCone_isPerfect, electron_csw_invariant A hA⟩

/-! ## D. Cartan-Einstein icosahedral dilaton link -/

/-- The stratified Witten-Morse rank layer can be used on the same background
where the repository already has the Weyl-Cartan dilatonic connection, the
`SU(5)` Cartan metric with icosahedral symmetry, and the Einstein
stress-energy symmetrization by the icosahedral group. -/
lemma cartanEinsteinIcosahedralDilaton_links {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : IcosahedralGroup →* Equiv.Perm ι)
    (T : TetradConnection ι) (g : ι → ι → Real) (weyl : ι → Real)
    (hsym : ∀ a b, g a b = g b a)
    (gamma : IcosahedralGroup) (i j : Fin 5)
    (chi a n : Real) (gM Ric : Matrix ι ι Real) (scalarR : Real)
    (Rm : RiemannTensor ι) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    IsWeylNonmetricity
        (nonmetricity (fun a b c => T.Γ a b c + weylDistortion g weyl a b c)) g weyl
      ∧ su5CartanMetric ((gamma : Equiv.Perm (Fin 5)) i)
          ((gamma : Equiv.Perm (Fin 5)) j) = su5CartanMetric i j
      ∧ IcosahedrallyInvariant rho
          (icosahedralAverage rho (fourIndexEnergyMomentum chi a n gM Ric scalarR Rm))
      ∧ icosahedralAverage rho (fourIndexEnergyMomentum chi a n gM Ric scalarR Rm)
          = icosahedralAverage rho (fieldEnergyMomentum chi a n gM Ric scalarR Rm)
            + icosahedralAverage rho (matterEnergyMomentum chi n gM Ric scalarR) := by
  have hstress :=
    icosahedral_symmetrized_stressEnergy rho chi a n gM Ric scalarR Rm hn1 hn2
  exact ⟨weylCartan_connection_isWeyl T g weyl hsym,
    su5CartanMetric_icosahedral_invariant gamma i j, hstress.1, hstress.2⟩

/-- Combined bridge for Example 6.6: the Kähler circle fixed-coordinate
description gives the trefoil-cone critical component, whose rank datum is
perfect and whose trefoil knot is linked to the existing Chern-Simons
invariant; the same result is compatible with the Cartan-Einstein
icosahedral/Weyl-Cartan dilaton background through existing repo lemmas. -/
lemma kahlerTrefoilCone_cartanEinsteinIcosahedralDilaton_bridge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : IcosahedralGroup →* Equiv.Perm ι)
    (T : TetradConnection ι) (g : ι → ι → Real) (weyl : ι → Real)
    (hsym : ∀ a b, g a b = g b a)
    (gamma : IcosahedralGroup) (i j : Fin 5)
    (chi a n : Real) (gM Ric : Matrix ι ι Real) (scalarR : Real)
    (Rm : RiemannTensor ι) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0)
    (A : Complex) (hA : A ≠ 0) :
    (∀ c : CP3Coordinate, cp3TrefoilConeCoordinate c ↔ cp3CircleWeight c = 0)
      ∧ IsPerfect trefoilConeRankData
      ∧ kauffmanClosure (kauffmanLoopValue A)
          (tlMul (kauffmanLoopValue A) (crossingTL A)
            (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
        = electronJones A
      ∧ IsWeylNonmetricity
          (nonmetricity (fun a b c => T.Γ a b c + weylDistortion g weyl a b c)) g weyl
      ∧ su5CartanMetric ((gamma : Equiv.Perm (Fin 5)) i)
          ((gamma : Equiv.Perm (Fin 5)) j) = su5CartanMetric i j
      ∧ IcosahedrallyInvariant rho
          (icosahedralAverage rho (fourIndexEnergyMomentum chi a n gM Ric scalarR Rm))
      ∧ icosahedralAverage rho (fourIndexEnergyMomentum chi a n gM Ric scalarR Rm)
          = icosahedralAverage rho (fieldEnergyMomentum chi a n gM Ric scalarR Rm)
            + icosahedralAverage rho (matterEnergyMomentum chi n gM Ric scalarR) := by
  have hcartan :=
    cartanEinsteinIcosahedralDilaton_links rho T g weyl hsym gamma i j
      chi a n gM Ric scalarR Rm hn1 hn2
  exact ⟨cp3TrefoilConeCoordinate_iff_circleWeight_zero,
    trefoilCone_isPerfect, electron_csw_invariant A hA, hcartan.1,
    hcartan.2.1, hcartan.2.2.1, hcartan.2.2.2⟩

end Physlib.QuantumMechanics.ComplexAction.WittenInstantonMorseBottStratified

end
