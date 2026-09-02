/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum
public import Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT
public import Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon
public import Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization
public import Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
public import Physlib.Relativity.CliffordAlgebra
public import Physlib.Relativity.PauliMatrices.Basic
meta import Zil

/-!
# A. Spinor Structure and Internal Symmetries

This module formalizes the stable algebraic part of V. V. Varlamov,
"Spinor Structure and Internal Symmetries", arXiv:1409.1400v2.

The paper relates finite-dimensional `SL(2,C)` spinor representations
`tau_(k/2,r/2)` to internal symmetry multiplets.  The formalized layer here
records the parts that are clean finite algebra:

* `SL(2,C)` representation labels `(k,r)`, their degree `(k+1)(r+1)`,
  spin numerator `|k-r|`, and spinspace size `2^(k+r)`.
* Complex-momentum eigenvalues as the generating kernel for the basic
  `SL(2,C)` energy levels.
* The paper's basic spin-mass level
  `m = mu0 * ((k+1)/2) * ((r+1)/2)`, stated also in the denominator-free
  form `4*m = mu0*(k+1)*(r+1)`.
* The admissibility condition for hadron `SU(3)` supermultiplets,
  expressed as `p mod 3 = q mod 3`, equivalent to `p-q = 0 mod 3` for
  Dynkin labels `(p,q)`.
* The `SU(3)` octet reduction bookkeeping `3 + 2 + 2 + 1 = 8`.
* The Gell-Mann-Okubo quadratic and linear splitting polynomials used in
  the paper for hypercharge and charge splittings inside an `SU(3)`
  supermultiplet.
* The Zeeman-effect analogy: the hypercharge and charge terms are
  linear shifts by a quantum number, just as `Delta E = coupling * field * m`
  in a Zeeman splitting.

The module links these statements to existing Physlib code instead of
redefining it: `weylDim3` and Casimirs from `Su3WeylDimensionCasimir`,
the baryon `SU(6)` `56 -> (10,4) + (8,2)` branching from
`Su6SpinFlavorBaryon`, particle-antiparticle conjugation from
`ParticleZooCPT`, and the `SU(5)` charge/hypercharge trace normalization
from `Su5WeinbergGutNormalization`.

## A.1. References

* V. V. Varlamov, "Spinor Structure and Internal Symmetries",
  arXiv:1409.1400v2.
* M. Gell-Mann and Y. Ne'eman, "The Eightfold Way".
* S. Okubo and C. Ryan, "Quadratic mass formula in SU(3)".
-/

set_option autoImplicit false

open scoped BigOperators

open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.Particles.ParticleZooCPT
open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
open Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon
open Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization
open Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
open Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
open Matrix
open spaceTime

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries

/-! ## A.2. `SL(2,C)` Spinor Labels -/

/-- A finite-dimensional `SL(2,C)` spinor representation label `(k,r)`,
corresponding to Varlamov's `tau_(k/2,r/2)`. -/
structure LorentzSpinorRepresentation where
  /-- Number of undotted spinor factors. -/
  leftFactors : Nat
  /-- Number of dotted spinor factors. -/
  rightFactors : Nat
deriving DecidableEq, Repr

/-- The degree of `tau_(k/2,r/2)`, namely `(k+1)(r+1)`. -/
def sl2cRepresentationDegree (R : LorentzSpinorRepresentation) : Nat :=
  (R.leftFactors + 1) * (R.rightFactors + 1)

/-- The spinspace size associated to `(k,r)`, namely `2^(k+r)`. -/
def spinspaceDimension (R : LorentzSpinorRepresentation) : Nat :=
  2 ^ (R.leftFactors + R.rightFactors)

/-- Twice the generalized spin: `2s = |k-r|`. -/
def spinNumerator (R : LorentzSpinorRepresentation) : Nat :=
  Int.natAbs ((R.leftFactors : Int) - (R.rightFactors : Int))

/-- The generalized spin value `s = |k-r|/2`. -/
def spinValue (R : LorentzSpinorRepresentation) : Rat :=
  (spinNumerator R : Rat) / 2

/-- The positive fixed-spin interlocking line with fixed doubled spin `d`.
Its `n`-th label is `(n+d,n)`, i.e. Varlamov's
`tau_((n+d)/2,n/2)`. -/
def fixedSpinLineLabel (d n : Nat) : LorentzSpinorRepresentation :=
  { leftFactors := n + d, rightFactors := n }

/-- The dual fixed-spin interlocking line with fixed doubled spin `d`.
Its `n`-th label is `(n,n+d)`. -/
def dualFixedSpinLineLabel (d n : Nat) : LorentzSpinorRepresentation :=
  { leftFactors := n, rightFactors := n + d }

/-- The spin-zero line `(n,n)`. -/
def spinZeroLineLabel (n : Nat) : LorentzSpinorRepresentation :=
  fixedSpinLineLabel 0 n

/-- The spin-one-half line `(n+1,n)`, written with doubled spin labels. -/
def spinHalfLineLabel (n : Nat) : LorentzSpinorRepresentation :=
  fixedSpinLineLabel 1 n

/-- The spin-one line `(n+2,n)`, written with doubled spin labels. -/
def spinOneLineLabel (n : Nat) : LorentzSpinorRepresentation :=
  fixedSpinLineLabel 2 n

/-- The representation degree is positive. -/
lemma sl2cRepresentationDegree_pos (R : LorentzSpinorRepresentation) :
    0 < sl2cRepresentationDegree R := by
  unfold sl2cRepresentationDegree
  positivity

/-- Every spinspace dimension in this finite model is positive. -/
lemma spinspaceDimension_pos (R : LorentzSpinorRepresentation) :
    0 < spinspaceDimension R := by
  unfold spinspaceDimension
  positivity

/-- A self-conjugate label `(k,k)` has generalized spin numerator zero. -/
lemma spinNumerator_self_conjugate_zero (k : Nat) :
    spinNumerator { leftFactors := k, rightFactors := k } = 0 := by
  simp [spinNumerator]

/-- Exchanging dotted and undotted factors does not change `|k-r|`. -/
lemma spinNumerator_chiral_swap (R : LorentzSpinorRepresentation) :
    spinNumerator { leftFactors := R.rightFactors, rightFactors := R.leftFactors } =
      spinNumerator R := by
  unfold spinNumerator
  rw [show ((R.rightFactors : Int) - (R.leftFactors : Int))
      = -((R.leftFactors : Int) - (R.rightFactors : Int)) by ring]
  rw [Int.natAbs_neg]

/-- Exchanging dotted and undotted factors preserves the generalized spin. -/
lemma spinValue_chiral_swap (R : LorentzSpinorRepresentation) :
    spinValue { leftFactors := R.rightFactors, rightFactors := R.leftFactors } =
      spinValue R := by
  simp [spinValue, spinNumerator_chiral_swap]

/-- The fixed-spin line has spin numerator equal to its doubled spin `d`. -/
lemma fixedSpinLineLabel_spinNumerator (d n : Nat) :
    spinNumerator (fixedSpinLineLabel d n) = d := by
  unfold spinNumerator fixedSpinLineLabel
  rw [show ((n + d : Nat) : Int) - (n : Int) = (d : Int) by omega]
  simp

/-- The dual fixed-spin line has the same spin numerator. -/
lemma dualFixedSpinLineLabel_spinNumerator (d n : Nat) :
    spinNumerator (dualFixedSpinLineLabel d n) = d := by
  unfold spinNumerator dualFixedSpinLineLabel
  rw [show (n : Int) - ((n + d : Nat) : Int) = -(d : Int) by omega]
  rw [Int.natAbs_neg]
  simp

/-- The fixed-spin line has representation degree `(n+d+1)(n+1)`. -/
lemma fixedSpinLineLabel_degree (d n : Nat) :
    sl2cRepresentationDegree (fixedSpinLineLabel d n) =
      (n + d + 1) * (n + 1) := by
  rfl

/-- The fixed-spin line has spinspace dimension `2^(2n+d)`. -/
lemma fixedSpinLineLabel_spinspaceDimension (d n : Nat) :
    spinspaceDimension (fixedSpinLineLabel d n) = 2 ^ (2 * n + d) := by
  unfold spinspaceDimension fixedSpinLineLabel
  change 2 ^ ((n + d) + n) = 2 ^ (2 * n + d)
  congr 1
  omega

/-- The spin-zero line has degree `(n+1)^2`. -/
lemma spinZeroLineLabel_degree (n : Nat) :
    sl2cRepresentationDegree (spinZeroLineLabel n) = (n + 1) ^ 2 := by
  unfold spinZeroLineLabel
  rw [fixedSpinLineLabel_degree]
  ring

/-- The spin-one-half line has degree `(n+2)(n+1)`. -/
lemma spinHalfLineLabel_degree (n : Nat) :
    sl2cRepresentationDegree (spinHalfLineLabel n) = (n + 2) * (n + 1) := by
  rfl

/-- The spin-one line has degree `(n+3)(n+1)`. -/
lemma spinOneLineLabel_degree (n : Nat) :
    sl2cRepresentationDegree (spinOneLineLabel n) = (n + 3) * (n + 1) := by
  rfl

/-- The spin-zero line is bosonic in the tensor-degree parity sense:
`k+r` is even. -/
lemma spinZeroLineLabel_factorParity (n : Nat) :
    ((spinZeroLineLabel n).leftFactors + (spinZeroLineLabel n).rightFactors) % 2 = 0 := by
  simp [spinZeroLineLabel, fixedSpinLineLabel]
  omega

/-- The spin-one-half line is fermionic in the tensor-degree parity sense:
`k+r` is odd. -/
lemma spinHalfLineLabel_factorParity (n : Nat) :
    ((spinHalfLineLabel n).leftFactors + (spinHalfLineLabel n).rightFactors) % 2 = 1 := by
  simp [spinHalfLineLabel, fixedSpinLineLabel]
  omega

/-- The spin-one line is bosonic in the tensor-degree parity sense:
`k+r` is even. -/
lemma spinOneLineLabel_factorParity (n : Nat) :
    ((spinOneLineLabel n).leftFactors + (spinOneLineLabel n).rightFactors) % 2 = 0 := by
  simp [spinOneLineLabel, fixedSpinLineLabel]
  omega

/-! ## A.3. Spinor Factors, Clifford Periodicity, and Neutrality -/

/-- The finite label set for the tensor factors in
`C2^{\otimes k} ⊗ (C2*)^{\otimes r}`: undotted factors on the left, dotted
factors on the right. -/
abbrev SpinorFactorLabel (R : LorentzSpinorRepresentation) : Type :=
  Fin R.leftFactors ⊕ Fin R.rightFactors

/-- The binary tensor dimension generated by all undotted and dotted spinor
factor labels. -/
def binarySpinorTensorDimension (R : LorentzSpinorRepresentation) : Nat :=
  2 ^ Fintype.card (SpinorFactorLabel R)

/-- The finite factor-label count is `k+r`. -/
lemma spinorFactorLabel_card (R : LorentzSpinorRepresentation) :
    Fintype.card (SpinorFactorLabel R) = R.leftFactors + R.rightFactors := by
  simp [SpinorFactorLabel]

/-- The binary tensor dimension agrees with the existing spinspace dimension
`2^(k+r)`. -/
lemma binarySpinorTensorDimension_eq_spinspaceDimension
    (R : LorentzSpinorRepresentation) :
    binarySpinorTensorDimension R = spinspaceDimension R := by
  simp [binarySpinorTensorDimension, spinspaceDimension]

/-- The mod-8 real Clifford residue attached to a signature `(p,q)`,
represented as `p-q mod 8`. -/
def cliffordSignatureResidue (p q : Nat) : Fin 8 :=
  ⟨(p + 8 - q % 8) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The four-dimensional Minkowski signature `(1,3)` has residue `6 mod 8`. -/
lemma cliffordSignatureResidue_minkowski_13 :
    (cliffordSignatureResidue 1 3).val = 6 := by
  norm_num [cliffordSignatureResidue]

/-- The `3+1` convention `(3,1)` has residue `2 mod 8`. -/
lemma cliffordSignatureResidue_minkowski_31 :
    (cliffordSignatureResidue 3 1).val = 2 := by
  norm_num [cliffordSignatureResidue]

/-- The concrete Dirac gamma generators are in the range of the existing
Clifford-algebra map. -/
lemma diracGamma_generator_from_clifford (i : Fin 4) :
    ⟨γ i, γ.γ_in_diracAlgebra i⟩ ∈ γ.ofCliffordAlgebra.range :=
  γ.γ_subtype_in_range i

/-- The existing Clifford-algebra map onto the Dirac gamma algebra is
surjective. -/
lemma diracCliffordAlgebra_surjective :
    Function.Surjective γ.ofCliffordAlgebra :=
  γ.ofCliffordAlgebra_surjective

/-- Electrical neutrality: only electric charge is zero. -/
def ElectricallyNeutral (q : QuantumNumbers) : Prop :=
  q.electric = 0

/-- True neutrality: all additive quantum numbers vanish, so the particle is
self-conjugate under charge conjugation. -/
def TrulyNeutral (q : QuantumNumbers) : Prop :=
  q.electric = 0 ∧ q.baryon = 0 ∧ q.lepton = 0

/-- True neutrality implies electrical neutrality. -/
lemma trulyNeutral_implies_electricallyNeutral {q : QuantumNumbers} :
    TrulyNeutral q -> ElectricallyNeutral q := by
  intro h
  exact h.1

/-- True neutrality is exactly self-conjugacy under the existing additive
charge-conjugation map. -/
lemma trulyNeutral_iff_conjugate_eq (q : QuantumNumbers) :
    TrulyNeutral q ↔ conjugate q = q := by
  rw [selfConjugate_iff_neutral]
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- An electrically neutral particle with nonzero lepton number is not truly
neutral. -/
lemma not_trulyNeutral_of_nonzero_lepton {q : QuantumNumbers}
    (hL : q.lepton ≠ 0) : ¬ TrulyNeutral q := by
  intro h
  exact hL h.2.2

/-- The muon neutrino is electrically neutral but not truly neutral in the
Dirac additive-quantum-number model because its lepton number is nonzero. -/
lemma muonNeutrino_electricallyNeutral_not_trulyNeutral :
    ElectricallyNeutral muonNeutrino ∧ ¬ TrulyNeutral muonNeutrino := by
  constructor
  · rfl
  · exact not_trulyNeutral_of_nonzero_lepton (by norm_num [muonNeutrino])

/-- The photon is truly neutral, reusing the existing self-conjugate photon
model. -/
lemma photon_trulyNeutral : TrulyNeutral photon := by
  rw [trulyNeutral_iff_conjugate_eq]
  exact photon_selfConjugate

/-- The Dirac spinor discrete-symmetry square signs: `P^2 = 1`, `C^2 = 1`,
`T^2 = -1`, and `CPT^2 = -1`. -/
structure DiracCPTSquareSigns where
  /-- Parity square sign. -/
  paritySquare : Int
  /-- Charge-conjugation square sign. -/
  chargeSquare : Int
  /-- Time-reversal square sign. -/
  timeSquare : Int
  /-- Combined CPT square sign. -/
  cptSquare : Int
deriving DecidableEq, Repr

/-- The concrete square-sign table for the Dirac spinor CPT operators. -/
def diracCPTSquareSigns : DiracCPTSquareSigns :=
  { paritySquare := 1, chargeSquare := 1, timeSquare := -1, cptSquare := -1 }

/-- The square-sign table is realized by the existing Dirac spinor `P`, `C`,
`T`, and `CPT` operators. -/
lemma diracCPTSquareSigns_checked (ψ : Fin 4 → ℂ) :
    parityOp (parityOp ψ) = ψ
      ∧ chargeConj (chargeConj ψ) = ψ
      ∧ timeReversal (timeReversal ψ) = -ψ
      ∧ cpt (cpt ψ) = -ψ :=
  ⟨parity_involutive ψ, chargeConj_involutive ψ, timeReversal_sq ψ, cpt_sq ψ⟩

/-- Clifford grade-involution sign on a homogeneous degree-`k` element:
`(-1)^k`. -/
def cliffordGradeInvolutionSign (k : Nat) : Int :=
  (-1 : Int) ^ k

/-- Clifford reversion sign on a homogeneous degree-`k` element:
`(-1)^(k*(k-1)/2)`. -/
def cliffordReversionSign (k : Nat) : Int :=
  (-1 : Int) ^ (k * (k - 1) / 2)

/-- Clifford conjugation sign on a homogeneous degree-`k` element:
`(-1)^(k*(k+1)/2)`. -/
def cliffordConjugationSign (k : Nat) : Int :=
  (-1 : Int) ^ (k * (k + 1) / 2)

/-- Clifford conjugation is grade involution followed by reversion on the four
homogeneous-degree residue classes. -/
lemma cliffordConjugationSign_eq_grade_mul_reversion_mod_four (k : Fin 4) :
    cliffordConjugationSign k =
      cliffordGradeInvolutionSign k * cliffordReversionSign k := by
  fin_cases k <;>
    norm_num [cliffordConjugationSign, cliffordGradeInvolutionSign,
      cliffordReversionSign]

/-- Boolean exclusive-or used for the finite `C`, `P`, and `T` bit records. -/
def symmetryBitXor (a b : Bool) : Bool :=
  decide (a ≠ b)

/-- The eight Clifford `CPT` automorphism labels, represented as independent
charge, parity, and time bits. -/
structure CliffordCPTAutomorphism where
  /-- The charge-conjugation bit. -/
  charge : Bool
  /-- The parity bit. -/
  parity : Bool
  /-- The time-reversal bit. -/
  time : Bool
deriving DecidableEq, Repr, Fintype

/-- The identity element in the finite Clifford `CPT` automorphism table. -/
def cliffordCPTIdentity : CliffordCPTAutomorphism :=
  { charge := false, parity := false, time := false }

/-- Composition in the finite Clifford `CPT` automorphism table, modeled as
componentwise addition in `(Z/2Z)^3`. -/
def cliffordCPTCompose (A B : CliffordCPTAutomorphism) : CliffordCPTAutomorphism :=
  { charge := symmetryBitXor A.charge B.charge
    parity := symmetryBitXor A.parity B.parity
    time := symmetryBitXor A.time B.time }

/-- The Clifford `CPT` automorphism table has eight elements. -/
lemma cliffordCPTAutomorphism_card :
    Fintype.card CliffordCPTAutomorphism = 8 := by
  decide

/-- Every element of the finite Clifford `CPT` table squares to the identity. -/
lemma cliffordCPTCompose_self (A : CliffordCPTAutomorphism) :
    cliffordCPTCompose A A = cliffordCPTIdentity := by
  rcases A with ⟨charge, parity, time⟩
  cases charge <;> cases parity <;> cases time <;> rfl

/-- The charge bit of a Clifford `CPT` label acts on additive quantum numbers
by the existing particle-zoo conjugation map. -/
def cliffordCPTChargeAction (A : CliffordCPTAutomorphism) (q : QuantumNumbers) :
    QuantumNumbers :=
  if A.charge then conjugate q else q

/-- A Clifford `CPT` label with no charge bit fixes additive quantum numbers. -/
lemma cliffordCPTChargeAction_no_charge
    (A : CliffordCPTAutomorphism) (q : QuantumNumbers) (hA : A.charge = false) :
    cliffordCPTChargeAction A q = q := by
  simp [cliffordCPTChargeAction, hA]

/-- A Clifford `CPT` label with the charge bit applies particle-zoo
conjugation. -/
lemma cliffordCPTChargeAction_charge
    (A : CliffordCPTAutomorphism) (q : QuantumNumbers) (hA : A.charge = true) :
    cliffordCPTChargeAction A q = conjugate q := by
  simp [cliffordCPTChargeAction, hA]

/-- Applying the charge part of the same Clifford `CPT` label twice fixes
additive quantum numbers. -/
lemma cliffordCPTChargeAction_twice (A : CliffordCPTAutomorphism) (q : QuantumNumbers) :
    cliffordCPTChargeAction A (cliffordCPTChargeAction A q) = q := by
  cases hA : A.charge
  · simp [cliffordCPTChargeAction, hA]
  · simp [cliffordCPTChargeAction, hA, zoo_conjugate_involutive]

/-! ## A.4. Interlocking Spinor Labels -/

/-- Adjacent labels in the interlocking spin-chain diagram: both spinor
factor counts differ by one. -/
def Interlocking (A B : LorentzSpinorRepresentation) : Prop :=
  (B.leftFactors = A.leftFactors + 1 ∨ A.leftFactors = B.leftFactors + 1)
    ∧ (B.rightFactors = A.rightFactors + 1 ∨ A.rightFactors = B.rightFactors + 1)

/-- Interlocking is symmetric. -/
lemma interlocking_symm {A B : LorentzSpinorRepresentation} :
    Interlocking A B -> Interlocking B A := by
  intro h
  rcases h with ⟨hl, hr⟩
  constructor
  · rcases hl with hl | hl
    · exact Or.inr hl
    · exact Or.inl hl
  · rcases hr with hr | hr
    · exact Or.inr hr
    · exact Or.inl hr

/-- Moving from `(k,r)` to `(k+1,r+1)` preserves the generalized spin
numerator. -/
lemma spinNumerator_diagonal_step (k r : Nat) :
    spinNumerator { leftFactors := k + 1, rightFactors := r + 1 } =
      spinNumerator { leftFactors := k, rightFactors := r } := by
  change Int.natAbs (((k + 1 : Nat) : Int) - ((r + 1 : Nat) : Int)) =
    Int.natAbs ((k : Int) - (r : Int))
  congr 1
  omega

/-! ## A.5. Basic Spin-Mass Level -/

/-- Varlamov's basic spin-mass level
`m = mu0 * ((k+1)/2) * ((r+1)/2)`. -/
def spinMassLevel (mu0 : Rat) (R : LorentzSpinorRepresentation) : Rat :=
  mu0 * ((R.leftFactors + 1 : Rat) / 2) * ((R.rightFactors + 1 : Rat) / 2)

/-- Denominator-free form of the spin-mass level:
`4*m = mu0*(k+1)*(r+1)`. -/
lemma four_mul_spinMassLevel (mu0 : Rat) (R : LorentzSpinorRepresentation) :
    4 * spinMassLevel mu0 R =
      mu0 * (R.leftFactors + 1 : Rat) * (R.rightFactors + 1 : Rat) := by
  unfold spinMassLevel
  ring

/-- The spin-mass level is symmetric under chiral exchange. -/
lemma spinMassLevel_chiral_swap (mu0 : Rat) (R : LorentzSpinorRepresentation) :
    spinMassLevel mu0 { leftFactors := R.rightFactors, rightFactors := R.leftFactors } =
      spinMassLevel mu0 R := by
  unfold spinMassLevel
  ring

/-- For a self-conjugate spin-zero line `(k,k)`, the denominator-free
spin-mass relation is `4*m = mu0*(k+1)^2`. -/
lemma four_mul_spinMassLevel_self_conjugate (mu0 : Rat) (k : Nat) :
    4 * spinMassLevel mu0 { leftFactors := k, rightFactors := k } =
      mu0 * (k + 1 : Rat) ^ 2 := by
  rw [four_mul_spinMassLevel]
  ring

/-! ## A.6. Bhabha-Gelfand-Yaglom Mass-Shell Reduction -/

/-- The Minkowski mass-shell scalar `p0^2 - p1^2 - p2^2 - p3^2`. -/
def minkowskiMassShell (p : Fin 4 → ℝ) : ℝ :=
  p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2

/-- The rest-frame four-momentum with energy `E` and zero spatial momentum. -/
def restMomentum (E : ℝ) : Fin 4 → ℝ :=
  fun mu => if mu = 0 then E else 0

/-- The rest-frame mass shell is `E^2`. -/
lemma minkowskiMassShell_restMomentum (E : ℝ) :
    minkowskiMassShell (restMomentum E) = E ^ 2 := by
  simp [minkowskiMassShell, restMomentum]

/-- Finite determinant model for the Bhabha/Gelfand-Yaglom reduction:
the characteristic determinant factors through mass-shell roots. -/
def bhabhaDeterminantModel {N : Nat} (c : ℝ) (masses : Fin N → ℝ)
    (p : Fin 4 → ℝ) : ℝ :=
  c * ∏ i, (minkowskiMassShell p - masses i ^ 2)

/-- A zero of the determinant with nonzero prefactor gives one mass-shell
root. This is the finite-product content of the paper's determinant
factorization. -/
lemma bhabhaDeterminant_zero_gives_massShell_root {N : Nat}
    {c : ℝ} {masses : Fin N → ℝ} {p : Fin 4 → ℝ}
    (hc : c ≠ 0) (hdet : bhabhaDeterminantModel c masses p = 0) :
    ∃ i, minkowskiMassShell p = masses i ^ 2 := by
  classical
  have hprod : (∏ i, (minkowskiMassShell p - masses i ^ 2)) = 0 := by
    exact (mul_eq_zero.mp hdet).resolve_left hc
  rcases Finset.prod_eq_zero_iff.mp hprod with ⟨i, _hi, hfactor⟩
  exact ⟨i, by nlinarith⟩

/-- A mass-shell root forces the determinant model to vanish. -/
lemma bhabhaDeterminant_zero_of_massShell_root {N : Nat}
    (c : ℝ) (masses : Fin N → ℝ) (p : Fin 4 → ℝ) (i : Fin N)
    (hroot : minkowskiMassShell p = masses i ^ 2) :
    bhabhaDeterminantModel c masses p = 0 := by
  classical
  have hfactor : minkowskiMassShell p - masses i ^ 2 = 0 := by
    nlinarith
  have hprod : (∏ j, (minkowskiMassShell p - masses j ^ 2)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hfactor
  simp [bhabhaDeterminantModel, hprod]

/-- The mass values generated by a finite spinor multiplet through Varlamov's
basic spin-mass level. -/
def bhabhaSpinMasses {N : Nat} (mu0 : Rat)
    (reps : Fin N → LorentzSpinorRepresentation) : Fin N → ℝ :=
  fun i => ((spinMassLevel mu0 (reps i) : Rat) : ℝ)

/-- In the spinor-generated determinant model, every zero with nonzero
prefactor lies on one of the spinor mass shells. -/
lemma bhabhaDeterminant_zero_gives_spinMassLevel_root {N : Nat}
    {c : ℝ} {mu0 : Rat} {reps : Fin N → LorentzSpinorRepresentation}
    {p : Fin 4 → ℝ}
    (hc : c ≠ 0)
    (hdet : bhabhaDeterminantModel c (bhabhaSpinMasses mu0 reps) p = 0) :
    ∃ i, minkowskiMassShell p = ((spinMassLevel mu0 (reps i) : Rat) : ℝ) ^ 2 :=
  bhabhaDeterminant_zero_gives_massShell_root hc hdet

/-- A spinor mass-shell root forces the spinor-generated determinant model to
vanish. -/
lemma bhabhaDeterminant_zero_of_spinMassLevel_root {N : Nat}
    (c : ℝ) (mu0 : Rat) (reps : Fin N → LorentzSpinorRepresentation)
    (p : Fin 4 → ℝ) (i : Fin N)
    (hroot : minkowskiMassShell p = ((spinMassLevel mu0 (reps i) : Rat) : ℝ) ^ 2) :
    bhabhaDeterminantModel c (bhabhaSpinMasses mu0 reps) p = 0 :=
  bhabhaDeterminant_zero_of_massShell_root c (bhabhaSpinMasses mu0 reps) p i hroot

/-! ## A.6.1. Bivector Metric Induced from Minkowski Space -/

/-- The metric induced on antisymmetric pairs:
`G_abcd = g_ac*g_bd - g_ad*g_bc`. -/
def inducedBivectorMetric (g : Fin 4 → Fin 4 → ℝ)
    (a b c d : Fin 4) : ℝ :=
  g a c * g b d - g a d * g b c

/-- The induced bivector metric is antisymmetric in its first index pair. -/
lemma inducedBivectorMetric_swap_left (g : Fin 4 → Fin 4 → ℝ)
    (a b c d : Fin 4) :
    inducedBivectorMetric g b a c d = -inducedBivectorMetric g a b c d := by
  unfold inducedBivectorMetric
  ring

/-- The induced bivector metric is antisymmetric in its second index pair. -/
lemma inducedBivectorMetric_swap_right (g : Fin 4 → Fin 4 → ℝ)
    (a b c d : Fin 4) :
    inducedBivectorMetric g a b d c = -inducedBivectorMetric g a b c d := by
  unfold inducedBivectorMetric
  ring

/-- Split six-dimensional bivector index: three real directions and three
dual imaginary directions for the paper's `C^3 ≃ R^6` description. -/
abbrev BivectorSplitIndex : Type :=
  Fin 3 ⊕ Fin 3

/-- The split bivector index has dimension six. -/
lemma bivectorSplitIndex_card :
    Fintype.card BivectorSplitIndex = 6 := by
  simp [BivectorSplitIndex]

/-- The diagonal metric on the split bivector space with signature
`(-,-,-,+,+,+)`. -/
def bivectorSplitMetricDiag : BivectorSplitIndex → ℝ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

/-- The first three split bivector directions have negative metric sign. -/
lemma bivectorSplitMetricDiag_left (i : Fin 3) :
    bivectorSplitMetricDiag (Sum.inl i) = -1 := by
  rfl

/-- The second three split bivector directions have positive metric sign. -/
lemma bivectorSplitMetricDiag_right (i : Fin 3) :
    bivectorSplitMetricDiag (Sum.inr i) = 1 := by
  rfl

/-- The split realification map from `C^3` to the bivector `R^6` model. -/
def c3ToBivectorR6 (z : Fin 3 → ℂ) : BivectorSplitIndex → ℝ
  | Sum.inl i => (z i).re
  | Sum.inr i => (z i).im

/-- The diagonal quadratic form on the split bivector `R^6` model. -/
def bivectorSplitQuadraticForm (v : BivectorSplitIndex → ℝ) : ℝ :=
  ∑ a, bivectorSplitMetricDiag a * v a ^ 2

/-- The split bivector quadratic form is the difference between imaginary and
real Euclidean norms under the realification `C^3 -> R^6`. -/
lemma bivectorSplitQuadraticForm_c3ToBivectorR6 (z : Fin 3 → ℂ) :
    bivectorSplitQuadraticForm (c3ToBivectorR6 z) =
      (∑ i : Fin 3, (z i).im ^ 2) - ∑ i : Fin 3, (z i).re ^ 2 := by
  simp [bivectorSplitQuadraticForm, c3ToBivectorR6, bivectorSplitMetricDiag,
    BivectorSplitIndex]
  ring

/-! ## A.7. Wigner Branches and Spin-Charge Product Labels -/

set_option backward.isDefEq.respectTransparency false in
/-- The six Wigner orbit classes listed in the paper for the Poincare
representation interpretation. -/
inductive WignerOrbitKind where
  /-- Positive-energy massive hyperboloid. -/
  | positiveMassive
  /-- Negative-energy massive hyperboloid. -/
  | negativeMassive
  /-- Negative invariant-square orbit. -/
  | spacelikeMassive
  /-- Positive-energy light cone. -/
  | positiveLightlike
  /-- Negative-energy light cone. -/
  | negativeLightlike
  /-- The zero momentum orbit. -/
  | zeroMomentum
deriving DecidableEq, Repr, Fintype

/-- Wigner's orbit list has six cases. -/
lemma wignerOrbitKind_card :
    Fintype.card WignerOrbitKind = 6 := by
  decide

/-- The positive-energy mass shell `O_m^+`: invariant mass `m` and
nonnegative energy. -/
def PositiveMassShell (p : Fin 4 → ℝ) (m : ℝ) : Prop :=
  minkowskiMassShell p = m ^ 2 ∧ 0 ≤ p 0

/-- The negative-energy mass shell `O_m^-`: invariant mass `m` and
nonpositive energy. -/
def NegativeMassShell (p : Fin 4 → ℝ) (m : ℝ) : Prop :=
  minkowskiMassShell p = m ^ 2 ∧ p 0 ≤ 0

/-- The spacelike Wigner orbit `O_im`: invariant square `-m^2`. -/
def SpacelikeMassShell (p : Fin 4 → ℝ) (m : ℝ) : Prop :=
  minkowskiMassShell p = -m ^ 2

/-- The positive-energy light cone `O_0^+`. -/
def PositiveLightCone (p : Fin 4 → ℝ) : Prop :=
  minkowskiMassShell p = 0 ∧ 0 < p 0

/-- The negative-energy light cone `O_0^-`. -/
def NegativeLightCone (p : Fin 4 → ℝ) : Prop :=
  minkowskiMassShell p = 0 ∧ p 0 < 0

/-- The zero-momentum Wigner orbit `O_0^0`. -/
def ZeroMomentumOrbit (p : Fin 4 → ℝ) : Prop :=
  ∀ μ : Fin 4, p μ = 0

/-- A spacelike representative with spatial momentum on the first axis. -/
def xAxisMomentum (a : ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = 1 then a else 0

/-- A lightlike representative with `p0 = p1 = E`. -/
def lightlikeMomentum (E : ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then E else if μ = 1 then E else 0

/-- The rest momentum with nonnegative mass lies on the positive-energy
mass shell. -/
lemma positiveMassShell_restMomentum {m : ℝ} (hm : 0 ≤ m) :
    PositiveMassShell (restMomentum m) m := by
  constructor
  · exact minkowskiMassShell_restMomentum m
  · simpa [restMomentum] using hm

/-- The negative rest-energy representative lies on the negative-energy
mass shell with the same invariant mass. -/
lemma negativeMassShell_restMomentum {m : ℝ} (hm : 0 ≤ m) :
    NegativeMassShell (restMomentum (-m)) m := by
  constructor
  · rw [minkowskiMassShell_restMomentum]
    ring
  · have hneg : -m ≤ 0 := by linarith
    simpa [restMomentum] using hneg

/-- The first-axis spacelike representative has invariant square `-a^2`. -/
lemma minkowskiMassShell_xAxisMomentum (a : ℝ) :
    minkowskiMassShell (xAxisMomentum a) = -a ^ 2 := by
  simp [minkowskiMassShell, xAxisMomentum]

/-- The first-axis spacelike representative lies on the spacelike Wigner
orbit with invariant square `-m^2`. -/
lemma spacelikeMassShell_xAxisMomentum (m : ℝ) :
    SpacelikeMassShell (xAxisMomentum m) m := by
  exact minkowskiMassShell_xAxisMomentum m

/-- The lightlike representative has zero Minkowski norm. -/
lemma minkowskiMassShell_lightlikeMomentum (E : ℝ) :
    minkowskiMassShell (lightlikeMomentum E) = 0 := by
  simp [minkowskiMassShell, lightlikeMomentum]

/-- A positive-energy lightlike representative belongs to `O_0^+`. -/
lemma positiveLightCone_lightlikeMomentum {E : ℝ} (hE : 0 < E) :
    PositiveLightCone (lightlikeMomentum E) := by
  constructor
  · exact minkowskiMassShell_lightlikeMomentum E
  · simpa [lightlikeMomentum] using hE

/-- A negative-energy lightlike representative belongs to `O_0^-`. -/
lemma negativeLightCone_lightlikeMomentum {E : ℝ} (hE : E < 0) :
    NegativeLightCone (lightlikeMomentum E) := by
  constructor
  · exact minkowskiMassShell_lightlikeMomentum E
  · simpa [lightlikeMomentum] using hE

/-- The zero four-vector belongs to the zero-momentum orbit. -/
lemma zeroMomentumOrbit_zero :
    ZeroMomentumOrbit (fun _ : Fin 4 => (0 : ℝ)) := by
  intro μ
  rfl

/-- The zero-momentum orbit has zero Minkowski norm. -/
lemma zeroMomentumOrbit_minkowskiMassShell {p : Fin 4 → ℝ}
    (hp : ZeroMomentumOrbit p) :
    minkowskiMassShell p = 0 := by
  unfold minkowskiMassShell
  rw [hp 0, hp 1, hp 2, hp 3]
  norm_num

/-- The finite spin projection label set for spin `s = twiceSpin/2`; it has
`2s+1 = twiceSpin+1` projections. -/
abbrev SpinMultipletLabel (twiceSpin : Nat) : Type :=
  Fin (twiceSpin + 1)

/-- The finite charge multiplet label set. -/
abbrev ChargeMultipletLabel (chargeDim : Nat) : Type :=
  Fin chargeDim

/-- A finite momentum-basis truncation label set. -/
abbrev MomentumBasisLabel (momentumDim : Nat) : Type :=
  Fin momentumDim

/-- Finite label model for `H^S ⊗ H^Q ⊗ H_momentum`: spin projection,
charge multiplet, and a momentum-basis truncation. -/
abbrev SpinChargeMomentumHilbertBasis
    (twiceSpin chargeDim momentumDim : Nat) : Type :=
  SpinMultipletLabel twiceSpin × ChargeMultipletLabel chargeDim × MomentumBasisLabel momentumDim

/-- The spin multiplicity is `2s+1`, written with `twiceSpin = 2s`. -/
def spinMultiplicity (twiceSpin : Nat) : Nat :=
  twiceSpin + 1

/-- The finite product basis has dimension
`(2s+1) * chargeDim * momentumDim`. -/
lemma spinChargeMomentumHilbertBasis_card
    (twiceSpin chargeDim momentumDim : Nat) :
    Fintype.card (SpinChargeMomentumHilbertBasis twiceSpin chargeDim momentumDim)
      = spinMultiplicity twiceSpin * chargeDim * momentumDim := by
  simp [SpinChargeMomentumHilbertBasis, SpinMultipletLabel, ChargeMultipletLabel,
    MomentumBasisLabel, spinMultiplicity, Nat.mul_assoc]

/-- A spin-`1/2` charge doublet has `4 * momentumDim` finite product labels. -/
lemma spinHalf_chargeDoublet_hilbertBasis_card (momentumDim : Nat) :
    Fintype.card (SpinChargeMomentumHilbertBasis 1 2 momentumDim) =
      4 * momentumDim := by
  rw [spinChargeMomentumHilbertBasis_card]
  simp [spinMultiplicity]

/-- The spin multiplicity generated by an `SL(2,C)` label is
`|k-r|+1`. -/
def representationSpinMultiplicity (R : LorentzSpinorRepresentation) : Nat :=
  spinNumerator R + 1

/-- Chiral exchange preserves the generated spin multiplicity. -/
lemma representationSpinMultiplicity_chiral_swap (R : LorentzSpinorRepresentation) :
    representationSpinMultiplicity
        { leftFactors := R.rightFactors, rightFactors := R.leftFactors } =
      representationSpinMultiplicity R := by
  simp [representationSpinMultiplicity, spinNumerator_chiral_swap]

/-- The finite product label count for the spin multiplet generated by an
`SL(2,C)` representation. -/
lemma representationSpinChargeMomentumHilbertBasis_card
    (R : LorentzSpinorRepresentation) (chargeDim momentumDim : Nat) :
    Fintype.card
        (SpinChargeMomentumHilbertBasis (spinNumerator R) chargeDim momentumDim)
      = representationSpinMultiplicity R * chargeDim * momentumDim := by
  rw [spinChargeMomentumHilbertBasis_card]
  rfl

/-! ## A.7.1. Electron and Proton Spin-Doublet Chains -/

/-- The left chiral electron spinor label `(1/2,0)`, written with doubled
spin labels. -/
def electronLeftSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 1, rightFactors := 0 }

/-- The right chiral electron spinor label `(0,1/2)`, written with doubled
spin labels. -/
def electronRightSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 0, rightFactors := 1 }

/-- The proton-chain label `(59/2,29)` used in the paper. -/
def protonLeftSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 59, rightFactors := 58 }

/-- The conjugate proton-chain label `(29,59/2)` used in the paper. -/
def protonRightSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 58, rightFactors := 59 }

/-- The electron doublet has spin numerator one, i.e. spin `1/2`. -/
lemma electronLeftSpinorChain_spinNumerator :
    spinNumerator electronLeftSpinorChain = 1 := by
  rfl

/-- The conjugate electron doublet has the same spin numerator. -/
lemma electronRightSpinorChain_spinNumerator :
    spinNumerator electronRightSpinorChain = 1 := by
  rfl

/-- The proton chain also has spin numerator one, hence belongs to a
spin-`1/2` line. -/
lemma protonLeftSpinorChain_spinNumerator :
    spinNumerator protonLeftSpinorChain = 1 := by
  rfl

/-- The conjugate proton chain has the same spin numerator. -/
lemma protonRightSpinorChain_spinNumerator :
    spinNumerator protonRightSpinorChain = 1 := by
  rfl

/-- The electron left-chain representation degree is `2`. -/
lemma electronLeftSpinorChain_degree :
    sl2cRepresentationDegree electronLeftSpinorChain = 2 := by
  rfl

/-- The proton chain has degree `60 * 59 = 3540`, matching the paper's
dimension count. -/
lemma protonLeftSpinorChain_degree :
    sl2cRepresentationDegree protonLeftSpinorChain = 3540 := by
  rfl

/-- Both electron chiral labels generate the same mass level. -/
lemma electronSpinorChain_massLevel_chiral_pair (mu0 : Rat) :
    spinMassLevel mu0 electronRightSpinorChain =
      spinMassLevel mu0 electronLeftSpinorChain := by
  unfold spinMassLevel electronRightSpinorChain electronLeftSpinorChain
  ring

/-- Both proton chiral labels generate the same mass level. -/
lemma protonSpinorChain_massLevel_chiral_pair (mu0 : Rat) :
    spinMassLevel mu0 protonRightSpinorChain =
      spinMassLevel mu0 protonLeftSpinorChain := by
  unfold spinMassLevel protonRightSpinorChain protonLeftSpinorChain
  ring

/-- In the MGY normalization used here, the proton chain has exact mass-level
ratio `1770` relative to the fundamental electron chain. -/
lemma protonSpinorChain_massLevel_eq_1770_mul_electron (mu0 : Rat) :
    spinMassLevel mu0 protonLeftSpinorChain =
      1770 * spinMassLevel mu0 electronLeftSpinorChain := by
  unfold spinMassLevel protonLeftSpinorChain electronLeftSpinorChain
  ring

/-- The denominator-free MGY form gives `4 m_p = 3540 mu0` for the proton
chain. -/
lemma four_mul_protonSpinorChain_massLevel (mu0 : Rat) :
    4 * spinMassLevel mu0 protonLeftSpinorChain = 3540 * mu0 := by
  rw [four_mul_spinMassLevel]
  norm_num [protonLeftSpinorChain]
  ring

/-- The denominator-free MGY form gives `4 m_e = 2 mu0` for the fundamental
electron chain. -/
lemma four_mul_electronSpinorChain_massLevel (mu0 : Rat) :
    4 * spinMassLevel mu0 electronLeftSpinorChain = 2 * mu0 := by
  rw [four_mul_spinMassLevel]
  norm_num [electronLeftSpinorChain]
  ring

/-! ## A.7.2. Octet Spinor Assignments -/

/-- The `Sigma` triplet label `tau_(67/2,33)` from the fermion octet. -/
def sigmaTripletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 67, rightFactors := 66 }

/-- The `Xi` doublet label `tau_(71/2,35)` from the fermion octet. -/
def xiDoubletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 71, rightFactors := 70 }

/-- The `Lambda` singlet label `tau_(65/2,32)` from the fermion octet. -/
def lambdaSingletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 65, rightFactors := 64 }

/-- The pion triplet label `tau_(11,11)` from the pseudoscalar meson octet. -/
def pionTripletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 22, rightFactors := 22 }

/-- The kaon doublet label `tau_(43/2,43/2)` from the pseudoscalar meson
octet. -/
def kaonDoubletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 43, rightFactors := 43 }

/-- The eta singlet label `tau_(45/2,45/2)` from the pseudoscalar meson
octet. -/
def etaSingletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 45, rightFactors := 45 }

/-- The rho triplet label `tau_(55/2,53/2)` from the vector meson octet. -/
def rhoTripletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 55, rightFactors := 53 }

/-- The vector-kaon doublet label `tau_(59/2,57/2)` from the vector meson
octet. -/
def vectorKaonDoubletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 59, rightFactors := 57 }

/-- The phi singlet label `tau_(28,27)` from the vector meson octet, written
with doubled spin labels as `(56,54)`. -/
def phiSingletSpinorChain : LorentzSpinorRepresentation :=
  { leftFactors := 56, rightFactors := 54 }

/-- The four fermion-octet charge multiplet labels all lie on the spin-`1/2`
line. -/
lemma fermionOctetSpinorChains_spinHalf :
    spinNumerator sigmaTripletSpinorChain = 1
      ∧ spinNumerator protonLeftSpinorChain = 1
      ∧ spinNumerator xiDoubletSpinorChain = 1
      ∧ spinNumerator lambdaSingletSpinorChain = 1 := by
  decide

/-- The checked representation degrees for the fermion-octet charge
multiplet labels. -/
lemma fermionOctetSpinorChains_degrees :
    sl2cRepresentationDegree sigmaTripletSpinorChain = 4556
      ∧ sl2cRepresentationDegree protonLeftSpinorChain = 3540
      ∧ sl2cRepresentationDegree xiDoubletSpinorChain = 5112
      ∧ sl2cRepresentationDegree lambdaSingletSpinorChain = 4290 := by
  decide

/-- The pseudoscalar-meson octet labels all lie on the spin-zero line. -/
lemma pseudoscalarOctetSpinorChains_spinZero :
    spinNumerator pionTripletSpinorChain = 0
      ∧ spinNumerator kaonDoubletSpinorChain = 0
      ∧ spinNumerator etaSingletSpinorChain = 0 := by
  decide

/-- The checked representation degrees for the pseudoscalar-meson octet
labels. -/
lemma pseudoscalarOctetSpinorChains_degrees :
    sl2cRepresentationDegree pionTripletSpinorChain = 529
      ∧ sl2cRepresentationDegree kaonDoubletSpinorChain = 1936
      ∧ sl2cRepresentationDegree etaSingletSpinorChain = 2116 := by
  decide

/-- The vector-meson octet labels all lie on the spin-one line. -/
lemma vectorOctetSpinorChains_spinOne :
    spinNumerator rhoTripletSpinorChain = 2
      ∧ spinNumerator vectorKaonDoubletSpinorChain = 2
      ∧ spinNumerator phiSingletSpinorChain = 2 := by
  decide

/-- The checked representation degrees for the vector-meson octet labels. -/
lemma vectorOctetSpinorChains_degrees :
    sl2cRepresentationDegree rhoTripletSpinorChain = 3024
      ∧ sl2cRepresentationDegree vectorKaonDoubletSpinorChain = 3480
      ∧ sl2cRepresentationDegree phiSingletSpinorChain = 3135 := by
  decide

/-- Spin-`1/2` RWE generators in the paper's normalization
`L_j = (c/2) sigma_j`. -/
noncomputable def spinHalfRWEGenerator (c : ℂ) (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (c / 2) • PauliMatrix.pauliMatrix (Sum.inr j)

/-- At `c = 2`, the spin-`1/2` RWE generators are exactly the canonical
Physlib Pauli matrices. -/
lemma spinHalfRWEGenerator_at_two_eq_pauli (j : Fin 3) :
    spinHalfRWEGenerator 2 j = PauliMatrix.pauliMatrix (Sum.inr j) := by
  simp [spinHalfRWEGenerator]

/-- The `sigma_1` generator squares to the identity at Pauli normalization. -/
lemma spinHalfRWEGenerator_one_sq :
    spinHalfRWEGenerator 2 0 * spinHalfRWEGenerator 2 0 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [spinHalfRWEGenerator_at_two_eq_pauli]
  exact PauliMatrix.pauliMatrix_mul_self (Sum.inr 0)

/-- The `sigma_2` generator squares to the identity at Pauli normalization. -/
lemma spinHalfRWEGenerator_two_sq :
    spinHalfRWEGenerator 2 1 * spinHalfRWEGenerator 2 1 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [spinHalfRWEGenerator_at_two_eq_pauli]
  exact PauliMatrix.pauliMatrix_mul_self (Sum.inr 1)

/-- The `sigma_3` generator squares to the identity at Pauli normalization. -/
lemma spinHalfRWEGenerator_three_sq :
    spinHalfRWEGenerator 2 2 * spinHalfRWEGenerator 2 2 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [spinHalfRWEGenerator_at_two_eq_pauli]
  exact PauliMatrix.pauliMatrix_mul_self (Sum.inr 2)

/-! ## A.7.3. Charge Doublets and Triplets -/

/-- Heisenberg charge-doublet eigenvalues: proton-like label has charge `1`,
neutron-like label has charge `0`. -/
def chargeDoubletEigenvalue (i : Fin 2) : Rat :=
  if (i : Nat) = 0 then 1 else 0

/-- The diagonal charge operator on the Heisenberg charge doublet. -/
def chargeDoubletOperator : Matrix (Fin 2) (Fin 2) Rat :=
  Matrix.diagonal chargeDoubletEigenvalue

/-- The first charge-doublet basis vector has charge `1`. -/
@[simp] lemma chargeDoubletEigenvalue_zero :
    chargeDoubletEigenvalue 0 = 1 := by
  norm_num [chargeDoubletEigenvalue]

/-- The second charge-doublet basis vector has charge `0`. -/
@[simp] lemma chargeDoubletEigenvalue_one :
    chargeDoubletEigenvalue 1 = 0 := by
  norm_num [chargeDoubletEigenvalue]

/-- The doublet charge operator has diagonal entry `1` on the first basis
state. -/
lemma chargeDoubletOperator_zero_zero :
    chargeDoubletOperator 0 0 = 1 := by
  simp [chargeDoubletOperator]

/-- The doublet charge operator has diagonal entry `0` on the second basis
state. -/
lemma chargeDoubletOperator_one_one :
    chargeDoubletOperator 1 1 = 0 := by
  simp [chargeDoubletOperator]

/-- The doublet charge operator is diagonal. -/
lemma chargeDoubletOperator_offDiagonal {i j : Fin 2} (h : i ≠ j) :
    chargeDoubletOperator i j = 0 := by
  simp [chargeDoubletOperator, h]

/-- Kemmer charge-triplet eigenvalues `1,0,-1`. -/
def chargeTripletEigenvalue (i : Fin 3) : Rat :=
  if (i : Nat) = 0 then 1 else if (i : Nat) = 1 then 0 else -1

/-- The diagonal charge operator on a Kemmer charge triplet. -/
def chargeTripletOperator : Matrix (Fin 3) (Fin 3) Rat :=
  Matrix.diagonal chargeTripletEigenvalue

/-- The first charge-triplet basis vector has charge `1`. -/
@[simp] lemma chargeTripletEigenvalue_zero :
    chargeTripletEigenvalue 0 = 1 := by
  norm_num [chargeTripletEigenvalue]

/-- The second charge-triplet basis vector has charge `0`. -/
@[simp] lemma chargeTripletEigenvalue_one :
    chargeTripletEigenvalue 1 = 0 := by
  norm_num [chargeTripletEigenvalue]

/-- The third charge-triplet basis vector has charge `-1`. -/
@[simp] lemma chargeTripletEigenvalue_two :
    chargeTripletEigenvalue 2 = -1 := by
  norm_num [chargeTripletEigenvalue]

/-- The triplet charge operator has diagonal entries `1,0,-1`. -/
lemma chargeTripletOperator_diagonal_values :
    chargeTripletOperator 0 0 = 1
      ∧ chargeTripletOperator 1 1 = 0
      ∧ chargeTripletOperator 2 2 = -1 := by
  simp [chargeTripletOperator]

/-- The triplet charge operator is diagonal. -/
lemma chargeTripletOperator_offDiagonal {i j : Fin 3} (h : i ≠ j) :
    chargeTripletOperator i j = 0 := by
  simp [chargeTripletOperator, h]

/-- The charge triplet is traceless: its three charge eigenvalues add to zero. -/
lemma chargeTripletEigenvalue_sum_zero :
    ∑ i : Fin 3, chargeTripletEigenvalue i = 0 := by
  rw [Fin.sum_univ_three]
  norm_num

/-! ## A.8. Complex Momentum as the Energy Kernel -/

/-- The paper's complex-momentum eigenvalue attached to the spinor label
`tau_(k/2,r/2)`: real part is the basic spin-mass level, imaginary part is an
entropic/damping level proportional to the generalized spin. -/
def complexMomentumEigenvalue (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) : ℂ :=
  (spinMassLevel mu0 R : ℂ) + Complex.I * ((sigma * spinValue R : Rat) : ℂ)

/-- The real part of the complex-momentum eigenvalue is the basic spin-mass
level generated by the `SL(2,C)` representation label. -/
lemma complexMomentumEigenvalue_re (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) :
    (complexMomentumEigenvalue mu0 sigma R).re = ((spinMassLevel mu0 R : Rat) : ℝ) := by
  simp [complexMomentumEigenvalue]

/-- The imaginary part of the complex-momentum eigenvalue is the chosen
spin-dependent damping level. -/
lemma complexMomentumEigenvalue_im (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) :
    (complexMomentumEigenvalue mu0 sigma R).im = ((sigma * spinValue R : Rat) : ℝ) := by
  simp [complexMomentumEigenvalue]

/-- With zero damping coefficient, complex momentum reduces to the real
spin-mass level. -/
lemma complexMomentumEigenvalue_zero_imaginary (mu0 : Rat) (R : LorentzSpinorRepresentation) :
    complexMomentumEigenvalue mu0 0 R = (spinMassLevel mu0 R : ℂ) := by
  apply Complex.ext <;> simp [complexMomentumEigenvalue]

/-- On the self-conjugate spin-zero line `(k,k)`, the spin-dependent imaginary
part of the complex momentum vanishes. -/
lemma complexMomentumEigenvalue_im_self_conjugate (mu0 sigma : Rat) (k : Nat) :
    (complexMomentumEigenvalue mu0 sigma { leftFactors := k, rightFactors := k }).im = 0 := by
  simp [complexMomentumEigenvalue_im, spinValue, spinNumerator_self_conjugate_zero]

/-- Chiral exchange of the `SL(2,C)` label leaves the complex-momentum
eigenvalue unchanged. -/
lemma complexMomentumEigenvalue_chiral_swap (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) :
    complexMomentumEigenvalue mu0 sigma
        { leftFactors := R.rightFactors, rightFactors := R.leftFactors } =
      complexMomentumEigenvalue mu0 sigma R := by
  apply Complex.ext
  · simp [complexMomentumEigenvalue_re, spinMassLevel_chiral_swap]
  · simp [complexMomentumEigenvalue_im, spinValue, spinNumerator_chiral_swap]

/-- A diagonal step in the interlocking spin chain preserves generalized spin
but increases the representation degree. This is the formal version of the
paper's point that particles can have the same spin but sit at different
`SL(2,C)` representation levels. -/
lemma diagonal_step_same_spin_higher_degree (k r : Nat) :
    spinNumerator { leftFactors := k + 1, rightFactors := r + 1 } =
        spinNumerator { leftFactors := k, rightFactors := r }
      ∧ sl2cRepresentationDegree { leftFactors := k, rightFactors := r } <
        sl2cRepresentationDegree { leftFactors := k + 1, rightFactors := r + 1 } := by
  constructor
  · exact spinNumerator_diagonal_step k r
  · unfold sl2cRepresentationDegree
    nlinarith

/-- The complex-momentum spectrum generated by a finite list of spinor
representations. -/
def complexMomentumSpectrum {N : Nat} (mu0 sigma : Rat)
    (reps : Fin N → LorentzSpinorRepresentation) : Fin N → ℂ :=
  fun i => complexMomentumEigenvalue mu0 sigma (reps i)

/-- The real component of the generated complex-momentum spectrum is the basic
spin-mass level for the corresponding representation. -/
lemma complexMomentumSpectrum_re {N : Nat} (mu0 sigma : Rat)
    (reps : Fin N → LorentzSpinorRepresentation) (i : Fin N) :
    (complexMomentumSpectrum mu0 sigma reps i).re =
      ((spinMassLevel mu0 (reps i) : Rat) : ℝ) :=
  complexMomentumEigenvalue_re mu0 sigma (reps i)

/-- The paper's average basic mass level over the charge multiplets of an
`SU(3)` supermultiplet. -/
def averageSpinMassLevel {N : Nat} (mu0 : Rat) (reps : Fin N → LorentzSpinorRepresentation) : Rat :=
  (∑ i, spinMassLevel mu0 (reps i)) / (N : Rat)

/-- For one charge multiplet, the average basic mass is the single generated
spin-mass level. -/
lemma averageSpinMassLevel_one (mu0 : Rat) (R : LorentzSpinorRepresentation) :
    averageSpinMassLevel mu0 (fun _ : Fin 1 => R) = spinMassLevel mu0 R := by
  simp [averageSpinMassLevel]

/-- The average basic mass is the average real part of the generated
complex-momentum spectrum. -/
lemma averageSpinMassLevel_eq_complexMomentumSpectrum_re {N : Nat} (mu0 sigma : Rat)
    (reps : Fin N → LorentzSpinorRepresentation) :
    ((averageSpinMassLevel mu0 reps : Rat) : ℝ)
      = (∑ i, (complexMomentumSpectrum mu0 sigma reps i).re) / (N : ℝ) := by
  simp [averageSpinMassLevel, complexMomentumSpectrum, complexMomentumEigenvalue_re]

/-- The complex-momentum eigenvalue is the existing complex Dirac/Weyl mass
carrier with real part equal to the generated spin-mass level. -/
lemma complexMomentumEigenvalue_eq_complexFermionMass
    (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) :
    complexMomentumEigenvalue mu0 sigma R =
      complexFermionMass ((spinMassLevel mu0 R : Rat) : ℝ)
        ((sigma * spinValue R : Rat) : ℝ) := by
  apply Complex.ext <;> simp [complexMomentumEigenvalue_re, complexMomentumEigenvalue_im,
    complexFermionMass_re, complexFermionMass_im]

/-- Real part of the complex-momentum mass shell: the existing Dirac complex
mass-square identity applied to the spinor-generated energy level. -/
lemma complexMomentumEigenvalue_sq_re (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) :
    ((complexMomentumEigenvalue mu0 sigma R) ^ 2).re =
      ((spinMassLevel mu0 R : Rat) : ℝ) ^ 2 - ((sigma * spinValue R : Rat) : ℝ) ^ 2 := by
  rw [complexMomentumEigenvalue_eq_complexFermionMass,
    complexFermionMass_sq_re]

/-- Imaginary part of the complex-momentum mass shell: the existing Dirac
complex mass-square identity applied to the spinor-generated energy level. -/
lemma complexMomentumEigenvalue_sq_im (mu0 sigma : Rat) (R : LorentzSpinorRepresentation) :
    ((complexMomentumEigenvalue mu0 sigma R) ^ 2).im =
      2 * ((spinMassLevel mu0 R : Rat) : ℝ) * ((sigma * spinValue R : Rat) : ℝ) := by
  rw [complexMomentumEigenvalue_eq_complexFermionMass,
    complexFermionMass_sq_im]

/-- The Levi-Civita/Nagao-Nielsen complex momentum density realizes the
spinor-generated complex-momentum eigenvalue when its real and entropic
momentum-density components match the generated levels. -/
lemma complexMomentumDensity_realizes_complexMomentumEigenvalue {ι : Type*} [Fintype ι]
    (T S : Matrix ι ι ℝ) (u : ι → ℝ) (nu : ι)
    (mu0 sigma : Rat) (R : LorentzSpinorRepresentation)
    (hRe : relMomentumDensity T u nu = ((spinMassLevel mu0 R : Rat) : ℝ))
    (hIm : entropicMomentumDensity S u nu = ((sigma * spinValue R : Rat) : ℝ)) :
    complexMomentumDensity T S u nu = complexMomentumEigenvalue mu0 sigma R := by
  rw [complexMomentumDensity_apply]
  rw [show (T *ᵥ u) nu = relMomentumDensity T u nu by rfl]
  rw [show (S *ᵥ u) nu = entropicMomentumDensity S u nu by rfl]
  rw [hRe, hIm]
  apply Complex.ext <;> simp [complexMomentumEigenvalue]

/-! ## A.9. Charged Spin, CPT, and Weyl-Cartan Dilatonic Charge -/

/-- A charged spin representation: an `SL(2,C)` spinor label together with
an electric charge and a Weyl-Cartan dilatonic charge. -/
structure ChargedSpinRepresentation where
  /-- The Lorentz spinor representation label `tau_(k/2,r/2)`. -/
  spinRep : LorentzSpinorRepresentation
  /-- Electric charge, normalized in the same rational units used in the
  particle-zoo files. -/
  electricCharge : Rat
  /-- Weyl-Cartan dilatonic charge, the charge coupled to
  `WeylCartanDilatonicCharge.weylForce`. -/
  dilatonicCharge : Rat
deriving DecidableEq, Repr

/-- The real spin magnitude associated to a charged spin representation. -/
def chargedSpinMagnitude (X : ChargedSpinRepresentation) : ℝ :=
  ((spinValue X.spinRep : Rat) : ℝ)

/-- CPT conjugation of a charged spin representation: exchange dotted and
undotted spinor factors and reverse both electric and dilatonic charges. -/
def chargedSpinCPTConjugate (X : ChargedSpinRepresentation) : ChargedSpinRepresentation :=
  { spinRep :=
      { leftFactors := X.spinRep.rightFactors, rightFactors := X.spinRep.leftFactors },
    electricCharge := -X.electricCharge,
    dilatonicCharge := -X.dilatonicCharge }

/-- CPT conjugation is an involution on charged spin representations. -/
lemma chargedSpinCPTConjugate_involutive (X : ChargedSpinRepresentation) :
    chargedSpinCPTConjugate (chargedSpinCPTConjugate X) = X := by
  rcases X with ⟨⟨leftFactors, rightFactors⟩, electricCharge, dilatonicCharge⟩
  simp [chargedSpinCPTConjugate]

/-- CPT preserves the generalized spin of the spinor representation. -/
lemma chargedSpinMagnitude_cptConjugate (X : ChargedSpinRepresentation) :
    chargedSpinMagnitude (chargedSpinCPTConjugate X) = chargedSpinMagnitude X := by
  simp [chargedSpinMagnitude, chargedSpinCPTConjugate, spinValue_chiral_swap]

/-- CPT preserves the spin-mass level because the chiral swap preserves
`((k+1)/2)*((r+1)/2)`. -/
lemma spinMassLevel_cptConjugate (mu0 : Rat) (X : ChargedSpinRepresentation) :
    spinMassLevel mu0 (chargedSpinCPTConjugate X).spinRep =
      spinMassLevel mu0 X.spinRep := by
  simp [chargedSpinCPTConjugate, spinMassLevel_chiral_swap]

/-- CPT reverses electric charge in the charged spin representation. -/
lemma electricCharge_cptConjugate (X : ChargedSpinRepresentation) :
    (chargedSpinCPTConjugate X).electricCharge = -X.electricCharge := by
  rfl

/-- CPT reverses the Weyl-Cartan dilatonic charge. -/
lemma dilatonicCharge_cptConjugate (X : ChargedSpinRepresentation) :
    (chargedSpinCPTConjugate X).dilatonicCharge = -X.dilatonicCharge := by
  rfl

/-- The Mathisson spin-curvature force attached to a charged spin
representation, reusing `WeylCartanDilatonicCharge.mathissonForce`. -/
noncomputable def chargedSpinMathissonForce (X : ChargedSpinRepresentation)
    (curvature : ℝ) : ℝ :=
  mathissonForce (chargedSpinMagnitude X) curvature

/-- The Weyl-Cartan force attached to the dilatonic charge of a charged spin
representation, reusing `WeylCartanDilatonicCharge.weylForce`. -/
noncomputable def chargedSpinWeylForce (X : ChargedSpinRepresentation)
    (fieldStrength : ℝ) : ℝ :=
  weylForce ((X.dilatonicCharge : Rat) : ℝ) fieldStrength

/-- CPT preserves the Mathisson spin-curvature force because it preserves spin
magnitude. -/
lemma chargedSpinMathissonForce_cptConjugate (X : ChargedSpinRepresentation)
    (curvature : ℝ) :
    chargedSpinMathissonForce (chargedSpinCPTConjugate X) curvature =
      chargedSpinMathissonForce X curvature := by
  simp [chargedSpinMathissonForce, chargedSpinMagnitude_cptConjugate]

/-- CPT reverses the Weyl-Cartan force through the reversed dilatonic charge. -/
lemma chargedSpinWeylForce_cptConjugate (X : ChargedSpinRepresentation)
    (fieldStrength : ℝ) :
    chargedSpinWeylForce (chargedSpinCPTConjugate X) fieldStrength =
      -chargedSpinWeylForce X fieldStrength := by
  simp [chargedSpinWeylForce, chargedSpinCPTConjugate, weylForce]

/-- The charged-spin test-particle force using the existing Weyl-Cartan
decomposition: geodesic, Mathisson spin-curvature, torsion, and Weyl
dilatonic pieces. -/
noncomputable def chargedSpinTestParticleForce (geodesic torsion curvature fieldStrength : ℝ)
    (X : ChargedSpinRepresentation) : ℝ :=
  testParticleForce geodesic (chargedSpinMathissonForce X curvature) torsion
    (chargedSpinWeylForce X fieldStrength)

/-- The charged-spin force and its CPT conjugate differ only by the sign of the
Weyl-Cartan dilatonic term when the background fields are held fixed. -/
lemma chargedSpinTestParticleForce_cptConjugate (geodesic torsion curvature fieldStrength : ℝ)
    (X : ChargedSpinRepresentation) :
    chargedSpinTestParticleForce geodesic torsion curvature fieldStrength
        (chargedSpinCPTConjugate X)
      = testParticleForce geodesic (chargedSpinMathissonForce X curvature) torsion
          (-chargedSpinWeylForce X fieldStrength) := by
  simp [chargedSpinTestParticleForce, chargedSpinMathissonForce_cptConjugate,
    chargedSpinWeylForce_cptConjugate]

/-- The fermionic CPT operator has projective order four: since `CPT² = -1`,
four applications act as the identity on Dirac spinors. -/
lemma cpt_projective_order_four (ψ : Fin 4 → ℂ) :
    cpt (cpt (cpt (cpt ψ))) = ψ := by
  rw [cpt_sq (cpt (cpt ψ)), cpt_sq ψ, neg_neg]

/-- The charged-spin layer linked to the existing fermionic CPT operator and
Weyl-Cartan dilatonic-force sector. -/
def HasChargedSpinCPTDilatonicBridge : Prop :=
  (∀ X : ChargedSpinRepresentation,
      chargedSpinCPTConjugate (chargedSpinCPTConjugate X) = X)
    ∧ (∀ (mu0 : Rat) (X : ChargedSpinRepresentation),
      spinMassLevel mu0 (chargedSpinCPTConjugate X).spinRep =
        spinMassLevel mu0 X.spinRep)
    ∧ (∀ (X : ChargedSpinRepresentation) (fieldStrength : ℝ),
      chargedSpinWeylForce (chargedSpinCPTConjugate X) fieldStrength =
        -chargedSpinWeylForce X fieldStrength)
    ∧ (∀ ψ : Fin 4 → ℂ, cpt (cpt (cpt (cpt ψ))) = ψ)

/-- The charged-spin/CPT/dilatonic bridge is checked from existing spinor,
Dirac-CPT, and Weyl-Cartan lemmas. -/
lemma chargedSpinCPTDilatonicBridge_checked : HasChargedSpinCPTDilatonicBridge :=
  ⟨chargedSpinCPTConjugate_involutive, spinMassLevel_cptConjugate,
    chargedSpinWeylForce_cptConjugate, cpt_projective_order_four⟩

/-! ## A.10. `SU(3)` Admissibility and Octet Reduction -/

/-- Varlamov's `SU(3)` hadron-supermultiplet admissibility condition for
Dynkin labels `(p,q)`: `p-q = 0 mod 3`, expressed without integer
subtraction as `p mod 3 = q mod 3`. -/
def su3HadronAdmissible (p q : Nat) : Prop :=
  p % 3 = q % 3

/-- The adjoint/octet `(1,1)` is admissible. -/
lemma su3_octet_admissible : su3HadronAdmissible 1 1 := by
  norm_num [su3HadronAdmissible]

/-- The decuplet `(3,0)` is admissible. -/
lemma su3_decuplet_admissible : su3HadronAdmissible 3 0 := by
  norm_num [su3HadronAdmissible]

/-- The fundamental `(1,0)` is not an admissible hadron supermultiplet under
the `p-q = 0 mod 3` criterion. -/
lemma su3_fundamental_not_hadron_admissible :
    ¬ su3HadronAdmissible 1 0 := by
  norm_num [su3HadronAdmissible]

/-- Tensor-composition data for the quark-scheme space `C^{k,r}`:
`k` fundamental `C^3` factors and `r` antifundamental factors. -/
structure SU3TensorComposition where
  /-- Number of quark factors. -/
  quarkFactors : Nat
  /-- Number of antiquark factors. -/
  antiquarkFactors : Nat
deriving DecidableEq, Repr

/-- The tensor degree `k+r` of the `SU(3)` quark-scheme tensor space. -/
def su3TensorDegree (C : SU3TensorComposition) : Nat :=
  C.quarkFactors + C.antiquarkFactors

/-- The dimension `3^(k+r)` of the full tensor space before irreducible
projection. -/
def su3TensorDimension (C : SU3TensorComposition) : Nat :=
  3 ^ su3TensorDegree C

/-- The maximal doubled spin assigned by the quark-counting rule:
`2 s_max = k+r` when each constituent has spin `1/2`. -/
def su3MaximalSpinNumerator (C : SU3TensorComposition) : Nat :=
  su3TensorDegree C

/-- The maximal spin value `(k+r)/2` assigned by the quark-counting rule. -/
def su3MaximalSpinValue (C : SU3TensorComposition) : Rat :=
  (su3MaximalSpinNumerator C : Rat) / 2

/-- Fermion-like tensor degree: `k+r` is odd. -/
def SU3TensorFermionLike (C : SU3TensorComposition) : Prop :=
  su3TensorDegree C % 2 = 1

/-- Boson-like tensor degree: `k+r` is even. -/
def SU3TensorBosonLike (C : SU3TensorComposition) : Prop :=
  su3TensorDegree C % 2 = 0

/-- Matching the `SU(3)` tensor degree with the spinor tensor degree
`leftFactors + rightFactors`. -/
def SU3TensorMatchesSpinorDegree
    (C : SU3TensorComposition) (R : LorentzSpinorRepresentation) : Prop :=
  su3TensorDegree C = R.leftFactors + R.rightFactors

/-- Matching tensor degrees gives matching parity tests. -/
lemma su3TensorParity_eq_spinorTensorParity
    (C : SU3TensorComposition) (R : LorentzSpinorRepresentation)
    (h : SU3TensorMatchesSpinorDegree C R) :
    su3TensorDegree C % 2 = (R.leftFactors + R.rightFactors) % 2 := by
  rw [h]

/-- Matching tensor degrees rewrites the quark-scheme tensor-space dimension
as `3` raised to the spinor factor count. -/
lemma su3TensorDimension_eq_pow_spinorFactorCount
    (C : SU3TensorComposition) (R : LorentzSpinorRepresentation)
    (h : SU3TensorMatchesSpinorDegree C R) :
    su3TensorDimension C = 3 ^ Fintype.card (SpinorFactorLabel R) := by
  rw [su3TensorDimension, h, spinorFactorLabel_card]

/-- A single quark factor in the fundamental `SU(3)` tensor space. -/
def quarkFundamentalTensor : SU3TensorComposition :=
  { quarkFactors := 1, antiquarkFactors := 0 }

/-- A single antiquark factor in the antifundamental `SU(3)` tensor space. -/
def antiquarkFundamentalTensor : SU3TensorComposition :=
  { quarkFactors := 0, antiquarkFactors := 1 }

/-- A meson-type tensor composition: one quark and one antiquark. -/
def mesonTensorComposition : SU3TensorComposition :=
  { quarkFactors := 1, antiquarkFactors := 1 }

/-- A baryon-type tensor composition: three quarks. -/
def baryonTensorComposition : SU3TensorComposition :=
  { quarkFactors := 3, antiquarkFactors := 0 }

/-- The fundamental quark tensor space has dimension `3` and odd tensor
degree. -/
lemma quarkFundamentalTensor_data :
    su3TensorDimension quarkFundamentalTensor = 3
      ∧ SU3TensorFermionLike quarkFundamentalTensor
      ∧ su3MaximalSpinNumerator quarkFundamentalTensor = 1 := by
  norm_num [su3TensorDimension, SU3TensorFermionLike, su3MaximalSpinNumerator,
    su3TensorDegree, quarkFundamentalTensor]

/-- The antifundamental antiquark tensor space has dimension `3` and odd
tensor degree. -/
lemma antiquarkFundamentalTensor_data :
    su3TensorDimension antiquarkFundamentalTensor = 3
      ∧ SU3TensorFermionLike antiquarkFundamentalTensor
      ∧ su3MaximalSpinNumerator antiquarkFundamentalTensor = 1 := by
  norm_num [su3TensorDimension, SU3TensorFermionLike, su3MaximalSpinNumerator,
    su3TensorDegree, antiquarkFundamentalTensor]

/-- A meson-type tensor space has dimension `9`, even tensor degree, and
maximal spin numerator `2`. -/
lemma mesonTensorComposition_data :
    su3TensorDimension mesonTensorComposition = 9
      ∧ SU3TensorBosonLike mesonTensorComposition
      ∧ su3MaximalSpinNumerator mesonTensorComposition = 2 := by
  norm_num [su3TensorDimension, SU3TensorBosonLike, su3MaximalSpinNumerator,
    su3TensorDegree, mesonTensorComposition]

/-- A baryon-type tensor space has dimension `27`, odd tensor degree, and
maximal spin numerator `3`. -/
lemma baryonTensorComposition_data :
    su3TensorDimension baryonTensorComposition = 27
      ∧ SU3TensorFermionLike baryonTensorComposition
      ∧ su3MaximalSpinNumerator baryonTensorComposition = 3 := by
  norm_num [su3TensorDimension, SU3TensorFermionLike, su3MaximalSpinNumerator,
    su3TensorDegree, baryonTensorComposition]

/-- The octet dimension is supplied by the existing `SU(3)` Weyl formula. -/
lemma varlamov_octet_degree : weylDim3 1 1 = 8 :=
  weylDim3_adjoint

/-- `SU(3) -> SU(2)` octet bookkeeping used by the paper:
triplet, doublet, antidoublet, and singlet dimensions. -/
structure OctetToIsospinReduction where
  /-- The isospin triplet dimension. -/
  triplet : Nat
  /-- The first isospin doublet dimension. -/
  doublet : Nat
  /-- The conjugate isospin doublet dimension. -/
  antiDoublet : Nat
  /-- The singlet dimension. -/
  singlet : Nat
deriving DecidableEq, Repr

/-- The standard octet reduction `3 + 2 + 2 + 1`. -/
def octetToIsospinReduction : OctetToIsospinReduction :=
  { triplet := 3, doublet := 2, antiDoublet := 2, singlet := 1 }

/-- The octet reduction dimensions add to the existing Weyl dimension
`dim(1,1)=8`. -/
lemma octetToIsospinReduction_card :
    octetToIsospinReduction.triplet
      + octetToIsospinReduction.doublet
      + octetToIsospinReduction.antiDoublet
      + octetToIsospinReduction.singlet = weylDim3 1 1 := by
  rw [weylDim3_adjoint]
  rfl

/-- A finite `SU(3) -> SU(2)` branch record: source Dynkin labels and the
dimensions of the resulting `SU(2)` isospin multiplets. -/
structure SU3ToSU2Branch where
  /-- Source `SU(3)` Dynkin label `p`. -/
  sourceP : Nat
  /-- Source `SU(3)` Dynkin label `q`. -/
  sourceQ : Nat
  /-- Dimensions of the `SU(2)` multiplets after restriction. -/
  multipletDims : List Nat
deriving DecidableEq, Repr

/-- The total dimension of an `SU(3) -> SU(2)` branch record. -/
def branchDimensionSum (B : SU3ToSU2Branch) : Nat :=
  B.multipletDims.sum

/-- The standard octet restriction dimensions `8 -> 3 + 2 + 2 + 1`. -/
def su3OctetToSU2Branch : SU3ToSU2Branch :=
  { sourceP := 1, sourceQ := 1, multipletDims := [3, 2, 2, 1] }

/-- The decuplet restriction dimensions `10 -> 4 + 3 + 2 + 1`. -/
def su3DecupletToSU2Branch : SU3ToSU2Branch :=
  { sourceP := 3, sourceQ := 0, multipletDims := [4, 3, 2, 1] }

/-- The fundamental restriction dimensions `3 -> 2 + 1`. -/
def su3FundamentalToSU2Branch : SU3ToSU2Branch :=
  { sourceP := 1, sourceQ := 0, multipletDims := [2, 1] }

/-- The octet branch dimension sum agrees with the `SU(3)` Weyl dimension. -/
lemma su3OctetToSU2Branch_dimension :
    branchDimensionSum su3OctetToSU2Branch =
      weylDim3 su3OctetToSU2Branch.sourceP su3OctetToSU2Branch.sourceQ := by
  norm_num [branchDimensionSum, su3OctetToSU2Branch, weylDim3]

/-- The decuplet branch dimension sum agrees with the `SU(3)` Weyl dimension. -/
lemma su3DecupletToSU2Branch_dimension :
    branchDimensionSum su3DecupletToSU2Branch =
      weylDim3 su3DecupletToSU2Branch.sourceP su3DecupletToSU2Branch.sourceQ := by
  norm_num [branchDimensionSum, su3DecupletToSU2Branch, weylDim3]

/-- The fundamental branch dimension sum agrees with the `SU(3)` Weyl
dimension. -/
lemma su3FundamentalToSU2Branch_dimension :
    branchDimensionSum su3FundamentalToSU2Branch =
      weylDim3 su3FundamentalToSU2Branch.sourceP su3FundamentalToSU2Branch.sourceQ := by
  norm_num [branchDimensionSum, su3FundamentalToSU2Branch, weylDim3]

/-- The octet and decuplet branch records satisfy Varlamov's hadron
admissibility condition. -/
lemma su3_hadron_branch_records_admissible :
    su3HadronAdmissible su3OctetToSU2Branch.sourceP su3OctetToSU2Branch.sourceQ
      ∧ su3HadronAdmissible su3DecupletToSU2Branch.sourceP
        su3DecupletToSU2Branch.sourceQ := by
  constructor
  · exact su3_octet_admissible
  · exact su3_decuplet_admissible

/-! ## A.10.1. Wigner/`SU(3)` Product Labels -/

/-- A finite bridge label between Wigner's orbit classification and an
internal `SU(3)` supermultiplet.  The `internalDim` field is the selected
finite dimension of the `SU(3)` multiplet. -/
structure WignerSU3ParticleLabel where
  /-- Wigner orbit class of the momentum representation. -/
  orbit : WignerOrbitKind
  /-- Lorentz spinor representation label. -/
  spinRep : LorentzSpinorRepresentation
  /-- First Dynkin label of the internal `SU(3)` representation. -/
  dynkinP : Nat
  /-- Second Dynkin label of the internal `SU(3)` representation. -/
  dynkinQ : Nat
  /-- Finite internal multiplet dimension. -/
  internalDim : Nat
deriving DecidableEq, Repr

/-- The finite product label set
`H^S ⊗ H^internal ⊗ H_momentum` attached to a Wigner/`SU(3)` label. -/
abbrev WignerSU3ProductBasis
    (L : WignerSU3ParticleLabel) (momentumDim : Nat) : Type :=
  SpinChargeMomentumHilbertBasis (spinNumerator L.spinRep) L.internalDim momentumDim

/-- The Wigner/`SU(3)` product-basis dimension factors into spin,
internal-multiplet, and momentum dimensions. -/
lemma wignerSU3ProductBasis_card
    (L : WignerSU3ParticleLabel) (momentumDim : Nat) :
    Fintype.card (WignerSU3ProductBasis L momentumDim) =
      representationSpinMultiplicity L.spinRep * L.internalDim * momentumDim := by
  rw [representationSpinChargeMomentumHilbertBasis_card]

/-- The hadron-admissibility predicate for a Wigner/`SU(3)` bridge label. -/
def WignerSU3ParticleLabel.HadronAdmissible (L : WignerSU3ParticleLabel) : Prop :=
  su3HadronAdmissible L.dynkinP L.dynkinQ

/-- The baryon octet as a Wigner massive spin-`1/2` label linked to the
`SU(3)` adjoint/octet. -/
def baryonOctetWignerSU3Label : WignerSU3ParticleLabel :=
  { orbit := WignerOrbitKind.positiveMassive,
    spinRep := protonLeftSpinorChain,
    dynkinP := 1,
    dynkinQ := 1,
    internalDim := weylDim3 1 1 }

/-- The pseudoscalar meson octet as a Wigner massive spin-`0` label linked to
the `SU(3)` adjoint/octet. -/
def pseudoscalarOctetWignerSU3Label : WignerSU3ParticleLabel :=
  { orbit := WignerOrbitKind.positiveMassive,
    spinRep := pionTripletSpinorChain,
    dynkinP := 1,
    dynkinQ := 1,
    internalDim := weylDim3 1 1 }

/-- The vector meson octet as a Wigner massive spin-`1` label linked to the
`SU(3)` adjoint/octet. -/
def vectorOctetWignerSU3Label : WignerSU3ParticleLabel :=
  { orbit := WignerOrbitKind.positiveMassive,
    spinRep := rhoTripletSpinorChain,
    dynkinP := 1,
    dynkinQ := 1,
    internalDim := weylDim3 1 1 }

/-- The three octet bridge labels are all `SU(3)`-hadron admissible. -/
lemma octetWignerSU3Labels_admissible :
    baryonOctetWignerSU3Label.HadronAdmissible
      ∧ pseudoscalarOctetWignerSU3Label.HadronAdmissible
      ∧ vectorOctetWignerSU3Label.HadronAdmissible := by
  norm_num [WignerSU3ParticleLabel.HadronAdmissible, baryonOctetWignerSU3Label,
    pseudoscalarOctetWignerSU3Label, vectorOctetWignerSU3Label, su3HadronAdmissible]

/-- The baryon octet product basis has dimension `16 * momentumDim`:
spin multiplicity `2` times internal octet dimension `8`. -/
lemma baryonOctetWignerSU3ProductBasis_card (momentumDim : Nat) :
    Fintype.card (WignerSU3ProductBasis baryonOctetWignerSU3Label momentumDim) =
      16 * momentumDim := by
  rw [wignerSU3ProductBasis_card]
  simp [baryonOctetWignerSU3Label, representationSpinMultiplicity,
    protonLeftSpinorChain, spinNumerator, weylDim3_adjoint]

/-- The pseudoscalar octet product basis has dimension `8 * momentumDim`:
spin multiplicity `1` times internal octet dimension `8`. -/
lemma pseudoscalarOctetWignerSU3ProductBasis_card (momentumDim : Nat) :
    Fintype.card (WignerSU3ProductBasis pseudoscalarOctetWignerSU3Label momentumDim) =
      8 * momentumDim := by
  rw [wignerSU3ProductBasis_card]
  simp [pseudoscalarOctetWignerSU3Label, representationSpinMultiplicity,
    pionTripletSpinorChain, spinNumerator, weylDim3_adjoint]

/-- The vector octet product basis has dimension `24 * momentumDim`:
spin multiplicity `3` times internal octet dimension `8`. -/
lemma vectorOctetWignerSU3ProductBasis_card (momentumDim : Nat) :
    Fintype.card (WignerSU3ProductBasis vectorOctetWignerSU3Label momentumDim) =
      24 * momentumDim := by
  rw [wignerSU3ProductBasis_card]
  simp [vectorOctetWignerSU3Label, representationSpinMultiplicity,
    rhoTripletSpinorChain, spinNumerator, weylDim3_adjoint]

/-! ## A.11. Octet Spectrum Families and Diagonal Unitary Fields -/

/-- Finite record for the three octet families used in the paper's mass
analysis: the spin-`1/2` fermion octet `F`, the spin-zero boson octet `B0`,
and the spin-one boson octet `B1`. -/
structure OctetSpectrumFamily where
  /-- Twice the spin: `1` for `F`, `0` for `B0`, and `2` for `B1`. -/
  twiceSpin : Nat
  /-- Baryon number: `1` for the fermion octet and `0` for the boson octets. -/
  baryonNumber : Rat
  /-- The parity-square sign from the paper: `+1` for `F`, `-1` for `B0,B1`. -/
  paritySquare : Int
  /-- Whether the family has a separate antiparticle octet. -/
  hasAntiparticleCounterpart : Bool
  /-- The shared `SU(3) -> SU(2)` branch record. -/
  branch : SU3ToSU2Branch
deriving DecidableEq, Repr

/-- The fermion octet `F_{1/2}`: spin `1/2`, baryon number `1`, and
`P^2 = +1`. -/
def fermionHalfOctetFamily : OctetSpectrumFamily :=
  { twiceSpin := 1
    baryonNumber := 1
    paritySquare := 1
    hasAntiparticleCounterpart := true
    branch := su3OctetToSU2Branch }

/-- The boson octet `B0`: spin `0`, baryon number `0`, and `P^2 = -1`. -/
def scalarBosonOctetFamily : OctetSpectrumFamily :=
  { twiceSpin := 0
    baryonNumber := 0
    paritySquare := -1
    hasAntiparticleCounterpart := false
    branch := su3OctetToSU2Branch }

/-- The boson octet `B1`: spin `1`, baryon number `0`, and `P^2 = -1`. -/
def vectorBosonOctetFamily : OctetSpectrumFamily :=
  { twiceSpin := 2
    baryonNumber := 0
    paritySquare := -1
    hasAntiparticleCounterpart := false
    branch := su3OctetToSU2Branch }

/-- The fermion octet has the expected spin multiplicity `2`. -/
lemma fermionHalfOctet_spinMultiplicity :
    spinMultiplicity fermionHalfOctetFamily.twiceSpin = 2 := by
  rfl

/-- The scalar boson octet has the expected spin multiplicity `1`. -/
lemma scalarBosonOctet_spinMultiplicity :
    spinMultiplicity scalarBosonOctetFamily.twiceSpin = 1 := by
  rfl

/-- The vector boson octet has the expected spin multiplicity `3`. -/
lemma vectorBosonOctet_spinMultiplicity :
    spinMultiplicity vectorBosonOctetFamily.twiceSpin = 3 := by
  rfl

/-- The three spectrum families use the same octet branch dimension
`8 = 3+2+2+1`. -/
lemma octetSpectrumFamilies_share_su3_octet :
    branchDimensionSum fermionHalfOctetFamily.branch = weylDim3 1 1
      ∧ branchDimensionSum scalarBosonOctetFamily.branch = weylDim3 1 1
      ∧ branchDimensionSum vectorBosonOctetFamily.branch = weylDim3 1 1 := by
  constructor
  · norm_num [fermionHalfOctetFamily, branchDimensionSum, su3OctetToSU2Branch, weylDim3]
  · constructor
    · norm_num [scalarBosonOctetFamily, branchDimensionSum, su3OctetToSU2Branch, weylDim3]
    · norm_num [vectorBosonOctetFamily, branchDimensionSum, su3OctetToSU2Branch, weylDim3]

/-- `B0` and `B1` have the same baryon number and parity square, but different
spin. -/
lemma bosonOctets_same_baryon_parity_distinct_spin :
    scalarBosonOctetFamily.baryonNumber = vectorBosonOctetFamily.baryonNumber
      ∧ scalarBosonOctetFamily.paritySquare = vectorBosonOctetFamily.paritySquare
      ∧ scalarBosonOctetFamily.twiceSpin ≠ vectorBosonOctetFamily.twiceSpin := by
  constructor
  · rfl
  · constructor
    · rfl
    · decide

/-- The fermion octet is the family with a separate antiparticle counterpart in
this finite model. -/
lemma fermionOctet_has_antiparticle_counterpart :
    fermionHalfOctetFamily.hasAntiparticleCounterpart = true := by
  rfl

/-- Coherent-subspace label for the superselection data used in the paper:
spin, parity-square sign, and baryon number. -/
structure CoherentSubspaceLabel where
  /-- Twice the spin of the coherent subspace. -/
  twiceSpin : Nat
  /-- Parity-square sign assigned to the subspace. -/
  paritySquare : Int
  /-- Baryon number assigned to the subspace. -/
  baryonNumber : Rat
deriving DecidableEq, Repr

/-- Coherent-subspace label extracted from an octet spectrum family. -/
def octetCoherentSubspaceLabel (F : OctetSpectrumFamily) : CoherentSubspaceLabel :=
  { twiceSpin := F.twiceSpin
    paritySquare := F.paritySquare
    baryonNumber := F.baryonNumber }

/-- The fermion octet and its antiparticle octet agree in spin and parity but
have opposite baryon number. -/
lemma fermion_antifermion_octets_same_spin_parity_opposite_baryon :
    let antiF : OctetSpectrumFamily :=
      { fermionHalfOctetFamily with baryonNumber := -fermionHalfOctetFamily.baryonNumber }
    (octetCoherentSubspaceLabel antiF).twiceSpin =
        (octetCoherentSubspaceLabel fermionHalfOctetFamily).twiceSpin
      ∧ (octetCoherentSubspaceLabel antiF).paritySquare =
        (octetCoherentSubspaceLabel fermionHalfOctetFamily).paritySquare
      ∧ (octetCoherentSubspaceLabel antiF).baryonNumber =
        -(octetCoherentSubspaceLabel fermionHalfOctetFamily).baryonNumber := by
  simp [octetCoherentSubspaceLabel, fermionHalfOctetFamily]

/-- The two boson octets agree in baryon number and parity but belong to
different spin coherent subspaces. -/
lemma bosonOctets_same_baryon_parity_different_spin_subspaces :
    (octetCoherentSubspaceLabel scalarBosonOctetFamily).baryonNumber =
        (octetCoherentSubspaceLabel vectorBosonOctetFamily).baryonNumber
      ∧ (octetCoherentSubspaceLabel scalarBosonOctetFamily).paritySquare =
        (octetCoherentSubspaceLabel vectorBosonOctetFamily).paritySquare
      ∧ (octetCoherentSubspaceLabel scalarBosonOctetFamily).twiceSpin ≠
        (octetCoherentSubspaceLabel vectorBosonOctetFamily).twiceSpin := by
  constructor
  · rfl
  · constructor
    · rfl
    · decide

/-! ## A.11.1. Octet Basic Mass Averages -/

/-- The four charge-multiplet representatives for the baryon octet
`F_{1/2}`: `Σ`, `N`, `Ξ`, and `Λ`. -/
def baryonOctetChargeMultipletReps (i : Fin 4) : LorentzSpinorRepresentation :=
  if i = 0 then sigmaTripletSpinorChain
  else if i = 1 then protonLeftSpinorChain
  else if i = 2 then xiDoubletSpinorChain
  else lambdaSingletSpinorChain

/-- The four charge-multiplet representatives for the pseudoscalar meson
octet `B0`: `π`, `K1`, `K2`, and `η`. -/
def pseudoscalarOctetChargeMultipletReps (i : Fin 4) : LorentzSpinorRepresentation :=
  if i = 0 then pionTripletSpinorChain
  else if i = 1 then kaonDoubletSpinorChain
  else if i = 2 then kaonDoubletSpinorChain
  else etaSingletSpinorChain

/-- The four charge-multiplet representatives for the vector meson octet
`B1`: `ρ`, `K*1`, `K*2`, and `φ`. -/
def vectorOctetChargeMultipletReps (i : Fin 4) : LorentzSpinorRepresentation :=
  if i = 0 then rhoTripletSpinorChain
  else if i = 1 then vectorKaonDoubletSpinorChain
  else if i = 2 then vectorKaonDoubletSpinorChain
  else phiSingletSpinorChain

/-- The baryon-octet baseline `m0` is the average of its four basic spin-mass
levels. -/
lemma baryonOctetAverageSpinMassLevel_eq (mu0 : Rat) :
    averageSpinMassLevel mu0 baryonOctetChargeMultipletReps =
      (spinMassLevel mu0 sigmaTripletSpinorChain
        + spinMassLevel mu0 protonLeftSpinorChain
        + spinMassLevel mu0 xiDoubletSpinorChain
        + spinMassLevel mu0 lambdaSingletSpinorChain) / 4 := by
  rw [averageSpinMassLevel, Fin.sum_univ_four]
  simp [baryonOctetChargeMultipletReps]

/-- The pseudoscalar-octet baseline `m0` is the average of the `π`, two kaon,
and `η` basic spin-mass levels. -/
lemma pseudoscalarOctetAverageSpinMassLevel_eq (mu0 : Rat) :
    averageSpinMassLevel mu0 pseudoscalarOctetChargeMultipletReps =
      (spinMassLevel mu0 pionTripletSpinorChain
        + spinMassLevel mu0 kaonDoubletSpinorChain
        + spinMassLevel mu0 kaonDoubletSpinorChain
        + spinMassLevel mu0 etaSingletSpinorChain) / 4 := by
  rw [averageSpinMassLevel, Fin.sum_univ_four]
  simp [pseudoscalarOctetChargeMultipletReps]

/-- The vector-octet baseline `m0` is the average of the `ρ`, two vector-kaon,
and `φ` basic spin-mass levels. -/
lemma vectorOctetAverageSpinMassLevel_eq (mu0 : Rat) :
    averageSpinMassLevel mu0 vectorOctetChargeMultipletReps =
      (spinMassLevel mu0 rhoTripletSpinorChain
        + spinMassLevel mu0 vectorKaonDoubletSpinorChain
        + spinMassLevel mu0 vectorKaonDoubletSpinorChain
        + spinMassLevel mu0 phiSingletSpinorChain) / 4 := by
  rw [averageSpinMassLevel, Fin.sum_univ_four]
  simp [vectorOctetChargeMultipletReps]

/-- Matrix-unit part of Okubo's external basis.  This is `E_lower,upper` in
zero-based matrix coordinates. -/
def okuboMatrixUnit (upper lower : Fin 3) : Matrix (Fin 3) (Fin 3) Rat :=
  Matrix.single lower upper 1

/-- Matrix units satisfy the commutator relation
`[E_ki,E_ml] = delta_im E_kl - delta_lk E_mi`. -/
lemma okuboMatrixUnit_commutator (i k l m : Fin 3) :
    okuboMatrixUnit i k * okuboMatrixUnit l m
        - okuboMatrixUnit l m * okuboMatrixUnit i k =
      (if i = m then okuboMatrixUnit l k else 0)
        - if l = k then okuboMatrixUnit i m else 0 := by
  unfold okuboMatrixUnit
  by_cases him : i = m
  · subst m
    by_cases hlk : l = k
    · subst k
      simp
    · simp [hlk]
  · by_cases hlk : l = k
    · subst k
      simp [him]
    · simp [him, hlk]

/-- Okubo's external `su(3)` matrix units.  With zero-based indices this is
`A^upper_lower`: off diagonal entries are matrix units, while diagonal entries
are `E_ii - (1/3) I`. -/
def okuboOperator (upper lower : Fin 3) : Matrix (Fin 3) (Fin 3) Rat :=
  if upper = lower then
    okuboMatrixUnit upper lower - (1 / 3 : Rat) • (1 : Matrix (Fin 3) (Fin 3) Rat)
  else
    okuboMatrixUnit upper lower

/-- The three diagonal Okubo operators add to zero. -/
lemma okuboOperator_diagonal_sum_zero :
    okuboOperator 0 0 + okuboOperator 1 1 + okuboOperator 2 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [okuboOperator, okuboMatrixUnit, Matrix.single] <;> norm_num

/-- The traceless diagonal hypercharge field with entries
`(1/3, 1/3, -2/3)`. -/
def hyperchargeUnitaryFieldDiag (i : Fin 3) : Rat :=
  if (i : Nat) = 2 then -2 / 3 else 1 / 3

/-- The traceless diagonal charge field with entries `(2/3, -1/3, -1/3)`. -/
def chargeUnitaryFieldDiag (i : Fin 3) : Rat :=
  if (i : Nat) = 0 then 2 / 3 else -1 / 3

@[simp] lemma hyperchargeUnitaryFieldDiag_zero :
    hyperchargeUnitaryFieldDiag 0 = 1 / 3 := by
  norm_num [hyperchargeUnitaryFieldDiag]

@[simp] lemma hyperchargeUnitaryFieldDiag_one :
    hyperchargeUnitaryFieldDiag 1 = 1 / 3 := by
  norm_num [hyperchargeUnitaryFieldDiag]

@[simp] lemma hyperchargeUnitaryFieldDiag_two :
    hyperchargeUnitaryFieldDiag 2 = -2 / 3 := by
  norm_num [hyperchargeUnitaryFieldDiag]

@[simp] lemma chargeUnitaryFieldDiag_zero :
    chargeUnitaryFieldDiag 0 = 2 / 3 := by
  norm_num [chargeUnitaryFieldDiag]

@[simp] lemma chargeUnitaryFieldDiag_one :
    chargeUnitaryFieldDiag 1 = -1 / 3 := by
  norm_num [chargeUnitaryFieldDiag]

@[simp] lemma chargeUnitaryFieldDiag_two :
    chargeUnitaryFieldDiag 2 = -1 / 3 := by
  norm_num [chargeUnitaryFieldDiag]

/-- The diagonal Okubo operator `A^1_1` is the charge-field diagonal
`(2/3,-1/3,-1/3)`. -/
lemma okuboOperator_zero_zero_eq_charge_diag (i : Fin 3) :
    okuboOperator 0 0 i i = chargeUnitaryFieldDiag i := by
  fin_cases i
  · norm_num [okuboOperator, okuboMatrixUnit, Matrix.single, chargeUnitaryFieldDiag]
  · norm_num [okuboOperator, okuboMatrixUnit, Matrix.single, chargeUnitaryFieldDiag]
  · norm_num [okuboOperator, okuboMatrixUnit, Matrix.single, chargeUnitaryFieldDiag]

/-- The diagonal Okubo operator `-A^3_3` is the hypercharge-field diagonal
`(1/3,1/3,-2/3)`. -/
lemma neg_okuboOperator_two_two_eq_hypercharge_diag (i : Fin 3) :
    -okuboOperator 2 2 i i = hyperchargeUnitaryFieldDiag i := by
  fin_cases i
  · simp [okuboOperator, okuboMatrixUnit, Matrix.single, hyperchargeUnitaryFieldDiag]
  · simp [okuboOperator, okuboMatrixUnit, Matrix.single, hyperchargeUnitaryFieldDiag]
  · simp [okuboOperator, okuboMatrixUnit, Matrix.single, hyperchargeUnitaryFieldDiag]
    norm_num

/-- The hypercharge diagonal field is traceless. -/
lemma hyperchargeUnitaryFieldDiag_sum_zero :
    ∑ i : Fin 3, hyperchargeUnitaryFieldDiag i = 0 := by
  rw [Fin.sum_univ_three]
  norm_num

/-- The charge diagonal field is traceless. -/
lemma chargeUnitaryFieldDiag_sum_zero :
    ∑ i : Fin 3, chargeUnitaryFieldDiag i = 0 := by
  rw [Fin.sum_univ_three]
  norm_num

/-- Linear combination of the two diagonal unitary fields used for
hypercharge/charge splitting. -/
def unitaryFieldDiag (C C' : Rat) (i : Fin 3) : Rat :=
  C * hyperchargeUnitaryFieldDiag i + C' * chargeUnitaryFieldDiag i

/-- Any linear combination of the two diagonal unitary fields is traceless. -/
lemma unitaryFieldDiag_sum_zero (C C' : Rat) :
    ∑ i : Fin 3, unitaryFieldDiag C C' i = 0 := by
  rw [Fin.sum_univ_three]
  unfold unitaryFieldDiag
  norm_num
  ring

/-- The diagonal unitary field is the same linear combination of Okubo's two
traceless diagonal matrix entries. -/
lemma unitaryFieldDiag_eq_okubo_diagonal (C C' : Rat) (i : Fin 3) :
    unitaryFieldDiag C C' i =
      C * (-okuboOperator 2 2 i i) + C' * okuboOperator 0 0 i i := by
  rw [neg_okuboOperator_two_two_eq_hypercharge_diag,
    okuboOperator_zero_zero_eq_charge_diag]
  rfl

/-- Okubo's diagonal quadratic perturbation `xi*a + eta*a^2`. -/
def okuboQuadraticShift (xi eta a : Rat) : Rat :=
  xi * a + eta * a ^ 2

/-- A zero diagonal eigenvalue gives no quadratic Okubo shift. -/
lemma okuboQuadraticShift_zero (xi eta : Rat) :
    okuboQuadraticShift xi eta 0 = 0 := by
  unfold okuboQuadraticShift
  ring

/-- Hypercharge Okubo shift evaluated on the diagonal field. -/
def hyperchargeOkuboShift (xi eta : Rat) (i : Fin 3) : Rat :=
  okuboQuadraticShift xi eta (hyperchargeUnitaryFieldDiag i)

/-- Charge Okubo shift evaluated on the diagonal field. -/
def chargeOkuboShift (xi eta : Rat) (i : Fin 3) : Rat :=
  okuboQuadraticShift xi eta (chargeUnitaryFieldDiag i)

/-- The diagonal Okubo mass-squared operator with independent hypercharge and
charge perturbations. -/
def okuboDiagonalMassSq
    (m0Sq xi eta xi' eta' : Rat) (i j : Fin 3) : Rat :=
  m0Sq + hyperchargeOkuboShift xi eta i + chargeOkuboShift xi' eta' j

/-- With all perturbation coefficients zero, the diagonal Okubo operator is
the degenerate mass-squared level. -/
lemma okuboDiagonalMassSq_zero_perturbation (m0Sq : Rat) (i j : Fin 3) :
    okuboDiagonalMassSq m0Sq 0 0 0 0 i j = m0Sq := by
  unfold okuboDiagonalMassSq hyperchargeOkuboShift chargeOkuboShift okuboQuadraticShift
  ring

/-- The diagonal Okubo operator decomposes into a hypercharge shift and a
charge shift. -/
lemma okuboDiagonalMassSq_sub_base
    (m0Sq xi eta xi' eta' : Rat) (i j : Fin 3) :
    okuboDiagonalMassSq m0Sq xi eta xi' eta' i j - m0Sq =
      hyperchargeOkuboShift xi eta i + chargeOkuboShift xi' eta' j := by
  unfold okuboDiagonalMassSq
  ring

/-- First-order mass regime corresponding to the paper's
`delta m^2 / m0^2 << 1`, encoded as a strict small-ratio bound. -/
def FirstOrderMassRegime (m0Sq deltaSq : Rat) : Prop :=
  m0Sq ≠ 0 ∧ |deltaSq / m0Sq| < 1

/-- The first-order mass-regime predicate includes nonzero base mass-squared. -/
lemma FirstOrderMassRegime.base_ne {m0Sq deltaSq : Rat}
    (h : FirstOrderMassRegime m0Sq deltaSq) : m0Sq ≠ 0 :=
  h.1

/-- The first-order mass-regime predicate gives the dimensionless small-ratio
bound directly. -/
lemma FirstOrderMassRegime.small_ratio {m0Sq deltaSq : Rat}
    (h : FirstOrderMassRegime m0Sq deltaSq) : |deltaSq / m0Sq| < 1 :=
  h.2

/-- Linear mass approximation from `m^2 = m0^2 + delta m^2` in the
first-order regime. -/
def linearizedMassFromQuadratic (m0 deltaSq : Rat) : Rat :=
  m0 + deltaSq / (2 * m0)

/-- With zero perturbation, the linearized mass is the base mass. -/
lemma linearizedMassFromQuadratic_zero (m0 : Rat) :
    linearizedMassFromQuadratic m0 0 = m0 := by
  unfold linearizedMassFromQuadratic
  ring

/-- The linearized mass correction is `delta m^2 / (2*m0)`. -/
lemma linearizedMassFromQuadratic_sub_base (m0 deltaSq : Rat) :
    linearizedMassFromQuadratic m0 deltaSq - m0 = deltaSq / (2 * m0) := by
  unfold linearizedMassFromQuadratic
  ring

/-! ## A.12. Gell-Mann-Okubo Splitting Polynomials -/

/-- The isospin-Casimir combination `I(I+1)-Y^2/4` appearing in the
Gell-Mann-Okubo splitting formula. -/
def isospinOkuboCasimir (Y I : Rat) : Rat :=
  I * (I + 1) - Y ^ 2 / 4

/-- The U-spin-Casimir combination `U(U+1)-Q^2/4` appearing in the charge
splitting part of the Gell-Mann-Okubo formula. -/
def uSpinOkuboCasimir (Q U : Rat) : Rat :=
  U * (U + 1) - Q ^ 2 / 4

/-- Quadratic Gell-Mann-Okubo mass-squared polynomial with hypercharge and
charge splitting terms. -/
def gellMannOkuboQuadraticMassSq
    (m0Sq alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) : Rat :=
  m0Sq + alpha + beta * Y + gamma * isospinOkuboCasimir Y I
    + alphaP - betaP * Q + gammaP * uSpinOkuboCasimir Q U

/-- Linear Gell-Mann-Okubo approximation with the same hypercharge and charge
splitting terms. -/
def gellMannOkuboLinearMass
    (m0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) : Rat :=
  m0 + alpha + beta * Y + gamma * isospinOkuboCasimir Y I
    + alphaP - betaP * Q + gammaP * uSpinOkuboCasimir Q U

/-- If the charge-splitting coefficients vanish, the quadratic formula reduces
to its hypercharge/isospin part. -/
lemma gellMannOkuboQuadratic_no_charge_splitting
    (m0Sq alpha beta gamma Y Q I U : Rat) :
    gellMannOkuboQuadraticMassSq m0Sq alpha beta gamma 0 0 0 Y Q I U =
      m0Sq + alpha + beta * Y + gamma * isospinOkuboCasimir Y I := by
  unfold gellMannOkuboQuadraticMassSq uSpinOkuboCasimir
  ring

/-- If the charge-splitting coefficients vanish, the linear formula reduces to
its hypercharge/isospin part. -/
lemma gellMannOkuboLinear_no_charge_splitting
    (m0 alpha beta gamma Y Q I U : Rat) :
    gellMannOkuboLinearMass m0 alpha beta gamma 0 0 0 Y Q I U =
      m0 + alpha + beta * Y + gamma * isospinOkuboCasimir Y I := by
  unfold gellMannOkuboLinearMass uSpinOkuboCasimir
  ring

/-! ## A.13. Zeeman-Type Linear Splittings -/

/-- A minimal algebraic Zeeman shift: a field couples linearly to a quantum
number, `Delta E = coupling * field * quantumNumber`. -/
def zeemanLinearShift (coupling field quantumNumber : Rat) : Rat :=
  coupling * field * quantumNumber

/-- With unit field, the Zeeman shift is the linear term
`coupling * quantumNumber`. -/
lemma zeemanLinearShift_unit_field (coupling quantumNumber : Rat) :
    zeemanLinearShift coupling 1 quantumNumber = coupling * quantumNumber := by
  unfold zeemanLinearShift
  ring

/-- Zeeman shifts split linearly between two quantum-number eigenvalues. -/
lemma zeemanLinearShift_difference (coupling field q₁ q₂ : Rat) :
    zeemanLinearShift coupling field q₁ - zeemanLinearShift coupling field q₂ =
      zeemanLinearShift coupling field (q₁ - q₂) := by
  unfold zeemanLinearShift
  ring

/-- The linear Gell-Mann-Okubo formula decomposes into a Casimir baseline plus
two Zeeman-type linear shifts: one in hypercharge `Y`, and one in electric
charge `Q` with effective coupling `-betaP`. -/
lemma gellMannOkuboLinear_eq_casimir_base_plus_zeeman
    (m0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) :
    gellMannOkuboLinearMass m0 alpha beta gamma alphaP betaP gammaP Y Q I U =
      (m0 + alpha + gamma * isospinOkuboCasimir Y I
        + alphaP + gammaP * uSpinOkuboCasimir Q U)
        + zeemanLinearShift beta 1 Y + zeemanLinearShift (-betaP) 1 Q := by
  unfold gellMannOkuboLinearMass zeemanLinearShift
  ring

/-- Varlamov's final linear spectrum scheme: first average the basic
`SL(2,C)` spin-mass levels over the charge multiplets, then apply the linear
Gell-Mann-Okubo hypercharge and charge splitting terms. -/
def varlamovLinearSupermultipletMass {N : Nat}
    (mu0 alpha beta gamma alphaP betaP gammaP : Rat)
    (reps : Fin N → LorentzSpinorRepresentation) (Y Q I U : Rat) : Rat :=
  gellMannOkuboLinearMass (averageSpinMassLevel mu0 reps)
    alpha beta gamma alphaP betaP gammaP Y Q I U

/-- With zero splitting coefficients, the final linear spectrum returns the
average basic spin-mass level. -/
lemma varlamovLinearSupermultipletMass_zero_splitting {N : Nat}
    (mu0 : Rat) (reps : Fin N → LorentzSpinorRepresentation) (Y Q I U : Rat) :
    varlamovLinearSupermultipletMass mu0 0 0 0 0 0 0 reps Y Q I U =
      averageSpinMassLevel mu0 reps := by
  unfold varlamovLinearSupermultipletMass gellMannOkuboLinearMass
  ring

/-- The final linear spectrum decomposes into its spin-mass average, Casimir
splittings, and the two Zeeman-type linear terms. -/
lemma varlamovLinearSupermultipletMass_eq_casimir_base_plus_zeeman {N : Nat}
    (mu0 alpha beta gamma alphaP betaP gammaP : Rat)
    (reps : Fin N → LorentzSpinorRepresentation) (Y Q I U : Rat) :
    varlamovLinearSupermultipletMass mu0 alpha beta gamma alphaP betaP gammaP
        reps Y Q I U =
      (averageSpinMassLevel mu0 reps + alpha + gamma * isospinOkuboCasimir Y I
        + alphaP + gammaP * uSpinOkuboCasimir Q U)
        + zeemanLinearShift beta 1 Y + zeemanLinearShift (-betaP) 1 Q := by
  unfold varlamovLinearSupermultipletMass
  rw [gellMannOkuboLinear_eq_casimir_base_plus_zeeman]

/-! ## A.13.1. Octet Linear Spectrum Pipelines -/

/-- The final linear mass formula for the baryon octet `F_{1/2}`, using the
four-representative spin-mass average as `m0`. -/
def baryonOctetLinearMass
    (mu0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) : Rat :=
  varlamovLinearSupermultipletMass mu0 alpha beta gamma alphaP betaP gammaP
    baryonOctetChargeMultipletReps Y Q I U

/-- The final linear mass formula for the pseudoscalar meson octet `B0`,
using the four-representative spin-mass average as `m0`. -/
def pseudoscalarOctetLinearMass
    (mu0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) : Rat :=
  varlamovLinearSupermultipletMass mu0 alpha beta gamma alphaP betaP gammaP
    pseudoscalarOctetChargeMultipletReps Y Q I U

/-- The final linear mass formula for the vector meson octet `B1`, using the
four-representative spin-mass average as `m0`. -/
def vectorOctetLinearMass
    (mu0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) : Rat :=
  varlamovLinearSupermultipletMass mu0 alpha beta gamma alphaP betaP gammaP
    vectorOctetChargeMultipletReps Y Q I U

/-- The baryon-octet pipeline reduces to the linear Gell-Mann-Okubo formula
with the explicit `F_{1/2}` average baseline. -/
lemma baryonOctetLinearMass_eq_average_gmo
    (mu0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) :
    baryonOctetLinearMass mu0 alpha beta gamma alphaP betaP gammaP Y Q I U =
      gellMannOkuboLinearMass
        ((spinMassLevel mu0 sigmaTripletSpinorChain
          + spinMassLevel mu0 protonLeftSpinorChain
          + spinMassLevel mu0 xiDoubletSpinorChain
          + spinMassLevel mu0 lambdaSingletSpinorChain) / 4)
        alpha beta gamma alphaP betaP gammaP Y Q I U := by
  unfold baryonOctetLinearMass varlamovLinearSupermultipletMass
  rw [baryonOctetAverageSpinMassLevel_eq]

/-- The pseudoscalar-octet pipeline reduces to the linear Gell-Mann-Okubo
formula with the explicit `B0` average baseline. -/
lemma pseudoscalarOctetLinearMass_eq_average_gmo
    (mu0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) :
    pseudoscalarOctetLinearMass mu0 alpha beta gamma alphaP betaP gammaP Y Q I U =
      gellMannOkuboLinearMass
        ((spinMassLevel mu0 pionTripletSpinorChain
          + spinMassLevel mu0 kaonDoubletSpinorChain
          + spinMassLevel mu0 kaonDoubletSpinorChain
          + spinMassLevel mu0 etaSingletSpinorChain) / 4)
        alpha beta gamma alphaP betaP gammaP Y Q I U := by
  unfold pseudoscalarOctetLinearMass varlamovLinearSupermultipletMass
  rw [pseudoscalarOctetAverageSpinMassLevel_eq]

/-- The vector-octet pipeline reduces to the linear Gell-Mann-Okubo formula
with the explicit `B1` average baseline. -/
lemma vectorOctetLinearMass_eq_average_gmo
    (mu0 alpha beta gamma alphaP betaP gammaP Y Q I U : Rat) :
    vectorOctetLinearMass mu0 alpha beta gamma alphaP betaP gammaP Y Q I U =
      gellMannOkuboLinearMass
        ((spinMassLevel mu0 rhoTripletSpinorChain
          + spinMassLevel mu0 vectorKaonDoubletSpinorChain
          + spinMassLevel mu0 vectorKaonDoubletSpinorChain
          + spinMassLevel mu0 phiSingletSpinorChain) / 4)
        alpha beta gamma alphaP betaP gammaP Y Q I U := by
  unfold vectorOctetLinearMass varlamovLinearSupermultipletMass
  rw [vectorOctetAverageSpinMassLevel_eq]

/-- If two states have the same Okubo Casimir coordinates, their linear
Gell-Mann-Okubo mass difference is exactly the difference of the two
Zeeman-type shifts. -/
lemma gellMannOkuboLinear_difference_of_equal_casimirs
    (m0 alpha beta gamma alphaP betaP gammaP Y₁ Y₂ Q₁ Q₂ I₁ I₂ U₁ U₂ : Rat)
    (hI : isospinOkuboCasimir Y₁ I₁ = isospinOkuboCasimir Y₂ I₂)
    (hU : uSpinOkuboCasimir Q₁ U₁ = uSpinOkuboCasimir Q₂ U₂) :
    gellMannOkuboLinearMass m0 alpha beta gamma alphaP betaP gammaP Y₁ Q₁ I₁ U₁
      - gellMannOkuboLinearMass m0 alpha beta gamma alphaP betaP gammaP Y₂ Q₂ I₂ U₂ =
        zeemanLinearShift beta 1 (Y₁ - Y₂) + zeemanLinearShift (-betaP) 1 (Q₁ - Q₂) := by
  unfold gellMannOkuboLinearMass zeemanLinearShift
  rw [hI, hU]
  ring

/-- The hypercharge-only Gell-Mann-Okubo term is the unit-field Zeeman shift in
the hypercharge quantum number. -/
lemma hyperchargeMassSplitting_is_zeeman (beta Y : Rat) :
    beta * Y = zeemanLinearShift beta 1 Y := by
  rw [zeemanLinearShift_unit_field]

/-- The charge-splitting term `-betaP * Q` is the unit-field Zeeman shift with
effective coupling `-betaP`. -/
lemma chargeMassSplitting_is_zeeman (betaP Q : Rat) :
    -betaP * Q = zeemanLinearShift (-betaP) 1 Q := by
  rw [zeemanLinearShift_unit_field]

/-- The Varlamov spinor/internal-symmetry layer reuses the existing real
Gell-Mann-Okubo baryon-octet identity from `HadronMassSpectrum`. -/
lemma varlamov_links_existing_hadronMassSpectrum_gmo_octet (a b c : ℝ) :
    2 * (octetMass a b c 1 (1 / 2) + octetMass a b c (-1) (1 / 2))
      = 3 * octetMass a b c 0 0 + octetMass a b c 0 1 :=
  gellMannOkubo_octet a b c

/-! ## A.14. Links to Existing Particle Infrastructure -/

/-- Varlamov's octet/decuplet bookkeeping reuses the existing `SU(6)` baryon
spin-flavour branching. -/
lemma varlamov_su6_spinFlavor_branching :
    Nat.choose 8 3 = weylDim3 3 0 * 4 + weylDim3 1 1 * 2 :=
  su6_56_split

/-- Charge conjugation used in the spinor-structure paper is linked to the
existing particle-zoo involution. -/
lemma varlamov_chargeConjugation_links_particleZoo (q : QuantumNumbers) :
    conjugate (conjugate q) = q :=
  zoo_conjugate_involutive q

/-- The electroweak charge/hypercharge split used by internal-symmetry
bookkeeping links to the existing `SU(5)` trace orthogonality. -/
lemma varlamov_charge_hypercharge_trace_orthogonal :
    (∑ i, weakIsospin3 i * hyperchargeY i) = 0 :=
  traceIsospinHypercharge

/-- Checked capability package for the Varlamov spinor/internal-symmetry
bridge: spin labels, `SU(3)` octet admissibility, the Weyl octet dimension,
the `SU(6)` baryon branching, particle-zoo charge conjugation, and `SU(5)`
trace orthogonality are available together. -/
def HasSpinorStructureInternalSymmetryBridge : Prop :=
  su3HadronAdmissible 1 1
    ∧ weylDim3 1 1 = 8
    ∧ Nat.choose 8 3 = weylDim3 3 0 * 4 + weylDim3 1 1 * 2
    ∧ (∀ q : QuantumNumbers, conjugate (conjugate q) = q)
    ∧ (∑ i, weakIsospin3 i * hyperchargeY i) = 0
    ∧ (∀ beta Y : Rat, beta * Y = zeemanLinearShift beta 1 Y)

/-- The Varlamov bridge is discharged entirely by existing `SU(3)`, `SU(6)`,
CPT, and electroweak trace lemmas, plus the local admissibility predicate. -/
lemma spinorStructureInternalSymmetryBridge_checked :
    HasSpinorStructureInternalSymmetryBridge :=
  ⟨su3_octet_admissible,
    varlamov_octet_degree,
    varlamov_su6_spinFlavor_branching,
    varlamov_chargeConjugation_links_particleZoo,
    varlamov_charge_hypercharge_trace_orthogonal,
    hyperchargeMassSplitting_is_zeeman⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.sl2cRepresentationDegree_pos where
  formalizes @ "claim:every-lorentz-sl2c-spinor-representation-has-positive-representation-degree",
  supported_by @ "paper:weinberg-quantum-theory-of-fields-lorentz-representations"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinNumerator_chiral_swap where
  formalizes @ "claim:the-chiral-parity-swap-exchanges-the-dotted-and-undotted-spinor-indices-of-a-lorentz-representation",
  supported_by @ "paper:weinberg-quantum-theory-of-fields-lorentz-representations"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinValue_chiral_swap where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinNumerator_chiral_swap",
  formalizes @ "claim:the-spin-value-of-a-lorentz-spinor-representation-is-invariant-under-the-chiral-parity-swap",
  requires @ "claim:the-chiral-parity-swap-exchanges-the-dotted-and-undotted-spinor-indices-of-a-lorentz-representation"

zil_file_contract physlib.spinorStructureInternalSymmetries where
  promises "The Lorentz SL(2,C) spinor representation structure and its internal-symmetry labels: every representation has positive representation degree and spin-space dimension; the chiral (parity) swap exchanges the dotted and undotted spinor indices, and the spin value is invariant under it; a self-conjugate representation has vanishing spin numerator; and the fixed spin-line labels realize the spin-zero, spin-half and spin-one representations with their degrees and binary spinor-tensor dimensions."
  at_level structural
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.LorentzSpinorRepresentation",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinNumerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinValue"]
  forbids_substitutes ["a construction of the spinor field operators or their dynamics, only the representation-label combinatorics are carried",
    "a proof of the spin-statistics connection, which is a separate theorem"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.sl2cRepresentationDegree_pos,
    Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinspaceDimension_pos,
    Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinNumerator_self_conjugate_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinNumerator_chiral_swap,
    Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries.spinValue_chiral_swap]

/- ZIL-END -/
