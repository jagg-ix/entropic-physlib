/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

/-!
# Everettian relative states in the Heisenberg picture

This file records the finite algebraic core of Samuel Kuypers and David Deutsch,
*Everettian relative states in the Heisenberg picture*, Proc. R. Soc. A **477**,
20200783 (2021), DOI: `10.1098/rspa.2020.0783`.

The paper works with quantum computational networks.  The part formalized here is
the finite two-outcome skeleton used in Sections 2--6:

* the projectors `P_+(q_z)=(1+q_z)/2` and `P_-(q_z)=(1-q_z)/2`;
* the CNOT/perfect-measurement copy relation for sharp `z` values;
* relative Heisenberg descriptors of the form `q_rel = q P`;
* the relative projector `P` acting as the unit of the relative descriptor algebra;
* branch-preserving Heisenberg evolution as autonomous evolution of relative
  descriptors;
* the branch-restricted form of the polynomial gate in eqs. (5.3)--(5.5);
* the binary memory descriptor of eq. (6.1) and the `2^n` register count;
* local finite-support updates as the discrete locality statement used by the
  Heisenberg-picture description;
* compatibility with the repository's finite spectral projector and
  unitary-decoherent measurement layers.

The module does not claim a full continuum quantum-field-theoretic locality
construction.  It isolates the equations above in a finite algebra where Lean can
check the projector and descriptor identities directly.

## References

* Samuel Kuypers and David Deutsch, *Everettian relative states in the
  Heisenberg picture*, Proc. R. Soc. A **477**, 20200783 (2021),
  DOI: `10.1098/rspa.2020.0783`.
* David Deutsch and Patrick Hayden, *Information flow in entangled quantum
  systems*, Proc. R. Soc. A **456**, 1759--1774 (2000).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open BigOperators
open Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement
open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

namespace Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-! ## A. Two-outcome spin projectors -/

set_option backward.isDefEq.respectTransparency false in
/-- The two eigenvalues used for the measured computational `z` variable. -/
inductive SpinOutcome where
  /-- The `+1` eigenvalue. -/
  | plus
  /-- The `-1` eigenvalue. -/
  | minus
deriving DecidableEq, Fintype, Repr

/-- Equivalence between the two spin outcomes and booleans, used for register counts. -/
def SpinOutcome.equivBool : SpinOutcome ≃ Bool where
  toFun
    | .plus => true
    | .minus => false
  invFun
    | true => .plus
    | false => .minus
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

/-- There are exactly two sharp spin outcomes. -/
lemma spinOutcome_card : Fintype.card SpinOutcome = 2 := by
  calc
    Fintype.card SpinOutcome = Fintype.card Bool := Fintype.card_congr SpinOutcome.equivBool
    _ = 2 := Fintype.card_bool

/-- The real eigenvalue associated to a two-outcome spin value. -/
def SpinOutcome.sign : SpinOutcome → ℝ
  | .plus => 1
  | .minus => -1

/-- The opposite two-outcome spin value. -/
def SpinOutcome.flip : SpinOutcome → SpinOutcome
  | .plus => .minus
  | .minus => .plus

/-- Multiplication of sharp `±1` spin values. -/
def SpinOutcome.mul : SpinOutcome → SpinOutcome → SpinOutcome
  | .plus, b => b
  | .minus, .plus => .minus
  | .minus, .minus => .plus

@[simp] lemma SpinOutcome.sign_plus : SpinOutcome.sign .plus = 1 := rfl

@[simp] lemma SpinOutcome.sign_minus : SpinOutcome.sign .minus = -1 := rfl

@[simp] lemma SpinOutcome.flip_plus : SpinOutcome.flip .plus = .minus := rfl

@[simp] lemma SpinOutcome.flip_minus : SpinOutcome.flip .minus = .plus := rfl

@[simp] lemma SpinOutcome.mul_plus_left (a : SpinOutcome) :
    SpinOutcome.mul .plus a = a := by
  cases a <;> rfl

@[simp] lemma SpinOutcome.mul_plus_right (a : SpinOutcome) :
    SpinOutcome.mul a .plus = a := by
  cases a <;> rfl

@[simp] lemma SpinOutcome.sign_mul (a b : SpinOutcome) :
    SpinOutcome.sign (SpinOutcome.mul a b) = SpinOutcome.sign a * SpinOutcome.sign b := by
  cases a <;> cases b <;> norm_num [SpinOutcome.sign, SpinOutcome.mul]

@[simp] lemma SpinOutcome.sign_sq (a : SpinOutcome) :
    SpinOutcome.sign a * SpinOutcome.sign a = 1 := by
  cases a <;> norm_num [SpinOutcome.sign]

/--
Coefficient of the branch projector
`P_s(q_z) = (1 + s q_z)/2` on a sharp eigenvalue `q_z = e`.
-/
def spinProjectorCoefficient (s e : SpinOutcome) : ℝ :=
  (1 + SpinOutcome.sign s * SpinOutcome.sign e) / 2

@[simp] lemma spinProjectorCoefficient_same (s : SpinOutcome) :
    spinProjectorCoefficient s s = 1 := by
  cases s <;> norm_num [spinProjectorCoefficient, SpinOutcome.sign]

@[simp] lemma spinProjectorCoefficient_flip (s : SpinOutcome) :
    spinProjectorCoefficient s (SpinOutcome.flip s) = 0 := by
  cases s <;> norm_num [spinProjectorCoefficient, SpinOutcome.sign, SpinOutcome.flip]

/-- The two branch projectors form a two-outcome PVM at the coefficient level. -/
lemma spinProjectorCoefficient_sum (e : SpinOutcome) :
    spinProjectorCoefficient .plus e + spinProjectorCoefficient .minus e = 1 := by
  cases e <;> norm_num [spinProjectorCoefficient, SpinOutcome.sign]

/-- Each two-outcome branch coefficient is idempotent on sharp eigenvalues. -/
lemma spinProjectorCoefficient_idempotent (s e : SpinOutcome) :
    spinProjectorCoefficient s e * spinProjectorCoefficient s e =
      spinProjectorCoefficient s e := by
  cases s <;> cases e <;> norm_num [spinProjectorCoefficient, SpinOutcome.sign]

/-- Distinct two-outcome branch coefficients have zero product. -/
lemma spinProjectorCoefficient_orthogonal (e : SpinOutcome) :
    spinProjectorCoefficient .plus e * spinProjectorCoefficient .minus e = 0 := by
  cases e <;> norm_num [spinProjectorCoefficient, SpinOutcome.sign]

/-! ## B. Projected branch vectors and Born weights -/

/-- The spectral value map for the two sharp `z` outcomes. -/
def spinSpectralValue : SpinOutcome → ℝ :=
  SpinOutcome.sign

/-- Project a finite two-outcome coefficient vector onto one branch. -/
def spinProjectedBranchVector (s : SpinOutcome) (ψ : SpinOutcome → ℂ) :
    SpinOutcome → ℂ :=
  fun e => (spinProjectorCoefficient s e : ℂ) * ψ e

/-- Branch projection agrees with the existing finite spectral projector. -/
lemma spinProjectedBranchVector_eq_finiteSpectralProjector
    (s : SpinOutcome) (ψ : SpinOutcome → ℂ) :
    spinProjectedBranchVector s ψ =
      finiteSpectralProjector spinSpectralValue {SpinOutcome.sign s} ψ := by
  funext e
  cases s <;> cases e <;>
    norm_num [spinProjectedBranchVector, spinProjectorCoefficient,
      finiteSpectralProjector, spinSpectralValue, SpinOutcome.sign]

/-- Applying the same branch projection twice changes nothing further. -/
lemma spinProjectedBranchVector_idempotent (s : SpinOutcome) (ψ : SpinOutcome → ℂ) :
    spinProjectedBranchVector s (spinProjectedBranchVector s ψ) =
      spinProjectedBranchVector s ψ := by
  rw [spinProjectedBranchVector_eq_finiteSpectralProjector,
    spinProjectedBranchVector_eq_finiteSpectralProjector]
  simpa [spinProjectedBranchVector_eq_finiteSpectralProjector] using
    finiteSpectralProjector_idempotent spinSpectralValue {SpinOutcome.sign s} ψ

/-- The two branch projections reconstruct the original two-outcome vector. -/
lemma spinProjectedBranchVector_sum (ψ : SpinOutcome → ℂ) :
    spinProjectedBranchVector .plus ψ + spinProjectedBranchVector .minus ψ = ψ := by
  funext e
  cases e <;>
    norm_num [spinProjectedBranchVector, spinProjectorCoefficient, SpinOutcome.sign]

/-- Born weight of one branch coefficient. -/
def branchBornWeight (ψ : SpinOutcome → ℂ) (s : SpinOutcome) : ℝ :=
  ‖ψ s‖ ^ 2

/-- The total Born weight of a two-outcome coefficient vector. -/
def totalBornWeight (ψ : SpinOutcome → ℂ) : ℝ :=
  ∑ s : SpinOutcome, branchBornWeight ψ s

/-- Pointwise equality of branch amplitudes gives equality of total Born weight. -/
lemma totalBornWeight_congr
    {ψ φ : SpinOutcome → ℂ} (h : ∀ s, φ s = ψ s) :
    totalBornWeight φ = totalBornWeight ψ := by
  unfold totalBornWeight branchBornWeight
  simp [h]

/-! ## C. Perfect-measurement records -/

/-- Pointer value after the sharp-value part of CNOT: `M_z' = M_z S_z`. -/
def cnotPointerValue (system pointer : SpinOutcome) : SpinOutcome :=
  SpinOutcome.mul pointer system

/-- If the pointer starts at `+1`, CNOT records the system value in the pointer. -/
@[simp] lemma cnotPointerValue_plus_pointer (system : SpinOutcome) :
    cnotPointerValue system .plus = system := by
  cases system <;> rfl

/-- Eigenvalue version of `M_z' = M_z S_z`. -/
lemma cnotPointerValue_sign (system pointer : SpinOutcome) :
    SpinOutcome.sign (cnotPointerValue system pointer) =
      SpinOutcome.sign pointer * SpinOutcome.sign system := by
  simp [cnotPointerValue, SpinOutcome.sign_mul, mul_comm]

/-- A finite measurement record: the system value and the pointer value. -/
structure MeasurementRecord where
  /-- The measured sharp system value. -/
  systemValue : SpinOutcome
  /-- The sharp pointer value after the measurement interaction. -/
  pointerValue : SpinOutcome

/-- A record is accurate when pointer and system values agree. -/
def MeasurementRecord.IsAccurate (r : MeasurementRecord) : Prop :=
  r.pointerValue = r.systemValue

/-- The record obtained from a sharp-value CNOT with pointer initially `+1`. -/
def cnotRecord (system : SpinOutcome) : MeasurementRecord :=
  { systemValue := system
    pointerValue := cnotPointerValue system .plus }

/-- The sharp-value CNOT record is accurate. -/
@[simp] lemma cnotRecord_isAccurate (system : SpinOutcome) :
    (cnotRecord system).IsAccurate := by
  simp [MeasurementRecord.IsAccurate, cnotRecord]

/-! ## D. Relative Heisenberg descriptors -/

/-- A branch projector in an abstract non-commutative operator algebra. -/
def IsBranchProjector {A : Type*} [Semiring A] (P : A) : Prop :=
  P * P = P

/-- A relative Heisenberg descriptor `q_rel = q P`. -/
def relativeDescriptor {A : Type*} [Semiring A] (q P : A) : A :=
  q * P

/-- The relative projector is a right identity for its relative descriptor. -/
lemma relativeDescriptor_mul_projector {A : Type*} [Semiring A]
    {q P : A} (hP : IsBranchProjector P) :
    relativeDescriptor q P * P = relativeDescriptor q P := by
  simpa [relativeDescriptor, IsBranchProjector, mul_assoc] using congrArg (fun x => q * x) hP

/--
If descriptor and projector commute, the relative projector is also a left
identity for the relative descriptor.
-/
lemma projector_mul_relativeDescriptor {A : Type*} [Semiring A]
    {q P : A} (hP : IsBranchProjector P) (hcomm : q * P = P * q) :
    P * relativeDescriptor q P = relativeDescriptor q P := by
  change P * P = P at hP
  calc
    P * relativeDescriptor q P = (P * q) * P := by
      simp [relativeDescriptor, mul_assoc]
    _ = (q * P) * P := by rw [← hcomm]
    _ = q * (P * P) := by simp [mul_assoc]
    _ = relativeDescriptor q P := by
      rw [hP]
      rfl

/--
Kuypers--Deutsch eq. (4.10) in abstract form for one descriptor component:
if `q²=1`, `P²=P`, and `q` commutes with `P`, then `(qP)²=P`.  Thus `P`
is the unit observable of the relative component algebra.
-/
lemma relativeDescriptor_sq_eq_projector {A : Type*} [Semiring A]
    {q P : A} (hq : q * q = 1) (hP : IsBranchProjector P) (hcomm : q * P = P * q) :
    relativeDescriptor q P * relativeDescriptor q P = P := by
  have hcomm' : P * q = q * P := hcomm.symm
  calc
    relativeDescriptor q P * relativeDescriptor q P = q * (P * q) * P := by
      simp [relativeDescriptor, mul_assoc]
    _ = q * (q * P) * P := by rw [hcomm']
    _ = (q * q) * (P * P) := by simp [mul_assoc]
    _ = P := by
      simp [hq, IsBranchProjector] at hP ⊢
      exact hP

/-! ## E. Autonomous branch evolution -/

/-- A Heisenberg evolution preserves a branch when it fixes the branch projector. -/
def PreservesBranchProjector {A : Type*} [Semiring A] (φ : A →+* A) (P : A) : Prop :=
  φ P = P

/--
Section 5 autonomy in algebraic form: if the Heisenberg evolution fixes the
branch projector, then the evolved relative descriptor is the relative descriptor
of the evolved absolute descriptor.
-/
lemma map_relativeDescriptor_of_preservesBranchProjector {A : Type*} [Semiring A]
    (φ : A →+* A) {q P : A} (hφP : PreservesBranchProjector φ P) :
    φ (relativeDescriptor q P) = relativeDescriptor (φ q) P := by
  unfold PreservesBranchProjector at hφP
  simp [relativeDescriptor, hφP]

/--
The scalar form of the gate polynomial in Kuypers--Deutsch eq. (5.3),
`α + β m + γ z + δ m z`, evaluated on sharp branch values.
-/
def branchGateScalar (a b c d m z : ℂ) : ℂ :=
  a + b * m + c * z + d * (m * z)

/-- Restricting eq. (5.3) to the `m=+1` branch gives the first coefficient pair
in eq. (5.5). -/
lemma branchGateScalar_plus (a b c d z : ℂ) :
    branchGateScalar a b c d 1 z = (a + b) + (c + d) * z := by
  unfold branchGateScalar
  ring

/-- Restricting eq. (5.3) to the `m=-1` branch gives the second coefficient pair
in eq. (5.5). -/
lemma branchGateScalar_minus (a b c d z : ℂ) :
    branchGateScalar a b c d (-1) z = (a - b) + (c - d) * z := by
  unfold branchGateScalar
  ring

/-- The sharp branch `z` value after an `R_z(θ)` rotation, as used in eq. (5.6). -/
def branchZAfterRz (s : SpinOutcome) (_θ : ℝ) : ℝ :=
  SpinOutcome.sign s

/-- The sharp `z` record in a branch is independent of the rotation angle `θ`. -/
lemma branchZAfterRz_angle_independent (s : SpinOutcome) (θ φ : ℝ) :
    branchZAfterRz s θ = branchZAfterRz s φ := by
  rfl

/-! ## F. Quasi-classical binary memory descriptors -/

/-- The bit extracted by the `P_-(q_z)` projector: `0` on `+1`, `1` on `-1`. -/
def spinBit : SpinOutcome → ℕ
  | .plus => 0
  | .minus => 1

@[simp] lemma spinBit_plus : spinBit .plus = 0 := rfl

@[simp] lemma spinBit_minus : spinBit .minus = 1 := rfl

/-- The bit value is exactly the `P_-` branch-projector coefficient. -/
lemma spinBit_eq_projector_minus_coeff (s : SpinOutcome) :
    (spinBit s : ℝ) = spinProjectorCoefficient .minus s := by
  cases s <;> norm_num [spinBit, spinProjectorCoefficient, SpinOutcome.sign]

/-- Natural-number binary memory value associated to a finite qubit register. -/
def binaryMemoryNat {n : ℕ} (bits : Fin n → SpinOutcome) : ℕ :=
  ∑ i : Fin n, spinBit (bits i) * 2 ^ i.val

/--
Kuypers--Deutsch eq. (6.1): the same finite memory descriptor as a sum of
weighted `P_-(q_z)` branch coefficients.
-/
def binaryMemoryDescriptor {n : ℕ} (bits : Fin n → SpinOutcome) : ℝ :=
  ∑ i : Fin n, (2 : ℝ) ^ i.val * spinProjectorCoefficient .minus (bits i)

/-- The projector-coefficient memory descriptor equals the natural binary value. -/
lemma binaryMemoryDescriptor_eq_natCast {n : ℕ} (bits : Fin n → SpinOutcome) :
    binaryMemoryDescriptor bits = (binaryMemoryNat bits : ℝ) := by
  unfold binaryMemoryDescriptor binaryMemoryNat
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> norm_num [spinBit, spinProjectorCoefficient, SpinOutcome.sign]

/-- The all-`+1` register has binary memory value `0`. -/
@[simp] lemma binaryMemoryNat_all_plus (n : ℕ) :
    binaryMemoryNat (fun _ : Fin n => SpinOutcome.plus) = 0 := by
  simp [binaryMemoryNat]

/-- A one-qubit all-`-1` register has binary memory value `1`. -/
@[simp] lemma binaryMemoryNat_one_minus :
    binaryMemoryNat (fun _ : Fin 1 => SpinOutcome.minus) = 1 := by
  simp [binaryMemoryNat]

/-- An `n`-qubit `z`-memory register has `2^n` possible sharp configurations. -/
lemma spinOutcome_register_card (n : ℕ) :
    Fintype.card (Fin n → SpinOutcome) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, spinOutcome_card]

/-! ## G. Finite locality of Heisenberg updates -/

/-- Two site-indexed descriptors agree outside a chosen finite interaction region. -/
def AgreesOutside {Site Obs : Type*} (S : Set Site) (new old : Site → Obs) : Prop :=
  ∀ x : Site, x ∉ S → new x = old x

/-- Update a site-indexed descriptor only on the chosen interaction region. -/
def updateOnSupport {Site Obs : Type*} (S : Set Site) (inside old : Site → Obs) :
    Site → Obs := by
  classical
  exact fun x => if x ∈ S then inside x else old x

/-- A support update leaves every site outside the support unchanged. -/
lemma updateOnSupport_agreesOutside {Site Obs : Type*}
    (S : Set Site) (inside old : Site → Obs) :
    AgreesOutside S (updateOnSupport S inside old) old := by
  intro x hx
  simp [updateOnSupport, hx]

/-! ## H. Repository-level measurement link -/

/-- The Heisenberg relative-state construction uses no primitive collapse step. -/
lemma everettHeisenberg_excludes_primitive_collapse :
    ¬ IsPrimitiveCollapse .unitaryInteraction ∧
      ¬ IsPrimitiveCollapse .environmentalDecoherence ∧
      ¬ IsPrimitiveCollapse .lindbladReducedDynamics ∧
      ¬ IsPrimitiveCollapse .bornWeightedConditioning := by
  exact ⟨unitaryInteraction_not_primitiveCollapse,
    environmentalDecoherence_not_primitiveCollapse,
    lindbladReducedDynamics_not_primitiveCollapse,
    bornWeightedConditioning_not_primitiveCollapse⟩

end Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

end

end
