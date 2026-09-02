/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
public import Physlib.QuantumMechanics.NonHermitian.WickRotation
public import Physlib.QFT.PathIntegral.FeynmanKac

/-!
# A. Symmetry-dilation motion from Heisenberg commutators

This module records the algebraic core of Enrique Casanova, Jose Rojas, and Melvin Arias,
*On the Derivation of Equations of Motion from Symmetries in Quantum-Mechanical Systems via
Heisenberg's Uncertainty Principle* (arXiv:2508.10661v1, 2025), using the existing finite-matrix
Dirac, Pauli, and Heisenberg-picture infrastructure.

The paper starts from the product of conjugate operator spaces, splits the product into commutator
and Jordan parts, and imposes the centralizer condition `[A,Q]=0`. In finite dimension this has a
simple checked consequence: if a state is in the kernel of the central operator `A`, then any compatible
symmetry-dilation `Q` maps it to another vector in the same kernel.

## A.1. Reused equations

* `PeriodicQHermitian.Basic.commutator` and `heisenbergGen` supply the Heisenberg-picture bracket.
* `FourSpinorDiracHamiltonian.diracHamiltonian4_sq` supplies the relativistic Dirac square / Klein-Gordon
  mass shell.
* `FourSpinorDiracHamiltonian.velocity_heisenberg_derivative` and `zitter_oscillation` supply the
  Heisenberg motion of the Dirac velocity operator.
* `PauliEquationSpinOrbit.sigmaDot_sq`, `sigmaDot_commutator`, `heisenberg_spin_precession`, and
  `pauliHamiltonianFW_spinOrbit` supply the nonrelativistic Pauli/spin sector.

## A.2. Paper-specific additions

* `operatorProduct_eq_half_commutator_add_half_jordan` formalizes Eq. (5), the product split.
* `centralizer_preserves_kernel` formalizes the compatible-observable / centralizer mechanism behind
  Eq. (6) and Assertion A2.
* `schrodingerCentralSymbol_eq_zero_iff` formalizes Eq. (42): `p^2 - 2aH=0` is the Schrödinger
  dispersion `H=p^2/(2a)` when `a != 0`.
* `pauliGaugeOperator_sq` formalizes Eqs. (43) and (44): the Galilean gauge shift
  `p_i -> p_i - (q/c)phi_i` feeds the same Pauli square.
* `carrollScalarSymbol_eq_zero_iff` formalizes Eqs. (47) and (48): the scalar Carroll symbol
  `n.p - 2aH^2` is the corresponding central dispersion constraint.
* `carrollEq49Phase_eq_reversiblePhaseC` and
  `carrollEq49_wickRotatedPhase_eq_real_invertedHeatWeight` link the oscillatory part of Eq. (49)
  to the existing reversible-phase / Wick-rotation API.
* `carrollEq49_wickRotatedPhase_eq_feynmanKacWeight` identifies the same Wick-rotated phase with
  the existing constant-potential Feynman-Kac weight.
* `carrollSchrodingerPauli_factorization` formalizes the spinful Carroll-Schrodinger-Pauli operator
  in Eq. (55): `(sigma.p - lambda)(sigma.p + lambda) = (p^2-lambda^2)I`, reusing the existing Pauli
  identity.
* `rotationRestoringCoupling_eq_cross` formalizes Eq. (54), the Pauli-matrix commutator form of
  the rotation-restoring coupling.
* `carrollSchrodingerPauliOperator_mulVec_eq_zero_of_sigmaDot_eigen` formalizes the eigen-spinor
  kernel condition behind Eqs. (55) and (56).
* `carrollSchrodingerPauliPotential_factorization` formalizes Eqs. (57) and (58): the ultra-boost
  potential-shifted momentum satisfies the same Pauli factorization.
* `carrollSchrodingerPauliPotential_weyl_limit` formalizes Eq. (59), the zero-coefficient limit
  to the Weyl/helicity operator `sigma.p`.

## References

* Enrique Casanova, Jose Rojas, Melvin Arias, *On the Derivation of Equations of Motion from
  Symmetries in Quantum-Mechanical Systems via Heisenberg's Uncertainty Principle*, arXiv:2508.10661v1
  (2025), especially Eqs. (5), (6), (16), (17), (42)-(44), (47), (48), and (55)-(59).
* Physlib modules reused here: `Dirac.FourSpinorDiracHamiltonian`, `Dirac.PauliEquationSpinOrbit`,
  and `PeriodicQHermitian.Ehrenfest`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix Complex
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.NonHermitian.WickRotation

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.HeisenbergSymmetryMotion

variable {n : Type*} [Fintype n]

/-- The Jordan/symmetric part of a product: `{A,B}=AB+BA`. -/
def jordanPart (A B : Matrix n n ℂ) : Matrix n n ℂ := A * B + B * A

/-- The scalar symbol of the nonrelativistic central operator from Eq. (42), `p^2 - 2aH`. -/
def schrodingerCentralSymbol (a H pSq : ℝ) : ℝ := pSq - 2 * a * H

/-- The spinful Carroll-Schrodinger-Pauli symbol from Eq. (55), `sigma.p - 2aH^2 I`. -/
def carrollSchrodingerPauliOperator (a H : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sigmaDot p - ((2 * a * H ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Eq. (43): the Galilean gauge shift of momentum, `p_i -> p_i - (q/c)phi_i`. -/
def galileanGaugeMomentum (q c : ℝ) (phi p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => p i - (q / c) * phi i

/-- Eq. (44): the Pauli operator obtained from the Galilean gauge-shifted momentum. -/
def pauliGaugeOperator (q c : ℝ) (phi p : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sigmaDot (galileanGaugeMomentum q c phi p)

/-- Eqs. (47) and (48): the scalar Carroll-Schrodinger symbol `n.p - 2aH^2`. -/
def carrollScalarSymbol (a H nDotP : ℝ) : ℝ := nDotP - 2 * a * H ^ 2

/-- Eq. (57): the ultra-boost shifted momentum used in the Carroll-Pauli equation. -/
def carrollShiftedMomentum (Q a c v H : ℝ) (phi p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => p i - (Q * a) * phi i * H + ((c ^ 2 * Q ^ 2) / (v ^ 2) * a) * phi i ^ 2

/-- Eq. (58): the Carroll-Schrodinger-Pauli operator after the ultra-boost potential shift. -/
def carrollSchrodingerPauliPotentialOperator
    (Q a c v H : ℝ) (phi p : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sigmaDot (carrollShiftedMomentum Q a c v H phi p)
    - ((2 * a * H ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Eq. (49)'s coefficient choice `a* = -1/(4mc^3)` for the scalar Carroll kernel. -/
def carrollEq49AStar (m c : ℝ) : ℝ := -1 / (4 * m * c ^ 3)

/-- Eq. (49)'s effective reversible energy when the quadratic time variable `t^2`
is used as the phase-evolution parameter. -/
def carrollEq49Energy (m c x : ℝ) : ℝ := -(m * c ^ 3) / (2 * x)

/-- The oscillatory phase in Eq. (49), excluding the normalization prefactor:
`exp(i m c^3 t^2 / (2 hbar x))`. -/
def carrollEq49Phase (m c hbar x t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((m * c ^ 3 * t ^ 2) / (2 * hbar * x) : ℝ) : ℂ))

/-- Eq. (54): the Pauli-matrix form of the rotation-restoring coupling
`E = -(i hbar / 2)[sigma.a, sigma.b]`. -/
def rotationRestoringCoupling (hbar : ℝ) (a b : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (-(I * (hbar : ℂ)) / 2 : ℂ) •
    Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator
      (sigmaDot a) (sigmaDot b)

/-- The centralizer condition `[A,Q]=0` for a central operator `A` and a symmetry-dilation `Q`. -/
def centralizes [DecidableEq n] (A Q : Matrix n n ℂ) : Prop :=
  Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator A Q = 0

/-- Eq. (5): the product is half the commutator plus half the Jordan part,
`AB = 1/2[A,B] + 1/2{A,B}`. -/
lemma operatorProduct_eq_half_commutator_add_half_jordan [DecidableEq n]
    (A B : Matrix n n ℂ) :
    A * B = ((1 / 2 : ℂ) •
        Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator A B)
      + ((1 / 2 : ℂ) • jordanPart A B) := by
  unfold Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator jordanPart
  ext i j
  simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- The centralizer condition is matrix commutation. -/
lemma centralizes_iff_mul_comm [DecidableEq n] (A Q : Matrix n n ℂ) :
    centralizes A Q ↔ A * Q = Q * A := by
  unfold centralizes Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

/-- If `[A,Q]=0` and `A psi=0`, then `A(Q psi)=0`. This is the finite-dimensional
kernel form of the paper's compatible-observable mechanism: a symmetry-dilation commuting with the central
operator preserves the solution space of the equation of motion. -/
lemma centralizer_preserves_kernel [DecidableEq n] (A Q : Matrix n n ℂ) (psi : n → ℂ)
    (hAQ : centralizes A Q) (hpsi : A.mulVec psi = 0) :
    A.mulVec (Q.mulVec psi) = 0 := by
  rw [Matrix.mulVec_mulVec psi A Q, (centralizes_iff_mul_comm A Q).mp hAQ,
    ← Matrix.mulVec_mulVec psi Q A, hpsi, Matrix.mulVec_zero]

/-- Eq. (42) solved for the energy generator: if `a != 0`, the constraint
`p^2 - 2aH = 0` is equivalent to `H = p^2/(2a)`. -/
lemma schrodingerCentralSymbol_eq_zero_iff (a H pSq : ℝ) (ha : a ≠ 0) :
    schrodingerCentralSymbol a H pSq = 0 ↔ H = pSq / (2 * a) := by
  unfold schrodingerCentralSymbol
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  constructor
  · intro h
    have hmul : 2 * a * H = pSq := by linarith
    calc H = (2 * a * H) / (2 * a) := by field_simp [h2a]
      _ = pSq / (2 * a) := by rw [hmul]
  · intro h
    rw [h]
    field_simp [h2a]
    ring_nf

/-- Eq. (44): the gauge-shifted Pauli operator squares to the shifted momentum norm. -/
lemma pauliGaugeOperator_sq (q c : ℝ) (phi p : Fin 3 → ℝ) :
    pauliGaugeOperator q c phi p * pauliGaugeOperator q c phi p
      = ((dotR (galileanGaugeMomentum q c phi p) (galileanGaugeMomentum q c phi p) : ℝ) : ℂ)
          • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  sigmaDot_sq (galileanGaugeMomentum q c phi p)

/-- The spin-orbit commutator remains the existing Pauli commutator after the Galilean gauge shift. -/
lemma pauliGaugeOperator_spin_commutator (q c : ℝ) (gradV phi p : Fin 3 → ℝ) :
    Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator
        (sigmaDot gradV) (pauliGaugeOperator q c phi p)
      = (2 * I) • sigmaDot (crossR gradV (galileanGaugeMomentum q c phi p)) :=
  spinOrbit_from_commutator gradV (galileanGaugeMomentum q c phi p)

/-- With zero gauge potential, the Galilean shifted momentum is the original momentum. -/
lemma galileanGaugeMomentum_zero_potential (q c : ℝ) (p : Fin 3 → ℝ) :
    galileanGaugeMomentum q c 0 p = p := by
  funext i
  simp [galileanGaugeMomentum]

/-- With zero gauge potential, Eq. (44) reduces to the original Pauli operator `sigma.p`. -/
lemma pauliGaugeOperator_zero_potential (q c : ℝ) (p : Fin 3 → ℝ) :
    pauliGaugeOperator q c 0 p = sigmaDot p := by
  simp [pauliGaugeOperator, galileanGaugeMomentum_zero_potential]

/-- Eqs. (47) and (48) solved for the Carroll energy square: if `a != 0`, the constraint
`n.p - 2aH^2 = 0` is equivalent to `H^2 = (n.p)/(2a)`. -/
lemma carrollScalarSymbol_eq_zero_iff (a H nDotP : ℝ) (ha : a ≠ 0) :
    carrollScalarSymbol a H nDotP = 0 ↔ H ^ 2 = nDotP / (2 * a) := by
  unfold carrollScalarSymbol
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  constructor
  · intro h
    have hmul : 2 * a * H ^ 2 = nDotP := by linarith
    calc H ^ 2 = (2 * a * H ^ 2) / (2 * a) := by field_simp [h2a]
      _ = nDotP / (2 * a) := by rw [hmul]
  · intro h
    rw [h]
    field_simp [h2a]
    ring_nf

/-- Eq. (49)'s coefficient choice normalizes as `-4mc^3 a* = 1`. -/
lemma carrollEq49AStar_normalization (m c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    -4 * m * c ^ 3 * carrollEq49AStar m c = 1 := by
  unfold carrollEq49AStar
  have hden : 4 * m * c ^ 3 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) (pow_ne_zero 3 hc)
  field_simp [hden]

/-- Eq. (49)'s oscillatory phase is the existing reversible Schrödinger phase
`reversiblePhaseC` with energy `-mc^3/(2x)` and evolution parameter `t^2`. -/
lemma carrollEq49Phase_eq_reversiblePhaseC (m c hbar x t : ℝ) :
    carrollEq49Phase m c hbar x t =
      reversiblePhaseC (carrollEq49Energy m c x) hbar ((t ^ 2 : ℝ) : ℂ) := by
  unfold carrollEq49Phase reversiblePhaseC carrollEq49Energy
  congr 1
  push_cast
  ring

/-- Wick rotating the Eq. (49) reversible phase gives the real inverted heat-kernel
weight `exp(mc^3 τ/(2 x hbar))`. This is only the scalar phase/weight identity;
no distributional delta limit is asserted here. -/
lemma carrollEq49_wickRotatedPhase_eq_real_invertedHeatWeight (m c hbar x τ : ℝ) :
    reversiblePhaseC (carrollEq49Energy m c x) hbar (-Complex.I * (τ : ℂ)) =
      ((Real.exp (((m * c ^ 3) * τ) / (2 * x * hbar)) : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]
  congr 2
  unfold carrollEq49Energy
  ring

/-- The Wick-rotated Eq. (49) phase is also the existing constant-potential
Feynman-Kac weight with potential `carrollEq49Energy / hbar`. -/
lemma carrollEq49_wickRotatedPhase_eq_feynmanKacWeight (m c hbar x τ : ℝ) :
    reversiblePhaseC (carrollEq49Energy m c x) hbar (-Complex.I * (τ : ℂ)) =
      ((Physlib.QFT.PathIntegral.feynman_kac_weight
        (fun _ : Unit => carrollEq49Energy m c x / hbar) τ () : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]
  simp [Physlib.QFT.PathIntegral.feynman_kac_weight]
  congr 1
  ring

/-- The relativistic branch of the paper reuses the existing four-spinor Dirac square and the
Heisenberg velocity equation: the same Clifford algebra gives the Klein-Gordon square and the velocity
commutator. -/
lemma relativistic_dirac_symmetry_motion_core (p1 p2 p3 m : ℝ) :
    diracHamiltonian4 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
        = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2 : ℝ) : ℂ) •
            (1 : Matrix (Fin 4) (Fin 4) ℂ)
      ∧ diracHamiltonian4 p1 p2 p3 m * diracAlpha1
          - diracAlpha1 * diracHamiltonian4 p1 p2 p3 m
        = (2 : ℂ) • zitterVelocity1 p1 p2 p3 m
      ∧ diracHamiltonian4 p1 p2 p3 m * zitterVelocity1 p1 p2 p3 m
          - zitterVelocity1 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
        = (2 : ℂ) • (diracHamiltonian4 p1 p2 p3 m * zitterVelocity1 p1 p2 p3 m) :=
  ⟨diracHamiltonian4_sq p1 p2 p3 m, velocity_heisenberg_derivative p1 p2 p3 m,
    zitter_oscillation p1 p2 p3 m⟩

/-- The nonrelativistic spin branch reuses the existing Pauli identity, Heisenberg spin precession,
and Foldy-Wouthuysen Pauli spin-orbit term. -/
lemma nonrelativistic_pauli_symmetry_motion_core
    (hbar : ℂ) (m kinetic potential relCorr lapV : ℝ) (a b gradV p : Fin 3 → ℝ) :
    heisenbergGen hbar (sigmaDot a) (sigmaDot b) = ((-2 / hbar : ℂ)) • sigmaDot (crossR a b)
      ∧ Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator
          (sigmaDot gradV) (sigmaDot p) = (2 * I) • sigmaDot (crossR gradV p)
      ∧ pauliHamiltonianFW m kinetic potential relCorr lapV gradV p
          - ((kinetic + potential + relCorr + lapV / (8 * m ^ 2) : ℝ) : ℂ) •
              (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = ((1 / (4 * m ^ 2) : ℝ) : ℂ) • sigmaDot (crossR gradV p) :=
  ⟨heisenberg_spin_precession hbar a b, spinOrbit_from_commutator gradV p,
    pauliHamiltonianFW_spinOrbit m kinetic potential relCorr lapV gradV p⟩

/-- Pauli factorization behind the spinful Carroll-Schrodinger-Pauli branch:
`(sigma.p-lambda I)(sigma.p+lambda I)=(p^2-lambda^2)I`. -/
lemma sigmaDot_scalar_factorization (p : Fin 3 → ℝ) (lam : ℝ) :
    (sigmaDot p - (lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      * (sigmaDot p + (lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (((dotR p p - lam ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [sub_mul, mul_add, sigmaDot_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> ring

/-- Eq. (55) factorized through the existing Pauli identity. Setting
`lambda = 2aH^2`, the Carroll-Schrodinger-Pauli operator squares to the scalar dispersion obstruction
`p^2-lambda^2`. -/
lemma carrollSchrodingerPauli_factorization (a H : ℝ) (p : Fin 3 → ℝ) :
    carrollSchrodingerPauliOperator a H p
      * (sigmaDot p + ((2 * a * H ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (((dotR p p - (2 * a * H ^ 2) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold carrollSchrodingerPauliOperator
  exact sigmaDot_scalar_factorization p (2 * a * H ^ 2)

/-- Eq. (59): when the ultra-relativistic coefficient vanishes, the spinful Carroll-Schrodinger-Pauli
operator reduces to the Weyl/helicity operator `sigma.p`. -/
lemma carrollSchrodingerPauli_weyl_limit (H : ℝ) (p : Fin 3 → ℝ) :
    carrollSchrodingerPauliOperator 0 H p = sigmaDot p := by
  unfold carrollSchrodingerPauliOperator
  simp

/-- Eq. (54) evaluated with the existing Pauli commutator:
`-(i hbar / 2)[sigma.a, sigma.b] = hbar sigma.(a×b)`. -/
lemma rotationRestoringCoupling_eq_cross (hbar : ℝ) (a b : Fin 3 → ℝ) :
    rotationRestoringCoupling hbar a b = (hbar : ℂ) • sigmaDot (crossR a b) := by
  unfold rotationRestoringCoupling
  rw [spinOrbit_from_commutator, smul_smul]
  congr 1
  rw [show (-(I * (hbar : ℂ)) / 2) * (2 * I) = (hbar : ℂ) * (-(I * I)) by ring]
  simp [Complex.I_mul_I]

/-- Eq. (55) in kernel form: if a spinor is an eigenvector of `sigma.p` with eigenvalue
`2aH^2`, then the Carroll-Schrodinger-Pauli operator annihilates it. This is the algebraic
part of the helicity plane-wave discussion leading to Eq. (56). -/
lemma carrollSchrodingerPauliOperator_mulVec_eq_zero_of_sigmaDot_eigen
    (a H : ℝ) (p : Fin 3 → ℝ) (u : Fin 2 → ℂ)
    (hspin : (sigmaDot p).mulVec u = ((2 * a * H ^ 2 : ℝ) : ℂ) • u) :
    (carrollSchrodingerPauliOperator a H p).mulVec u = 0 := by
  unfold carrollSchrodingerPauliOperator
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hspin]
  simp

/-- Eq. (58) factorized through the existing Pauli identity after the ultra-boost potential shift. -/
lemma carrollSchrodingerPauliPotential_factorization
    (Q a c v H : ℝ) (phi p : Fin 3 → ℝ) :
    carrollSchrodingerPauliPotentialOperator Q a c v H phi p
      * (sigmaDot (carrollShiftedMomentum Q a c v H phi p)
          + ((2 * a * H ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (((dotR (carrollShiftedMomentum Q a c v H phi p)
              (carrollShiftedMomentum Q a c v H phi p)
            - (2 * a * H ^ 2) ^ 2 : ℝ) : ℂ)
          • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold carrollSchrodingerPauliPotentialOperator
  exact sigmaDot_scalar_factorization (carrollShiftedMomentum Q a c v H phi p) (2 * a * H ^ 2)

/-- With zero potential, the ultra-boost shifted momentum is the original momentum. -/
lemma carrollShiftedMomentum_zero_potential (Q a c v H : ℝ) (p : Fin 3 → ℝ) :
    carrollShiftedMomentum Q a c v H 0 p = p := by
  funext i
  simp [carrollShiftedMomentum]

/-- With zero potential, Eq. (58) reduces to the earlier Carroll-Schrodinger-Pauli operator. -/
lemma carrollSchrodingerPauliPotential_zero_potential
    (Q a c v H : ℝ) (p : Fin 3 → ℝ) :
    carrollSchrodingerPauliPotentialOperator Q a c v H 0 p
      = carrollSchrodingerPauliOperator a H p := by
  simp [carrollSchrodingerPauliPotentialOperator, carrollSchrodingerPauliOperator,
    carrollShiftedMomentum_zero_potential]

/-- Eq. (59): at zero ultra-relativistic coefficient, Eq. (58) reduces to the Weyl/helicity
operator `sigma.p`. -/
lemma carrollSchrodingerPauliPotential_weyl_limit
    (Q c v H : ℝ) (phi p : Fin 3 → ℝ) :
    carrollSchrodingerPauliPotentialOperator Q 0 c v H phi p = sigmaDot p := by
  unfold carrollSchrodingerPauliPotentialOperator carrollShiftedMomentum
  simp

end Physlib.QuantumMechanics.ComplexAction.Dirac.HeisenbergSymmetryMotion

end
