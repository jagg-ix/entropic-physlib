/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.BindingFormula
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite resonance matrices

Near an intersection of diffraction hyperplanes, Veliev replaces the free
Bloch eigenvalue by an eigenvalue of a finite matrix.  Its diagonal entries are
free mode energies and its off-diagonal entries are Fourier coefficients of
the periodic potential.

This file formalizes that finite reduction exactly.  It proves the coordinate
matrix action, the component eigenvalue equation, Hermitian symmetry under the
usual Fourier reality condition, and an explicit residual carrier.  No
approximate spectral theorem is assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

open scoped BigOperators Matrix

variable {n : ℕ}

/-- Finite resonance matrix with real diagonal energy and off-diagonal Fourier
coupling. -/
def resonanceMatrix
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then energy i else coupling i j

@[simp] theorem resonanceMatrix_diag
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ) (i : Fin n) :
    resonanceMatrix energy coupling i i = energy i := by
  simp [resonanceMatrix]

@[simp] theorem resonanceMatrix_offDiag
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    {i j : Fin n} (hij : i ≠ j) :
    resonanceMatrix energy coupling i j = coupling i j := by
  simp [resonanceMatrix, hij]

/-- Coordinate action of the finite resonance matrix. -/
def resonanceAction
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (v : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ∑ j, resonanceMatrix energy coupling i j * v j

/-- Matrix multiplication agrees exactly with the coordinate resonance
action. -/
theorem resonanceMatrix_mulVec
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (v : Fin n → ℂ) :
    Matrix.mulVec (resonanceMatrix energy coupling) v =
      resonanceAction energy coupling v := by
  funext i
  rfl

/-- Eigenpair equation for the finite resonance problem. -/
def IsResonanceEigenpair
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (Λ : ℂ) (v : Fin n → ℂ) : Prop :=
  Matrix.mulVec (resonanceMatrix energy coupling) v = Λ • v

/-- Componentwise form of the resonance eigenvalue equation. -/
theorem isResonanceEigenpair_iff
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (Λ : ℂ) (v : Fin n → ℂ) :
    IsResonanceEigenpair energy coupling Λ v ↔
      ∀ i, ∑ j, resonanceMatrix energy coupling i j * v j =
        Λ * v i := by
  constructor
  · intro h i
    have hi := congrFun h i
    simpa [IsResonanceEigenpair, Matrix.mulVec, dotProduct, Pi.smul_apply] using hi
  · intro h
    funext i
    simpa [IsResonanceEigenpair, Matrix.mulVec, dotProduct, Pi.smul_apply] using h i

/-- Residual of an approximate resonance eigenpair. -/
def resonanceResidual
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (Λ : ℂ) (v : Fin n → ℂ) : Fin n → ℂ :=
  Matrix.mulVec (resonanceMatrix energy coupling) v - Λ • v

/-- Vanishing residual is equivalent to the exact resonance eigenpair
equation. -/
theorem resonanceResidual_eq_zero_iff
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (Λ : ℂ) (v : Fin n → ℂ) :
    resonanceResidual energy coupling Λ v = 0 ↔
      IsResonanceEigenpair energy coupling Λ v := by
  simp [resonanceResidual, IsResonanceEigenpair, sub_eq_zero]

/-- Pointwise norm bound for an approximate resonance eigenpair. -/
def HasResonanceResidualBound
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (Λ : ℂ) (v : Fin n → ℂ) (ε : ℝ) : Prop :=
  ∀ i, ‖resonanceResidual energy coupling Λ v i‖ ≤ ε

/-- Exact eigenpairs have every nonnegative residual bound. -/
theorem hasResonanceResidualBound_of_eigenpair
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (Λ : ℂ) (v : Fin n → ℂ)
    (hpair : IsResonanceEigenpair energy coupling Λ v)
    {ε : ℝ} (hε : 0 ≤ ε) :
    HasResonanceResidualBound energy coupling Λ v ε := by
  have hz : resonanceResidual energy coupling Λ v = 0 :=
    (resonanceResidual_eq_zero_iff energy coupling Λ v).2 hpair
  intro i
  have hi : resonanceResidual energy coupling Λ v i = 0 := by
    simpa only [Pi.zero_apply] using congrFun hz i
  rw [hi, norm_zero]
  exact hε

/-- Fourier reality condition for a finite coupling matrix. -/
def IsHermitianCoupling
    (coupling : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j, star (coupling j i) = coupling i j

/-- Real diagonal energies and Hermitian Fourier couplings produce a Hermitian
resonance matrix. -/
theorem resonanceMatrix_isHermitian
    (energy : Fin n → ℝ)
    (coupling : Fin n → Fin n → ℂ)
    (hcoupling : IsHermitianCoupling coupling) :
    (resonanceMatrix energy coupling).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [resonanceMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [resonanceMatrix, hij, hji, hcoupling i j]

/-- A Fourier coefficient family satisfying `q(-η)=conj(q η)` induces a
Hermitian difference coupling. -/
theorem differenceCoupling_isHermitian
    {Γ : Type*} [AddCommGroup Γ]
    (mode : Fin n → Γ) (q : Γ → ℂ)
    (hq : ∀ η, star (q η) = q (-η)) :
    IsHermitianCoupling (fun i j => q (mode i - mode j)) := by
  intro i j
  rw [hq]
  congr 1
  simp [sub_eq_add_neg, add_comm]

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
