/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction

/-!
# Binary-icosahedral action on quaternionic Pauli and Dirac spinors

The exact binary icosahedral group `2I` is already constructed in
`CliffordRootSystemInduction` as the 120 norm-one quaternions over `Q(sqrt 5)`.
A quaternion is one two-component complex spinor.  A pair of quaternions is
therefore a four-component Dirac spinor.  This module defines the concrete `2I`
action on both carriers and proves norm preservation and central-sign descent
of their quadratic observables.
-/

set_option autoImplicit false
open scoped BigOperators Quaternion

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor

open Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction

/-- One quaternionic Pauli spinor, equivalent to two complex components. -/
abbrev BinarySpinor := ℍ[ℝ]

/-- Two quaternionic Pauli blocks, equivalent to a four-component Dirac spinor. -/
abbrev BinaryDiracSpinor := Fin 2 → BinarySpinor

/-- A concrete `2I` element acts on a Pauli spinor by left quaternion multiplication. -/
noncomputable def binarySpinorAction
    (g : BinaryIcosahedralGroup) (psi : BinarySpinor) : BinarySpinor :=
  h4QuaternionToReal g.1 * psi

@[simp] theorem binarySpinorAction_one (psi : BinarySpinor) :
    binarySpinorAction 1 psi = psi := by
  simp [binarySpinorAction]

/-- The concrete left action respects the `2I` group law. -/
theorem binarySpinorAction_mul
    (g h : BinaryIcosahedralGroup) (psi : BinarySpinor) :
    binarySpinorAction (g * h) psi = binarySpinorAction g (binarySpinorAction h psi) := by
  simp only [binarySpinorAction, BinaryIcosahedralGroup.coe_mul, h4QuaternionToReal_mul]
  rw [mul_assoc]

/-- Every concrete binary-icosahedral transformation preserves the Pauli-spinor norm. -/
theorem binarySpinorAction_normSq
    (g : BinaryIcosahedralGroup) (psi : BinarySpinor) :
    Quaternion.normSq (binarySpinorAction g psi) = Quaternion.normSq psi := by
  exact binaryIcosahedralGroup_toReal_leftMul_normSq g psi

/-- The central element sends the Pauli spinor to the negative transformed spinor. -/
theorem binarySpinorAction_neg
    (g : BinaryIcosahedralGroup) (psi : BinarySpinor) :
    binarySpinorAction (-g) psi = - binarySpinorAction g psi := by
  simp [binarySpinorAction, BinaryIcosahedralGroup.coe_neg, h4QuaternionToReal_neg]

/-- The quadratic density carried by one quaternionic Pauli spinor. -/
noncomputable def spinorDensity (psi : BinarySpinor) : ℝ := Quaternion.normSq psi

/-- The central pair `g` and `-g` gives the same Pauli-spinor density. -/
theorem central_pair_same_density
    (g : BinaryIcosahedralGroup) (psi : BinarySpinor) :
    spinorDensity (binarySpinorAction (-g) psi)
      = spinorDensity (binarySpinorAction g psi) := by
  unfold spinorDensity
  calc
    Quaternion.normSq (binarySpinorAction (-g) psi) = Quaternion.normSq psi :=
      binarySpinorAction_normSq (-g) psi
    _ = Quaternion.normSq (binarySpinorAction g psi) :=
      (binarySpinorAction_normSq g psi).symm

/-- The componentwise `2I` action on a four-component Dirac spinor. -/
noncomputable def binaryDiracSpinorAction
    (g : BinaryIcosahedralGroup) (psi : BinaryDiracSpinor) : BinaryDiracSpinor :=
  fun block => binarySpinorAction g (psi block)

@[simp] theorem binaryDiracSpinorAction_one (psi : BinaryDiracSpinor) :
    binaryDiracSpinorAction 1 psi = psi := by
  funext block
  simp [binaryDiracSpinorAction]

/-- The Dirac-spinor action respects multiplication in the concrete `2I` group. -/
theorem binaryDiracSpinorAction_mul
    (g h : BinaryIcosahedralGroup) (psi : BinaryDiracSpinor) :
    binaryDiracSpinorAction (g * h) psi
      = binaryDiracSpinorAction g (binaryDiracSpinorAction h psi) := by
  funext block
  exact binarySpinorAction_mul g h (psi block)

/-- The central sign negates the complete four-component Dirac spinor. -/
theorem binaryDiracSpinorAction_neg
    (g : BinaryIcosahedralGroup) (psi : BinaryDiracSpinor) :
    binaryDiracSpinorAction (-g) psi = - binaryDiracSpinorAction g psi := by
  funext block
  exact binarySpinorAction_neg g (psi block)

/-- Total four-spinor density: the sum of the two quaternionic block norms. -/
noncomputable def diracSpinorDensity (psi : BinaryDiracSpinor) : ℝ :=
  ∑ block, spinorDensity (psi block)

/-- Every concrete `2I` element preserves the complete Dirac-spinor density. -/
theorem binaryDiracSpinorAction_density
    (g : BinaryIcosahedralGroup) (psi : BinaryDiracSpinor) :
    diracSpinorDensity (binaryDiracSpinorAction g psi) = diracSpinorDensity psi := by
  unfold diracSpinorDensity binaryDiracSpinorAction spinorDensity
  apply Finset.sum_congr rfl
  intro block _
  exact binarySpinorAction_normSq g (psi block)

/-- The central pair `g` and `-g` descends to the same complete Dirac density,
    giving the quadratic `2I -> A5` observable quotient on the four-spinor. -/
theorem central_pair_same_dirac_density
    (g : BinaryIcosahedralGroup) (psi : BinaryDiracSpinor) :
    diracSpinorDensity (binaryDiracSpinorAction (-g) psi)
      = diracSpinorDensity (binaryDiracSpinorAction g psi) := by
  rw [binaryDiracSpinorAction_density, binaryDiracSpinorAction_density]

/-- The concrete binary-icosahedral four-spinor action and its bilinear descent
    as one theorem-facing package. -/
theorem binary_icosahedral_dirac_spinor_assembly
    (g : BinaryIcosahedralGroup) (psi : BinaryDiracSpinor) :
    diracSpinorDensity (binaryDiracSpinorAction g psi) = diracSpinorDensity psi
      ∧ binaryDiracSpinorAction (-g) psi = - binaryDiracSpinorAction g psi
      ∧ diracSpinorDensity (binaryDiracSpinorAction (-g) psi)
          = diracSpinorDensity (binaryDiracSpinorAction g psi) :=
  ⟨binaryDiracSpinorAction_density g psi,
    binaryDiracSpinorAction_neg g psi,
    central_pair_same_dirac_density g psi⟩

end Physlib.QuantumMechanics.ComplexAction.BinaryIcosahedralDiracSpinor
