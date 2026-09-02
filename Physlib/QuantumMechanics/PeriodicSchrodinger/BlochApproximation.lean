/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.DirectionalPotential
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Bloch coefficient localization

Veliev's simple-set arguments prove that a normalized Bloch eigenfunction is
concentrated at one distinguished free or directional mode. This file
formalizes the coefficient-level conclusion independently of the analytic
estimates used to establish it.

For a finite truncation, the phase-aligned squared distance is

`|b(main)-1|² + Σ_{j ≠ main} |b(j)|²`.

For an arbitrary, possibly infinite, mode type, the tail is represented by a
`tsum`. Thus the same interface can consume finite Galerkin estimates or a
summable full Bloch expansion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

open scoped BigOperators

/-! ## Finite mode truncations -/

/-- Squared coefficient mass outside a distinguished finite mode. -/
def finiteTailMass {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase main, ‖b j‖ ^ 2

/-- Squared phase-aligned coefficient distance from the distinguished basis
mode. -/
def finiteBlochDistanceSq {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) : ℝ :=
  ‖b main - 1‖ ^ 2 + finiteTailMass b main

/-- Finite tail mass is nonnegative. -/
theorem finiteTailMass_nonneg {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) :
    0 ≤ finiteTailMass b main := by
  unfold finiteTailMass
  positivity

/-- Phase-aligned distance is nonnegative. -/
theorem finiteBlochDistanceSq_nonneg {n : ℕ}
  (b : Fin n → ℂ) (main : Fin n) :
    0 ≤ finiteBlochDistanceSq b main := by
  unfold finiteBlochDistanceSq
  exact add_nonneg (sq_nonneg _) (finiteTailMass_nonneg b main)

/-- The tail is bounded by the full phase-aligned distance. -/
theorem finiteTailMass_le_distance {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) :
    finiteTailMass b main ≤ finiteBlochDistanceSq b main := by
  unfold finiteBlochDistanceSq
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The distinguished coefficient error is bounded by the full distance. -/
theorem mainCoefficientErrorSq_le_distance {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) :
    ‖b main - 1‖ ^ 2 ≤ finiteBlochDistanceSq b main := by
  unfold finiteBlochDistanceSq
  exact le_add_of_nonneg_right (finiteTailMass_nonneg b main)

/-- Finite Bloch localization at accuracy `ε`. -/
def IsFiniteBlochLocalized {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) (ε : ℝ) : Prop :=
  finiteBlochDistanceSq b main ≤ ε ^ 2

/-- Bloch localization controls the off-mode tail. -/
theorem finiteTailMass_le_of_localized {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) {ε : ℝ}
    (h : IsFiniteBlochLocalized b main ε) :
    finiteTailMass b main ≤ ε ^ 2 :=
  (finiteTailMass_le_distance b main).trans h

/-- Bloch localization controls the distinguished coefficient error. -/
theorem mainCoefficientErrorSq_le_of_localized {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) {ε : ℝ}
    (h : IsFiniteBlochLocalized b main ε) :
    ‖b main - 1‖ ^ 2 ≤ ε ^ 2 :=
  (mainCoefficientErrorSq_le_distance b main).trans h

/-- Exact localization means coefficient one at the distinguished mode and
zero finite tail. -/
theorem finiteBlochDistanceSq_eq_zero_iff {n : ℕ}
    (b : Fin n → ℂ) (main : Fin n) :
    finiteBlochDistanceSq b main = 0 ↔
      b main = 1 ∧ finiteTailMass b main = 0 := by
  constructor
  · intro h
    have hmain : ‖b main - 1‖ ^ 2 = 0 := by
      have hle := mainCoefficientErrorSq_le_distance b main
      rw [h] at hle
      exact le_antisymm hle (sq_nonneg _)
    have htail : finiteTailMass b main = 0 := by
      have hle := finiteTailMass_le_distance b main
      rw [h] at hle
      exact le_antisymm hle (finiteTailMass_nonneg b main)
    have hnorm : ‖b main - 1‖ = 0 := by
      nlinarith [norm_nonneg (b main - 1)]
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hnorm), htail⟩
  · rintro ⟨hmain, htail⟩
    simp [finiteBlochDistanceSq, hmain, htail]

/-! ## Infinite reciprocal-mode expansions -/

variable {A : Type*} [DecidableEq A]

/-- Squared coefficient tail over an arbitrary, possibly infinite, mode type. -/
def infiniteTailMass
    (b : A → ℂ) (main : A) : ℝ :=
  ∑' a, if a = main then 0 else ‖b a‖ ^ 2

/-- Summability requirement for an infinite Bloch coefficient tail. -/
def HasSummableBlochTail
    (b : A → ℂ) (main : A) : Prop :=
  Summable fun a => if a = main then 0 else ‖b a‖ ^ 2

/-- Infinite phase-aligned squared distance. -/
def infiniteBlochDistanceSq
    (b : A → ℂ) (main : A) : ℝ :=
  ‖b main - 1‖ ^ 2 + infiniteTailMass b main

/-- Infinite tail mass is nonnegative. -/
theorem infiniteTailMass_nonneg
    (b : A → ℂ) (main : A) :
    0 ≤ infiniteTailMass b main := by
  unfold infiniteTailMass
  exact tsum_nonneg fun a => by
    split_ifs
    · exact le_rfl
    · positivity

/-- Infinite Bloch distance is nonnegative. -/
theorem infiniteBlochDistanceSq_nonneg
    (b : A → ℂ) (main : A) :
    0 ≤ infiniteBlochDistanceSq b main := by
  unfold infiniteBlochDistanceSq
  exact add_nonneg (sq_nonneg _) (infiniteTailMass_nonneg b main)

/-- The infinite tail is bounded by the full phase-aligned distance. -/
theorem infiniteTailMass_le_distance
    (b : A → ℂ) (main : A) :
    infiniteTailMass b main ≤ infiniteBlochDistanceSq b main := by
  unfold infiniteBlochDistanceSq
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Infinite Bloch localization at accuracy `ε`. -/
def IsInfiniteBlochLocalized
    (b : A → ℂ) (main : A) (ε : ℝ) : Prop :=
  HasSummableBlochTail b main ∧
    infiniteBlochDistanceSq b main ≤ ε ^ 2

/-- Infinite localization controls the entire summable off-mode tail. -/
theorem infiniteTailMass_le_of_localized
    (b : A → ℂ) (main : A) {ε : ℝ}
    (h : IsInfiniteBlochLocalized b main ε) :
    infiniteTailMass b main ≤ ε ^ 2 :=
  (infiniteTailMass_le_distance b main).trans h.2

/-- A coefficient family supported exactly at the distinguished mode has zero
infinite tail. -/
theorem infiniteTailMass_eq_zero_of_supported
    (b : A → ℂ) (main : A)
    (hoff : ∀ a, a ≠ main → b a = 0) :
    infiniteTailMass b main = 0 := by
  unfold infiniteTailMass
  calc
    (∑' a, if a = main then 0 else ‖b a‖ ^ 2) = ∑' _a : A, 0 :=
      tsum_congr fun a => by
        by_cases ha : a = main
        · simp [ha]
        · simp [ha, hoff a ha]
    _ = 0 := tsum_zero

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
