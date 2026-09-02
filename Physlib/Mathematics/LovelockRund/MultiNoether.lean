/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.ContinuumVariational

/-!
# Multi-parameter Noether current families

Lovelock--Rund Section 6.6 proves Noether's theorem for multiple integrals and
an arbitrary `r`-parameter transformation group. Each independent parameter
produces one current whose divergence is proportional to the Euler--Lagrange
residual.

This module encodes the parameter family with an arbitrary type `A`. No
finiteness assumption is imposed on the symmetry-parameter family.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open InnerProductSpace InnerProductSpace'

variable {d : ℕ}
variable {U : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]

/-- A family of local Noether identities indexed by arbitrary symmetry
parameters. -/
structure MultiNoetherCurrentData (A : Type*) where
  /-- Common Euler--Lagrange residual. -/
  eulerLagrange : Space d → U
  /-- Infinitesimal characteristic associated with each parameter. -/
  characteristic : A → Space d → U
  /-- Noether current associated with each parameter. -/
  current : A → Space d → Space d
  /-- Local Noether identity for each parameter. -/
  identity : ∀ a x,
    divergence ℝ (current a) x =
      ⟪eulerLagrange x, characteristic a x⟫_ℝ

namespace MultiNoetherCurrentData

variable {A : Type*}

/-- On shell, every current in an arbitrary parameter family is divergence
free. -/
theorem divergence_eq_zero
    (N : MultiNoetherCurrentData (d := d) (U := U) A)
    (hEL : N.eulerLagrange = 0) :
    ∀ a, divergence ℝ (N.current a) = 0 := by
  intro a
  funext x
  rw [N.identity]
  simp [hEL]

/-- Pointwise form of simultaneous conservation. -/
theorem divergence_apply_eq_zero
    (N : MultiNoetherCurrentData (d := d) (U := U) A)
    (hEL : N.eulerLagrange = 0) (a : A) (x : Space d) :
    divergence ℝ (N.current a) x = 0 := by
  exact congrFun (N.divergence_eq_zero hEL a) x

/-- Every current has zero integrated divergence on shell. -/
theorem integral_divergence_eq_zero
    (N : MultiNoetherCurrentData (d := d) (U := U) A)
    (hEL : N.eulerLagrange = 0) (a : A) :
    ∫ x, divergence ℝ (N.current a) x = 0 := by
  rw [N.divergence_eq_zero hEL a]
  simp

/-- The one-parameter Noether carrier is the specialization to `Unit`. -/
def toSingle
    (N : MultiNoetherCurrentData (d := d) (U := U) Unit) :
    NoetherCurrentData (d := d) (U := U) where
  eulerLagrange := N.eulerLagrange
  characteristic := N.characteristic ()
  current := N.current ()
  identity := N.identity ()

/-- Conservation of the `Unit`-indexed family agrees with conservation of its
single-current specialization. -/
theorem toSingle_divergence_eq_zero
    (N : MultiNoetherCurrentData (d := d) (U := U) Unit)
    (hEL : N.eulerLagrange = 0) :
    divergence ℝ N.toSingle.current = 0 :=
  N.divergence_eq_zero hEL ()

/-- Restriction of a Noether family along a parameter map. -/
def reindex {B : Type*}
    (N : MultiNoetherCurrentData (d := d) (U := U) A)
    (f : B → A) : MultiNoetherCurrentData (d := d) (U := U) B where
  eulerLagrange := N.eulerLagrange
  characteristic := fun b => N.characteristic (f b)
  current := fun b => N.current (f b)
  identity := fun b => N.identity (f b)

/-- Reindexing preserves the local Noether identity definitionally. -/
@[simp] theorem reindex_identity {B : Type*}
    (N : MultiNoetherCurrentData (d := d) (U := U) A)
    (f : B → A) (b : B) (x : Space d) :
    divergence ℝ ((N.reindex f).current b) x =
      ⟪(N.reindex f).eulerLagrange x,
        (N.reindex f).characteristic b x⟫_ℝ :=
  (N.reindex f).identity b x

/-- Any subfamily of an on-shell conserved family remains conserved. -/
theorem reindex_divergence_eq_zero {B : Type*}
    (N : MultiNoetherCurrentData (d := d) (U := U) A)
    (f : B → A) (hEL : N.eulerLagrange = 0) :
    ∀ b, divergence ℝ ((N.reindex f).current b) = 0 := by
  intro b
  exact N.divergence_eq_zero hEL (f b)

end MultiNoetherCurrentData

end Physlib.Mathematics.LovelockRund

end
