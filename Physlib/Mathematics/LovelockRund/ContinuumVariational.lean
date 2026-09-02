/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalFieldTheory.Local.Variation
public import Physlib.Mathematics.Calculus.Divergence
public import Physlib.Mathematics.VariationalCalculus.Basic
public import Physlib.Mathematics.VariationalCalculus.HasVarGradient

/-!
# Continuum variational principles and Noether balance

This module formalizes the continuum first-variation and conservation-law
layer of Lovelock--Rund Chapters 6 and 8. It reuses Physlib's existing compactly
supported local variations, variational gradients, fundamental lemma, and
divergence operator.

The spatial domain is `Space d`, an actual continuum. The field-value space
`U` is not required to be finite dimensional, so the same weak-variation API
applies to infinitely many internal field degrees of freedom.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open MeasureTheory InnerProductSpace InnerProductSpace'
open ClassicalFieldTheory.Local

variable {d : ℕ}
variable {U : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]

/-- Pairing of a pointwise variational gradient with a compactly supported
admissible variation. -/
def firstVariationPairing
    (grad : Space d → U) (η : AdmissibleVariation d U) : ℝ :=
  ∫ x, ⟪grad x, η x⟫_ℝ

/-- Weak stationarity: the first variation vanishes against every smooth,
compactly supported test variation. -/
def IsWeakExtremal (grad : Space d → U) : Prop :=
  ∀ η : AdmissibleVariation d U, firstVariationPairing grad η = 0

/-- The continuum fundamental lemma: for a continuous gradient, weak
stationarity is equivalent to pointwise vanishing of the Euler--Lagrange
field. -/
theorem isWeakExtremal_iff_eq_zero
    (grad : Space d → U) (hgrad : Continuous grad) :
    IsWeakExtremal grad ↔ grad = 0 := by
  constructor
  · intro hweak
    apply fundamental_theorem_of_variational_calculus'
      (μ := volume) hgrad
    intro η hη
    exact hweak ⟨η, hη⟩
  · intro hzero η
    rw [hzero]
    simp [firstVariationPairing]

/-- Weak stationarity of the variational gradient attached to a Physlib
functional is equivalent to the vanishing of any known continuous gradient. -/
theorem hasVarGradient_weakExtremal_iff
    (F : (Space d → U) → (Space d → ℝ))
    (grad : Space d → U) (u : Space d → U)
    (hF : HasVarGradientAt F grad u)
    (hgrad : Continuous grad) :
    IsWeakExtremal (varGradient F u) ↔ grad = 0 := by
  rw [HasVarGradientAt.varGradient F grad u hF]
  exact isWeakExtremal_iff_eq_zero grad hgrad

/-- First-order field Euler--Lagrange residual
`∂L/∂u - div (∂L/∂(∇u))`. -/
def firstOrderEulerLagrange
    (dLdu : Space d → ℝ)
    (fieldMomentum : Space d → Space d) : Space d → ℝ :=
  fun x => dLdu x - divergence ℝ fieldMomentum x

/-- Pointwise Euler--Lagrange equation in divergence form. -/
theorem firstOrderEulerLagrange_eq_zero_iff
    (dLdu : Space d → ℝ)
    (fieldMomentum : Space d → Space d) (x : Space d) :
    firstOrderEulerLagrange dLdu fieldMomentum x = 0 ↔
      dLdu x = divergence ℝ fieldMomentum x := by
  simp [firstOrderEulerLagrange, sub_eq_zero]

/-- Data for a local Noether identity. The divergence of the current equals
an Euler--Lagrange residual paired with the infinitesimal characteristic of
the symmetry. -/
structure NoetherCurrentData where
  /-- Euler--Lagrange residual. -/
  eulerLagrange : Space d → U
  /-- Infinitesimal symmetry characteristic. -/
  characteristic : Space d → U
  /-- Pointwise Noether current. -/
  current : Space d → Space d
  /-- Local Noether identity. -/
  identity : ∀ x,
    divergence ℝ current x =
      ⟪eulerLagrange x, characteristic x⟫_ℝ

namespace NoetherCurrentData

/-- On shell, a local Noether current is pointwise divergence free. -/
theorem divergence_eq_zero
    (N : NoetherCurrentData (d := d) (U := U))
    (hEL : N.eulerLagrange = 0) :
    divergence ℝ N.current = 0 := by
  funext x
  rw [N.identity]
  simp [hEL]

/-- On shell, the integrated divergence of the Noether current vanishes. -/
theorem integral_divergence_eq_zero
    (N : NoetherCurrentData (d := d) (U := U))
    (hEL : N.eulerLagrange = 0) :
    ∫ x, divergence ℝ N.current x = 0 := by
  rw [N.divergence_eq_zero hEL]
  simp

/-- A symmetry whose characteristic vanishes produces an identically
conserved current without imposing the equations of motion. -/
theorem divergence_eq_zero_of_characteristic_zero
    (N : NoetherCurrentData (d := d) (U := U))
    (hchar : N.characteristic = 0) :
    divergence ℝ N.current = 0 := by
  funext x
  rw [N.identity]
  simp [hchar]

end NoetherCurrentData

/-- Pointwise balance-law data. This is useful for dissipative or complex-action
extensions where the Noether current has a nonzero source. -/
structure BalanceLawData where
  current : Space d → Space d
  source : Space d → ℝ
  balance : ∀ x, divergence ℝ current x = source x

namespace BalanceLawData

/-- A source-free balance law is a conservation law. -/
theorem divergence_eq_zero
    (B : BalanceLawData (d := d)) (hsource : B.source = 0) :
    divergence ℝ B.current = 0 := by
  funext x
  rw [B.balance]
  simp [hsource]

end BalanceLawData

end Physlib.Mathematics.LovelockRund

end
