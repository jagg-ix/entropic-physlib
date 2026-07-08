/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Herglotz dissipation coefficient

In a Herglotz-type variational principle with action variable `z` satisfying
`ż = L(q, q̇, z)` (Simoes–Colombo, *Variational Dissipative Mechanics on Lie
Algebroids*, 2025, Section 4), the dissipation is governed by the contact
derivative `α(t) := ∂L/∂z` evaluated along the trajectory. The Rayleigh /
second-law sign convention is `α ≤ 0`, equivalently `λ := −α ≥ 0` is the
non-negative entropy-production rate.

This module fixes that structure. The balance / integrating-factor theorems
live in `Balance.lean`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.ClassicalMechanics.Herglotz.Basic

/-- **Herglotz dissipation coefficient** evaluated along a trajectory: the contact
derivative `α(t) = ∂L/∂z` of the Herglotz Lagrangian. The Rayleigh /
second-law sign is `α ≤ 0`. -/
structure HerglotzDissipation where
  /-- `α(t) = ∂L/∂z` along the trajectory. -/
  alpha : ℝ → ℝ
  /-- Dissipation sign (Rayleigh / second-law convention): `∂L/∂z ≤ 0`. -/
  alpha_nonpos : ∀ t, alpha t ≤ 0

namespace HerglotzDissipation

variable (D : HerglotzDissipation)

/-- Dissipation rate `λ := −α ≥ 0`. -/
def lambda (t : ℝ) : ℝ := - D.alpha t

theorem lambda_nonneg (t : ℝ) : 0 ≤ D.lambda t := by
  unfold lambda; linarith [D.alpha_nonpos t]

theorem lambda_eq_neg_alpha (t : ℝ) : D.lambda t = - D.alpha t := rfl

end HerglotzDissipation

end Physlib.ClassicalMechanics.Herglotz.Basic

end
