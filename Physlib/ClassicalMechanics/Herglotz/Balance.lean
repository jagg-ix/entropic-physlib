/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.Herglotz.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Noether–Herglotz balance law and the rescaled invariant

This module formalises the integrated form of the Noether–Herglotz theorem from
Simoes–Colombo, *Variational Dissipative Mechanics on Lie Algebroids* (2025),
Proposition 4.4 (eq. 23): an infinitesimal symmetry `σ` of a Herglotz Lagrangian
`L(q, q̇, z)` produces a momentum `J_σ` satisfying the first-order balance

  `J̇_σ = (∂L/∂z) · J_σ`,

and the **rescaled momentum** `exp(−∫₀ᵗ ∂L/∂z) · J_σ` is conserved along
solutions (the integrating-factor / dissipated-invariant form, Section 4 intro).
At `∂L/∂z = 0` the ordinary Noether conservation `J̇ = 0` is recovered
(Remark 4.5).

The same identity governs the Herglotz energy (`E` in place of `J_σ`,
Proposition 4.1, eq. 21), so this module's theorem covers *both* the
Noether–Herglotz momentum balance and the energy balance.

This is the abstract, scalar (TQ-special-case) form: the Lie-algebroid /
Euler–Poincaré / Atiyah / Wong generalisations in the paper are deliberately
*not* formalised here (Stage 1 of a staged port).

The entropic-time bridge — that the integrating-factor exponent is exactly the
accumulated entropic proper time — lives in
`Physlib.StatisticalMechanics.HerglotzEntropyTime`.

## References

- **Bartosiewicz & Torres 2008** — *Noether's theorem on time scales* [bib: `Bartosiewicz2008`]
- **Herglotz 1930** — *Berührungstransformationen (lectures)* [bib key needed: `Herglotz1930`]
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians* [bib key needed: `Lazo2018`]
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.ClassicalMechanics.Herglotz.Basic
namespace Physlib.ClassicalMechanics.Herglotz.Balance

/-- **Noether–Herglotz balance carrier.** Holds a (Noether / energy) charge `J`,
the contact derivative `α(t) = ∂L/∂z`, and the accumulator `A(t) = ∫₀ᵗ α(ω)dω`,
together with the two differential laws:

* `J̇(t) = α(t) · J(t)` — Noether–Herglotz balance law (Proposition 4.4 eq. 23,
  or Proposition 4.1 eq. 21 with `J = E`);
* `A'(t) = α(t)` — the accumulator integrates `α`.

The carrier does **not** assume a sign on `α`; the theorems below hold for any
`α` (the rescaled-invariant identity is sign-independent). The
entropic-time arrow needs `α ≤ 0` and is added separately in
`EntropyTime.lean`. -/
structure HerglotzNoetherBalance where
  /-- Conserved (in the conservative limit) Noether / energy charge. -/
  J : ℝ → ℝ
  /-- Contact derivative `α = ∂L/∂z` along the trajectory. -/
  alpha : ℝ → ℝ
  /-- Accumulator `A(t) = ∫₀ᵗ α(ω)dω`, equivalently `A' = α`. -/
  A : ℝ → ℝ
  /-- **Noether–Herglotz balance law** `J̇ = α·J` (Proposition 4.4, eq. 23). -/
  hasDerivAt_J : ∀ t, HasDerivAt J (alpha t * J t) t
  /-- The accumulator is an antiderivative of `α`. -/
  hasDerivAt_A : ∀ t, HasDerivAt A (alpha t) t

namespace HerglotzNoetherBalance

variable (B : HerglotzNoetherBalance)

/-- **Rescaled invariant (Noether–Herglotz, integrated form).** Multiplying the
balance-law charge by the integrating factor `exp(−A) = exp(−∫α)` produces a
*conserved* quantity along the trajectory: `d/dt[J(t) · exp(−A(t))] = 0`. -/
lemma rescaled_invariant_deriv_zero (t : ℝ) :
    HasDerivAt (fun s => B.J s * Real.exp (- B.A s)) 0 t := by
  have h1 : HasDerivAt (fun s => Real.exp (- B.A s))
      (Real.exp (- B.A t) * (- B.alpha t)) t :=
    (B.hasDerivAt_A t).neg.exp
  have h2 := (B.hasDerivAt_J t).mul h1
  exact h2.congr_deriv (by ring)

/-- **Ordinary Noether conservation recovered at zero defect** (Remark 4.5). With
`α ≡ 0` the rescaled invariant collapses to `J` itself, and `J` is conserved. -/
lemma hasDerivAt_J_zero_of_alpha_zero (hα : ∀ t, B.alpha t = 0) (t : ℝ) :
    HasDerivAt B.J 0 t := by
  have h := B.hasDerivAt_J t
  rw [hα t, zero_mul] at h
  simpa using h

end HerglotzNoetherBalance

end Physlib.ClassicalMechanics.Herglotz.Balance

end
