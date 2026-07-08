/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.DissipativeMechanics

/-!
# Entropic action principle — frozen-LRF residue of total action

Phase 4 of the counterpart program (A3 + A7).  In the entropic-time
framework the complete action records both a classical (real) part and
an entropic (imaginary) part:

  `S_total  =  S_classical  +  S_entropic`,

where `S_classical = ∫L dt` is the standard Lagrangian action and
`S_entropic = S_I = ℏ · τ_ent` is the imaginary-action contribution
driving entropy production.  At the **frozen LRF** the entropic part
vanishes (`S_I = 0`), so the total action reduces to the classical
action — and stationary points of the total action coincide with
stationary points of the classical action (standard Hamilton's
principle).

This module defines an `EntropicAction` structure and the two recovery
theorems:

* **A3 — `total_eq_classical_at_zero_entropic`** — at zero entropic
  contribution the total action is just the classical action.
* **A7 — `stationary_total_at_frozen_iff_classical_EL`** — given a
  `DissipativeEulerLagrangeSystem`, stationary points of the total
  action coincide with classical EL stationary points iff the
  dissipative force vanishes (the principle of least action recovers
  its standard form).

These complete the classical-mechanics half of the counterpart
program at the *action-functional* level.


## References

- **Bartosiewicz & Torres 2008** — *Noether's theorem on time scales*
- **Herglotz 1930** — *Berührungstransformationen (lectures)*
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians*
- **Noether 1918** — *Invariante Variationsprobleme*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.ClassicalMechanics.ActionPrinciple

open Physlib.ClassicalMechanics.DissipativeMechanics Time

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **Total action structure.**  Two real numbers `classical` and
`entropic`; the total action `total` is their sum.  In the full
entropic-time picture `classical = ∫L dt` and `entropic = ℏ · τ_ent`
(or `= S_I`); the structure abstracts those concrete definitions so we
can state the recovery theorem without dragging in measure-theoretic
infrastructure. -/
structure EntropicAction where
  /-- Classical (Lagrangian) action `S_classical = ∫L dt`. -/
  classical : ℝ
  /-- Entropic (imaginary) action `S_entropic = S_I = ℏ · τ_ent`,
  non-negative. -/
  entropic : ℝ
  /-- Entropic contribution is non-negative (operational second law). -/
  entropic_nonneg : 0 ≤ entropic

namespace EntropicAction

variable (A : EntropicAction)

/-- **Total action**: classical + entropic. -/
def total : ℝ := A.classical + A.entropic

@[simp] theorem total_def : A.total = A.classical + A.entropic := rfl

/-- **A3 — Action principle at frozen LRF.**  When the entropic
contribution vanishes (frozen LRF / reversible regime), the total
action equals the classical action.  The entropic-time identification
of the standard Lagrangian action as the *frozen-LRF residue* of the
complete (entropy-augmented) action. -/
theorem total_eq_classical_at_zero_entropic (h : A.entropic = 0) :
    A.total = A.classical := by
  simp [h]

/-- The total action is always at least the classical action (the
entropic contribution is non-negative). -/
theorem total_ge_classical : A.classical ≤ A.total := by
  have := A.entropic_nonneg
  simp [total]; linarith

/-- The total action equals the classical action **iff** the entropic
contribution vanishes — the iff version of A3. -/
theorem total_eq_classical_iff_zero_entropic :
    A.total = A.classical ↔ A.entropic = 0 := by
  unfold total
  constructor
  · intro h; linarith
  · intro h; linarith

end EntropicAction

/-! ## A7 — Stationary action principle at zero dissipation -/

/-- **A7 — Hamilton's principle of stationary action at zero
dissipation.**  Given a `DissipativeEulerLagrangeSystem`, the trajectory
satisfies the *standard* Euler-Lagrange equations (i.e., is a
stationary point of the *classical* action) iff the dissipative
force vanishes identically.

This is the action-principle form of the equality case: stationary
points of the *total* action coincide with stationary points
of the *classical* action exactly when the entropic contribution is
inactive — the principle of least action recovers its standard
Hamiltonian form at the frozen LRF. -/
theorem stationary_total_at_frozen_iff_classical_EL
    (S : DissipativeEulerLagrangeSystem X) :
    (_root_.ClassicalMechanics.eulerLagrangeOp S.L S.q = fun _ => 0)
      ↔ (∀ t, S.dissipativeForce t = 0) := by
  constructor
  · intro hEL t
    have hb := S.balance
    have : S.dissipativeForce t = (fun _ : Time => (0 : X)) t := by
      rw [← hb, hEL]
    simpa using this
  · intro hzero
    exact S.eulerLagrange_at_zero_dissipation hzero

end Physlib.ClassicalMechanics.ActionPrinciple

end
