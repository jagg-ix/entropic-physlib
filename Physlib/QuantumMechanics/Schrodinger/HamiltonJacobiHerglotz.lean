/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Schrodinger.HamiltonJacobiMadelung
public import Physlib.ClassicalMechanics.HerglotzLazoContact

/-!
# de Broglie–Bohm mechanics is the conservative (frictionless) slice of Herglotz contact mechanics

Links the quantum Hamilton–Jacobi–Madelung equation (`HamiltonJacobiMadelung`) to the Herglotz–Lazo contact
mechanics of classical mechanics (`ClassicalMechanics.HerglotzLazoContact`).

**The physically valid statement — and the one that is *not*.** Herglotz contact mechanics records genuine
dissipation in the contact term `ρ·s` of `L_eff = L_R − ρ·s` (`ρ` = contact-friction coefficient, `s` =
accumulated imaginary action), e.g. the damped oscillator `m ẍ + k x = −γẋ` with `ρ = γ/m ≠ 0`. The de
Broglie–Bohm quantum Hamilton–Jacobi equation `∂tS + |∇S|²/(2m) + V + Q = 0` describes **unitary,
conservative, time-reversible** evolution: the quantum potential `Q = −ℏ²ΔR/(2mR)` is a *conservative*
contribution (`V + Q` is a potential energy, and the effective Hamiltonian `½m‖v‖² + V + Q` is independent of
the action `S` itself). It would therefore be **physically wrong** to identify `Q` with a Herglotz friction
term.

The *correct* link is the reverse: Bohmian mechanics is the **conservative / reversible slice** of Herglotz
contact mechanics — `ρ = 0` (no contact friction) and `s = 0` (the wavefunction `ψ = R·e^{iS/ℏ}` has no
imaginary action). The quantum potential sits entirely in the **reversible** Lagrangian `L_R = ½m‖v‖² −
(V + Q)` (kinetic minus the conservative effective potential, with `v` the guidance velocity), and the
effective Herglotz Lagrangian reduces to it (`bohm_herglotz_frictionless`, `bohm_herglotz_zero_action`). This
is exactly the reversible limit where Herglotz contact mechanics collapses to conservative Hamilton flow — and
it *distinguishes* Bohmian mechanics from the dissipative `ρ ≠ 0` systems (`dampedOscillatorContactSlice`).

* **§A — the reversible Bohm Lagrangian and its Herglotz slice** (`bohmReversibleLagrangian`,
  `bohmHerglotzSlice`).
* **§B — the frictionless / conservative reductions** (`bohm_herglotz_frictionless`,
  `bohm_herglotz_zero_action`, `freeParticle_bohmReversibleLagrangian`).

## References

* G. Herglotz (1930); D. Bohm (1952). structure: `Physlib`
  (`HamiltonJacobiMadelung`, `ClassicalMechanics.HerglotzLazoContact`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.Schrodinger

open ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## §A — the reversible Bohm Lagrangian and its Herglotz slice -/

/-- **The reversible de Broglie–Bohm Lagrangian** along the slice at a point `x`:
`L_R(t) = ½m‖v‖² − (V + Q)` — kinetic energy (through the guidance velocity `v = ∇S/m`) minus the
*conservative* effective potential `V + Q`. The quantum potential is part of the reversible Lagrangian. -/
noncomputable def bohmReversibleLagrangian (S V R : ℝ → E → ℝ) (m ℏ : ℝ) (x : E) : ℝ → ℝ :=
  fun t => m / 2 * ‖guidanceVelocity S m t x‖ ^ 2 - (V t x + quantumPotential (R t) m ℏ x)

/-- **The Herglotz contact slice of the de Broglie–Bohm system.** Reversible Lagrangian = the Bohm
Lagrangian; contact friction `ρ = 0` and accumulated imaginary action `s = 0` — Bohmian mechanics is
conservative and unitary, so it records *no* Herglotz dissipation. -/
noncomputable def bohmHerglotzSlice (S V R : ℝ → E → ℝ) (m ℏ : ℝ) (x : E) : HerglotzContactSlice where
  L_R := bohmReversibleLagrangian S V R m ℏ x
  ρ := fun _ => 0
  s := fun _ => 0

/-! ## §B — the frictionless / conservative reductions -/

/-- **[de Broglie–Bohm has no Herglotz contact friction] `ρ = 0 ⇒ L_eff = L_R`.** The effective
Herglotz Lagrangian of the Bohm slice is its reversible part — the quantum potential is conservative, not
dissipative; this distinguishes Bohmian mechanics from the damped oscillator (`ρ = γ/m ≠ 0`). -/
theorem bohm_herglotz_frictionless (S V R : ℝ → E → ℝ) (m ℏ : ℝ) (x : E) (t : ℝ) :
    (bohmHerglotzSlice S V R m ℏ x).effectiveLagrangian t = bohmReversibleLagrangian S V R m ℏ x t :=
  effectiveLagrangian_at_zero_contact_friction _ t rfl

/-- **[Zero imaginary action ⇒ conservative] `s = 0 ⇒ L_eff = L_R`.** The unitary wavefunction
`ψ = R·e^{iS/ℏ}` accumulates no imaginary action, the second (independent) reason the Bohm slice is
conservative. -/
theorem bohm_herglotz_zero_action (S V R : ℝ → E → ℝ) (m ℏ : ℝ) (x : E) (t : ℝ) :
    (bohmHerglotzSlice S V R m ℏ x).effectiveLagrangian t = bohmReversibleLagrangian S V R m ℏ x t :=
  effectiveLagrangian_at_zero_action _ t rfl

/-- **[Worked value: the free-particle reversible Lagrangian is the kinetic energy `‖k‖²/2m`].** With
`V = 0`, constant amplitude (`Q = 0`) and guidance velocity `v = k/m`, the reversible Bohm Lagrangian is the
constant kinetic energy — purely conservative. -/
theorem freeParticle_bohmReversibleLagrangian (k : E) (m c ℏ : ℝ) (hm : m ≠ 0) (x : E) (t : ℝ) :
    bohmReversibleLagrangian (freePhase k m) (fun _ _ => 0) (fun _ _ => c) m ℏ x t
      = ‖k‖ ^ 2 / (2 * m) := by
  rw [bohmReversibleLagrangian, freeParticle_guidanceVelocity,
    show quantumPotential ((fun (_ : ℝ) (_ : E) => c) t) m ℏ x = 0 from quantumPotential_const c m ℏ x,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

end Physlib.QuantumMechanics.Schrodinger

end
