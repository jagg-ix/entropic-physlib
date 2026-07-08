/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.HerglotzUnification
public import Physlib.ClassicalMechanics.HerglotzLazoContact

/-!
# Calibrating the Herglotz contact friction to an open quantum system

Establishes the physically valid link between **Herglotz–Lazo contact mechanics** and **quantum mechanics**,
and the **calibration factor** it requires.

The link is *not* to unitary/conservative QM (that is the frictionless `ρ = 0` slice — see the de
Broglie–Bohm bridge `HamiltonJacobiHerglotz`), but to **open / dissipative** QM. A Lindblad jump
operator `L` already calibrates the Herglotz `α`-rate structure (`HerglotzNoetherBalance`) via
`ofLindbladRate` with `α = −(2/ℏ)·‖Lψ‖²`. Here that same rate is transported to the **contact-slice** structure
`HerglotzContactSlice` (`L_eff = L_R − ρ·s`), giving a single structure on which the conservative and
dissipative cases live side by side:

  the contact-friction coefficient is the quantum dissipation rate
  `ρ := (2/ℏ)·‖Lψ‖²`   (`lindbladContactSlice`, `lindbladRate`),

which is exactly `−α` of the Lindblad `HerglotzNoetherBalance` (`lindbladContactSlice_rho_eq_neg_alpha`).

**The calibration factor.** The bridge is impossible without `ℏ`: it is the dimensional conversion between the
classical contact rate and the quantum dissipator. The factor is `2/ℏ`, and the companion action↔time
calibration is `S_I = ℏ·τ_ent` (`ClassicalMechanics.ActionPrinciple`). With it:

* **dissipativity** — `ρ ≥ 0` for `ℏ > 0` (`lindbladRate_nonneg`), matching `α ≤ 0`;
* **conservative (unitary) limit** — no jump operator (`L = 0`) gives `ρ = 0`
  (`lindbladRate_unitary`), so the contact slice is frictionless and reduces to the reversible Lagrangian
  (`lindblad_contact_conservative_limit`). This is precisely the regime of the conservative Bohm slice — the
  two bridges meet at `ρ = 0`.

So: a physically valid Herglotz–Lazo ↔ QM link *does* exist (to open systems), and it *does* require a
calibration theorem; the factor is `2/ℏ` (with `S_I = ℏ·τ_ent`).

* **§A — the calibrated contact slice** (`lindbladRate`, `lindbladContactSlice`).
* **§B — the calibration and its limits** (`lindbladContactSlice_rho_eq_neg_alpha`, `lindbladRate_nonneg`,
  `lindbladRate_unitary`, `lindblad_contact_conservative_limit`).

## References

* G. Herglotz (1930); Lazo et al. (2018); Lindblad (1976); GKS (1976). structure: `Physlib`
  (`Lindblad.HerglotzUnification`, `ClassicalMechanics.HerglotzLazoContact`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open ClassicalMechanics
open Physlib.QuantumMechanics.Lindblad.HerglotzUnification

namespace Physlib.QuantumMechanics.Lindblad.HerglotzContactCalibration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## §A — the calibrated contact slice -/

/-- **The Lindblad (quantum) dissipation rate** `λ = (2/ℏ)·‖Lψ‖²` — the rate at which a jump operator `L`
acting on a state `ψ` produces entropic time. This is `−α` of `ofLindbladRate`. -/
noncomputable def lindbladRate (L : H →L[ℂ] H) (hbar : ℝ) (ψ : H) : ℝ :=
  (2 / hbar) * ‖L ψ‖ ^ 2

/-- **The Herglotz contact slice calibrated to an open (Lindblad) quantum system.** The contact-friction
coefficient is the quantum dissipation rate `ρ = (2/ℏ)·‖Lψ‖²`; the calibration factor is `2/ℏ`. -/
noncomputable def lindbladContactSlice (L : H →L[ℂ] H) (hbar : ℝ) (ψ : H)
    (L_R s : ℝ → ℝ) : HerglotzContactSlice where
  L_R := L_R
  ρ := fun _ => lindbladRate L hbar ψ
  s := s

/-! ## §B — the calibration and its limits -/

/-- **[Calibration] the contact friction is `−α` of the Lindblad balance.** The classical Herglotz contact
friction coincides with the quantum dissipation rate `(2/ℏ)·‖Lψ‖²` — the explicit calibration tying
Herglotz–Lazo contact mechanics to the open quantum system. -/
theorem lindbladContactSlice_rho_eq_neg_alpha (L : H →L[ℂ] H) (hbar : ℝ) (ψ : H)
    (L_R s : ℝ → ℝ) (J0 t : ℝ) :
    (lindbladContactSlice L hbar ψ L_R s).ρ t = -((ofLindbladRate L hbar ψ J0).alpha t) := by
  show (2 / hbar) * ‖L ψ‖ ^ 2 = -(-(2 / hbar) * ‖L ψ‖ ^ 2)
  ring

/-- **[Dissipativity] `ρ ≥ 0` for `ℏ > 0`** — the contact friction is non-negative (the slice is genuinely
dissipative), matching `α ≤ 0`. -/
theorem lindbladRate_nonneg (L : H →L[ℂ] H) {hbar : ℝ} (hbar_pos : 0 < hbar) (ψ : H) :
    0 ≤ lindbladRate L hbar ψ := by
  rw [lindbladRate]
  positivity

/-- **[Conservative / unitary limit] no jump operator gives zero contact friction** `L = 0 ⇒ ρ = 0`. -/
@[simp] theorem lindbladRate_unitary (hbar : ℝ) (ψ : H) :
    lindbladRate (0 : H →L[ℂ] H) hbar ψ = 0 := by
  simp [lindbladRate]

/-- **[Conservative / unitary limit] the unitary contact slice is frictionless** `L = 0 ⇒ L_eff = L_R`. The
open-system contact slice reduces to the reversible Lagrangian exactly when there is no dissipation — the same
`ρ = 0` regime as the conservative de Broglie–Bohm slice. -/
theorem lindblad_contact_conservative_limit (hbar : ℝ) (ψ : H) (L_R s : ℝ → ℝ) (t : ℝ) :
    (lindbladContactSlice (0 : H →L[ℂ] H) hbar ψ L_R s).effectiveLagrangian t = L_R t :=
  effectiveLagrangian_at_zero_contact_friction _ t (lindbladRate_unitary hbar ψ)

end Physlib.QuantumMechanics.Lindblad.HerglotzContactCalibration

end
