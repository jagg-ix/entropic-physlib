/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

/-!
# The `k = c` specialization is the Nagao–Nielsen mass-shell cone

Connects the variable-light-speed model (`LorentzViolationVariableLightSpeed`) to the existing Nagao–Nielsen
convergence cone (`ComptonClock.NagaoNielsenMassShellCone`): at the invariant speed `k = c`, the `k`-generalized
structure *is* the `(1,1)` Nagao–Nielsen form `nnLorentzForm q = (Re q)² − (Im q)²`. This turns "generalizes the
Minkowski/NN cone with `c ↦ k`" from a docstring note into proved specializations.

* **§A — the interval is the `NN` form.** **`kBoost_preserves_nnLorentzForm`**: on the spacetime coordinate
  `q = c·t + i·x`, the `k = c` boost preserves `nnLorentzForm` — exactly `kInterval_invariant` re-expressed
  through the Nagao–Nielsen `(1,1)` form.
* **§B — the mass shell is the cone value.** **`kMassShell_on_nnCone`**: the on-shell energy–momentum
  `q = E/c + i·p = γm₀c + i·γm₀v` sits on the cone with value `(m₀c)²`, the same invariant as
  `NagaoNielsenMassShellCone.nnLorentzForm_energyMomentum` — so the `k = c` modified mass shell `E² = p²c² +
  (m₀c²)²` is the NN forward mass-shell.

**Honest layering.** Both are exact specializations of the `k`-identities of
`LorentzViolationVariableLightSpeed` to `k = c`, landing on the proven Nagao–Nielsen form; no new physical input.

## References

* `ComplexAction.LorentzViolationVariableLightSpeed` (`kInterval_invariant`, `modified_mass_shell`) and
  `ComplexAction.ComptonClock.NagaoNielsenMassShellCone` (`nnLorentzForm`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LorentzViolationNagaoNielsen


/-- **The `k = c` boost preserves the Nagao–Nielsen form** — on the spacetime coordinate `q = c·t + i·x`, the
boost `t ↦ γ(t − vx/c²)`, `x ↦ γ(x − vt)` leaves `nnLorentzForm q = (ct)² − x²` invariant. This is
`kInterval_invariant` at `k = c`, seen through the `(1,1)` cone. -/
lemma kBoost_preserves_nnLorentzForm (v c γ t x : ℝ) (hc : c ≠ 0)
    (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) :
    nnLorentzForm ⟨c * (γ * (t - v * x / c ^ 2)), γ * (x - v * t)⟩ = nnLorentzForm ⟨c * t, x⟩ := by
  unfold nnLorentzForm
  show (c * (γ * (t - v * x / c ^ 2))) ^ 2 - (γ * (x - v * t)) ^ 2 = (c * t) ^ 2 - x ^ 2
  have h := kInterval_invariant v c γ t x hc hγ
  linear_combination h


/-- **The `k = c` mass shell is the Nagao–Nielsen cone value `(m₀c)²`** — the on-shell energy–momentum
`q = E/c + i·p = γm₀c + i·γm₀v` (with `E = γm₀c²`, `p = γm₀v`) lies on the convergence cone with
`nnLorentzForm q = (m₀c)²`, the same forward mass-shell invariant as
`NagaoNielsenMassShellCone.nnLorentzForm_energyMomentum`. -/
lemma kMassShell_on_nnCone (m₀ v c γ : ℝ) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) :
    nnLorentzForm ⟨γ * m₀ * c, γ * m₀ * v⟩ = (m₀ * c) ^ 2 := by
  unfold nnLorentzForm
  show (γ * m₀ * c) ^ 2 - (γ * m₀ * v) ^ 2 = (m₀ * c) ^ 2
  linear_combination (m₀ ^ 2) * hγ

/-- **A massive particle is a convergent ("timelike") point of the cone** — for `m₀c ≠ 0` the `k = c` on-shell
coordinate satisfies `nnConverges` (`0 < nnLorentzForm`), tying the mass shell to the Nagao–Nielsen convergence
criterion. -/
lemma kMassShell_converges (m₀ v c γ : ℝ) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) (hmc : m₀ * c ≠ 0) :
    nnConverges ⟨γ * m₀ * c, γ * m₀ * v⟩ := by
  unfold nnConverges
  rw [kMassShell_on_nnCone m₀ v c γ hγ]
  positivity

end Physlib.QuantumMechanics.ComplexAction.LorentzViolationNagaoNielsen
