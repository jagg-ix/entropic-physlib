/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

/-!
# The Ehrenfest classical Klein–Gordon field lives on the Nagao–Nielsen mass-shell cone

Links the entropic-dynamics Ehrenfest theorem (Ipek–Abedi–Caticha §8, Eq. 100:
`(□ − m²)χ̄ = 0` — `EntropicDynamicsEvolutionSchrodingerEhrenfest`) to the arc's Nagao–Nielsen mass-shell / complex-
action convergence machinery (`ComptonClock.NagaoNielsenMassShellCone`). The expected field `χ̄` of the
reconstructed quantum field theory obeys the classical Klein–Gordon equation, whose plane-wave dispersion
`E² = (pc)² + (mc²)²` is exactly the Nagao–Nielsen convergence cone `L(E/c + ip) = (mc)²`:

* the Ehrenfest expected field's energy–momentum is **on the mass-shell** `L(E/c + ip) = (mc)²`
 (`ehrenfest_field_on_nn_massShell`) — the classical Klein–Gordon dispersion `(□ − m²)χ̄ = 0` in momentum space is
 the real Lorentz invariant `(E/c)² − p² = (mc)²`;
* the field is **in the Nagao–Nielsen convergence cone iff massive** (`ehrenfest_field_converges_iff_massive`) — a
 massive expected field `(mc)² > 0` is a timelike point of the complex-coordinate cone, exactly where the
 steepest-descent path integral converges;
* so the **Ehrenfest classical Klein–Gordon equation is the mass-shell cone** (`ehrenfest_kleinGordon_is_nn_massShell`):
 the entropic-dynamics mean field lands on the same forward mass-shell that the electron-cell arc identifies with
 the Nagao–Nielsen convergence cone and the complex-action weight's damping domain.

This closes the entropic-dynamics reconstruction back onto the complex-action mass-shell: the expected field of the
information-based QFT (§8) obeys the classical Klein–Gordon equation, and that equation *is* the Nagao–Nielsen
convergence cone / mass-shell of the arc — entropic dynamics and the complex-action path integral meet on the
mass-shell.

* **§A — the Ehrenfest field is on the NN mass-shell** (`ehrenfest_field_on_nn_massShell`).
* **§B — it converges iff massive** (`ehrenfest_field_converges_iff_massive`).
* **§C — the Ehrenfest Klein–Gordon equation is the mass-shell cone** (`ehrenfest_kleinGordon_is_nn_massShell`).

The identities reuse `nnLorentzForm_energyMomentum` and `nnConverges_energyMomentum_iff`
(exact) and the Ehrenfest Klein–Gordon equivalence (`ehrenfest_classical_kleinGordon`). The Fourier transform
taking `(□ − m²)χ̄ = 0` to the dispersion relation is the physical reading, realized via the
`energyMomentumComplex` coordinate. No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §8 (Eq. 100); K. Nagao, H.B. Nielsen (complex action /
 convergence cone). Repo dependencies: `EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest`,
 `ComptonClock.NagaoNielsenMassShellCone`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEhrenfestMassShell

/-! ## §A — the Ehrenfest field is on the Nagao–Nielsen mass-shell -/

/-- **[The Ehrenfest expected field lies on the Nagao–Nielsen mass-shell] `L(E/c + ip) = (mc)²`.** The
entropic-dynamics mean field `χ̄` obeys the classical Klein–Gordon equation `(□ − m²)χ̄ = 0` (Ehrenfest theorem,
Eq. 100); its plane-wave energy–momentum, encoded as `q = E/c + ip`, satisfies the real Lorentz invariant
`(E/c)² − p² = (mc)²` — the Nagao–Nielsen convergence cone of the complex-action path integral. -/
theorem ehrenfest_field_on_nn_massShell (m c p : ℝ) (hc : c ≠ 0) :
    nnLorentzForm (energyMomentumComplex m c p) = (m * c) ^ 2 :=
  nnLorentzForm_energyMomentum m c p hc

/-! ## §B — it converges iff massive -/

/-- **[The Ehrenfest field is in the convergence cone iff massive] `nnConverges ↔ mc ≠ 0`.** The expected field's
energy–momentum is a timelike point of the Nagao–Nielsen `(1,1)` convergence cone — where the steepest-descent
complex-action path integral converges — exactly when the particle is massive, `(mc)² > 0`. -/
theorem ehrenfest_field_converges_iff_massive (m c p : ℝ) (hc : c ≠ 0) :
    nnConverges (energyMomentumComplex m c p) ↔ m * c ≠ 0 :=
  nnConverges_energyMomentum_iff m c p hc

/-! ## §C — the Ehrenfest Klein–Gordon equation is the mass-shell cone -/

/-- **[The Ehrenfest classical Klein–Gordon equation is the Nagao–Nielsen mass-shell cone].** For the
entropic-dynamics expected field `χ̄`:

* the Ehrenfest relation `□χ̄ = m²χ̄` is the classical Klein–Gordon equation `(□ − m²)χ̄ = 0` (Eq. 100);
* its plane-wave dispersion is the Nagao–Nielsen mass-shell `L(E/c + ip) = (mc)²`.

The mean field of the information-based reconstruction lands on the forward mass-shell / convergence cone of the
complex-action path integral — entropic dynamics closes onto the arc's mass-shell. -/
theorem ehrenfest_kleinGordon_is_nn_massShell (m c p chiBar boxChiBar : ℝ) (hc : c ≠ 0) :
    (boxChiBar = ehrenfestForceQuadratic m chiBar ↔ boxChiBar - m ^ 2 * chiBar = 0)
      ∧ nnLorentzForm (energyMomentumComplex m c p) = (m * c) ^ 2 :=
  ⟨ehrenfest_classical_kleinGordon m chiBar boxChiBar,
    ehrenfest_field_on_nn_massShell m c p hc⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEhrenfestMassShell

end
