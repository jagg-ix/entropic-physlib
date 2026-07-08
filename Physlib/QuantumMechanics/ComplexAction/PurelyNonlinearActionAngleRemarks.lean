/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle

/-!
# Remarks and appendices: general `π_{m,n}`, the adiabatic invariant, and the action-angle foundations (Ghosh–Bhamidipati 1905.08062)

The §3 remarks and Appendices A–B of `PurelyNonlinearActionAngle` (1905.08062): the general generalized-`π`, the
adiabatic-invariant construction for the time-dependent oscillator, and the action-angle foundations.

* **The general generalized `π`** `π_{m,n} = (2/n) B((m−1)/m, 1/n)` (§3, from the curve `|x|^m + |y|^n = 1`), of
 which `π_{2,α+1}` (`PurelyNonlinearActionAngle.genPi2`) is the physical `m = 2`, `n = α+1` case (Eq. 3.1).
* **The adiabatic invariant** (Eq. 3.5): for a slowly time-dependent length scale `τ(t)`, the generalized momentum
 `I = p²/(2τ) + |q|^{α+1}/((α+1)τ)` is `I = H/τ` — the Hamiltonian rescaled; `J = ∮ I dφ` is the adiabatic
 invariant. (The canonical generating function `F` with its `₂F₁` hypergeometric evaluation, Eqs. 3.7–3.10, is the
 paper's special-function analysis.)
* **The action-angle foundations** (Appendix A): the on-shell momentum `p = √(2m(E − V))` (Eq. A.15) for any
 conservative `H = p²/2m + V = E`, and the harmonic action-energy relation `E = ω I` with `I = ½mωA²` (Eqs.
 A.14, A.16) — the `α = 1` benchmark of the amplitude-dependent purely nonlinear case.

* **§A — the general generalized `π`.** `genPi`; **`genPi2_eq_genPi`**.
* **§B — the adiabatic invariant (Eq. 3.5).** `adiabaticMomentum`; **`adiabaticMomentum_eq`**.
* **§C — action-angle foundations (Appendix A).** **`momentum_general`** (Eq. A.15), `harmonicAction`,
 `harmonicEnergy`; **`harmonicEnergy_eq_omega_action`** (Eq. A.16).

Exact `ring`/`betaFn` identities for the general `π`, the adiabatic-momentum rescaling and the
action-angle foundations. The generalized-trigonometric solution `q(t) = q₀ sin_{2,α+1}(Ωt + π_{2,α+1}/2)`
(Eq. 2.13), the incomplete-beta inversion `arcsin_{m,n}` (Eqs. 3.4, B.20), and the `₂F₁` generating function
(Eqs. 3.9–3.10) are the paper's special-function content, recorded not re-derived.

## References

* A. Ghosh, C. Bhamidipati, arXiv:1905.08062, §3 (Eqs. 3.1, 3.5) and Appendix A (Eqs. A.14–A.16). Extends
 `PurelyNonlinearActionAngle`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleRemarks

/-! ## §A — the general generalized `π` (§3) -/

/-- The **general generalized `π`** `π_{m,n} = (2/n) B((m−1)/m, 1/n)` (§3) — the half-period of the generalized
sine `sin_{m,n}` parametrizing the curve `|x|^m + |y|^n = 1`. -/
noncomputable def genPi (m n : ℝ) : ℝ := 2 / n * betaFn ((m - 1) / m) (1 / n)

/-- **The physical `π_{2,α+1}` is the general `π_{m,n}` at `m = 2`, `n = α+1`** (Eq. 3.1) — the purely nonlinear
oscillator's generalized half-period is the `m = 2` case of the general one. -/
theorem genPi2_eq_genPi (α : ℝ) : genPi2 α = genPi 2 (α + 1) := by
  unfold genPi2 genPi
  rw [show ((2 : ℝ) - 1) / 2 = 1 / 2 from by norm_num]

/-! ## §B — the adiabatic invariant (Eq. 3.5) -/

/-- The **generalized momentum for the time-dependent oscillator** `I = p²/(2τ) + |q|^{α+1}/((α+1)τ)` (Eq. 3.5) —
with a slowly varying length scale `τ(t)`, the putative adiabatic invariant is `J = ∮ I dφ`. -/
noncomputable def adiabaticMomentum (α τ q p : ℝ) : ℝ :=
  p ^ 2 / (2 * τ) + |q| ^ (α + 1) / ((α + 1) * τ)

/-- **The adiabatic momentum is the Hamiltonian rescaled by `τ`** `I = H/τ` (Eq. 3.5) — the generalized momentum
is the purely nonlinear Hamiltonian (`PurelyNonlinearActionAngle.pnlHamiltonian`) divided by the length scale `τ`;
the `τ`-scaling is what makes `J = ∮ I dφ` an adiabatic invariant of the slowly time-dependent system. -/
theorem adiabaticMomentum_eq (α τ q p : ℝ) (hα : α + 1 ≠ 0) (hτ : τ ≠ 0) :
    adiabaticMomentum α τ q p = pnlHamiltonian α q p / τ := by
  unfold adiabaticMomentum pnlHamiltonian
  field_simp

/-! ## §C — action-angle foundations (Appendix A) -/

/-- **The on-shell momentum for any conservative system** `p² = 2m(E − V)` (Eq. A.15) — from `H = p²/2m + V = E`,
the momentum on a level set; the shape of the level curve alone (no explicit solution) gives the action
`I = (1/2π)∮ p dq`. -/
theorem momentum_general (m p E V : ℝ) (hm : m ≠ 0) (hH : p ^ 2 / (2 * m) + V = E) :
    p ^ 2 = 2 * m * (E - V) := by
  have h2m : 2 * m ≠ 0 := by simp [hm]
  have hp : p ^ 2 / (2 * m) = E - V := by linarith
  rw [div_eq_iff h2m] at hp
  rw [hp]; ring

/-- The **harmonic-oscillator action** `I = ½mωA²` (Eq. A.14) — the amplitude-`A` action of the `α = 1` benchmark. -/
noncomputable def harmonicAction (m ω A : ℝ) : ℝ := 1 / 2 * m * ω * A ^ 2

/-- The **harmonic-oscillator energy** `E = ½mω²A² = ½kA²` (with `ω² = k/m`). -/
noncomputable def harmonicEnergy (m ω A : ℝ) : ℝ := 1 / 2 * m * ω ^ 2 * A ^ 2

/-- **The harmonic energy is the frequency times the action** `E = ωI` (Eq. A.16) — for the linear harmonic
oscillator the Hamiltonian is `H(I) = ωI`, so the angle drops out and the motion is trivial. This is the
isochronous `α = 1` benchmark of the amplitude-dependent purely nonlinear energy. -/
theorem harmonicEnergy_eq_omega_action (m ω A : ℝ) :
    harmonicEnergy m ω A = ω * harmonicAction m ω A := by
  unfold harmonicEnergy harmonicAction
  ring

end Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleRemarks
