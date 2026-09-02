/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-!
# The action-angle momentum on the Nagao–Nielsen complex contour, and the complex action

This links the purely nonlinear oscillator's action-angle momentum (`PurelyNonlinearGeneralizedTrig.reducedMomentum`,
Ghosh–Bhamidipati 1905.08062) to the **Nagao–Nielsen complex `p, q`** (`NagaoNielsenBenderDunneComplexMoment`) and
the **complex action** (`PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsenComplexActionWeight`).

The reduced momentum `p = √(2I/τ − q^{α+1}/τ²)` is real in the classically-allowed region. In the
**classically-forbidden region** `q^{α+1}/τ² > 2I/τ` the radicand is negative, so the momentum is **imaginary** —
the analytic continuation onto the Nagao–Nielsen complex contour: `p = i√(q^{α+1}/τ² − 2I/τ)`, with `Re p = 0`
but the *same* on-shell square `p² = 2I/τ − q^{α+1}/τ²` (`reducedMomentum_sq` continued). An imaginary momentum
makes the action `S = ∫ p dq` acquire an imaginary part, so the complex-action weight `e^{(i/ℏ)(S_R + iS_I)}`
(`nagaoNielsenComplexActionWeight`) is damped by `e^{−S_I/ℏ}` — tunneling suppression. The classically-allowed
region (`S_I = 0`, real momentum) is the reversible/unitary limit.

The complex phase-space coordinate itself is the Nagao–Nielsen one `q_NN = E/c + i·p` (`nnComplexCoordinate`), whose
Lorentzian form `(Re q)² − (Im q)² = (E/c)² − p²` is the on-shell mass-shell condition.

* **§A — the action-angle momentum on the NN contour.** `nnReducedMomentum`; **`nnReducedMomentum_sq`** (`p² = R`,
  the continued on-shell relation), **`nnReducedMomentum_re`** (`Re p = 0`, imaginary in the forbidden region).
* **§B — the NN complex coordinate and the complex action.** **`actionAngle_nnCoordinate_massShell`**
  (`(Re q)² − (Im q)² = (E/c)² − p²`), **`nnComplexAction_modulus_is_kuiken`** (the complex-action weight's modulus
  is the entropic damping `e^{−S_I/ℏ}`; reversible when `S_I = 0`).

**Honest layering.** Exact `Complex`/`Real.sqrt` identities for the momentum continuation, the mass-shell form and
the complex-action modulus. Reuses `reducedMomentum`, `nnComplexCoordinate`, `nagaoNielsenComplexActionWeight`.

## References

* A. Ghosh, C. Bhamidipati, arXiv:1905.08062; K. Nagao, H. B. Nielsen (complex action). Links
  `PurelyNonlinearGeneralizedTrig` to `NagaoNielsenBenderDunneComplexMoment` and `ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction


/-- The **action-angle momentum continued onto the Nagao–Nielsen contour** `p = i√(q^{α+1}/τ² − 2I/τ)` — the
analytic continuation of `reducedMomentum` into the classically-forbidden region `q^{α+1}/τ² > 2I/τ`, where the
classical momentum is imaginary (the NN complex momentum on the deformed contour). -/
noncomputable def nnReducedMomentum (I α τ q : ℝ) : ℂ :=
  Complex.I * (Real.sqrt (q ^ (α + 1) / τ ^ 2 - 2 * I / τ) : ℂ)

/-- **The NN momentum has the same on-shell square** `p² = 2I/τ − q^{α+1}/τ²` (continued to the forbidden region
`2I/τ − q^{α+1}/τ² ≤ 0`) — the complex continuation of `reducedMomentum_sq`, now with an imaginary momentum. -/
lemma nnReducedMomentum_sq (I α τ q : ℝ) (h : 2 * I / τ - q ^ (α + 1) / τ ^ 2 ≤ 0) :
    (nnReducedMomentum I α τ q) ^ 2 = ((2 * I / τ - q ^ (α + 1) / τ ^ 2 : ℝ) : ℂ) := by
  unfold nnReducedMomentum
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ q ^ (α + 1) / τ ^ 2 - 2 * I / τ)]
  push_cast
  ring

/-- **The NN momentum is imaginary** `Re p = 0` — in the classically-forbidden region the action-angle momentum has
no real part; the motion is under the barrier (tunneling), the Nagao–Nielsen complex-contour regime. -/
@[simp] lemma nnReducedMomentum_re (I α τ q : ℝ) : (nnReducedMomentum I α τ q).re = 0 := by
  simp [nnReducedMomentum, Complex.mul_re]


/-- **The NN complex coordinate's mass-shell form** `(Re q)² − (Im q)² = (E/c)² − p²` — the action-angle energy
`E` and momentum `p` build the Nagao–Nielsen complex phase-space coordinate `q_NN = E/c + i·p`
(`nnComplexCoordinate`), whose Lorentzian form `nnLorentzForm` is the on-shell mass-shell condition. -/
lemma actionAngle_nnCoordinate_massShell (E p c : ℝ) :
    nnLorentzForm (nnComplexCoordinate ![E] ![p] c 0) = (E / c) ^ 2 - p ^ 2 := by
  simpa using nnComplexCoordinate_lorentzForm ![E] ![p] c 0

/-- **The complex-action weight's modulus is the entropic damping** `‖e^{(i/ℏ)(S_R + iS_I)}‖ = kuikenWeight ℏ S_I
= e^{−S_I/ℏ}` — the Nagao–Nielsen complex action of the action-angle motion is damped by its imaginary part `S_I`
(the tunneling / forbidden-region contribution from the imaginary momentum). The classically-allowed region
(`S_I = 0`, real `reducedMomentum`) is the reversible/unitary limit, `‖·‖ = 1`. -/
lemma nnComplexAction_modulus_is_kuiken (S_R S_I ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ‖nagaoNielsenComplexActionWeight S_R S_I ℏ‖ = kuikenWeight ℏ S_I := by
  rw [nagaoNielsen_eq_master S_R S_I ℏ hℏ, master_modulus_is_kuiken]

end Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction
