/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction

/-!
# The counterterm that tames the null-boundary parametrization ambiguity (Appendix B)

Appendix B of Lehner, Myers, Poisson & Sorkin (arXiv:1609.00207): the null-segment boundary action
`S_Σ(joined)` depends on the parametrization of the null generators (Eq. 2.70,
`NullBoundaryGravitationalAction.reparamAction`). Can a counterterm `ΔS_Σ = ∫_Σ ℒ √γ d²θ dλ`, built
from intrinsic-geometry scalars, cancel that dependence? The answer is **yes**, with a counterterm
Lagrangian in the expansion `Θ`:

 `ℒ(Θ) = −2Θ (ln|Θ| + c)` (Eq. B4),

the unique (up to the constant `c`) solution of the invariance ODE `Θ dℒ/dΘ − ℒ + 2Θ = 0` (Eq. B8).

* **§A — the counterterm Lagrangian and its derivative** (Eq. B4). `counterterm Θ c = −2Θ(ln|Θ|+c)`;
 `hasDerivAt_counterterm` establishes `ℒ'(Θ) = −2(ln|Θ|+c) − 2` genuinely (via `Real.hasDerivAt_log`).
* **§B — the invariance ODE** (Eq. B8). `Θ ℒ'(Θ) − ℒ(Θ) + 2Θ = 0` holds for **every** `c`
 (`counterterm_ode`) — the differential equation whose solution is `ℒ` of §A.
* **§C — the reparametrization law of the counterterm** (Eqs. B3, B5). Under `Θ ↦ e^β Θ`, the density
 `e^{−β} ℒ(e^β Θ) = ℒ(Θ) − 2Θβ` (`counterterm_reparam`): the counterterm shifts by exactly the
 `−2Θβ` needed to cancel the action's `+2Θβ` shift.
* **§D — restored invariance** (Eqs. B5, B6). `S̃_Σ + ΔS̃_Σ = S_Σ + ΔS_Σ`
 (`counterterm_restores_invariance`), reusing `NullBoundaryGravitationalAction.reparamAction` — the
 full boundary action is now parametrization independent.

The Lagrangian `ℒ(Θ) = −2Θ(ln|Θ|+c)` includes the Boltzmann `−x ln x` form in the expansion `Θ`: the
reparametrization-fixing counterterm is an *entropy density of the null congruence's expansion*.

Proven: the derivative of `ℒ`, the invariance ODE, the reparametrization shift
`ℒ(Θ) − 2Θβ`, and the resulting cancellation restoring invariance. Interpretive: the integrals
`∫_Σ … √γ d²θ dλ` are represented by their integrated values / integrand identities; the geometric
scalar `Θ = ∂_λ ln√γ` (the null expansion) is taken as the datum.

## References

* L. Lehner, R. C. Myers, E. Poisson, R. D. Sorkin, "Gravitational action with null boundaries",
 arXiv:1609.00207 [`Lehner:2016vdi`], Appendix B, Eqs. (B1)–(B8). Reuses
 `NullBoundaryGravitationalAction` (`reparamAction`, Eq. 2.70).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NullBoundaryCounterterm

open Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction

/-! ## §A — the counterterm Lagrangian and its derivative (Eq. B4) -/

/-- **The counterterm Lagrangian** `ℒ(Θ) = −2Θ(ln|Θ| + c)` (Eq. B4), a function of the null expansion
`Θ` (with an arbitrary additive constant `c`), added to the boundary action to cancel the
parametrization dependence. -/
noncomputable def counterterm (Θ c : ℝ) : ℝ := -2 * (Θ * (Real.log |Θ| + c))

/-- **The derivative of the counterterm** `ℒ'(Θ) = −2(ln|Θ| + c) − 2` (Eq. B7). -/
noncomputable def countertermDeriv (Θ c : ℝ) : ℝ := -2 * (Real.log |Θ| + c) - 2

/-- **`ℒ'(Θ) = −2(ln|Θ|+c) − 2`** (Eq. B7): the counterterm Lagrangian has the stated derivative in the
expansion `Θ` (away from `Θ = 0`), established from `Real.hasDerivAt_log`. -/
theorem hasDerivAt_counterterm (Θ c : ℝ) (hΘ : Θ ≠ 0) :
    HasDerivAt (fun x => counterterm x c) (countertermDeriv Θ c) Θ := by
  have hlog : HasDerivAt Real.log Θ⁻¹ Θ := Real.hasDerivAt_log hΘ
  have h : HasDerivAt (fun y => -2 * (id y * (Real.log y + c)))
      (-2 * (1 * (Real.log Θ + c) + Θ * Θ⁻¹)) Θ :=
    ((hasDerivAt_id Θ).mul (hlog.add_const c)).const_mul (-2)
  have hfun : (fun x => counterterm x c) = (fun y => -2 * (id y * (Real.log y + c))) := by
    funext x; simp only [counterterm, id_eq, Real.log_abs]
  have hval : -2 * (1 * (Real.log Θ + c) + Θ * Θ⁻¹) = countertermDeriv Θ c := by
    unfold countertermDeriv
    rw [Real.log_abs, mul_inv_cancel₀ hΘ]; ring
  rw [hfun, ← hval]; exact h

/-! ## §B — the invariance ODE (Eq. B8) -/

/-- **The invariance differential equation** `Θ ℒ'(Θ) − ℒ(Θ) + 2Θ = 0` (Eq. B8): the counterterm
Lagrangian of §A solves it for **every** constant `c`. This is the condition for
`S_Σ(joined) + ΔS_Σ` to be invariant under a reparametrization of the null generators. -/
theorem counterterm_ode (Θ c : ℝ) :
    Θ * countertermDeriv Θ c - counterterm Θ c + 2 * Θ = 0 := by
  unfold countertermDeriv counterterm; ring

/-! ## §C — the reparametrization law of the counterterm (Eqs. B3, B5) -/

/-- **The counterterm density shifts by `−2Θβ`** (Eqs. B3, B5): under a reparametrization `Θ ↦ e^β Θ`
of the null generators, the counterterm density transforms as `e^{−β} ℒ(e^β Θ) = ℒ(Θ) − 2Θβ`, because
`ln|e^β Θ| = β + ln|Θ|`. This is exactly the shift needed to cancel the action's `+2Θβ` shift. -/
theorem counterterm_reparam (Θ β c : ℝ) (hΘ : Θ ≠ 0) :
    Real.exp (-β) * counterterm (Real.exp β * Θ) c = counterterm Θ c - 2 * Θ * β := by
  have hexp : (0 : ℝ) < Real.exp β := Real.exp_pos β
  have habsΘ : |Θ| ≠ 0 := abs_ne_zero.mpr hΘ
  have hlog : Real.log |Real.exp β * Θ| = β + Real.log |Θ| := by
    rw [abs_mul, abs_of_pos hexp, Real.log_mul (ne_of_gt hexp) habsΘ, Real.log_exp]
  unfold counterterm
  rw [hlog, Real.exp_neg]
  field_simp
  ring

/-! ## §D — restored reparametrization invariance (Eqs. B5, B6) -/

/-- **The reparametrized counterterm** `ΔS̃_Σ = ΔS_Σ − 2∫_Σ Θβ √γ d²θ dλ` (Eq. B5), the integrated
form of the `−2Θβ` shift of §C. -/
def reparamCounterterm (ΔS ΘβIntegral : ℝ) : ℝ := ΔS - 2 * ΘβIntegral

/-- **The counterterm restores reparametrization invariance** (Eq. B6): the action's shift
`S̃_Σ = S_Σ + 2∫Θβ` (`NullBoundaryGravitationalAction.reparamAction`) is exactly cancelled by the
counterterm's shift `ΔS̃_Σ = ΔS_Σ − 2∫Θβ`, so `S̃_Σ + ΔS̃_Σ = S_Σ + ΔS_Σ` — the full null-boundary
action is now independent of the parametrization of the generators. -/
theorem counterterm_restores_invariance (S ΔS ΘβIntegral : ℝ) :
    reparamAction S ΘβIntegral + reparamCounterterm ΔS ΘβIntegral = S + ΔS := by
  unfold reparamAction reparamCounterterm; ring

end Physlib.QuantumMechanics.ComplexAction.NullBoundaryCounterterm
