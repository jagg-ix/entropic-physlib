/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Misra's internal-time operator bridges future-included Q-formalism and Herglotz dissipation

`RelationalTime.LiouvillianAgeOperator` formalized the Misra–Prigogine–Courbage conjugate
time operator in the spectral representation: the Liouvillian `L` is multiplication by the
spectral variable `λ` (`spectralLiouvillian`), the internal-time operator is `T = i d/dλ`
(`ageOperator`), and they satisfy the canonical conjugacy `i[L, T] = I` (`liouvillian_age_ccr`).

This file **integrates** that infinitesimal relation along the Liouville flow
`U_t = e^{−iLt}` (multiplication by `e^{−iλt}`) and uses the resulting *clock relation* to
connect two formalisms that otherwise look unrelated:

* the **future-included** complex action theory of Nagao–Nielsen (a *two-sided* time
  evolution: a past boundary `A` at `−∞` and a future boundary `B` at `+∞`), and
* **Herglotz** dissipative mechanics (a monotone action variable evolving along the flow).

## The clock relation (integrated `i[L,T] = I`)

* `liouvilleEvolve` — the flow `U_t f (λ) = e^{−iλt} f(λ)`.
* `liouvilleEvolve_zero`, `liouvilleEvolve_add` — `U` is a **one-parameter group**
  `U_s ∘ U_t = U_{s+t}`, `U_0 = id`, defined for **all `t ∈ ℝ`**: forward `t > 0` is
  evolution toward the future boundary `B`, backward `t < 0` toward the past boundary `A`.
  This two-sided time line is exactly the future-included structure (and the full real
  spectrum `λ ∈ ℝ` of `L` is its temporal extent).
* `ageOperator_liouvilleEvolve` — the **intertwining** `T U_t = U_t (T + t)`: evolving by
  `t` shifts the internal-time operator by exactly `t`.
* `ageOperator_evolve_commutator` — the **clock relation** `[T, U_t] = t · U_t`: the
  commutator of the internal-time operator with the evolution is the *elapsed time itself*.
  This is the finite (integrated) form of `i[L,T] = I`.

## What it bridges

* **Misra.** `T` reads the elapsed flow time `t` (the clock relation). Monotone functions
  of `T` are the Lyapunov variables / entropy superoperators that give the intrinsic arrow
  of time (MPC §3). The internal time increases by exactly `t` along the flow.
* **Herglotz.** Herglotz's generalized variational principle has a *monotone action
  variable* `S` along the trajectory, whose growth drives the dissipation/friction. The
  internal-time operator `T` is the operator realization of that variable: a quantity
  conjugate to the generator that accumulates along the flow (`[T,U_t] = t U_t`), the
  source of irreversibility shared with the imaginary action `S_I` (cf.
  `ComplexAction.BenderIdentity`, `dS_I/dt = Γ/2`).
* **Future-included complex-action.** Because `U` is a group over all of `ℝ`, both temporal
  directions (`A` at `−∞`, `B` at `+∞`) are present — the future-included theory. The sign
  of the spectral/time coordinate is the future/past split of
  `ComplexAction.Rapidity.FutureIncludedLorentzian` (`timelikeFuture`/`timelikePast`); the
  future-not-included theory keeps a single direction (a definite arrow, the irreversible
  `Λ`-dynamics of Misra).

Reference: B. Misra, I. Prigogine, M. Courbage, Proc. Natl. Acad. Sci. USA **76** (1979)
4768 (internal-time operator); K. Nagao, H. B. Nielsen, arXiv:1304.4017 (future-included /
future-not-included complex-action); G. Herglotz (1930), generalized variational principle.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz

open Physlib.QuantumMechanics.RelationalTime

/-- **The Liouville flow** `U_t = e^{−iLt}` in the spectral representation: multiplication
by `e^{−iλt}`, `(U_t f)(λ) = e^{−iλt} f(λ)`. -/
noncomputable def liouvilleEvolve (t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun lam => Complex.exp (-Complex.I * lam * t) * f lam

/-- `U_0 = id`. -/
@[simp] theorem liouvilleEvolve_zero (f : ℝ → ℂ) : liouvilleEvolve 0 f = f := by
  funext lam; simp [liouvilleEvolve]

/-- **One-parameter group law** `U_s ∘ U_t = U_{s+t}`: the time translations compose. With
`liouvilleEvolve_zero` this makes `U` a two-sided (`t ∈ ℝ`) time-evolution group — the
future-included structure (future `t > 0`, past `t < 0`). -/
theorem liouvilleEvolve_add (s t : ℝ) (f : ℝ → ℂ) :
    liouvilleEvolve s (liouvilleEvolve t f) = liouvilleEvolve (s + t) f := by
  funext lam
  simp only [liouvilleEvolve]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **The intertwining `T U_t = U_t (T + t)`** (the integrated `i[L,T] = I`): applying the
internal-time operator after evolving by `t` is the same as evolving the shifted operator
`T + t`. The internal time picks up exactly the elapsed `t`. -/
theorem ageOperator_liouvilleEvolve (t : ℝ) (f : ℝ → ℂ) (lam : ℝ)
    (hf : DifferentiableAt ℝ f lam) :
    ageOperator (liouvilleEvolve t f) lam
      = liouvilleEvolve t (fun mu => ageOperator f mu + (t : ℂ) * f mu) lam := by
  have hcoe : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 lam := (hasDerivAt_id lam).ofReal_comp
  have hg : HasDerivAt (fun x : ℝ => -Complex.I * (x : ℂ) * (t : ℂ)) (-Complex.I * (t : ℂ)) lam := by
    simpa using (hcoe.const_mul (-Complex.I)).mul_const (t : ℂ)
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)))
      (Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) * (-Complex.I * (t : ℂ))) lam := by
    simpa using hg.cexp
  have hprod : HasDerivAt (liouvilleEvolve t f)
      (Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) * (-Complex.I * (t : ℂ)) * f lam
        + Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) * deriv f lam) lam :=
    hexp.mul hf.hasDerivAt
  unfold ageOperator
  rw [hprod.deriv]
  simp only [liouvilleEvolve]
  linear_combination
    (-(Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) * (t : ℂ) * f lam)) * Complex.I_mul_I

/-- **The clock relation `[T, U_t] = t · U_t`**: the commutator of Misra's internal-time
operator `T` with the Liouville evolution `U_t` is multiplication by the *elapsed time*
`t`. This is the finite, integrated form of the canonical conjugacy `i[L, T] = I`
(`liouvillian_age_ccr`): `T` is a genuine clock reading the flow time, the monotone
internal-time / Lyapunov variable shared by Misra's irreversibility, Herglotz's action
variable, and the future-included accumulated time. -/
theorem ageOperator_evolve_commutator (t : ℝ) (f : ℝ → ℂ) (lam : ℝ)
    (hf : DifferentiableAt ℝ f lam) :
    ageOperator (liouvilleEvolve t f) lam - liouvilleEvolve t (ageOperator f) lam
      = (t : ℂ) * liouvilleEvolve t f lam := by
  rw [ageOperator_liouvilleEvolve t f lam hf]
  simp only [liouvilleEvolve]
  ring

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz

end
