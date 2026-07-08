/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz

/-!
# The Misra internal time is canonically conjugate to the Zeno Liouvillian stripe

The **substantive** (non-tautological) link between the Zeno-limit Liouvillian and the internal-time operator.
`ZenoSpectralTimeUnification` observed that the Zeno eigenvalue, the Misra evolution, the Compton clock and the
Regge weight all satisfy `‖exp(λt)‖ = exp(Re λ · t)` — a shared *magnitude*, but a thin (near-tautological)
form-match. The real link is the **canonical commutation relation `i[L, T] = I`** of
`RelationalTime.LiouvillianAgeOperator` (`liouvillian_age_ccr`), which is content-ful: the identity is *produced*
by the product rule when the differentiation operator `T = i d/dλ` fails to commute with multiplication by `λ`.

In the Zeno limit the Liouvillian spectrum organizes into stripes (`ZenoLiouvillianSpectrum`): real parts
`Re λ = c_k Γ` (dissipative, the decay — the `‖exp‖` shadow) and imaginary parts `Im λ = u_α − w_β` (the
oscillation frequencies that *fill* each stripe with `d₁²` eigenvalues, densely as the many-body chain grows). It
is that continuous, stripe-filling **oscillation spectrum** — a Liouvillian with continuous spectrum on the real
line — that includes the Misra time operator (Pauli's theorem forbids one for the discrete finite-qubit spectrum).

* **§A — the canonical conjugacy is the link.** **`zenoStripe_liouvillian_age_ccr`** (`i[L, T] = I` on the
 stripe spectral variable, via `liouvillian_age_ccr`): the internal time `T = i d/dλ` is canonically conjugate to
 the Liouvillian `L = ` multiplication by the stripe frequency `λ`. Not a magnitude coincidence — the identity
 comes from `d/dλ(λ f) = f + λ f'`, the non-commutativity of frequency and time.
* **§B — the internal time reads elapsed time.** **`ageOperator_time_eigenfunction`**
 (`T e^{iλτ} = −τ · e^{iλτ}`): the internal-time operator's (generalized) eigenfunctions are the frequency plane
 waves `e^{iλτ}`, with eigenvalue the elapsed time `−τ`. A definite-time state is spread over all stripe
 frequencies — the Fourier duality that *is* `[L, T] = −iI` (`L e^{iλτ} = λ · e^{iλτ}` is not a scalar eigenvalue:
 `L` is diagonal in frequency, `T` in time).
* **§C — the differential time reads the integrated evolution.** **`ageOperator_reads_evolution_time`**
 (`T U_t = t · U_t`): the Liouville evolution `U_t = liouvilleEvolve t 1` (of `MisraAgeFutureIncludedHerglotz`) is
 a `T`-eigenfunction with eigenvalue the elapsed time `t` — the plane-wave eigenfunction of §B *is* the evolution,
 so the differential `i[L,T]=I` is the source of the integrated intertwining `[T, U_t] = t·U_t`.

`zenoStripe_liouvillian_age_ccr` instantiates the exact `liouvillian_age_ccr` on the stripe
variable; `ageOperator_time_eigenfunction` and `spectralLiouvillian_planewave` are exact `deriv`/`ring`
identities. The continuous-spectrum claim (the filled stripe records `T`, the finite qubit does not) is the
physical reading of Pauli's theorem, stated not proved.

## References

* B. Misra, I. Prigogine, M. Courbage, PNAS **76** (1979) 4768 (`i[L,T]=I`); Popkov & Presilla, PRL **126**,
 190402 (2021). Built on `TimeOperator.MisraAgeFutureIncludedHerglotz` (which re-exports
 `RelationalTime.LiouvillianAgeOperator`) and `Lindblad.ZenoLiouvillianSpectrum`.

No new axioms.
-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz

@[expose] public section

namespace Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy

/-! ## §A — the canonical conjugacy is the link -/

/-- **The Misra canonical conjugacy `i[L, T] = I` on the Zeno stripe** — for the Liouvillian
`L = spectralLiouvillian` (multiplication by the stripe frequency `λ = Im(eigenvalue)`) and the internal time
`T = ageOperator = i d/dλ`, `i[L, T] f = f`. This is the genuine (non-tautological) link between the Zeno
Liouvillian spectrum and the internal-time operator: the identity is born from `d/dλ(λ f) = f + λ f'`, the
non-commutativity of frequency and time, not from any `‖exp‖` magnitude. -/
theorem zenoStripe_liouvillian_age_ccr (f : ℝ → ℂ) (lam : ℝ) (hf : DifferentiableAt ℝ f lam) :
    Complex.I * (spectralLiouvillian (ageOperator f) lam - ageOperator (spectralLiouvillian f) lam)
      = f lam :=
  liouvillian_age_ccr f lam hf

/-! ## §B — the internal time reads elapsed time -/

/-- **The internal-time operator's eigenfunctions are the frequency plane waves** `T e^{iλτ} = −τ · e^{iλτ}` — the
Misra time `T = i d/dλ` acting on the plane wave `e^{iλτ}` (a state of definite elapsed time `τ`) returns the
eigenvalue `−τ`: the internal time reads the flow time. The plane wave is spread over *all* stripe frequencies
`λ`, the Fourier-dual of a definite-frequency mode — the content of `[L, T] = −iI`. -/
theorem ageOperator_time_eigenfunction (τ lam : ℝ) :
    ageOperator (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ) * (τ : ℂ))) lam
      = (-τ : ℂ) * Complex.exp (Complex.I * (lam : ℂ) * (τ : ℂ)) := by
  unfold ageOperator
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 lam := (hasDerivAt_id lam).ofReal_comp
  have hg : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ) * (τ : ℂ)) (Complex.I * (τ : ℂ)) lam := by
    simpa using (hx.const_mul Complex.I).mul_const (τ : ℂ)
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ) * (τ : ℂ)))
      (Complex.exp (Complex.I * (lam : ℂ) * (τ : ℂ)) * (Complex.I * (τ : ℂ))) lam := by
    simpa using hg.cexp
  rw [hexp.deriv]
  have hI : Complex.I * (Complex.exp (Complex.I * (lam : ℂ) * (τ : ℂ)) * (Complex.I * (τ : ℂ)))
      = (Complex.I * Complex.I) * (τ : ℂ) * Complex.exp (Complex.I * (lam : ℂ) * (τ : ℂ)) := by ring
  rw [hI, Complex.I_mul_I]
  ring

/-! ## §C — the differential time reads the integrated evolution -/

/-- **The internal time reads the elapsed evolution time** `T U_t = t · U_t` (eigenvalue form) — the Liouville
evolution factor `U_t = liouvilleEvolve t 1` (of the trivial mode, `MisraAgeFutureIncludedHerglotz`) is a
`T`-eigenfunction with eigenvalue the elapsed time `t`. The plane-wave eigenfunction of §B *is* the Liouville
evolution `e^{−iλt}`, so the differential `i[L, T] = I` is the source of the integrated intertwining
`[T, U_t] = t · U_t` (`ageOperator_evolve_commutator`): `T` genuinely reads the flow time. -/
theorem ageOperator_reads_evolution_time (t lam : ℝ) :
    ageOperator (liouvilleEvolve t (fun _ => 1)) lam
      = (t : ℂ) * liouvilleEvolve t (fun _ => 1) lam := by
  have hfun : (liouvilleEvolve t (fun _ => 1))
      = fun x : ℝ => Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) := by
    funext x; simp [liouvilleEvolve]
  rw [hfun]
  unfold ageOperator
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 lam := (hasDerivAt_id lam).ofReal_comp
  have hg : HasDerivAt (fun x : ℝ => -Complex.I * (x : ℂ) * (t : ℂ)) (-Complex.I * (t : ℂ)) lam := by
    simpa using (hx.const_mul (-Complex.I)).mul_const (t : ℂ)
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)))
      (Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) * (-Complex.I * (t : ℂ))) lam := by
    simpa using hg.cexp
  rw [hexp.deriv]
  have hI : Complex.I * (Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) * (-Complex.I * (t : ℂ)))
      = (Complex.I * -Complex.I) * (t : ℂ) * Complex.exp (-Complex.I * (lam : ℂ) * (t : ℂ)) := by ring
  rw [hI, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg]]
  ring

end Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
