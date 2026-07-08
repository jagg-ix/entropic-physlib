/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.GreenFunction
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The Nagao–Nielsen Lorentzian FPI propagator realizes the Misra time operator

This file uses the Nagao–Nielsen **Feynman path-integral / Lorentzian** propagator
(`NonHermitianComplexAction.GreenFunction.greenKernel`, the real-time amplitude `e^{−iλt/ℏ}` derived from the
FPI of `PathIntegral.MomentumPathIntegral`) to realize the **Misra–Prigogine–Courbage internal time
operator** (`RelationalTime.LiouvillianAgeOperator`).

## The construction

Misra's spectral Liouvillian is multiplication by the spectral variable
(`spectralLiouvillian f = λ·f`, `L` = energy), and the conjugate **age operator** is
`ageOperator f = i d/dλ` (`T` = internal time), with the canonical conjugacy `i[L,T] = I`
(MPC Eq. 1.3).

View the Lorentzian FPI propagator as a function of the **spectral variable `λ` = energy = the
Liouvillian eigenvalue**:

  `G_λ := greenKernel λ ℏ t = e^{−iλt/ℏ}`.

Then:

* `fpi_spectralLiouvillian_energy` — `L G = λ·G`: the Liouvillian reads off the **energy** `λ`.
* `fpi_ageOperator_eigen` — **`T G = (t/ℏ)·G`**: the Lorentzian propagator is an *eigenfunction
  of the Misra age operator* with eigenvalue `t/ℏ`. The Misra internal time **is** the Feynman
  path-integral time, read off the Lorentzian phase `e^{−iλt/ℏ}`.
* `fpi_liouvillian_age_ccr` — `[L,T] G = −i G`, i.e. `i[L,T] = I` on the FPI propagator: the
  Misra energy–time conjugacy is the FPI's energy–time conjugacy.

So the Nagao–Nielsen Lorentzian path integral is a concrete realization of the MPC
Liouvillian–age conjugate pair: `L` = energy (Liouvillian eigenvalue), `T` = the path-integral
time (age eigenvalue), conjugate by `i[L,T] = I`. This complements
`TimeOperator.MisraAgeFutureIncludedHerglotz` (the abstract Liouville flow `U_t = e^{−iLt}`) by exhibiting
the *Nagao–Nielsen propagator itself* as the joint energy/time spectral object.

## References

* K. Nagao, H. B. Nielsen, arXiv:1304.4017 (FPI momentum relation, Lorentzian propagator);
  Sergi–Giaquinta 2016 (`H_C = H_R − iH_I`).
* B. Misra, I. Prigogine, M. Courbage 1979 (the time operator `T`, `i[L,T] = I`);
  `RelationalTime.LiouvillianAgeOperator`, `RelationalTime.MisraAgeFutureIncludedHerglotz`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.RelationalTime

namespace Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.PropagatorTimeOperator

/-- The Lorentzian FPI propagator as a function of the **spectral variable** `λ` (= energy =
Liouvillian eigenvalue): `G_λ = greenKernel λ ℏ t = e^{−iλt/ℏ}`. -/
noncomputable def fpiSpectralKernel (ℏ t : ℝ) : ℝ → ℂ :=
  fun lam => greenKernel (lam : ℂ) ℏ t

/-- **The propagator is differentiable in the spectral variable**, with
`d/dλ G = G·(−i t/ℏ)`. -/
theorem fpiSpectralKernel_hasDerivAt (ℏ t lam : ℝ) :
    HasDerivAt (fpiSpectralKernel ℏ t)
      (greenKernel (lam : ℂ) ℏ t * (-Complex.I * 1 * (t : ℂ) / (ℏ : ℂ))) lam := by
  have hofR : HasDerivAt (fun lam : ℝ => (lam : ℂ)) 1 lam := by
    simpa using (hasDerivAt_id lam).ofReal_comp
  exact (((hofR.const_mul (-Complex.I)).mul_const (t : ℂ)).div_const (ℏ : ℂ)).cexp

/-- **`L` reads off the energy**: `spectralLiouvillian G = λ·G` — the Liouvillian eigenvalue on
the FPI propagator is the energy `λ`. -/
theorem fpi_spectralLiouvillian_energy (ℏ t lam : ℝ) :
    spectralLiouvillian (fpiSpectralKernel ℏ t) lam = (lam : ℂ) * greenKernel (lam : ℂ) ℏ t :=
  rfl

/-- **`T` reads off the path-integral time**: `ageOperator G = (t/ℏ)·G` — the Lorentzian FPI
propagator is an *eigenfunction of the Misra age operator* with eigenvalue `t/ℏ`. The Misra
internal time is the Feynman path-integral time, read off the Lorentzian phase. -/
theorem fpi_ageOperator_eigen (ℏ t lam : ℝ) :
    ageOperator (fpiSpectralKernel ℏ t) lam = ((t / ℏ : ℝ) : ℂ) * greenKernel (lam : ℂ) ℏ t := by
  unfold ageOperator
  rw [(fpiSpectralKernel_hasDerivAt ℏ t lam).deriv]
  push_cast
  rw [show Complex.I * (greenKernel (↑lam) ℏ t * (-Complex.I * 1 * ↑t / ↑ℏ))
      = (Complex.I * (-Complex.I * 1)) * (↑t / ↑ℏ) * greenKernel (↑lam) ℏ t by ring,
    show Complex.I * (-Complex.I * 1) = 1 by rw [mul_one, mul_neg, Complex.I_mul_I, neg_neg],
    one_mul]

/-- **The Misra conjugacy `i[L,T] = I` on the FPI propagator**: `[L,T] G = −i G`. The
Nagao–Nielsen energy–time structure of the Lorentzian propagator is exactly the MPC
Liouvillian–age canonical commutation relation. -/
theorem fpi_liouvillian_age_ccr (ℏ t lam : ℝ) :
    spectralLiouvillian (ageOperator (fpiSpectralKernel ℏ t)) lam
        - ageOperator (spectralLiouvillian (fpiSpectralKernel ℏ t)) lam
      = -Complex.I * fpiSpectralKernel ℏ t lam :=
  liouvillian_age_commutator (fpiSpectralKernel ℏ t) lam
    (fpiSpectralKernel_hasDerivAt ℏ t lam).differentiableAt

end Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.PropagatorTimeOperator

end

end
