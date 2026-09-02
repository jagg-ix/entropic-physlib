/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The affine–Killing exponential on a bifurcate Killing horizon: the geometric origin of the Hawking temperature (Kay–Wald §2)

Formalizes the geometric heart of §2 of Kay–Wald (Phys. Rep. 207 (1991)): on a bifurcate Killing horizon, the
horizon-generating Killing field `ξ` is related to the affine tangent `l` by `ξ = f l` with `f = κU` (their
Eq. 2.1), so the affine parameter `U` is the **exponential of the Killing parameter** `v`,

`U = e^{κv}`,

with `κ` the surface gravity. This exponential map is the geometric origin of the Hawking temperature: the
imaginary-Killing-time periodicity of `U` is `2π/κ`, which *is* the KMS inverse temperature `β = 1/T_H` of the
Kay–Wald thermal state (`KayWaldHawkingKMSHorizon`).

* the **affine parameter is the exponential of the Killing parameter** `U = e^{κv}` (`affineParameter`, Eq. 2.1);
* the **Killing field is `ξ = κU ∂_U`** — the derivative `dU/dv = κU` (`affineParameter_hasDerivAt`), the surface
  gravity as the rate of exponential stretching of the affine parameter along the Killing flow;
* the **imaginary-Killing-time period is `2π/κ`** — the complexified affine parameter satisfies
  `U(v + 2πi/κ) = U(v)` (`affineParameter_imaginary_period`), the periodicity in Euclidean Killing time that gives
  the KMS state at the Hawking temperature `T_H = κ/2π`; this period is exactly the Hawking inverse temperature
  `2π/κ = β` (`imaginary_period_is_hawking_beta`).

So the surface gravity `κ` enters the affine–Killing exponential `U = e^{κv}`, and its imaginary-time period
`2π/κ` is the KMS inverse temperature: the geometry of the bifurcate Killing horizon *is* the thermal periodicity
of the Kay–Wald state at `T_H = κ/2π`, on the arc's entropic hub.

* **§A — the affine–Killing exponential `U = e^{κv}`** (`affineParameter`, `affineParameter_hasDerivAt`).
* **§B — the imaginary-time period `2π/κ` is the Hawking inverse temperature** (`affineParameter_imaginary_period`,
  `imaginary_period_is_hawking_beta`).

**Honest layering.** The exponential map, the Killing-field derivative `dU/dv = κU`, and the `2πi/κ` periodicity
are exact `Real.exp`/`Complex.exp` calculus. The four-wedge causal structure, the bifurcation surface geometry,
and the analytic continuation to Euclidean signature are the referenced Kay–Wald §2 content. ## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49, §2 (Eq. 2.1; bifurcate Killing horizon, surface gravity). Repo
  carrier: `EntropicTime.KayWaldHawkingKMSHorizon`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Physlib.Relativity.SemiClassical

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBifurcateHorizonSurfaceGravity


/-- **The affine parameter along the horizon** `U = e^{κv}` (Kay–Wald Eq. 2.1) — the exponential of the Killing
parameter `v`, with `κ` the surface gravity; the relation `ξ = κU ∂_U` between the Killing field and the affine
tangent. -/
noncomputable def affineParameter (κ v : ℝ) : ℝ := Real.exp (κ * v)

/-- **[The Killing field is `ξ = κU ∂_U`] `dU/dv = κU`.** The affine parameter stretches exponentially along the
Killing flow at the rate set by the surface gravity: `d(e^{κv})/dv = κ e^{κv} = κU`, i.e. the horizon-generating
Killing field is `ξ = κU ∂_U`. -/
lemma affineParameter_hasDerivAt (κ v : ℝ) :
    HasDerivAt (affineParameter κ) (κ * affineParameter κ v) v := by
  have h : HasDerivAt (fun v => κ * v) κ v := by
    simpa using (hasDerivAt_id v).const_mul κ
  exact h.exp.congr_deriv (by simp [affineParameter, mul_comm])


/-- **The complexified affine parameter** `U(v) = e^{κv}` for complex Killing time `v` — the analytic continuation
used to read off the KMS periodicity. -/
noncomputable def complexAffineParameter (κ : ℝ) (v : ℂ) : ℂ := Complex.exp ((κ : ℂ) * v)

/-- **[The imaginary-Killing-time period is `2π/κ`] `U(v + 2πi/κ) = U(v)`.** The complexified affine parameter is
periodic in imaginary Killing time with period `2π/κ`: `e^{κ(v + 2πi/κ)} = e^{κv}e^{2πi} = e^{κv}`. This Euclidean
periodicity is the KMS condition that makes the Kay–Wald state thermal at the Hawking temperature. -/
lemma affineParameter_imaginary_period (κ : ℝ) (v : ℂ) (hκ : (κ : ℂ) ≠ 0) :
    complexAffineParameter κ (v + 2 * (Real.pi : ℂ) * Complex.I / (κ : ℂ))
      = complexAffineParameter κ v := by
  unfold complexAffineParameter
  rw [show (κ : ℂ) * (v + 2 * (Real.pi : ℂ) * Complex.I / (κ : ℂ))
        = (κ : ℂ) * v + 2 * (Real.pi : ℂ) * Complex.I by field_simp,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **[The imaginary-time period is the Hawking inverse temperature] `2π/κ = β_H`.** In natural units
(`ℏ = c = kB = 1`) the imaginary-Killing-time period `2π/κ` of the affine parameter is exactly the Hawking inverse
temperature `β = 1/T_H` (`hawkingBeta`): the geometric periodicity of the bifurcate Killing horizon is the KMS
inverse temperature of the thermal state at `T_H = κ/2π`. -/
lemma imaginary_period_is_hawking_beta (κ : ℝ) (hκ : κ ≠ 0) :
    2 * Real.pi / κ = hawkingBeta 1 κ 1 1 := by
  unfold hawkingBeta hawkingTemperature
  field_simp

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBifurcateHorizonSurfaceGravity

end
