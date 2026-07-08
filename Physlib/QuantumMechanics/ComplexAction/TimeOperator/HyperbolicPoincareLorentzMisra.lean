/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.PropagatorTimeOperator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Poincaré sphere is hyperbolic: Lorentz boost, Minkowski mass-shell, and the Misra time operator

The polar Poincaré coordinate of the Bogoliubov quasiparticle is `S₃ = u² − v² = ξ/E`
(`Bogoliubov.Transformation.bogoliubov_uv_diff`). This file **recognizes that this is hyperbolic
(Lorentzian) geometry**, not spherical:

* the Bogoliubov pair `(E, ξ)` is a **timelike Minkowski vector** whose invariant interval is the
  gap, `E² − ξ² = Δ²` — exactly `lorentzianForm` of `ComplexDelta.Convergence`, the
  Lorentzian/Nagao–Nielsen path-integral form (`bogoliubov_energyVector_lorentzianForm`). The gap
  `Δ` is the **invariant mass** on the mass-shell `E² − ξ² = Δ²`;
* the squeeze parametrization `u = cosh θ, v = sinh θ` is a **Lorentz boost** with rapidity `θ`:
  `cosh²θ − sinh²θ = 1` is the unit timelike hyperbola, and the boost preserves the Minkowski form
  `t² − x²` (`lorentzBoost_preserves_form`). The polar coordinate `ξ/E = tanh θ` is the relativistic
  **velocity** `β`, bounded `|β| ≤ 1` (`bogoliubov_velocity_abs_le_one`) — the Poincaré *disk*
  (Lobachevsky / velocity disk), the hyperbolic-geometry model;
* the **Misra–Prigogine–Courbage time operator** (`RelationalTime.LiouvillianAgeOperator`, realized
  on the Lorentzian FPI propagator in `NonHermitianComplexAction.PropagatorTimeOperator`) reads the internal time `t/ℏ`
  as the **future-pointing time coordinate** of a timelike Lorentz vector
  (`misraAge_timelikeFuture`), conjugate to the energy `λ` by `i[L,T] = I`
  (`fpi_liouvillian_age_ccr`). So the Misra internal time is a Minkowski future time on the same
  hyperbolic geometry.

## Main results

* `lorentzianForm_ofReal_add_mul_I` — `L(a + ib) = a² − b²` (the Minkowski form in coordinates).
* `bogoliubov_energyVector_lorentzianForm` — `L(E + iξ) = Δ²` (the mass-shell; gap = invariant mass).
* `bogoliubov_energyVector_timelike` — `(E, ξ)` is timelike for a genuine gap `Δ ≠ 0`.
* `boostVector_lorentzianForm` — `L(Δcosh θ + iΔsinh θ) = Δ²` (the boost orbit / unit hyperbola).
* `lorentzBoost_preserves_form` — the Lorentz boost preserves `t² − x²` (Lorentz invariance).
* `bogoliubov_velocity_abs_le_one`, `boostVector_velocity` — `ξ/E = tanh θ = β`, `|β| ≤ 1`.
* `misraAge_timelikeFuture` — the Misra age eigenvalue `t/ℏ` is a future-pointing Minkowski time.
* `hyperbolic_lorentz_misra` — **the link**: mass-shell `L(E+iξ)=Δ²`, boost invariance, and the
  Misra conjugacy `i[L,T]=I` hold together on the hyperbolic geometry.

## References

* H. Poincaré (sphere); the Poincaré disk model of hyperbolic geometry. N. N. Bogoljubov (1958).
* K. Nagao, H. B. Nielsen, arXiv:1304.4017 (Lorentzian FPI). B. Misra, I. Prigogine, M. Courbage
  1979 (time operator `i[L,T]=I`). `ComplexDelta.Convergence`, `Rapidity.FutureIncludedLorentzian`,
  `Bogoliubov.Transformation`, `NonHermitianComplexAction.PropagatorTimeOperator` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.PropagatorTimeOperator
open Physlib.QuantumMechanics.RelationalTime

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

/-! ## §A — the Minkowski form in coordinates, and the Bogoliubov mass-shell -/

/-- **The Minkowski / Lorentzian form in coordinates** `L(a + ib) = a² − b²` (`a` = time, `b` =
space): the Nagao–Nielsen `lorentzianForm` of the contour point `a + ib`. -/
theorem lorentzianForm_ofReal_add_mul_I (a b : ℝ) :
    lorentzianForm ((a : ℂ) + (b : ℂ) * Complex.I) = a ^ 2 - b ^ 2 := by
  simp [lorentzianForm, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **The Bogoliubov mass-shell**: the quasiparticle pair `(E, ξ)` has Minkowski interval equal to
the gap squared, `L(E + iξ) = E² − ξ² = Δ²`. The gap `Δ` is the **invariant mass**; `E = √(ξ²+Δ²)`
is the relativistic dispersion `E² = ξ² + Δ²`. This is the hyperbolic (Lorentzian) geometry behind
the polar Poincaré coordinate. -/
theorem bogoliubov_energyVector_lorentzianForm (ξ Δ : ℝ) :
    lorentzianForm ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I) = Δ ^ 2 := by
  rw [lorentzianForm_ofReal_add_mul_I]
  unfold bogoliubovEnergy
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- **The Bogoliubov energy vector is timelike** for a genuine gap `Δ ≠ 0`: `L(E + iξ) = Δ² > 0`.
The quasiparticle lives inside the causal cone — the dispersion is on the mass-shell. -/
theorem bogoliubov_energyVector_timelike (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    timelike ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I) := by
  unfold timelike
  rw [bogoliubov_energyVector_lorentzianForm]
  positivity

/-! ## §B — the squeeze is a Lorentz boost; the polar coordinate is the velocity (Poincaré disk) -/

/-- **The boost orbit vector** `Δcosh θ + iΔsinh θ` (rapidity `θ`): the squeeze parametrization of
the Bogoliubov pair, `E = Δcosh θ`, `ξ = Δsinh θ`. -/
def boostVector (Δ θ : ℝ) : ℂ :=
  ((Δ * Real.cosh θ : ℝ) : ℂ) + ((Δ * Real.sinh θ : ℝ) : ℂ) * Complex.I

/-- **The boost orbit is the unit timelike hyperbola scaled by the mass**: `L(boostVector Δ θ) = Δ²`
for every rapidity `θ` (`cosh²θ − sinh²θ = 1`). The rapidity slides along the mass-shell without
changing the invariant mass `Δ` — a Lorentz boost. -/
theorem boostVector_lorentzianForm (Δ θ : ℝ) :
    lorentzianForm (boostVector Δ θ) = Δ ^ 2 := by
  unfold boostVector
  rw [lorentzianForm_ofReal_add_mul_I, mul_pow, mul_pow, ← mul_sub,
    Real.cosh_sq_sub_sinh_sq, mul_one]

/-- **The Lorentz boost** with rapidity `θ` acting on a `(time, space)` pair. -/
def lorentzBoost (θ t x : ℝ) : ℝ × ℝ :=
  (Real.cosh θ * t + Real.sinh θ * x, Real.sinh θ * t + Real.cosh θ * x)

/-- **The Lorentz boost preserves the Minkowski form** `t² − x²` (Lorentz invariance of the
Nagao–Nielsen Lorentzian path-integral form). This is the symmetry that slides the Bogoliubov pair
along its mass-shell. -/
theorem lorentzBoost_preserves_form (θ t x : ℝ) :
    (lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2 := by
  simp only [lorentzBoost]
  linear_combination (t ^ 2 - x ^ 2) * Real.cosh_sq_sub_sinh_sq θ

/-- **The boost velocity is the hyperbolic tangent of the rapidity**: `ξ/E = sinh θ / cosh θ =
tanh θ`. The polar Poincaré coordinate is the relativistic velocity `β = tanh θ`. -/
theorem boostVector_velocity (Δ θ : ℝ) (hΔ : Δ ≠ 0) :
    (Δ * Real.sinh θ) / (Δ * Real.cosh θ) = Real.tanh θ := by
  rw [mul_div_mul_left _ _ hΔ, Real.tanh_eq_sinh_div_cosh]

/-- **The polar Poincaré coordinate is a sub-luminal velocity** `|ξ/E| ≤ 1`: the Bogoliubov
coherence difference `u² − v² = ξ/E` lies in `[−1, 1]`, the **Poincaré (velocity / Lobachevsky)
disk** — the hyperbolic-geometry model of the polarisation state. -/
theorem bogoliubov_velocity_abs_le_one (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    |ξ / bogoliubovEnergy ξ Δ| ≤ 1 := by
  have hE : 0 < bogoliubovEnergy ξ Δ := by
    unfold bogoliubovEnergy; exact Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hE, div_le_one hE]
  exact abs_le_bogoliubovEnergy ξ Δ

/-! ## §C — the Misra internal time is a future-pointing Minkowski time -/

/-- **The Misra internal time is a future-pointing Lorentz time**: the age-operator eigenvalue
`t/ℏ` (the Misra internal time the Lorentzian FPI propagator records,
`NonHermitianComplexAction.PropagatorTimeOperator.fpi_ageOperator_eigen`) is the time coordinate of a *timelike future*
Minkowski vector `t/ℏ + ix` whenever `|x| < t/ℏ`. The Misra arrow of time **is** the future cone of
the Nagao–Nielsen Lorentzian structure (`Rapidity.FutureIncludedLorentzian.timelikeFuture`). -/
theorem misraAge_timelikeFuture (ℏ t x : ℝ) (hℏ : 0 < ℏ) (ht : 0 < t) (hx : |x| < t / ℏ) :
    timelikeFuture (((t / ℏ : ℝ) : ℂ) + ((x : ℝ) : ℂ) * Complex.I) := by
  have hpos : 0 < t / ℏ := div_pos ht hℏ
  refine ⟨?_, ?_⟩
  · unfold timelike
    rw [lorentzianForm_ofReal_add_mul_I]
    nlinarith [sq_abs x, abs_nonneg x, hx, hpos]
  · have hre : (((t / ℏ : ℝ) : ℂ) + ((x : ℝ) : ℂ) * Complex.I).re = t / ℏ := by
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre]; exact hpos

/-! ## §D — the link: hyperbolic geometry, Lorentz boost, and the Misra conjugacy together -/

/-- **The link.** On the hyperbolic (Lorentzian) geometry of the Poincaré data, three structures
hold simultaneously:

* **mass-shell** — the Bogoliubov pair `(E, λ)` is on the Minkowski mass-shell `L(E + iλ) = Δ²`
  (the gap is the invariant mass);
* **Lorentz invariance** — the boost with any rapidity `θ` preserves the Minkowski form `t² − x²`
  (the squeeze slides along the mass-shell);
* **Misra conjugacy** — the Lorentzian FPI propagator includes the Misra energy/time pair with
  `i[L,T] = I` (`[L,T] G = −i G`): the energy `λ` (Liouvillian eigenvalue) and the internal time
  `t/ℏ` (age eigenvalue) are the two conjugate Minkowski axes.

So the Poincaré sphere's polar coordinate is a Lorentz velocity, the squeeze is a boost, and the
Misra internal time is the conjugate future-Minkowski time on the same hyperbolic geometry. -/
theorem hyperbolic_lorentz_misra (ℏ t lam Δ : ℝ) :
    lorentzianForm ((bogoliubovEnergy lam Δ : ℂ) + (lam : ℂ) * Complex.I) = Δ ^ 2
      ∧ (∀ θ x : ℝ,
          (lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2)
      ∧ spectralLiouvillian (ageOperator (fpiSpectralKernel ℏ t)) lam
          - ageOperator (spectralLiouvillian (fpiSpectralKernel ℏ t)) lam
        = -Complex.I * fpiSpectralKernel ℏ t lam :=
  ⟨bogoliubov_energyVector_lorentzianForm lam Δ,
   fun θ x => lorentzBoost_preserves_form θ t x,
   fpi_liouvillian_age_ccr ℏ t lam⟩

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

end

end
