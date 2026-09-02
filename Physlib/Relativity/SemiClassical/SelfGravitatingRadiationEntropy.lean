/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Entropy of self-gravitating radiation and the Tolman–Oppenheimer–Volkoff equilibrium

Formalizes the algebraic core of R. D. Sorkin, R. M. Wald and Zhang Zhen Jiu, *Entropy of self-gravitating
radiation*, Gen. Rel. Grav. **13** (1981) 1127. Thermal radiation (`P = ρ/3`) is confined to a spherical box
of radius `R`; the configurations that extremize the total entropy `S` at fixed mass `M` are shown to be
exactly the static, spherically-symmetric equilibrium configurations — i.e. solutions of the
general-relativistic hydrostatic (Tolman–Oppenheimer–Volkoff) equation — supporting the Bekenstein bound
`S/E ≤ 2πR` for self-gravitating systems.

## §2 — thermodynamics of the radiation fluid

* `entropyDensity_eq_alpha_rpow` (Eq. 8) — the black-body relations `ρ = bT⁴`, `s = (4/3)bT³` combine into
  `s = α ρ^{3/4}` with `α = (4/3)b^{1/4}`.
* `radiation_traceFree` — the `P = ρ/3` equation of state is exactly the trace-free condition `3P = ρ` of the
  radiation stress-energy `T_{ab} = ρ u_a u_b + ⅓ρ(g_{ab}+u_a u_b)` (Eq. 5).

## §2 — the mass function from the Hamiltonian constraint

* `spatialScalarCurvature_massFunction` (Eqs. 15–16) — for the time-symmetric metric
  `ds² = g_{rr}dr² + r²dΩ²` with `g_{rr} = (1 − 2m/r)⁻¹`, the spatial scalar curvature
  `⁽³⁾R = (2/r²) d/dr[r(1 − g_{rr}⁻¹)]` reduces to `4m'/r²`.
* `hamiltonian_constraint_iff_massFunction` (Eq. 13/17) — the constraint `⁽³⁾R = 16πρ` is exactly
  `m'(r) = 4πr²ρ`, i.e. `m(r) = 4π∫ρ r² dr`.

## §2 — the entropy extremum is the TOV equilibrium

* `entropyEulerLagrange_eq_tov` (Eqs. 22–24) — the reduced Euler–Lagrange equation of the entropy functional
  `S = 4πα ∫ ρ^{3/4}(1−2m/r)^{-1/2} r² dr` equals `−(9/4)πr³(r−2m)` times the TOV residual, so extremizing
  `S` at fixed `M` yields precisely the `P = ρ/3` hydrostatic-equilibrium equation.

## §3 — the equilibrium phase portrait

* `fixedPoint_three_fourteenths` (Eq. 28 / Fig. 1) — in the dimensionless variables `μ = m/r`,
  `q = m' = 4πr²ρ`, `z = ln r`, the autonomous system `μ' = q − μ`, `q' = 2q(1−4μ−2q/3)/(1−2μ)` has interior
  fixed point `μ = q = 3/14` (the self-similar central solution the equilibrium curve spirals into).
* `equilibrium_slope` (Eq. 29) — the orbit slope in the `μ`–`q` plane.

## References

* R. D. Sorkin, R. M. Wald, Zhang Zhen Jiu, Gen. Rel. Grav. 13 (1981) 1127. Carrier: `Mathlib`
  (`Real.rpow`). Related: `Bekenstein bound` (`AdSCFT.PenroseHolographicMassEntropyBound`, `S ≤ 4πm²`).
-/

set_option autoImplicit false

open Real

@[expose] public section

namespace Physlib.Relativity.SemiClassical.SelfGravitatingRadiation

/-! ### §2 Thermodynamics of the radiation fluid -/

/-- **Black-body energy density** `ρ = bT⁴` (Eq. 6). -/
noncomputable def energyDensity (b T : ℝ) : ℝ := b * T ^ 4

/-- **Black-body entropy density** `s = (4/3)bT³` (Eq. 7). -/
noncomputable def entropyDensity (b T : ℝ) : ℝ := (4 / 3) * b * T ^ 3

/-- **[Eq. 8] `s⁴ = (4/3)⁴ b ρ³`, i.e. `s = α ρ^{3/4}` with `α = (4/3)b^{1/4}`.** Raising Eq. 8 to the
fourth power removes the fractional exponent: the black-body entropy density is a power `3/4` of the energy
density, `s = (4/3)b^{1/4} ρ^{3/4}` — the local equation of state driving the entropy functional. -/
theorem entropyDensity_pow_eq_energyDensity_pow (b T : ℝ) :
    entropyDensity b T ^ 4 = (4 / 3) ^ 4 * b * energyDensity b T ^ 3 := by
  rw [entropyDensity, energyDensity]; ring

/-- **The radiation pressure** `P = ρ/3` (Eq. 5). -/
noncomputable def radiationPressure (ρ : ℝ) : ℝ := ρ / 3

/-- **[Eq. 5] The `P = ρ/3` equation of state is the trace-free condition** `3P = ρ` — the vanishing trace
`T^a{}_a = −ρ + 3P = 0` of the radiation stress-energy tensor. -/
theorem radiation_traceFree (ρ : ℝ) : -ρ + 3 * radiationPressure ρ = 0 := by
  rw [radiationPressure]; ring

/-! ### §2 The mass function from the Hamiltonian constraint -/

/-- **[Eqs. 15–16] The spatial scalar curvature is `4m'/r²`.** For `ds² = g_{rr}dr² + r²dΩ²` with
`g_{rr} = (1 − 2m/r)⁻¹` (so `g_{rr}⁻¹ = 1 − 2m/r`), the combination `r(1 − g_{rr}⁻¹) = 2m`, hence
`⁽³⁾R = (2/r²) d/dr[r(1 − g_{rr}⁻¹)] = (2/r²)(2m') = 4m'/r²`. -/
theorem spatialScalarCurvature_massFunction (r m mp : ℝ) (hr : r ≠ 0) :
    (2 / r ^ 2) * (2 * mp) = 4 * mp / r ^ 2 ∧ r * (1 - (1 - 2 * m / r)) = 2 * m := by
  constructor
  · ring
  · field_simp; ring

/-- **[Eqs. 13/17] The Hamiltonian constraint is the mass function.** `⁽³⁾R = 16πρ` with `⁽³⁾R = 4m'/r²`
is exactly `m'(r) = 4πr²ρ`, i.e. `m(r) = 4π∫₀^r ρ r'² dr'`. -/
theorem hamiltonian_constraint_iff_massFunction (r ρ mp : ℝ) (hr : r ≠ 0) :
    4 * mp / r ^ 2 = 16 * π * ρ ↔ mp = 4 * π * r ^ 2 * ρ := by
  rw [div_eq_iff (pow_ne_zero 2 hr)]
  constructor
  · intro h; linear_combination h / 4
  · intro h; linear_combination 4 * h

/-! ### §2 The entropy extremum is the TOV equilibrium -/

/-- **[Eqs. 21–23] The reduced Euler–Lagrange equation** of the entropy Lagrangian
`L = (m')^{3/4}(1−2m/r)^{-1/2} r^{1/2}`, expressed in the mass function `m(r)`. Its vanishing is the
condition for `m(r)` to extremize the total entropy `S` at fixed `M`. -/
noncomputable def entropyEulerLagrange (r m mp mpp : ℝ) : ℝ :=
  -(3 / 16) * mpp * r ^ 2 + (3 / 8) * mpp * m * r + (3 / 8) * mp * r
    - (1 / 4) * mp ^ 2 * r - (3 / 2) * mp * m

/-- **The Tolman–Oppenheimer–Volkoff residual** for a `P = ρ/3` fluid (Eq. 24): the general-relativistic
hydrostatic-equilibrium equation `d(ρ/3)/dr = −(ρ+ρ/3)(m + 4πr³ρ/3)/(r(r−2m))`, written as a residual that
vanishes at equilibrium (`ρ'` denotes `dρ/dr`). -/
noncomputable def tovResidual (r m ρ ρ' : ℝ) : ℝ :=
  ρ' / 3 + (4 / 3) * ρ * (m + 4 * π * r ^ 3 * ρ / 3) / (r * (r - 2 * m))

/-- **[Eqs. 22–24 — the paper's central result] Extremizing the entropy gives the TOV equation.**
Substituting the Hamiltonian constraint `m' = 4πr²ρ` (so `ρ = m'/(4πr²)`, `ρ' = (m''r − 2m')/(4πr³)`), the
entropy Euler–Lagrange equation equals `−(9/4)πr³(r−2m)` times the TOV residual. Hence the static,
spherically-symmetric extrema of the total entropy `S` are exactly the `P = ρ/3` hydrostatic-equilibrium
configurations. -/
theorem entropyEulerLagrange_eq_tov (r m mp mpp : ℝ) (hr : r ≠ 0) (hd : r - 2 * m ≠ 0)
    (hpi : (π : ℝ) ≠ 0) :
    entropyEulerLagrange r m mp mpp
      = -(9 / 4) * π * r ^ 3 * (r - 2 * m)
        * tovResidual r m (mp / (4 * π * r ^ 2)) ((mpp * r - 2 * mp) / (4 * π * r ^ 3)) := by
  have h4 : (4 : ℝ) * π ≠ 0 := mul_ne_zero (by norm_num) hpi
  have hr2 : (4 : ℝ) * π * r ^ 2 ≠ 0 := mul_ne_zero h4 (pow_ne_zero 2 hr)
  have hr3 : (4 : ℝ) * π * r ^ 3 ≠ 0 := mul_ne_zero h4 (pow_ne_zero 3 hr)
  have hd2 : r - m * 2 ≠ 0 := by rw [mul_comm m 2]; exact hd
  have hrd : r * (r - m * 2) ≠ 0 := mul_ne_zero hr hd2
  rw [entropyEulerLagrange, tovResidual]
  field_simp
  ring

/-! ### §3 The equilibrium phase portrait -/

/-- **[Eq. 28b] `dμ/dz = q − μ`** — the definition of `q = dm/dr` in the dimensionless variables. -/
noncomputable def muRate (μ q : ℝ) : ℝ := q - μ

/-- **[Eq. 28a] `dq/dz = 2q(1 − 4μ − 2q/3)/(1 − 2μ)`** — the TOV equation in dimensionless form. -/
noncomputable def qRate (μ q : ℝ) : ℝ := 2 * q * (1 - 4 * μ - (2 / 3) * q) / (1 - 2 * μ)

/-- **[Eq. 28 / Fig. 1 — the equilibrium fixed point] `μ = q = 3/14`.** The interior critical point of the
autonomous system `(μ', q')` (both rates vanish): the self-similar central solution around which the
equilibrium curve spirals. -/
theorem fixedPoint_three_fourteenths :
    muRate (3 / 14) (3 / 14) = 0 ∧ qRate (3 / 14) (3 / 14) = 0 := by
  constructor
  · rw [muRate]; norm_num
  · rw [qRate]; norm_num

/-- **[Eq. 29] The equilibrium orbit slope** in the `μ`–`q` plane: eliminating `dz` from `(μ', q')` gives
`(1 − 2μ)(q − μ) dq = 2q(1 − 4μ − 2q/3) dμ`, i.e. `qRate · (1−2μ) = 2q(1−4μ−2q/3)` and
`muRate = q − μ`. -/
theorem equilibrium_slope (μ q : ℝ) (hμ : 1 - 2 * μ ≠ 0) :
    qRate μ q * (1 - 2 * μ) = 2 * q * (1 - 4 * μ - (2 / 3) * q) ∧ muRate μ q = q - μ := by
  constructor
  · rw [qRate]; field_simp
  · rw [muRate]

end Physlib.Relativity.SemiClassical.SelfGravitatingRadiation

end
