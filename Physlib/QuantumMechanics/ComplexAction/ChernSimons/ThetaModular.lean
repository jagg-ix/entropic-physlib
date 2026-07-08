/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TorusHilbert
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# The level-`k` Chern–Simons–Witten theta character and its modular transforms

Upgrades the single theta *mode* `thetaMode` of `ChernSimons.TorusHilbert` to the full level-`k`,
charge-zero CSW theta **character** — the lattice sum over `n ∈ ℤ` — and equips it with the modular
transformation laws, by identifying it with Mathlib's two-variable Jacobi theta function.

* **§A — the lattice sum and the Jacobi bridge.** `cswTheta k τ z := ∑' n, θ_n(τ,z)` (the charge-zero
  level-`k` character). Term by term it is Mathlib's `jacobiTheta₂_term`, so
  `cswTheta k τ z = jacobiTheta₂ (k·z) (k·τ)` (`cswTheta_eq_jacobiTheta₂`) — the whole Mathlib modular
  machinery transports across this rescaling.
* **§B — `T` and lattice periodicities (integer level).** At an integer level `K` the character is invariant
  under the modular `T²` shift `τ ↦ τ + 2` (`cswTheta_tau_add_two`) and under the Wilson-line / lattice
  shift `z ↦ z + 1` (`cswTheta_z_add_one`) — each holds term by term because `K·n²`, `K·n ∈ ℤ` make the
  extra phase `e^{2πi·ℤ} = 1`. These are exactly where Witten's **integer** quantization of `k` is used.
* **§C — the modular `S` transform (Poisson summation).** `cswTheta_modular_S` is the functional equation
  under `τ ↦ −1/(kτ)`, with the `1/√(−ikτ)` and Gaussian factors — Mathlib's
  `jacobiTheta₂_functional_equation`, the deep Poisson-summation input, transported across the bridge.

This realizes part of item (7) (theta/Weyl–Kac characters, heat equations, modular transforms) of the CSW
program. The general-charge character (`m = n + a/k`), the modular `S`-matrix on the multiplet of characters,
and the non-abelian Weyl–Kac formula remain open.

## References

* E. Witten (1989, 1991); Hayashi (the CSW-gravity torus theorem). `Mathlib`
  (`jacobiTheta₂`, `jacobiTheta₂_functional_equation`).

No new axioms.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — the lattice sum and the Jacobi bridge -/

/-- **[Each CSW theta mode is a Jacobi theta term]** `θ_n(τ,z) = jacobiTheta₂_term n (k·z) (k·τ)`: the
level-`k` mode is Mathlib's two-variable Jacobi summand at the rescaled arguments `(k·z, k·τ)`. -/
theorem thetaMode_eq_jacobiTheta₂_term (k τ z : ℂ) (n : ℤ) :
    thetaMode k (n : ℂ) τ z = jacobiTheta₂_term n (k * z) (k * τ) := by
  rw [thetaMode, jacobiTheta₂_term]
  congr 1
  ring

/-- **The level-`k`, charge-zero CSW theta character** `Θ_k(τ,z) = Σ_{n∈ℤ} θ_n(τ,z)` — the full lattice sum
of the level-`k` theta modes (the building block of the torus conformal blocks). -/
noncomputable def cswTheta (k τ z : ℂ) : ℂ :=
  ∑' (n : ℤ), thetaMode k (n : ℂ) τ z

/-- **[The CSW character is a rescaled Jacobi theta]** `Θ_k(τ,z) = jacobiTheta₂ (k·z) (k·τ)`. This bridge
transports every Mathlib modular identity to the CSW character. -/
theorem cswTheta_eq_jacobiTheta₂ (k τ z : ℂ) :
    cswTheta k τ z = jacobiTheta₂ (k * z) (k * τ) := by
  unfold cswTheta jacobiTheta₂
  exact tsum_congr (fun n => thetaMode_eq_jacobiTheta₂_term k τ z n)

/-! ## §B — `T` and lattice periodicities (integer level) -/

/-- **[Modular `T²` periodicity, integer level]** `Θ_K(τ + 2, z) = Θ_K(τ, z)`. At integer level the
character is invariant under the modular `T²` shift, because the extra phase `e^{2πi·K n²}` is `1`
(`K n² ∈ ℤ`). -/
theorem cswTheta_tau_add_two (K : ℤ) (τ z : ℂ) :
    cswTheta (K : ℂ) (τ + 2) z = cswTheta (K : ℂ) τ z := by
  unfold cswTheta
  refine tsum_congr (fun n => ?_)
  have hstep : thetaMode (K : ℂ) (n : ℂ) (τ + 2) z
      = thetaMode (K : ℂ) (n : ℂ) τ z
        * Complex.exp (((K * n ^ 2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    simp only [thetaMode, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hstep, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **[Lattice / Wilson-line periodicity, integer level]** `Θ_K(τ, z + 1) = Θ_K(τ, z)`. At integer level the
character is invariant under the unit lattice shift in `z`, because the extra phase `e^{2πi·K n}` is `1`
(`K n ∈ ℤ`). -/
theorem cswTheta_z_add_one (K : ℤ) (τ z : ℂ) :
    cswTheta (K : ℂ) τ (z + 1) = cswTheta (K : ℂ) τ z := by
  unfold cswTheta
  refine tsum_congr (fun n => ?_)
  have hstep : thetaMode (K : ℂ) (n : ℂ) τ (z + 1)
      = thetaMode (K : ℂ) (n : ℂ) τ z
        * Complex.exp (((K * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    simp only [thetaMode, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hstep, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## §C — the modular `S` transform (Poisson summation) -/

/-- **[Modular `S` transform / functional equation]** `Θ_k(τ,z)` equals an explicit Gaussian × square-root
factor times the Jacobi theta at the inverted modular parameter `−1/(kτ)`. This is Mathlib's
`jacobiTheta₂_functional_equation` (the Poisson-summation input), transported across the Jacobi bridge — the
genuine modular `S` covariance of the CSW conformal block, not a termwise rearrangement. -/
theorem cswTheta_modular_S (k τ z : ℂ) :
    cswTheta k τ z =
      1 / (-Complex.I * (k * τ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (k * z) ^ 2 / (k * τ))
        * jacobiTheta₂ ((k * z) / (k * τ)) (-1 / (k * τ)) := by
  rw [cswTheta_eq_jacobiTheta₂]
  exact jacobiTheta₂_functional_equation (k * z) (k * τ)

/-- **[Modular `S` transform, modular argument simplified]** For nonzero level the inverted modular
parameter's Jacobi argument simplifies to `z/τ`. -/
theorem cswTheta_modular_S_arg (k τ z : ℂ) (hk : k ≠ 0) :
    cswTheta k τ z =
      1 / (-Complex.I * (k * τ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (k * z) ^ 2 / (k * τ))
        * jacobiTheta₂ (z / τ) (-1 / (k * τ)) := by
  rw [cswTheta_modular_S, mul_div_mul_left z τ hk]

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
