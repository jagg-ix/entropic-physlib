/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaModular

/-!
# The general-charge level-`k` Chern–Simons–Witten theta characters

Generalizes the charge-zero character `cswTheta` of `ChernSimons.ThetaModular` to the **full multiplet**
of level-`k` characters with a charge / twist `a` (mode label `m = n + a`), and gives each its closed
form and modular transformations through Mathlib's two-variable Jacobi theta.

* **§A — the shifted character and its closed form.** `cswThetaCharge k a τ z := Σ_n θ_{n+a}(τ,z)` is the
  level-`k` character of charge `a`. The `a`-shift factors out a Gaussian prefactor, leaving a Jacobi theta
  at a `τ`-shifted `z`-argument: `cswThetaCharge k a τ z = e^{iπk(a²τ + 2az)} · jacobiTheta₂ (k(z+aτ)) (kτ)`
  (`cswThetaCharge_eq`). At `a = 0` it is the charge-zero character (`cswThetaCharge_zero`).
* **§B — charge is defined mod the lattice.** Shifting the charge by an integer lattice unit leaves the
  character unchanged (`cswThetaCharge_add_one`) — the level-`k` characters are labelled by `a` mod `1`, i.e.
  by `k` distinct charges, just by reindexing the lattice sum.
* **§C — the modular `S` transform of a charge sector.** Each charge sector obeys the functional equation
  under `τ ↦ −1/(kτ)` (`cswThetaCharge_modular_S`), via `jacobiTheta₂_functional_equation`. This is the
  per-character input from which the Verlinde `S`-matrix on the character multiplet is assembled.

Advances item (7). Still open: the closed-form **`S`-matrix** `Θ_a(−1/τ) = Σ_b S_{ab} Θ_b(τ)` resolving the
inversion into a finite sum over charges (a discrete Gauss sum / Poisson decomposition over residues mod
`k`), and the non-abelian Weyl–Kac character.

## References

* E. Witten (1989, 1991); Hayashi (the CSW-gravity torus theorem). `Mathlib`
  (`jacobiTheta₂`, `jacobiTheta₂_functional_equation`).

No new axioms.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — the shifted character and its closed form -/

/-- **The Gaussian charge prefactor** `e^{iπk(a²τ + 2az)}` produced by completing the square on the
charge-`a` shift of the lattice. -/
noncomputable def thetaChargePrefactor (k a τ z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * k * a ^ 2 * τ + 2 * Complex.I * (Real.pi : ℂ) * k * a * z)

/-- **[Each shifted mode splits into the prefactor times a Jacobi term]**
`θ_{n+a}(τ,z) = e^{iπk(a²τ+2az)} · jacobiTheta₂_term n (k(z+aτ)) (kτ)` — completing the square moves the
`a`-shift into the Gaussian prefactor and a `τ`-shift of the `z`-argument. -/
theorem thetaMode_shift_eq (k a τ z : ℂ) (n : ℤ) :
    thetaMode k ((n : ℂ) + a) τ z
      = thetaChargePrefactor k a τ z * jacobiTheta₂_term n (k * (z + a * τ)) (k * τ) := by
  rw [thetaMode, thetaChargePrefactor, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

/-- **The level-`k`, charge-`a` CSW theta character** `Θ_{k,a}(τ,z) = Σ_{n∈ℤ} θ_{n+a}(τ,z)`. -/
noncomputable def cswThetaCharge (k a τ z : ℂ) : ℂ :=
  ∑' (n : ℤ), thetaMode k ((n : ℂ) + a) τ z

/-- **[Closed form of the charge-`a` character]**
`Θ_{k,a}(τ,z) = e^{iπk(a²τ+2az)} · jacobiTheta₂ (k(z+aτ)) (kτ)`. -/
theorem cswThetaCharge_eq (k a τ z : ℂ) :
    cswThetaCharge k a τ z
      = thetaChargePrefactor k a τ z * jacobiTheta₂ (k * (z + a * τ)) (k * τ) := by
  unfold cswThetaCharge jacobiTheta₂
  rw [tsum_congr (fun n => thetaMode_shift_eq k a τ z n), tsum_mul_left]

/-- **[Charge zero is the basic character]** `Θ_{k,0} = Θ_k`. -/
theorem cswThetaCharge_zero (k τ z : ℂ) :
    cswThetaCharge k 0 τ z = cswTheta k τ z := by
  unfold cswThetaCharge cswTheta
  exact tsum_congr (fun n => by rw [add_zero])

/-! ## §B — charge is defined mod the lattice -/

/-- **[Charge defined mod the lattice]** `Θ_{k,a+1} = Θ_{k,a}` — shifting the charge by an integer lattice
unit only reindexes the lattice sum, so the level-`k` characters are labelled by `a` mod `1` (the `k`
distinct charges). -/
theorem cswThetaCharge_add_one (k a τ z : ℂ) :
    cswThetaCharge k (a + 1) τ z = cswThetaCharge k a τ z := by
  unfold cswThetaCharge
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => thetaMode k ((n : ℂ) + a) τ z)]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.coe_addRight]
  rw [show ((n : ℂ) + (a + 1)) = (((n + 1 : ℤ) : ℂ) + a) from by push_cast; ring]

/-! ## §C — the modular `S` transform of a charge sector -/

/-- **[Modular `S` transform of a charge sector]** the charge-`a` character obeys the Jacobi functional
equation under `τ ↦ −1/(kτ)`, with the Gaussian charge prefactor included. This is the per-character
input to the Verlinde `S`-matrix. -/
theorem cswThetaCharge_modular_S (k a τ z : ℂ) :
    cswThetaCharge k a τ z
      = thetaChargePrefactor k a τ z
        * (1 / (-Complex.I * (k * τ)) ^ (1 / 2 : ℂ)
          * Complex.exp (-(Real.pi : ℂ) * Complex.I * (k * (z + a * τ)) ^ 2 / (k * τ))
          * jacobiTheta₂ ((k * (z + a * τ)) / (k * τ)) (-1 / (k * τ))) := by
  rw [cswThetaCharge_eq, jacobiTheta₂_functional_equation (k * (z + a * τ)) (k * τ)]

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
