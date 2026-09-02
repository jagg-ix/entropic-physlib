/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
meta import Zil

/-!
# The entropic-Newton gravitational hydrogen-like bound state

Plastino–Rocca, *Entropic Forces and Newton's Gravitation* (Entropy 2020, 22, 273): because the
entropic gravitational potential is `−GmM/r` (`EntropicNewtonFiniteAtOrigin`), the reduced radial
Schrödinger equation for two gravitating masses is the **Coulomb/hydrogen form** (their eq. 19, at
`l = 0`)

`U'' + (2μ/ℏ²)(E + GmM/r) U = 0`,

with `GmM` playing the role of the Coulomb charge product.  Its `l = 0` ground state is the
gravitational analogue of hydrogen's `1s`:

`U(r) = r · e^{−r/a}`,   gravitational Bohr radius `a = ℏ²/(μGmM)`,   `E = −μ(GmM)²/(2ℏ²)`.

* `hasDerivAt_radialWave`, `deriv2_radialWave` — the first and second derivatives of `U = r e^{−r/a}`.
* `groundStateEnergy_eq_neg_hbar_sq_div` — the ground-state energy is `E = −ℏ²/(2μa²)`, tying the
  eigenvalue to the Bohr radius.
* `entropicNewtonGroundState_solves` — `U = r e^{−r/a}` with `a = ℏ²/(μGmM)` and
  `E = −μ(GmM)²/(2ℏ²)` solves the `l = 0` entropic-Newton radial equation (eq. 19), so the entropic
  gravitational potential supports a discrete hydrogen-like bound state.

Honest scope: this is the `l = 0` ground-state solution of the reduced radial equation; the full
`n, l` Bessel/Laguerre spectrum and the smooth Fourier-regularized potential of the paper are not
formalized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState

/-- **The `l = 0` reduced radial wavefunction** `U(r) = r · e^{−r/a}` (gravitational `1s`). -/
def radialWave (a r : ℝ) : ℝ := r * Real.exp (-r / a)

/-- **The gravitational Bohr radius** `a = ℏ²/(μGmM)`. -/
def bohrRadius (μ G m M ℏ : ℝ) : ℝ := ℏ ^ 2 / (μ * G * m * M)

/-- **The gravitational ground-state energy** `E = −μ(GmM)²/(2ℏ²)`. -/
def groundStateEnergy (μ G m M ℏ : ℝ) : ℝ := -(μ * (G * m * M) ^ 2) / (2 * ℏ ^ 2)

/-- The first derivative `U'(r) = e^{−r/a}(1 − r/a)`. -/
theorem hasDerivAt_radialWave (a r : ℝ) :
    HasDerivAt (radialWave a) (Real.exp (-r / a) * (1 - r / a)) r := by
  have h1 : HasDerivAt (fun x : ℝ => -x / a) (-1 / a) r := ((hasDerivAt_id r).neg).div_const a
  have hexp : HasDerivAt (fun x => Real.exp (-x / a)) (Real.exp (-r / a) * (-1 / a)) r := h1.exp
  exact ((hasDerivAt_id r).mul hexp).congr_deriv (by simp only [id_eq]; ring)

/-- The derivative of `U'(r) = e^{−r/a}(1 − r/a)` is `e^{−r/a}(r/a² − 2/a)`. -/
theorem hasDerivAt_radialWaveDeriv (a r : ℝ) :
    HasDerivAt (fun x => Real.exp (-x / a) * (1 - x / a))
      (Real.exp (-r / a) * (r / a ^ 2 - 2 / a)) r := by
  have h1 : HasDerivAt (fun x : ℝ => -x / a) (-1 / a) r := ((hasDerivAt_id r).neg).div_const a
  have hexp : HasDerivAt (fun x => Real.exp (-x / a)) (Real.exp (-r / a) * (-1 / a)) r := h1.exp
  have h2 : HasDerivAt (fun x : ℝ => (1 : ℝ) - x / a) (-1 / a) r :=
    ((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).div_const a)).congr_deriv (by ring)
  exact (hexp.mul h2).congr_deriv (by ring)

/-- **The second derivative** `U''(r) = e^{−r/a}(r/a² − 2/a)`. -/
theorem deriv2_radialWave (a r : ℝ) :
    deriv (deriv (radialWave a)) r = Real.exp (-r / a) * (r / a ^ 2 - 2 / a) := by
  have hd : deriv (radialWave a) = fun x => Real.exp (-x / a) * (1 - x / a) := by
    funext x; exact (hasDerivAt_radialWave a x).deriv
  rw [hd]
  exact (hasDerivAt_radialWaveDeriv a r).deriv

/-- **The ground-state energy is `E = −ℏ²/(2μa²)`** — the eigenvalue expressed through the
gravitational Bohr radius `a = ℏ²/(μGmM)`. -/
@[zil_level physical_theorem]
theorem groundStateEnergy_eq_neg_hbar_sq_div (μ G m M ℏ : ℝ)
    (hμ : μ ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0) :
    groundStateEnergy μ G m M ℏ = -ℏ ^ 2 / (2 * μ * bohrRadius μ G m M ℏ ^ 2) := by
  have hGmM : G * m * M ≠ 0 := mul_ne_zero (mul_ne_zero hG hm) hM
  unfold groundStateEnergy bohrRadius
  field_simp

/-- **The entropic-Newton gravitational hydrogen ground state.**  The reduced radial wavefunction
`U(r) = r · e^{−r/a}` with gravitational Bohr radius `a = ℏ²/(μGmM)` and energy
`E = −μ(GmM)²/(2ℏ²)` solves the `l = 0` entropic-Newton radial Schrödinger equation (Plastino–Rocca
eq. 19)

`U'' + (2μ/ℏ²)(E + GmM/r) U = 0`,

so the entropic gravitational potential `−GmM/r` supports a discrete hydrogen-like bound state. -/
@[zil_level physical_theorem]
theorem entropicNewtonGroundState_solves (μ G m M ℏ r : ℝ)
    (hμ : μ ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0) (hr : r ≠ 0) :
    deriv (deriv (radialWave (bohrRadius μ G m M ℏ))) r
      + (2 * μ / ℏ ^ 2) * (groundStateEnergy μ G m M ℏ + (G * m * M) / r)
          * radialWave (bohrRadius μ G m M ℏ) r = 0 := by
  have hGmM : G * m * M ≠ 0 := mul_ne_zero (mul_ne_zero hG hm) hM
  set a := bohrRadius μ G m M ℏ with ha_def
  rw [deriv2_radialWave a r]
  simp only [radialWave]
  have hfactor :
      Real.exp (-r / a) * (r / a ^ 2 - 2 / a)
          + 2 * μ / ℏ ^ 2 * (groundStateEnergy μ G m M ℏ + G * m * M / r) * (r * Real.exp (-r / a))
        = Real.exp (-r / a)
            * ((r / a ^ 2 - 2 / a)
                + 2 * μ / ℏ ^ 2 * (groundStateEnergy μ G m M ℏ + G * m * M / r) * r) := by
    ring
  rw [hfactor, mul_eq_zero]
  right
  rw [ha_def]
  unfold groundStateEnergy bohrRadius
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState

zil attach groundStateEnergy_eq_neg_hbar_sq_div where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-entropic-newton-gravitational-ground-state-energy-equals-minus-h-bar-squared-over-two-mu-a-squared-with-a-the-gravitational-bohr-radius-h-bar-squared-over-mu-g-m-m"

zil attach entropicNewtonGroundState_solves where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.deriv2_radialWave",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-reduced-radial-wavefunction-u-equals-r-times-exp-minus-r-over-a-with-gravitational-bohr-radius-a-equals-h-bar-squared-over-mu-g-m-m-and-energy-minus-mu-g-m-m-squared-over-two-h-bar-squared-solves-the-l-zero-entropic-newton-coulomb-radial-schrodinger-equation-so-the-entropic-gravitational-potential-supports-a-discrete-hydrogen-like-bound-state"

zil_file_contract physlib.entropicNewtonHydrogenBoundState where
  promises "The entropic-Newton gravitational hydrogen-like bound state of Plastino-Rocca. Because the entropic gravitational potential is minus G m M over r, the reduced radial Schrodinger equation at zero angular momentum is the Coulomb hydrogen form U double prime plus two mu over h bar squared times E plus G m M over r times U equals zero, with G m M as the Coulomb charge product. The l zero ground state is the gravitational analogue of hydrogen one s: U equals r times exp minus r over a, with gravitational Bohr radius a equals h bar squared over mu G m M and energy minus mu G m M squared over two h bar squared. The ground-state energy equals minus h bar squared over two mu a squared, tying the eigenvalue to the Bohr radius, and this wavefunction with these values solves the l zero entropic-Newton radial equation, so the entropic gravitational potential supports a discrete hydrogen-like bound state. This is the l zero ground state of the reduced radial equation; the full n l Bessel Laguerre spectrum and the smooth Fourier-regularized potential of the paper are not formalized here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.radialWave",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.bohrRadius",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.groundStateEnergy"
  ]
  forbids_substitutes [
    "reading the l zero ground-state solution as the full n l Bessel Laguerre bound-state spectrum or the paper's smooth Fourier-regularized potential"
  ]
  witnessed_by [
    groundStateEnergy_eq_neg_hbar_sq_div,
    entropicNewtonGroundState_solves
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.entropicNewtonHydrogenBoundState
