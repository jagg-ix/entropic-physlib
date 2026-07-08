/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.MatsubaraSpinor
public import Physlib.QFT.PathIntegral.Lorentzian

/-!
# Recovering the complex Feynman–Kac path integral from the Euclidean Dunkl process

Closes the loop on the Wigner–Dunkl arc: `Dunkl.EuclideanProcess` (Junker §5) gave the *real*
Euclidean weight of the Dunkl process (the Bessel Feynman–Kac weight `e^{−∫V}`), and
`Dunkl.MatsubaraSpinor` identified it with the Matsubara/thermal weight `e^{−βE}`. Here we recover
the **complex** Feynman–Kac path integral already on this branch — the Lorentzian path-integral kernel
`lorentzianKernel S_R S_I ℏ = exp(i·S_R/ℏ − S_I/ℏ)` of `Physlib.QFT.PathIntegral.Lorentzian` (the
`e^{iS/ℏ}` complex-action weight; the foundation of reference tree's `LorentzianPathIntegralBridge` /
`FeynmanKacBridge`).

The bridge is the **modulus**: the real Euclidean/Matsubara weight of the Dunkl process is exactly the
modulus of the complex Feynman–Kac kernel, and the full complex kernel factors as an oscillatory phase
times that Euclidean weight (Nagao–Nielsen `e^{iS/ℏ} = e^{iS_R/ℏ}·e^{−S_I/ℏ}`).

* **§A — the Euclidean weight is the modulus of the complex kernel** (`dunkl_euclidean_eq_complexFK_norm`):
  `matsubaraBoltzmannWeight β E = ‖lorentzianKernel S_R (βEℏ) ℏ‖`. The Dunkl Bessel/Matsubara damping
  `e^{−βE}` is recovered as `‖e^{iS_R/ℏ − S_I/ℏ}‖` with imaginary action `S_I = βEℏ`.
* **§B — the complex kernel is phase × Dunkl Euclidean weight** (`dunkl_complexFK_factorizes`): the full
  complex Feynman–Kac kernel is the reversible oscillatory phase `e^{iS_R/ℏ}` times the (real) Dunkl
  Euclidean weight — the Lorentzian path integral whose Wick rotation is the Dunkl process.
* **§C — reversibility** (`dunkl_complexFK_reversible`): at `S_I = 0` the complex kernel is a pure
  unit-modulus phase, matching the free Dunkl process (weight `1`).
* **§D — the spinor field's complex path integral** (`spinor_complexFK_norm`): the Dirac spinor's
  fermionic thermal weight (the negative-energy Dirac-sea factor `e^{+βℏω/2} > 1`) is the modulus of the
  complex Feynman–Kac kernel of the absorbing (antiperiodic) sector.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexFeynmanKac

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-! ## §A — the Dunkl Euclidean weight is the modulus of the complex Feynman–Kac kernel -/

/-- **[Recovery] The Dunkl/Matsubara Euclidean weight is the modulus of the complex Feynman–Kac kernel.**
`matsubaraBoltzmannWeight β E = ‖lorentzianKernel S_R (βEℏ) ℏ‖`: the real Bessel/Matsubara damping
`e^{−βE}` of the Euclidean Dunkl process (`Dunkl.EuclideanProcess`, `Dunkl.MatsubaraSpinor`) is
exactly the modulus of the complex path-integral kernel `exp(i·S_R/ℏ − S_I/ℏ)` with imaginary action
`S_I = βEℏ`. This recovers the complex Feynman–Kac path integral already on this branch from the (real)
Euclidean Dunkl process. -/
theorem dunkl_euclidean_eq_complexFK_norm (S_R E β ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    matsubaraBoltzmannWeight β E = ‖lorentzianKernel S_R (β * E * ℏ) ℏ‖ := by
  rw [lorentzianKernel_norm_is_damping]; unfold matsubaraBoltzmannWeight
  congr 1; field_simp

/-- The same recovery in the constant-potential Feynman–Kac form (`feynman_kac_weight`): the reference tree
real FK weight is the modulus of the complex (Lorentzian) FK kernel. -/
theorem fk_weight_eq_complexFK_norm (S_R E β ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    feynman_kac_weight (fun _ : Unit => E) β () = ‖lorentzianKernel S_R (β * E * ℏ) ℏ‖ := by
  rw [Dunkl.MatsubaraSpinor.fk_weight_eq_matsubara, dunkl_euclidean_eq_complexFK_norm S_R E β ℏ hℏ]

/-! ## §B — the complex kernel = oscillatory phase × Dunkl Euclidean weight -/

/-- **[Recovery] The complex Feynman–Kac kernel factors as the reversible phase times the Dunkl Euclidean
weight.** `lorentzianKernel S_R (βEℏ) ℏ = e^{iS_R/ℏ} · (matsubaraBoltzmannWeight β E)` — the Nagao–Nielsen
split `e^{iS/ℏ} = e^{iS_R/ℏ}·e^{−S_I/ℏ}` with the entropic/Euclidean factor being precisely the real Dunkl
process weight. The complex path integral is the oscillatory phase with the Dunkl Euclidean process. -/
theorem dunkl_complexFK_factorizes (S_R E β ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    lorentzianKernel S_R (β * E * ℏ) ℏ
      = Complex.exp ((S_R / ℏ : ℂ) * Complex.I) * (matsubaraBoltzmannWeight β E : ℂ) := by
  rw [lorentzianKernel_factorizes]; congr 2; unfold matsubaraBoltzmannWeight
  congr 1; field_simp

/-! ## §C — reversibility: `S_I = 0` is the free (unitary) limit -/

/-- **[Recovery] At reversibility (`S_I = 0`) the complex Feynman–Kac kernel is a pure unit-modulus
phase** — matching the free Dunkl process, whose Euclidean weight is `1` (`dunkl_fk_free_weight`,
`matsubara_free_limit`). The imaginary action `S_I` is the entropic/Euclidean damping that turns the
unitary complex path integral into the dissipative Dunkl process. -/
theorem dunkl_complexFK_reversible (S_R ℏ : ℝ) :
    ‖lorentzianKernel S_R 0 ℏ‖ = 1 := by
  rw [lorentzianKernel_norm_is_damping]; simp

/-- **The reversible limit agrees with the free Dunkl/Matsubara weight**: both are `1`. -/
theorem dunkl_complexFK_reversible_eq_free (S_R ℏ E : ℝ) :
    ‖lorentzianKernel S_R 0 ℏ‖ = matsubaraBoltzmannWeight 0 E := by
  rw [dunkl_complexFK_reversible, Dunkl.MatsubaraSpinor.matsubara_free_limit]

/-! ## §D — the Dirac spinor field's complex path integral -/

/-- **[Recovery] The Dirac spinor's fermionic thermal weight is the modulus of the complex Feynman–Kac
kernel of the absorbing sector.** With the negative-energy Dirac-sea ground `fermionicEnergyReal ℏ ω 0 =
−ℏω/2`, the imaginary action `S_I = β·(−ℏω/2)·ℏ < 0`, so the modulus `e^{+βℏω/2} > 1` — the spinor's
antiparticle/Dirac-sea contribution, encoded in the absorbing (antiperiodic) Bessel sector of the Dunkl
process, recovered from the complex path integral. -/
theorem spinor_complexFK_norm (S_R ℏ ω β : ℝ) (hℏ : ℏ ≠ 0) :
    matsubaraBoltzmannWeight β (fermionicEnergyReal ℏ ω 0)
      = ‖lorentzianKernel S_R (β * fermionicEnergyReal ℏ ω 0 * ℏ) ℏ‖ :=
  dunkl_euclidean_eq_complexFK_norm S_R _ β ℏ hℏ

end Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexFeynmanKac

end
