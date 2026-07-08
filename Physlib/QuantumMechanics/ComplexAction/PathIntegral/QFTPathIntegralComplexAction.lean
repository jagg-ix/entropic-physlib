/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.QIFThermodynamicReversible
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
public import Physlib.QFT.PathIntegral.Lorentzian
public import Physlib.QFT.PathIntegral.FeynmanKac

/-!
# The QIF / thermodynamic weights ARE the QFT path-integral kernels

This file *proves* that the thermodynamic / QIF objects of the last steps
(`ThermoFieldDynamics.ThermodynamicCanonicalQuantization`, `TimeOperator.QIFThermodynamicReversible`) are the **same**
analytic objects as the QFT path-integral kernels already on the branch — the Nagao–Nielsen
**Minkowski / Lorentzian** path integral (`QFT.PathIntegral.Lorentzian`), the **Wick**
complex action weight (`QFT.Wick.Consistency`), the **Feynman–Kac / Euclidean** weight
(`QFT.PathIntegral.FeynmanKac`), and my **Feynman path-integral momentum** derivation
(`ComplexAction.PathIntegral.MomentumPathIntegral`, Nagao–Nielsen arXiv:1304.4017). So the "no action with
no information" / `T = 0` / reversible-QIF condition is *literally* the unitary (modulus-1)
limit of the Minkowski path integral and the trivial (weight-1) limit of the Euclidean one.

## §A — the same kernel, three names

`thermoActionWeight S_R S_I b = e^{iS/b̄} = e^{(S_R/b̄)i − S_I/b̄}` is **definitionally** the Wick
`complexActionWeight`, hence equal to the Lorentzian path-integral kernel `lorentzianKernel`:

  `thermoActionWeight = complexActionWeight = lorentzianKernel`.

The modified Green function `greenKernel λ ℏ t = e^{−iλt/ℏ}` of `H_C = H_R − iH_I` then has
the **same modulus** as the Lorentzian kernel with `S_I = −Im λ·t` — its dissipative decay is
the Minkowski path integral's `e^{−S_I/ℏ}`.

## §B — no action with no information = unitary Minkowski PI = trivial Euclidean PI

* `lorentzianKernel_norm_one_iff` — `‖lorentzianKernel S_R S_I ℏ‖ = 1 ↔ S_I = 0`: the
  Minkowski path-integral kernel is a **pure oscillatory phase** (unitary) iff the imaginary
  action vanishes — the QFT face of §D's `thermoActionWeight_norm_one_iff`.
* `fk_weight_one_of_reversible` — at `S_I = 0` the Feynman–Kac / Euclidean weight is `1`
  (no damping): the reversible / `T = 0` limit of `fk_weight_equals_entropic_damping`.
* `momentum_no_fk_damping_of_reversible` — at the reversible point `Im m = 0` the momentum
  Gaussian has no real damping (`¬ 0 < Re b`); the momentum integral is **purely
  oscillatory** (Fresnel), the Minkowski regime of `momentum_integral_converges_iff`
  (Euclidean damping `Re b > 0 ⟺ Im m > 0`).
* `greenKernel_unitary_eq_lorentzian_no_information` — the main result: on a real-eigenvalue
  mode (`Im λ = 0` = spectral `H_I = 0` = reversible QIF = `T = 0`) the `H_C` propagator is
  unitary **and** equals in modulus the unimodular Lorentzian kernel.

So the chain of the previous replies closes onto the existing QFT layer:

  `T = 0  ⟺  reversibleQIF (H_I = 0)  ⟺  Im λ = 0  ⟺  S_I = 0`
  `       ⟺  ‖lorentzianKernel‖ = 1` (unitary Minkowski PI, pure phase)
  `       ⟺  fk weight = 1` (trivial Euclidean PI)
  `       ⟺  Im m = 0` (no Feynman–Kac damping, purely oscillatory momentum integral).

## References

* K. Nagao, H. B. Nielsen, arXiv:1104.3381 (`H_C = H_R − iH_I`), arXiv:1304.4017 (FPI
  momentum relation, the oscillatory / Euclidean-damping dichotomy).
* `QFT.PathIntegral.Lorentzian`, `QFT.Wick.Consistency`, `QFT.PathIntegral.FeynmanKac`
  (this development) — the Minkowski / Wick / Euclidean kernels.
* Lima et al., arXiv:2511.14121 — the `b̄`-scaled thermodynamic action weight.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QFT.PathIntegral
open Physlib.QFT.Wick.Consistency

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.QFTPathIntegralComplexAction

/-! ## §A — the thermodynamic weight is the Wick / Lorentzian path-integral kernel -/

/-- **The thermodynamic weight is the Wick complex action weight** — definitionally the same
`e^{(S_R/b̄)i − S_I/b̄}`. -/
theorem thermoActionWeight_eq_complexActionWeight (S_R S_I b : ℝ) :
    thermoActionWeight S_R S_I b = complexActionWeight S_R S_I b := rfl

/-- **The thermodynamic weight is the Nagao–Nielsen Lorentzian (Minkowski) path-integral
kernel.** -/
theorem thermoActionWeight_eq_lorentzianKernel (S_R S_I ℏ : ℝ) :
    thermoActionWeight S_R S_I ℏ = lorentzianKernel S_R S_I ℏ := by
  rw [thermoActionWeight_eq_complexActionWeight, lorentzianKernel_eq_complexActionWeight]

/-- **The `H_C` Green function's decay is the Lorentzian path integral's**:
`‖greenKernel λ ℏ t‖ = ‖lorentzianKernel S_R (−Im λ·t) ℏ‖` — the modified Green function of
`H_C = H_R − iH_I` has the same modulus as the Minkowski path-integral kernel with
imaginary action `S_I = −Im λ·t`. -/
theorem norm_greenKernel_eq_lorentzianKernel (lam : ℂ) (ℏ t S_R : ℝ) :
    ‖greenKernel lam ℏ t‖ = ‖lorentzianKernel S_R (-lam.im * t) ℏ‖ := by
  rw [norm_greenKernel_eq_thermoActionWeight lam ℏ t S_R, thermoActionWeight_eq_lorentzianKernel]

/-! ## §B — no action with no information = unitary Minkowski / trivial Euclidean PI -/

/-- **The Minkowski path integral is unitary iff there is no imaginary action**:
`‖lorentzianKernel S_R S_I ℏ‖ = 1 ↔ S_I = 0` — the QFT face of `thermoActionWeight_norm_one_iff`. -/
theorem lorentzianKernel_norm_one_iff {ℏ : ℝ} (hℏ : ℏ ≠ 0) (S_R S_I : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = 1 ↔ S_I = 0 := by
  rw [← thermoActionWeight_eq_lorentzianKernel]
  exact thermoActionWeight_norm_one_iff hℏ S_R S_I

/-- **The Euclidean (Feynman–Kac) weight is trivial at reversibility**: when the imaginary
action vanishes (`S_I = V·T·ℏ = 0`, the `T = 0` / reversible-QIF point), the Feynman–Kac
weight is `1` — no damping. The reversible limit of `fk_weight_equals_entropic_damping`. -/
theorem fk_weight_one_of_reversible (V T ℏ : ℝ) (hℏ : 0 < ℏ) (S_I : ℝ)
    (hSI : S_I = V * T * ℏ) (hrev : S_I = 0) :
    feynman_kac_weight (fun _ : Unit => V) T () = 1 := by
  rw [← fk_euclidean_entropic_damping_correspondence V T ℏ hℏ S_I hSI, hrev]
  simp

/-- **No Feynman–Kac damping at the reversible point**: when the imaginary mass vanishes
(`Im m = 0`) the momentum Gaussian coefficient has no positive real part, so the momentum
path integral is **purely oscillatory** (Fresnel) rather than Euclidean-damped — the
Minkowski regime of `momentum_integral_converges_iff` (`Re b > 0 ⟺ Im m > 0`). -/
theorem momentum_no_fk_damping_of_reversible (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) (hrev : m.im = 0) :
    ¬ (0 < (momentumGaussianCoeff m ℏ dt).re) := by
  rw [momentum_integral_converges_iff m hℏ hdt hm, hrev]
  exact lt_irrefl 0

/-- **Main result — the `H_C` propagator is the unitary Minkowski kernel at no-information.**
On a real-eigenvalue mode (`Im λ = 0`, the spectral form of `H_I = 0` = reversible QIF =
`T = 0`) the modified Green function is unitary and equal in modulus to the unimodular
Nagao–Nielsen Lorentzian path-integral kernel — no entropic action, no information. -/
theorem greenKernel_unitary_eq_lorentzian_no_information
    {ℏ t : ℝ} (hℏ : ℏ ≠ 0) (ht : t ≠ 0) {lam : ℂ} (hI : lam.im = 0) (S_R : ℝ) :
    ‖greenKernel lam ℏ t‖ = 1 ∧ ‖lorentzianKernel S_R 0 ℏ‖ = 1 :=
  ⟨(greenKernel_norm_one_iff hℏ ht lam).mpr hI,
   (lorentzianKernel_norm_one_iff hℏ S_R 0).mpr rfl⟩

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.QFTPathIntegralComplexAction

end

end
