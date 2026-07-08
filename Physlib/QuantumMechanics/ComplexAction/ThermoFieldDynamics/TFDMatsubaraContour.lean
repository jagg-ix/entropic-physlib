/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The TFD self-energy momentum & Matsubara contour, via the Nagao–Nielsen contour

Supplies the *analytic layer* of the Fujimoto–Morikawa–Sasaki self-energy evaluations (`ThermoFieldDynamics.TFDImaginaryPart`,
`ThermoFieldDynamics.TFDSelfEnergyIdentities`) — the two genuinely-analytic operations left aside there — by **using the
Nagao–Nielsen contour Gaussian** (`ComplexDelta.ContourGaussian`) and the residue at the Matsubara poles.

* **the momentum (loop) Gaussian** — after Schwinger parametrization a propagator's loop integral reduces to
  the Gaussian `∫ e^{−cz²} dz`, which the NN contour evaluates to `√(π/c)` along *any* ray `|θ| < π/4`
  (`gaussianContourIntegral`). The **Wick rotation** from the real-time (Minkowski, `θ=0`) contour to the
  imaginary-time (Euclidean) one stays inside this wedge, and the integral is unchanged
  (`gaussianContourIntegral_indep`) — this contour independence *is* the statement that real-time TFD
  reproduces the imaginary-time (ITF) result, the central claim of the paper.
* **the Matsubara frequency sum** — the conversion `(1/β)∑ₙ f(2πn/β) = ∮ …` (Eq. 2) is a residue sum over the
  Bose factor `1/(e^{βz}−1)`, whose poles are the Matsubara frequencies `zₙ = 2πin/β` with residue `1/β`. The
  pole condition `e^{βzₙ}=1` and the simple-pole derivative `d/dz(e^{βz}−1)|_{zₙ} = β` are formalized.

* **§A — the momentum Gaussian (Wick rotation)** (`momentumGaussian_realAxis`, `momentum_wick_invariance`).
  The loop Gaussian `= √(π/c)` on the real-time contour, equal to its Euclidean rotation.
* **§B — the Matsubara contour/residue** (`matsubaraFreq`, `bose_pole`, `bose_residue`). The Bose poles `zₙ`,
  `e^{βzₙ}=1`, and the residue `1/β`.

## References

* Y. Fujimoto, M. Morikawa, M. Sasaki, Phys. Rev. D 33 (1986) (Eqs. 1–3, the Matsubara sum Eq. 2).
* Repo dependencies: `ComplexDelta.ContourGaussian.gaussianContourIntegral`/`_indep` (the NN rotated Gaussian and
  its contour independence — the Wick wedge `|θ|<π/4`); `ThermoFieldDynamics.TFDImaginaryPart` (the self-energy this underpins).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour

open Real Complex
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian

/-! ## §A — the momentum (loop) Gaussian, via the NN contour (Wick rotation) -/

/-- **The real-time momentum Gaussian** `∫ e^{−ck²} dk = √(π/c)` — the Schwinger-parametrized loop integral on
the real-time (Minkowski, `θ=0`) contour, from the Nagao–Nielsen `gaussianContourIntegral`. -/
theorem momentumGaussian_realAxis (c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, contourIntegrand (gaussH c) 0 s = (Real.sqrt (π / c) : ℂ) :=
  gaussianContourIntegral hc (by rw [abs_zero]; positivity)

/-- **[Wick rotation: real-time TFD = imaginary-time ITF] The loop Gaussian is contour-independent.** The
real-time (`θ=0`) and the Euclidean-rotated (`θ`) momentum Gaussians agree for any `|θ| < π/4`
(`gaussianContourIntegral_indep`) — the Wick rotation stays in the convergence wedge, so TFD reproduces the
imaginary-time-formalism result. -/
theorem momentum_wick_invariance (c θ : ℝ) (hc : 0 < c) (hθ : |θ| < π / 4) :
    ∫ s : ℝ, contourIntegrand (gaussH c) 0 s = ∫ s : ℝ, contourIntegrand (gaussH c) θ s :=
  gaussianContourIntegral_indep hc (by rw [abs_zero]; positivity) hθ

/-! ## §B — the Matsubara frequency sum: poles and residues -/

/-- **The Matsubara frequency** `zₙ = 2πin/β` — the pole of the Bose factor `1/(e^{βz}−1)` that the frequency
sum `(1/β)∑ₙ f(2πn/β)` is converted to a contour integral around. -/
noncomputable def matsubaraFreq (β : ℝ) (n : ℤ) : ℂ := ((2 * π * n / β : ℝ) : ℂ) * Complex.I

/-- **[Matsubara pole] `e^{βzₙ} = 1`** — the Bose factor `1/(e^{βz}−1)` has a pole at every Matsubara
frequency `zₙ = 2πin/β`, since `βzₙ = 2πin`. -/
theorem bose_pole (β : ℝ) (n : ℤ) (hβ : β ≠ 0) :
    Complex.exp ((β : ℂ) * matsubaraFreq β n) = 1 := by
  unfold matsubaraFreq
  have h1 : β * (2 * π * (n : ℝ) / β) = 2 * π * (n : ℝ) := by field_simp
  have hcast : (β : ℂ) * (((2 * π * (n : ℝ) / β : ℝ) : ℂ) * Complex.I)
      = (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    rw [← mul_assoc, ← Complex.ofReal_mul, h1]; push_cast; ring
  rw [hcast, Complex.exp_int_mul_two_pi_mul_I]

/-- **[Matsubara residue `= 1/β`] The simple-pole derivative `d/dz(e^{βz}−1)|_{zₙ} = β`.** At the Matsubara
pole `zₙ` the denominator `e^{βz}−1` has derivative `β·e^{βzₙ} = β`, so the residue of `1/(e^{βz}−1)` is `1/β`
— the weight the frequency sum picks up at each pole (`(1/β)∑ₙ = ∮ …` of Eq. 2). -/
theorem bose_residue (β : ℝ) (n : ℤ) (hβ : β ≠ 0) :
    HasDerivAt (fun z => Complex.exp ((β : ℂ) * z) - 1) (β : ℂ) (matsubaraFreq β n) := by
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp ((β : ℂ) * z))
      (Complex.exp ((β : ℂ) * matsubaraFreq β n) * (β : ℂ)) (matsubaraFreq β n) := by
    exact ((Complex.hasDerivAt_exp ((β : ℂ) * matsubaraFreq β n)).comp (matsubaraFreq β n)
      ((hasDerivAt_id _).const_mul (β : ℂ))).congr_deriv (by ring)
  have hval : Complex.exp ((β : ℂ) * matsubaraFreq β n) * (β : ℂ) = (β : ℂ) := by
    rw [bose_pole β n hβ, one_mul]
  rw [hval] at hexp
  exact hexp.sub_const 1

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour

end
