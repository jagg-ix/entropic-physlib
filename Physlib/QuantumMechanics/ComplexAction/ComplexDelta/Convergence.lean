/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential

/-!
# The complex-`q` delta function converges in a Minkowski timelike cone (complex-action §2.5)

Nagao–Nielsen's Complex Action Theory extends the delta function to complex `q`
(*Formulation of Complex Action Theory*, Prog. Theor. Phys. **126**(6), §2.5,
p. 1027–1028). The regularised delta `δ_c^ε(q) = √(1/4πε) · e^{−q²/4ε}` (Eq. 2.28)
converges precisely on the domain where (Eq. 2.29)

 `L(q) ≡ (Re q)² − (Im q)² > 0`.

`L` is the **Minkowski quadratic form** of signature `(+, −)` on `ℂ ≅ ℝ¹'¹` — `Re q`
the "time" coordinate, `Im q` the "space" coordinate. `L(q) > 0` is exactly the
**timelike** cone (Fig. 2 of the paper). This file formalizes that structure:

* `lorentzianForm_eq_re_sq` — `L(q) = Re(q²)`: the Lorentzian form is the real part of
 `q²` (so it controls the Gaussian's decay).
* `gaussianMagnitude` — `‖e^{−c·q²}‖ = e^{−c·L(q)}` (`c = 1/4ε`): the magnitude of the
 complex-action Gaussian is governed by `L`.
* `gaussian_lt_one_iff` — for `c > 0`, the Gaussian is **suppressed** (`‖·‖ < 1`) iff
 `L(q) > 0`: convergence is exactly the timelike condition (Eq. 2.29).
* `lorentzian_pos_iff_timelike` — `L(q) > 0 ↔ |Im q| < |Re q|`: the timelike double
 cone around the real axis.

## The Wick-rotation bridge to causality

* `lorentzianForm_mul_I` — `L(i·q) = −L(q)`: **multiplication by the imaginary unit
 flips timelike ↔ spacelike.** This is the same `i` that rotates the real action into
 the imaginary action in complex-action (`exp(iS/ℏ) = exp(iS_R/ℏ)·exp(−S_I/ℏ)`) and real time
 into Euclidean time. It is the formal link between the complex-action convergence cone here and
 the upper-half-plane analyticity of the damped-response causality
 (`ComplexAction.ComplexOscillator.DampedOscillatorCausality`): both are convergence/analyticity domains
 selected by a sign condition, exchanged by the Wick rotation `q ↦ i·q`.

scope: this formalizes the *convergence domain* and its Lorentzian/Wick
structure (Eqs. 2.28–2.29), not the distributional identity `∫ f·δ_c = f(0)` (Eq. 2.30),
which needs the contour-integral / principal-value machinery the paper develops by hand.

Reference: K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor.
Phys. **126**(6) (2011) 1021–1049, §2.5, Eqs. (2.28)–(2.30), doi:10.1143/PTP.126.1021.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-- **The complex-action Lorentzian form** `L(q) = (Re q)² − (Im q)²` (Nagao–Nielsen Eq. 2.29):
the Minkowski quadratic form on `ℂ ≅ ℝ¹'¹` whose positivity is the delta function's
convergence condition. -/
def lorentzianForm (q : ℂ) : ℝ := q.re ^ 2 - q.im ^ 2

/-- **`L(q) = Re(q²)`.** The Lorentzian form is the real part of `q²`, which is what
controls the decay of the Gaussian `e^{−q²/4ε}`. -/
theorem lorentzianForm_eq_re_sq (q : ℂ) : lorentzianForm q = (q ^ 2).re := by
  simp [lorentzianForm, sq, Complex.mul_re]

/-- **The complex-action Gaussian's magnitude is governed by `L`.** `‖e^{−c·q²}‖ = e^{−c·L(q)}`
(with `c = 1/4ε`). -/
theorem gaussianMagnitude (q : ℂ) (c : ℝ) :
    ‖Complex.exp (-(c : ℂ) * q ^ 2)‖ = Real.exp (-c * lorentzianForm q) := by
  rw [Complex.norm_exp, lorentzianForm_eq_re_sq]
  congr 1
  simp [Complex.mul_re]

/-- **Convergence is the timelike condition** (Nagao–Nielsen Eq. 2.29). For `c > 0`
(`c = 1/4ε`), the regularised Gaussian is suppressed, `‖e^{−c·q²}‖ < 1`, exactly when
`L(q) > 0`. -/
theorem gaussian_lt_one_iff (q : ℂ) {c : ℝ} (hc : 0 < c) :
    ‖Complex.exp (-(c : ℂ) * q ^ 2)‖ < 1 ↔ 0 < lorentzianForm q := by
  rw [gaussianMagnitude, Real.exp_lt_one_iff]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The convergence domain is the timelike double cone** around the real axis:
`L(q) > 0 ↔ |Im q| < |Re q|` (Fig. 2). -/
theorem lorentzian_pos_iff_timelike (q : ℂ) :
    0 < lorentzianForm q ↔ |q.im| < |q.re| := by
  unfold lorentzianForm
  constructor
  · intro h
    have h1 : |q.im| ^ 2 < |q.re| ^ 2 := by rw [sq_abs, sq_abs]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) h1
  · intro h
    have h1 : |q.im| ^ 2 < |q.re| ^ 2 := by
      apply pow_lt_pow_left₀ h (abs_nonneg _); norm_num
    rw [sq_abs, sq_abs] at h1; linarith

/-- **The Wick rotation flips timelike ↔ spacelike**: `L(i·q) = −L(q)`. Multiplying by
the imaginary unit — the same `i` taking the real action to the imaginary action in complex-action
and real time to Euclidean time — exchanges the convergence (timelike) cone with the
divergence (spacelike) cone. The formal bridge to the upper-half-plane causality. -/
theorem lorentzianForm_mul_I (q : ℂ) :
    lorentzianForm (Complex.I * q) = - lorentzianForm q := by
  simp [lorentzianForm]

end Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

end
