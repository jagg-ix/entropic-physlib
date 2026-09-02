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

Honest scope: this formalizes the *convergence domain* and its Lorentzian/Wick
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
lemma lorentzianForm_eq_re_sq (q : ℂ) : lorentzianForm q = (q ^ 2).re := by
  simp [lorentzianForm, sq, Complex.mul_re]

/-- **The complex-action Gaussian's magnitude is governed by `L`.** `‖e^{−c·q²}‖ = e^{−c·L(q)}`
(with `c = 1/4ε`). -/
lemma gaussianMagnitude (q : ℂ) (c : ℝ) :
    ‖Complex.exp (-(c : ℂ) * q ^ 2)‖ = Real.exp (-c * lorentzianForm q) := by
  rw [Complex.norm_exp, lorentzianForm_eq_re_sq]
  congr 1
  simp [Complex.mul_re]

/-- **Convergence is the timelike condition** (Nagao–Nielsen Eq. 2.29). For `c > 0`
(`c = 1/4ε`), the regularised Gaussian is suppressed, `‖e^{−c·q²}‖ < 1`, exactly when
`L(q) > 0`. -/
lemma gaussian_lt_one_iff (q : ℂ) {c : ℝ} (hc : 0 < c) :
    ‖Complex.exp (-(c : ℂ) * q ^ 2)‖ < 1 ↔ 0 < lorentzianForm q := by
  rw [gaussianMagnitude, Real.exp_lt_one_iff]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The convergence domain is the timelike double cone** around the real axis:
`L(q) > 0 ↔ |Im q| < |Re q|` (Fig. 2). -/
lemma lorentzian_pos_iff_timelike (q : ℂ) :
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
lemma lorentzianForm_mul_I (q : ℂ) :
    lorentzianForm (Complex.I * q) = - lorentzianForm q := by
  simp [lorentzianForm]

/-! ## The modified complex conjugate and the `{}`-real / `{}`-imaginary split

Nagao–Nielsen, *Formalism of a harmonic oscillator in the future-included complex action
theory* (Prog. Theor. Exp. Phys. **2019**, 073B01, §2.3, Eqs. (16)–(19)), introduce a
**modified complex conjugate** `*_{[]}` that conjugates a coefficient while keeping the
dynamical variable analytic, and the induced `{}`-real / `{}`-imaginary decomposition
`f = Re_{[]}f + i·Im_{[]}f`.  For a monomial `f = k·φ` (coefficient `k`, kept-analytic factor
`φ`) the modified conjugate is `k̄·φ`.  This is the **abstract kernel of the entropic split**
`S = S_R + i S_I` (the repository convention, `complexActionPathIntegralWeight = exp(iS/ℏ)`):
the `{}`-real part is the reversible (oscillatory) action `S_R`, the `{}`-imaginary part is the
entropic action `S_I` whose sign governs the damping weight `|e^{iS/ℏ}| = e^{−S_I/ℏ}` (the same
`i` as `lorentzianForm_mul_I` above). -/

/-- **The modified complex conjugate** `*_{[]}` (Nagao–Nielsen 2019 Eq. (16)) of a monomial
`k·φ`: conjugate the coefficient `k`, keep the analytic factor `φ`. -/
noncomputable def modConj (k φ : ℂ) : ℂ := (starRingEnd ℂ) k * φ

/-- **The `{}`-real part** `Re_{[]}(k·φ)` (Nagao–Nielsen 2019 Eq. (18)). -/
noncomputable def modRe (k φ : ℂ) : ℂ := (k * φ + modConj k φ) / 2

/-- **The `{}`-imaginary part** `Im_{[]}(k·φ)` (Nagao–Nielsen 2019 Eq. (19)). -/
noncomputable def modIm (k φ : ℂ) : ℂ := (k * φ - modConj k φ) / (2 * Complex.I)

/-- **The `{}`-real part keeps only the real coefficient** `Re_{[]}(k·φ) = (Re k)·φ`. -/
theorem modRe_eq (k φ : ℂ) : modRe k φ = (k.re : ℂ) * φ := by
  unfold modRe modConj
  rw [show k * φ + (starRingEnd ℂ) k * φ = (k + (starRingEnd ℂ) k) * φ by ring,
    Complex.add_conj]
  push_cast; ring

/-- **The `{}`-imaginary part keeps only the imaginary coefficient**
`Im_{[]}(k·φ) = (Im k)·φ` — the entropic action `S_I` is carried by the imaginary part of the
coefficient. -/
theorem modIm_eq (k φ : ℂ) : modIm k φ = (k.im : ℂ) * φ := by
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  unfold modIm modConj
  rw [show k * φ - (starRingEnd ℂ) k * φ = (k - (starRingEnd ℂ) k) * φ by ring,
    Complex.sub_conj, div_eq_iff hI]
  push_cast; ring

/-- **The `{}`-decomposition** `f = Re_{[]}f + i·Im_{[]}f` (Nagao–Nielsen 2019 Eq. (17)): a
complex monomial splits into its reversible and entropic parts. -/
theorem modDecomposition (k φ : ℂ) : k * φ = modRe k φ + Complex.I * modIm k φ := by
  rw [modRe_eq, modIm_eq,
    show (k.re : ℂ) * φ + Complex.I * ((k.im : ℂ) * φ)
      = ((k.re : ℂ) + (k.im : ℂ) * Complex.I) * φ by ring, Complex.re_add_im]

/-- **`{}`-real ⟺ real coefficient** — for a nonzero analytic factor, `k·φ` is fixed by the
modified conjugate (`f*_{[]} = f`) exactly when its coefficient is real: the reversible,
non-dissipative case with vanishing entropic action. -/
theorem modConj_bracketReal_iff (k φ : ℂ) (hφ : φ ≠ 0) :
    modConj k φ = k * φ ↔ k.im = 0 := by
  unfold modConj
  constructor
  · intro h
    exact Complex.conj_eq_iff_im.mp (mul_right_cancel₀ hφ h)
  · intro h
    rw [Complex.conj_eq_iff_im.mpr h]

/-- **`{}`-imaginary ⟺ imaginary coefficient** — `f*_{[]} = −f` exactly when the coefficient
is purely imaginary: the pure-damping case where the action is entirely entropic. -/
theorem modConj_bracketImag_iff (k φ : ℂ) (hφ : φ ≠ 0) :
    modConj k φ = -(k * φ) ↔ k.re = 0 := by
  unfold modConj
  rw [show -(k * φ) = (-k) * φ by ring]
  constructor
  · intro h
    have hc : (starRingEnd ℂ) k = -k := mul_right_cancel₀ hφ h
    have hre := congrArg Complex.re hc
    simp only [Complex.conj_re, Complex.neg_re] at hre
    linarith
  · intro h
    have hc : (starRingEnd ℂ) k = -k := by
      apply Complex.ext
      · simp [Complex.conj_re, Complex.neg_re, h]
      · simp [Complex.conj_im, Complex.neg_im]
    rw [hc]

/-- **The entropic part vanishes iff the coefficient is `{}`-real** —
`Im_{[]}(k·φ) = 0 ↔ Im k = 0 ∨ φ = 0`: no imaginary action means no entropic damping, the
reversible limit that recovers the real-action theory. -/
theorem modIm_eq_zero_iff (k φ : ℂ) : modIm k φ = 0 ↔ k.im = 0 ∨ φ = 0 := by
  rw [modIm_eq, mul_eq_zero, Complex.ofReal_eq_zero]

/-! ## The complex-coefficient Gaussian: the `{}`-split governs the convergence cone

For a **complex** coefficient `c` — the delta with complex argument `δ_c^ε(aq)` has effective
coefficient `c = a²/4ε` (Nagao–Nielsen 2019 Eq. (11)) — the magnitude of the Gaussian
`e^{−c·q²}` is set by the real part of the exponent, which the `{}`-split of §2.3 resolves:
the `{}`-real coefficient `Re c` multiplies the Lorentzian form `L(q)` (the reversible
convergence), and the `{}`-imaginary coefficient `Im c` multiplies `Im(q²)` (the entropic
tilt).  This ties the modified-conjugate split back to the delta-function convergence cone of
§2.2. -/

/-- **The complex-coefficient Gaussian magnitude** — generalizes `gaussianMagnitude` to a
complex coefficient `c`: `‖e^{−c·q²}‖ = e^{−Re(c·q²)}`. -/
theorem gaussianMagnitude_complexCoeff (q c : ℂ) :
    ‖Complex.exp (-c * q ^ 2)‖ = Real.exp (-(c * q ^ 2).re) := by
  rw [Complex.norm_exp]
  congr 1
  rw [neg_mul, Complex.neg_re]

/-- **Convergence for a complex coefficient** — the Gaussian is suppressed (`‖·‖ < 1`) exactly
when the real part of the exponent coefficient is positive, `Re(c·q²) > 0` (generalizes
`gaussian_lt_one_iff`, no positivity hypothesis on `c`). -/
theorem gaussian_complexCoeff_lt_one_iff (q c : ℂ) :
    ‖Complex.exp (-c * q ^ 2)‖ < 1 ↔ 0 < (c * q ^ 2).re := by
  rw [gaussianMagnitude_complexCoeff, Real.exp_lt_one_iff]
  constructor <;> intro h <;> linarith

/-- **The `{}`-split of the convergence exponent** — `Re(c·q²) = (Re c)·L(q) − (Im c)·Im(q²)`:
the `{}`-real coefficient governs the Lorentzian convergence, the `{}`-imaginary (entropic)
coefficient governs the tilt off the real axis. -/
theorem gaussianExponent_bracketSplit (q c : ℂ) :
    (c * q ^ 2).re = c.re * lorentzianForm q - c.im * (q ^ 2).im := by
  rw [Complex.mul_re, lorentzianForm_eq_re_sq]

/-- **On the real axis only the `{}`-real coefficient damps** — for real `q = x`,
`‖e^{−c·x²}‖ = e^{−(Re c)·x²}`: the entropic (`{}`-imaginary) part of the coefficient does not
suppress the magnitude on the physical contour (`Im(x²) = 0`), only tilts the phase.  It is
exactly off the real axis that the entropic coefficient enters the convergence. -/
theorem gaussianMagnitude_realAxis (x : ℝ) (c : ℂ) :
    ‖Complex.exp (-c * (x : ℂ) ^ 2)‖ = Real.exp (-c.re * x ^ 2) := by
  rw [gaussianMagnitude_complexCoeff]
  congr 1
  rw [gaussianExponent_bracketSplit]
  have h1 : lorentzianForm (x : ℂ) = x ^ 2 := by simp [lorentzianForm]
  have h2 : (((x : ℂ)) ^ 2).im = 0 := by
    rw [show ((x : ℂ)) ^ 2 = ((x ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  rw [h1, h2]; ring

/-! ## The complex rescaling of the delta (Nagao–Nielsen 2019 Eqs. (14)–(15))

Under a complex rescaling `q ↦ a·q` the regularised delta `δ_c^ε(q) = √(1/4πε)·e^{−q²/4ε}`
obeys (Nagao–Nielsen 2019 Eq. (14))

  `δ_c^ε(a·q) = (sign(Re a)/a)·δ_c^{ε/a²}(q)`,

with `sign(Re a)` (Eq. (15)) the branch selector `+1`/`−1` for `Re a ≷ 0`.  Two algebraic
facts carry this: the **exponents match** — both Gaussians decay as `e^{−a²q²/4ε}` — and the
prefactor ratio `√(a²/ε)/√(1/ε) = √(a²)` picks the branch `√(a²) = sign(Re a)·a`.  This is the
pointwise / continuum device NN use to keep analyticity when scaling the complex coordinate. -/

/-- **The Gaussian exponent** `−q²/4ε` of the regularised delta, with `ε` extended to a
complex parameter (Nagao–Nielsen 2019 Eq. (11)). -/
noncomputable def gaussExp (ε q : ℂ) : ℂ := -q ^ 2 / (4 * ε)

/-- **The exponents match under complex rescaling** — `gaussExp ε (a·q) = gaussExp (ε/a²) q`:
scaling the argument by `a` is absorbed by scaling the width `ε ↦ ε/a²`, the exponent core of
Eq. (14). -/
theorem gaussExp_scaling (a q ε : ℂ) (ha : a ≠ 0) (hε : ε ≠ 0) :
    gaussExp ε (a * q) = gaussExp (ε / a ^ 2) q := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  unfold gaussExp
  field_simp

/-- **The sign of the real part** `sign(Re a)` (Nagao–Nielsen 2019 Eq. (15)): the branch
selector, `+1` when `Re a > 0` and `−1` otherwise. -/
noncomputable def signRe (a : ℂ) : ℝ := if 0 < a.re then 1 else -1

/-- **`sign(Re a)² = 1`** — the branch selector squares to one. -/
theorem signRe_sq (a : ℂ) : signRe a * signRe a = 1 := by
  unfold signRe; split_ifs <;> norm_num

/-- **`sign(Re a)·a` is a square root of `a²`** — `(sign(Re a)·a)² = a²`: the prefactor branch
of Eq. (14), `√(a²) = sign(Re a)·a`, encoded without the `cpow` branch cut. -/
theorem signRe_mul_self_sq (a : ℂ) : ((signRe a : ℂ) * a) ^ 2 = a ^ 2 := by
  have h : ((signRe a : ℂ)) ^ 2 = 1 := by
    rw [sq, ← Complex.ofReal_mul, signRe_sq, Complex.ofReal_one]
  rw [mul_pow, h, one_mul]

end Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

end
