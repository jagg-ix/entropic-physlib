/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
meta import Zil

/-!
# The heat semigroup for the Jacobi–Dunkl operator (Chouchene–Gallardo–Mili)

Formalizes the structural core of *F. Chouchene, L. Gallardo, M. Mili, "The Heat Semigroup for the
Jacobi–Dunkl Operator and the Related Markov Processes", Potential Anal. 25 (2006) 103–119*.

The **Jacobi–Dunkl operator** is the differential-difference operator on `ℝ`

  `Λ_{α,β} f(x) = f'(x) + [(2α+1)coth x + (2β+1)tanh x]·(f(x) − f(−x))/2`  (Eq. 1),

the hyperbolic analogue of the Dunkl operator (`A(x) = |x|^{2α+1}`), here with the Jacobi weight
`A(x) = |x|^{2α+1}(sinh x/x)^{2α+1}(cosh x)^{2β+1}`. This module carries the algebraic and structural
results — the reflection-difference/parity structure, the maximum principle, and the
Gaussian-multiplier heat-semigroup law — on the level of the operator and its Fourier symbol, taking
the analytic realization (the spectral measure, the heat kernel, the `Lᵖ` spaces) as cited.

* `reflectionDiff` — the odd part `(f(x)−f(−x))/2`; vanishes on even functions, is the identity on
  odd functions.
* `jacobiDunklSquare_even_eq_jacobiOp` — **Proposition 3.6**: on even functions the square `Λ²`
  reduces to the Jacobi operator `Δ_{α,β} = f'' + w·f'` (this is why the absolute value `|X|` of a
  Jacobi–Dunkl process is the Jacobi diffusion).
* `jacobiDunklSquare_nonpos_at_max` — **Proposition 3.1**, the maximum principle: at a global maximum
  (with the second-derivative-test data `f'(x₀)=0`, `f''(x₀)≤0`) and a decreasing coefficient
  (`w'(x₀)≤0`), the square operator is nonpositive, `Λ²f(x₀) ≤ 0` — the dispersivity underlying the
  positive contraction semigroup.
* `heatMultiplier`, `heatMultiplier_add`, `heatMultiplier_le_one` — **Theorem 3.1(ii)** and the Feller
  contraction: the Fourier symbol `e^{−tλ²}` of the heat semigroup `H_t` (`F(H_t f)(λ)=e^{−tλ²}F(f)`,
  Eq. 26/33) is a one-parameter multiplicative semigroup (`e^{−(t+s)λ²}=e^{−tλ²}e^{−sλ²}` — the
  Chapman–Kolmogorov relation of the associated Markov process) bounded by `1` for `t ≥ 0`. This is
  the *same* Gaussian-multiplier structure as the classical heat semigroup and the modular flow.
* `jacobiDunklCoeff_odd` — the coefficient `(2α+1)coth x + (2β+1)tanh x` is odd, so `Λ` reverses
  parity (the defining Dunkl-type structure).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup

/-- The **reflection difference** (odd part) `(f(x) − f(−x))/2` appearing in the Jacobi–Dunkl
operator's difference term. -/
noncomputable def reflectionDiff (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x - f (-x)) / 2

/-- The **Jacobi–Dunkl operator** `Λf = f' + w·(reflection difference)` with coefficient
`w = A'/A = (2α+1)coth x + (2β+1)tanh x`. -/
noncomputable def jacobiDunkl (w f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x + w x * reflectionDiff f x

/-- The **Jacobi operator** `Δf = f'' + w·f'` — the second-order (even) part of `Λ²` (Eq. 9). -/
noncomputable def jacobiOp (w f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x + w x * deriv f x

/-- The **square of the Jacobi–Dunkl operator** `Λ²f = Δf + w'·(reflection difference)` (Eq. 18),
with `dw` the derivative of the coefficient `w = A'/A`. -/
noncomputable def jacobiDunklSquare (w dw f : ℝ → ℝ) (x : ℝ) : ℝ :=
  jacobiOp w f x + dw x * reflectionDiff f x

/-- **The reflection difference vanishes on even functions.** -/
theorem reflectionDiff_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    reflectionDiff f x = 0 := by
  unfold reflectionDiff; rw [hf]; ring

/-- **The reflection difference is the identity on odd functions.** -/
theorem reflectionDiff_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (x : ℝ) :
    reflectionDiff f x = f x := by
  unfold reflectionDiff; rw [hf]; ring

/-- **On even functions the Jacobi–Dunkl operator is the derivative** `Λf = f'`. -/
theorem jacobiDunkl_even_eq_deriv (w : ℝ → ℝ) {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    jacobiDunkl w f x = deriv f x := by
  unfold jacobiDunkl; rw [reflectionDiff_even hf, mul_zero, add_zero]

/-- **[Proposition 3.6] On even functions the square `Λ²` reduces to the Jacobi operator `Δ`.** The
reflection difference vanishes on even `f`, so `Λ²f = Δf = f'' + w·f'`. This is the structural fact
that the absolute value `|X|` of a Jacobi–Dunkl process is the Jacobi diffusion with generator
`Δ_{α,β}`. -/
theorem jacobiDunklSquare_even_eq_jacobiOp (w dw : ℝ → ℝ) {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
    (x : ℝ) : jacobiDunklSquare w dw f x = jacobiOp w f x := by
  unfold jacobiDunklSquare; rw [reflectionDiff_even hf, mul_zero, add_zero]

/-- **[Proposition 3.1, the maximum principle / dispersivity]** At a global maximum `x₀` of `f`
(second-derivative-test data `f'(x₀)=0`, `f''(x₀)≤0`) with a decreasing coefficient
(`dw x₀ = (A'/A)'(x₀) ≤ 0`), the square operator is nonpositive: `Λ²f(x₀) ≤ 0`. The Jacobi part is
`≤ 0` by the second-derivative test, and the difference term `w'·(f(x₀)−f(−x₀))/2 ≤ 0` because the
coefficient is decreasing and `f(x₀)` is the global maximum. This dispersivity is the Hille–Yosida
input making `Λ²` the generator of a positive contraction semigroup. -/
theorem jacobiDunklSquare_nonpos_at_max {w dw f : ℝ → ℝ} {x₀ : ℝ}
    (hf' : deriv f x₀ = 0) (hf'' : deriv (deriv f) x₀ ≤ 0) (hdw : dw x₀ ≤ 0)
    (hmax : ∀ x, f x ≤ f x₀) :
    jacobiDunklSquare w dw f x₀ ≤ 0 := by
  have hjac : jacobiOp w f x₀ ≤ 0 := by
    unfold jacobiOp; rw [hf', mul_zero, add_zero]; exact hf''
  have hrefl : 0 ≤ reflectionDiff f x₀ := by
    unfold reflectionDiff
    have hle := hmax (-x₀)
    linarith
  have hterm : dw x₀ * reflectionDiff f x₀ ≤ 0 := by
    nlinarith [mul_nonneg (neg_nonneg.2 hdw) hrefl]
  unfold jacobiDunklSquare
  linarith

/-- The **Jacobi–Dunkl heat multiplier** `e^{−tλ²}` — the Fourier symbol of the heat semigroup,
`F(H_t f)(λ) = e^{−tλ²}·F(f)(λ)` (Eq. 26/33). -/
noncomputable def heatMultiplier (t lam : ℝ) : ℝ := Real.exp (-(t * lam ^ 2))

/-- The heat multiplier at time `0` is the identity `1`. -/
theorem heatMultiplier_zero (lam : ℝ) : heatMultiplier 0 lam = 1 := by
  unfold heatMultiplier; simp

/-- **[Theorem 3.1(ii), the semigroup / Chapman–Kolmogorov relation]** `e^{−(t+s)λ²} = e^{−tλ²}·e^{−sλ²}`.
The heat semigroup satisfies `H_{t+s} = H_t H_s` because its Fourier symbol is the one-parameter
multiplicative semigroup `t ↦ e^{−tλ²}`; this is exactly the Chapman–Kolmogorov equation of the
associated Jacobi–Dunkl Markov process at the level of the generalized Fourier transform. -/
theorem heatMultiplier_add (t s lam : ℝ) :
    heatMultiplier (t + s) lam = heatMultiplier t lam * heatMultiplier s lam := by
  unfold heatMultiplier; rw [← Real.exp_add]; congr 1; ring

/-- The heat multiplier is strictly positive (the heat kernel is strictly positive, Corollary 3.1). -/
theorem heatMultiplier_pos (t lam : ℝ) : 0 < heatMultiplier t lam := Real.exp_pos _

/-- **[Feller contraction, Proposition 3.5]** For `t ≥ 0` the heat multiplier is bounded by `1`: the
heat semigroup is a contraction, `‖H_t f‖_∞ ≤ ‖f‖_∞`. -/
theorem heatMultiplier_le_one {t : ℝ} (ht : 0 ≤ t) (lam : ℝ) : heatMultiplier t lam ≤ 1 := by
  unfold heatMultiplier
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hpos : 0 ≤ t * lam ^ 2 := by positivity
  linarith

/-- **The heat multiplier is the exponential of `t` times the eigenvalue `−λ²`.** The Jacobi–Dunkl
kernel `ψ_λ` is an eigenfunction of `Λ²` with eigenvalue `−λ²` (`F(Λ²f)(λ) = −λ²F(f)(λ)`, Lemma 3.1),
so the heat semigroup acts on it by `e^{t·(−λ²)}`. -/
theorem heatMultiplier_eq_exp_eigenvalue (t lam : ℝ) :
    heatMultiplier t lam = Real.exp (t * (-(lam ^ 2))) := by
  unfold heatMultiplier; congr 1; ring

/-- The Jacobi–Dunkl coefficient `w = A'/A = (2α+1)coth x + (2β+1)tanh x` (with `coth = cosh/sinh`). -/
noncomputable def jacobiDunklCoeff (α β x : ℝ) : ℝ :=
  (2 * α + 1) * (Real.cosh x / Real.sinh x) + (2 * β + 1) * Real.tanh x

/-- **The Jacobi–Dunkl coefficient is odd** `w(−x) = −w(x)` — `coth` and `tanh` are odd. Hence `Λ`
maps even functions to odd and odd to even: it **reverses parity**, the defining Dunkl-type
structure. -/
theorem jacobiDunklCoeff_odd (α β x : ℝ) :
    jacobiDunklCoeff α β (-x) = -jacobiDunklCoeff α β x := by
  unfold jacobiDunklCoeff
  rw [Real.cosh_neg, Real.sinh_neg, Real.tanh_neg, div_neg]
  ring

end Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklSquare_even_eq_jacobiOp where
  formalizes @ "claim:on-even-functions-the-square-of-the-jacobi-dunkl-operator-reduces-to-the-jacobi-operator-so-the-absolute-value-of-a-jacobi-dunkl-process-is-the-jacobi-diffusion",
  supported_by @ "paper:chouchene-gallardo-mili-jacobi-dunkl-heat-semigroup-markov"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklSquare_nonpos_at_max where
  formalizes @ "claim:at-a-global-maximum-with-a-decreasing-coefficient-the-square-jacobi-dunkl-operator-is-nonpositive-the-maximum-principle-dispersivity",
  supported_by @ "paper:chouchene-gallardo-mili-jacobi-dunkl-heat-semigroup-markov",
  caveat @ "claim:the-second-derivative-test-data-first-derivative-zero-and-second-derivative-nonpositive-at-the-maximum-are-taken-as-hypotheses"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.heatMultiplier_add where
  formalizes @ "claim:the-jacobi-dunkl-heat-fourier-symbol-is-a-one-parameter-multiplicative-semigroup-the-chapman-kolmogorov-relation-of-the-markov-process",
  supported_by @ "paper:chouchene-gallardo-mili-jacobi-dunkl-heat-semigroup-markov"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.heatMultiplier_le_one where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:for-nonnegative-time-the-jacobi-dunkl-heat-fourier-symbol-is-bounded-by-one-the-feller-contraction"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklCoeff_odd where
  formalizes @ "claim:the-jacobi-dunkl-coefficient-coth-plus-tanh-is-odd-so-the-operator-reverses-parity"

zil_file_contract physlib.jacobiDunklHeatSemigroup where
  promises "The structural core of the Jacobi-Dunkl heat semigroup: the reflection-difference (odd part) vanishes on even functions and is the identity on odd functions, so the square Lambda^2 reduces to the Jacobi operator Delta on even functions (Prop 3.6, why the modulus of a Jacobi-Dunkl process is the Jacobi diffusion); at a global maximum with decreasing coefficient the square operator is nonpositive (Prop 3.1 maximum principle / dispersivity); the heat Fourier symbol e^{-t lambda^2} is a one-parameter multiplicative semigroup (Thm 3.1(ii), the Chapman-Kolmogorov relation) bounded by 1 for nonnegative time (Feller contraction), equal to the exponential of t times the eigenvalue -lambda^2; and the coefficient coth+tanh is odd so the operator reverses parity."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.reflectionDiff",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklSquare",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.heatMultiplier"]
  forbids_substitutes ["the spectral measure, the strictly positive heat kernel, and the Lp realization of the semigroup, which require the generalized Fourier / Paley-Wiener infrastructure and are taken as cited",
    "the Markov process construction, only the Chapman-Kolmogorov relation at the Fourier-symbol level is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.reflectionDiff_even,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.reflectionDiff_odd,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklSquare_even_eq_jacobiOp,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklSquare_nonpos_at_max,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.heatMultiplier_add,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.heatMultiplier_le_one,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.heatMultiplier_eq_exp_eigenvalue,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.JacobiDunklHeatSemigroup.jacobiDunklCoeff_odd]

/- ZIL-END -/
