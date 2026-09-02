/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The `p`-Laplacian, its standing-wave origin, and the `Lᵖ`-critical exponent

Formalizes the tractable structural core of S. Deng, Q. Wu, *Normalized solutions for `p`-Laplacian equations
with potential* (arXiv:2310.10510). The paper studies normalized solutions (fixed `Lᵖ` mass) of the
`p`-Laplacian equation `−Δ_p u − V|u|^{p−2}u + λ|u|^{p−2}u = |u|^{q−2}u` on `ℝ^N` (Eq. 1.1), where
`Δ_p u = div(|∇u|^{p−2}∇u)`. Its existence results (mountain-pass, local minimizer, Pohozaev) are deep
variational analysis; the pieces that formalize cleanly and reuse physlib's vector calculus are:

* **§A — the `p`-Laplacian operator and its `p = 2` reduction.** `pLaplacian p u = div(‖∇u‖^{p−2} • ∇u)`,
  built on physlib's `Space.div`/`Space.grad`, with `pLaplacian_two_eq_laplacian`: `Δ₂ u = Δ u` (the paper's
  remark that at `p = 2`, Eq. 1.1 is the Schrödinger equation Eq. 1.2). At `p = 2` the weight `‖∇u‖⁰ = 1`, so
  the `p`-Laplacian is exactly `div(∇u) = Δ`.
* **§B — the standing-wave origin (§1).** Eq. 1.2 comes from the nonlinear Schrödinger equation by the
  standing-wave ansatz `ψ(t,x) = e^{−iλt}u(x)` with `u` real. `standingWave_normSq`: `‖ψ‖² = u²` (the
  probability density is time-independent — the mass constraint `∫u² = a²` is conserved), and
  `standingWave_time_deriv`: `i∂ₜψ = λψ` (the frequency `λ` is the eigenvalue that becomes the Lagrange
  multiplier of the normalized problem).
* **§C — the `Lᵖ`-critical exponent (Gagliardo–Nirenberg balance).** `lpCriticalExponent p N = p + p²/N`
  (the paper's `L²`-critical `2 + 4/N` at `p = 2`), characterized as the exponent where the Gagliardo–Nirenberg
  gradient power `N(q−p)/p` equals `p` — the scaling balance that separates the `Lᵖ`-subcritical (functional
  bounded below on the constraint) from the supercritical regime.

Reuses (GREP-first) `Space.laplacian` (`= div ∘ grad`), `Space.div`, `Space.grad`, `Complex.exp` /
`Complex.norm_exp_ofReal_mul_I` (as in `MadelungPolarDecomposition`), and Mathlib real-power / complex-exp
calculus.

## References

* S. Deng, Q. Wu, arXiv:2310.10510, Eq. 1.1/1.2/1.3, §1–2. Carriers: `Space.Derivatives.Laplacian`
  (`laplacian = ∇⬝∇`), `Space.Derivatives.Div`/`Grad`, Mathlib `HasDerivAt.cexp`,
  `Complex.norm_exp_ofReal_mul_I`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger.PLaplacianNormalizedSolution

/-! ### §A The `p`-Laplacian operator and its reduction to the Laplacian at `p = 2` -/

/-- **[The `p`-Laplacian] `Δ_p u = div(‖∇u‖^{p−2} ∇u)`** — the quasilinear operator of Eq. 1.1, built from
physlib's gradient and divergence. The weight `‖∇u‖^{p−2}` uses the real power. -/
noncomputable def pLaplacian {d : ℕ} (p : ℝ) (u : Space d → ℝ) : Space d → ℝ :=
  Space.div (fun x => ‖Space.grad u x‖ ^ (p - 2) • Space.grad u x)

/-- **[The `p`-Laplacian is the Laplacian at `p = 2`] `Δ₂ u = Δ u`.** At `p = 2` the weight `‖∇u‖^{2−2} = 1`,
so `pLaplacian 2 u = div(∇u) = Δ u` (physlib's `Space.laplacian`). This is the paper's observation that Eq. 1.1
reduces at `p = 2` to the Schrödinger equation Eq. 1.2. -/
theorem pLaplacian_two_eq_laplacian {d : ℕ} (u : Space d → ℝ) :
    pLaplacian 2 u = Space.laplacian u := by
  simp only [pLaplacian, show (2 : ℝ) - 2 = 0 by norm_num, Real.rpow_zero, one_smul]
  rfl

/-! ### §B The standing-wave origin of the stationary equation (paper §1) -/

/-- **[The Schrödinger standing wave] `ψ(t,x) = e^{−iλt} u(x)`** (with `u` real) — the ansatz whose stationary
profile `u` solves Eq. 1.2. -/
noncomputable def standingWave {d : ℕ} (lam : ℝ) (u : Space d → ℝ) (t : ℝ) (x : Space d) : ℂ :=
  Complex.exp (((-(lam * t) : ℝ) : ℂ) * Complex.I) * (u x : ℂ)

/-- **[The probability density is time-independent] `‖ψ(t,x)‖² = u(x)²`.** The standing wave carries a
stationary density: `|e^{−iλt}| = 1`, so `‖ψ‖² = u²`. Hence the mass `∫‖ψ‖² = ∫u²` is conserved in time and
the normalization constraint `∫u² = a²` (Eq. 1.3) is preserved. -/
theorem standingWave_normSq {d : ℕ} (lam : ℝ) (u : Space d → ℝ) (t : ℝ) (x : Space d) :
    ‖standingWave lam u t x‖ ^ 2 = (u x) ^ 2 := by
  rw [standingWave, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, one_mul,
    Real.norm_eq_abs, sq_abs]

/-- **[The frequency is the eigenvalue] `i ∂ₜψ = λ ψ`.** Differentiating the standing wave in time returns the
frequency `λ` times `ψ`: this is the eigenvalue relation that, on substituting into the nonlinear Schrödinger
equation, produces the `+λu` term of the stationary equation Eq. 1.2 — with `λ` the Lagrange multiplier of the
mass-constrained (normalized) problem. -/
theorem standingWave_time_deriv {d : ℕ} (lam : ℝ) (u : Space d → ℝ) (t : ℝ) (x : Space d) :
    Complex.I * deriv (fun τ => standingWave lam u τ x) t = (lam : ℂ) * standingWave lam u t x := by
  have hg : HasDerivAt (fun τ : ℝ => ((-(lam * τ) : ℝ) : ℂ) * Complex.I)
      (-(lam : ℂ) * Complex.I) t := by
    have hlin : (fun τ : ℝ => ((-(lam * τ) : ℝ) : ℂ) * Complex.I)
        = fun τ : ℝ => (-(lam : ℂ) * Complex.I) * (τ : ℂ) := by
      funext τ; push_cast; ring
    rw [hlin]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(lam : ℂ) * Complex.I)
  have hexp : HasDerivAt (fun τ : ℝ => Complex.exp (((-(lam * τ) : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((-(lam * t) : ℝ) : ℂ) * Complex.I) * (-(lam : ℂ) * Complex.I)) t :=
    hg.cexp
  have hd : HasDerivAt (fun τ => standingWave lam u τ x)
      (Complex.exp (((-(lam * t) : ℝ) : ℂ) * Complex.I) * (-(lam : ℂ) * Complex.I)
        * (u x : ℂ)) t := by
    simpa only [standingWave] using hexp.mul_const ((u x : ℝ) : ℂ)
  rw [hd.deriv, standingWave,
    show Complex.I * (Complex.exp (((-(lam * t) : ℝ) : ℂ) * Complex.I)
          * (-(lam : ℂ) * Complex.I) * (u x : ℂ))
        = -(lam : ℂ) * (Complex.I * Complex.I)
          * (Complex.exp (((-(lam * t) : ℝ) : ℂ) * Complex.I) * (u x : ℂ)) from by ring,
    Complex.I_mul_I]
  ring

/-! ### §C The `Lᵖ`-critical exponent (Gagliardo–Nirenberg scaling balance) -/

/-- **[The `Lᵖ`-critical exponent] `p + p²/N`** — the exponent `q` at which the mass-constrained functional
transitions from bounded-below (`Lᵖ`-subcritical) to unbounded-below (supercritical). -/
def lpCriticalExponent (p N : ℝ) : ℝ := p + p ^ 2 / N

/-- **[`L²`-critical exponent `2 + 4/N`]** — the classical Schrödinger threshold (`p = 2`). -/
theorem lpCriticalExponent_two (N : ℝ) : lpCriticalExponent 2 N = 2 + 4 / N := by
  simp only [lpCriticalExponent]; norm_num

/-- **The Gagliardo–Nirenberg gradient power** `N(q−p)/p` — the exponent of `‖∇u‖ₚ` appearing in
`‖u‖_q^q ≤ C ‖∇u‖ₚ^{N(q−p)/p} ‖u‖ₚ^{…}` after raising the GN inequality to the power `q`. -/
def gnGradientPower (N p q : ℝ) : ℝ := N * (q - p) / p

/-- **[The `Lᵖ`-critical exponent is the Gagliardo–Nirenberg scaling balance] `N(q−p)/p = p ⟺ q = p + p²/N`.**
The critical exponent is exactly where the gradient power of the Gagliardo–Nirenberg bound equals `p`, i.e.
where the nonlinear term scales like the Dirichlet energy `(1/p)‖∇u‖ₚ^p` under the mass-preserving dilation —
so the constrained functional loses its lower bound. -/
theorem gnGradientPower_eq_p_iff (N p q : ℝ) (hN : N ≠ 0) (hp : p ≠ 0) :
    gnGradientPower N p q = p ↔ q = lpCriticalExponent p N := by
  rw [gnGradientPower, lpCriticalExponent, div_eq_iff hp]
  constructor
  · intro h; field_simp; linarith [h]
  · intro h; rw [h]; field_simp; ring

end Physlib.QuantumMechanics.Schrodinger.PLaplacianNormalizedSolution

end
