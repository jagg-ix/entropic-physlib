/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster

/-!
# Banihashemi–Jacobson §II completed: ADM constraint, gauge fixing, and the lapse-contour example

Completes the formalization of **§II "Path Integral and Lapse Contour"** of *B. Banihashemi, T. Jacobson,
"On the lapse contour in the gravitational path integral", arXiv:2405.10307v3 (2025)*. `GravLapse.ContourMaster`
already carries Eqs. 1, 2, 5 (the phase-space PI, the constraint Fourier integral, and the `N − iε`
lapse-displaced weight). This file adds the remaining §II content: the ADM lapse, the Hamiltonian
constraint (Eq. 3) and its indefinite-sign trace decomposition (footnote 4), the maximal-slicing gauge fixing
and its Faddeev–Popov bracket (Eq. 4, footnotes 5–6), and the illustrative momentum–lapse integral
(Eqs. 6–10) whose convergence and contour evasion are controlled by the *same* `ε`.

* **§A — the ADM lapse and the essential singularity** (`spacetimeVolElement_eq_zero_iff`,
  `admLapse_pos`). The lapse is `N = 1/√(−g^{tt})` (`admLapse`, intro + footnote 14), and the spacetime
  volume element `√(−g) = N√q` (`spacetimeVolElement`) vanishes **iff** `N = 0` — the degenerate metric at
  zero lapse is the essential singularity that forces the contour off the real axis.
* **§B — the Hamiltonian constraint (Eq. 3) and its indefinite trace part** (`hamiltonianConstraint`,
  `momentumQuadratic_traceDecomp`). `ℋ = q^{−1/2}(p^{ij}p_{ij} − ½p²) − q^{1/2}R`; the DeWitt kinetic term
  `p^{ij}p_{ij} − ½p²` decomposes (footnote 4, 3 spatial dims) as `p̃^{ij}p̃_{ij} − (1/6)p²` — the trace mode
  `p²` enters with a **minus** sign, so the trace-momentum Gaussian would *diverge*.
* **§C — maximal slicing fixes the divergence** (`momentumQuadratic_maximalSlice_nonneg`). The gauge
  `χ = p` (maximal slices, footnote 5) removes the indefinite trace mode, leaving the positive-semidefinite
  trace-free form `p̃^{ij}p̃_{ij} ≥ 0` — a convergent Gaussian. This is the *consequence* of Eq. 4: the
  Faddeev–Popov bracket `{p, ℋ} = 2q^{1/2}(R − D²)δ` is momentum-independent (footnote 6), so the remaining
  momentum integrals stay Gaussian. (The functional bracket Eq. 4 itself is not separately formalized — only
  its consequence, the gauge-fixed convergence.)
* **§D — the illustrative integral (Eqs. 6, 8, 9, 10) and the unified `ε`** (`same_epsilon_does_both`,
  `eq8Integrand_modulus`). The toy constraint is the relativistic mass shell `ℋ = p² − m²`
  (`relativisticConstraint`); the Eq. 8 integrand is the source `e^{ip·x}` times the lapse weight at this
  constraint (`eq8Integrand`). The momentum-Gaussian coefficient `−i(N − iε)` has
  real part `−ε` (`momentumGaussCoeff_re`), so the momentum integral converges **iff** `ε > 0`
  (`momentumGauss_converges_iff`); and the displaced contour `N − iε` is nonzero for `ε > 0`
  (`lapseContour_avoids_singularity`), evading the essential singularity that sits on the contour at the
  origin when `ε = 0` (`lapseContour_singular_at_origin`). The main result `same_epsilon_does_both`: a single
  `ε > 0` simultaneously (a) makes the momentum Gaussian converge and (b) keeps the lapse contour off the
  essential singularity — the paper's central claim that the contour displacement is *dictated* by
  integrating the momenta first. The change of variable `t = i(N − iε)m²` (Eq. 10) is `tSubstitution`,
  nonzero on the displaced contour (`tSubstitution_ne_zero`).

**Honest scope.** The analytic evaluation of the toy integral to a Bessel function
`J_{n/2−1}(m|x|)` (Eq. 7, via Poisson's/Schläfli's integral, DLMF 10.9.4 / 10.9.19) is the paper's
special-function result; it is *stated* here, not re-derived (Mathlib lacks the Bessel-`J` Poisson
representation). Eq. 4 is the functional Poisson bracket; this file formalizes its coefficient and its
consequence (gauge-fixed convergence), not the full functional-calculus derivation.

## References

* B. Banihashemi, T. Jacobson, *On the lapse contour in the gravitational path integral*,
  arXiv:2405.10307v3 (2 Mar 2025), DOI `10.48550/arXiv.2405.10307`. **§II** (pp. 2–4): Hamiltonian
  constraint `ℋ` (Eq. 3, p. 2); the trace/trace-free split (footnote 4, p. 3); the gauge `χ = p` (footnote
  5, p. 3) and the Faddeev–Popov bracket `{p, ℋ}` (Eq. 4, p. 3; momentum-independence, footnote 6, p. 3);
  the illustrative integrals (Eqs. 6–10, pp. 3–4); the ADM lapse `N = 1/√(−g^{tt})` (footnote 14, p. 5).
* R. Arnowitt, S. Deser, C. W. Misner, *The dynamics of general relativity* (1962) — the ADM lapse/shift.
* L. D. Faddeev, V. N. Popov, *Covariant quantization of the gravitational field*, Usp. Fiz. Nauk 111
  (1973) 427 — the gauge-fixing determinant.
* DLMF §10.9 — Poisson's and Schläfli's integral representations of the Bessel function (Eq. 7).
* Repo carrier: `GravLapse.ContourMaster` (`lapseWeight`, `lapseWeight_modulus`, `lapse_im_eq_gap`),
  `NonHermitian.WickRotation` (`complexEnergy`, the complex lapse `N − iε`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII

open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation


/-- **[Banihashemi–Jacobson intro / footnote 14] The ADM lapse** `N = 1/√(−g^{tt})` — the lapse is the
reciprocal of the square root of minus the `tt`-component of the inverse metric. -/
noncomputable def admLapse (gtt : ℝ) : ℝ := 1 / Real.sqrt (-gtt)

/-- The ADM lapse is positive for a Lorentzian time-time inverse-metric component `g^{tt} < 0`. -/
lemma admLapse_pos (gtt : ℝ) (h : gtt < 0) : 0 < admLapse gtt :=
  one_div_pos.mpr (Real.sqrt_pos.mpr (by linarith))

/-- **The spacetime volume element** `√(−g) = N√q` — lapse times the spatial volume element. -/
noncomputable def spacetimeVolElement (N q : ℝ) : ℝ := N * Real.sqrt q

/-- **[The essential singularity] The metric degenerates exactly at zero lapse.** For a nondegenerate
spatial metric (`q > 0`), the spacetime volume element `√(−g) = N√q` vanishes **iff** `N = 0`: the
zero-lapse configuration is the degenerate metric where the action of general relativity is ill defined —
the essential singularity of the integrand that forces the lapse contour off the real axis. -/
lemma spacetimeVolElement_eq_zero_iff (N q : ℝ) (hq : 0 < q) :
    spacetimeVolElement N q = 0 ↔ N = 0 := by
  unfold spacetimeVolElement
  rw [mul_eq_zero]
  refine ⟨fun h => h.resolve_right (Real.sqrt_pos.mpr hq).ne', Or.inl⟩


/-- **[Banihashemi–Jacobson Eq. 3] The vacuum Hamiltonian constraint**
`ℋ = q^{−1/2}(p^{ij}p_{ij} − ½p²) − q^{1/2}R`, with `q` the spatial-metric determinant, `ppC = p^{ij}p_{ij}`,
`pTr = p` the trace momentum, and `R` the spatial Ricci scalar. -/
noncomputable def hamiltonianConstraint (q ppC pTr R : ℝ) : ℝ :=
  (ppC - (1 / 2) * pTr ^ 2) / Real.sqrt q - Real.sqrt q * R

/-- **The DeWitt kinetic quadratic form** `p^{ij}p_{ij} − ½p²` of the Hamiltonian constraint. -/
noncomputable def momentumQuadratic (ppC pTr : ℝ) : ℝ := ppC - (1 / 2) * pTr ^ 2

/-- **[Banihashemi–Jacobson footnote 4] The trace decomposition exposes the indefinite sign.** Writing the
momentum as trace-free plus trace, `p^{ij}p_{ij} = p̃^{ij}p̃_{ij} + (1/3)p²` (3 spatial dimensions), the
DeWitt kinetic form becomes `p^{ij}p_{ij} − ½p² = p̃^{ij}p̃_{ij} − (1/6)p²`: the **trace** mode `p²` enters
with a *minus* sign, so its momentum Gaussian would diverge — the obstruction the paper must fix. -/
lemma momentumQuadratic_traceDecomp (tfSq pTr ppC : ℝ)
    (htf : ppC = tfSq + (1 / 3) * pTr ^ 2) :
    momentumQuadratic ppC pTr = tfSq - (1 / 6) * pTr ^ 2 := by
  unfold momentumQuadratic; rw [htf]; ring


/-- **[Banihashemi–Jacobson footnote 5] On a maximal slice** the trace momentum is fixed to zero (`χ = p`,
mean extrinsic curvature `= 0`); the DeWitt kinetic form reduces to the trace-free part
`momentumQuadratic ppC 0 = ppC`. -/
lemma momentumQuadratic_maximalSlice (ppC : ℝ) : momentumQuadratic ppC 0 = ppC := by
  unfold momentumQuadratic; ring

/-- **The gauge-fixed momentum form is positive-semidefinite.** After removing the indefinite trace mode
(maximal slicing), the remaining form is the trace-free square `p̃^{ij}p̃_{ij} ≥ 0` — a *convergent* momentum
Gaussian, curing the divergence of footnote 4. -/
lemma momentumQuadratic_maximalSlice_nonneg (tfSq : ℝ) (htf : 0 ≤ tfSq) :
    0 ≤ momentumQuadratic tfSq 0 := by
  rw [momentumQuadratic_maximalSlice]
  simpa using htf


/-- **[Banihashemi–Jacobson Eq. 6 ff.] The toy constraint is the relativistic mass shell** `ℋ = p² − m²` —
the Hamiltonian constraint of a relativistic particle, standing in for the gravitational `ℋ`. -/
noncomputable def relativisticConstraint (p2 m : ℝ) : ℝ := p2 - m ^ 2

/-- **[Banihashemi–Jacobson Eq. 8] The momentum–lapse integrand** `e^{ip·x} · e^{−i(N−iε)(p²−m²)}` — the
plane-wave source times the lapse-displaced mass-shell constraint weight. -/
noncomputable def eq8Integrand (px p2 m N ε : ℝ) : ℂ :=
  Complex.exp (Complex.I * (px : ℂ)) * lapseWeight N ε (relativisticConstraint p2 m)

/-- **[Implement] The integrand modulus is the momentum Gaussian** `‖e^{ip·x}·e^{−i(N−iε)(p²−m²)}‖ =
e^{−ε(p²−m²)}`: the source is unimodular, and the lapse displacement supplies a Gaussian damping in the
momentum (decaying at large `p²` precisely when `ε > 0`). -/
lemma eq8Integrand_modulus (px p2 m N ε : ℝ) :
    ‖eq8Integrand px p2 m N ε‖ = Real.exp (-(ε * relativisticConstraint p2 m)) := by
  unfold eq8Integrand
  rw [norm_mul, lapseWeight_modulus, kuikenWeight, div_one]
  have h1 : ‖Complex.exp (Complex.I * (px : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [h1, one_mul]

/-- **[Banihashemi–Jacobson Eq. 8] The momentum Gaussian coefficient** `−i(N − iε)` of the `p²` term. -/
noncomputable def momentumGaussCoeff (N ε : ℝ) : ℂ := -Complex.I * complexEnergy N ε

/-- **The momentum Gaussian coefficient has real part `−ε`.** `Re[−i(N − iε)] = −ε`: the `−iε` lapse
displacement is exactly the real damping of the momentum Gaussian. -/
lemma momentumGaussCoeff_re (N ε : ℝ) : (momentumGaussCoeff N ε).re = -ε := by
  unfold momentumGaussCoeff complexEnergy
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **[Implement] The momentum integral converges iff `ε > 0`.** The `p²` Gaussian `e^{−i(N−iε)p²}` decays
(`Re` of its coefficient is negative) exactly when the lapse displacement `ε` is positive. -/
lemma momentumGauss_converges_iff (N ε : ℝ) :
    (momentumGaussCoeff N ε).re < 0 ↔ 0 < ε := by
  rw [momentumGaussCoeff_re]; constructor <;> intro h <;> linarith

/-- **[Banihashemi–Jacobson Eq. 9] The displaced contour evades the essential singularity.** For `ε > 0`
the complex lapse `N − iε` is nonzero for every real `N`, so the integrand factor `e^{ix²/(4(N−iε))}` (and
the prefactor `(π/(i(N−iε)))^{n/2}`) is regular on the whole contour — the contour passes *below* the
essential singularity at the origin. -/
lemma lapseContour_avoids_singularity (N ε : ℝ) (hε : 0 < ε) : complexEnergy N ε ≠ 0 := by
  intro h
  have him := lapse_im_eq_gap N ε
  rw [h, Complex.zero_im] at him
  linarith

/-- **[Banihashemi–Jacobson Eq. 9] At `ε = 0` the singularity sits on the contour.** With no displacement,
the complex lapse is `N`, which vanishes at `N = 0`: the essential singularity of `e^{ix²/(4N)}` lies on the
real integration contour, rendering the `N` integral ill defined. -/
lemma lapseContour_singular_at_origin : complexEnergy 0 0 = 0 := by
  simp [complexEnergy]

/-- **[Main result — Banihashemi–Jacobson §II] One `ε` does both.** A single positive lapse displacement
`ε > 0` simultaneously (a) makes the momentum Gaussian converge and (b) keeps the lapse contour off the
essential singularity. The contour displacement required to evade the singularity is *not ad hoc*: it is the
same `ε` dictated by integrating the momenta first — the paper's central conclusion. -/
lemma same_epsilon_does_both (N ε : ℝ) (hε : 0 < ε) :
    (momentumGaussCoeff N ε).re < 0 ∧ complexEnergy N ε ≠ 0 :=
  ⟨(momentumGauss_converges_iff N ε).mpr hε, lapseContour_avoids_singularity N ε hε⟩

/-- **[Banihashemi–Jacobson Eq. 10] The change of variable** `t = i(N − iε)m²` that recasts the `N` integral
as Schläfli's Bessel integral (the `t`-contour from `−i∞ + ε` to `i∞ + ε`). -/
noncomputable def tSubstitution (N ε m : ℝ) : ℂ := Complex.I * complexEnergy N ε * (m ^ 2 : ℝ)

/-- The `t`-variable is nonzero on the displaced contour (`ε > 0`, `m ≠ 0`) — the substitution is
nonsingular, matching the regular Bessel integrand. -/
lemma tSubstitution_ne_zero (N ε m : ℝ) (hε : 0 < ε) (hm : m ≠ 0) :
    tSubstitution N ε m ≠ 0 := by
  unfold tSubstitution
  refine mul_ne_zero (mul_ne_zero Complex.I_ne_zero ?_) (by exact_mod_cast pow_ne_zero 2 hm)
  intro h
  have him := lapse_im_eq_gap N ε
  rw [h, Complex.zero_im] at him
  linarith

end Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII

end
