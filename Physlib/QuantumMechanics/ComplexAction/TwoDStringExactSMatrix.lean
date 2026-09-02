/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
meta import Zil

/-!
# The exact `c = 1` two-dimensional string `S`-matrix (Moore–Plesser–Ramgoolam)

Formalizes the exact/algebraic core of G. Moore, M. R. Plesser, S. Ramgoolam, *Exact S-matrix for
two-dimensional string theory*, Nucl. Phys. B 377 (1992) 143–190 — the **nonperturbative unitarity** of the
`c = 1` reflection amplitude.

The exact euclidean fermion reflection factor continues to the Minkowski reflection amplitude (Eq. 2.15). The
paper's central result:

* **Theory I is unitary**: the continued reflection factor is a **pure phase** — `‖R^I‖ = 1`
  (`norm_reflectionFactorI`). Each factor is unimodular: the Gamma ratio `Γ(½−iy)/Γ(½+iy)` and the rational
  factor `(1+ix)/(1−ix)` are quotients of complex conjugates (`norm_gamma_half_ratio`,
  `norm_one_add_I_div_one_sub_I`), and `μ^{iω}` is a phase.
* **Theory II is not unitary**: `R^II = R^I/(1 + i e^{−π(μ+ω)})` (Eq. 2.10) has modulus
  `‖R^II‖ = (1 + e^{−2π(μ+ω)})^{−1/2} < 1` (`norm_reflectionFactorII`, `reflectionFactorII_norm_lt_one`).

## References

* G. Moore, M. R. Plesser, S. Ramgoolam (1992), Nucl. Phys. B 377, 143–190, Eqs. (2.8)–(2.15). `Mathlib`
  (`Complex.Gamma_conj`, `Complex.norm_cpow_of_ne_zero`).


-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix


/-- **[Principal square root of a unit-modulus number is unimodular]** `‖z^{1/2}‖ = 1` when `‖z‖ = 1`. -/
lemma norm_cpow_half_of_norm_one {z : ℂ} (hz : z ≠ 0) (h : ‖z‖ = 1) :
    ‖z ^ (((1 / 2 : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_of_ne_zero hz, h, Complex.ofReal_im, Complex.ofReal_re]
  simp

/-- **[`(1+ix)/(1−ix)` is a pure phase]** — numerator and denominator are complex conjugates. -/
lemma norm_one_add_I_div_one_sub_I (x : ℝ) :
    ‖(1 + Complex.I * (x : ℂ)) / (1 - Complex.I * (x : ℂ))‖ = 1 := by
  have hne : (1 + Complex.I * (x : ℂ)) ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simp at hre
  have hconj : (1 - Complex.I * (x : ℂ)) = (starRingEnd ℂ) (1 + Complex.I * (x : ℂ)) := by
    simp only [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [norm_div, hconj, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]

/-- **[The Gamma ratio `Γ(½−iy)/Γ(½+iy)` is a pure phase]** — `Γ(½+iy) = conj Γ(½−iy)` by
`Complex.Gamma_conj`. -/
lemma norm_gamma_half_ratio (y : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ))
      / Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ = 1 := by
  have harg : (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ))
      = ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) := by
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have hne : Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have hconj : Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))
      = (starRingEnd ℂ) (Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ))) := by
    rw [← Complex.Gamma_conj, harg]
  rw [norm_div, hconj, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]

/-- **[`‖1 + i a‖ = √(1+a²)` for real `a`].** -/
lemma norm_one_add_I_mul_ofReal (a : ℝ) :
    ‖1 + Complex.I * (a : ℂ)‖ = Real.sqrt (1 + a ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring


/-- **The theory-I (`A = 0`) Minkowski reflection factor** (Eq. 2.15, `q > 0`). -/
noncomputable def reflectionFactorI (μ ω : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((μ * Real.log μ : ℝ) : ℂ)) * (μ : ℂ) ^ (Complex.I * (ω : ℂ)) * Complex.I
    * ((1 + Complex.I * ((Real.exp (-Real.pi * (μ + ω)) : ℝ) : ℂ))
        / (1 - Complex.I * ((Real.exp (-Real.pi * (μ + ω)) : ℝ) : ℂ))) ^ (((1 / 2 : ℝ) : ℂ))
    * (Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * ((μ + ω : ℝ) : ℂ))
        / Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * ((μ + ω : ℝ) : ℂ))) ^ (((1 / 2 : ℝ) : ℂ))

/-- **[Theory I is unitary: the reflection factor is a pure phase]** `‖R^I‖ = 1`. The central
nonperturbative-unitarity result of the paper for the `c = 1` `S`-matrix. -/
lemma norm_reflectionFactorI (μ ω : ℝ) (hμ : 0 < μ) : ‖reflectionFactorI μ ω‖ = 1 := by
  have hr1ne : (1 + Complex.I * ((Real.exp (-Real.pi * (μ + ω)) : ℝ) : ℂ))
      / (1 - Complex.I * ((Real.exp (-Real.pi * (μ + ω)) : ℝ) : ℂ)) ≠ 0 := by
    rw [div_ne_zero_iff]
    constructor
    · intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, mul_zero, zero_mul, sub_zero,
        add_zero] at hre
      exact one_ne_zero hre
    · intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, mul_zero, zero_mul, sub_zero] at hre
      exact one_ne_zero hre
  have hg1 : Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * ((μ + ω : ℝ) : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have hg2 : Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * ((μ + ω : ℝ) : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  rw [reflectionFactorI, norm_mul, norm_mul, norm_mul, norm_mul,
    norm_cpow_half_of_norm_one hr1ne (norm_one_add_I_div_one_sub_I _),
    norm_cpow_half_of_norm_one (div_ne_zero hg1 hg2) (norm_gamma_half_ratio _),
    Complex.norm_I, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hμ]
  simp


/-- **The theory-II Minkowski reflection factor** (Eq. 2.10): `R^II = R^I / (1 + i e^{−π(μ+ω)})`. -/
noncomputable def reflectionFactorII (μ ω : ℝ) : ℂ :=
  reflectionFactorI μ ω / (1 + Complex.I * ((Real.exp (-Real.pi * (μ + ω)) : ℝ) : ℂ))

/-- **[Theory-II reflection magnitude]** `‖R^II‖ = (1 + e^{−2π(μ+ω)})^{−1/2}` — not a pure phase. -/
lemma norm_reflectionFactorII (μ ω : ℝ) (hμ : 0 < μ) :
    ‖reflectionFactorII μ ω‖ = (Real.sqrt (1 + Real.exp (-2 * Real.pi * (μ + ω))))⁻¹ := by
  have hsq : Real.exp (-Real.pi * (μ + ω)) ^ 2 = Real.exp (-2 * Real.pi * (μ + ω)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [reflectionFactorII, norm_div, norm_reflectionFactorI μ ω hμ, norm_one_add_I_mul_ofReal, hsq,
    one_div]

/-- **[Theory II is not unitary]** `‖R^II‖ < 1`: reflection probability is strictly lost. -/
lemma reflectionFactorII_norm_lt_one (μ ω : ℝ) (hμ : 0 < μ) :
    ‖reflectionFactorII μ ω‖ < 1 := by
  rw [norm_reflectionFactorII μ ω hμ]
  have hS : 1 < Real.sqrt (1 + Real.exp (-2 * Real.pi * (μ + ω))) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith [Real.exp_pos (-2 * Real.pi * (μ + ω))]
  exact inv_lt_one_of_one_lt₀ hS


/-- **The theory-II transmission factor** (Eq. 2.11, continued): `T^II = −i e^{−π(μ+ω)} R^II`. -/
noncomputable def transmissionFactorII (μ ω : ℝ) : ℂ :=
  -Complex.I * ((Real.exp (-Real.pi * (μ + ω)) : ℝ) : ℂ) * reflectionFactorII μ ω

/-- **[Single-particle probability conservation]** `‖R^II‖² + ‖T^II‖² = 1`. Although theory II fails
multi-particle unitarity (it omits fermionic soliton sectors), the single-particle reflection and
transmission probabilities sum to one: `‖R^II‖² = 1/(1+e^{−2π(μ+ω)})`, `‖T^II‖² = e^{−2π(μ+ω)}/(1+e^{−2π(μ+ω)})`. -/
lemma reflectionTransmission_prob_conservation (μ ω : ℝ) (hμ : 0 < μ) :
    ‖reflectionFactorII μ ω‖ ^ 2 + ‖transmissionFactorII μ ω‖ ^ 2 = 1 := by
  set u := Real.exp (-2 * Real.pi * (μ + ω)) with hu
  have hu0 : (0 : ℝ) < u := Real.exp_pos _
  have hRsq : ‖reflectionFactorII μ ω‖ ^ 2 = (1 + u)⁻¹ := by
    rw [norm_reflectionFactorII μ ω hμ, ← hu, inv_pow, Real.sq_sqrt (by positivity)]
  have hesq : Real.exp (-Real.pi * (μ + ω)) ^ 2 = u := by
    rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hT : ‖transmissionFactorII μ ω‖ = Real.exp (-Real.pi * (μ + ω)) * ‖reflectionFactorII μ ω‖ := by
    rw [transmissionFactorII, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hTsq : ‖transmissionFactorII μ ω‖ ^ 2 = u * (1 + u)⁻¹ := by
    rw [hT, mul_pow, hesq, hRsq]
  rw [hRsq, hTsq]
  field_simp


/-- **[A quotient of conjugates is a pure phase with the doubled argument]** `z / z̄ = e^{2i arg z}`. -/
lemma div_conj_eq_exp_two_arg {z : ℂ} (hz : z ≠ 0) :
    z / (starRingEnd ℂ) z = Complex.exp (2 * (Complex.arg z : ℂ) * Complex.I) := by
  have hz' : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hconj : (starRingEnd ℂ) z = (‖z‖ : ℂ) * Complex.exp (-(Complex.arg z : ℂ) * Complex.I) := by
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I z]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [hconj]
  nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_div_mul_left _ _ hz', ← Complex.exp_sub]
  congr 1; ring

/-- **The exact reflection phase** `Θ(x) = arg Γ(½ − ix)` (Eq. 4.5, large-`x` form of the total phase). -/
noncomputable def reflectionPhase (x : ℝ) : ℝ :=
  Complex.arg (Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (x : ℂ)))

/-- **[The Gamma factor's phase is `2·arg Γ(½−iy)`]** `Γ(½−iy)/Γ(½+iy) = e^{2i·reflectionPhase y}`. The
half-phase `arg Γ(½−iy)` is exactly the reflection phase `Θ` of Eq. 4.5. -/
lemma gammaRatio_eq_exp_two_reflectionPhase (y : ℝ) :
    Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ))
        / Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))
      = Complex.exp (2 * (reflectionPhase y : ℂ) * Complex.I) := by
  have harg : (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ))
      = ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) := by
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have hne : Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  rw [show Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))
      = (starRingEnd ℂ) (Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (y : ℂ))) from by
      rw [← Complex.Gamma_conj, harg]]
  rw [reflectionPhase]
  exact div_conj_eq_exp_two_arg hne

/-- **[The rational factor's phase]** `(1+ix)/(1−ix) = e^{2i·arg(1+ix)}` — the second pure-phase factor of
the unitary reflection amplitude; its argument vanishes as `x → 0`, so the total phase reduces to the Gamma
phase `Θ` of Eq. 4.5 in the large-energy limit. -/
lemma rationalRatio_eq_exp_two_arg (x : ℝ) :
    (1 + Complex.I * (x : ℂ)) / (1 - Complex.I * (x : ℂ))
      = Complex.exp (2 * (Complex.arg (1 + Complex.I * (x : ℂ)) : ℂ) * Complex.I) := by
  have hconj : (1 - Complex.I * (x : ℂ)) = (starRingEnd ℂ) (1 + Complex.I * (x : ℂ)) := by
    simp only [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have hne : (1 + Complex.I * (x : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, mul_zero, zero_mul, sub_zero,
      add_zero] at hre
    exact one_ne_zero hre
  rw [hconj]; exact div_conj_eq_exp_two_arg hne

end Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix


namespace Physlib.QuantumMechanics.ComplexAction.MoorePlesserRamgoolamPoleStructure

/-- **The reflection-factor denominator** (Eq. 2.8) `1 − i e^{−π(μ+iz)}` — a Bhaduri-style Selberg factor
whose zeros are the analytic-`S`-matrix poles. -/
noncomputable def mprSelbergFactor (μ : ℝ) (z : ℂ) : ℂ :=
  1 - Complex.I * Complex.exp (-(Real.pi : ℂ) * ((μ : ℂ) + Complex.I * z))

/-- **[The metastable-bound-state poles]** `mprSelbergFactor μ z = 0` **iff** `z` lies on the discrete tower
`z_n = (½ − 2n) + iμ` (`n ∈ ℤ`): the complete set of reflection-`S`-matrix poles of Moore–Plesser–Ramgoolam
§5, with imaginary part the chemical potential `μ` and real part `½ − 2n`. -/
lemma mprSelbergFactor_eq_zero_iff (μ : ℝ) (z : ℂ) :
    mprSelbergFactor μ z = 0 ↔ ∃ n : ℤ, z = ((1 / 2 : ℂ) - 2 * (n : ℂ)) + Complex.I * (μ : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    push_cast; ring
  rw [mprSelbergFactor, sub_eq_zero, eq_comm,
    show Complex.I * Complex.exp (-(Real.pi : ℂ) * ((μ : ℂ) + Complex.I * z))
        = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I
          + -(Real.pi : ℂ) * ((μ : ℂ) + Complex.I * z)) from by rw [Complex.exp_add, ← hI],
    Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  constructor
  · intro h
    have hE : (Real.pi : ℂ) * Complex.I * z
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I - (Real.pi : ℂ) * (μ : ℂ)
          - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by linear_combination -h
    have hT : (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℂ) - 2 * (n : ℂ)) + Complex.I * (μ : ℂ))
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I - (Real.pi : ℂ) * (μ : ℂ)
          - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; linear_combination (Real.pi : ℂ) * (μ : ℂ) * Complex.I_sq
    exact mul_left_cancel₀ (mul_ne_zero hπ Complex.I_ne_zero) (hE.trans hT.symm)
  · intro h
    rw [h]; push_cast; linear_combination (-(Real.pi : ℂ) * (μ : ℂ)) * Complex.I_sq

/-- **[Pole-location corollary]** `mprSelbergFactor` vanishes at each `z_n = (½ − 2n) + iμ`. -/
lemma mprSelbergFactor_vanishes (μ : ℝ) (n : ℤ) :
    mprSelbergFactor μ (((1 / 2 : ℂ) - 2 * (n : ℂ)) + Complex.I * (μ : ℂ)) = 0 :=
  (mprSelbergFactor_eq_zero_iff μ _).mpr ⟨n, rfl⟩

end Physlib.QuantumMechanics.ComplexAction.MoorePlesserRamgoolamPoleStructure


open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

namespace Physlib.QuantumMechanics.ComplexAction.MoorePlesserRamgoolamInvertedResonanceBridge

/-- **The MPR inverted-oscillator resonance energy** `E_l = −i(l+½)ℏΩ` (`Ω` the inverted frequency; the
matrix model `H = ½p² − ⅛λ²` has `Ω = ½`). -/
noncomputable def mprInvertedResonance (ℏ Ω : ℝ) (l : ℕ) : ℂ :=
  -Complex.I * ((((l : ℝ) + 1 / 2) * ℏ * Ω : ℝ) : ℂ)

/-- **[The MPR resonance is the Nagao–Nielsen complex-oscillator energy at imaginary frequency]**
`E_l = oscillatorEnergy ℏ (−iΩ) l`. The inversion `ω → −iΩ` maps the bound Nagao–Nielsen spectrum
`ℏω(l+½)` onto the matrix-model resonances. -/
lemma mprInvertedResonance_eq_oscillatorEnergy (ℏ Ω : ℝ) (l : ℕ) :
    mprInvertedResonance ℏ Ω l = oscillatorEnergy ℏ (-Complex.I * (Ω : ℂ)) l := by
  unfold mprInvertedResonance oscillatorEnergy
  push_cast
  ring

/-- **[The resonance is a pure decay]** `Re E_l = 0` — no bound (real) part, unlike the Bhaduri case which
also has a harmonic frequency `ω₁`. -/
lemma mprInvertedResonance_re (ℏ Ω : ℝ) (l : ℕ) : (mprInvertedResonance ℏ Ω l).re = 0 := by
  simp [mprInvertedResonance, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **[The decay width]** `Im E_l = −(l+½)ℏΩ` — the Bhaduri inverted-oscillator decay width `−(l+½)ℏω₂`. -/
lemma mprInvertedResonance_im (ℏ Ω : ℝ) (l : ℕ) :
    (mprInvertedResonance ℏ Ω l).im = -(((l : ℝ) + 1 / 2) * ℏ * Ω) := by
  simp [mprInvertedResonance, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- **[The decay gap is strictly positive]** `−Im E_l = (l+½)ℏΩ > 0` (the Nagao–Nielsen non-Hermitian gap)
for positive `ℏ, Ω`. -/
lemma mprInvertedResonance_gap_pos (ℏ Ω : ℝ) (hℏ : 0 < ℏ) (hΩ : 0 < Ω) (l : ℕ) :
    0 < -(mprInvertedResonance ℏ Ω l).im := by
  rw [mprInvertedResonance_im, neg_neg]
  positivity

/-- **The matrix-model resonances** `E_l = −i(l+½)ℏ/2` (`H = ½p² − ⅛λ²`, so `Ω = ½`). -/
noncomputable def mprMatrixModelResonance (ℏ : ℝ) (l : ℕ) : ℂ :=
  mprInvertedResonance ℏ (1 / 2) l

end Physlib.QuantumMechanics.ComplexAction.MoorePlesserRamgoolamInvertedResonanceBridge


open Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

namespace Physlib.QuantumMechanics.ComplexAction.MoorePlesserRamgoolamNagaoNielsenBridge

/-- **The MPR reflection imaginary action** `S_I/ℏ = ½ log(1 + e^{−2π(μ+ω)})` — the
Nagao–Nielsen imaginary action whose damping factor `e^{−S_I/ℏ}` is the theory-II reflection magnitude. -/
noncomputable def mprReflectionImaginaryAction (μ ω : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + Real.exp (-2 * Real.pi * (μ + ω)))

/-- **[The imaginary action is strictly positive]** — theory II is non-reversible. -/
lemma mprReflectionImaginaryAction_pos (μ ω : ℝ) : 0 < mprReflectionImaginaryAction μ ω := by
  refine mul_pos (by norm_num) (Real.log_pos ?_)
  have := Real.exp_pos (-2 * Real.pi * (μ + ω)); linarith

/-- **[Theory-II reflection magnitude is the Nagao–Nielsen damping factor]**
`‖R^II‖ = e^{−S_I}` with `S_I = ½ log(1 + e^{−2π(μ+ω)})`. -/
lemma norm_reflectionFactorII_eq_exp_neg_imaginaryAction (μ ω : ℝ) (hμ : 0 < μ) :
    ‖reflectionFactorII μ ω‖ = Real.exp (-mprReflectionImaginaryAction μ ω) := by
  rw [norm_reflectionFactorII μ ω hμ, mprReflectionImaginaryAction]
  have hsqrt : Real.sqrt (1 + Real.exp (-2 * Real.pi * (μ + ω)))
      = Real.exp (Real.log (1 + Real.exp (-2 * Real.pi * (μ + ω))) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]; congr 1; ring
  rw [hsqrt, ← Real.exp_neg]; congr 1; ring

/-- **[Theory II ↔ Nagao–Nielsen weight with positive imaginary action].** The theory-II reflection
amplitude has the modulus of a Nagao–Nielsen complex-action path weight with the strictly positive
imaginary action `mprReflectionImaginaryAction` — the `c = 1` non-unitarity *is* the suppression factor. -/
lemma reflectionFactorII_norm_eq_nnPathWeight (μ ω S_R : ℝ) (hμ : 0 < μ) :
    ‖reflectionFactorII μ ω‖ = ‖nnPathWeight S_R (mprReflectionImaginaryAction μ ω) 1‖ := by
  rw [norm_reflectionFactorII_eq_exp_neg_imaginaryAction μ ω hμ, norm_nnPathWeight, div_one]

/-- **[Theory I ↔ Nagao–Nielsen weight with zero imaginary action].** The unitary theory-I reflection
amplitude is a pure Nagao–Nielsen phase: `‖R^I‖ = 1 = ‖nnPathWeight S_R 0 1‖` (vanishing imaginary action,
reversible). -/
lemma reflectionFactorI_norm_eq_nnPathWeight_reversible (μ ω S_R : ℝ) (hμ : 0 < μ) :
    ‖reflectionFactorI μ ω‖ = ‖nnPathWeight S_R 0 1‖ := by
  rw [norm_reflectionFactorI μ ω hμ, norm_nnPathWeight]; simp

end Physlib.QuantumMechanics.ComplexAction.MoorePlesserRamgoolamNagaoNielsenBridge

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI where
  formalizes @ "claim:the-type-I-two-d-string-reflection-factor-is-unitary-of-modulus-one",
  supported_by @ "paper:moore-plesser-ramgoolam-1992-two-d-string-s-matrix"

zil attach Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionFactorII_norm_lt_one where
  supported_by @ "lean:HermitianMat.exp_pos",
  formalizes @ "claim:the-type-II-two-d-string-reflection-factor-has-modulus-below-one-non-unitary",
  requires @ "claim:the-type-I-two-d-string-reflection-factor-is-unitary-of-modulus-one",
  caveat @ "claim:the-non-unitary-type-II-branch-is-the-dissipative-face-of-the-inverted-oscillator-reflection"

zil_file_contract physlib.twoDStringExactSMatrix where
  promises "The Moore-Plesser-Ramgoolam exact two-dimensional string S-matrix: the type-I reflection factor off the Liouville wall is unitary of modulus one, while the type-II factor has modulus strictly below one, the non-unitary face of the inverted-oscillator reflection."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionFactorI",
    "lean:Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionFactorII"]
  forbids_substitutes ["the full genus expansion or non-perturbative completion of the 2D string",
    "a derivation of the tachyon spectrum, only the reflection-factor moduli"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI,
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionFactorII_norm_lt_one]

/- ZIL-END -/
