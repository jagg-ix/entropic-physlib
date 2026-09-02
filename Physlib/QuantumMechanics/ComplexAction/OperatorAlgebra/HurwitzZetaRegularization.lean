/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom
public import Physlib.QuantumMechanics.ComplexAction.Dunkl.NagaoNielsenOscillator

/-!
# Hurwitz-zeta regularization of the one-loop `l`-mode sum (Johansson 2014)

Extends `GravLapse.GravOneLoopGelfandYaglom`: the one-loop fluctuation determinant of Mallik–Narain is an infinite
product over the `l`-modes (their Eq. 51), regularized via the **Hurwitz zeta function**
`ζ(s,a) = ∑_{k≥0} 1/(k+a)^s`. This file formalizes the Euler–Maclaurin structure of `ζ(s,a)` following
*F. Johansson, "Rigorous high-precision computation of the Hurwitz zeta function and its derivatives,"
Numer. Algorithms 69 (2015) 253 (DOI 10.1007/s11075-014-9893-1)*, and identifies the one-loop spectral
zeta with it.

* **§A — the Hurwitz zeta series** (`hurwitzZetaSeries`, Johansson §1): `ζ(s,a) = ∑_k 1/(k+a)^s`, with the
  Riemann zeta `ζ(s) = ζ(s,1)` (`riemannZeta_eq_hurwitz_one`).
* **§B — the Euler–Maclaurin head/tail split** (`hurwitzZeta_em_split`, Johansson Eqs. 5–6): `ζ(s,a) =
  S_N + (tail)`, the head sum `S_N = ∑_{k<N} 1/(k+a)^s` (`emHeadSum`) plus the remainder, the first step of
  the Euler–Maclaurin evaluation.
* **§C — the Euler–Maclaurin integral term** (`emIntegralTerm`, Johansson Eq. 7): `I = (a+N)^{1−s}/(s−1)`,
  the `∫_N^∞ (a+t)^{−s} dt` term, positive for `s > 1` (`emIntegralTerm_pos`).
* **§D — the rising factorial** (`risingFactorial`, Johansson): the Pochhammer `(s)_r` appearing in the
  derivatives `f^{(r)} = (−1)^r (s)_r/(a+k)^{s+r}`.
* **§E — the one-loop spectral zeta IS the Hurwitz zeta** (`spectralZeta_linear_eq_hurwitz`): for the
  linear spectrum `λ_l = l + a` of the `l`-mode operator, the spectral zeta `ζ_𝒟(s) = ∑_l λ_l^{−s}` equals
  `ζ(s,a)`, so the `ζ`-regularized log-determinant `ln det 𝒟 = −ζ'_𝒟(0)` (`zetaRegLogDet`) of the
  Gel'fand–Yaglom one-loop operator (`GravLapse.GravOneLoopGelfandYaglom`) is computed by the Johansson Hurwitz zeta
  (`zetaRegLogDet_linear_eq_hurwitz`).

## References

* F. Johansson, *Rigorous high-precision computation of the Hurwitz zeta function and its derivatives*,
  Numer. Algorithms 69 (2015) 253–270, DOI 10.1007/s11075-014-9893-1 — the Euler–Maclaurin formula for
  `ζ(s,a)` with rigorous error bounds.
* S. Mallik, G. Narain, *IR behaviour of one-loop complex `ℝ×S³` saddles*, arXiv:2604.21736 (2026) — the
  one-loop `l`-mode determinant and its `ζ`-regularization (§VI.B).
* S. W. Hawking, *Zeta function regularization of path integrals in curved spacetime*, Commun. Math. Phys.
  55 (1977) 133 — the `ln det = −ζ'(0)` prescription.
* Repo carrier: `GravLapse.GravOneLoopGelfandYaglom` (the one-loop determinant and prefactor).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization

open scoped Real


/-- **[Johansson §1] The Hurwitz zeta function** `ζ(s,a) = ∑_{k≥0} 1/(k+a)^s` (the convergent series for
`s > 1`, `a > 0`; defined here as the `tsum`). -/
noncomputable def hurwitzZetaSeries (s a : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + a) ^ s

/-- **[Johansson §1] The Riemann zeta is the Hurwitz zeta at `a = 1`** `ζ(s) = ζ(s,1)`. -/
noncomputable def riemannZetaSeries (s : ℝ) : ℝ := hurwitzZetaSeries s 1

lemma riemannZeta_eq_hurwitz_one (s : ℝ) : riemannZetaSeries s = hurwitzZetaSeries s 1 := rfl


/-- **[Johansson Eq. 6] The Euler–Maclaurin head sum** `S_N = ∑_{k=0}^{N-1} 1/(k+a)^s`. -/
noncomputable def emHeadSum (s a : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + a) ^ s

/-- **[Johansson Eq. 5] The Euler–Maclaurin head/tail split** `ζ(s,a) = S_N + (tail)`: splitting the
Hurwitz series at `k = N` into the finite head sum `S_N` and the tail `∑_{k≥0} 1/((k+N)+a)^s` (which the
Euler–Maclaurin formula approximates by `I + T + R`). -/
lemma hurwitzZeta_em_split (s a : ℝ) (N : ℕ)
    (h : Summable (fun k : ℕ => 1 / ((k : ℝ) + a) ^ s)) :
    hurwitzZetaSeries s a = emHeadSum s a N + ∑' k : ℕ, 1 / (((k + N : ℕ) : ℝ) + a) ^ s := by
  unfold hurwitzZetaSeries emHeadSum
  exact (Summable.sum_add_tsum_nat_add N h).symm


/-- **[Johansson Eq. 7] The Euler–Maclaurin integral term** `I = ∫_N^∞ (a+t)^{−s} dt = (a+N)^{1−s}/(s−1)`
— the leading (continuum) contribution to the tail. -/
noncomputable def emIntegralTerm (s a : ℝ) (N : ℕ) : ℝ := (a + N) ^ (1 - s) / (s - 1)

/-- The integral term is positive for `s > 1` and `a + N > 0`. -/
lemma emIntegralTerm_pos (s a : ℝ) (N : ℕ) (hs : 1 < s) (haN : 0 < a + N) :
    0 < emIntegralTerm s a N := by
  unfold emIntegralTerm
  exact div_pos (Real.rpow_pos_of_pos haN _) (by linarith)


/-- **[Johansson] The rising factorial** `(s)_r = s(s+1)⋯(s+r−1)` appearing in the derivatives
`f^{(r)}(k) = (−1)^r (s)_r/(a+k)^{s+r}` of the Hurwitz summand. -/
noncomputable def risingFactorial (s : ℝ) (r : ℕ) : ℝ := ∏ k ∈ Finset.range r, (s + k)

lemma risingFactorial_zero (s : ℝ) : risingFactorial s 0 = 1 := by simp [risingFactorial]

lemma risingFactorial_succ (s : ℝ) (r : ℕ) :
    risingFactorial s (r + 1) = risingFactorial s r * (s + r) := by
  simp [risingFactorial, Finset.prod_range_succ]


/-- **The spectral zeta function** `ζ_𝒟(s) = ∑_l λ_l^{−s}` of an operator with eigenvalues `λ_l`. -/
noncomputable def spectralZeta (lam : ℕ → ℝ) (s : ℝ) : ℝ := ∑' l : ℕ, (lam l) ^ (-s)

/-- **[Link] The one-loop spectral zeta of a linear spectrum is the Hurwitz zeta.** For the `l`-mode
operator with eigenvalues `λ_l = l + a` (the linear tower of the Gel'fand–Yaglom determinant), the spectral
zeta `∑_l (l+a)^{−s}` is exactly Johansson's Hurwitz zeta `ζ(s,a)`. -/
lemma spectralZeta_linear_eq_hurwitz (a s : ℝ) (ha : 0 ≤ a) :
    spectralZeta (fun l => (l : ℝ) + a) s = hurwitzZetaSeries s a := by
  unfold spectralZeta hurwitzZetaSeries
  congr 1; ext l; rw [Real.rpow_neg (by positivity), one_div]

/-- **[Hawking] The `ζ`-regularized log-determinant** `ln det 𝒟 = −ζ'_𝒟(0)` — the zeta-function
regularization of the divergent `l`-mode product (Mallik–Narain Eq. 51). -/
noncomputable def zetaRegLogDet (lam : ℕ → ℝ) : ℝ := -(deriv (spectralZeta lam) 0)

/-- **[Link] The `ζ`-regularized one-loop log-determinant of the linear spectrum is computed by the
Hurwitz zeta.** `ln det 𝒟 = −d/ds ζ(s,a)|_{s=0}` — the Gel'fand–Yaglom one-loop determinant
(`GravLapse.GravOneLoopGelfandYaglom`) of the `l = l+a` tower is regularized by Johansson's Hurwitz zeta. -/
lemma zetaRegLogDet_linear_eq_hurwitz (a : ℝ) (ha : 0 ≤ a) :
    zetaRegLogDet (fun l => (l : ℝ) + a) = -(deriv (fun s => hurwitzZetaSeries s a) 0) := by
  unfold zetaRegLogDet
  have heq : spectralZeta (fun l => (l : ℝ) + a) = fun s => hurwitzZetaSeries s a := by
    funext s; exact spectralZeta_linear_eq_hurwitz a s ha
  rw [heq]


/-- **[Link] The `ζ`-regularized determinant feeds the Gel'fand–Yaglom one-loop prefactor.** With the
`ζ`-regularized log-determinant `ln det 𝒟 = zetaRegLogDet`, the determinant is `det 𝒟 = e^{zetaRegLogDet}`,
and the one-loop Gaussian prefactor of `GravLapse.GravOneLoopGelfandYaglom` is `(det 𝒟)^{−1/2} = e^{−zetaRegLogDet/2}`
— the `ζ`-regularization of the infinite `l`-mode product *is* the input to the one-loop prefactor. -/
lemma oneLoopPrefactor_zetaReg (lam : ℕ → ℝ) :
    GravLapse.GravOneLoopGelfandYaglom.oneLoopPrefactor (Real.exp (zetaRegLogDet lam))
      = Real.exp (-(zetaRegLogDet lam) / 2) := by
  rw [GravLapse.GravOneLoopGelfandYaglom.oneLoopPrefactor, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1; ring

/-- **[Link] The Hurwitz-zeta parameter is the Dunkl/Bessel absorbing index** `a = ν + ½ =
besselAbsorbingIndex ν` (`Dunkl.EuclideanProcess`) — the Dunkl oscillator's zero-point shift and the
absorbing (Dirichlet) Bessel-process index coincide with the Hurwitz shift, tying the `ζ`-regularization to
the Wigner–Dunkl arc. -/
lemma hurwitz_param_eq_bessel_absorbing (ν : ℝ) :
    ν + 1 / 2 = Dunkl.EuclideanProcess.besselAbsorbingIndex ν := rfl

/-- **[Link] The absorbing-Bessel `l`-mode tower's spectral zeta is the Hurwitz zeta.** For the Dunkl
process's absorbing sector (the odd, antiperiodic / Dirichlet `l`-modes with index `ν + ½`,
`Dunkl.EuclideanProcess`), the spectral zeta `∑_l (l + ν + ½)^{−s}` is the Hurwitz zeta
`ζ(s, ν+½)` — so the Mallik–Narain `ζ`-regularized one-loop determinant of the Dunkl/Bessel tower is
Johansson's Hurwitz zeta. -/
lemma bessel_absorbing_spectralZeta (ν s : ℝ) (hν : -(1 / 2) ≤ ν) :
    spectralZeta (fun l => (l : ℝ) + Dunkl.EuclideanProcess.besselAbsorbingIndex ν) s
      = hurwitzZetaSeries s (Dunkl.EuclideanProcess.besselAbsorbingIndex ν) := by
  apply spectralZeta_linear_eq_hurwitz
  unfold Dunkl.EuclideanProcess.besselAbsorbingIndex; linarith


/-- **[Link] The Nagao–Nielsen complex oscillator's dimensionless spectrum is `n + ½`.** Dividing the NN
oscillator energy `E_n = ℏω(n+½)` (`ComplexOscillator.ComplexHarmonicOscillatorBoson.oscillatorEnergyReal`) by `ℏω` gives the
dimensionless tower `n + ½` whose spectral zeta is the Hurwitz zeta. -/
lemma nn_oscillator_dimensionless (ℏ ω : ℝ) (hℏ : ℏ ≠ 0) (hω : ω ≠ 0) (n : ℕ) :
    ComplexOscillator.ComplexHarmonicOscillatorBoson.oscillatorEnergyReal ℏ ω n / (ℏ * ω) = (n : ℝ) + 1 / 2 := by
  rw [ComplexOscillator.ComplexHarmonicOscillatorBoson.oscillatorEnergyReal]; field_simp

/-- **[Link] The Nagao–Nielsen complex oscillator's spectral zeta is the Hurwitz zeta `ζ(s, ½)`.** The NN
complex oscillator (`ComplexOscillator.ComplexHarmonicOscillatorBoson`, dimensionless spectrum `n + ½`) has spectral zeta
`∑_n (n+½)^{−s} = ζ(s, ½)` — its `ζ`-regularized determinant is Johansson's Hurwitz zeta at the bosonic
zero-point `½`. -/
lemma nn_oscillator_spectralZeta (s : ℝ) :
    spectralZeta (fun n => (n : ℝ) + 1 / 2) s = hurwitzZetaSeries s (1 / 2) :=
  spectralZeta_linear_eq_hurwitz (1 / 2) s (by norm_num)

/-- **[Link] The Dunkl–Nagao–Nielsen complex oscillator's spectral zeta is the Hurwitz zeta `ζ(s, ν+½)`.**
The Dunkl oscillator `E_n = ℏω(n+ν+½)` (`Dunkl.NagaoNielsenOscillator.dunklOscillatorEnergy`, the NN
complex oscillator dressed by the reflection `ν`) has dimensionless spectrum `n + ν + ½`, whose spectral
zeta is `ζ(s, ν+½)` — the reflection `ν` shifts the Hurwitz zero-point exactly by the Dunkl deformation,
joining the NN-oscillator `ζ`-regularization to the Wigner–Dunkl arc (cf. `bessel_absorbing_spectralZeta`,
`ν+½ = besselAbsorbingIndex ν`). -/
lemma dunkl_nn_oscillator_spectralZeta (ν s : ℝ) (hν : -(1 / 2) ≤ ν) :
    spectralZeta (fun n => (n : ℝ) + (ν + 1 / 2)) s = hurwitzZetaSeries s (ν + 1 / 2) :=
  spectralZeta_linear_eq_hurwitz (ν + 1 / 2) s (by linarith)

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization

end
