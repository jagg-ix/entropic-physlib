/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.PSeries

/-!
# `ζ(−1) = −1/12`: the string Casimir energy, proved

The string-Casimir module (`SciamaFockStringCasimir`) computed the transverse mode tower's spectral zeta as the
convergent Dirichlet series `riemannZetaSeries` (valid only for `s > 1`) and *quoted* the analytic continuation
`ζ(−1) = −1/12`.  Here that value is **proved** from Mathlib's analytically-continued Riemann zeta
(`riemannZeta`, via the Bernoulli-number formula `ζ(−k) = (−1)ᵏ Bₖ₊₁/(k+1)`), and the connection to the string
mode tower is made rigorous:

* `riemannZeta_neg_one` — **`ζ(−1) = −1/12`** (`= −B₂/2`, `B₂ = 1/6`).
* `riemannZetaSeries_eq_riemannZeta_re` — for `s > 1` the arc's convergent series `riemannZetaSeries s` equals
  `(riemannZeta s).re`: Mathlib's `riemannZeta` **is** the analytic continuation of the string mode tower's
  spectral zeta, so evaluating it at `s = −1` is the honest ζ-regularization.
* `stringIntercept_eq_zeta_casimir` — the string intercept `a = (D−2)/24` is now *derived* from the proved
  Casimir `−(D−2)·½·ζ(−1) = (D−2)/24`, closing the `SciamaFockStringCasimir` caveat: the critical dimension
  `D = 26` follows from `ζ(−1) = −1/12`, not from a quoted number.

Honest scope: the value `ζ(−1) = −1/12`, the series↔continuation identity on `Re s > 1`, and the Casimir/
intercept derivation.  The full analytic continuation of the *arc's* `riemannZetaSeries` (rather than Mathlib's
`riemannZeta`) is not re-derived — the two are identified on their common domain and Mathlib's continuation is
used past it.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir

/-- **[`ζ(−1) = −1/12`]** The analytically-continued Riemann zeta at `−1`, via the Bernoulli formula
`ζ(−k) = (−1)ᵏ Bₖ₊₁/(k+1)` with `B₂ = 1/6`. -/
theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  rw [Nat.cast_one, bernoulli_two] at h
  rw [h]
  push_cast
  norm_num

/-- `(ζ(−1)).re = −1/12` as a real number. -/
theorem riemannZeta_neg_one_re : (riemannZeta (-1)).re = -1 / 12 := by
  rw [riemannZeta_neg_one]
  simp

/-- **[Series = continuation on `Re s > 1`] `riemannZetaSeries s = (ζ(s)).re`.**  On its domain of convergence
the arc's Dirichlet series `Σₙ 1/(n+1)^s` is the real part of Mathlib's analytically-continued `riemannZeta`, so
`riemannZeta` is the genuine analytic continuation of the string mode tower's spectral zeta. -/
theorem riemannZetaSeries_eq_riemannZeta_re (s : ℝ) (hs : 1 < s) :
    riemannZetaSeries s = (riemannZeta (s : ℂ)).re := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (s : ℂ)
      = ((1 / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  have hsummC : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ (s : ℂ)) := by
    have h1 : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ (s : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr hs'
    refine ((summable_nat_add_iff 1).mpr h1).congr (fun n => ?_)
    rw [Nat.cast_add_one]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs', Complex.re_tsum hsummC,
    riemannZetaSeries, hurwitzZetaSeries]
  refine tsum_congr (fun n => ?_)
  rw [hterm n, Complex.ofReal_re]

/-- **[Intercept from the Casimir] `a = −(D−2)·½·ζ(−1) = (D−2)/24`.**  The string intercept is now derived from
the proved `ζ(−1) = −1/12`; with the massless level-1 vector (`a = 1`) this gives the critical dimension
`D = 26` (`SciamaFockStringCasimir.stringIntercept_eq_one_iff`). -/
theorem stringIntercept_eq_zeta_casimir (D : ℝ) :
    stringIntercept D = -(D - 2) * (1 / 2 * (riemannZeta (-1)).re) := by
  rw [riemannZeta_neg_one_re, stringIntercept]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir

end
