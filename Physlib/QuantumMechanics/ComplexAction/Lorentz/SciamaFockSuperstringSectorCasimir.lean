/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Superstring sector Casimir energies from the Hurwitz zeta `ζ(−1, a)`

The worldsheet moding fixes the Hurwitz offset `a` of the sector's oscillator tower (the Nagao–Nielsen /
Wigner–Dunkl `a`-shift of `SciamaFockNagaoNielsenZeta`), and the ζ-regularized zero-point of that sector is the
Hurwitz zeta at negative integer, `ζ(−1, a) = −B₂(a)/2` (`hurwitzZeta_neg_nat`, Bernoulli polynomial `B₂`):

* `hurwitzZeta_zero_neg_one` — **integer (bosonic / Ramond) modes** `a = 0`: `ζ(−1, 0) = ζ(−1) = −1/12`
  (`hurwitzZeta 0 = riemannZeta`, `SciamaFockZetaCasimir.riemannZeta_neg_one`).  The Casimir `½·(−1/12) = −1/24`
  per transverse boson — the `D = 26` bosonic string.
* `hurwitzZeta_half_neg_one` — **half-integer (Neveu–Schwarz) modes** `a = ½`: `ζ(−1, ½) = −B₂(½)/2 = 1/24`
  (`B₂(½) = −1/12`).  The NS sector's zero-point has the *opposite* sign.
* `hurwitzZeta_half_eq_neg_half_zero` — the **half-integer reflection** `ζ(−1, ½) = (2⁻¹ − 1)·ζ(−1, 0)`: shifting
  the moding by ½ rescales the sector Casimir by `2^s − 1` at `s = −1`, the arithmetic behind the NS/R Casimir
  split of the superstring GSO projection.

So the Nagao–Nielsen `a`-parameter that shifted the Hurwitz zeta `ζ(s, ν+½)` is, at `s = −1`, the **superstring
sector label**: `a = 0` (integer / R) gives `−1/12`, `a = ½` (NS) gives `1/24`, and their difference is the
zero-point offset that GSO-projects the tachyon and fixes the superstring dimension.

Honest scope: the exact sector Casimir values `ζ(−1, 0) = −1/12`, `ζ(−1, ½) = 1/24`, and their `2^s − 1`
reflection, all from Mathlib's analytically-continued Hurwitz zeta and the Bernoulli polynomial `B₂`.  The GSO
projection and the superstring critical dimension `D = 10` are contextualized, not derived here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockSuperstringSectorCasimir

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir
open HurwitzZeta

/-- **[Integer / bosonic sector Casimir] `ζ(−1, 0) = −1/12`.**  Integer-moded (bosonic / Ramond) oscillators:
the Hurwitz zeta at `a = 0` is the Riemann zeta, whose value at `−1` is `−1/12`. -/
theorem hurwitzZeta_zero_neg_one : hurwitzZeta (0 : UnitAddCircle) (-1) = -1 / 12 := by
  rw [hurwitzZeta_zero, riemannZeta_neg_one]

/-- **[Neveu–Schwarz sector Casimir] `ζ(−1, ½) = 1/24`.**  Half-integer-moded (NS) oscillators: the Hurwitz zeta
at `a = ½` gives `−B₂(½)/2 = 1/24` — the NS zero-point has the opposite sign to the integer sector. -/
theorem hurwitzZeta_half_neg_one :
    hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (-1) = 1 / 24 := by
  have hx : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h := hurwitzZeta_neg_nat (k := 1) one_ne_zero hx
  rw [Nat.cast_one] at h
  rw [h, Polynomial.eval_map]
  simp [Polynomial.bernoulli, Finset.sum_range_succ]
  norm_num

/-- **[Half-integer moding reflection] `ζ(−1, ½) = (2⁻¹ − 1)·ζ(−1, 0)`.**  Shifting the moding by ½ rescales the
sector Casimir by the factor `2^s − 1` evaluated at `s = −1` — the arithmetic of the superstring NS/R split. -/
theorem hurwitzZeta_half_eq_neg_half_zero :
    hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (-1)
      = (2⁻¹ - 1) * hurwitzZeta (0 : UnitAddCircle) (-1) := by
  rw [hurwitzZeta_half_neg_one, hurwitzZeta_zero_neg_one]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockSuperstringSectorCasimir

end
