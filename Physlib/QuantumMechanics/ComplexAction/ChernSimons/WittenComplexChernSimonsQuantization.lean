/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.Explicit

/-!
# Witten's complex Chern–Simons quantization — couplings, reality, and the two branches

Formalizes the algebraic core of E. Witten, *Quantization of Chern–Simons Gauge Theory with Complex Gauge
Group* (Commun. Math. Phys. 137, 29–66, 1991) — the foundational paper behind the Hayashi CSW-gravity work.
A companion to `ChernSimons.ConcreteSynthesis` (which is maintained separately); this file supplies the
Witten-specific coupling and reality content.

The complex `G_ℂ` Chern–Simons action (Witten Eq. 2.1) has couplings `t = k + is`, `t̄ = k − is` (Eq. 2.2),
with `k` the **integer** Chern–Simons level (Eq. 2.3, `HayashiCouplings.level : ℤ`) and `s` a free parameter.

* **§A — coupling components** (`holomorphicCoupling_re/_im`): `t.re = k − Im s`, `t.im = Re s`.
* **§B — the reality condition** (Witten §2): the two couplings are complex conjugates iff `s` is real
  (`reality_condition_minkowski`), which is exactly the Minkowski/Lorentzian unitary branch; the second
  unitary branch (Euclidean, negative cosmological constant) is at imaginary `s`
  (`euclidean_branch_iff`). The two branches are mutually exclusive for `s ≠ 0` (`branches_disjoint`).
* **§C — level quantization** (Eq. 2.3): `t + t̄ = 2k` so `k` is the half-sum of the couplings, an integer;
  `t − t̄ = 2is` recovers the continuous parameter (`level_eq_half_coupling_sum`, `s_eq`).
* **§D — the Euclidean branch makes the coupling real** (Witten §2.1): on the imaginary-`s` branch
  `t = k + is` is self-conjugate (`conj t = t`, `euclidean_branch_coupling_real`) — the second unitary branch,
  Euclidean `SL(2,ℂ)` gravity with negative cosmological constant (the regime of `hayashiSL2CGravity`).

## References

* E. Witten (1991), *Quantization of Chern–Simons Gauge Theory with Complex Gauge Group*, Commun. Math.
  Phys. 137, 29–66, §2, Eqs. 2.1–2.3. structure: `Physlib` (`ChernSimons.Gravity`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — coupling components -/

/-- **[`t.re = k − Im s`]** the real part of the holomorphic coupling. -/
theorem holomorphicCoupling_re (c : HayashiCouplings) :
    (holomorphicCoupling c).re = (c.level : ℝ) - (c.s).im := by
  simp only [holomorphicCoupling, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.intCast_re]; ring

/-- **[`t.im = Re s`]** the imaginary part of the holomorphic coupling. -/
theorem holomorphicCoupling_im (c : HayashiCouplings) :
    (holomorphicCoupling c).im = (c.s).re := by
  simp [holomorphicCoupling, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.intCast_im]

/-! ## §B — the reality condition (Witten §2) -/

/-- **[Minkowski reality condition, Witten §2] `t̄ = conj t ⟺ s real`.** The two Chern–Simons couplings are
complex conjugates exactly when `s` is real — the condition for a real Lagrangian, hence the Lorentzian
unitary branch. -/
theorem reality_condition_minkowski (c : HayashiCouplings) :
    antiholomorphicCoupling c = (starRingEnd ℂ) (holomorphicCoupling c) ↔ (c.s).im = 0 := by
  rw [Complex.ext_iff, holomorphicCoupling, antiholomorphicCoupling]
  simp only [Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
    Complex.intCast_im]
  constructor
  · rintro ⟨h, _⟩; linarith
  · intro h; constructor <;> simp [h]

/-- **[Euclidean branch, Witten §2] `t real ⟺ s imaginary`.** The holomorphic coupling is real exactly when
`s` is purely imaginary — Witten's second unitary branch, Euclidean gravity with negative cosmological
constant. -/
theorem euclidean_branch_iff (c : HayashiCouplings) :
    (holomorphicCoupling c).im = 0 ↔ (c.s).re = 0 := by
  rw [holomorphicCoupling_im]

/-- **[The two branches are disjoint for `s ≠ 0`].** A nonzero `s` cannot be both real and imaginary, so the
Lorentzian (`Im s = 0`) and Euclidean (`Re s = 0`) unitary branches do not overlap. -/
theorem branches_disjoint (c : HayashiCouplings) (hs : c.s ≠ 0) :
    ¬ ((c.s).im = 0 ∧ (c.s).re = 0) := by
  rintro ⟨h1, h2⟩
  exact hs (Complex.ext h2 h1)

/-! ## §C — level quantization (Witten Eq. 2.3) -/

/-- **[The level is the half-sum of the couplings] `(t + t̄)/2 = k`** — `k` is an integer (Witten's
quantization law `k ∈ ℤ`, `HayashiCouplings.level`), the topological Chern–Simons level. -/
theorem level_eq_half_coupling_sum (c : HayashiCouplings) :
    (holomorphicCoupling c + antiholomorphicCoupling c) / 2 = (c.level : ℂ) := by
  rw [holomorphicCoupling_add_antiholomorphicCoupling]; ring

/-- **[The free parameter `s` from the couplings] `(t − t̄)/(2i) = s`.** -/
theorem s_eq_coupling_diff (c : HayashiCouplings) :
    (holomorphicCoupling c - antiholomorphicCoupling c) / (2 * Complex.I) = c.s := by
  rw [holomorphicCoupling_sub_antiholomorphicCoupling]
  field_simp

/-! ## §D — the Euclidean branch makes the coupling real (Witten §2.1) -/

/-- **[On the Euclidean branch the coupling `t` is real, Witten §2.1].** When `s` is purely imaginary
(`Re s = 0`) the holomorphic coupling `t = k + is` is self-conjugate (`conj t = t`) — a genuinely real
coupling. This is the second unitary branch, Euclidean `SL(2,ℂ)` gravity with negative cosmological constant
(the regime of `hayashiSL2CGravity`). -/
theorem euclidean_branch_coupling_real (c : HayashiCouplings) (hEuclid : (c.s).re = 0) :
    (starRingEnd ℂ) (holomorphicCoupling c) = holomorphicCoupling c := by
  rw [Complex.conj_eq_iff_im, holomorphicCoupling_im]; exact hEuclid

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
