/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
public import Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

/-!
# Linking the Nagao–Nielsen and Kozak contours through the entropic time

This file links the **complex-plane contours** of the complex oscillator / Nagao–Nielsen complex
action (`ComplexDelta.Convergence.lorentzianForm`, the convergence cone `L(q) > 0`) to the
**Kramers–Kronig contours** of Kozak et al. (`KramersKronig.Parity`, even/odd parity), and shows
both meet the **entropic time** `τ_ent = S_I/ℏ = binEntropy(v²)` (`Bogoliubov.EntropicTime`).

A contour point is `q = ω + iγ` (`ω` real frequency, `γ` damping). The three structures all key
on the same split into real and imaginary parts:

* **Nagao–Nielsen**: `L(q) = (Re q)² − (Im q)² = ω² − γ²`; the contour converges in the *timelike*
  cone `L > 0` (`|ω| > |γ|`), and the Wick rotation `q → iq` flips it (`L(iq) = −L(q)`).
* **Kozak (KK)**: as a function of the real frequency `ω`, the Nagao–Nielsen dispersion
  `ω ↦ L(ω + iγ)` is **even** — exactly the Kozak even-parity dispersion.
* **Entropic time**: the imaginary part `γ` is the Bogoliubov gap `Δ`; on the **real contour**
  `γ = 0` (the Nagao–Nielsen real axis = the Kozak real-frequency axis) the entropic time
  vanishes — the reversible fiber. Off the real axis (`γ ≠ 0`) the dissipation produces entropy.

## Main results

* `lorentzianDispersion` — `ω ↦ L(ω + iγ)`; `lorentzianDispersion_fnEven` (Kozak even parity).
* `lorentzianDispersion_real_nonneg` — at `γ = 0`, `L = ω² ≥ 0` (Nagao–Nielsen timelike / reversible).
* `wick_flips_lorentzian` — `L(iq) = −L(q)` (the contour rotation = Kozak half-plane swap).
* `real_contour_reversible` — **the link**: on the real contour (`γ = 0`) the Nagao–Nielsen form
  is timelike, the Kozak dispersion is even, *and* the Bogoliubov entropic time is zero — the
  three contour/parity/entropy structures agree at the reversible fiber.

## References

* K. Nagao, H. B. Nielsen (complex contours); M. Kozak et al., IJISET 4(12) (2017) (KK contours).
* `ComplexDelta.Convergence`, `KramersKronig.Parity`, `Bogoliubov.EntropicTime` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime

/-! ## §A — the Nagao–Nielsen contour form as a Kozak-even dispersion -/

/-- **The Nagao–Nielsen Lorentzian form on the contour `q = ω + iγ`, as a function of the real
frequency `ω`**: `L(ω + iγ) = ω² − γ²`. -/
def lorentzianDispersion (γ : ℝ) : ℝ → ℝ :=
  fun ω => lorentzianForm ((ω : ℂ) + (γ : ℂ) * Complex.I)

/-- **The Nagao–Nielsen dispersion is Kozak-even** in the frequency `ω` (`L(−ω + iγ) = L(ω + iγ)`):
the convergence-cone form is the even (dispersion) part of the Kramers–Kronig structure. -/
theorem lorentzianDispersion_fnEven (γ : ℝ) : FnEven (lorentzianDispersion γ) := by
  intro ω
  unfold lorentzianDispersion lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-! ## §B — the real contour (`γ = 0`) is timelike; the Wick rotation flips it -/

/-- **On the real contour** (`γ = 0`) the Nagao–Nielsen form is timelike `L = ω² ≥ 0` — the
reversible axis. -/
theorem lorentzianDispersion_real_nonneg (ω : ℝ) : 0 ≤ lorentzianDispersion 0 ω := by
  unfold lorentzianDispersion lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  positivity

/-- **The Wick rotation flips the Lorentzian form** `L(iq) = −L(q)`: the contour rotation by `π/2`
takes the timelike (reversible) cone to the spacelike (irreversible) one — the Kozak upper ↔
lower half-plane swap (multiplication by `i` rotates the half-plane). -/
theorem wick_flips_lorentzian (q : ℂ) : lorentzianForm (Complex.I * q) = -lorentzianForm q :=
  lorentzianForm_mul_I q

/-! ## §C — the link: real contour = reversible (all three structures agree) -/

/-- **The contour link.** On the real contour (`γ = 0`, the Nagao–Nielsen real axis = the Kozak
real-frequency axis) the three structures agree at the reversible fiber:

* the Nagao–Nielsen form is timelike, `L = ω² ≥ 0`;
* the Kozak dispersion is even (`FnEven`);
* the Bogoliubov entropic time vanishes, `τ_ent = 0` (no gap, no entropy production).

Off the real axis (`γ = Δ ≠ 0`) the imaginary part is the dissipative / entropic direction common
to all three: the convergence cone narrows, the contour acquires an odd absorption part, and the
entropic time turns on. -/
theorem real_contour_reversible (ξ : ℝ) (hξ : 0 < ξ) (ω : ℝ) :
    0 ≤ lorentzianDispersion 0 ω
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0 :=
  ⟨lorentzianDispersion_real_nonneg ω, lorentzianDispersion_fnEven 0,
   bogoliubov_entropicTime_normal_zero ξ hξ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime

end
