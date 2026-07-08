/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# The 45° light cone of special relativity and the hyperbolic unification of complex-action/entropic-time

This file formalizes the **45° rules** of special relativity (the light cone) using the hyperbolic
boost theorems of this branch, links them to the last reply (`Bogoliubov.DiracEinsteinMass`: the gap
`Δ` as rest mass, `E² − ξ² = Δ²`), and connects both to the **hyperbolic unification equations** of
the complex-action/entropic-time grand-unification document (`E_R ∝ cos(k_R) cosh(k_I)`,
`E_I = ⟨T̂⟩ ∝ sin(k_R) sinh(k_I)`).

## The 45° light cone (special relativity)

In a Minkowski diagram the light cone is the pair of `45°` null lines `Re q = ±Im q`, the boundary
between the *timelike* (dynamics) and *spacelike* (locality) regions — the two non-information
"faces" of the unification document. We formalize the null condition as `lightlike q := lorentzianForm
q = 0` and prove:

* `lightlike_iff_abs_eq` — the `45°` condition `|Re q| = |Im q|` (equal legs, slope `±1`).
* `boost_preserves_lightlike` — **the defining 45° rule**: a Lorentz boost maps the light cone to
  itself (`t² = x² ⟹ t'² = x'²`), via `lorentzBoost_preserves_form`. The `45°` lines are boost
  invariant.
* `tanh_abs_lt_one` — `|β| = |tanh η| < 1`: a finite boost never reaches the `45°` slope (light
  speed); the null lines are asymptotes.

## Link to the last reply: massless ⟺ on the light cone

* `massless_energyVector_lightlike` — at `Δ = 0` the energy vector `(E, ξ)` is lightlike
  (`lorentzianForm = Δ² = 0`): the **massless limit is the 45° cone** (`β = ξ/E = ±1`,
  `velocity_eq_one_iff_massless`).
* `massive_energyVector_not_lightlike` — `Δ ≠ 0` keeps it strictly inside the cone (timelike).

## The hyperbolic unification equations (grand-unification document)

The complex dispersion `cos(k_R + i k_I)` *is* the single hyperbolic unification equation; its real
and imaginary parts are the document's two sectors:

* `catDispersion_re` — `Re cos(k_R + i k_I) = cos(k_R) cosh(k_I)` (the real energy `E_R`).
* `catDispersion_im` — `Im cos(k_R + i k_I) = −sin(k_R) sinh(k_I)` (the entropic time `E_I = ⟨T̂⟩`).
* `catBackReaction_eq_lorentzFactor` — the back-reaction factor `cosh(k_I)` **is** the Lorentz factor
  `γ = lorentzFactor k_I` (imaginary momentum `k_I` = rapidity), `≥ 1` (`catBackReaction_ge_one`):
  ticking (`k_I ≠ 0`) raises `E_R` exactly as Einstein's `E = γmc² ≥ mc²`.

## Main results

* `lightlike`, `lightlike_iff_abs_eq`, `lightlike_slope`, `boost_preserves_lightlike`,
  `tanh_abs_lt_one`.
* `massless_energyVector_lightlike`, `massive_energyVector_not_lightlike`.
* `catDispersion`, `catDispersion_re`, `catDispersion_im`, `catEnergyReal`, `catEntropicTime`,
  `catEnergyReal_eq`, `catEntropicTime_eq`, `catBackReaction_eq_lorentzFactor`,
  `catEntropicTime_eq_zero_iff`.
* `lightcone45_hyperbolic_unification` — the bundled link.

## References

* complex-action/entropic-time grand-unification document (Dec 2025), §0 (Three Faces) and the complex tight-binding
  dispersion `E_R ∝ cos cosh`, `E_I ∝ sin sinh`.
* `Bogoliubov.DiracEinsteinMass`, `TimeOperator.HyperbolicPoincareLorentzMisra`, `Rapidity.FutureIncludedLorentzian`
  (this development); `Complex.cos_add_mul_I` (Mathlib).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass

namespace Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification

/-! ## §A — the 45° light cone (the null condition) -/

/-- **The light cone (null condition)** `L(q) = 0`: the `45°` lines of the Minkowski diagram, the
boundary between the timelike and spacelike regions. -/
def lightlike (q : ℂ) : Prop := lorentzianForm q = 0

/-- **The 45° condition** `|Re q| = |Im q|` (equal legs, slope `±1`): a point is lightlike iff its
"time" and "space" coordinates have equal magnitude. -/
theorem lightlike_iff_abs_eq (q : ℂ) : lightlike q ↔ |q.re| = |q.im| := by
  unfold lightlike lorentzianForm
  rw [sub_eq_zero]
  constructor
  · intro h
    have hfac : (q.re - q.im) * (q.re + q.im) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact abs_eq_abs.mpr (Or.inl (by linarith))
    · exact abs_eq_abs.mpr (Or.inr (by linarith))
  · intro h
    rcases abs_eq_abs.mp h with h1 | h1
    · rw [h1]
    · rw [h1]; ring

/-- **The 45° slopes** `Im q = ±Re q`: a lightlike point lies on one of the two `45°` null lines. -/
theorem lightlike_slope (q : ℂ) (h : lightlike q) : q.im = q.re ∨ q.im = -q.re := by
  rcases abs_eq_abs.mp ((lightlike_iff_abs_eq q).mp h) with h1 | h1
  · exact Or.inl h1.symm
  · exact Or.inr (by linarith)

/-! ## §B — the 45° rules under the Lorentz boost (special relativity) -/

/-- **The defining 45° rule of special relativity**: a Lorentz boost maps the light cone to itself.
If `t² = x²` (a `45°` null point) then the boosted point is still null (`t'² = x'²`), because the
boost preserves the Minkowski form `t² − x²` (`lorentzBoost_preserves_form`). -/
theorem boost_preserves_lightlike (θ t x : ℝ) (h : t ^ 2 = x ^ 2) :
    (lorentzBoost θ t x).1 ^ 2 = (lorentzBoost θ t x).2 ^ 2 := by
  have hpres := lorentzBoost_preserves_form θ t x
  linarith [hpres, h]

/-- **A finite boost never reaches the 45° slope (light speed)** `|β| = |tanh η| < 1`: since
`cosh² η − sinh² η = 1` forces `|sinh η| < cosh η`. The `45°` null lines are asymptotes of the boost
orbit — sub-luminal velocities compose to sub-luminal velocities. -/
theorem tanh_abs_lt_one (η : ℝ) : |Real.tanh η| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos η),
    div_lt_one (Real.cosh_pos η), ← Real.sqrt_sq_eq_abs]
  have h1 : Real.sinh η ^ 2 < Real.cosh η ^ 2 := by nlinarith [Real.cosh_sq_sub_sinh_sq η]
  calc Real.sqrt (Real.sinh η ^ 2) < Real.sqrt (Real.cosh η ^ 2) :=
        Real.sqrt_lt_sqrt (sq_nonneg _) h1
    _ = Real.cosh η := Real.sqrt_sq (Real.cosh_pos η).le

/-! ## §C — link to the last reply: massless ⟺ on the 45° cone -/

/-- **The massless limit is the 45° light cone**: at `Δ = 0` the energy vector `(E, ξ)` is lightlike
(`lorentzianForm = Δ² = 0`). With no rest mass the worldline runs along the `45°` null line
`β = ξ/E = ±1`. -/
theorem massless_energyVector_lightlike (ξ : ℝ) :
    lightlike ((bogoliubovEnergy ξ 0 : ℂ) + (ξ : ℂ) * Complex.I) := by
  unfold lightlike
  rw [bogoliubov_energyVector_lorentzianForm]
  norm_num

/-- **A massive worldline stays strictly inside the 45° cone** (`Δ ≠ 0 ⟹` not lightlike): the gap
`Δ²` is the positive Minkowski interval, so the energy vector is timelike, never on the null line. -/
theorem massive_energyVector_not_lightlike (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    ¬ lightlike ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I) := by
  unfold lightlike
  rw [bogoliubov_energyVector_lorentzianForm]
  exact pow_ne_zero 2 hΔ

/-! ## §D — the hyperbolic unification equations (complex-action/entropic-time grand-unification document) -/

/-- **The complex complex-action/entropic-time dispersion** `cos(k_R + i k_I)` — the single hyperbolic unification
equation whose real/imaginary parts are the document's real energy and entropic time. -/
def catDispersion (k_R k_I : ℝ) : ℂ := Complex.cos ((k_R : ℂ) + (k_I : ℂ) * Complex.I)

/-- **The real-energy equation** `Re cos(k_R + i k_I) = cos(k_R) cosh(k_I)` (the document's `E_R`,
the `cosh` back-reaction). -/
theorem catDispersion_re (k_R k_I : ℝ) :
    (catDispersion k_R k_I).re = Real.cos k_R * Real.cosh k_I := by
  unfold catDispersion
  rw [Complex.cos_add_mul_I]
  simp [Complex.sub_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]

/-- **The entropic-time equation** `Im cos(k_R + i k_I) = −sin(k_R) sinh(k_I)` (the document's
`E_I = ⟨T̂⟩`, the `sinh` clock). -/
theorem catDispersion_im (k_R k_I : ℝ) :
    (catDispersion k_R k_I).im = -(Real.sin k_R * Real.sinh k_I) := by
  unfold catDispersion
  rw [Complex.cos_add_mul_I]
  simp [Complex.sub_im, Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im]

/-- **The real energy** `E_R = −J(2 cos(k_R) cosh(k_I) − 2Δ)` (grand-unification document). -/
def catEnergyReal (J Δ k_R k_I : ℝ) : ℝ := -J * (2 * Real.cos k_R * Real.cosh k_I - 2 * Δ)

/-- **The entropic time** `E_I = ⟨T̂⟩ = J(2 sin(k_R) sinh(k_I))` (grand-unification document). -/
def catEntropicTime (J k_R k_I : ℝ) : ℝ := J * (2 * Real.sin k_R * Real.sinh k_I)

/-- **`E_R` is the real part of the unified complex dispersion** (`-2J·Re + 2JΔ`). -/
theorem catEnergyReal_eq (J Δ k_R k_I : ℝ) :
    catEnergyReal J Δ k_R k_I = -2 * J * (catDispersion k_R k_I).re + 2 * J * Δ := by
  rw [catDispersion_re]; unfold catEnergyReal; ring

/-- **`E_I = ⟨T̂⟩` is the imaginary part of the unified complex dispersion** (`-2J·Im`). -/
theorem catEntropicTime_eq (J k_R k_I : ℝ) :
    catEntropicTime J k_R k_I = -2 * J * (catDispersion k_R k_I).im := by
  rw [catDispersion_im]; unfold catEntropicTime; ring

/-- **The `cosh(k_I)` back-reaction is the Lorentz factor** `γ = lorentzFactor k_I` (imaginary
momentum `k_I` = rapidity). The real-energy enhancement of the document is Einstein's `γ`. -/
theorem catBackReaction_eq_lorentzFactor (k_I : ℝ) : Real.cosh k_I = lorentzFactor k_I := rfl

/-- **The back-reaction is `≥ 1`** (`cosh k_I ≥ 1`): a frozen clock (`k_I = 0`) gives the minimal
energy `cosh 0 = 1`, and ticking (`k_I ≠ 0`) raises it — exactly `E = γmc² ≥ mc²`. -/
theorem catBackReaction_ge_one (k_I : ℝ) : 1 ≤ Real.cosh k_I := lorentzFactor_ge_one k_I

/-- **The entropic time vanishes iff the clock is frozen**: `⟨T̂⟩ = 0 ⟺ sin(k_R) = 0 ∨ sinh(k_I) = 0`
(real momentum at a band edge, or zero imaginary momentum `k_I = 0`). -/
theorem catEntropicTime_eq_zero_iff (J k_R k_I : ℝ) (hJ : J ≠ 0) :
    catEntropicTime J k_R k_I = 0 ↔ Real.sin k_R = 0 ∨ Real.sinh k_I = 0 := by
  unfold catEntropicTime
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hh | hh
    · exact absurd hh hJ
    · rcases mul_eq_zero.mp hh with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact Or.inl h3
      · exact Or.inr h2
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-! ## §E — the bundled link -/

/-- **The 45° light cone and the hyperbolic unification, together.**

* the **45° light cone is boost-invariant** (`t² = x² ⟹ t'² = x'²`) — special relativity;
* the **massless limit lies on the 45° cone** (`Δ = 0 ⟹` lightlike), while a **massive worldline
  stays inside it** (`Δ ≠ 0 ⟹` not lightlike) — the gap as rest mass;
* the document's **real-energy back-reaction `cosh(k_I)` is the Lorentz factor** `γ = lorentzFactor
  k_I ≥ 1` — the hyperbolic unification, with `k_I` (imaginary momentum) the boost rapidity. -/
theorem lightcone45_hyperbolic_unification (ξ k_I : ℝ) :
    (∀ θ t x : ℝ, t ^ 2 = x ^ 2 → (lorentzBoost θ t x).1 ^ 2 = (lorentzBoost θ t x).2 ^ 2)
      ∧ lightlike ((bogoliubovEnergy ξ 0 : ℂ) + (ξ : ℂ) * Complex.I)
      ∧ (∀ Δ : ℝ, Δ ≠ 0 → ¬ lightlike ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I))
      ∧ Real.cosh k_I = lorentzFactor k_I
      ∧ 1 ≤ lorentzFactor k_I :=
  ⟨fun θ t x h => boost_preserves_lightlike θ t x h,
   massless_energyVector_lightlike ξ,
   fun Δ hΔ => massive_energyVector_not_lightlike ξ Δ hΔ,
   catBackReaction_eq_lorentzFactor k_I,
   catBackReaction_ge_one k_I⟩

end Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification

end

end
