/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime

/-!
# The gravitational lapse contour is the Nagao–Nielsen / Kozak / entropic contour point

Links the Banihashemi–Jacobson lapse contour (`GravLapse.ContourMaster`) to the unified contour-point
structure of `EntropicTime.NagaoKozakContourEntropicTime` — the Nagao–Nielsen convergence cone, the Kozak even-parity
Kramers–Kronig dispersion, and the Bogoliubov entropic time. The connecting observation: the **complex
lapse** `N − iε` (Banihashemi–Jacobson arXiv:2405.10307 Eq. 5) is exactly a **contour point**
`q = ω + iγ` with real frequency `ω = N` (the lapse) and damping `γ = ε` (the `iε` regulator). The
contour displacement `ε` is the single dissipative / entropic imaginary direction shared by all three
structures.

* **§A — the complex lapse is a contour point; its Nagao–Nielsen form is the Kozak dispersion**
  (`complexLapse_eq_contourPoint`, `lapse_lorentzianForm_eq_dispersion`). `complexEnergy N ε = N − iε` is
  the contour point `ω + iγ` at `ω = N`, `γ = −ε`, and its Nagao–Nielsen convergence-cone form
  `lorentzianForm(N − iε) = N² − ε²` is `lorentzianDispersion ε N` — the Kozak-even dispersion in the lapse
  frequency `N` with the contour displacement `ε` as the damping.
* **§B — the real lapse contour is the reversible fiber** (`lapse_real_contour_reversible`). At `ε = 0`
  (the real lapse axis = the Nagao–Nielsen real axis = the Kozak real-frequency axis) the four structures
  agree: the form is timelike `L = N² ≥ 0`, the dispersion is even, the Bogoliubov entropic time vanishes,
  *and* the lapse weight is unimodular `‖lapseWeight N 0 ℋ‖ = 1` (no entropic damping). The reversible
  fiber of `real_contour_reversible` is exactly the reversible (`S_I = 0`) lapse fiber.
* **§C — turning on the contour displacement is irreversible** (`lapse_cone_narrows`,
  `lapse_irreversible_off_axis`). For `ε ≠ 0` the Nagao–Nielsen convergence cone narrows
  (`N² − ε² < N²`), and for `ε, ℋ > 0` the lapse weight modulus drops below one
  (`‖lapseWeight N ε ℋ‖ = e^{−εℋ} < 1`): the `iε` lapse displacement is the Bogoliubov gap `Δ = γ`, the
  Kozak odd-absorption direction, and the Nagao–Nielsen spacelike direction all at once.

## References

* B. Banihashemi, T. Jacobson, *On the lapse contour in the gravitational path integral*,
  arXiv:2405.10307v3 (2 Mar 2025), DOI `10.48550/arXiv.2405.10307`, §II — the `N − iε` complex lapse
  contour (Eq. 5, p. 3); the contour is below the real axis, giving the metric a complex signature
  (§III, p. 5).
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. 126 (2011) 1021,
  DOI `10.1143/PTP.126.1021` — the convergence cone `L(q) > 0` (the timelike contour).
* M. Kozak, V. Lukeš et al., *Kramers–Kronig relations*, IJISET 4(12) (2017) — the even/odd parity
  dispersion / absorption split of the half-plane contour.
* Repo dependencies: `GravLapse.ContourMaster` (`lapseWeight`, `lapseWeight_modulus`),
  `EntropicTime.NagaoKozakContourEntropicTime` (`lorentzianDispersion`, `real_contour_reversible`),
  `NonHermitian.WickRotation` (`complexEnergy`, the complex lapse), `ComplexDelta.Convergence`
  (`lorentzianForm`), `Bogoliubov.EntropicTime` (`bogoliubovEntropicTime`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime

open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## §A — the complex lapse is a contour point; its NN form is the Kozak dispersion -/

/-- The Nagao–Nielsen dispersion on the contour `q = ω + iγ` is `L(ω + iγ) = ω² − γ²`. -/
theorem lorentzianDispersion_eq (γ ω : ℝ) : lorentzianDispersion γ ω = ω ^ 2 - γ ^ 2 := by
  unfold lorentzianDispersion lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **The Nagao–Nielsen form of the complex lapse is the spacetime interval** `lorentzianForm(N − iε) =
N² − ε²`. **Constructed from the contour point's legs**: the spacetime-interval equation
`lorentzianForm(q) = (Re q)² − (Im q)²` (the definition of `lorentzianForm`) applied to `q = complexEnergy N ε`,
with the **timelike leg** `Re q = N` (`GravLapse.ContourMaster.lapse_re_eq`) and the **spacelike leg**
`Im q = −ε` (`GravLapse.ContourMaster.lapse_im_eq_gap`, the gap): `N² − (−ε)² = N² − ε²`. The gap `ε` of
`lapse_im_eq_gap` is exactly the spacelike component subtracted in the interval. -/
theorem lapse_lorentzianForm_eq (N ε : ℝ) : lorentzianForm (complexEnergy N ε) = N ^ 2 - ε ^ 2 := by
  unfold lorentzianForm
  rw [lapse_re_eq, lapse_im_eq_gap]; ring

/-- **[Link `lapse_im_eq_gap` → spacetime interval] The contour point's legs.** The spacetime interval
`lorentzianForm(N − iε) = N² − ε²` decomposes as `(timelike)² − (spacelike)²` with timelike leg `Re = N`
(`lapse_re_eq`) and **spacelike leg `Im = −ε`** (`lapse_im_eq_gap`): the non-Hermitian gap `ε` is the
spacelike direction of the spacetime interval, the single dissipative/entropic leg. -/
theorem lapse_interval_legs (N ε : ℝ) :
    lorentzianForm (complexEnergy N ε) = N ^ 2 - ε ^ 2
      ∧ (complexEnergy N ε).re = N
      ∧ (complexEnergy N ε).im = -ε :=
  ⟨lapse_lorentzianForm_eq N ε, lapse_re_eq N ε, lapse_im_eq_gap N ε⟩

/-- **[Link] The complex lapse is a contour point** `q = ω + iγ`. The Banihashemi–Jacobson complex lapse
`complexEnergy N ε = N − iε` is the unified contour point with real frequency `ω = N` (the lapse) and
damping `γ = −ε` (the `iε` regulator). -/
theorem complexLapse_eq_contourPoint (N ε : ℝ) :
    complexEnergy N ε = (N : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I := by
  unfold complexEnergy; push_cast; ring

/-- **[Link] The Nagao–Nielsen form of the complex lapse IS the Kozak-even dispersion.**
`lorentzianForm(complexEnergy N ε) = lorentzianDispersion ε N = N² − ε²`: the convergence-cone form of the
gravitational complex lapse is the Kozak even-parity dispersion in the lapse frequency `N`, with the lapse
contour displacement `ε` as the damping `γ`. -/
theorem lapse_lorentzianForm_eq_dispersion (N ε : ℝ) :
    lorentzianForm (complexEnergy N ε) = lorentzianDispersion ε N := by
  rw [lapse_lorentzianForm_eq, lorentzianDispersion_eq]

/-! ## §B — the real lapse contour (`ε = 0`) is the reversible fiber -/

/-- **The lapse weight is unimodular on the real contour** `‖lapseWeight N 0 ℋ‖ = 1` — at `ε = 0` there is
no `iε` displacement, so no entropic damping: the constraint integrand is a pure phase. -/
theorem lapse_real_modulus_one (N Ham : ℝ) : ‖lapseWeight N 0 Ham‖ = 1 := by
  rw [lapseWeight_modulus, kuikenWeight]; norm_num

/-- **[Main result link] The real lapse contour is the reversible fiber where all four structures agree.** On
the real lapse axis (`ε = 0`, the Nagao–Nielsen real axis = the Kozak real-frequency axis):

* the Nagao–Nielsen form is timelike, `lorentzianForm(complexEnergy N 0) = N² ≥ 0`;
* the Kozak dispersion is even (`FnEven`);
* the Bogoliubov entropic time vanishes, `τ_ent = 0`;
* the lapse weight is unimodular, `‖lapseWeight N 0 ℋ‖ = 1` (no entropic damping, `S_I = 0`).

This identifies the reversible fiber of `EntropicTime.NagaoKozakContourEntropicTime.real_contour_reversible` with the
reversible (zero imaginary-action) fiber of the Banihashemi–Jacobson lapse contour. -/
theorem lapse_real_contour_reversible (ξ N Ham : ℝ) (hξ : 0 < ξ) :
    0 ≤ lorentzianForm (complexEnergy N 0)
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0
      ∧ ‖lapseWeight N 0 Ham‖ = 1 := by
  refine ⟨?_, ?_, ?_, lapse_real_modulus_one N Ham⟩
  · rw [lapse_lorentzianForm_eq_dispersion]; exact lorentzianDispersion_real_nonneg N
  · exact lorentzianDispersion_fnEven 0
  · exact bogoliubov_entropicTime_normal_zero ξ hξ

/-! ## §C — turning on the contour displacement (`ε ≠ 0`) is irreversible -/

/-- **[Link] The contour displacement narrows the Nagao–Nielsen convergence cone.** For `ε ≠ 0` the
Nagao–Nielsen form of the complex lapse `N² − ε²` is strictly below its reversible value `N²`: switching on
the `iε` displacement moves the lapse off the timelike axis toward the spacelike (irreversible) region. -/
theorem lapse_cone_narrows (N ε : ℝ) (hε : ε ≠ 0) :
    lorentzianForm (complexEnergy N ε) < lorentzianForm (complexEnergy N 0) := by
  rw [lapse_lorentzianForm_eq, lapse_lorentzianForm_eq]
  have : 0 < ε ^ 2 := lt_of_le_of_ne (sq_nonneg ε) (Ne.symm (pow_ne_zero 2 hε))
  nlinarith

/-- **[Link] Off the real axis the lapse weight is sub-unimodular (irreversible).** For `ε, ℋ > 0` the
lapse weight modulus `‖lapseWeight N ε ℋ‖ = e^{−εℋ} < 1`: the `iε` contour displacement is the dissipative
direction — the Bogoliubov gap `Δ = γ`, the Kozak odd-absorption part — and it produces genuine entropic
damping (entropy production). -/
theorem lapse_irreversible_off_axis (N ε Ham : ℝ) (hε : 0 < ε) (hH : 0 < Ham) :
    ‖lapseWeight N ε Ham‖ < 1 := by
  rw [lapseWeight_modulus, kuikenWeight, div_one]
  calc Real.exp (-(ε * Ham)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
    _ = 1 := Real.exp_zero

end Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime

end
