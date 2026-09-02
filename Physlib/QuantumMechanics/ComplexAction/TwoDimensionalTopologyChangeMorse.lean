/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange
public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

/-!
# The Morse-metric derivation of the topology-change strengths, and the contours

`TwoDimensionalTopologyChange` took the complex delta-function strengths `β − 2πi` (yarmulke) and
`2πi` (trousers) as input. This module supplies the Morse-metric derivation (Louko–Sorkin §2) and
links it to the **Nagao–Nielsen** (Wick) and **Witten** analytic-continuation contours.

Louko–Sorkin build the metric from a Morse function `f = ½(x² + εy²)` and a regulator `γ`:
`ds² = (x² + εy² + γ)(dx² + dy²) − ζ(x dx + εy dy)²` (Eq. 2.3), `ζ > 1` for Lorentzian signature.

* **§A — the Euclidean cone** (`ε = 1`, `ζ < 1`, real `γ`). The metric is a cone `ds² = ¼(1−ζ)dr²
  + r²dφ²` (Eq. 2.5) of **defect angle** `coneDefectAngle ζ = 2π(1 − 2/√(1−ζ))`; the regularized
  density `½√g R → (coneDefectAngle) δ₂` (Eq. 2.12). It is **flat iff `ζ = −3`**
  (`coneDefectAngle_flat_iff`); `√g R` has strength `2·` the defect (the abstract's "twice the defect
  angle", `ricciDensityDeltaStrength`).
* **§B — the Nagao–Nielsen (Wick) contour** to the Lorentzian yarmulke (`ζ > 1`). The defect argument
  continues `√(1−ζ) = i√(ζ−1)` (`defect_wick_continuation`); the regulator becomes imaginary
  `γ = iσ = wickRotateInv σ` (`imaginaryRegulator_eq_nagaoNielsen`); the `(++)` signature flips to
  `(−+)` (`euclidean_to_lorentzian_signature_flip`, reusing `wick_flips_lorentzian`).
* **§C — the Misner rapidity and the complex strength.** The `φ ~ φ + 2π` periodicity becomes a boost
  of rapidity `misnerRapidity ζ = 4π/√(ζ−1)` (Eq. 2.13). The Wick-continued defect angle is exactly
  `i` times the Louko–Sorkin **yarmulke strength** `β − 2πi` with `β = misnerRapidity`
  (`lorentzianDefectStrength_eq_wick_yarmulke`) — closing the derivation, the factor `i` being the
  `exp(iS)` rotation.
* **§D — the Witten allowability.** The regulator sign is fixed by path-integral convergence — the
  analytic-continuation prescription of Witten (steepest-descent/Lefschetz contours,
  `WittenAnalyticContinuationChernSimons`): the trousers amplitude sits on the convergent (allowable)
  side, modulus `< 1` (`trousers_on_allowable_contour`, reusing `trousers_suppressed`).

**Honest layering.** Proven: the cone flat-condition, the Wick continuation of the defect and the
regulator, the signature flip, and the identity of the continued defect with `i·(β − 2πi)`.
Interpretive: the distributional limit `½√g R → (coneDefectAngle) δ₂` (Eqs. 2.6–2.12) is Louko–
Sorkin's analysis, encoded here as `coneDefectAngle` rather than re-derived as a distribution.

## References

* J. Louko, R. D. Sorkin, "Complex actions in two-dimensional topology change", Class. Quantum Grav.
  **14**, 179 (1997) [`Louko:1995jw`], §2, Eqs. (2.2)–(2.16). E. Witten, "Analytic Continuation of
  Chern–Simons Theory", arXiv:1001.2933 (the allowable/steepest-descent contour). Reuses
  `TwoDimensionalTopologyChange` (`yarmulkeStrength`, `trousers_suppressed`),
  `QFT.PathIntegral.WickClock` (`wickRotateInv`), `EntropicTime.NagaoKozakContourEntropicTime`
  (`wick_flips_lorentzian`).


-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChangeMorse


/-- **The Morse function** `f = ½(x² + εy²)` (Louko–Sorkin Eq. 2.2), `ε = ±1` the Morse index; its
critical point at the origin is the locus of metric degeneration. -/
noncomputable def morseFunction (ε x y : ℝ) : ℝ := (x ^ 2 + ε * y ^ 2) / 2

/-- The Morse function vanishes at its critical point (the degeneracy locus) `x = y = 0`. -/
@[simp] lemma morseFunction_origin (ε : ℝ) : morseFunction ε 0 0 = 0 := by
  simp [morseFunction]

/-- **The Euclidean cone defect angle** `2π(1 − 2/√(1−ζ))` (Louko–Sorkin Eqs. 2.5, 2.12): the
coefficient of `δ₂` in the regularized density `½√g R` at the conical singularity. -/
noncomputable def coneDefectAngle (ζ : ℝ) : ℝ := 2 * Real.pi * (1 - 2 / Real.sqrt (1 - ζ))

/-- **The Ricci-density delta strength `= 2·` the defect angle** — the abstract's statement that
`√g R` has a delta-function of strength twice the defect (`½√g R` carries the defect itself). -/
noncomputable def ricciDensityDeltaStrength (ζ : ℝ) : ℝ := 2 * coneDefectAngle ζ

/-- **The cone is flat iff `ζ = −3`**: the defect angle vanishes precisely at `ζ = −3`
(Louko–Sorkin, note after Eq. 2.5). -/
lemma coneDefectAngle_flat_iff (ζ : ℝ) (hζ : ζ < 1) : coneDefectAngle ζ = 0 ↔ ζ = -3 := by
  have hpos : 0 < 1 - ζ := by linarith
  have hsqrt : 0 < Real.sqrt (1 - ζ) := Real.sqrt_pos.mpr hpos
  have hne : Real.sqrt (1 - ζ) ≠ 0 := ne_of_gt hsqrt
  unfold coneDefectAngle
  rw [mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · norm_num at h
    · exact absurd h Real.pi_ne_zero
    · have h2 : Real.sqrt (1 - ζ) = 2 := by
        have h1 : 2 / Real.sqrt (1 - ζ) = 1 := by linarith
        field_simp [hne] at h1; linarith
      have hsq := Real.sq_sqrt (le_of_lt hpos)
      rw [h2] at hsq; norm_num at hsq; linarith
  · intro h; subst h; right
    have : Real.sqrt (1 - (-3 : ℝ)) = 2 := by
      rw [show (1:ℝ) - -3 = 4 by norm_num, show (4:ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [this]; norm_num


/-- **The Wick continuation of the defect argument** `√(1−ζ) = i√(ζ−1)` for `ζ ≥ 1`: as `ζ` crosses
`1`, `1 − ζ` turns negative and its square root rotates by `i` — the Nagao–Nielsen `θ → iη`
continuation applied to the cone. -/
lemma defect_wick_continuation (ζ : ℝ) (hζ : 1 ≤ ζ) :
    (Complex.I * (Real.sqrt (ζ - 1) : ℂ)) ^ 2 = ((1 - ζ : ℝ) : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ ζ - 1)]
  push_cast; ring

/-- **The Lorentzian imaginary regulator is the Nagao–Nielsen contour point**: `γ = iσ = wickRotateInv
σ` (Louko–Sorkin take `γ = ±iσ` for the yarmulke, §2.2). -/
lemma imaginaryRegulator_eq_nagaoNielsen (σ : ℝ) :
    Complex.I * (σ : ℂ) = wickRotateInv σ := rfl

/-- **The Euclidean `(++)` signature flips to Lorentzian `(−+)`** along the contour: the Lorentzian
form negates under `q ↦ iq` (reusing `wick_flips_lorentzian`). -/
lemma euclidean_to_lorentzian_signature_flip (q : ℂ) :
    lorentzianForm (Complex.I * q) = - lorentzianForm q :=
  wick_flips_lorentzian q


/-- **The Misner boost rapidity** `4π/√(ζ−1)` (Louko–Sorkin Eq. 2.13): the `φ ~ φ + 2π` periodicity of
the cone becomes the identification of `T > |X|` Minkowski space by a boost of this rapidity. -/
noncomputable def misnerRapidity (ζ : ℝ) : ℝ := 4 * Real.pi / Real.sqrt (ζ - 1)

/-- **The Wick-continued Lorentzian defect strength** `2π(1 − 2/(i√(ζ−1)))` — the Euclidean
`coneDefectAngle` with `√(1−ζ)` replaced by the Nagao–Nielsen continuation `i√(ζ−1)`. -/
noncomputable def lorentzianDefectStrength (ζ : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * (1 - 2 / (Complex.I * (Real.sqrt (ζ - 1) : ℂ)))

/-- **The Morse derivation closes**: the Wick-continued Euclidean defect angle is exactly `i` times the
Louko–Sorkin **yarmulke strength** `β − 2πi`, with `β = misnerRapidity ζ` the Misner rapidity. The
factor `i` is the `exp(iS)` rotation: the Euclidean defect (a real curvature strength) becomes the
imaginary `−2π` of the yarmulke plus the real Misner rapidity. -/
lemma lorentzianDefectStrength_eq_wick_yarmulke (ζ : ℝ) (hζ : 1 < ζ) :
    lorentzianDefectStrength ζ = Complex.I * yarmulkeStrength (misnerRapidity ζ) := by
  have hs : (Real.sqrt (ζ - 1) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  unfold lorentzianDefectStrength yarmulkeStrength misnerRapidity
  rw [Complex.ofReal_div]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq, hI3]
  ring

/-- The yarmulke's imaginary strength `−2π` is the negative of the `2π` winding of `φ` (the loop
around the conical point), independent of the rapidity. -/
lemma yarmulke_imaginary_is_winding (ζ : ℝ) :
    (yarmulkeStrength (misnerRapidity ζ)).im = -(2 * Real.pi) :=
  yarmulkeStrength_im _


/-- **The trousers sit on the Witten-allowable (convergent) contour**: the regulator sign is fixed by
convergence of the path integral — Witten's analytic-continuation prescription — and the resulting
trousers amplitude has modulus `< 1` (reusing `trousers_suppressed`). -/
lemma trousers_on_allowable_contour (κ ℏ : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) :
    ‖cobordismWeight trousersStrength κ ℏ‖ < 1 :=
  trousers_suppressed κ ℏ hκ hℏ

end Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChangeMorse
