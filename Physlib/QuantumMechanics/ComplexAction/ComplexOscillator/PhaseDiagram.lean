/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The phase diagram of the complex harmonic oscillator in `m` and `ω` (Nagao–Nielsen §3)

This file formalizes the **phase formalism** of the complex harmonic oscillator — Nagao–Nielsen
*Formalism of a harmonic oscillator in the future-included complex action theory*
(arXiv:1902.01424), §3.1–3.2 — extending `ComplexOscillator.ComplexHarmonicOscillatorBoson`. With complex
mass `m = r_m e^{iθ_m}` and complex frequency `ω = r_ω e^{iθ_ω}` (Eqs. 3.14–3.15), the
potential `V = ½ m ω² q²` (Eq. 3.18) decomposes (Eqs. 3.19–3.21) as `V = V_R + i V_I` with

  `V_R = ½ Re(mω²) q²`,  `V_I = ½ Im(mω²) q²`,

and in angular form (Eqs. 3.28–3.29), writing `φ = arg(mω²) = θ_m + 2θ_ω`,

  `V_R = ½ ‖mω²‖ cos φ · q²`,  `V_I = ½ ‖mω²‖ sin φ · q²`.

## Sensibility / convergence conditions (the phase-diagram boundaries)

* **Kinetic** (Eq. 3.22): `m_I = Im m ≥ 0` (`ComplexOscillator.ComplexHarmonicOscillatorBoson.oscillatorKineticConverges`,
  `0 ≤ θ_m ≤ π`).
* **Potential** (Eq. 3.23): `Im(mω²) ≤ 0`
  (`ComplexOscillator.ComplexHarmonicOscillatorBoson.oscillatorPotentialConverges`, `−π ≤ φ ≤ 0`), equivalent to
  `V_I ≤ 0` (`potentialConverges_iff_potentialIm_nonpos`).

## The phase classification (§3.2)

Inside the convergence wedge `φ = arg(mω²) ∈ [−π, 0]`, the sign of `V_R` (= sign of `Re(mω²)`)
classifies the oscillator:

* **Harmonic oscillator (HO)** — `Re(mω²) > 0` (restoring potential, `V_R > 0`).
* **Inverted harmonic oscillator (IHO)** — `Re(mω²) < 0` (`V_R < 0`).

The two boundary regions of the wedge (Nagao–Nielsen's regions 1 and 5):

* `phase_region_HO_boundary` — `φ = 0`: `V_I = 0`, `V_R > 0` (a pure HO);
* `phase_region_IHO_boundary` — `φ = π` (`= −π`): `V_I = 0`, `V_R < 0` (a pure IHO).

(The interior `−π < φ < 0` has `V_I < 0`: genuinely complex, dissipative potentials.)

## References

* K. Nagao, H. B. Nielsen, arXiv:1902.01424, §3.1–3.2 (Eqs. 3.14–3.29), Fig. 3 (phase diagram).
* `ComplexOscillator.ComplexHarmonicOscillatorBoson` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram

/-! ## §A — the complex potential and its real/imaginary parts (Eqs. 3.18–3.21) -/

/-- **The complex oscillator potential** `V = ½ m ω² q²` (Nagao–Nielsen Eq. 3.18). -/
def oscillatorPotential (m ω q : ℂ) : ℂ := (1 / 2) * m * ω ^ 2 * q ^ 2

/-- **The real potential** `V_R = ½ Re(mω²) q²` (Eq. 3.20). -/
def oscillatorPotentialRe (m ω : ℂ) (q : ℝ) : ℝ := (1 / 2) * (m * ω ^ 2).re * q ^ 2

/-- **The imaginary potential** `V_I = ½ Im(mω²) q²` (Eq. 3.21). -/
def oscillatorPotentialIm (m ω : ℂ) (q : ℝ) : ℝ := (1 / 2) * (m * ω ^ 2).im * q ^ 2

/-- **The potential decomposes as `V = V_R + i V_I`** (Eq. 3.19), for real `q`. -/
theorem oscillatorPotential_decompose (m ω : ℂ) (q : ℝ) :
    oscillatorPotential m ω (q : ℂ)
      = (oscillatorPotentialRe m ω q : ℂ) + (oscillatorPotentialIm m ω q : ℂ) * Complex.I := by
  have h1 : oscillatorPotential m ω (q : ℂ) = ((q ^ 2 / 2 : ℝ) : ℂ) * (m * ω ^ 2) := by
    unfold oscillatorPotential; push_cast; ring
  rw [h1]
  conv_lhs => rw [← Complex.re_add_im (m * ω ^ 2)]
  unfold oscillatorPotentialRe oscillatorPotentialIm
  push_cast
  ring

/-! ## §B — the angular form (Eqs. 3.28–3.29): `φ = arg(mω²) = θ_m + 2θ_ω` -/

/-- **`V_R = ½ ‖mω²‖ cos φ · q²`** with `φ = arg(mω²)` (Nagao–Nielsen Eq. 3.28). -/
theorem oscillatorPotentialRe_eq_arg (m ω : ℂ) (q : ℝ) :
    oscillatorPotentialRe m ω q
      = (1 / 2) * (‖m * ω ^ 2‖ * Real.cos (Complex.arg (m * ω ^ 2))) * q ^ 2 := by
  unfold oscillatorPotentialRe
  rw [Complex.norm_mul_cos_arg]

/-- **`V_I = ½ ‖mω²‖ sin φ · q²`** with `φ = arg(mω²)` (Nagao–Nielsen Eq. 3.29). -/
theorem oscillatorPotentialIm_eq_arg (m ω : ℂ) (q : ℝ) :
    oscillatorPotentialIm m ω q
      = (1 / 2) * (‖m * ω ^ 2‖ * Real.sin (Complex.arg (m * ω ^ 2))) * q ^ 2 := by
  unfold oscillatorPotentialIm
  rw [Complex.norm_mul_sin_arg]

/-! ## §C — convergence conditions (Eqs. 3.22–3.23) -/

/-- **Potential convergence ⟺ `V_I ≤ 0`** (Eq. 3.23): the sensibility condition
`Im(mω²) ≤ 0` is exactly non-positivity of the imaginary potential (for `q ≠ 0`). -/
theorem potentialConverges_iff_potentialIm_nonpos (m ω : ℂ) {q : ℝ} (hq : q ≠ 0) :
    oscillatorPotentialConverges m ω ↔ oscillatorPotentialIm m ω q ≤ 0 := by
  unfold oscillatorPotentialConverges oscillatorPotentialIm
  have hq2 : (0 : ℝ) < q ^ 2 := by positivity
  constructor
  · intro h; nlinarith [hq2, h]
  · intro h; nlinarith [hq2, h]

/-! ## §D — the phase classification: HO vs IHO and the boundary regions (§3.2) -/

/-- **Harmonic oscillator (HO)**: a restoring potential, `Re(mω²) > 0`. -/
def IsHarmonicOscillator (m ω : ℂ) : Prop := 0 < (m * ω ^ 2).re

/-- **Inverted harmonic oscillator (IHO)**: an expelling potential, `Re(mω²) < 0`. -/
def IsInvertedHarmonicOscillator (m ω : ℂ) : Prop := (m * ω ^ 2).re < 0

/-- **HO ⟺ `V_R > 0`** (restoring potential, for `q ≠ 0`). -/
theorem isHO_iff_potentialRe_pos (m ω : ℂ) {q : ℝ} (hq : q ≠ 0) :
    IsHarmonicOscillator m ω ↔ 0 < oscillatorPotentialRe m ω q := by
  unfold IsHarmonicOscillator oscillatorPotentialRe
  have hq2 : (0 : ℝ) < q ^ 2 := by positivity
  constructor
  · intro h; nlinarith [hq2, h]
  · intro h; nlinarith [hq2, h]

/-- **IHO ⟺ `V_R < 0`** (expelling potential, for `q ≠ 0`). -/
theorem isIHO_iff_potentialRe_neg (m ω : ℂ) {q : ℝ} (hq : q ≠ 0) :
    IsInvertedHarmonicOscillator m ω ↔ oscillatorPotentialRe m ω q < 0 := by
  unfold IsInvertedHarmonicOscillator oscillatorPotentialRe
  have hq2 : (0 : ℝ) < q ^ 2 := by positivity
  constructor
  · intro h; nlinarith [hq2, h]
  · intro h; nlinarith [hq2, h]

/-- **Boundary region 1 (`φ = arg(mω²) = 0`)**: `V_I = 0` and `V_R > 0` — a pure harmonic
oscillator on the real-positive potential axis (`mω² ≠ 0`). -/
theorem phase_region_HO_boundary (m ω : ℂ) (hz : m * ω ^ 2 ≠ 0)
    (h : Complex.arg (m * ω ^ 2) = 0) :
    (m * ω ^ 2).im = 0 ∧ 0 < (m * ω ^ 2).re := by
  rw [Complex.arg_eq_zero_iff] at h
  refine ⟨h.2, h.1.lt_of_ne fun heq => hz ?_⟩
  simp only [Complex.ext_iff, Complex.zero_re, Complex.zero_im]
  exact ⟨heq.symm, h.2⟩

/-- **Boundary region 5 (`φ = arg(mω²) = π = −π`)**: `V_I = 0` and `V_R < 0` — a pure
inverted harmonic oscillator on the real-negative potential axis. -/
theorem phase_region_IHO_boundary (m ω : ℂ) (h : Complex.arg (m * ω ^ 2) = Real.pi) :
    (m * ω ^ 2).im = 0 ∧ (m * ω ^ 2).re < 0 := by
  rw [Complex.arg_eq_pi_iff] at h
  exact ⟨h.2, h.1⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram

end

end
