/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-!
# Sorkin Fig. 2 (boost versus rotation) and the Nagao–Nielsen contour

Sorkin (1975) Fig. 2(e) contrasts the two bone circulators: a **rotation** (timelike bone, defect
angle `θ`) turns the two transverse axes in the *same* sense, while a **boost** (spacelike bone,
rapidity `η`) turns them in *opposite* senses. Algebraically the rotation is orthogonal
(`Rᵀ R = 1`, the compact `SO(2)`) and the boost is symmetric (`Bᵀ = B`, the non-compact `SO(1,1)`).

The two are the same transformation continued along the **Nagao–Nielsen (Wick) contour** `θ → iη`
(`QFT.PathIntegral.wickRotateInv`): `cos(iη) = cosh η`, `sin(iη) = i·sinh η`, so the boost's
`cosh`/`sinh` are the rotation's `cos`/`sin` at imaginary angle. Along this contour the Nagao–Kozak
Wick rotation flips the Lorentzian form (`wick_flips_lorentzian`), taking a timelike bone
(`t²−z² > 0`, rotation) to a spacelike bone (`< 0`, boost) — the analytic-continuation content of
Fig. 2.

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`], Sec. II B and **Fig. 2(e)** (boost versus rotation), Appendix B (the defect
  of a spacelike bone as a complex angle `θ = iη`). Reuses `LeviCivita.TetradInvariant`
  (`planeRotation`, `planeBoost`), `QFT.PathIntegral.WickClock` (`wickRotateInv`),
  `EntropicTime.NagaoKozakContourEntropicTime` (`wick_flips_lorentzian`),
  `ComplexDelta.Convergence` (`lorentzianForm`).

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.BoostRotationWickContour

open Matrix
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-! ## Fig. 2(e) — a rotation turns the axes together, a boost turns them oppositely -/

/-- **A rotation is orthogonal** (`Rᵀ R = 1`): the timelike-bone circulator is a compact `SO(2)`
transformation preserving the transverse Euclidean form `x² + y²` — it turns the two axes in the
same sense. -/
theorem planeRotation_orthogonal (θ : ℝ) : (planeRotation θ)ᵀ * planeRotation θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **A boost is symmetric** (`Bᵀ = B`): the spacelike-bone circulator is a non-compact `SO(1,1)`
transformation — not orthogonal, self-transpose — turning the two axes in opposite senses. This is
the boost-versus-rotation distinction of Fig. 2(e). -/
theorem planeBoost_symmetric (η : ℝ) : (planeBoost η)ᵀ = planeBoost η := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [planeBoost, Matrix.transpose_apply]

/-! ## The Nagao–Nielsen contour `θ → iη` continues the rotation into the boost -/

/-- **`cos(iη) = cosh η`**: the boost's `cosh` is the rotation's `cos` continued along the
Nagao–Nielsen Wick contour `wickRotateInv η = i η`. -/
theorem boost_cosh_eq_rotation_wick (η : ℝ) :
    Complex.cos (wickRotateInv η) = (Real.cosh η : ℂ) := by
  unfold wickRotateInv; rw [mul_comm, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- **`sin(iη) = i·sinh η`**: the boost's `sinh` is the rotation's `sin` continued along the
Nagao–Nielsen Wick contour. -/
theorem boost_sinh_eq_rotation_wick (η : ℝ) :
    Complex.sin (wickRotateInv η) = Complex.I * (Real.sinh η : ℂ) := by
  unfold wickRotateInv; rw [mul_comm, Complex.sin_mul_I, ← Complex.ofReal_sinh, mul_comm]

/-- **A timelike bone Wick-rotates to a spacelike bone**: along the Nagao–Kozak contour the Wick
rotation `q ↦ i q` flips the Lorentzian form (`wick_flips_lorentzian`), so a timelike separation
(`t² − z² > 0`, the rotation/`θ` regime) becomes spacelike (`< 0`, the boost/`η` regime) — Fig. 2's
boost-versus-rotation as analytic continuation. -/
theorem timelike_wick_to_spacelike (q : ℂ) (h : 0 < lorentzianForm q) :
    lorentzianForm (Complex.I * q) < 0 := by
  rw [wick_flips_lorentzian]; linarith

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.BoostRotationWickContour
