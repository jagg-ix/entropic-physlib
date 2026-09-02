/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry

/-!
# Schrödinger phase covariance under parabolic rescaling

This module completes the phase-level parabolic-rescaling calculation from
Jonathan Hickman's exposition of the Du--Zhang theorem (arXiv:2304.02507,
§3.3).  It proves both the real phase identity and the factorization of the
complex oscillatory kernel.  The time-only specialization is connected to the
existing `freeSchrodingerPhase` used by Physlib's genuine `L²(ℝⁿ)` evolution.

No change-of-variables theorem for the full oscillatory integral is asserted;
that later analytic step additionally needs a Fourier dilation operator and
support/Jacobian bookkeeping.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling

open EuclideanL2FreeEvolution SchrodingerParabolicGeometry

/-- Physical space--time, represented as `(x,t)`. -/
abbrev EuclideanSpaceTime (n : ℕ) := EuclideanFrequency n × ℝ

/-! ## 1. The real Schrödinger phase -/

/-- The paper's free Schrödinger phase
`φ((x,t);ξ) = ⟪x,ξ⟫ + t‖ξ‖²`. -/
def schrodingerPhase {n : ℕ} (z : EuclideanSpaceTime n)
    (ξ : EuclideanFrequency n) : ℝ :=
  inner ℝ z.1 ξ + z.2 * ‖ξ‖ ^ 2

/-- The centre-frequency phase factored out by parabolic rescaling. -/
def centrePhase {n : ℕ} (z : EuclideanSpaceTime n)
    (centre : EuclideanFrequency n) : ℝ :=
  schrodingerPhase z centre

/-- The dual space--time rescaling
`(x,t) ↦ (r x + 2rt centre, r²t)`. -/
def parabolicSpaceTimeRescale {n : ℕ}
    (centre : EuclideanFrequency n) (radius : ℝ)
    (z : EuclideanSpaceTime n) : EuclideanSpaceTime n :=
  (radius • z.1 + (2 * radius * z.2) • centre,
    radius ^ 2 * z.2)

/-- The exact phase covariance used in the paper's parabolic-rescaling
argument. -/
lemma schrodingerPhase_frequencyRescale {n : ℕ}
    (z : EuclideanSpaceTime n) (centre : EuclideanFrequency n)
    (radius : ℝ) (η : EuclideanFrequency n) :
    schrodingerPhase z (frequencyRescale centre radius η) =
      centrePhase z centre +
        schrodingerPhase (parabolicSpaceTimeRescale centre radius z) η := by
  simp only [schrodingerPhase, centrePhase, frequencyRescale,
    parabolicSpaceTimeRescale, inner_add_right, real_inner_smul_right,
    inner_add_left, real_inner_smul_left, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

/-! ## 2. The complex oscillatory kernel -/

/-- The unit complex oscillatory kernel `exp(i φ(z;ξ))`. -/
def schrodingerOscillatoryPhase {n : ℕ} (z : EuclideanSpaceTime n)
    (ξ : EuclideanFrequency n) : ℂ :=
  Complex.exp (Complex.I * Complex.ofReal (schrodingerPhase z ξ))

@[simp] lemma norm_schrodingerOscillatoryPhase {n : ℕ}
    (z : EuclideanSpaceTime n) (ξ : EuclideanFrequency n) :
    ‖schrodingerOscillatoryPhase z ξ‖ = 1 := by
  rw [schrodingerOscillatoryPhase, Complex.norm_exp]
  simp

/-- Parabolic rescaling factorizes the complex oscillatory kernel into the
centre-frequency phase and the rescaled unit-frequency phase. -/
lemma schrodingerOscillatoryPhase_frequencyRescale {n : ℕ}
    (z : EuclideanSpaceTime n) (centre : EuclideanFrequency n)
    (radius : ℝ) (η : EuclideanFrequency n) :
    schrodingerOscillatoryPhase z (frequencyRescale centre radius η) =
      schrodingerOscillatoryPhase z centre *
        schrodingerOscillatoryPhase
          (parabolicSpaceTimeRescale centre radius z) η := by
  unfold schrodingerOscillatoryPhase
  rw [schrodingerPhase_frequencyRescale, Complex.ofReal_add, mul_add,
    Complex.exp_add]
  rfl

/-! ## 3. Connection to the existing `L²` propagator -/

/-- At zero spatial position, the oscillatory phase is exactly the frequency
multiplier already used to define `freeSchrodingerEvolution`. -/
lemma schrodingerOscillatoryPhase_zeroSpace_eq_freeSchrodingerPhase {n : ℕ}
    (t : ℝ) (ξ : EuclideanFrequency n) :
    schrodingerOscillatoryPhase (0, t) ξ =
      freeSchrodingerPhase t ξ := by
  simp [schrodingerOscillatoryPhase, schrodingerPhase,
    freeSchrodingerPhase]

/-! ## 4. Phase-rescaling capstone -/

/-- Target-two capstone: the real phase, unit complex oscillatory kernel, and
existing free `L²` multiplier are compatible with the paper's parabolic
rescaling. -/
lemma schrodingerPhase_parabolicRescaling_chain {n : ℕ}
    (z : EuclideanSpaceTime n) (centre : EuclideanFrequency n)
    (radius : ℝ) (η : EuclideanFrequency n) :
    schrodingerPhase z (frequencyRescale centre radius η) =
      centrePhase z centre +
        schrodingerPhase (parabolicSpaceTimeRescale centre radius z) η ∧
    schrodingerOscillatoryPhase z (frequencyRescale centre radius η) =
      schrodingerOscillatoryPhase z centre *
        schrodingerOscillatoryPhase
          (parabolicSpaceTimeRescale centre radius z) η ∧
    ‖schrodingerOscillatoryPhase
      (parabolicSpaceTimeRescale centre radius z) η‖ = 1 := by
  exact ⟨schrodingerPhase_frequencyRescale z centre radius η,
    schrodingerOscillatoryPhase_frequencyRescale z centre radius η,
    norm_schrodingerOscillatoryPhase _ _⟩

end Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling
