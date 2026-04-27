/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
/-!

# Harmonic Wave

Time-harmonic waves.

Note TODO `EGU3E` may require considerable effort to be made rigorous and may heavily depend on
the status of Fourier theory in Mathlib.

-/

@[expose] public section

namespace ClassicalMechanics
open Space

/-- The wavevector which indicates a direction and has magnitude `2π/λ`. -/
abbrev WaveVector (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

/-- Direction of a wavevector. -/
noncomputable def WaveVector.toDirection {d : ℕ} (k : WaveVector d) (h : k ≠ 0) :
    Direction d where
  unit := (‖k‖⁻¹) • basis.repr.symm (k)
  norm := by
    simp [norm_smul]
    field_simp

/-- General form of time-harmonic wave in terms of angular frequency `ω` and wave vector `k`. -/
noncomputable def harmonicWave (a g : ℝ → Space d → ℝ) (ω : WaveVector d → ℝ) (k : WaveVector d) :
    Time → Space d → ℝ :=
    fun t r => a (ω k) r * Real.cos (ω k * t - g (ω k) r)

TODO "EGQUA" "In `Physlib/ClassicalMechanics/WaveEquation/HarmonicWave.lean`, show that the
  classical wave equation on `Space d` is invariant under rotations, so that for a single
  harmonic plane wave any propagation direction `s : Direction d` can be rotated to the
  canonical direction `EuclideanSpace.single 2 1` used by `transverseHarmonicPlaneWave`."
open InnerProductSpace
set_option linter.unusedVariables false in
/-- Transverse monochromatic time-harmonic plane wave where the direction of propagation
  is taken to be `EuclideanSpace.single 2 1`. `f₀x` and `f₀y` are the respective amplitudes,
  `ω` is the angular frequency, `δx` and `δy` are the respective phases for `fx` and `fy`. -/
@[nolint unusedArguments]
noncomputable def transverseHarmonicPlaneWave (k : WaveVector) (f₀x f₀y ω δx δy : ℝ)
    (hk : k = EuclideanSpace.single 2 (ω/c)) :
    Time → Space → EuclideanSpace ℝ (Fin 3) :=
    let fx := harmonicWave (fun _ _ => f₀x) (fun _ r => ⟪k, basis.repr r⟫_ℝ - δx) (fun _ => ω) k
    let fy := harmonicWave (fun _ _ => f₀y) (fun _ r => ⟪k, basis.repr r⟫_ℝ - δy) (fun _ => ω) k
    fun t r => fx t r • EuclideanSpace.single 0 1 + fy t r • EuclideanSpace.single 1 1

set_option backward.isDefEq.respectTransparency false in
/-- The transverse harmonic planewave representation is equivalent to the general planewave
  expression with `‖k‖ = ω/c`. -/
lemma transverseHarmonicPlaneWave_eq_planeWave {c : ℝ} {k : WaveVector} {f₀x f₀y ω δx δy : ℝ}
    (hc_ge_zero : 0 < c) (hω_ge_zero : 0 < ω) (hk : k = EuclideanSpace.single 2 (ω/c)) :
    (transverseHarmonicPlaneWave k f₀x f₀y ω δx δy hk) = planeWave
    (fun p => (f₀x * Real.cos (-(ω/c)*p + δx)) • (EuclideanSpace.single 0 1) +
    (f₀y * Real.cos (-(ω/c)*p + δy)) • (EuclideanSpace.single 1 1)) c
    (WaveVector.toDirection k (by rw [hk]; simp [ne_of_gt, hc_ge_zero, hω_ge_zero])) := by
  unfold transverseHarmonicPlaneWave planeWave
  ext1 t
  ext1 r
  rw [harmonicWave, harmonicWave, WaveVector.toDirection]
  simp only [Fin.isValue, neg_mul]
  have normk: ‖k‖ = ω/c := by
    rw [hk]
    simp [← abs_div, hc_ge_zero, hω_ge_zero, le_of_lt]
  rw [normk]
  rw [mul_sub, inner_smul_right, real_inner_comm, ← mul_assoc]
  ring_nf
  simp [ne_of_gt, hc_ge_zero, hω_ge_zero, mul_comm ω, mul_assoc, basis_repr_inner_eq]

TODO "EGU3E" "In `Physlib/ClassicalMechanics/WaveEquation/HarmonicWave.lean`, show that any
  disturbance (subject to suitable regularity/integrability conditions) can be expressed as a
  superposition of `harmonicWave`s via the Fourier integral. This may require considerable
  effort to be made rigorous and may heavily depend on the status of Fourier theory in
  Mathlib."

end ClassicalMechanics
