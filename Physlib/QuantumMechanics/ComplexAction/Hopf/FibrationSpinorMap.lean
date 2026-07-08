/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism

/-!
# The spinor Hopf map as Stokes/Poincare coordinates

This file formalizes the proof-ready core of the Hopf-fibration material in the tau notes:
the standard map from a two-component spinor to its Bloch/Poincare-sphere base point.

For a spinor `χ : ℂ²`, the Hopf base coordinates are the Pauli/Stokes expectation values

`(S₁, S₂, S₃) = (χ†σ₁χ, χ†σ₂χ, χ†σ₃χ)`.

The already-proven Stokes identity gives the sphere equation

`S₁² + S₂² + S₃² = S₀²`,

where `S₀ = χ†χ` is the intensity. The genuinely Hopf-fibration statement added here is the
`S¹` fiber invariance: multiplying the spinor by any unit complex phase `u` with
`u†u = 1` leaves the base point unchanged. Thus the base depends on the ray/fiber class of
the spinor, not on its global phase.

This is the standard, non-speculative part of the tau Hopf-fibration notes:

* `hopfBase` is the Bloch/Poincare base point.
* `hopfBase_lies_on_poincare_sphere` proves the image lies on the sphere.
* `hopfBase_phase_invariant` proves the `S¹` fiber phase is quotient data.

No smooth principal-bundle, connection-form, curvature, or Dirac-monopole infrastructure is
claimed here; those require additional manifold/differential-form development.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap

open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism

/-! ## §A — the Hopf base coordinates -/

/-- **The Hopf base point** of a two-spinor: the three Pauli/Stokes expectation values
`(S₁,S₂,S₃) = (χ†σ₁χ, χ†σ₂χ, χ†σ₃χ)`. This is the Bloch/Poincare-sphere image of the spinor. -/
noncomputable def hopfBase (χ : Fin 2 → ℂ) : Fin 3 → ℂ :=
  fun i => stokesS (Sum.inr i) χ

/-- **The Hopf intensity** `S₀ = χ†χ`, the radius of the Poincare sphere. -/
noncomputable def hopfIntensity (χ : Fin 2 → ℂ) : ℂ :=
  stokesS (Sum.inl 0) χ

/-- **[Hopf image lies on the Poincare sphere]**
`S₁² + S₂² + S₃² = S₀²`. This is exactly the Stokes-spinor sphere theorem,
read as the base-space equation of the spinor Hopf map. -/
theorem hopfBase_lies_on_poincare_sphere (χ : Fin 2 → ℂ) :
    hopfBase χ 0 ^ 2 + hopfBase χ 1 ^ 2 + hopfBase χ 2 ^ 2 = hopfIntensity χ ^ 2 :=
  poincare_sphere χ

/-! ## §B — the `S¹` fiber action is invisible on the base -/

/-- **Global phase rotation** of a two-spinor by a complex phase `u`. When `u†u = 1`, this is the
usual `S¹` fiber action of the Hopf fibration. -/
def phaseRotate (u : ℂ) (χ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => u * χ i

lemma unitPhase_cancel (u z : ℂ) (hu : star u * u = 1) : star u * (u * z) = z := by
  rw [← mul_assoc, hu, one_mul]

lemma phaseRotate_stokesS0 (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    stokesS (Sum.inl 0) (phaseRotate u χ) = stokesS (Sum.inl 0) χ := by
  rw [stokesS0_apply, stokesS0_apply]
  simp only [phaseRotate, star_mul, mul_assoc]
  rw [unitPhase_cancel u (χ 0) hu, unitPhase_cancel u (χ 1) hu]

lemma phaseRotate_stokesS1 (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    stokesS (Sum.inr 0) (phaseRotate u χ) = stokesS (Sum.inr 0) χ := by
  rw [stokesS1_apply, stokesS1_apply]
  simp only [phaseRotate, star_mul, mul_assoc]
  rw [unitPhase_cancel u (χ 1) hu, unitPhase_cancel u (χ 0) hu]

lemma phaseRotate_stokesS2 (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    stokesS (Sum.inr 1) (phaseRotate u χ) = stokesS (Sum.inr 1) χ := by
  rw [stokesS2_apply, stokesS2_apply]
  simp only [phaseRotate, star_mul, mul_assoc]
  rw [unitPhase_cancel u (χ 0) hu, unitPhase_cancel u (χ 1) hu]

lemma phaseRotate_stokesS3 (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    stokesS (Sum.inr 2) (phaseRotate u χ) = stokesS (Sum.inr 2) χ := by
  rw [stokesS3_apply, stokesS3_apply]
  simp only [phaseRotate, star_mul, mul_assoc]
  rw [unitPhase_cancel u (χ 0) hu, unitPhase_cancel u (χ 1) hu]

/-- **[The Hopf base is invariant under the `S¹` fiber phase]**. Multiplying a spinor by any
unit complex phase `u` (`u†u = 1`) leaves the Bloch/Poincare base point `(S₁,S₂,S₃)`
unchanged. This is the algebraic content of the Hopf quotient
`S¹ ↪ S³ → S²`: the global phase is fiber data, not base data. -/
theorem hopfBase_phase_invariant (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    hopfBase (phaseRotate u χ) = hopfBase χ := by
  ext i
  fin_cases i
  · exact phaseRotate_stokesS1 u χ hu
  · exact phaseRotate_stokesS2 u χ hu
  · exact phaseRotate_stokesS3 u χ hu

/-- **[The Hopf intensity is also phase-invariant]**. The sphere radius `S₀ = χ†χ` is unchanged by
the same unit `S¹` fiber phase. -/
theorem hopfIntensity_phase_invariant (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    hopfIntensity (phaseRotate u χ) = hopfIntensity χ :=
  phaseRotate_stokesS0 u χ hu

/-- **[The Hopf fibration core, assembled]**. A unit global phase preserves both the base point and the
Poincare-sphere equation for the phase-rotated spinor. -/
theorem spinor_hopf_fibration_core (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    hopfBase (phaseRotate u χ) = hopfBase χ
      ∧ hopfIntensity (phaseRotate u χ) = hopfIntensity χ
      ∧ hopfBase (phaseRotate u χ) 0 ^ 2
          + hopfBase (phaseRotate u χ) 1 ^ 2
          + hopfBase (phaseRotate u χ) 2 ^ 2
        = hopfIntensity (phaseRotate u χ) ^ 2 :=
  ⟨hopfBase_phase_invariant u χ hu, hopfIntensity_phase_invariant u χ hu,
    hopfBase_lies_on_poincare_sphere (phaseRotate u χ)⟩

end Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap

end
