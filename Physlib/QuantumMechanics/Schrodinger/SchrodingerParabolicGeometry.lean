/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution

/-!
# Parabolic rescaling geometry for free Schrödinger evolution

This module formalizes the geometric parabolic-rescaling lemma from Jonathan
Hickman's exposition of the Du--Zhang theorem (arXiv:2304.02507, §3.3).
The frequency paraboloid `Σ(ξ) = (ξ, ‖ξ‖²)` is preserved by the explicit
ambient affine shear/dilation attached to a frequency centre and nonzero
radius.  The restriction is proved bijective, rather than recorded merely as
an informal change of variables.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Set

namespace Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry

/-- Euclidean frequency space in dimension `n`. -/
abbrev EuclideanFrequency (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ambient frequency--temporal Fourier space. -/
abbrev ParabolicFrequency (n : ℕ) := EuclideanFrequency n × ℝ

/-! ## 1. The frequency paraboloid -/

/-- The standard Schrödinger paraboloid embedding `Σ(ξ) = (ξ, ‖ξ‖²)`. -/
def paraboloidPoint {n : ℕ} (ξ : EuclideanFrequency n) :
    ParabolicFrequency n :=
  (ξ, ‖ξ‖ ^ 2)

/-- The full frequency paraboloid as the range of `Σ`. -/
def frequencyParaboloid (n : ℕ) : Set (ParabolicFrequency n) :=
  Set.range paraboloidPoint

lemma paraboloidPoint_injective {n : ℕ} :
    Function.Injective (paraboloidPoint (n := n)) := by
  intro ξ η h
  exact congrArg Prod.fst h

/-! ## 2. Explicit affine rescaling -/

/-- The affine frequency change `η ↦ centre + radius • η`. -/
def frequencyRescale {n : ℕ} (centre : EuclideanFrequency n)
    (radius : ℝ) (η : EuclideanFrequency n) : EuclideanFrequency n :=
  centre + radius • η

/-- The ambient shear/dilation from the paper.  On `(η,τ)` it is
`(centre + rη, ‖centre‖² + 2r⟪centre,η⟫ + r²τ)`. -/
def parabolicAmbientRescale {n : ℕ} (centre : EuclideanFrequency n)
    (radius : ℝ) (ζ : ParabolicFrequency n) : ParabolicFrequency n :=
  (centre + radius • ζ.1,
    ‖centre‖ ^ 2 + 2 * radius * inner ℝ centre ζ.1 + radius ^ 2 * ζ.2)

/-- Nonzero affine frequency rescaling is an explicit equivalence. -/
def frequencyRescaleEquiv {n : ℕ} (centre : EuclideanFrequency n)
    (radius : ℝ) (hradius : radius ≠ 0) :
    EuclideanFrequency n ≃ EuclideanFrequency n where
  toFun := frequencyRescale centre radius
  invFun := fun ξ => radius⁻¹ • (ξ - centre)
  left_inv := by
    intro η
    simp [frequencyRescale, hradius]
  right_inv := by
    intro ξ
    simp [frequencyRescale, smul_smul, hradius]

/-- The ambient affine map sends each paraboloid point to the rescaled
paraboloid point.  This is equation (19) of the paper in typed form. -/
lemma parabolicAmbientRescale_paraboloidPoint {n : ℕ}
    (centre : EuclideanFrequency n) (radius : ℝ)
    (η : EuclideanFrequency n) :
    parabolicAmbientRescale centre radius (paraboloidPoint η) =
      paraboloidPoint (frequencyRescale centre radius η) := by
  ext
  · rfl
  · simp only [parabolicAmbientRescale, paraboloidPoint, frequencyRescale,
      norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_right]
    rw [mul_pow, sq_abs]
    ring

/-! ## 3. Bijection of the paraboloid -/

/-- For nonzero radius, the ambient affine shear/dilation restricts to a
bijection of the full paraboloid.  Restricting the frequency equivalence to a
unit ball gives the paper's cap-to-cap bijection. -/
lemma parabolicAmbientRescale_bijOn_frequencyParaboloid {n : ℕ}
    (centre : EuclideanFrequency n) {radius : ℝ} (hradius : radius ≠ 0) :
    Set.BijOn (parabolicAmbientRescale centre radius)
      (frequencyParaboloid n) (frequencyParaboloid n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨η, rfl⟩
    exact ⟨frequencyRescale centre radius η,
      (parabolicAmbientRescale_paraboloidPoint centre radius η).symm⟩
  · rintro _ ⟨η, rfl⟩ _ ⟨θ, rfl⟩ h
    have hfreq : frequencyRescale centre radius η =
        frequencyRescale centre radius θ :=
      paraboloidPoint_injective
        (by simpa only [parabolicAmbientRescale_paraboloidPoint] using h)
    exact congrArg paraboloidPoint
      ((frequencyRescaleEquiv centre radius hradius).injective hfreq)
  · rintro _ ⟨ξ, rfl⟩
    let η := (frequencyRescaleEquiv centre radius hradius).symm ξ
    refine ⟨paraboloidPoint η, ⟨η, rfl⟩, ?_⟩
    rw [parabolicAmbientRescale_paraboloidPoint]
    exact congrArg paraboloidPoint
      ((frequencyRescaleEquiv centre radius hradius).apply_symm_apply ξ)

/-! ## 4. Geometric capstone -/

/-- Target-one capstone: the explicit affine map realizes the paper's
paraboloid self-similarity and is bijective on the paraboloid. -/
lemma schrodingerParaboloid_affineSelfSimilarity {n : ℕ}
    (centre : EuclideanFrequency n) {radius : ℝ} (hradius : radius ≠ 0) :
    (∀ η, parabolicAmbientRescale centre radius (paraboloidPoint η) =
      paraboloidPoint (frequencyRescale centre radius η)) ∧
    Set.BijOn (parabolicAmbientRescale centre radius)
      (frequencyParaboloid n) (frequencyParaboloid n) := by
  exact ⟨parabolicAmbientRescale_paraboloidPoint centre radius,
    parabolicAmbientRescale_bijOn_frequencyParaboloid centre hradius⟩

end Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry
