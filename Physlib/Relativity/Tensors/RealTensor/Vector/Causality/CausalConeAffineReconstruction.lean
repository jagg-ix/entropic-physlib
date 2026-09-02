/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeAffineIncidence
meta import Zil

/-!
# Unrestricted affine reconstruction from causal incidence

This file combines the null, spacelike, and timelike line-image theorems into preservation
of every nondegenerate affine line. The fundamental theorem of real affine geometry then
represents a bare causal automorphism by an affine equivalence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace
open Physlib.Mathematics.AffineCollineation

/-! # A. All affine lines -/

private lemma affineLine_swap (p q : Vector 3) :
    affineLine p (q - p) = affineLine q (p - q) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨1 - a, by module⟩
  · rintro ⟨a, rfl⟩
    exact ⟨1 - a, by module⟩

/-- **Unrestricted line preservation.** A bare causal automorphism of physical 3+1
Minkowski space maps every nondegenerate affine line exactly onto the line through the
images of its base point and unit parameter point, with no causal-character restriction
on the direction and no continuity or affine premise. -/
@[zil_level physical_theorem]
theorem affineLine_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p v : Vector 3} (hv0 : v ≠ 0) :
    φ '' affineLine p v = affineLine (φ p) (φ (p + v) - φ p) := by
  rcases lt_trichotomy ⟪v, v⟫ₘ 0 with hvSpace | hvNull | hvTime
  · exact spacelikeAffineLine_image_of_causalAutomorphism hφ hvSpace
  · by_cases ht : 0 ≤ timeComponent v
    · simpa only [nullAffineLine, affineLine] using
        nullAffineLine_image_of_causalAutomorphism hφ hvNull ht hv0
    · have hnegQ : ⟪-v, -v⟫ₘ = 0 := by simpa using hvNull
      have hnegT : 0 ≤ timeComponent (-v) := by
        change 0 ≤ -timeComponent v
        exact neg_nonneg.mpr (le_of_not_ge ht)
      have hsourceSwap : affineLine p v = affineLine (p + v) (-v) := by
        simpa using affineLine_swap p (p + v)
      have htargetSwap :
          affineLine (φ p) (φ (p + v) - φ p) =
            affineLine (φ (p + v)) (φ p - φ (p + v)) :=
        affineLine_swap (φ p) (φ (p + v))
      calc
        φ '' affineLine p v = φ '' affineLine (p + v) (-v) :=
          congrArg (Set.image φ) hsourceSwap
        _ = affineLine (φ (p + v)) (φ p - φ (p + v)) := by
          simpa only [nullAffineLine, affineLine, add_neg_cancel_right] using
            nullAffineLine_image_of_causalAutomorphism hφ (p := p + v)
              (n := -v) hnegQ hnegT (neg_ne_zero.mpr hv0)
        _ = affineLine (φ p) (φ (p + v) - φ p) := htargetSwap.symm
  · exact timelikeAffineLine_image_of_causalAutomorphism hφ hvTime

/-! # B. Fundamental real-affine reconstruction -/

private lemma vector3_has_independent_pair :
    ∃ u v : Vector 3, PairIndependent u v := by
  let e₀ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.basisFun (Fin 3) ℝ 0
  let u : Vector 3 := ofTemporalComponent 1
  let v : Vector 3 := ofSpatialComponent e₀
  refine ⟨u, v, ?_, ?_⟩
  · intro hu
    have ht := congrArg timeComponent hu
    simp [u, timeComponent_ofTemporalComponent] at ht
  · intro a hva
    have hs := congrArg (spatialCLM 3) hva
    rw [map_smul] at hs
    change spatialPart v = a • spatialPart u at hs
    have hs0 : e₀ = 0 := by
      simpa [u, v, spatialPart_ofTemporalComponent,
        spatialPart_ofSpatialComponent] using hs
    have hone := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) hs0
    simp [e₀] at hone

/-- Every bare causal automorphism of physical 3+1 Minkowski space is represented by a
real affine equivalence. This is the fundamental-theorem-of-affine-geometry output of the
complete null, spacelike, and timelike incidence reconstruction. -/
@[zil_level physical_theorem]
theorem exists_affineEquiv_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) :
    ∃ e : Vector 3 ≃ᵃ[ℝ] Vector 3, ∀ x, e x = φ x := by
  exact exists_affineEquiv_of_affineLine_images hφ.1 vector3_has_independent_pair
    (fun _ _ hv0 => affineLine_image_of_causalAutomorphism hφ hv0)

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach affineLine_image_of_causalAutomorphism where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:nullAffineLine_image_of_causalAutomorphism",
  formalizes @ "claim:a-bare-causal-automorphism-maps-every-nondegenerate-complete-\
affine-line-exactly-onto-the-line-through-its-image-endpoints",
  supported_by @ "lean:Lorentz.Vector.nullAffineLine_image_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.spacelikeAffineLine_image_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.timelikeAffineLine_image_of_causalAutomorphism"

zil attach exists_affineEquiv_of_causalAutomorphism where
  supported_by @ "lean:affineLine_image_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:every-bare-causal-automorphism-of-three-plus-one-minkowski-space-\
is-a-real-affine-equivalence",
  supported_by @ "lean:Lorentz.Vector.affineLine_image_of_causalAutomorphism",
  supported_by @ "lean:Physlib.Mathematics.AffineCollineation.\
exists_affineEquiv_of_affineLine_images"

/- ZIL-END -/
