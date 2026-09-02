/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.AffineCollineation
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLightRayPreservation
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
meta import Zil

/-!
# Affine incidence reconstructed from the Minkowski null cone

This file supplies the incidence-geometric stage between preservation of complete null
affine lines and the fundamental theorem of real affine geometry. Its first layer proves
that a causal automorphism preserves the tangent affine hyperplane along every null line.
The hyperplane is reconstructed from null incidence itself, rather than assumed as an
additional affine object.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace
open Physlib.Mathematics.AffineCollineation

/-! # A. Unoriented null incidence -/

private lemma minkowski_neg_self (v : Vector 3) : ⟪-v, -v⟫ₘ = ⟪v, v⟫ₘ := by
  rw [show -v = (-1 : ℝ) • v by simp]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- A bare causal automorphism of physical Minkowski space preserves null separation in
both directions. The proof orients each null displacement toward the future and applies
the order-theoretic light-cone-boundary characterization; no continuity or affine premise
is used. -/
@[zil_level physical_theorem]
theorem nullSeparation_iff_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) (p q : Vector 3) :
    ⟪φ q - φ p, φ q - φ p⟫ₘ = 0 ↔ ⟪q - p, q - p⟫ₘ = 0 := by
  constructor
  · intro hnull
    by_cases ht : 0 ≤ timeComponent (φ q - φ p)
    · have hboundary : φ q ∈ futureLightConeBoundary (φ p) :=
        ⟨(lightLike_iff_norm_sq_zero _).mpr hnull, ht⟩
      exact (lightLike_iff_norm_sq_zero _).mp
        ((futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p q).mp hboundary).1
    · have hboundary : φ p ∈ futureLightConeBoundary (φ q) := by
        refine ⟨(lightLike_iff_norm_sq_zero _).mpr ?_, ?_⟩
        · have hneg : ⟪-(φ q - φ p), -(φ q - φ p)⟫ₘ = 0 := by
            rw [minkowski_neg_self, hnull]
          rw [show φ p - φ q = -(φ q - φ p) by abel]
          exact hneg
        · rw [show φ p - φ q = -(φ q - φ p) by abel]
          change 0 ≤ -timeComponent (φ q - φ p)
          exact neg_nonneg.mpr (le_of_not_ge ht)
      have hsource :=
        (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ q p).mp hboundary
      have hneg := (lightLike_iff_norm_sq_zero _).mp hsource.1
      have hneg' : ⟪-(p - q), -(p - q)⟫ₘ = 0 := by
        rw [minkowski_neg_self, hneg]
      rw [show q - p = -(p - q) by abel]
      exact hneg'
  · intro hnull
    by_cases ht : 0 ≤ timeComponent (q - p)
    · have hboundary : q ∈ futureLightConeBoundary p :=
        ⟨(lightLike_iff_norm_sq_zero _).mpr hnull, ht⟩
      exact (lightLike_iff_norm_sq_zero _).mp
        ((futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p q).mpr hboundary).1
    · have hboundary : p ∈ futureLightConeBoundary q := by
        refine ⟨(lightLike_iff_norm_sq_zero _).mpr ?_, ?_⟩
        · have hneg : ⟪-(q - p), -(q - p)⟫ₘ = 0 := by
            rw [minkowski_neg_self, hnull]
          rw [show p - q = -(q - p) by abel]
          exact hneg
        · rw [show p - q = -(q - p) by abel]
          change 0 ≤ -timeComponent (q - p)
          exact neg_nonneg.mpr (le_of_not_ge ht)
      have himage :=
        (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ q p).mpr hboundary
      have hneg := (lightLike_iff_norm_sq_zero _).mp himage.1
      have hneg' : ⟪-(φ p - φ q), -(φ p - φ q)⟫ₘ = 0 := by
        rw [minkowski_neg_self, hneg]
      rw [show φ q - φ p = -(φ p - φ q) by abel]
      exact hneg'

/-- The unoriented null cone with vertex `p`. -/
def nullConeAt (p : Vector 3) : Set (Vector 3) :=
  {q | ⟪q - p, q - p⟫ₘ = 0}

/-- A causal automorphism maps every complete unoriented null cone exactly onto the null
cone at the image vertex. -/
@[zil_level physical_theorem]
theorem nullConeAt_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) (p : Vector 3) :
    φ '' nullConeAt p = nullConeAt (φ p) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (nullSeparation_iff_of_causalAutomorphism hφ p x).mpr hx
  · intro hq
    obtain ⟨x, rfl⟩ := hφ.1.surjective q
    exact ⟨x, (nullSeparation_iff_of_causalAutomorphism hφ p x).mp hq, rfl⟩

/-! # B. Tangent null hyperplanes from incidence -/

/-- The affine hyperplane through `p` Minkowski-orthogonal to `n`. When `n` is nonzero
and null, this is the tangent hyperplane to the null cone at every point of the null line
`p + ℝn`. -/
def nullOrthogonalHyperplane (p n : Vector 3) : Set (Vector 3) :=
  {x | ⟪x - p, n⟫ₘ = 0}

private lemma null_orthogonal_proportional {u n : Vector 3}
    (huQ : ⟪u, u⟫ₘ = 0) (hnQ : ⟪n, n⟫ₘ = 0)
    (hun : ⟪u, n⟫ₘ = 0) (hn0 : n ≠ 0) : ∃ a : ℝ, u = a • n := by
  by_cases hu0 : u = 0
  · exact ⟨0, by simp [hu0]⟩
  by_cases huT : 0 ≤ timeComponent u
  · by_cases hnT : 0 ≤ timeComponent n
    · have hray := futureCausal_null_sameRay_of_mink_zero
        (u := u) (v := n) ⟨huQ.ge, huT⟩ ⟨hnQ.ge, hnT⟩ huQ hnQ hun
      obtain ⟨a, _, ha⟩ := hray.exists_nonneg_right hn0
      exact ⟨a, ha⟩
    · have hnT' : 0 ≤ timeComponent (-n) := by
        change 0 ≤ -timeComponent n
        exact neg_nonneg.mpr (le_of_not_ge hnT)
      have hray := futureCausal_null_sameRay_of_mink_zero
        (u := u) (v := -n) ⟨huQ.ge, huT⟩
        ⟨(by simpa using hnQ.ge), hnT'⟩ huQ (by simpa using hnQ) (by simpa using hun)
      obtain ⟨a, _, ha⟩ := hray.exists_nonneg_right (neg_ne_zero.mpr hn0)
      exact ⟨-a, by simpa using ha⟩
  · have huT' : 0 ≤ timeComponent (-u) := by
      change 0 ≤ -timeComponent u
      exact neg_nonneg.mpr (le_of_not_ge huT)
    by_cases hnT : 0 ≤ timeComponent n
    · have hray := futureCausal_null_sameRay_of_mink_zero
        (u := -u) (v := n) ⟨(by simpa using huQ.ge), huT'⟩ ⟨hnQ.ge, hnT⟩
        (by simpa using huQ) hnQ (by simpa using hun)
      obtain ⟨a, _, ha⟩ := hray.exists_nonneg_right hn0
      exact ⟨-a, by simpa using congrArg Neg.neg ha⟩
    · have hnT' : 0 ≤ timeComponent (-n) := by
        change 0 ≤ -timeComponent n
        exact neg_nonneg.mpr (le_of_not_ge hnT)
      have hray := futureCausal_null_sameRay_of_mink_zero
        (u := -u) (v := -n) ⟨(by simpa using huQ.ge), huT'⟩
        ⟨(by simpa using hnQ.ge), hnT'⟩ (by simpa using huQ) (by simpa using hnQ)
        (by simpa using hun)
      obtain ⟨a, _, ha⟩ := hray.exists_nonneg_right (neg_ne_zero.mpr hn0)
      exact ⟨a, by simpa using congrArg Neg.neg ha⟩

private lemma minkowski_vsub_line_expand (x p n : Vector 3) (a : ℝ) :
    ⟪x - (p + a • n), x - (p + a • n)⟫ₘ =
      ⟪x - p, x - p⟫ₘ - 2 * a * ⟪x - p, n⟫ₘ + a ^ 2 * ⟪n, n⟫ₘ := by
  have hvsub : x - (p + a • n) = (x - p) - a • n := by module
  rw [hvsub]
  calc
    ⟪x - p - a • n, x - p - a • n⟫ₘ =
        ⟪x - p, x - p⟫ₘ - ⟪x - p, a • n⟫ₘ -
          ⟪a • n, x - p⟫ₘ + ⟪a • n, a • n⟫ₘ := by
      simp only [map_sub, sub_apply]
      ring
    _ = ⟪x - p, x - p⟫ₘ - 2 * a * ⟪x - p, n⟫ₘ +
        a ^ 2 * ⟪n, n⟫ₘ := by
      rw [minkowskiProduct_symm (a • n) (x - p)]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring

/-- A point lies in the null tangent hyperplane along `p + ℝn` exactly when it lies on
that null line or has no null-separated point on the line. This reconstructs the affine
hyperplane using only null-line membership and null incidence. -/
lemma mem_nullOrthogonalHyperplane_iff_incidence
    {p n x : Vector 3} (hnQ : ⟪n, n⟫ₘ = 0) (hn0 : n ≠ 0) :
    x ∈ nullOrthogonalHyperplane p n ↔
      x ∈ affineLine p n ∨
        ∀ y, y ∈ affineLine p n → ⟪x - y, x - y⟫ₘ ≠ 0 := by
  constructor
  · intro hx
    by_cases hxQ : ⟪x - p, x - p⟫ₘ = 0
    · obtain ⟨a, ha⟩ := null_orthogonal_proportional hxQ hnQ hx hn0
      left
      exact ⟨a, by rw [← ha]; abel⟩
    · right
      intro y hy
      rcases hy with ⟨a, rfl⟩
      rw [minkowski_vsub_line_expand, hx, hnQ]
      simpa using hxQ
  · rintro (hxLine | hxNoNull)
    · rcases hxLine with ⟨a, rfl⟩
      change ⟪p + a • n - p, n⟫ₘ = 0
      have hsub : p + a • n - p = a • n := by abel
      rw [hsub]
      simp [hnQ]
    · by_contra hx
      have hinner : ⟪x - p, n⟫ₘ ≠ 0 := by
        simpa [nullOrthogonalHyperplane] using hx
      let a := ⟪x - p, x - p⟫ₘ / (2 * ⟪x - p, n⟫ₘ)
      have hnull : ⟪x - (p + a • n), x - (p + a • n)⟫ₘ = 0 := by
        rw [minkowski_vsub_line_expand, hnQ, mul_zero, add_zero]
        dsimp [a]
        field_simp [hinner]
        ring
      exact hxNoNull (p + a • n) ⟨a, rfl⟩ hnull

/-- A causal automorphism maps the tangent hyperplane along every nondegenerate
future-directed null line exactly onto the tangent hyperplane along the image null line.
No affine-hyperplane preservation premise is used: both sides are identified by the
null-incidence characterization above. -/
@[zil_level physical_theorem]
theorem nullOrthogonalHyperplane_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p n : Vector 3} (hnQ : ⟪n, n⟫ₘ = 0)
    (hnT : 0 ≤ timeComponent n) (hn0 : n ≠ 0) :
    φ '' nullOrthogonalHyperplane p n =
      nullOrthogonalHyperplane (φ p) (φ (p + n) - φ p) := by
  let m := φ (p + n) - φ p
  have hsourceQ : ⟪p + n - p, p + n - p⟫ₘ = 0 := by
    simpa only [add_sub_cancel_left] using hnQ
  have hmQ : ⟪m, m⟫ₘ = 0 := by
    exact (nullSeparation_iff_of_causalAutomorphism hφ p (p + n)).mpr hsourceQ
  have hm0 : m ≠ 0 := by
    apply sub_ne_zero.mpr
    exact hφ.1.injective.ne (by
      intro hpn
      apply hn0
      simpa only [add_eq_left] using hpn)
  have hline : φ '' affineLine p n = affineLine (φ p) m := by
    simpa only [nullAffineLine, affineLine, m] using
      nullAffineLine_image_of_causalAutomorphism hφ hnQ hnT hn0
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (mem_nullOrthogonalHyperplane_iff_incidence hmQ hm0).mpr
    rcases (mem_nullOrthogonalHyperplane_iff_incidence hnQ hn0).mp hx with
      hxLine | hxNoNull
    · left
      rw [← hline]
      exact ⟨x, hxLine, rfl⟩
    · right
      intro y hyLine
      have hyImage : y ∈ φ '' affineLine p n := by rwa [hline]
      rcases hyImage with ⟨y₀, hy₀Line, rfl⟩
      intro hnull
      exact hxNoNull y₀ hy₀Line
        ((nullSeparation_iff_of_causalAutomorphism hφ y₀ x).mp hnull)
  · intro hz
    obtain ⟨x, rfl⟩ := hφ.1.surjective z
    refine ⟨x, ?_, rfl⟩
    apply (mem_nullOrthogonalHyperplane_iff_incidence hnQ hn0).mpr
    rcases (mem_nullOrthogonalHyperplane_iff_incidence hmQ hm0).mp hz with
      hxLine | hxNoNull
    · left
      have hxImage : φ x ∈ φ '' affineLine p n := by rwa [hline]
      rcases hxImage with ⟨y, hyLine, hyx⟩
      exact hφ.1.injective hyx ▸ hyLine
    · right
      intro y hyLine
      have hφyLine : φ y ∈ affineLine (φ p) m := by
        rw [← hline]
        exact ⟨y, hyLine, rfl⟩
      intro hnull
      exact hxNoNull (φ y) hφyLine
        ((nullSeparation_iff_of_causalAutomorphism hφ y x).mpr hnull)

/-! # C. Null-normal frames for spacelike directions -/

/-- The first unit vector in the Euclidean spatial factor. -/
private def spatialUnit0 : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.basisFun (Fin 3) ℝ 0

/-- The second unit vector in the Euclidean spatial factor. -/
private def spatialUnit1 : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.basisFun (Fin 3) ℝ 1

/-- The third unit vector in the Euclidean spatial factor. -/
private def spatialUnit2 : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.basisFun (Fin 3) ℝ 2

private lemma spatialBasis_inner (i j : Fin 3) :
    ⟪EuclideanSpace.basisFun (Fin 3) ℝ i,
      EuclideanSpace.basisFun (Fin 3) ℝ j⟫_ℝ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal i j

private lemma spatialBasis_combination_norm_sq {i j : Fin 3} (hij : i ≠ j) (a b : ℝ) :
    ‖a • EuclideanSpace.basisFun (Fin 3) ℝ i +
      b • EuclideanSpace.basisFun (Fin 3) ℝ j‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul]
  have hinner :
      ⟪EuclideanSpace.basisFun (Fin 3) ℝ i,
        EuclideanSpace.basisFun (Fin 3) ℝ j⟫_ℝ = 0 := by
    simpa [hij] using spatialBasis_inner i j
  rw [real_inner_smul_left, real_inner_smul_right, hinner]
  simp

private lemma spatialBasis_first_inner_combination {j : Fin 3} (hj : 0 ≠ j)
    (r a b : ℝ) :
    ⟪r • EuclideanSpace.basisFun (Fin 3) ℝ 0,
      a • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
        b • EuclideanSpace.basisFun (Fin 3) ℝ j⟫_ℝ = r * a := by
  rw [inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right]
  have hself :
      ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0,
        EuclideanSpace.basisFun (Fin 3) ℝ 0⟫_ℝ = 1 := by
    simp
  have hcross :
      ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0,
        EuclideanSpace.basisFun (Fin 3) ℝ j⟫_ℝ = 0 := by
    simpa [hj] using spatialBasis_inner 0 j
  rw [hself, hcross]
  ring

/-- A spatial reflection aligning the spatial part of `v` with the first coordinate axis. -/
private def spatialAlignment (v : Vector 3) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ℝ ∙ (spatialPart v - ‖spatialPart v‖ • spatialUnit0))ᗮ.reflection

/-- The positive transverse radius of the null-normal circle for a spacelike vector. -/
private def spacelikeTransverseRadius (v : Vector 3) : ℝ :=
  Real.sqrt (‖spatialPart v‖ ^ 2 - timeComponent v ^ 2)

/-- Three canonical spatial components of null vectors orthogonal to `v`, after spatial
alignment. -/
private def alignedNullNormalSpatial (v : Vector 3) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![timeComponent v • spatialUnit0 + spacelikeTransverseRadius v • spatialUnit1,
    timeComponent v • spatialUnit0 - spacelikeTransverseRadius v • spatialUnit1,
    timeComponent v • spatialUnit0 + spacelikeTransverseRadius v • spatialUnit2]

/-- A concrete three-vector null-normal frame for a direction in physical Minkowski
space. For a spacelike direction the frame is future-directed, null, linearly independent,
and Minkowski-orthogonal to that direction. -/
private def spacelikeNullNormalFrame (v : Vector 3) (i : Fin 3) : Vector 3 :=
  ofTemporalComponent ‖spatialPart v‖ +
    ofSpatialComponent ((spatialAlignment v).symm (alignedNullNormalSpatial v i))

private lemma spatialAlignment_apply (v : Vector 3) :
    spatialAlignment v (spatialPart v) = ‖spatialPart v‖ • spatialUnit0 := by
  apply Submodule.reflection_sub
  rw [norm_smul, Real.norm_eq_abs, abs_norm]
  simp [spatialUnit0]

private lemma spacelikeTransverseRadius_pos {v : Vector 3} (hv : ⟪v, v⟫ₘ < 0) :
    0 < spacelikeTransverseRadius v := by
  apply Real.sqrt_pos.2
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs] at hv
  linarith

private lemma spacelikeTransverseRadius_sq {v : Vector 3} (hv : ⟪v, v⟫ₘ < 0) :
    spacelikeTransverseRadius v ^ 2 = ‖spatialPart v‖ ^ 2 - timeComponent v ^ 2 := by
  rw [spacelikeTransverseRadius]
  apply Real.sq_sqrt
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs] at hv
  linarith

private lemma spatialPart_norm_pos_of_spacelike {v : Vector 3} (hv : ⟪v, v⟫ₘ < 0) :
    0 < ‖spatialPart v‖ := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs] at hv
  nlinarith [norm_nonneg (spatialPart v)]

private lemma alignedNullNormalSpatial_norm_sq (v : Vector 3) (i : Fin 3) :
    ‖alignedNullNormalSpatial v i‖ ^ 2 =
      timeComponent v ^ 2 + spacelikeTransverseRadius v ^ 2 := by
  fin_cases i
  · simpa [alignedNullNormalSpatial, spatialUnit0, spatialUnit1] using
      spatialBasis_combination_norm_sq (i := (0 : Fin 3)) (j := 1) (by decide)
        (timeComponent v) (spacelikeTransverseRadius v)
  · simpa [alignedNullNormalSpatial, spatialUnit0, spatialUnit1, sub_eq_add_neg] using
      spatialBasis_combination_norm_sq (i := (0 : Fin 3)) (j := 1) (by decide)
        (timeComponent v) (-spacelikeTransverseRadius v)
  · simpa [alignedNullNormalSpatial, spatialUnit0, spatialUnit2] using
      spatialBasis_combination_norm_sq (i := (0 : Fin 3)) (j := 2) (by decide)
        (timeComponent v) (spacelikeTransverseRadius v)

private lemma alignedNullNormalSpatial_inner (v : Vector 3) (i : Fin 3) :
    ⟪‖spatialPart v‖ • spatialUnit0, alignedNullNormalSpatial v i⟫_ℝ =
      ‖spatialPart v‖ * timeComponent v := by
  fin_cases i
  · simpa [alignedNullNormalSpatial, spatialUnit0, spatialUnit1] using
      spatialBasis_first_inner_combination (j := (1 : Fin 3)) (by decide)
        ‖spatialPart v‖ (timeComponent v) (spacelikeTransverseRadius v)
  · simpa [alignedNullNormalSpatial, spatialUnit0, spatialUnit1, sub_eq_add_neg] using
      spatialBasis_first_inner_combination (j := (1 : Fin 3)) (by decide)
        ‖spatialPart v‖ (timeComponent v) (-spacelikeTransverseRadius v)
  · simpa [alignedNullNormalSpatial, spatialUnit0, spatialUnit2] using
      spatialBasis_first_inner_combination (j := (2 : Fin 3)) (by decide)
        ‖spatialPart v‖ (timeComponent v) (spacelikeTransverseRadius v)

private lemma spacelikeNullNormalFrame_timeComponent (v : Vector 3) (i : Fin 3) :
    timeComponent (spacelikeNullNormalFrame v i) = ‖spatialPart v‖ := by
  change temporalCLM 3 (spacelikeNullNormalFrame v i) = ‖spatialPart v‖
  rw [spacelikeNullNormalFrame, map_add]
  change timeComponent (ofTemporalComponent ‖spatialPart v‖) +
    timeComponent (ofSpatialComponent ((spatialAlignment v).symm
      (alignedNullNormalSpatial v i))) = ‖spatialPart v‖
  rw [timeComponent_ofTemporalComponent, timeComponent_ofSpatialComponent, add_zero]

private lemma spacelikeNullNormalFrame_spatialPart (v : Vector 3) (i : Fin 3) :
    spatialPart (spacelikeNullNormalFrame v i) =
      (spatialAlignment v).symm (alignedNullNormalSpatial v i) := by
  change spatialCLM 3 (spacelikeNullNormalFrame v i) = _
  rw [spacelikeNullNormalFrame, map_add]
  change spatialPart (ofTemporalComponent ‖spatialPart v‖) +
    spatialPart (ofSpatialComponent ((spatialAlignment v).symm
      (alignedNullNormalSpatial v i))) = _
  rw [spatialPart_ofTemporalComponent, spatialPart_ofSpatialComponent, zero_add]

/-- Every member of the concrete spacelike null-normal frame is null. -/
private lemma spacelikeNullNormalFrame_null {v : Vector 3} (hv : ⟪v, v⟫ₘ < 0)
    (i : Fin 3) :
    ⟪spacelikeNullNormalFrame v i, spacelikeNullNormalFrame v i⟫ₘ = 0 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
  rw [spacelikeNullNormalFrame_timeComponent, spacelikeNullNormalFrame_spatialPart,
    Real.norm_eq_abs, abs_norm, LinearIsometryEquiv.norm_map]
  rw [alignedNullNormalSpatial_norm_sq, spacelikeTransverseRadius_sq hv]
  ring

/-- Every member of the concrete spacelike null-normal frame is Minkowski-orthogonal to
the original spacelike direction. -/
private lemma spacelikeNullNormalFrame_orthogonal (v : Vector 3) (i : Fin 3) :
    ⟪v, spacelikeNullNormalFrame v i⟫ₘ = 0 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  rw [spacelikeNullNormalFrame_timeComponent, spacelikeNullNormalFrame_spatialPart]
  have hinner :
      ⟪spatialPart v, (spatialAlignment v).symm (alignedNullNormalSpatial v i)⟫_ℝ =
        ⟪spatialAlignment v (spatialPart v), alignedNullNormalSpatial v i⟫_ℝ := by
    symm
    simpa using (spatialAlignment v).inner_map_map (spatialPart v)
      ((spatialAlignment v).symm (alignedNullNormalSpatial v i))
  rw [hinner, spatialAlignment_apply, alignedNullNormalSpatial_inner]
  ring

/-- The concrete null-normal frame of a spacelike direction is future-directed and
nonzero. -/
private lemma spacelikeNullNormalFrame_time_pos {v : Vector 3} (hv : ⟪v, v⟫ₘ < 0)
    (i : Fin 3) :
    0 < timeComponent (spacelikeNullNormalFrame v i) := by
  rw [spacelikeNullNormalFrame_timeComponent]
  exact spatialPart_norm_pos_of_spacelike hv

/-- The three concrete null normals of a spacelike direction are linearly independent. -/
private lemma spacelikeNullNormalFrame_linearIndependent {v : Vector 3}
    (hv : ⟪v, v⟫ₘ < 0) :
    LinearIndependent ℝ (spacelikeNullNormalFrame v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have ht := congrArg (temporalCLM 3) hg
  rw [map_sum] at ht
  simp_rw [map_smul, temporalCLM_apply_eq_timeComponent,
    spacelikeNullNormalFrame_timeComponent] at ht
  have ht0 : ∑ i, g i • ‖spatialPart v‖ = 0 := by simpa using ht
  have hsp := congrArg (spatialCLM 3) hg
  rw [map_sum] at hsp
  simp_rw [map_smul] at hsp
  change ∑ i, g i • spatialPart (spacelikeNullNormalFrame v i) = 0 at hsp
  simp_rw [spacelikeNullNormalFrame_spatialPart] at hsp
  have hs := congrArg (spatialAlignment v) hsp
  rw [map_sum] at hs
  simp_rw [map_smul, LinearIsometryEquiv.apply_symm_apply] at hs
  have hs0 : ∑ i, g i • alignedNullNormalSpatial v i = 0 := by simpa using hs
  have hs1 := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 1) hs0
  have hs2 := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 2) hs0
  simp [Fin.sum_univ_three, alignedNullNormalSpatial, spatialUnit0, spatialUnit1,
    spatialUnit2] at ht0 hs1 hs2
  have hnorm := spatialPart_norm_pos_of_spacelike hv
  have hradius := spacelikeTransverseRadius_pos hv
  have hg2 : g 2 = 0 := hs2.resolve_right hradius.ne'
  have hdiff : (g 0 - g 1) * spacelikeTransverseRadius v = 0 := by
    nlinarith [hs1]
  have hg01 : g 0 = g 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hradius.ne')
  have hg0 : g 0 = 0 := by nlinarith [ht0]
  have hg1 : g 1 = 0 := hg01 ▸ hg0
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- Every spacelike direction in physical Minkowski space has three linearly independent,
future-directed null normals. This is a constructive null basis of its orthogonal
complement, not an assumed density or basis certificate. -/
lemma exists_spacelike_null_normal_frame {v : Vector 3} (hv : ⟪v, v⟫ₘ < 0) :
    ∃ n : Fin 3 → Vector 3,
      LinearIndependent ℝ n ∧
      (∀ i, ⟪n i, n i⟫ₘ = 0) ∧
      (∀ i, 0 < timeComponent (n i)) ∧
      ∀ i, ⟪v, n i⟫ₘ = 0 := by
  exact ⟨spacelikeNullNormalFrame v, spacelikeNullNormalFrame_linearIndependent hv,
    spacelikeNullNormalFrame_null hv, spacelikeNullNormalFrame_time_pos hv,
    spacelikeNullNormalFrame_orthogonal v⟩

/-! # D. One-dimensional common orthogonals -/

/-- The Minkowski product packaged as an algebraic bilinear form. -/
private def minkowskiBilin : LinearMap.BilinForm ℝ (Vector 3) where
  toFun v := (minkowskiProduct v).toLinearMap
  map_add' v w := by ext z; simp
  map_smul' a v := by ext z; simp

private lemma minkowskiBilin_isRefl : minkowskiBilin.IsRefl := by
  intro v w h
  simpa [minkowskiBilin, minkowskiProduct_symm w v] using h

private lemma minkowskiBilin_nondegenerate : minkowskiBilin.Nondegenerate := by
  constructor
  · intro v h
    exact (minkowskiProduct_eq_zero_forall_iff v).mp h
  · intro v h
    apply (minkowskiProduct_eq_zero_forall_iff v).mp
    intro w
    rw [minkowskiProduct_symm]
    exact h w

private lemma vector3_finrank : Module.finrank ℝ (Vector 3) = 4 := by
  rw [Module.finrank_eq_card_basis Lorentz.Vector.basis]
  simp

private lemma common_orthogonal_eq_line {n : Fin 3 → Vector 3}
    (hn : LinearIndependent ℝ n) {d : Vector 3} (hd0 : d ≠ 0)
    (hd : ∀ i, ⟪d, n i⟫ₘ = 0) :
    ∀ z, (∀ i, ⟪z, n i⟫ₘ = 0) ↔ ∃ a : ℝ, z = a • d := by
  let W := Submodule.span ℝ (Set.range n)
  let O := minkowskiBilin.orthogonal W
  have hWrank : Module.finrank ℝ W = 3 := by
    dsimp [W]
    rw [finrank_span_eq_card hn]
    simp
  have hOrank : Module.finrank ℝ O = 1 := by
    dsimp [O]
    rw [LinearMap.BilinForm.finrank_orthogonal minkowskiBilin_nondegenerate,
      vector3_finrank, hWrank]
  have hdO : d ∈ O := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        simpa [minkowskiBilin, minkowskiProduct_symm] using hd i
    | zero => simp [minkowskiBilin]
    | add x y _ _ hx hy =>
        calc
          minkowskiBilin (x + y) d = minkowskiBilin x d + minkowskiBilin y d := by
            simp [minkowskiBilin]
          _ = 0 := by rw [hx, hy, add_zero]
    | smul a x _ hx =>
        calc
          minkowskiBilin (a • x) d = a * minkowskiBilin x d := by
            simp [minkowskiBilin]
          _ = 0 := by rw [hx, mul_zero]
  have hspan : ℝ ∙ d = O := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem d O).mpr hdO
    · rw [hOrank, finrank_span_singleton hd0]
  intro z
  have hO : (∀ i, ⟪z, n i⟫ₘ = 0) ↔ z ∈ O := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hz w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
          rcases hx with ⟨i, rfl⟩
          simpa [minkowskiBilin, minkowskiProduct_symm] using hz i
      | zero => simp [minkowskiBilin]
      | add x y _ _ hx hy =>
          calc
            minkowskiBilin (x + y) z = minkowskiBilin x z + minkowskiBilin y z := by
              simp [minkowskiBilin]
            _ = 0 := by rw [hx, hy, add_zero]
      | smul a x _ hx =>
          calc
            minkowskiBilin (a • x) z = a * minkowskiBilin x z := by
              simp [minkowskiBilin]
            _ = 0 := by rw [hx, mul_zero]
    · intro hz i
      have hi : n i ∈ W := Submodule.subset_span ⟨i, rfl⟩
      have hzi := hz (n i) hi
      simpa [minkowskiBilin, minkowskiProduct_symm] using hzi
  rw [hO, ← hspan, Submodule.mem_span_singleton]
  constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩

private lemma linearIndependent_not_smul {n : Fin 3 → Vector 3}
    (hn : LinearIndependent ℝ n) {i j : Fin 3} (hij : i ≠ j) (a : ℝ) :
    n i ≠ a • n j := by
  intro ha
  let f : Fin 2 → Fin 3 := ![i, j]
  have hf : Function.Injective f := by
    intro x y
    have hji : j ≠ i := Ne.symm hij
    fin_cases x <;> fin_cases y <;> simp_all [f]
  have hp : LinearIndependent ℝ (fun k => n (f k)) := hn.comp f hf
  have hfamily : (fun k => n (f k)) = ![n i, n j] := by
    funext k
    fin_cases k <;> rfl
  have hpair : LinearIndependent ℝ ![n i, n j] := hfamily ▸ hp
  have hrel : (1 : ℝ) • n i + (-a) • n j = 0 := by
    rw [one_smul, ha]
    module
  have hcoef := LinearIndependent.pair_iff.mp hpair 1 (-a) hrel
  norm_num at hcoef

private lemma nullFrame_linearIndependent {n : Fin 3 → Vector 3}
    (hnQ : ∀ i, ⟪n i, n i⟫ₘ = 0) (hn0 : ∀ i, n i ≠ 0)
    (hpair : ∀ i j, i ≠ j → ∀ a : ℝ, n i ≠ a • n j) :
    LinearIndependent ℝ n := by
  have h01 : ⟪n 0, n 1⟫ₘ ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := null_orthogonal_proportional (hnQ 0) (hnQ 1) h (hn0 1)
    exact hpair 0 1 (by decide) a ha
  have h02 : ⟪n 0, n 2⟫ₘ ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := null_orthogonal_proportional (hnQ 0) (hnQ 2) h (hn0 2)
    exact hpair 0 2 (by decide) a ha
  have h12 : ⟪n 1, n 2⟫ₘ ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := null_orthogonal_proportional (hnQ 1) (hnQ 2) h (hn0 2)
    exact hpair 1 2 (by decide) a ha
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  have h0 := congrArg (fun z => minkowskiProductMap z (n 0)) hg
  have h1 := congrArg (fun z => minkowskiProductMap z (n 1)) hg
  have h2 := congrArg (fun z => minkowskiProductMap z (n 2)) hg
  simp only [minkowskiProductMap_add_fst, minkowskiProductMap_smul_fst] at h0 h1 h2
  change g 0 * ⟪n 0, n 0⟫ₘ + g 1 * ⟪n 1, n 0⟫ₘ +
    g 2 * ⟪n 2, n 0⟫ₘ = ⟪0, n 0⟫ₘ at h0
  change g 0 * ⟪n 0, n 1⟫ₘ + g 1 * ⟪n 1, n 1⟫ₘ +
    g 2 * ⟪n 2, n 1⟫ₘ = ⟪0, n 1⟫ₘ at h1
  change g 0 * ⟪n 0, n 2⟫ₘ + g 1 * ⟪n 1, n 2⟫ₘ +
    g 2 * ⟪n 2, n 2⟫ₘ = ⟪0, n 2⟫ₘ at h2
  rw [hnQ 0, minkowskiProduct_symm (n 1) (n 0),
    minkowskiProduct_symm (n 2) (n 0)] at h0
  rw [hnQ 1, minkowskiProduct_symm (n 2) (n 1)] at h1
  rw [hnQ 2] at h2
  have hzero (i : Fin 3) : ⟪(0 : Vector 3), n i⟫ₘ = 0 := by
    rw [minkowskiProduct_toCoord]
    simp
  rw [hzero 0] at h0
  rw [hzero 1] at h1
  rw [hzero 2] at h2
  simp only [mul_zero, zero_add, add_zero] at h0 h1 h2
  have hg2prod :
      (2 * ⟪n 0, n 2⟫ₘ * ⟪n 1, n 2⟫ₘ) * g 2 = 0 := by
    linear_combination ⟪n 0, n 2⟫ₘ * h1 + ⟪n 1, n 2⟫ₘ * h0 -
      ⟪n 0, n 1⟫ₘ * h2
  have hcoef : 2 * ⟪n 0, n 2⟫ₘ * ⟪n 1, n 2⟫ₘ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) h02) h12
  have hg2 : g 2 = 0 := (mul_eq_zero.mp hg2prod).resolve_left hcoef
  rw [hg2, zero_mul, add_zero] at h0 h1
  have hg1 : g 1 = 0 := (mul_eq_zero.mp h0).resolve_right h01
  have hg0 : g 0 = 0 := (mul_eq_zero.mp h1).resolve_right h01
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

private lemma mem_affineLine_iff_common_nullHyperplanes {p v x : Vector 3}
    {n : Fin 3 → Vector 3} (hn : LinearIndependent ℝ n) (hv0 : v ≠ 0)
    (hvn : ∀ i, ⟪v, n i⟫ₘ = 0) :
    x ∈ affineLine p v ↔ ∀ i, x ∈ nullOrthogonalHyperplane p (n i) := by
  rw [show x ∈ affineLine p v ↔ ∃ a : ℝ, x - p = a • v by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by abel⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; abel⟩]
  rw [← common_orthogonal_eq_line hn hv0 hvn (x - p)]
  rfl

private lemma image_nullFrame_linearIndependent
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) {p : Vector 3}
    {n : Fin 3 → Vector 3} (hn : LinearIndependent ℝ n)
    (hnQ : ∀ i, ⟪n i, n i⟫ₘ = 0) (hnT : ∀ i, 0 < timeComponent (n i))
    (hn0 : ∀ i, n i ≠ 0) :
    LinearIndependent ℝ (fun i => φ (p + n i) - φ p) := by
  let m : Fin 3 → Vector 3 := fun i => φ (p + n i) - φ p
  have hmQ (i : Fin 3) : ⟪m i, m i⟫ₘ = 0 := by
    exact (nullSeparation_iff_of_causalAutomorphism hφ p (p + n i)).mpr (by
      simpa [m] using hnQ i)
  have hm0 (i : Fin 3) : m i ≠ 0 := by
    apply sub_ne_zero.mpr
    exact hφ.1.injective.ne (by
      intro hpn
      apply hn0 i
      simpa only [add_eq_left] using hpn)
  have hpair (i j : Fin 3) (hij : i ≠ j) (a : ℝ) : m i ≠ a • m j := by
    intro ha
    have hlinej : φ '' affineLine p (n j) = affineLine (φ p) (m j) := by
      simpa only [nullAffineLine, affineLine, m] using
        nullAffineLine_image_of_causalAutomorphism hφ (hnQ j) (hnT j).le (hn0 j)
    have htarget : φ (p + n i) ∈ affineLine (φ p) (m j) := by
      refine ⟨a, ?_⟩
      calc
        φ (p + n i) = φ p + m i := by simp [m]
        _ = φ p + a • m j := by rw [ha]
    rw [← hlinej] at htarget
    rcases htarget with ⟨y, ⟨b, hy⟩, hφy⟩
    have hyi : y = p + n i := hφ.1.injective (hφy.trans rfl)
    apply linearIndependent_not_smul hn hij b
    exact add_left_cancel (hyi.symm.trans hy)
  exact nullFrame_linearIndependent hmQ hm0 hpair

/-! # E. Spacelike affine-line preservation -/

/-- A bare causal automorphism maps every spacelike affine line exactly onto the affine
line through the images of its base point and unit parameter point. The proof constructs
three independent null normals, maps their reconstructed tangent hyperplanes, and takes
their one-dimensional common orthogonal; it assumes no affine or continuity premise. -/
@[zil_level physical_theorem]
theorem spacelikeAffineLine_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p v : Vector 3} (hv : ⟪v, v⟫ₘ < 0) :
    φ '' affineLine p v = affineLine (φ p) (φ (p + v) - φ p) := by
  let n : Fin 3 → Vector 3 := spacelikeNullNormalFrame v
  let m : Fin 3 → Vector 3 := fun i => φ (p + n i) - φ p
  let d : Vector 3 := φ (p + v) - φ p
  have hn : LinearIndependent ℝ n := spacelikeNullNormalFrame_linearIndependent hv
  have hnQ (i : Fin 3) : ⟪n i, n i⟫ₘ = 0 := spacelikeNullNormalFrame_null hv i
  have hnT (i : Fin 3) : 0 < timeComponent (n i) :=
    spacelikeNullNormalFrame_time_pos hv i
  have hn0 (i : Fin 3) : n i ≠ 0 := by
    intro hi
    have htime := congrArg timeComponent hi
    have hzero : timeComponent (0 : Vector 3) = 0 := rfl
    rw [hzero] at htime
    linarith [hnT i]
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hm : LinearIndependent ℝ m := by
    simpa [m] using image_nullFrame_linearIndependent hφ hn hnQ hnT hn0
  have hd0 : d ≠ 0 := by
    apply sub_ne_zero.mpr
    exact hφ.1.injective.ne (by
      intro hpv
      apply hv0
      simpa only [add_eq_left] using hpv)
  have himageH (i : Fin 3) :
      φ '' nullOrthogonalHyperplane p (n i) =
        nullOrthogonalHyperplane (φ p) (m i) := by
    simpa [m] using nullOrthogonalHyperplane_image_of_causalAutomorphism
      hφ (hnQ i) (hnT i).le (hn0 i)
  have hvn (i : Fin 3) : ⟪v, n i⟫ₘ = 0 :=
    spacelikeNullNormalFrame_orthogonal v i
  have hdn (i : Fin 3) : ⟪d, m i⟫ₘ = 0 := by
    have hsource : p + v ∈ nullOrthogonalHyperplane p (n i) := by
      change ⟪p + v - p, n i⟫ₘ = 0
      simpa only [add_sub_cancel_left] using hvn i
    have himage : φ (p + v) ∈ φ '' nullOrthogonalHyperplane p (n i) :=
      ⟨p + v, hsource, rfl⟩
    rw [himageH i] at himage
    exact himage
  have hsource (x : Vector 3) :
      x ∈ affineLine p v ↔ ∀ i, x ∈ nullOrthogonalHyperplane p (n i) :=
    mem_affineLine_iff_common_nullHyperplanes hn hv0 hvn
  have htarget (x : Vector 3) :
      x ∈ affineLine (φ p) d ↔
        ∀ i, x ∈ nullOrthogonalHyperplane (φ p) (m i) :=
    mem_affineLine_iff_common_nullHyperplanes hm hd0 hdn
  have hincidence (i : Fin 3) (x : Vector 3) :
      x ∈ nullOrthogonalHyperplane p (n i) ↔
        φ x ∈ nullOrthogonalHyperplane (φ p) (m i) := by
    constructor
    · intro hx
      rw [← himageH i]
      exact ⟨x, hx, rfl⟩
    · intro hx
      have hxImage : φ x ∈ φ '' nullOrthogonalHyperplane p (n i) := by
        rwa [himageH i]
      rcases hxImage with ⟨y, hy, hxy⟩
      exact hφ.1.injective hxy ▸ hy
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (htarget (φ x)).mpr
    intro i
    exact (hincidence i x).mp ((hsource x).mp hx i)
  · intro hz
    obtain ⟨x, rfl⟩ := hφ.1.surjective z
    refine ⟨x, (hsource x).mpr ?_, rfl⟩
    intro i
    exact (hincidence i x).mpr ((htarget (φ x)).mp hz i)

/-! # F. Hyperbolic affine-plane preservation -/

private lemma null_connector_norm_sq {m n : Vector 3} (hmQ : ⟪m, m⟫ₘ = 0)
    (hnQ : ⟪n, n⟫ₘ = 0) (a b : ℝ) :
    ⟪b • n - a • m, b • n - a • m⟫ₘ = -2 * a * b * ⟪m, n⟫ₘ := by
  calc
    ⟪b • n - a • m, b • n - a • m⟫ₘ =
        ⟪b • n, b • n⟫ₘ - ⟪b • n, a • m⟫ₘ -
          ⟪a • m, b • n⟫ₘ + ⟪a • m, a • m⟫ₘ := by
      simp only [map_sub, sub_apply]
      ring
    _ = -2 * a * b * ⟪m, n⟫ₘ := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [hmQ, hnQ, minkowskiProduct_symm n m]
      ring

private lemma image_mem_hyperbolicPlane_of_connector
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p m n q r x : Vector 3}
    (hmQ : ⟪m, m⟫ₘ = 0) (hnQ : ⟪n, n⟫ₘ = 0)
    (hmT : 0 ≤ timeComponent m) (hnT : 0 ≤ timeComponent n)
    (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (hq : q ∈ affineLine p m) (hr : r ∈ affineLine p n)
    (hv : ⟪r - q, r - q⟫ₘ < 0) (hx : x ∈ affineLine q (r - q)) :
    φ x ∈ affinePlane (φ p) (φ (p + m) - φ p) (φ (p + n) - φ p) := by
  let M := φ (p + m) - φ p
  let N := φ (p + n) - φ p
  have hlineM : φ '' affineLine p m = affineLine (φ p) M := by
    simpa only [nullAffineLine, affineLine, M] using
      nullAffineLine_image_of_causalAutomorphism hφ hmQ hmT hm0
  have hlineN : φ '' affineLine p n = affineLine (φ p) N := by
    simpa only [nullAffineLine, affineLine, N] using
      nullAffineLine_image_of_causalAutomorphism hφ hnQ hnT hn0
  have hφq : φ q ∈ affineLine (φ p) M := by
    rw [← hlineM]
    exact ⟨q, hq, rfl⟩
  have hφr : φ r ∈ affineLine (φ p) N := by
    rw [← hlineN]
    exact ⟨r, hr, rfl⟩
  rcases hφq with ⟨c, hc⟩
  rcases hφr with ⟨d, hd⟩
  have hline : φ '' affineLine q (r - q) =
      affineLine (φ q) (φ r - φ q) := by
    have hqr : q + (r - q) = r := by abel
    simpa only [hqr] using
      spacelikeAffineLine_image_of_causalAutomorphism hφ (p := q) hv
  have hφx : φ x ∈ affineLine (φ q) (φ r - φ q) := by
    rw [← hline]
    exact ⟨x, hx, rfl⟩
  rcases hφx with ⟨t, ht⟩
  refine ⟨(1 - t) * c, t * d, ?_⟩
  rw [ht, hc, hd]
  dsimp [M, N]
  module

private lemma hyperbolicAffinePlane_image_subset
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p m n : Vector 3} (hmQ : ⟪m, m⟫ₘ = 0) (hnQ : ⟪n, n⟫ₘ = 0)
    (hmT : 0 ≤ timeComponent m) (hnT : 0 ≤ timeComponent n)
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : 0 < ⟪m, n⟫ₘ) :
    φ '' affinePlane p m n ⊆
      affinePlane (φ p) (φ (p + m) - φ p) (φ (p + n) - φ p) := by
  rintro _ ⟨x, ⟨a, b, hx⟩, rfl⟩
  by_cases ha : a = 0
  · subst a
    have hxLine : x ∈ affineLine p n := ⟨b, by simpa using hx⟩
    have hline := nullAffineLine_image_of_causalAutomorphism hφ (p := p) hnQ hnT hn0
    have hφx : φ x ∈ affineLine (φ p) (φ (p + n) - φ p) := by
      rw [← show φ '' affineLine p n =
        affineLine (φ p) (φ (p + n) - φ p) by
          simpa only [nullAffineLine, affineLine] using hline]
      exact ⟨x, hxLine, rfl⟩
    rcases hφx with ⟨c, hc⟩
    exact ⟨0, c, by simpa using hc⟩
  by_cases hb : b = 0
  · subst b
    have hxLine : x ∈ affineLine p m := ⟨a, by simpa using hx⟩
    have hline := nullAffineLine_image_of_causalAutomorphism hφ (p := p) hmQ hmT hm0
    have hφx : φ x ∈ affineLine (φ p) (φ (p + m) - φ p) := by
      rw [← show φ '' affineLine p m =
        affineLine (φ p) (φ (p + m) - φ p) by
          simpa only [nullAffineLine, affineLine] using hline]
      exact ⟨x, hxLine, rfl⟩
    rcases hφx with ⟨c, hc⟩
    exact ⟨c, 0, by simpa using hc⟩
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rcases lt_or_gt_of_ne hab0 with habNeg | habPos
  · let q := p + (-a) • m
    let r := p + (b / 2) • n
    have hq : q ∈ affineLine p m := ⟨-a, rfl⟩
    have hr : r ∈ affineLine p n := ⟨b / 2, rfl⟩
    have hv : ⟪r - q, r - q⟫ₘ < 0 := by
      have hdir : r - q = (b / 2) • n - (-a) • m := by
        dsimp [q, r]
        module
      rw [hdir, null_connector_norm_sq hmQ hnQ]
      nlinarith
    have hxConnector : x ∈ affineLine q (r - q) := by
      refine ⟨2, ?_⟩
      rw [hx]
      dsimp [q, r]
      module
    exact image_mem_hyperbolicPlane_of_connector hφ hmQ hnQ hmT hnT hm0 hn0
      hq hr hv hxConnector
  · let q := p + (2 * a) • m
    let r := p + (2 * b) • n
    have hq : q ∈ affineLine p m := ⟨2 * a, rfl⟩
    have hr : r ∈ affineLine p n := ⟨2 * b, rfl⟩
    have hv : ⟪r - q, r - q⟫ₘ < 0 := by
      have hdir : r - q = (2 * b) • n - (2 * a) • m := by
        dsimp [q, r]
        module
      rw [hdir, null_connector_norm_sq hmQ hnQ]
      nlinarith
    have hxConnector : x ∈ affineLine q (r - q) := by
      refine ⟨(2 : ℝ)⁻¹, ?_⟩
      rw [hx]
      dsimp [q, r]
      module
    exact image_mem_hyperbolicPlane_of_connector hφ hmQ hnQ hmT hnT hm0 hn0
      hq hr hv hxConnector

/-- A bare causal automorphism maps the affine plane generated by two nonorthogonal
future-null directions exactly onto the plane generated by their image directions. Such
a plane is hyperbolic: its restricted Minkowski form has one positive and one negative
direction. The proof uses only null-axis preservation and spacelike connector lines. -/
@[zil_level physical_theorem]
theorem hyperbolicAffinePlane_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p m n : Vector 3} (hmQ : ⟪m, m⟫ₘ = 0) (hnQ : ⟪n, n⟫ₘ = 0)
    (hmT : 0 ≤ timeComponent m) (hnT : 0 ≤ timeComponent n)
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : 0 < ⟪m, n⟫ₘ) :
    φ '' affinePlane p m n =
      affinePlane (φ p) (φ (p + m) - φ p) (φ (p + n) - φ p) := by
  let M := φ (p + m) - φ p
  let N := φ (p + n) - φ p
  have hmBoundary : p + m ∈ futureLightConeBoundary p := by
    constructor
    · rw [lightLike_iff_norm_sq_zero]
      simpa only [add_sub_cancel_left] using hmQ
    · simpa only [add_sub_cancel_left] using hmT
  have hnBoundary : p + n ∈ futureLightConeBoundary p := by
    constructor
    · rw [lightLike_iff_norm_sq_zero]
      simpa only [add_sub_cancel_left] using hnQ
    · simpa only [add_sub_cancel_left] using hnT
  have hMBoundary : φ (p + m) ∈ futureLightConeBoundary (φ p) :=
    (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + m)).mpr hmBoundary
  have hNBoundary : φ (p + n) ∈ futureLightConeBoundary (φ p) :=
    (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + n)).mpr hnBoundary
  have hMQ : ⟪M, M⟫ₘ = 0 := (lightLike_iff_norm_sq_zero _).mp hMBoundary.1
  have hNQ : ⟪N, N⟫ₘ = 0 := (lightLike_iff_norm_sq_zero _).mp hNBoundary.1
  have hMT : 0 ≤ timeComponent M := hMBoundary.2
  have hNT : 0 ≤ timeComponent N := hNBoundary.2
  have hM0 : M ≠ 0 := by
    apply sub_ne_zero.mpr
    exact hφ.1.injective.ne (by
      intro hpm
      apply hm0
      simpa only [add_eq_left] using hpm)
  have hN0 : N ≠ 0 := by
    apply sub_ne_zero.mpr
    exact hφ.1.injective.ne (by
      intro hpn
      apply hn0
      simpa only [add_eq_left] using hpn)
  have hMNnonneg : 0 ≤ ⟪M, N⟫ₘ :=
    minkowskiProduct_nonneg_of_futureCausal hMQ.ge hNQ.ge hMT hNT
  have hMN0 : ⟪M, N⟫ₘ ≠ 0 := by
    intro hMN
    have himageQ :
        ⟪φ (p + n) - φ (p + m), φ (p + n) - φ (p + m)⟫ₘ = 0 := by
      have hdiff : φ (p + n) - φ (p + m) = N - M := by
        dsimp [M, N]
        abel
      rw [hdiff]
      have h := null_connector_norm_sq hMQ hNQ (1 : ℝ) (1 : ℝ)
      simpa only [one_smul, one_mul, mul_one, hMN, mul_zero] using h
    have hsourceQ :=
      (nullSeparation_iff_of_causalAutomorphism hφ (p + m) (p + n)).mp himageQ
    have hsourceDiff : p + n - (p + m) = n - m := by abel
    rw [hsourceDiff] at hsourceQ
    have hsourceExpand := null_connector_norm_sq hmQ hnQ (1 : ℝ) (1 : ℝ)
    have hsourceQ' : -2 * ⟪m, n⟫ₘ = 0 := by
      rw [← hsourceQ]
      simpa only [one_smul, one_mul, mul_one] using hsourceExpand.symm
    nlinarith
  have hMN : 0 < ⟪M, N⟫ₘ := lt_of_le_of_ne hMNnonneg (Ne.symm hMN0)
  apply Set.Subset.antisymm
  · simpa only [M, N] using
      hyperbolicAffinePlane_image_subset hφ hmQ hnQ hmT hnT hm0 hn0 hmn
  · intro z hz
    let e : Vector 3 ≃ Vector 3 := Equiv.ofBijective φ hφ.1
    have he_apply (x : Vector 3) : e x = φ x := rfl
    have hinv : IsCausalAutomorphism e.symm := by
      refine ⟨e.symm.bijective, ?_⟩
      intro x y
      calc
        causallyFollows (e.symm x) (e.symm y) ↔
            causallyFollows (φ (e.symm x)) (φ (e.symm y)) :=
          (hφ.2 (e.symm x) (e.symm y)).symm
        _ ↔ causallyFollows x y := by
          rw [← he_apply, ← he_apply, e.apply_symm_apply, e.apply_symm_apply]
    have hzImage : e.symm z ∈ e.symm '' affinePlane (φ p) M N := ⟨z, hz, rfl⟩
    have hx := hyperbolicAffinePlane_image_subset hinv hMQ hNQ hMT hNT hM0 hN0 hMN
      hzImage
    have hpInv : e.symm (φ p) = p := by
      rw [← he_apply]
      exact e.symm_apply_apply p
    have hmInv : e.symm (φ p + M) = p + m := by
      rw [show φ p + M = φ (p + m) by dsimp [M]; abel, ← he_apply]
      exact e.symm_apply_apply (p + m)
    have hnInv : e.symm (φ p + N) = p + n := by
      rw [show φ p + N = φ (p + n) by dsimp [N]; abel, ← he_apply]
      exact e.symm_apply_apply (p + n)
    have hxSource : e.symm z ∈ affinePlane p m n := by
      rw [hpInv, hmInv, hnInv, add_sub_cancel_left, add_sub_cancel_left] at hx
      exact hx
    exact ⟨e.symm z, hxSource, by rw [← he_apply, e.apply_symm_apply]⟩

/-! # G. Timelike affine-line preservation -/

/-- The future-directed orientation of a nonzero timelike vector. -/
private def futureOrientation (v : Vector 3) : Vector 3 :=
  if 0 < timeComponent v then v else -v

/-- Two unit spacelike directions orthogonal to a timelike vector, obtained by aligning
its spatial part with the first Euclidean coordinate and using the two transverse axes. -/
private def timelikeTransverse (v : Vector 3) (i : Fin 2) : Vector 3 :=
  ofSpatialComponent ((spatialAlignment v).symm (![spatialUnit1, spatialUnit2] i))

private lemma futureOrientation_norm_sq (v : Vector 3) :
    ⟪futureOrientation v, futureOrientation v⟫ₘ = ⟪v, v⟫ₘ := by
  by_cases ht : 0 < timeComponent v
  · simp [futureOrientation, ht]
  · simp [futureOrientation, ht]

private lemma futureOrientation_time_pos {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ) :
    0 < timeComponent (futureOrientation v) := by
  have ht0 : timeComponent v ≠ 0 := by
    intro ht
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart, ht] at hv
    norm_num at hv
    nlinarith [sq_nonneg ‖spatialPart v‖]
  by_cases ht : 0 < timeComponent v
  · simp only [futureOrientation, if_pos ht]
    exact ht
  · have htneg : timeComponent v < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
    simp only [futureOrientation, if_neg ht]
    exact neg_pos.mpr htneg

private lemma timelikeTransverse_time (v : Vector 3) (i : Fin 2) :
    timeComponent (timelikeTransverse v i) = 0 := by
  simp [timelikeTransverse, timeComponent_ofSpatialComponent]

private lemma timelikeTransverse_spatial (v : Vector 3) (i : Fin 2) :
    spatialPart (timelikeTransverse v i) =
      (spatialAlignment v).symm (![spatialUnit1, spatialUnit2] i) := by
  simp [timelikeTransverse, spatialPart_ofSpatialComponent]

private lemma timelikeTransverse_norm_sq (v : Vector 3) (i : Fin 2) :
    ⟪timelikeTransverse v i, timelikeTransverse v i⟫ₘ = -1 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, timelikeTransverse_time,
    timelikeTransverse_spatial, LinearIsometryEquiv.norm_map]
  fin_cases i <;>
    simp [spatialUnit1, spatialUnit2]

private lemma timelikeTransverse_orthogonal (v : Vector 3) (i : Fin 2) :
    ⟪v, timelikeTransverse v i⟫ₘ = 0 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart, timelikeTransverse_time,
    mul_zero, zero_sub, timelikeTransverse_spatial]
  have hinner :
      ⟪spatialPart v, (spatialAlignment v).symm (![spatialUnit1, spatialUnit2] i)⟫_ℝ =
        ⟪spatialAlignment v (spatialPart v), ![spatialUnit1, spatialUnit2] i⟫_ℝ := by
    symm
    simpa using (spatialAlignment v).inner_map_map (spatialPart v)
      ((spatialAlignment v).symm (![spatialUnit1, spatialUnit2] i))
  rw [hinner, spatialAlignment_apply]
  fin_cases i
  · simpa [spatialUnit0, spatialUnit1] using
      spatialBasis_first_inner_combination (j := (1 : Fin 3)) (by decide)
        ‖spatialPart v‖ 0 1
  · simpa [spatialUnit0, spatialUnit2] using
      spatialBasis_first_inner_combination (j := (2 : Fin 3)) (by decide)
        ‖spatialPart v‖ 0 1

private lemma futureOrientation_transverse_orthogonal (v : Vector 3) (i : Fin 2) :
    ⟪futureOrientation v, timelikeTransverse v i⟫ₘ = 0 := by
  by_cases ht : 0 < timeComponent v
  · simpa [futureOrientation, ht] using timelikeTransverse_orthogonal v i
  · rw [futureOrientation, if_neg ht]
    simpa using congrArg Neg.neg (timelikeTransverse_orthogonal v i)

/-- The positive null generator of the `i`th hyperbolic plane through a timelike
direction. -/
private def timelikeNullPlus (v : Vector 3) (i : Fin 2) : Vector 3 :=
  futureOrientation v + Real.sqrt ⟪v, v⟫ₘ • timelikeTransverse v i

/-- The negative transverse null generator of the `i`th hyperbolic plane through a
timelike direction. -/
private def timelikeNullMinus (v : Vector 3) (i : Fin 2) : Vector 3 :=
  futureOrientation v - Real.sqrt ⟪v, v⟫ₘ • timelikeTransverse v i

private lemma timelikeNullPlus_null {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ) (i : Fin 2) :
    ⟪timelikeNullPlus v i, timelikeNullPlus v i⟫ₘ = 0 := by
  have hsqrt : (Real.sqrt ⟪v, v⟫ₘ) ^ 2 = ⟪v, v⟫ₘ := Real.sq_sqrt hv.le
  rw [timelikeNullPlus]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [futureOrientation_norm_sq, futureOrientation_transverse_orthogonal,
    minkowskiProduct_symm (timelikeTransverse v i) (futureOrientation v),
    futureOrientation_transverse_orthogonal, timelikeTransverse_norm_sq]
  nlinarith

private lemma timelikeNullMinus_null {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ) (i : Fin 2) :
    ⟪timelikeNullMinus v i, timelikeNullMinus v i⟫ₘ = 0 := by
  have hsqrt : (Real.sqrt ⟪v, v⟫ₘ) ^ 2 = ⟪v, v⟫ₘ := Real.sq_sqrt hv.le
  rw [timelikeNullMinus]
  simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
  rw [futureOrientation_norm_sq, futureOrientation_transverse_orthogonal,
    minkowskiProduct_symm (timelikeTransverse v i) (futureOrientation v),
    futureOrientation_transverse_orthogonal, timelikeTransverse_norm_sq]
  nlinarith

private lemma timelikeNullPlus_time_pos {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ)
    (i : Fin 2) : 0 < timeComponent (timelikeNullPlus v i) := by
  rw [timelikeNullPlus]
  change timeComponent (futureOrientation v) +
    Real.sqrt ⟪v, v⟫ₘ * timeComponent (timelikeTransverse v i) > 0
  rw [timelikeTransverse_time, mul_zero, add_zero]
  exact futureOrientation_time_pos hv

private lemma timelikeNullMinus_time_pos {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ)
    (i : Fin 2) : 0 < timeComponent (timelikeNullMinus v i) := by
  rw [timelikeNullMinus]
  change timeComponent (futureOrientation v) -
    Real.sqrt ⟪v, v⟫ₘ * timeComponent (timelikeTransverse v i) > 0
  rw [timelikeTransverse_time, mul_zero, sub_zero]
  exact futureOrientation_time_pos hv

private lemma timelikeNull_pair_product {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ)
    (i : Fin 2) :
    ⟪timelikeNullPlus v i, timelikeNullMinus v i⟫ₘ = 2 * ⟪v, v⟫ₘ := by
  have hsqrt : (Real.sqrt ⟪v, v⟫ₘ) ^ 2 = ⟪v, v⟫ₘ := Real.sq_sqrt hv.le
  rw [timelikeNullPlus, timelikeNullMinus]
  simp only [map_add, map_sub, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [futureOrientation_norm_sq, futureOrientation_transverse_orthogonal,
    minkowskiProduct_symm (timelikeTransverse v i) (futureOrientation v),
    futureOrientation_transverse_orthogonal, timelikeTransverse_norm_sq]
  nlinarith

private lemma timelike_frame_linearIndependent {v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ) :
    LinearIndependent ℝ ![futureOrientation v, timelikeTransverse v 0,
      timelikeTransverse v 1] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  have ht := congrArg timeComponent hg
  change g 0 * timeComponent (futureOrientation v) +
    g 1 * timeComponent (timelikeTransverse v 0) +
      g 2 * timeComponent (timelikeTransverse v 1) = 0 at ht
  rw [timelikeTransverse_time, timelikeTransverse_time] at ht
  have ht' : g 0 * timeComponent (futureOrientation v) = 0 := by simpa using ht
  have hg0 : g 0 = 0 := (mul_eq_zero.mp ht').resolve_right
    (futureOrientation_time_pos hv).ne'
  rw [hg0, zero_smul, zero_add] at hg
  change g 1 • timelikeTransverse v 0 + g 2 • timelikeTransverse v 1 = 0 at hg
  have hsp0 := congrArg (spatialCLM 3) hg
  rw [map_add, map_smul, map_smul] at hsp0
  change g 1 • spatialPart (timelikeTransverse v 0) +
    g 2 • spatialPart (timelikeTransverse v 1) = 0 at hsp0
  rw [timelikeTransverse_spatial, timelikeTransverse_spatial] at hsp0
  have hsp := congrArg (spatialAlignment v) hsp0
  rw [map_add, map_smul, map_smul,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply] at hsp
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) hsp
  have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 2) hsp
  simp [spatialUnit1, spatialUnit2] at h1 h2
  intro i
  fin_cases i
  · exact hg0
  · exact h1
  · exact h2

private lemma null_pair_linearIndependent {m n : Vector 3}
    (hmQ : ⟪m, m⟫ₘ = 0) (hnQ : ⟪n, n⟫ₘ = 0) (hmn : 0 < ⟪m, n⟫ₘ) :
    LinearIndependent ℝ ![m, n] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hm := congrArg (fun z => ⟪z, m⟫ₘ) hab
  have hn := congrArg (fun z => ⟪z, n⟫ₘ) hab
  simp only [map_add, map_smul] at hm hn
  change a * ⟪m, m⟫ₘ + b * ⟪n, m⟫ₘ = ⟪0, m⟫ₘ at hm
  change a * ⟪m, n⟫ₘ + b * ⟪n, n⟫ₘ = ⟪0, n⟫ₘ at hn
  rw [hmQ] at hm
  rw [hnQ] at hn
  rw [minkowskiProduct_symm n m] at hm
  have hzeroM : ⟪(0 : Vector 3), m⟫ₘ = 0 := by simp
  have hzeroN : ⟪(0 : Vector 3), n⟫ₘ = 0 := by simp
  rw [hzeroM] at hm
  rw [hzeroN] at hn
  have hm' : b * ⟪m, n⟫ₘ = 0 := by simpa using hm
  have hn' : a * ⟪m, n⟫ₘ = 0 := by simpa using hn
  constructor
  · exact (mul_eq_zero.mp hn').resolve_right hmn.ne'
  · exact (mul_eq_zero.mp hm').resolve_right hmn.ne'

private lemma mem_affinePlane_iff_span {p u v x : Vector 3} :
    x ∈ affinePlane p u v ↔ x - p ∈ Submodule.span ℝ ({u, v} : Set (Vector 3)) := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by abel⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, ?_⟩
    calc
      x = p + (x - p) := by abel
      _ = p + (a • u + b • v) := by rw [hab]
      _ = p + a • u + b • v := by module

private lemma common_two_planes_eq_line {S T : Submodule ℝ (Vector 3)}
    (hS : Module.finrank ℝ S = 2) (hT : Module.finrank ℝ T = 2)
    (hne : S ≠ T) {d : Vector 3} (hd0 : d ≠ 0) (hdS : d ∈ S) (hdT : d ∈ T) :
    ∀ z, z ∈ S ∧ z ∈ T ↔ ∃ a : ℝ, z = a • d := by
  let U := S ⊓ T
  have hdU : d ∈ U := ⟨hdS, hdT⟩
  have hUrank : Module.finrank ℝ U ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ Module.finrank ℝ U := by omega
    have hUS : U = S := Submodule.eq_of_le_of_finrank_le inf_le_left (by
      rw [hS]
      exact htwo)
    have hUT : U = T := Submodule.eq_of_le_of_finrank_le inf_le_right (by
      rw [hT]
      exact htwo)
    exact hne (hUS.symm.trans hUT)
  have hspan : ℝ ∙ d = U := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem d U).mpr hdU
    · rw [finrank_span_singleton hd0]
      exact hUrank
  intro z
  rw [show z ∈ S ∧ z ∈ T ↔ z ∈ U by rfl, ← hspan, Submodule.mem_span_singleton]
  constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩

private lemma pairSpan_finrank_eq_two {u v : Vector 3}
    (h : LinearIndependent ℝ ![u, v]) :
    Module.finrank ℝ (Submodule.span ℝ ({u, v} : Set (Vector 3))) = 2 := by
  rw [show ({u, v} : Set (Vector 3)) = Set.range ![u, v] by ext z; simp [or_comm]]
  rw [finrank_span_eq_card h]
  simp

private lemma image_futureNull_pair_product_pos
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p m n : Vector 3} (hmQ : ⟪m, m⟫ₘ = 0) (hnQ : ⟪n, n⟫ₘ = 0)
    (hmT : 0 ≤ timeComponent m) (hnT : 0 ≤ timeComponent n)
    (hmn : 0 < ⟪m, n⟫ₘ) :
    0 < ⟪φ (p + m) - φ p, φ (p + n) - φ p⟫ₘ := by
  let M := φ (p + m) - φ p
  let N := φ (p + n) - φ p
  have hMBoundary : φ (p + m) ∈ futureLightConeBoundary (φ p) :=
    (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + m)).mpr ⟨
      (lightLike_iff_norm_sq_zero _).mpr (by simpa using hmQ), by simpa using hmT⟩
  have hNBoundary : φ (p + n) ∈ futureLightConeBoundary (φ p) :=
    (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + n)).mpr ⟨
      (lightLike_iff_norm_sq_zero _).mpr (by simpa using hnQ), by simpa using hnT⟩
  have hMQ : ⟪M, M⟫ₘ = 0 := (lightLike_iff_norm_sq_zero _).mp hMBoundary.1
  have hNQ : ⟪N, N⟫ₘ = 0 := (lightLike_iff_norm_sq_zero _).mp hNBoundary.1
  have hnonneg : 0 ≤ ⟪M, N⟫ₘ :=
    minkowskiProduct_nonneg_of_futureCausal hMQ.ge hNQ.ge hMBoundary.2 hNBoundary.2
  have hne : ⟪M, N⟫ₘ ≠ 0 := by
    intro hzero
    have himageQ : ⟪N - M, N - M⟫ₘ = 0 := by
      have h := null_connector_norm_sq hMQ hNQ (1 : ℝ) (1 : ℝ)
      simpa only [one_smul, one_mul, mul_one, hzero, mul_zero] using h
    have hsourceQ := (nullSeparation_iff_of_causalAutomorphism hφ (p + m) (p + n)).mp
      (by simpa [M, N] using himageQ)
    have hsourceExpand := null_connector_norm_sq hmQ hnQ (1 : ℝ) (1 : ℝ)
    have : -2 * ⟪m, n⟫ₘ = 0 := by
      calc
        -2 * ⟪m, n⟫ₘ = ⟪n - m, n - m⟫ₘ := by
          simpa only [one_smul, one_mul, mul_one] using hsourceExpand.symm
        _ = 0 := by simpa using hsourceQ
    nlinarith
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private lemma mem_affineLine_iff_two_affinePlanes {p d u₀ v₀ u₁ v₁ x : Vector 3}
    (hS₀ : Module.finrank ℝ (Submodule.span ℝ ({u₀, v₀} : Set (Vector 3))) = 2)
    (hS₁ : Module.finrank ℝ (Submodule.span ℝ ({u₁, v₁} : Set (Vector 3))) = 2)
    (hne : Submodule.span ℝ ({u₀, v₀} : Set (Vector 3)) ≠
      Submodule.span ℝ ({u₁, v₁} : Set (Vector 3)))
    (hd0 : d ≠ 0)
    (hd₀ : d ∈ Submodule.span ℝ ({u₀, v₀} : Set (Vector 3)))
    (hd₁ : d ∈ Submodule.span ℝ ({u₁, v₁} : Set (Vector 3))) :
    x ∈ affineLine p d ↔ x ∈ affinePlane p u₀ v₀ ∧ x ∈ affinePlane p u₁ v₁ := by
  have hcommon := common_two_planes_eq_line hS₀ hS₁ hne hd0 hd₀ hd₁ (x - p)
  rw [mem_affinePlane_iff_span, mem_affinePlane_iff_span]
  constructor
  · rintro ⟨a, rfl⟩
    apply hcommon.mpr
    exact ⟨a, by abel⟩
  · intro hx
    rcases hcommon.mp hx with ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; abel⟩

/-- A bare causal automorphism maps every timelike affine line exactly onto the affine
line through the images of its base point and unit parameter point. Two constructively
chosen hyperbolic planes recover the line as their one-dimensional intersection. -/
@[zil_level physical_theorem]
theorem timelikeAffineLine_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p v : Vector 3} (hv : 0 < ⟪v, v⟫ₘ) :
    φ '' affineLine p v = affineLine (φ p) (φ (p + v) - φ p) := by
  let m : Fin 2 → Vector 3 := timelikeNullPlus v
  let n : Fin 2 → Vector 3 := timelikeNullMinus v
  let S : Fin 2 → Submodule ℝ (Vector 3) :=
    fun i => Submodule.span ℝ ({m i, n i} : Set (Vector 3))
  let M : Fin 2 → Vector 3 := fun i => φ (p + m i) - φ p
  let N : Fin 2 → Vector 3 := fun i => φ (p + n i) - φ p
  let T : Fin 2 → Submodule ℝ (Vector 3) :=
    fun i => Submodule.span ℝ ({M i, N i} : Set (Vector 3))
  let d := φ (p + v) - φ p
  have hmQ (i : Fin 2) : ⟪m i, m i⟫ₘ = 0 := timelikeNullPlus_null hv i
  have hnQ (i : Fin 2) : ⟪n i, n i⟫ₘ = 0 := timelikeNullMinus_null hv i
  have hmT (i : Fin 2) : 0 < timeComponent (m i) := timelikeNullPlus_time_pos hv i
  have hnT (i : Fin 2) : 0 < timeComponent (n i) := timelikeNullMinus_time_pos hv i
  have hmn (i : Fin 2) : 0 < ⟪m i, n i⟫ₘ := by
    rw [timelikeNull_pair_product hv]
    positivity
  have hSrank (i : Fin 2) : Module.finrank ℝ (S i) = 2 := by
    exact pairSpan_finrank_eq_two (null_pair_linearIndependent (hmQ i) (hnQ i) (hmn i))
  have hvS (i : Fin 2) : v ∈ S i := by
    rw [Submodule.mem_span_pair]
    by_cases ht : 0 < timeComponent v
    · refine ⟨(2 : ℝ)⁻¹, 2⁻¹, ?_⟩
      simp only [m, n, timelikeNullPlus, timelikeNullMinus, futureOrientation, if_pos ht]
      module
    · refine ⟨-(2 : ℝ)⁻¹, -2⁻¹, ?_⟩
      simp only [m, n, timelikeNullPlus, timelikeNullMinus, futureOrientation, if_neg ht]
      module
  have hSne : S 0 ≠ S 1 := by
    intro hS
    have hsqrt : 0 < Real.sqrt ⟪v, v⟫ₘ := Real.sqrt_pos.2 hv
    have hs1 : Real.sqrt ⟪v, v⟫ₘ • timelikeTransverse v 1 ∈ S 1 := by
      rw [Submodule.mem_span_pair]
      refine ⟨(2 : ℝ)⁻¹, -(2 : ℝ)⁻¹, ?_⟩
      simp only [m, n, timelikeNullPlus, timelikeNullMinus]
      module
    rw [← hS, Submodule.mem_span_pair] at hs1
    rcases hs1 with ⟨a, b, hab⟩
    have hrel : (a + b) • futureOrientation v +
        ((a - b) * Real.sqrt ⟪v, v⟫ₘ) • timelikeTransverse v 0 +
          (-Real.sqrt ⟪v, v⟫ₘ) • timelikeTransverse v 1 = 0 := by
      calc
        _ = a • m 0 + b • n 0 -
            Real.sqrt ⟪v, v⟫ₘ • timelikeTransverse v 1 := by
          simp only [m, n, timelikeNullPlus, timelikeNullMinus]
          module
        _ = 0 := by rw [hab]; module
    have hcoeff := Fintype.linearIndependent_iff.mp (timelike_frame_linearIndependent hv)
      ![a + b, (a - b) * Real.sqrt ⟪v, v⟫ₘ, -Real.sqrt ⟪v, v⟫ₘ] (by
        simpa [Fin.sum_univ_three] using hrel)
    have hlast := hcoeff 2
    simp at hlast
    exact hsqrt.ne' hlast
  have hMprod (i : Fin 2) : 0 < ⟪M i, N i⟫ₘ := by
    exact image_futureNull_pair_product_pos hφ (hmQ i) (hnQ i) (hmT i).le
      (hnT i).le (hmn i)
  have hMQ (i : Fin 2) : ⟪M i, M i⟫ₘ = 0 :=
    (nullSeparation_iff_of_causalAutomorphism hφ p (p + m i)).mpr (by simpa using hmQ i)
  have hNQ (i : Fin 2) : ⟪N i, N i⟫ₘ = 0 :=
    (nullSeparation_iff_of_causalAutomorphism hφ p (p + n i)).mpr (by simpa using hnQ i)
  have hTrank (i : Fin 2) : Module.finrank ℝ (T i) = 2 := by
    exact pairSpan_finrank_eq_two (null_pair_linearIndependent (hMQ i) (hNQ i) (hMprod i))
  have hplane (i : Fin 2) : φ '' affinePlane p (m i) (n i) =
      affinePlane (φ p) (M i) (N i) := by
    exact hyperbolicAffinePlane_image_of_causalAutomorphism hφ (hmQ i) (hnQ i)
      (hmT i).le (hnT i).le (by intro h; simpa [h] using hmT i)
      (by intro h; simpa [h] using hnT i) (hmn i)
  have hTne : T 0 ≠ T 1 := by
    intro hT
    have htargetPlane : affinePlane (φ p) (M 0) (N 0) =
        affinePlane (φ p) (M 1) (N 1) := by
      ext z
      rw [mem_affinePlane_iff_span, mem_affinePlane_iff_span]
      change z - φ p ∈ T 0 ↔ z - φ p ∈ T 1
      rw [hT]
    have himagePlane : φ '' affinePlane p (m 0) (n 0) =
        φ '' affinePlane p (m 1) (n 1) := (hplane 0).trans (htargetPlane.trans (hplane 1).symm)
    have hsourcePlane : affinePlane p (m 0) (n 0) = affinePlane p (m 1) (n 1) :=
      (Set.image_injective.mpr hφ.1.injective) himagePlane
    apply hSne
    ext z
    calc
      z ∈ S 0 ↔ p + z ∈ affinePlane p (m 0) (n 0) := by
        rw [mem_affinePlane_iff_span]
        simp [S]
      _ ↔ p + z ∈ affinePlane p (m 1) (n 1) := Set.ext_iff.mp hsourcePlane (p + z)
      _ ↔ z ∈ S 1 := by
        rw [mem_affinePlane_iff_span]
        simp [S]
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hd0 : d ≠ 0 := by
    apply sub_ne_zero.mpr
    exact hφ.1.injective.ne (by
      intro hpv
      apply hv0
      simpa only [add_eq_left] using hpv)
  have hdT (i : Fin 2) : d ∈ T i := by
    have hpvPlane : p + v ∈ affinePlane p (m i) (n i) :=
      (mem_affinePlane_iff_span).mpr (by simpa [S] using hvS i)
    have himage : φ (p + v) ∈ affinePlane (φ p) (M i) (N i) := by
      rw [← hplane i]
      exact ⟨p + v, hpvPlane, rfl⟩
    exact (mem_affinePlane_iff_span).mp himage
  have hsource (x : Vector 3) : x ∈ affineLine p v ↔
      x ∈ affinePlane p (m 0) (n 0) ∧ x ∈ affinePlane p (m 1) (n 1) :=
    mem_affineLine_iff_two_affinePlanes (hSrank 0) (hSrank 1) hSne hv0 (hvS 0) (hvS 1)
  have htarget (x : Vector 3) : x ∈ affineLine (φ p) d ↔
      x ∈ affinePlane (φ p) (M 0) (N 0) ∧ x ∈ affinePlane (φ p) (M 1) (N 1) :=
    mem_affineLine_iff_two_affinePlanes (hTrank 0) (hTrank 1) hTne hd0 (hdT 0) (hdT 1)
  have hincidence (i : Fin 2) (x : Vector 3) :
      x ∈ affinePlane p (m i) (n i) ↔ φ x ∈ affinePlane (φ p) (M i) (N i) := by
    constructor
    · intro hx
      rw [← hplane i]
      exact ⟨x, hx, rfl⟩
    · intro hx
      have hxImage : φ x ∈ φ '' affinePlane p (m i) (n i) := by rwa [hplane i]
      rcases hxImage with ⟨y, hy, hxy⟩
      exact hφ.1.injective hxy ▸ hy
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (htarget (φ x)).mpr
    exact ⟨(hincidence 0 x).mp ((hsource x).mp hx).1,
      (hincidence 1 x).mp ((hsource x).mp hx).2⟩
  · intro hz
    obtain ⟨x, rfl⟩ := hφ.1.surjective z
    refine ⟨x, (hsource x).mpr ?_, rfl⟩
    exact ⟨(hincidence 0 x).mpr ((htarget (φ x)).mp hz).1,
      (hincidence 1 x).mpr ((htarget (φ x)).mp hz).2⟩

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach nullSeparation_iff_of_causalAutomorphism where
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_mem_iff_of_causalAutomorphism",
  formalizes @ "claim:a-bare-causal-automorphism-of-three-plus-one-minkowski-space-\
preserves-unoriented-null-separation-in-both-directions",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_mem_iff_of_causalAutomorphism"

zil attach nullConeAt_image_of_causalAutomorphism where
  supported_by @ "lean:nullSeparation_iff_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:a-bare-causal-automorphism-maps-every-complete-unoriented-null-cone-\
exactly-onto-the-null-cone-at-the-image-vertex",
  supported_by @ "lean:Lorentz.Vector.nullSeparation_iff_of_causalAutomorphism"

zil attach mem_nullOrthogonalHyperplane_iff_incidence where
  formalizes @ "claim:a-null-tangent-hyperplane-is-reconstructed-as-the-null-line-together-\
with-the-points-having-no-null-separated-point-on-that-line",
  supported_by @ "lean:Lorentz.Vector.futureCausal_null_sameRay_of_mink_zero"

zil attach nullOrthogonalHyperplane_image_of_causalAutomorphism where
  supported_by @ "lean:mem_nullOrthogonalHyperplane_iff_incidence",
  formalizes @ "claim:a-bare-causal-automorphism-maps-every-null-tangent-affine-\
hyperplane-exactly-onto-the-tangent-hyperplane-along-the-image-null-line",
  supported_by @ "lean:Lorentz.Vector.mem_nullOrthogonalHyperplane_iff_incidence",
  supported_by @ "lean:Lorentz.Vector.nullAffineLine_image_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.nullSeparation_iff_of_causalAutomorphism"

zil attach exists_spacelike_null_normal_frame where
  supported_by @ "lean:nullAffineLine_image_of_causalAutomorphism",
  supported_by @ "lean:nullSeparation_iff_of_causalAutomorphism",
  formalizes @ "claim:every-spacelike-direction-in-three-plus-one-minkowski-space-has-\
three-linearly-independent-future-null-normals",
  supported_by @ "lean:Lorentz.Vector.minkowskiProduct"

zil attach spacelikeAffineLine_image_of_causalAutomorphism where
  supported_by @ "lean:nullAffineLine_image_of_causalAutomorphism",
  supported_by @ "lean:nullOrthogonalHyperplane_image_of_causalAutomorphism",
  formalizes @ "claim:a-bare-causal-automorphism-maps-every-complete-spacelike-affine-\
line-exactly-onto-the-line-through-its-image-endpoints",
  supported_by @ "lean:Lorentz.Vector.exists_spacelike_null_normal_frame",
  supported_by @ "lean:Lorentz.Vector.nullOrthogonalHyperplane_image_of_causalAutomorphism"

zil attach hyperbolicAffinePlane_image_of_causalAutomorphism where
  supported_by @ "lean:minkowskiProduct_nonneg_of_futureCausal",
  supported_by @ "lean:nullSeparation_iff_of_causalAutomorphism",
  formalizes @ "claim:a-bare-causal-automorphism-maps-every-hyperbolic-affine-plane-\
generated-by-two-nonorthogonal-future-null-directions-onto-its-image-plane",
  supported_by @ "lean:Lorentz.Vector.nullAffineLine_image_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.spacelikeAffineLine_image_of_causalAutomorphism"

zil attach timelikeAffineLine_image_of_causalAutomorphism where
  supported_by @ "lean:hyperbolicAffinePlane_image_of_causalAutomorphism",
  supported_by @ "lean:nullSeparation_iff_of_causalAutomorphism",
  formalizes @ "claim:a-bare-causal-automorphism-maps-every-complete-timelike-affine-\
line-exactly-onto-the-line-through-its-image-endpoints",
  supported_by @ "lean:Lorentz.Vector.hyperbolicAffinePlane_image_of_causalAutomorphism"

/- ZIL-END -/
