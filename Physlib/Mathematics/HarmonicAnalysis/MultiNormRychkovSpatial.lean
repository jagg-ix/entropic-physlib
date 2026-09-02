/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual

/-!
# Physical-space formulas for the Rychkov dual kernels

This module converts the Fourier polynomials of equations (4.2)--(4.3) into
finite sums of the repository's existing Schwartz convolutions.  It then
reuses Mathlib's compact-support theorem for ordinary convolution to prove
that every constructed tilded kernel has compact spatial support.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Convolution FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormRychkovSpatial

open MultiNormDualCalderon MultiNormMomentDerivative MultiNormRychkovDual
  MultiNormSchwartzKernel MultiNormTemperedCalderon

/-- Compact support of the function underlying a bundled Schwartz map.  This
wrapper keeps coercion reduction out of public theorem elaboration. -/
def HasCompactSchwartzSupport {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) : Prop :=
  HasCompactSupport (fun x => f x)

lemma fourier_sub {d : ℕ} (f g : 𝓢(CoordinateSpace d, ℂ)) :
    𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  simpa only [FourierTransform.fourierCLE_apply] using
    map_sub (FourierTransform.fourierCLE ℂ
      𝓢(CoordinateSpace d, ℂ)) f g

lemma fourier_finset_sum {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → 𝓢(CoordinateSpace d, ℂ)) :
    𝓕 (∑ i ∈ s, f i) = ∑ i ∈ s, 𝓕 (f i) := by
  simpa only [FourierTransform.fourierCLE_apply] using
    map_sum (FourierTransform.fourierCLE ℂ
      𝓢(CoordinateSpace d, ℂ)) f s

lemma fourier_finset_sum_apply {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → 𝓢(CoordinateSpace d, ℂ))
    (ξ : CoordinateSpace d) :
    𝓕 (∑ i ∈ s, f i) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, FourierTransform.fourier_add, add_apply,
        Finset.sum_insert ha, ih]

/-! ## A. Residual convolution powers -/

/-- Applying the spatial residual `I - residual * ·` exactly `k` times to a
Schwartz kernel.  Its Fourier transform is
`F(base) * (1 - F(residual))^k`. -/
def residualConvolutionApply {d : ℕ}
    (residual base : 𝓢(CoordinateSpace d, ℂ)) :
    ℕ → 𝓢(CoordinateSpace d, ℂ)
  | 0 => base
  | k + 1 => residualConvolutionApply residual base k -
      SchwartzMap.convolution (.mul ℂ ℂ) residual
        (residualConvolutionApply residual base k)

lemma fourier_residualConvolutionApply_apply {d : ℕ}
    (residual base : 𝓢(CoordinateSpace d, ℂ))
    (k : ℕ) (ξ : CoordinateSpace d) :
    𝓕 (residualConvolutionApply residual base k) ξ =
      𝓕 base ξ * (1 - 𝓕 residual ξ) ^ k := by
  induction k with
  | zero => simp [residualConvolutionApply]
  | succ k ih =>
      rw [residualConvolutionApply, fourier_sub,
        sub_apply,
        SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
      simp only [ih, ContinuousLinearMap.mul_apply']
      ring

/-! ## B. Exact physical-space formulas -/

/-- The finite physical-space polynomial for the final approximation
convolution in equation (4.3). -/
def rychkovApproximationSpatialPolynomial {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  let g := SchwartzMap.convolution (.mul ℂ ℂ)
    (complexDyadicApproximationKernel φ ell)
    (complexDyadicApproximationKernel φ ell)
  ∑ k ∈ Finset.range M, residualConvolutionApply g g k

/-- The constructed final approximation convolution is exactly its finite
physical-space residual polynomial, not merely Fourier-equivalent data. -/
lemma dualApproximationConvolution_eq_spatialPolynomial {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    dualApproximationConvolution φ (rychkovDualApproximation φ M) ell =
      rychkovApproximationSpatialPolynomial φ M ell := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (dualApproximationConvolution φ
    (rychkovDualApproximation φ M) ell) =
      𝓕 (rychkovApproximationSpatialPolynomial φ M ell)
  ext ξ
  rw [fourier_dualApproximationConvolution_rychkov_apply]
  simp only [rychkovApproximationSpatialPolynomial, fourier_finset_sum_apply,
    fourier_residualConvolutionApply_apply]
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  simp [approximationFactor, pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The finite physical-space polynomial for a tilded approximation kernel
in equation (4.2). -/
def rychkovDualApproximationSpatialPolynomial {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  let base := complexDyadicApproximationKernel φ ell
  let residual := SchwartzMap.convolution (.mul ℂ ℂ) base base
  ∑ k ∈ Finset.range M, residualConvolutionApply residual base k

lemma rychkovDualApproximation_eq_spatialPolynomial {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    rychkovDualApproximation φ M ell =
      rychkovDualApproximationSpatialPolynomial φ M ell := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (rychkovDualApproximation φ M ell) =
    𝓕 (rychkovDualApproximationSpatialPolynomial φ M ell)
  ext ξ
  rw [fourier_rychkovDualApproximation]
  simp only [rychkovDualApproximationSpatialPolynomial, fourier_finset_sum_apply,
    fourier_residualConvolutionApply_apply]
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  simp [approximationFrequencyFactor_apply, approximationFactor, pow_two,
    Finset.mul_sum]

/-- The two-residual physical-space polynomial for a positive-level tilded
detail kernel in equation (4.2). -/
def rychkovDualDetailSuccSpatialPolynomial {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  let previous := complexDyadicApproximationKernel φ ell
  let current := complexDyadicApproximationKernel φ (ell + 1)
  let previousSquare := SchwartzMap.convolution (.mul ℂ ℂ) previous previous
  let currentSquare := SchwartzMap.convolution (.mul ℂ ℂ) current current
  ∑ k ∈ Finset.range M,
    residualConvolutionApply previousSquare
      (residualConvolutionApply currentSquare (current + previous)
        (M - 1 - k)) k

lemma rychkovDualDetail_succ_eq_spatialPolynomial {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    rychkovDualDetail φ M (ell + 1) =
      rychkovDualDetailSuccSpatialPolynomial φ M ell := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (rychkovDualDetail φ M (ell + 1)) =
    𝓕 (rychkovDualDetailSuccSpatialPolynomial φ M ell)
  ext ξ
  rw [fourier_rychkovDualDetail_succ]
  simp only [rychkovDualDetailSuccSpatialPolynomial, fourier_finset_sum_apply,
    fourier_residualConvolutionApply_apply]
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  simp [detailFrequencyFactor_apply, detailFactor, pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ## C. Compact spatial support -/

lemma complexDyadicApproximationKernel_hasCompactSupport {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (ell : ℕ) :
    HasCompactSupport (complexDyadicApproximationKernel φ ell) := by
  have hcomp : HasCompactSupport (fun x : CoordinateSpace d =>
      φ.normed volume (dyadicExpansionCLE ell x)) := by
    simpa [Function.comp_def] using
      φ.hasCompactSupport_normed.comp_homeomorph
        (dyadicExpansionCLE ell).toHomeomorph
  have hreal : HasCompactSupport (dyadicApproximationKernel φ ell) := by
    have hscaled := hcomp.smul_left
      (f := fun _ : CoordinateSpace d =>
        dyadicExpansion ell ^ Module.finrank ℝ (CoordinateSpace d))
    have heq :
        ((fun _ : CoordinateSpace d =>
          dyadicExpansion ell ^ Module.finrank ℝ (CoordinateSpace d)) •
            fun x => φ.normed volume (dyadicExpansionCLE ell x)) =
          fun x => dyadicApproximationKernel φ ell x := by
      funext x
      simp only [Pi.mul_apply, smul_eq_mul, dyadicApproximationKernel_apply,
        dyadicExpansionCLE_apply]
    change HasCompactSupport (fun x => dyadicApproximationKernel φ ell x)
    rw [← heq]
    exact hscaled
  have hc : HasCompactSupport
      (Complex.ofReal ∘ fun x => dyadicApproximationKernel φ ell x) :=
    hreal.comp_left Complex.ofReal_zero
  have heq :
      (Complex.ofReal ∘ fun x => dyadicApproximationKernel φ ell x) =
        fun x => complexDyadicApproximationKernel φ ell x := by
    funext x
    simp only [Function.comp_apply, complexDyadicApproximationKernel,
      SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply]
  change HasCompactSupport (fun x => complexDyadicApproximationKernel φ ell x)
  rw [← heq]
  exact hc

/-- Compact support of the repository's bundled Schwartz convolution follows
from Mathlib's function-level convolution theorem. -/
lemma schwartzConvolution_hasCompactSupport {d : ℕ}
    {f g : 𝓢(CoordinateSpace d, ℂ)}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (SchwartzMap.convolution (.mul ℂ ℂ) f g) := by
  have hc : HasCompactSupport (f ⋆[(.mul ℂ ℂ)] g) :=
    hf.convolution (.mul ℂ ℂ) hg
  have heq :
      (fun x => SchwartzMap.convolution (.mul ℂ ℂ) f g x) =
        (f ⋆[(.mul ℂ ℂ)] g) := by
    funext x
    exact SchwartzMap.convolution_apply (.mul ℂ ℂ) f g x
  change HasCompactSupport
    (fun x => SchwartzMap.convolution (.mul ℂ ℂ) f g x)
  rw [heq]
  exact hc

lemma residualConvolutionApply_hasCompactSupport {d : ℕ}
    {residual base : 𝓢(CoordinateSpace d, ℂ)}
    (hr : HasCompactSupport residual) (hb : HasCompactSupport base)
    (k : ℕ) : HasCompactSupport (residualConvolutionApply residual base k) := by
  induction k with
  | zero => simpa [residualConvolutionApply] using hb
  | succ k ih =>
      rw [residualConvolutionApply]
      exact ih.sub (schwartzConvolution_hasCompactSupport hr ih)

lemma hasCompactSupport_finset_sum {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → 𝓢(CoordinateSpace d, ℂ))
    (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change HasCompactSupport (0 : CoordinateSpace d → ℂ)
      exact HasCompactSupport.zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma hasCompactSchwartzSupport_finset_sum {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → 𝓢(CoordinateSpace d, ℂ))
    (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSchwartzSupport (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold HasCompactSchwartzSupport
      change HasCompactSupport (0 : CoordinateSpace d → ℂ)
      exact HasCompactSupport.zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      unfold HasCompactSchwartzSupport at ih ⊢
      change HasCompactSupport
        (⇑(f a) + fun x => (∑ i ∈ s, f i) x)
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma rychkovApproximationSpatialPolynomial_hasCompactSupport {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    HasCompactSchwartzSupport (rychkovApproximationSpatialPolynomial φ M ell) := by
  let g := SchwartzMap.convolution (.mul ℂ ℂ)
    (complexDyadicApproximationKernel φ ell)
    (complexDyadicApproximationKernel φ ell)
  have hg : HasCompactSupport g := schwartzConvolution_hasCompactSupport
    (complexDyadicApproximationKernel_hasCompactSupport φ ell)
    (complexDyadicApproximationKernel_hasCompactSupport φ ell)
  unfold rychkovApproximationSpatialPolynomial
  apply hasCompactSchwartzSupport_finset_sum
  intro k hk
  exact residualConvolutionApply_hasCompactSupport hg hg k

/-- Every constructed tilded approximation is compactly supported in physical
space, derived from the finite convolution formula rather than assumed. -/
lemma rychkovDualApproximation_hasCompactSupport {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    HasCompactSchwartzSupport (rychkovDualApproximation φ M ell) := by
  rw [rychkovDualApproximation_eq_spatialPolynomial]
  let base := complexDyadicApproximationKernel φ ell
  let residual := SchwartzMap.convolution (.mul ℂ ℂ) base base
  have hb : HasCompactSupport base :=
    complexDyadicApproximationKernel_hasCompactSupport φ ell
  have hr : HasCompactSupport residual :=
    schwartzConvolution_hasCompactSupport hb hb
  unfold rychkovDualApproximationSpatialPolynomial
  apply hasCompactSchwartzSupport_finset_sum
  intro k hk
  exact residualConvolutionApply_hasCompactSupport hr hb k

/-- Every constructed tilded detail, including level zero, is compactly
supported in physical space. -/
lemma rychkovDualDetail_hasCompactSupport {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    HasCompactSchwartzSupport (rychkovDualDetail φ M ell) := by
  cases ell with
  | zero =>
      simpa [rychkovDualDetail] using
        rychkovDualApproximation_hasCompactSupport φ M 0
  | succ ell =>
      rw [rychkovDualDetail_succ_eq_spatialPolynomial]
      let previous := complexDyadicApproximationKernel φ ell
      let current := complexDyadicApproximationKernel φ (ell + 1)
      let previousSquare := SchwartzMap.convolution (.mul ℂ ℂ) previous previous
      let currentSquare := SchwartzMap.convolution (.mul ℂ ℂ) current current
      have hp : HasCompactSupport previous :=
        complexDyadicApproximationKernel_hasCompactSupport φ ell
      have hc : HasCompactSupport current :=
        complexDyadicApproximationKernel_hasCompactSupport φ (ell + 1)
      have hps : HasCompactSupport previousSquare :=
        schwartzConvolution_hasCompactSupport hp hp
      have hcs : HasCompactSupport currentSquare :=
        schwartzConvolution_hasCompactSupport hc hc
      unfold rychkovDualDetailSuccSpatialPolynomial
      apply hasCompactSchwartzSupport_finset_sum
      intro k hk
      have hbase : HasCompactSupport (current + previous) := hc.add hp
      have hinner : HasCompactSupport
          (residualConvolutionApply currentSquare (current + previous)
            (M - 1 - k)) :=
        residualConvolutionApply_hasCompactSupport hcs hbase (M - 1 - k)
      exact residualConvolutionApply_hasCompactSupport hps hinner k

/-- Lemma 4.2(f), compact-support portion: all actual constructed tilded
kernels and all final approximation convolutions have compact spatial
support.  A uniform explicit dilate bound is a separate quantitative result. -/
lemma rychkov_constructed_spatial_compactSupport {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) :
    (∀ ell, HasCompactSchwartzSupport
      (rychkovDualApproximation φ M ell)) ∧
    (∀ ell, HasCompactSchwartzSupport
      (rychkovDualDetail φ M ell)) ∧
    (∀ ell, HasCompactSchwartzSupport
      (dualApproximationConvolution φ (rychkovDualApproximation φ M) ell)) := by
  refine ⟨rychkovDualApproximation_hasCompactSupport φ M,
    rychkovDualDetail_hasCompactSupport φ M, ?_⟩
  intro ell
  rw [dualApproximationConvolution_eq_spatialPolynomial]
  exact rychkovApproximationSpatialPolynomial_hasCompactSupport φ M ell

end MultiNormRychkovSpatial

end Physlib.Mathematics.HarmonicAnalysis
