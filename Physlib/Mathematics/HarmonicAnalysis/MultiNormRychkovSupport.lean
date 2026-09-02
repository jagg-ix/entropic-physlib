/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit

/-! # Uniform spatial support for the constructed Rychkov kernels -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Convolution FourierTransform SchwartzMap Topology Pointwise

namespace Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport

open MultiNormDualCalderon MultiNormMomentDerivative MultiNormRychkovDual
  MultiNormRychkovSpatial MultiNormSchwartzKernel MultiNormTemperedCalderon

lemma complexDyadicApproximationKernel_tsupport_subset_closedBall {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (ell : ℕ) :
    tsupport (complexDyadicApproximationKernel φ ell) ⊆
      Metric.closedBall 0 φ.rOut := by
  apply closure_minimal
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hnorm
    have hxnorm : φ.rOut < ‖x‖ := lt_of_not_ge hnorm
    have hscale : φ.rOut < ‖dyadicExpansion ell • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (dyadicExpansion_pos ell).le]
      have hone : 1 ≤ dyadicExpansion ell := by
        exact one_le_pow₀ (by norm_num)
      nlinarith [norm_nonneg x]
    have hout : dyadicExpansion ell • x ∉ Metric.closedBall 0 φ.rOut := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hscale
    have hzero : φ.normed volume (dyadicExpansion ell • x) = 0 := by
      by_contra hne
      have hmem : dyadicExpansion ell • x ∈
          Function.support (φ.normed volume) := by
        simpa [Function.mem_support] using hne
      rw [φ.support_normed_eq] at hmem
      exact hout (Metric.ball_subset_closedBall hmem)
    exact hx (by simp [complexDyadicApproximationKernel_apply, hzero])
  · exact Metric.isClosed_closedBall

lemma schwartzConvolution_tsupport_subset_closedBall {d : ℕ}
    {f g : 𝓢(CoordinateSpace d, ℂ)} {rf rg : ℝ}
    (hf : tsupport f ⊆ Metric.closedBall 0 rf)
    (hg : tsupport g ⊆ Metric.closedBall 0 rg) :
    tsupport (SchwartzMap.convolution (.mul ℂ ℂ) f g) ⊆
      Metric.closedBall 0 (rf + rg) := by
  apply closure_minimal
  · intro x hx
    have hconv : Function.support (f ⋆[(.mul ℂ ℂ)] g) ⊆
        Function.support f + Function.support g :=
      support_convolution_subset (.mul ℂ ℂ)
    have heq : SchwartzMap.convolution (.mul ℂ ℂ) f g x =
        (f ⋆[(.mul ℂ ℂ)] g) x :=
      SchwartzMap.convolution_apply (.mul ℂ ℂ) f g x
    rw [Function.mem_support] at hx
    have hx' : x ∈ Function.support (f ⋆[(.mul ℂ ℂ)] g) := by
      rw [Function.mem_support]
      rwa [← heq]
    rcases hconv hx' with ⟨y, hy, z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le y z).trans
      (add_le_add
        (by simpa [dist_zero_right] using
          (Metric.mem_closedBall.mp (hf (subset_closure hy))))
        (by simpa [dist_zero_right] using
          (Metric.mem_closedBall.mp (hg (subset_closure hz)))))
  · exact Metric.isClosed_closedBall

lemma residualConvolutionApply_tsupport_subset_closedBall {d : ℕ}
    {residual base : 𝓢(CoordinateSpace d, ℂ)} {rr rb : ℝ}
    (hr : 0 ≤ rr) (hresidual : tsupport residual ⊆ Metric.closedBall 0 rr)
    (hbase : tsupport base ⊆ Metric.closedBall 0 rb) (k : ℕ) :
    tsupport (residualConvolutionApply residual base k) ⊆
      Metric.closedBall 0 (rb + k * rr) := by
  induction k with
  | zero => simpa [residualConvolutionApply] using hbase
  | succ k ih =>
      rw [residualConvolutionApply]
      refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
      · exact ih.trans (Metric.closedBall_subset_closedBall (by
          push_cast
          nlinarith))
      · exact (schwartzConvolution_tsupport_subset_closedBall hresidual ih).trans
          (Metric.closedBall_subset_closedBall (by
            push_cast
            nlinarith))

lemma finset_sum_tsupport_subset_closedBall {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → 𝓢(CoordinateSpace d, ℂ)) {r : ℝ}
    (h : ∀ i ∈ s, tsupport (f i) ⊆ Metric.closedBall 0 r) :
    tsupport ((∑ i ∈ s, f i : 𝓢(CoordinateSpace d, ℂ)) :
      CoordinateSpace d → ℂ) ⊆ Metric.closedBall 0 r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show ((0 : 𝓢(CoordinateSpace d, ℂ)) : CoordinateSpace d → ℂ) = 0 by rfl]
      simp [tsupport]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (tsupport_add _ _).trans (Set.union_subset
        (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The paper's explicit support dilation factor.  The coarse coefficient
`4M+1` uniformly covers every convolution monomial in both formula (4.2)
families. -/
def rychkovSpatialDilationFactor (M : ℕ) : ℝ := 4 * M + 1

def rychkovSpatialCarrier {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) :
    Set (CoordinateSpace d) :=
  Metric.closedBall 0 (rychkovSpatialDilationFactor M * φ.rOut)

lemma rychkovDualApproximation_tsupport_subset_spatialCarrier {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    tsupport (rychkovDualApproximation φ M ell) ⊆
      rychkovSpatialCarrier φ M := by
  rw [rychkovDualApproximation_eq_spatialPolynomial]
  let base := complexDyadicApproximationKernel φ ell
  let residual := SchwartzMap.convolution (.mul ℂ ℂ) base base
  have hr : 0 ≤ φ.rOut := φ.rOut_pos.le
  have hbase : tsupport base ⊆ Metric.closedBall 0 φ.rOut :=
    complexDyadicApproximationKernel_tsupport_subset_closedBall φ ell
  have hresidual : tsupport residual ⊆ Metric.closedBall 0 (2 * φ.rOut) := by
    simpa [two_mul] using
      (schwartzConvolution_tsupport_subset_closedBall hbase hbase)
  unfold rychkovDualApproximationSpatialPolynomial rychkovSpatialCarrier
  change tsupport ((∑ k ∈ Finset.range M,
    residualConvolutionApply residual base k : 𝓢(CoordinateSpace d, ℂ)) :
      CoordinateSpace d → ℂ) ⊆
      Metric.closedBall 0 (rychkovSpatialDilationFactor M * φ.rOut)
  apply finset_sum_tsupport_subset_closedBall
  intro k hk
  refine (residualConvolutionApply_tsupport_subset_closedBall
    (mul_nonneg (by norm_num) hr) hresidual hbase k).trans
      (Metric.closedBall_subset_closedBall ?_)
  have hkM : k < M := Finset.mem_range.mp hk
  unfold rychkovSpatialDilationFactor
  have hkM' : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.le_of_lt hkM)
  nlinarith

lemma rychkovDualDetail_tsupport_subset_spatialCarrier {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    tsupport (rychkovDualDetail φ M ell) ⊆
      rychkovSpatialCarrier φ M := by
  cases ell with
  | zero =>
      simpa [rychkovDualDetail] using
        rychkovDualApproximation_tsupport_subset_spatialCarrier φ M 0
  | succ ell =>
      rw [rychkovDualDetail_succ_eq_spatialPolynomial]
      let previous := complexDyadicApproximationKernel φ ell
      let current := complexDyadicApproximationKernel φ (ell + 1)
      let previousSquare := SchwartzMap.convolution (.mul ℂ ℂ) previous previous
      let currentSquare := SchwartzMap.convolution (.mul ℂ ℂ) current current
      have hr : 0 ≤ φ.rOut := φ.rOut_pos.le
      have hp : tsupport previous ⊆ Metric.closedBall 0 φ.rOut :=
        complexDyadicApproximationKernel_tsupport_subset_closedBall φ ell
      have hc : tsupport current ⊆ Metric.closedBall 0 φ.rOut :=
        complexDyadicApproximationKernel_tsupport_subset_closedBall φ (ell + 1)
      have hps : tsupport previousSquare ⊆ Metric.closedBall 0 (2 * φ.rOut) := by
        simpa [two_mul] using
          (schwartzConvolution_tsupport_subset_closedBall hp hp)
      have hcs : tsupport currentSquare ⊆ Metric.closedBall 0 (2 * φ.rOut) := by
        simpa [two_mul] using
          (schwartzConvolution_tsupport_subset_closedBall hc hc)
      have hbase : tsupport (current + previous) ⊆ Metric.closedBall 0 φ.rOut :=
        (tsupport_add _ _).trans (Set.union_subset hc hp)
      unfold rychkovDualDetailSuccSpatialPolynomial rychkovSpatialCarrier
      change tsupport ((∑ k ∈ Finset.range M,
        residualConvolutionApply previousSquare
          (residualConvolutionApply currentSquare (current + previous)
            (M - 1 - k)) k : 𝓢(CoordinateSpace d, ℂ)) :
          CoordinateSpace d → ℂ) ⊆
          Metric.closedBall 0 (rychkovSpatialDilationFactor M * φ.rOut)
      apply finset_sum_tsupport_subset_closedBall
      intro k hk
      have hkM : k < M := Finset.mem_range.mp hk
      have hinner := residualConvolutionApply_tsupport_subset_closedBall
        (mul_nonneg (by norm_num) hr) hcs hbase (M - 1 - k)
      have houter := residualConvolutionApply_tsupport_subset_closedBall
        (mul_nonneg (by norm_num) hr) hps hinner k
      refine houter.trans (Metric.closedBall_subset_closedBall ?_)
      unfold rychkovSpatialDilationFactor
      have hsub : (M - 1 - k : ℕ) + k ≤ M := by omega
      have hsub' : ((M - 1 - k : ℕ) : ℝ) + (k : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hsub
      nlinarith

end Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport
