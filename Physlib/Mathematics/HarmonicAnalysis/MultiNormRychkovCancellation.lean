/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Arbitrary moment cancellation for the constructed Rychkov details -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Convolution FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovCancellation

open MultiNormDualCalderon MultiNormMomentDerivative MultiNormRychkovDual
  MultiNormRychkovLimit MultiNormSchwartzKernel MultiNormTemperedCalderon

def VanishesToOrderAtZero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℂ) (m : ℕ) : Prop :=
  ∀ n : ℕ, n < m → iteratedFDeriv ℝ n f 0 = 0

lemma VanishesToOrderAtZero.mono {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {m n : ℕ}
    (hf : VanishesToOrderAtZero f m) (h : n ≤ m) :
    VanishesToOrderAtZero f n := by
  intro k hk
  exact hf k (hk.trans_le h)

lemma VanishesToOrderAtZero.add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {m : ℕ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfv : VanishesToOrderAtZero f m)
    (hgv : VanishesToOrderAtZero g m) :
    VanishesToOrderAtZero (fun x => f x + g x) m := by
  intro n hn
  change iteratedFDeriv ℝ n (f + g) 0 = 0
  rw [iteratedFDeriv_add_apply (hf.of_le (mod_cast le_top)).contDiffAt
    (hg.of_le (mod_cast le_top)).contDiffAt]
  simp [hfv n hn, hgv n hn]

lemma VanishesToOrderAtZero.finset_sum {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ι → E → ℂ} {m : ℕ}
    (hsmooth : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hvanish : ∀ i ∈ s, VanishesToOrderAtZero (f i) m) :
    VanishesToOrderAtZero (fun x => ∑ i ∈ s, f i x) m := by
  intro n hn
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    (hsmooth i hi).of_le (mod_cast le_top) |>.contDiffAt)]
  exact Finset.sum_eq_zero fun i hi => hvanish i hi n hn

lemma VanishesToOrderAtZero.mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {a b : ℕ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfv : VanishesToOrderAtZero f a)
    (hgv : VanishesToOrderAtZero g b) :
    VanishesToOrderAtZero (fun x => f x * g x) (a + b) := by
  intro n hn
  have hbound := norm_iteratedFDeriv_mul_le hf hg (0 : E)
    (n := n) (N := (⊤ : ℕ∞)) (mod_cast le_top)
  have hsum : (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f 0‖ *
        ‖iteratedFDeriv ℝ (n - i) g 0‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hia : i < a
    · simp [hfv i hia]
    · have hbig : n - i < b := by omega
      simp [hgv (n - i) hbig]
  rw [hsum] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

lemma VanishesToOrderAtZero.pow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {a : ℕ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfv : VanishesToOrderAtZero f a) (k : ℕ) :
    VanishesToOrderAtZero (fun x => f x ^ k) (k * a) := by
  induction k with
  | zero => simp [VanishesToOrderAtZero]
  | succ k ih =>
      simpa [pow_succ, Nat.succ_mul] using
        ih.mul (hf.pow k) hf hfv

lemma vanishesToOrderAtZero_one_of_value_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ}
    (hzero : f 0 = 0) : VanishesToOrderAtZero f 1 := by
  intro n hn
  have : n = 0 := by omega
  subst n
  ext m
  simpa using hzero

lemma vanishesToOrderAtZero_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℂ) : VanishesToOrderAtZero f 0 := by
  intro n hn
  omega

lemma residual_vanishesToOrderAtZero {d : ℕ}
    (ν : 𝓢(CoordinateSpace d, ℂ)) (hν : ν 0 = 1) :
    VanishesToOrderAtZero (fun ξ => 1 - ν ξ ^ 2) 1 := by
  apply vanishesToOrderAtZero_one_of_value_zero
  simp [hν]

lemma residual_pow_vanishesToOrderAtZero {d : ℕ}
    (ν : 𝓢(CoordinateSpace d, ℂ)) (hν : ν 0 = 1) (k : ℕ) :
    VanishesToOrderAtZero (fun ξ => (1 - ν ξ ^ 2) ^ k) k := by
  simpa using (residual_vanishesToOrderAtZero ν hν).pow
    (contDiff_const.sub ((ν.smooth (⊤ : ℕ∞)).pow 2)) k

lemma detailMultiplierTerm_vanishesToOrderAtZero {d : ℕ}
    (previous current : 𝓢(CoordinateSpace d, ℂ))
    (hp : previous 0 = 1) (hc : current 0 = 1)
    (M k : ℕ) (hk : k < M) :
    VanishesToOrderAtZero
      (fun ξ => (1 - previous ξ ^ 2) ^ k *
        (1 - current ξ ^ 2) ^ (M - 1 - k)) (M - 1) := by
  have h := (residual_pow_vanishesToOrderAtZero previous hp k).mul
    ((contDiff_const.sub ((previous.smooth (⊤ : ℕ∞)).pow 2)).pow k)
    ((contDiff_const.sub ((current.smooth (⊤ : ℕ∞)).pow 2)).pow (M - 1 - k))
    (residual_pow_vanishesToOrderAtZero current hc (M - 1 - k))
  have heq : k + (M - 1 - k) = M - 1 := by omega
  rwa [heq] at h

lemma detailMultiplier_vanishesToOrderAtZero {d : ℕ}
    (previous current : 𝓢(CoordinateSpace d, ℂ))
    (hp : previous 0 = 1) (hc : current 0 = 1) (M : ℕ) :
    VanishesToOrderAtZero (detailMultiplier M previous current) (M - 1) := by
  unfold detailMultiplier
  apply VanishesToOrderAtZero.finset_sum
  · intro k hk
    exact ((contDiff_const.sub ((previous.smooth (⊤ : ℕ∞)).pow 2)).pow k).mul
      ((contDiff_const.sub ((current.smooth (⊤ : ℕ∞)).pow 2)).pow (M - 1 - k))
  · intro k hk
    exact detailMultiplierTerm_vanishesToOrderAtZero previous current hp hc M k
      (Finset.mem_range.mp hk)

lemma detailFactor_vanishesToOrderAtZero {d : ℕ}
    (previous current : 𝓢(CoordinateSpace d, ℂ))
    (hp : previous 0 = 1) (hc : current 0 = 1) (M : ℕ) :
    VanishesToOrderAtZero
      (fun ξ => detailFactor M (previous ξ) (current ξ)) (M - 1) := by
  have hzero := vanishesToOrderAtZero_zero
    (fun ξ => current ξ + previous ξ)
  have hmul := hzero.mul
    ((current.smooth (⊤ : ℕ∞)).add (previous.smooth (⊤ : ℕ∞)))
    (detailMultiplier_hasTemperateGrowth M previous current).1
    (detailMultiplier_vanishesToOrderAtZero previous current hp hc M)
  simpa [detailFactor, detailMultiplier] using hmul

lemma detailFrequencyFactor_vanishesToOrderAtZero {d : ℕ}
    (previous current : 𝓢(CoordinateSpace d, ℂ))
    (hp : previous 0 = 1) (hc : current 0 = 1) (M : ℕ) :
    VanishesToOrderAtZero (detailFrequencyFactor M previous current) (M - 1) := by
  change VanishesToOrderAtZero
    (fun ξ => detailFrequencyFactor M previous current ξ) (M - 1)
  simpa only [detailFrequencyFactor_apply] using
    detailFactor_vanishesToOrderAtZero previous current hp hc M

lemma prod_inner_multiIndexDirections {d : ℕ}
    (α : CoordinateMultiIndex d) (x : CoordinateSpace d) :
    (∏ j : Fin (multiIndexDirections α).length,
      inner ℝ x ((multiIndexDirections α).get j)) =
      ∏ i : Fin d, x i ^ α i := by
  rw [← List.prod_ofFn]
  unfold multiIndexDirections
  rw [← Function.comp_def, ← List.map_ofFn, List.ofFn_get]
  rw [List.map_flatMap]
  rw [← Finset.prod_map_toList]
  generalize (Finset.univ : Finset (Fin d)).toList = l
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_replicate] at ih
      simp only [List.flatMap_cons, List.map_cons, List.prod_append,
        List.prod_cons, List.map_replicate, List.prod_replicate]
      rw [ih]
      simp [EuclideanSpace.inner_single_right]

lemma iteratedFDeriv_fourier_apply_directions_eq_moment {d : ℕ}
    (α : CoordinateMultiIndex d) (f : 𝓢(CoordinateSpace d, ℂ)) :
    (iteratedFDeriv ℝ (multiIndexDirections α).length
      (fun ξ => (𝓕 f) ξ) 0)
        (multiIndexDirections α).get =
      (- (2 * Real.pi * Complex.I)) ^ (multiIndexDirections α).length *
        schwartzMoment α f := by
  have hfourier := Real.iteratedFDeriv_fourier
    (f := fun x => f x) (N := (⊤ : ℕ∞))
    (fun n _ => f.integrable_pow_mul volume n)
    f.continuous.aestronglyMeasurable
      (n := (multiIndexDirections α).length) le_top
  rw [← SchwartzMap.fourier_coe] at hfourier
  have hzero := congrFun hfourier (0 : CoordinateSpace d)
  have happly := DFunLike.congr_fun hzero (multiIndexDirections α).get
  rw [Real.fourier_eq] at happly
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one,
    one_smul] at happly
  have hint : Integrable (fun v : CoordinateSpace d =>
      VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun x => f x) v
        (multiIndexDirections α).length) :=
    VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ)
      (f.integrable_pow_mul volume (multiIndexDirections α).length)
      f.continuous.aestronglyMeasurable
  rw [ContinuousMultilinearMap.integral_apply hint] at happly
  rw [happly]
  calc
    _ = ∫ x : CoordinateSpace d,
        (- (2 * Real.pi * Complex.I)) ^ (multiIndexDirections α).length *
          ((∏ i : Fin d, (x i : ℂ) ^ α i) * f x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [VectorFourier.fourierPowSMulRight_apply]
      change (- (2 * Real.pi * Complex.I)) ^ (multiIndexDirections α).length •
          (∏ i : Fin (multiIndexDirections α).length,
            inner ℝ x ((multiIndexDirections α).get i)) • f x = _
      rw [prod_inner_multiIndexDirections]
      simp only [smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    _ = (- (2 * Real.pi * Complex.I)) ^ (multiIndexDirections α).length *
        ∫ x : CoordinateSpace d, (∏ i : Fin d, (x i : ℂ) ^ α i) * f x := by
      rw [integral_const_mul]
    _ = _ := rfl

lemma hasCancellationOrder_of_fourier_vanishes {d m : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ))
    (hvanish : VanishesToOrderAtZero (fun ξ => (𝓕 f) ξ) m) :
    HasCancellationOrder f m := by
  intro α hα
  have hlen : (multiIndexDirections α).length < m := by
    rwa [length_multiIndexDirections]
  have hz := hvanish (multiIndexDirections α).length hlen
  have heq := iteratedFDeriv_fourier_apply_directions_eq_moment α f
  have hmul :
      (- (2 * Real.pi * Complex.I)) ^ (multiIndexDirections α).length *
          schwartzMoment α f = 0 := by
    rw [← heq, hz]
    rfl
  have hc : (- (2 * Real.pi * Complex.I)) ^
      (multiIndexDirections α).length ≠ 0 := by
    apply pow_ne_zero
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hpi)
      Complex.I_ne_zero)
  exact (mul_eq_zero.mp hmul).resolve_left hc

lemma rychkovDualDetail_hasCancellationOrder {d m ell : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (hell : 0 < ell) :
    HasCancellationOrder (rychkovDualDetail φ (m + 1) ell) m := by
  cases ell with
  | zero => omega
  | succ ell =>
      apply hasCancellationOrder_of_fourier_vanishes
      have hp := fourier_complexDyadicApproximationKernel_zero φ ell
      have hc := fourier_complexDyadicApproximationKernel_zero φ (ell + 1)
      have h := detailFrequencyFactor_vanishesToOrderAtZero
        (𝓕 (complexDyadicApproximationKernel φ ell))
        (𝓕 (complexDyadicApproximationKernel φ (ell + 1))) hp hc (m + 1)
      simpa only [fourier_rychkovDualDetail_succ, Nat.add_sub_cancel] using h

end Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovCancellation
