/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon
public import Physlib.Mathematics.Distribution.SchwartzTensorProduct
meta import Zil

/-!
# Full finite-index tensor Calderon families

This module implements the tensor-product mechanism of Proposition 4.3 over
the paper's full coordinate index `Fin n → ℕ`.  It reuses Physlib's existing
continuous `SchwartzMap.productTensor`; the only new definitions select the
coordinate kernels and the finite coordinatewise box at a cutoff.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff SchwartzMap

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormTensorCalderon

open MultiNormDualCalderon MultiNormMomentDerivative
  MultiNormSchwartzKernel MultiNormTemperedCalderon

/-- The finite coordinatewise box `{K | K ≤ L}` in the full index space
`Fin n → ℕ`. -/
def fullTensorIndexBox {n : ℕ} (L : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => Finset.range (L i + 1)

@[simp]
lemma mem_fullTensorIndexBox_iff {n : ℕ} {L K : Fin n → ℕ} :
    K ∈ fullTensorIndexBox L ↔ K ≤ L := by
  simp only [fullTensorIndexBox, Fintype.mem_piFinset, Finset.mem_range,
    Nat.lt_succ_iff]
  rfl

/-- Product tensor of the one-parameter approximation kernels at the full
multi-index `L`. -/
def fullTensorApproximationKernel {n d : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (L : Fin n → ℕ) : 𝓢(Fin n → CoordinateSpace d, ℂ) :=
  SchwartzMap.productTensor fun i => complexDyadicApproximationKernel (φ i) (L i)

/-- Product tensor of all coordinate detail kernels at `K`. -/
def fullTensorDetailKernel {n d : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (K : Fin n → ℕ) : 𝓢(Fin n → CoordinateSpace d, ℂ) :=
  SchwartzMap.productTensor fun i => complexDyadicDetailKernel (φ i) (K i)

/-- Multilinearity of the repository's existing product tensor expands a
product of finite sums into the full finite function-indexed box. -/
lemma productTensor_sum_box {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Fin n → ℕ → 𝓢(E, ℂ)) (L : Fin n → ℕ) :
    SchwartzMap.productTensor
        (fun i => ∑ ell ∈ Finset.range (L i + 1), F i ell) =
      ∑ K ∈ fullTensorIndexBox L,
        SchwartzMap.productTensor (fun i => F i (K i)) := by
  ext x
  simp only [SchwartzMap.productTensor_apply, sum_apply, fullTensorIndexBox]
  exact Finset.prod_univ_sum (fun i => Finset.range (L i + 1))
    (fun i ell => F i ell (x i))

/-- The first Proposition 4.3 finite identity: the full tensor approximate
identity is exactly the sum of all tensor details in its coordinatewise box. -/
lemma fullTensorApproximation_eq_sum_details {n d : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (L : Fin n → ℕ) :
    fullTensorApproximationKernel φ L =
      ∑ K ∈ fullTensorIndexBox L, fullTensorDetailKernel φ K := by
  rw [fullTensorApproximationKernel]
  calc
    SchwartzMap.productTensor
        (fun i => complexDyadicApproximationKernel (φ i) (L i)) =
      SchwartzMap.productTensor
        (fun i => ∑ ell ∈ Finset.range (L i + 1),
          complexDyadicDetailKernel (φ i) ell) := by
            congr 1
            funext i
            exact (sum_range_complexDyadicDetailKernel (φ i) (L i)).symm
    _ = ∑ K ∈ fullTensorIndexBox L,
        SchwartzMap.productTensor
          (fun i => complexDyadicDetailKernel (φ i) (K i)) :=
      productTensor_sum_box
        (fun i ell => complexDyadicDetailKernel (φ i) ell) L
    _ = ∑ K ∈ fullTensorIndexBox L, fullTensorDetailKernel φ K := rfl

/-- Product tensor of coordinate low-frequency dual convolutions. -/
def fullTensorDualApproximationKernel {n d m : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (D : ∀ i, DualCalderonFamily (φ i) m) (L : Fin n → ℕ) :
    𝓢(Fin n → CoordinateSpace d, ℂ) :=
  SchwartzMap.productTensor fun i =>
    dualApproximationConvolution (φ i) (D i).dualApproximation (L i)

/-- Product tensor of coordinate detail/dual-detail convolutions. -/
def fullTensorDualDetailKernel {n d m : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (D : ∀ i, DualCalderonFamily (φ i) m) (K : Fin n → ℕ) :
    𝓢(Fin n → CoordinateSpace d, ℂ) :=
  SchwartzMap.productTensor fun i =>
    dualDetailConvolution (φ i) (D i).dualDetail (K i)

/-- Proposition 4.3(b), at every finite full-index cutoff: tensoring the
coordinate Lemma 4.2 partial identities gives the coordinatewise-box partial
Calderon identity. -/
lemma fullTensorDualApproximation_eq_sum_details {n d m : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (D : ∀ i, DualCalderonFamily (φ i) m) (L : Fin n → ℕ) :
    fullTensorDualApproximationKernel φ D L =
      ∑ K ∈ fullTensorIndexBox L, fullTensorDualDetailKernel φ D K := by
  rw [fullTensorDualApproximationKernel]
  calc
    SchwartzMap.productTensor
        (fun i => dualApproximationConvolution
          (φ i) (D i).dualApproximation (L i)) =
      SchwartzMap.productTensor
        (fun i => ∑ ell ∈ Finset.range (L i + 1),
          dualDetailConvolution (φ i) (D i).dualDetail ell) := by
            congr 1
            funext i
            exact ((D i).partial_kernel_identity (L i)).symm
    _ = ∑ K ∈ fullTensorIndexBox L,
        SchwartzMap.productTensor
          (fun i => dualDetailConvolution (φ i) (D i).dualDetail (K i)) :=
      productTensor_sum_box
        (fun i ell => dualDetailConvolution (φ i) (D i).dualDetail ell) L
    _ = ∑ K ∈ fullTensorIndexBox L,
        fullTensorDualDetailKernel φ D K := rfl

/-- The tensor dual partial identity embedded canonically in tempered
distributions on the full product space. -/
lemma fullTensorDualDistribution_partial_identity {n d m : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    [(volume : Measure (Fin n → CoordinateSpace d)).HasTemperateGrowth]
    (D : ∀ i, DualCalderonFamily (φ i) m) (L : Fin n → ℕ) :
    SchwartzMap.toTemperedDistributionCLM
        (Fin n → CoordinateSpace d) ℂ volume
        (fullTensorDualApproximationKernel φ D L) =
      ∑ K ∈ fullTensorIndexBox L,
        SchwartzMap.toTemperedDistributionCLM
          (Fin n → CoordinateSpace d) ℂ volume
          (fullTensorDualDetailKernel φ D K) := by
  simpa [map_sum] using congrArg
    (SchwartzMap.toTemperedDistributionCLM
      (Fin n → CoordinateSpace d) ℂ volume)
    (fullTensorDualApproximation_eq_sum_details φ D L)

/-- Proposition 4.3 capstone over the actual full multi-index type.  It
combines the original tensor telescope, the dual convolutional telescope, its
tempered-distribution image, and arbitrary coordinate cancellation inherited
from Lemma 4.2. -/
lemma fullMultiIndex_tensorProduct_calderon_family {n d m : ℕ}
    (φ : Fin n → ContDiffBump (0 : CoordinateSpace d))
    (D : ∀ i, DualCalderonFamily (φ i) m) (L : Fin n → ℕ) :
    fullTensorApproximationKernel φ L =
      ∑ K ∈ fullTensorIndexBox L, fullTensorDetailKernel φ K ∧
    fullTensorDualApproximationKernel φ D L =
      ∑ K ∈ fullTensorIndexBox L, fullTensorDualDetailKernel φ D K ∧
    (∀ K ∈ fullTensorIndexBox L, ∀ i, 0 < K i →
      HasCancellationOrder ((D i).dualDetail (K i)) m) := by
  exact ⟨fullTensorApproximation_eq_sum_details φ L,
    fullTensorDualApproximation_eq_sum_details φ D L,
    fun K _ i hi => (D i).cancellation (K i) hi⟩

end MultiNormTensorCalderon

end Physlib.Mathematics.HarmonicAnalysis

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullMultiIndex_tensorProduct_calderon_family where
  formalizes @ "claim:the-tensor-product-calderon-family-conjoins-the-original-telescope-the-dual-telescope-and-per-coordinate-arbitrary-cancellation-over-the-full-multi-index",
  requires @ "claim:the-tensor-approximation-kernel-equals-the-sum-of-detail-kernels-over-the-full-index-box",
  supported_by @ "paper:multi-norm-tensor-product-calderon-proposition"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorApproximation_eq_sum_details where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.productTensor_sum_box",
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-tensor-approximation-kernel-equals-the-sum-of-detail-kernels-over-the-full-index-box"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorDualApproximation_eq_sum_details where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.productTensor_sum_box",
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-dual-tensor-approximation-kernel-equals-the-sum-of-dual-detail-kernels-over-the-box-at-every-cutoff"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.productTensor_sum_box where
  formalizes @ "claim:the-product-tensor-of-coordinatewise-finite-sums-expands-multilinearly-over-the-full-index-box"

zil_file_contract physlib.multiNormTensorCalderon where
  promises "The tensor-product Calderon identity over multi-indices: reusing the existing continuous Schwartz product-tensor (no new tensor machinery), the product tensor of coordinatewise finite sums expands multilinearly over the full index box, so the tensor approximation kernel equals the box sum of detail kernels for both the original and the dual families at every finite cutoff; the Proposition 4.3 capstone conjoins the original telescope, the dual telescope, and per-coordinate arbitrary cancellation over the full multi-index type."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorApproximationKernel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorDetailKernel"]
  forbids_substitutes ["any new tensor-product construction, the existing continuous SchwartzMap.productTensor is reused unchanged"]
  witnessed_by [Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullMultiIndex_tensorProduct_calderon_family,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorApproximation_eq_sum_details,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorDualApproximation_eq_sum_details,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.productTensor_sum_box]

/- ZIL-END -/
