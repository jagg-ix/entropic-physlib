/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QFT.ScalarGreenFunctions.FreeTheory
meta import Zil

/-!
# The standard AdS/CFT correspondence: the GKP–Witten field–operator dictionary

Formalizes the **standard** AdS/CFT correspondence — the Gubser–Klebanov–Polyakov / Witten dictionary
(*S. Gubser, I. Klebanov, A. Polyakov, Phys. Lett. B 428 (1998) 105; E. Witten, Adv. Theor. Math. Phys. 2
(1998) 253*). A bulk scalar field of mass `m` in `AdS_{d+1}` is dual to a boundary CFT_d operator `O` of
conformal dimension `Δ`, fixed by the **mass–dimension relation**

  `Δ(Δ − d) = m² R²`   (`R` = AdS radius),

with the GKP–Witten generating-functional relation `Z_grav[φ₀] = ⟨e^{∫ φ₀ O}⟩_CFT`: a bulk field with
boundary value `φ₀` sources the operator `O`. Near the boundary `φ ~ z^{d−Δ} φ₀ + z^Δ ⟨O⟩` (source + VEV).
This is the standard dictionary, in contrast to the (non-standard) modular-flow route; it sits alongside the
Ryu–Takayanagi entropy of `AdSCFT.RyuTakayanagiFormulaAlgebra` as the bulk-boundary field map, sharing the same
Brown–Henneaux central charge for `AdS₃/CFT₂`.

Writing `μ = m² R²` (which may be negative down to the Breitenlohner–Freedman bound):

* **§A — the mass–dimension relation** (`conformalDimension`, `massDimension_relation`,
  `conformalDimension_sum`, `conformalDimension_prod`). `Δ± = d/2 ± √(d²/4 + μ)` solve `Δ(Δ−d) = μ`, with
  `Δ₊ + Δ₋ = d` and `Δ₊ Δ₋ = −μ` (Vieta on `Δ² − dΔ − μ = 0`).
* **§B — the Breitenlohner–Freedman bound and unitarity** (`breitenlohnerFreedman`,
  `conformalDimension_ge_half`). `Δ` is real iff `μ ≥ −d²/4` (AdS scalar stability); `Δ₊ ≥ d/2` (above the
  unitarity floor).
* **§C — the GKP–Witten dictionary** (`falloff_source_exponent`, `bulkToBoundaryKernel`,
  `bulkToBoundaryKernel_scaling`, `bulkToBoundaryKernel_boundary_limit`,
  `cubicWittenDensity`,
  `cubicWittenDensity_scaling`, `cftTwoPoint`, `cftTwoPoint_scaling`). The source falloff exponent is
  `d − Δ₊ = Δ₋`; the Euclidean bulk-to-boundary kernel
  `K_Δ(z,x;x₀) = (z / ((x-x₀)²+z²))^Δ` has the exact simultaneous bulk/boundary covariance
  `K_Δ(λz,λx;λx₀)=λ^{-Δ}K_Δ(z,x;x₀)`. Three kernels multiplied by the Poincaré
  volume density have the full cubic Witten-integrand dilation weight; after
  including the coordinate Jacobian, the bulk-volume weight cancels and only
  the three external primary weights remain. The dictionary output is the CFT
  two-point function `⟨O(x)O(0)⟩ ~ |x|^{−2Δ}`, conformally covariant
  `⟨O(λx)…⟩ = λ^{−2Δ}⟨O(x)…⟩`; the normalized kernel converges to this
  power law at every noncoincident boundary point.
* **§D — source differentiation** (`gkpWittenRegularizedOnShellAction`,
  `gkpWitten_regularized_source_response`,
  `gkpWitten_affine_source_hessian`). Reusing the repository's finite scalar
  propagator quadratic form and its full affine polarization, the first source
  derivative is the linear response and differentiating it once more returns
  the propagator bilinear/Hessian coefficient at an arbitrary background
  source.
* **§E — the standard `AdS₃/CFT₂` dictionary** (`adS3CFT2_dictionary`). Bundles the boundary CFT₂ data: the
  Brown–Henneaux central charge `c = 3R/2G` (from `AdSCFT.RyuTakayanagiFormulaAlgebra`) and the operator
  dimension `Δ(Δ−2) = m²R²`.

## References

* S. Gubser, I. Klebanov, A. Polyakov (1998); E. Witten (1998) — the AdS/CFT field–operator dictionary and
  the generating-functional relation. P. Breitenlohner, D. Z. Freedman, Ann. Phys. 144 (1982) 249 — the
  stability bound.
* Repo carrier: `AdSCFT.RyuTakayanagiFormulaAlgebra` (`brownHenneaux`, the AdS₃ central charge).


-/

set_option autoImplicit false
open scoped Topology

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QFT.ScalarGreenFunctions


/-- **[GKP–Witten] The conformal dimension** `Δ₊ = d/2 + √(d²/4 + μ)` of the boundary operator dual to a bulk
scalar with `μ = m²R²`. -/
noncomputable def conformalDimension (d μ : ℝ) : ℝ := d / 2 + Real.sqrt ((d / 2) ^ 2 + μ)

/-- The conjugate dimension `Δ₋ = d/2 − √(d²/4 + μ)` (the alternate quantization / source falloff). -/
noncomputable def conformalDimensionMinus (d μ : ℝ) : ℝ := d / 2 - Real.sqrt ((d / 2) ^ 2 + μ)

/-- **[Standard AdS/CFT] The mass–dimension relation** `Δ(Δ − d) = m²R²`. The bulk scalar mass fixes the
boundary operator's conformal dimension. -/
@[zil_level bridge_theorem]
lemma massDimension_relation (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimension d μ * (conformalDimension d μ - d) = μ := by
  unfold conformalDimension
  nlinarith [Real.sq_sqrt h, Real.sqrt_nonneg ((d / 2) ^ 2 + μ)]

/-- The conjugate dimension also solves the mass–dimension relation `Δ₋(Δ₋ − d) = m²R²`. -/
lemma massDimensionMinus_relation (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimensionMinus d μ * (conformalDimensionMinus d μ - d) = μ := by
  unfold conformalDimensionMinus
  nlinarith [Real.sq_sqrt h, Real.sqrt_nonneg ((d / 2) ^ 2 + μ)]

/-- **[Vieta] `Δ₊ + Δ₋ = d`** — the two dimensions sum to the boundary dimension. -/
@[zil_level bridge_theorem]
lemma conformalDimension_sum (d μ : ℝ) :
    conformalDimension d μ + conformalDimensionMinus d μ = d := by
  unfold conformalDimension conformalDimensionMinus; ring

/-- **[Vieta] `Δ₊ Δ₋ = −m²R²`** — the product of the two dimensions. -/
lemma conformalDimension_prod (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimension d μ * conformalDimensionMinus d μ = -μ := by
  unfold conformalDimension conformalDimensionMinus; nlinarith [Real.sq_sqrt h]


/-- **[Breitenlohner–Freedman] The dimension is real iff `m²R² ≥ −d²/4`.** The AdS scalar is stable above the
BF bound. -/
lemma breitenlohnerFreedman (d μ : ℝ) : 0 ≤ (d / 2) ^ 2 + μ ↔ -(d / 2) ^ 2 ≤ μ := by
  constructor <;> intro h <;> linarith

/-- **[Unitarity] `Δ₊ ≥ d/2`** — the operator dimension is above the unitarity floor. -/
lemma conformalDimension_ge_half (d μ : ℝ) : d / 2 ≤ conformalDimension d μ := by
  unfold conformalDimension; have := Real.sqrt_nonneg ((d / 2) ^ 2 + μ); linarith


/-- **[GKP–Witten falloffs] The source falloff exponent is `d − Δ₊ = Δ₋`.** Near the boundary
`φ ~ z^{d−Δ} φ₀ + z^Δ ⟨O⟩`: the leading (source) term has exponent `d − Δ₊`, the conjugate dimension `Δ₋`. -/
lemma falloff_source_exponent (d μ : ℝ) :
    d - conformalDimension d μ = conformalDimensionMinus d μ := by
  have := conformalDimension_sum d μ; linarith

/-- **[Maldacena lecture Eq. 4.10] The Euclidean bulk-to-boundary propagator**
`K_Δ(z,x;x₀) = (z / ((x-x₀)²+z²))^Δ`.

This is the one-boundary-coordinate restriction of the standard
`z^Δ / (|x-x₀|²+z²)^Δ` kernel.  Keeping the quotient inside `Real.rpow`
makes its conformal covariance exact for arbitrary real `Δ`; the positive
radial coordinate supplies the needed nonnegative base. -/
noncomputable def bulkToBoundaryKernel (Δ z x x₀ : ℝ) : ℝ :=
  (z / ((x - x₀) ^ 2 + z ^ 2)) ^ Δ

/-- **[Bulk/boundary conformal covariance]**
`K_Δ(λz,λx;λx₀)=λ^{-Δ}K_Δ(z,x;x₀)` for `z,λ>0`.

Thus the same AdS dilation rescales the bulk kernel with the weight of a
boundary primary of dimension `Δ`.  This is the analytic kernel statement
missing from the previous mass-dimension bookkeeping; it still does not
evaluate a Witten diagram or construct the bulk path integral. -/
@[zil_level bridge_theorem]
lemma bulkToBoundaryKernel_scaling (Δ z x x₀ lam : ℝ)
    (hz : 0 < z) (hlam : 0 < lam) :
    bulkToBoundaryKernel Δ (lam * z) (lam * x) (lam * x₀) =
      lam ^ (-Δ) * bulkToBoundaryKernel Δ z x x₀ := by
  have hden : (x - x₀) ^ 2 + z ^ 2 ≠ 0 := by positivity
  have hlamne : lam ≠ 0 := hlam.ne'
  have hratio :
      lam * z / ((lam * x - lam * x₀) ^ 2 + (lam * z) ^ 2) =
        lam⁻¹ * (z / ((x - x₀) ^ 2 + z ^ 2)) := by
    field_simp
  unfold bulkToBoundaryKernel
  rw [hratio, Real.mul_rpow (inv_nonneg.mpr hlam.le)
    (div_nonneg hz.le (by positivity)), Real.inv_rpow, Real.rpow_neg hlam.le]
  exact hlam.le

/-- The pointwise product of three bulk-to-boundary kernels entering a cubic
contact Witten diagram with boundary insertions at `x₁,x₂,x₃`. -/
noncomputable def cubicWittenKernel
    (Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ : ℝ) : ℝ :=
  bulkToBoundaryKernel Δ₁ z x x₁ *
      bulkToBoundaryKernel Δ₂ z x x₂ *
    bulkToBoundaryKernel Δ₃ z x x₃

/-- The product of three bulk-to-boundary kernels has boundary-primary
dilation weight `-(Δ₁+Δ₂+Δ₃)`. -/
lemma cubicWittenKernel_scaling
    (Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ lam : ℝ)
    (hz : 0 < z) (hlam : 0 < lam) :
    cubicWittenKernel Δ₁ Δ₂ Δ₃
        (lam * z) (lam * x) (lam * x₁) (lam * x₂) (lam * x₃) =
      lam ^ (-(Δ₁ + Δ₂ + Δ₃)) *
        cubicWittenKernel Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ := by
  unfold cubicWittenKernel
  rw [bulkToBoundaryKernel_scaling Δ₁ z x x₁ lam hz hlam,
    bulkToBoundaryKernel_scaling Δ₂ z x x₂ lam hz hlam,
    bulkToBoundaryKernel_scaling Δ₃ z x x₃ lam hz hlam]
  have hweights :
      lam ^ (-Δ₁) * lam ^ (-Δ₂) * lam ^ (-Δ₃) =
        lam ^ (-(Δ₁ + Δ₂ + Δ₃)) := by
    rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]
    congr 1
    ring
  calc
    lam ^ (-Δ₁) * bulkToBoundaryKernel Δ₁ z x x₁ *
          (lam ^ (-Δ₂) * bulkToBoundaryKernel Δ₂ z x x₂) *
        (lam ^ (-Δ₃) * bulkToBoundaryKernel Δ₃ z x x₃) =
        (lam ^ (-Δ₁) * lam ^ (-Δ₂) * lam ^ (-Δ₃)) *
          (bulkToBoundaryKernel Δ₁ z x x₁ *
            bulkToBoundaryKernel Δ₂ z x x₂ *
            bulkToBoundaryKernel Δ₃ z x x₃) := by ring
    _ = lam ^ (-(Δ₁ + Δ₂ + Δ₃)) *
          (bulkToBoundaryKernel Δ₁ z x x₁ *
            bulkToBoundaryKernel Δ₂ z x x₂ *
            bulkToBoundaryKernel Δ₃ z x x₃) := by rw [hweights]

/-- The one-radial/one-boundary-coordinate restriction of the Euclidean
`AdS_{d+1}` Poincaré volume density `z^{-(d+1)}`. -/
noncomputable def poincareVolumeDensity (d z : ℝ) : ℝ :=
  z ^ (-(d + 1))

/-- The Poincaré volume density has dilation weight `-(d+1)`. -/
lemma poincareVolumeDensity_scaling (d z lam : ℝ)
    (hz : 0 < z) (hlam : 0 < lam) :
    poincareVolumeDensity d (lam * z) =
      lam ^ (-(d + 1)) * poincareVolumeDensity d z := by
  unfold poincareVolumeDensity
  exact Real.mul_rpow hlam.le hz.le

/-- The pointwise cubic contact Witten density: Poincaré volume density times
three bulk-to-boundary propagators. -/
noncomputable def cubicWittenDensity
    (d Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ : ℝ) : ℝ :=
  poincareVolumeDensity d z *
    cubicWittenKernel Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃

/-- **[Cubic contact Witten diagram, pointwise analytic core]**
the complete pointwise density has simultaneous AdS/boundary dilation weight
`-(d+1+Δ₁+Δ₂+Δ₃)`: the volume-density weight plus the three external primary
weights.

This is the local analytic integrand statement.  It does not assert
integrability at the AdS boundary, choose a renormalization, or evaluate the
bulk contact integral. -/
@[zil_level bridge_theorem]
lemma cubicWittenDensity_scaling
    (d Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ lam : ℝ)
    (hz : 0 < z) (hlam : 0 < lam) :
    cubicWittenDensity d Δ₁ Δ₂ Δ₃
        (lam * z) (lam * x) (lam * x₁) (lam * x₂) (lam * x₃) =
      lam ^ (-(d + 1 + Δ₁ + Δ₂ + Δ₃)) *
        cubicWittenDensity d Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ := by
  unfold cubicWittenDensity
  rw [poincareVolumeDensity_scaling d z lam hz hlam,
    cubicWittenKernel_scaling Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ lam hz hlam]
  have hweights :
      lam ^ (-(d + 1)) * lam ^ (-(Δ₁ + Δ₂ + Δ₃)) =
        lam ^ (-(d + 1 + Δ₁ + Δ₂ + Δ₃)) := by
    rw [← Real.rpow_add hlam]
    congr 1
    ring
  calc
    lam ^ (-(d + 1)) * poincareVolumeDensity d z *
        (lam ^ (-(Δ₁ + Δ₂ + Δ₃)) *
          cubicWittenKernel Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃) =
        (lam ^ (-(d + 1)) * lam ^ (-(Δ₁ + Δ₂ + Δ₃))) *
          (poincareVolumeDensity d z *
            cubicWittenKernel Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃) := by ring
    _ = lam ^ (-(d + 1 + Δ₁ + Δ₂ + Δ₃)) *
          (poincareVolumeDensity d z *
            cubicWittenKernel Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃) := by rw [hweights]

/-- The `(d+1)`-dimensional coordinate Jacobian of a uniform positive
dilation, represented in the same real-exponent carrier as the Poincaré
volume density. -/
noncomputable def cubicWittenDilationJacobian (d lam : ℝ) : ℝ :=
  lam ^ (d + 1)

/-- **[Integrated cubic Witten covariance, Jacobian core]**
multiplying the transformed pointwise density by the coordinate Jacobian
cancels the Poincaré volume weight.  The transformed integration density
therefore carries only the sum of the three external primary weights.

This proves the exact change-of-variables weight needed by an integrated
contact diagram.  It does not supply boundary integrability, holographic
counterterms, or a numerical evaluation of the contact integral. -/
@[zil_level bridge_theorem]
lemma cubicWittenDensity_jacobian_covariance
    (d Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ lam : ℝ)
    (hz : 0 < z) (hlam : 0 < lam) :
    cubicWittenDilationJacobian d lam *
        cubicWittenDensity d Δ₁ Δ₂ Δ₃
          (lam * z) (lam * x) (lam * x₁) (lam * x₂) (lam * x₃) =
      lam ^ (-(Δ₁ + Δ₂ + Δ₃)) *
        cubicWittenDensity d Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ := by
  rw [cubicWittenDensity_scaling
    d Δ₁ Δ₂ Δ₃ z x x₁ x₂ x₃ lam hz hlam]
  unfold cubicWittenDilationJacobian
  have hweight :
      lam ^ (d + 1) * lam ^ (-(d + 1 + Δ₁ + Δ₂ + Δ₃)) =
        lam ^ (-(Δ₁ + Δ₂ + Δ₃)) := by
    rw [← Real.rpow_add hlam]
    congr 1
    ring
  rw [← mul_assoc, hweight]

/-- **[GKP–Witten output] The CFT two-point function** `⟨O(x)O(0)⟩ ~ |x|^{−2Δ}` of a dimension-`Δ` operator —
the boundary observable the dictionary computes. -/
noncomputable def cftTwoPoint (Δ x : ℝ) : ℝ := |x| ^ (-2 * Δ)

/-- **[Conformal covariance] `⟨O(λx)O(0)⟩ = λ^{−2Δ} ⟨O(x)O(0)⟩`** for `λ > 0` — the scaling fixed by the
conformal dimension. -/
lemma cftTwoPoint_scaling (Δ x lam : ℝ) (hlam : 0 < lam) :
    cftTwoPoint Δ (lam * x) = lam ^ (-2 * Δ) * cftTwoPoint Δ x := by
  unfold cftTwoPoint
  rw [abs_mul, abs_of_pos hlam, Real.mul_rpow (le_of_lt hlam) (abs_nonneg x)]

/-- Dividing the bulk-to-boundary kernel by its normalizable radial factor
`z^Δ` leaves the inverse boundary-distance denominator. -/
lemma bulkToBoundaryKernel_normalized_eq
    (Δ z x x₀ : ℝ) (hz : 0 < z) :
    z ^ (-Δ) * bulkToBoundaryKernel Δ z x x₀ =
      ((x - x₀) ^ 2 + z ^ 2) ^ (-Δ) := by
  have hden : 0 < (x - x₀) ^ 2 + z ^ 2 := by positivity
  unfold bulkToBoundaryKernel
  rw [Real.div_rpow hz.le hden.le]
  rw [Real.rpow_neg hz.le, Real.rpow_neg hden.le]
  have hzpow : z ^ Δ ≠ 0 := (Real.rpow_pos_of_pos hz Δ).ne'
  field_simp

/-- **[GKP–Witten extrapolate dictionary, noncoincident boundary limit]**
after removing the normalizable radial factor, the Euclidean bulk kernel
converges at `z → 0⁺` to the CFT two-point power law:
`z^{-Δ} K_Δ(z,x;x₀) → |x-x₀|^{-2Δ}`.

The hypothesis `x ≠ x₀` excludes the distributional contact singularity. This
is an actual right-filter boundary limit, but not a construction of the
contact-term distribution or holographic counterterms. -/
@[zil_level bridge_theorem]
lemma bulkToBoundaryKernel_boundary_limit
    (Δ x x₀ : ℝ) (hx : x ≠ x₀) :
    Filter.Tendsto
      (fun z : ℝ => z ^ (-Δ) * bulkToBoundaryKernel Δ z x x₀)
      (𝓝[>] 0) (𝓝 (cftTwoPoint Δ (x - x₀))) := by
  have hbase : (x - x₀) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hx)
  have hcont :
      ContinuousAt (fun z : ℝ => ((x - x₀) ^ 2 + z ^ 2) ^ (-Δ)) 0 := by
    apply ContinuousAt.rpow_const
      (continuousAt_const.add (continuousAt_id.pow 2))
    exact Or.inl (by simpa using hbase)
  have hlim :
      Filter.Tendsto
        (fun z : ℝ => ((x - x₀) ^ 2 + z ^ 2) ^ (-Δ))
        (𝓝[>] 0) (𝓝 (((x - x₀) ^ 2) ^ (-Δ))) := by
    simpa using tendsto_nhdsWithin_of_tendsto_nhds hcont
  have heq :
      (fun z : ℝ => z ^ (-Δ) * bulkToBoundaryKernel Δ z x x₀) =ᶠ[𝓝[>] 0]
        (fun z : ℝ => ((x - x₀) ^ 2 + z ^ 2) ^ (-Δ)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact bulkToBoundaryKernel_normalized_eq Δ z x x₀ hz
  have hout :
      ((x - x₀) ^ 2) ^ (-Δ) = cftTwoPoint Δ (x - x₀) := by
    unfold cftTwoPoint
    rw [sq, show (x - x₀) * (x - x₀) =
      |x - x₀| * |x - x₀| by
        simp,
      Real.mul_rpow (abs_nonneg (x - x₀)) (abs_nonneg (x - x₀))]
    rw [← Real.rpow_add (abs_pos.mpr (sub_ne_zero.mpr hx))]
    congr 1
    ring
  rw [← hout]
  exact hlim.congr' heq.symm

/-! ## §D — finite regularized on-shell source response -/

/-- A finite regularized quadratic on-shell source carrier
`I[J]/2 = (1/2) J Δ J`, built from the existing free-scalar propagator
quadratic form.  The complex parameter `t` restricts the source functional to
the line `J ↦ tJ`. -/
noncomputable def gkpWittenRegularizedOnShellAction {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) * realSourceQuadratic Delta (fun i => t * J i)

/-- The linear source response along `J ↦ tJ`. -/
noncomputable def gkpWittenRegularizedSourceResponse {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) (t : ℂ) : ℂ :=
  t * realSourceQuadratic Delta J

/-- Homogeneity of the finite regularized on-shell source action. -/
lemma gkpWittenRegularizedOnShellAction_eq {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) (t : ℂ) :
    gkpWittenRegularizedOnShellAction Delta J t =
      (t ^ 2 / 2) * realSourceQuadratic Delta J := by
  rw [gkpWittenRegularizedOnShellAction, realSourceQuadratic_smul]
  ring

/-- The first source derivative of the finite regularized on-shell action is
its linear response. -/
lemma gkpWittenRegularizedOnShellAction_hasDerivAt {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) (t : ℂ) :
    HasDerivAt (gkpWittenRegularizedOnShellAction Delta J)
      (gkpWittenRegularizedSourceResponse Delta J t) t := by
  rw [show gkpWittenRegularizedOnShellAction Delta J =
      fun u => (u ^ 2 / 2) * realSourceQuadratic Delta J by
    funext u
    exact gkpWittenRegularizedOnShellAction_eq Delta J u]
  unfold gkpWittenRegularizedSourceResponse
  convert ((hasDerivAt_pow 2 t).div_const 2).mul_const
    (realSourceQuadratic Delta J) using 1
  all_goals first | rfl | ring

/-- Differentiating the linear response returns the supplied propagator
quadratic coefficient. -/
lemma gkpWittenRegularizedSourceResponse_hasDerivAt {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) (t : ℂ) :
    HasDerivAt (gkpWittenRegularizedSourceResponse Delta J)
      (realSourceQuadratic Delta J) t := by
  unfold gkpWittenRegularizedSourceResponse
  simpa using (hasDerivAt_id t).mul_const (realSourceQuadratic Delta J)

/-- **[GKP–Witten source response, finite regularization]**
at zero source the one-point response of the quadratic carrier vanishes, while
one further source derivative returns `J Δ J`, the regularized two-point
coefficient.

The result reuses the repository's finite free-scalar Green matrix.  It is an
actual complex-derivative theorem, but it does not construct an interacting
bulk measure, remove the regulator, or identify a renormalized continuum
boundary distribution. -/
@[zil_level bridge_theorem]
lemma gkpWitten_regularized_source_response {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) :
    HasDerivAt (gkpWittenRegularizedOnShellAction Delta J) 0 0 ∧
      HasDerivAt (gkpWittenRegularizedSourceResponse Delta J)
        (realSourceQuadratic Delta J) 0 := by
  constructor
  · simpa [gkpWittenRegularizedSourceResponse] using
      gkpWittenRegularizedOnShellAction_hasDerivAt Delta J 0
  · exact gkpWittenRegularizedSourceResponse_hasDerivAt Delta J 0

/-- The finite regularized on-shell action along an affine source variation
`J ↦ J+tH`. -/
noncomputable def gkpWittenAffineOnShellAction {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    realSourceQuadratic Delta (fun i => J i + t * H i)

/-- For a symmetric propagator, the source response along `H` at background
`J+tH` is `JΔH+t HΔH`. -/
noncomputable def gkpWittenAffineSourceResponse {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) (t : ℂ) : ℂ :=
  realSourceBilinear Delta J H +
    t * realSourceQuadratic Delta H

/-- Exact polynomial form of the affine on-shell source action for a symmetric
neutral-scalar propagator. -/
lemma gkpWittenAffineOnShellAction_eq {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : Delta.transpose = Delta)
    (J H : Fin n → ℂ) (t : ℂ) :
    gkpWittenAffineOnShellAction Delta J H t =
      (1 / 2 : ℂ) * realSourceQuadratic Delta J +
        t * realSourceBilinear Delta J H +
        (t ^ 2 / 2) * realSourceQuadratic Delta H := by
  unfold gkpWittenAffineOnShellAction
  rw [realSourceQuadratic_affine_of_transpose_eq Delta hsymm]
  ring

/-- The first affine source derivative is the propagator response at the
current background source. -/
lemma gkpWittenAffineOnShellAction_hasDerivAt {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : Delta.transpose = Delta)
    (J H : Fin n → ℂ) (t : ℂ) :
    HasDerivAt (gkpWittenAffineOnShellAction Delta J H)
      (gkpWittenAffineSourceResponse Delta J H t) t := by
  rw [show gkpWittenAffineOnShellAction Delta J H =
      fun u =>
        (1 / 2 : ℂ) * realSourceQuadratic Delta J +
          u * realSourceBilinear Delta J H +
          (u ^ 2 / 2) * realSourceQuadratic Delta H by
    funext u
    exact gkpWittenAffineOnShellAction_eq Delta hsymm J H u]
  unfold gkpWittenAffineSourceResponse
  convert (((hasDerivAt_const t
      ((1 / 2 : ℂ) * realSourceQuadratic Delta J)).add
        ((hasDerivAt_id t).mul_const
          (realSourceBilinear Delta J H))).add
      (((hasDerivAt_pow 2 t).div_const 2).mul_const
        (realSourceQuadratic Delta H))) using 1
  all_goals first | rfl | ring

/-- The affine response differentiates to the quadratic form in the variation
direction, i.e. the diagonal propagator Hessian. -/
lemma gkpWittenAffineSourceResponse_hasDerivAt {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) (t : ℂ) :
    HasDerivAt (gkpWittenAffineSourceResponse Delta J H)
      (realSourceQuadratic Delta H) t := by
  unfold gkpWittenAffineSourceResponse
  convert (hasDerivAt_const t
      (realSourceBilinear Delta J H)).add
    ((hasDerivAt_id t).mul_const (realSourceQuadratic Delta H)) using 1
  all_goals first | rfl | ring

/-- **[GKP–Witten functional Hessian, finite regularization]**
at an arbitrary background source `J`, variation in direction `H` has
one-point response `JΔH`, and differentiating once more returns the two-point
Hessian `HΔH`.

This upgrades the zero-source ray to a genuine affine directional variation.
It remains a finite free-scalar regularization, not an interacting continuum
bulk functional or a regulator-removal theorem. -/
@[zil_level bridge_theorem]
lemma gkpWitten_affine_source_hessian {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : Delta.transpose = Delta)
    (J H : Fin n → ℂ) :
    HasDerivAt (gkpWittenAffineOnShellAction Delta J H)
        (realSourceBilinear Delta J H) 0 ∧
      HasDerivAt (gkpWittenAffineSourceResponse Delta J H)
        (realSourceQuadratic Delta H) 0 := by
  constructor
  · simpa [gkpWittenAffineSourceResponse] using
      gkpWittenAffineOnShellAction_hasDerivAt Delta hsymm J H 0
  · exact gkpWittenAffineSourceResponse_hasDerivAt Delta J H 0

/-! ## §E — the `AdS₃/CFT₂` specialization -/

/-- **[Standard AdS₃/CFT₂] The boundary CFT₂ data from the bulk.** The Brown–Henneaux central charge
`c = 3R/2G` (`AdSCFT.RyuTakayanagiFormulaAlgebra.brownHenneaux`) and the operator dimension fixed by
`Δ(Δ − 2) = m²R²` — the standard dictionary for `AdS₃/CFT₂`, alongside the Ryu–Takayanagi entropy. -/
lemma adS3CFT2_dictionary (R G μ : ℝ) (h : 0 ≤ (2 / 2 : ℝ) ^ 2 + μ) :
    brownHenneaux R G = 3 * R / (2 * G)
      ∧ conformalDimension 2 μ * (conformalDimension 2 μ - 2) = μ :=
  ⟨rfl, massDimension_relation 2 μ h⟩

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.massDimension_relation where
  formalizes @ "claim:the-gkp-witten-mass-dimension-relation-delta-is-d-over-two-plus-root-of-d-over-two-squared-plus-mass",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-ads-cft-correlators"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.conformalDimension_sum where
  formalizes @ "claim:the-two-gkp-witten-conformal-dimensions-sum-to-the-boundary-dimension-d",
  requires @ "claim:the-gkp-witten-mass-dimension-relation-delta-is-d-over-two-plus-root-of-d-over-two-squared-plus-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.bulkToBoundaryKernel_scaling where
  formalizes @ "claim:the-euclidean-gkp-witten-bulk-to-boundary-kernel-has-exact-simultaneous-ads-boundary-dilation-weight-minus-delta",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:maldacena-lecture-ads-cft-0309246v5-equation-4-10",
  caveat @ "claim:one-boundary-coordinate-kernel-covariance-not-a-witten-diagram-integral-on-shell-action-evaluation-or-derivation-of-the-ads-cft-correspondence"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.bulkToBoundaryKernel_boundary_limit where
  formalizes @ "claim:after-removing-the-normalizable-radial-factor-the-euclidean-bulk-to-boundary-kernel-converges-at-every-noncoincident-boundary-point-to-the-cft-two-point-power-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-extrapolate-dictionary",
  supported_by @ "paper:ads-cft-review-1501.00007v2-bulk-boundary-correlators",
  caveat @ "claim:genuine-right-filter-boundary-limit-away-from-the-contact-singularity-not-a-construction-of-the-distributional-contact-term-holographic-counterterms-or-the-interacting-bulk-path-integral"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.cubicWittenDensity_scaling where
  formalizes @ "claim:the-pointwise-cubic-contact-witten-density-has-the-sum-of-the-poincare-volume-weight-and-three-boundary-primary-weights",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:maldacena-lecture-ads-cft-0309246v5-bulk-to-boundary-kernel-and-contact-witten-diagrams",
  caveat @ "claim:pointwise-one-boundary-coordinate-integrand-covariance-not-boundary-integrability-holographic-renormalization-or-evaluation-of-the-bulk-contact-integral"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.cubicWittenDensity_jacobian_covariance where
  formalizes @ "claim:the-d-plus-one-coordinate-jacobian-cancels-the-poincare-volume-weight-of-the-cubic-contact-witten-density-leaving-only-three-external-primary-weights",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:maldacena-lecture-ads-cft-0309246v5-contact-witten-diagram-change-of-variables",
  caveat @ "claim:exact-jacobian-times-pointwise-density-covariance-not-boundary-integrability-holographic-counterterms-or-numerical-evaluation-of-the-bulk-contact-integral"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.gkpWitten_regularized_source_response where
  formalizes @ "claim:the-finite-regularized-gkp-witten-quadratic-on-shell-source-carrier-has-zero-one-point-response-at-zero-source-and-second-source-response-equal-to-the-propagator-quadratic",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-generating-functional-prescription",
  caveat @ "claim:finite-free-scalar-matrix-regularization-with-actual-complex-source-derivatives-not-an-interacting-bulk-measure-regulator-removal-or-renormalized-continuum-boundary-distribution"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.gkpWitten_affine_source_hessian where
  formalizes @ "claim:an-arbitrary-affine-boundary-source-variation-of-the-finite-gkp-witten-on-shell-carrier-has-first-response-j-delta-h-and-second-response-h-delta-h",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-functional-source-differentiation",
  caveat @ "claim:genuine-complex-directional-derivatives-at-an-arbitrary-background-source-but-still-a-finite-free-scalar-matrix-regularization-not-an-interacting-continuum-bulk-functional"

zil_file_contract physlib.gkpWittenAdSCFTDictionary where
  promises "The GKP-Witten AdS/CFT dictionary: the bulk mass fixes the boundary operator conformal dimension by delta equals d over two plus the root of d over two squared plus the mass, the two roots sum to d, the Euclidean bulk-to-boundary kernel has exact simultaneous AdS/boundary dilation weight minus delta and its normalized noncoincident boundary limit is the CFT two-point power law, the full pointwise cubic contact density has the combined Poincare-volume and external-primary dilation weight while its coordinate Jacobian cancels the bulk-volume weight, and a reused finite propagator quadratic has actual first and second complex source derivatives both at zero source and along arbitrary affine background-source variations."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.conformalDimension",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.cftTwoPoint"]
  forbids_substitutes ["a derivation of the holographic correspondence, the dictionary is taken as the GKP-Witten prescription",
    "evaluation or holographic renormalization of a bulk Witten-diagram integral",
    "the distributional contact singularity in the boundary extrapolate limit",
    "an interacting continuum bulk measure or regulator removal, the source-response theorem uses the existing finite free-scalar Green matrix"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.massDimension_relation,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.conformalDimension_sum,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.bulkToBoundaryKernel_scaling,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.bulkToBoundaryKernel_boundary_limit,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.cubicWittenDensity_scaling,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.cubicWittenDensity_jacobian_covariance,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.gkpWitten_regularized_source_response,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.gkpWitten_affine_source_hessian]

/- ZIL-END -/

#zil_formalization_lint physlib.gkpWittenAdSCFTDictionary
