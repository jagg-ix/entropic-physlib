/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Spectral measures

## i. Overview

A norm-additive spectral measure `μS` on a measurable space `α` is a σ-additive
function `Set α → H →L[ℂ] H` such that each set is mapped to a star projection,
the empty set and non-measurable sets are mapped to zero, and `univ` is mapped
to the identity.  The legacy `SpectralMeasure` implements this by extending
`VectorMeasure α (H →L[ℂ] H)`, hence asks for operator-norm countable
additivity.

The continuum-correct carrier is `StrongSpectralMeasure`: for every vector
`x : H`, disjoint spectral projections sum to the union projection after
application to `x`.  This is strong-operator countable additivity and admits
the usual nonatomic spectral resolutions, which are generally not additive in
operator norm.

For each pair `u v : H`, composition with the continuous matrix coefficient
`T ↦ ⟪u, T v⟫` gives a genuine complex measure.  Its real and imaginary total
variations provide a canonical finite positive control measure, and its
Radon--Nikodym density integrates back to `⟪u,v⟫`.

## ii. Key results

- `SpectralMeasure` : A star projection-valued measure.
- `StrongSpectralMeasure` : A strong-operator-countably-additive
    projection-valued measure, the preferred continuum carrier.
- `comp_eq_of_inter` : For a spectral measure `μS` and measurable sets `A` and `B`,
    the composition `μS A ∘ μS B = μS (A ∩ B)`.
- `coefficientMeasure` : The scalar complex spectral measure
    `A ↦ ⟪u, μS A v⟫`.
- `coefficient_density_integral` : The canonical finite-control-measure density
    integrates to the Hilbert-space matrix coefficient `⟪u,v⟫`.

## iii. Table of contents

- A. Definition
- B. Composition
- C. Scalar matrix coefficients and canonical spectral densities
- D. Strong-operator spectral measures

## iv. References

-/

@[expose] public section

noncomputable section

open ContinuousLinearMap
open Filter
open MeasureTheory
open Set

instance (H : Type*) [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    IsAddTorsionFree (H →L[ℂ] H) where
  nsmul_right_injective n hn := by
    refine Function.HasLeftInverse.injective ?_
    use fun f ↦ (n : ℂ)⁻¹ • f
    intro; ext; simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ne_zero (R := ℂ), hn]

/-!
## A. Definition
-/

/-- A _spectral measure_ on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H`
  such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets
  are mapped to zero, and `univ` is mapped to the identity. -/
structure SpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →L[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

/-- A projection-valued spectral measure with countable additivity in the
strong operator topology.  This is the standard continuum notion: for every
`x : H`, the vectors `E(sᵢ)x` sum in Hilbert norm to `E(⋃ᵢsᵢ)x`. -/
structure StrongSpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  measureOf' : Set α → H →L[ℂ] H
  empty' : measureOf' ∅ = 0
  not_measurable' : ∀ s, ¬ MeasurableSet s → measureOf' s = 0
  m_iUnion' : ∀ (s : ℕ → Set α),
    (∀ i, MeasurableSet (s i)) →
    (∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (s i) (s j)) →
    ∀ x, HasSum (fun i => measureOf' (s i) x)
      (measureOf' (⋃ i, s i) x)
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' Set.univ = 1

namespace QuantumMechanics.SpaceDHilbertSpace

/-! Volume-specialised compatibility helpers over the measure-generalised upstream API. -/

variable {d : ℕ}

lemma coe_hilbertSpace_memHS (f : QuantumMechanics.SpaceDHilbertSpace d) :
    MemHS (f : Space d → ℂ) volume :=
  memHS_coe f

lemma coe_mk_ae {f : Space d → ℂ} (hf : MemHS f volume) :
    (mk hf) =ᵐ[volume] f := by
  simpa [mk] using MeasureTheory.AEEqFun.coeFn_mk f hf.1

end QuantumMechanics.SpaceDHilbertSpace

namespace SpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : SpectralMeasure α H)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (SpectralMeasure α H) (VectorMeasure α (H →L[ℂ] H)) :=
  ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (SpectralMeasure α H) fun _ ↦ Set α → H →L[ℂ] H :=
  ⟨fun μS ↦ μS.toVectorMeasure.measureOf'⟩

lemma isStarProjection (A : Set α) : IsStarProjection (μS A) := μS.isStarProjection' A

@[simp]
lemma univ : μS univ = 1 := μS.univ'

/-!
## B. Composition
-/

@[simp]
lemma comp_self (A : Set α) : μS A ∘L μS A = μS A := (μS.isStarProjection A).isIdempotentElem

lemma comp_of_disjoint
    {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A ∘L μS B = 0 := by
  have hunion : μS.toVectorMeasure.measureOf' (A ∪ B) =
      μS.toVectorMeasure.measureOf' A + μS.toVectorMeasure.measureOf' B :=
    μS.toVectorMeasure.of_union h hA hB
  have hmul : μS A ∘L μS (A ∪ B) = μS A := by
    refine (IsStarProjection.sub_iff_mul_eq_left
      (μS.isStarProjection A) (μS.isStarProjection (A ∪ B))).mp ?_
    change IsStarProjection (μS (A ∪ B) - μS A)
    rw [hunion, add_sub_cancel_left]
    exact μS.isStarProjection B
  have hself : μS.toVectorMeasure.measureOf' A ∘L
      μS.toVectorMeasure.measureOf' A = μS.toVectorMeasure.measureOf' A :=
    μS.comp_self A
  rw [hunion, comp_add, hself] at hmul
  apply add_left_cancel (a := μS A)
  exact hmul.trans (add_zero (μS A)).symm

lemma comp_eq_of_inter {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A ∘L μS B = μS (A ∩ B) := by
  have hA_decomp : μS.toVectorMeasure.measureOf' A =
      μS.toVectorMeasure.measureOf' (A ∩ B) + μS.toVectorMeasure.measureOf' (A \ B) := by
    calc
      μS.toVectorMeasure.measureOf' A =
          μS.toVectorMeasure.measureOf' ((A ∩ B) ∪ (A \ B)) := by
            rw [inter_union_sdiff]
      _ = μS.toVectorMeasure.measureOf' (A ∩ B) +
          μS.toVectorMeasure.measureOf' (A \ B) :=
        μS.toVectorMeasure.of_union disjoint_sdiff_inter.symm
          (hA.inter hB) (hA.diff hB)
  have hB_decomp : μS.toVectorMeasure.measureOf' B =
      μS.toVectorMeasure.measureOf' (B ∩ A) + μS.toVectorMeasure.measureOf' (B \ A) := by
    calc
      μS.toVectorMeasure.measureOf' B =
          μS.toVectorMeasure.measureOf' ((B ∩ A) ∪ (B \ A)) := by
            rw [inter_union_sdiff]
      _ = μS.toVectorMeasure.measureOf' (B ∩ A) +
          μS.toVectorMeasure.measureOf' (B \ A) :=
        μS.toVectorMeasure.of_union disjoint_sdiff_inter.symm
          (hB.inter hA) (hB.diff hA)
  rw [hA_decomp, hB_decomp, add_comp, comp_add, comp_add]
  rw [inter_comm B A, μS.comp_of_disjoint disjoint_sdiff_inter (hA.diff hB) (hA.inter hB)]
  rw [inter_comm A B, μS.comp_of_disjoint disjoint_sdiff_inter.symm (hB.inter hA) (hB.diff hA)]
  simp [μS.comp_of_disjoint disjoint_sdiff_sdiff (hA.diff hB) (hB.diff hA)]

lemma commute (A B : Set α) : Commute (μS A) (μS B) := by
  by_cases hAB : MeasurableSet A ∧ MeasurableSet B
  · rw [commute_iff_eq]
    simp only [mul_def, μS.comp_eq_of_inter hAB.1 hAB.2,
      μS.comp_eq_of_inter hAB.2 hAB.1, inter_comm]
  · rcases not_and_or.mp hAB with hA | hB
    · have hzero : μS.toVectorMeasure.measureOf' A = 0 :=
        μS.toVectorMeasure.not_measurable hA
      rw [commute_iff_eq]
      simp only [mul_def, hzero, zero_comp, comp_zero]
    · have hzero : μS.toVectorMeasure.measureOf' B = 0 :=
        μS.toVectorMeasure.not_measurable hB
      rw [commute_iff_eq]
      simp only [mul_def, hzero, zero_comp, comp_zero]

/-!
## C. Scalar matrix coefficients and canonical spectral densities
-/

/-- The continuous linear functional `T ↦ ⟪u, T v⟫` on bounded operators. -/
def matrixCoefficientCLM (u v : H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ H v)

@[simp]
lemma matrixCoefficientCLM_apply (u v : H) (T : H →L[ℂ] H) :
    matrixCoefficientCLM u v T = inner ℂ u (T v) := rfl

/-- The complex scalar measure `A ↦ ⟪u, μS(A)v⟫` induced by a
projection-valued spectral measure. -/
def coefficientMeasure (u v : H) : ComplexMeasure α :=
  μS.toVectorMeasure.mapRange
    (matrixCoefficientCLM u v).toAddMonoidHom
    (matrixCoefficientCLM u v).continuous

@[simp]
lemma coefficientMeasure_apply (u v : H) (s : Set α) :
    μS.coefficientMeasure u v s = inner ℂ u (μS s v) := rfl

@[simp]
lemma coefficientMeasure_univ (u v : H) :
    μS.coefficientMeasure u v Set.univ = inner ℂ u v := by
  simp

/-- A canonical finite positive measure dominating a complex measure: the sum
of the total variations of its real and imaginary parts. -/
def complexControlMeasure (c : ComplexMeasure α) : Measure α :=
  c.re.totalVariation + c.im.totalVariation

/-- The total variation of a signed measure is finite.  This follows directly
from the finite positive and negative measures in its Jordan decomposition. -/
instance instIsFiniteMeasureSignedTotalVariation (s : SignedMeasure α) :
    IsFiniteMeasure s.totalVariation := by
  unfold SignedMeasure.totalVariation
  infer_instance

instance instIsFiniteMeasureComplexControl (c : ComplexMeasure α) :
    IsFiniteMeasure (complexControlMeasure c) := by
  unfold complexControlMeasure
  infer_instance

/-- Every complex measure is absolutely continuous with respect to its
canonical real/imaginary total-variation control measure. -/
lemma absolutelyContinuous_complexControlMeasure (c : ComplexMeasure α) :
    c ≪ᵥ (complexControlMeasure c).toENNRealVectorMeasure := by
  rw [ComplexMeasure.absolutelyContinuous_ennreal_iff]
  constructor
  · rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      show (complexControlMeasure c).toENNRealVectorMeasure.ennrealToMeasure =
        complexControlMeasure c from VectorMeasure.equivMeasure.right_inv _]
    exact Measure.AbsolutelyContinuous.rfl.add_right c.im.totalVariation
  · rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      show (complexControlMeasure c).toENNRealVectorMeasure.ennrealToMeasure =
        complexControlMeasure c from VectorMeasure.equivMeasure.right_inv _]
    exact Measure.AbsolutelyContinuous.rfl.add_right' c.re.totalVariation

/-- Radon--Nikodym reconstruction of a complex measure against its canonical
finite positive control measure. -/
lemma withDensity_rnDeriv_complexControlMeasure (c : ComplexMeasure α) :
    (complexControlMeasure c).withDensityᵥ
        (c.rnDeriv (complexControlMeasure c)) = c := by
  have hac := absolutelyContinuous_complexControlMeasure c
  rw [ComplexMeasure.absolutelyContinuous_ennreal_iff] at hac
  have hre :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq c.re (complexControlMeasure c) hac.1
  have him :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq c.im (complexControlMeasure c) hac.2
  ext s hs : 1
  rw [withDensityᵥ_apply (c.integrable_rnDeriv (complexControlMeasure c)) hs]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re]
    · change
        (∫ x in s, c.re.rnDeriv (complexControlMeasure c) x
          ∂complexControlMeasure c) = (c s).re
      rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs, hre]
      rfl
    · exact (c.integrable_rnDeriv (complexControlMeasure c)).integrableOn
  · rw [← RCLike.im_eq_complex_im, ← integral_im]
    · change
        (∫ x in s, c.im.rnDeriv (complexControlMeasure c) x
          ∂complexControlMeasure c) = (c s).im
      rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs, him]
      rfl
    · exact (c.integrable_rnDeriv (complexControlMeasure c)).integrableOn

/-- The canonical complex density integrates to the measure of the whole
spectral carrier. -/
lemma integral_rnDeriv_complexControlMeasure (c : ComplexMeasure α) :
    ∫ x, c.rnDeriv (complexControlMeasure c) x ∂complexControlMeasure c =
      c Set.univ := by
  have h := congrArg (fun m : ComplexMeasure α => m Set.univ)
    (withDensity_rnDeriv_complexControlMeasure c)
  rw [withDensityᵥ_apply (c.integrable_rnDeriv (complexControlMeasure c))
      MeasurableSet.univ] at h
  simpa only [Measure.restrict_univ] using h

/-- The canonical positive control measure of a scalar spectral coefficient. -/
def coefficientControlMeasure (u v : H) : Measure α :=
  complexControlMeasure (μS.coefficientMeasure u v)

/-- The canonical Radon--Nikodym density of a scalar spectral coefficient. -/
def coefficientDensity (u v : H) : α → ℂ :=
  (μS.coefficientMeasure u v).rnDeriv
    (μS.coefficientControlMeasure u v)

lemma coefficientDensity_integrable (u v : H) :
    Integrable (μS.coefficientDensity u v)
      (μS.coefficientControlMeasure u v) :=
  ComplexMeasure.integrable_rnDeriv _ _

/-- **Spectral matrix-coefficient reconstruction.**  Integrating the canonical
density of `A ↦ ⟪u, μS(A)v⟫` against its finite positive control measure gives
exactly `⟪u,v⟫`. -/
theorem coefficient_density_integral (u v : H) :
    ∫ x, μS.coefficientDensity u v x
        ∂μS.coefficientControlMeasure u v =
      inner ℂ u v := by
  unfold coefficientDensity coefficientControlMeasure
  rw [integral_rnDeriv_complexControlMeasure, coefficientMeasure_univ]

end SpectralMeasure

/-!
## D. Strong-operator spectral measures
-/

namespace StrongSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : StrongSpectralMeasure α H)

instance instCoeFun : CoeFun (StrongSpectralMeasure α H) fun _ ↦
    Set α → H →L[ℂ] H :=
  ⟨StrongSpectralMeasure.measureOf'⟩

@[simp]
lemma empty : μS ∅ = 0 := μS.empty'

@[simp]
lemma not_measurable {s : Set α} (hs : ¬MeasurableSet s) :
    μS s = 0 := μS.not_measurable' s hs

@[simp]
lemma univ : μS Set.univ = 1 := μS.univ'

lemma isStarProjection (s : Set α) :
    IsStarProjection (μS s) := μS.isStarProjection' s

lemma m_iUnion {s : ℕ → Set α}
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (s i) (s j))
    (x : H) :
    HasSum (fun i => μS (s i) x) (μS (⋃ i, s i) x) :=
  μS.m_iUnion' s hs hdisj x

/-- Strong additivity becomes ordinary scalar complex-measure additivity
after applying a continuous Hilbert-space matrix coefficient. -/
def coefficientMeasure (u v : H) : ComplexMeasure α where
  measureOf' s := inner ℂ u (μS s v)
  empty' := by simp
  not_measurable' s hs := by rw [μS.not_measurable hs]; simp
  m_iUnion' s hs hdisj := by
    exact (μS.m_iUnion hs hdisj v).map
      (innerSL ℂ u).toAddMonoidHom
      (innerSL ℂ u).continuous

@[simp]
lemma coefficientMeasure_apply (u v : H) (s : Set α) :
    μS.coefficientMeasure u v s = inner ℂ u (μS s v) := rfl

@[simp]
lemma coefficientMeasure_univ (u v : H) :
    μS.coefficientMeasure u v Set.univ = inner ℂ u v := by
  simp

/-- The canonical finite positive control measure of a strong spectral
matrix coefficient. -/
def coefficientControlMeasure (u v : H) : Measure α :=
  SpectralMeasure.complexControlMeasure (μS.coefficientMeasure u v)

/-- The canonical `L¹` Radon--Nikodym density of a strong spectral matrix
coefficient. -/
def coefficientDensity (u v : H) : α → ℂ :=
  (μS.coefficientMeasure u v).rnDeriv
    (μS.coefficientControlMeasure u v)

lemma coefficientDensity_integrable (u v : H) :
    Integrable (μS.coefficientDensity u v)
      (μS.coefficientControlMeasure u v) :=
  ComplexMeasure.integrable_rnDeriv _ _

/-- **Strong-PVM matrix-coefficient reconstruction.**  The scalar measure
induced by a continuum strong spectral resolution has a canonical finite
positive control measure whose density integrates to `⟪u,v⟫`. -/
theorem coefficient_density_integral (u v : H) :
    ∫ x, μS.coefficientDensity u v x
        ∂μS.coefficientControlMeasure u v =
      inner ℂ u v := by
  unfold coefficientDensity coefficientControlMeasure
  rw [SpectralMeasure.integral_rnDeriv_complexControlMeasure,
    coefficientMeasure_univ]

end StrongSpectralMeasure

/-!
## E. The canonical continuum configuration PVM

The spectral theorem for a real multiplication operator on `L²` does not need
an abstract unbounded Borel functional calculus: its projections are the
measurable-set indicator multipliers.  This section constructs those
projections and proves strong countable additivity.  The proof uses exactly
the continuum topology required by a nonatomic PVM:

* indicator restriction is a bounded self-adjoint idempotent;
* disjoint ranges are orthogonal;
* finite spectral sums are a single union projection;
* dominated `L²` convergence gives the increasing-union limit;
* orthogonal square summability upgrades natural partial convergence to a
  genuine unconditional `HasSum`.
-/

namespace QuantumMechanics.SpaceDHilbertSpace

open MeasureTheory

/-- Restrict an `L²(Space d)` wavefunction to a measurable set. -/
lemma indicator_memHS {d : ℕ} (s : Set (Space d)) (hs : MeasurableSet s)
    (ψ : SpaceDHilbertSpace d) : MemHS (s.indicator ψ) :=
  MemLp.indicator hs (coe_hilbertSpace_memHS ψ)

/-- The bounded `L²` projection given by multiplication by a measurable-set
indicator. -/
def indicatorProjection {d : ℕ} (s : Set (Space d)) (hs : MeasurableSet s) :
    SpaceDHilbertSpace d →L[ℂ] SpaceDHilbertSpace d :=
  LinearMap.mkContinuous
    { toFun := fun ψ => mk (indicator_memHS s hs ψ)
      map_add' := by
        intro ψ φ
        rw [← mk_add]
        apply (mk_eq_iff _ _).mpr
        filter_upwards [Lp.coeFn_add ψ φ] with x hadd
        by_cases hx : x ∈ s
        · simp only [Pi.add_apply, Set.indicator_of_mem hx]
          exact hadd
        · simp [Set.indicator_of_notMem hx]
      map_smul' := by
        intro c ψ
        rw [← mk_const_smul]
        apply (mk_eq_iff _ _).mpr
        filter_upwards [Lp.coeFn_smul c ψ] with x hsmul
        by_cases hx : x ∈ s
        · simp only [Pi.smul_apply, Set.indicator_of_mem hx]
          simpa using hsmul
        · simp only [Pi.smul_apply, Set.indicator_of_notMem hx, smul_zero] }
    1 (by
      intro ψ
      change ‖mk (indicator_memHS s hs ψ)‖ ≤ 1 * ‖ψ‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [coe_mk_ae (indicator_memHS s hs ψ)] with x hx
      rw [hx, one_mul]
      exact norm_indicator_le_norm_self _ _)

theorem indicatorProjection_apply_ae {d : ℕ} (s : Set (Space d))
    (hs : MeasurableSet s) (ψ : SpaceDHilbertSpace d) :
    (indicatorProjection s hs ψ : Space d → ℂ) =ᵐ[volume] s.indicator ψ :=
  coe_mk_ae (indicator_memHS s hs ψ)

theorem indicatorProjection_norm_le {d : ℕ} (s : Set (Space d))
    (hs : MeasurableSet s) (ψ : SpaceDHilbertSpace d) :
    ‖indicatorProjection s hs ψ‖ ≤ ‖ψ‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [indicatorProjection_apply_ae s hs ψ] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _

theorem indicatorProjection_congr {d : ℕ}
    {s t : Set (Space d)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s = t) :
    indicatorProjection s hs = indicatorProjection t ht := by
  subst t
  rfl

theorem indicatorProjection_union {d : ℕ}
    {s t : Set (Space d)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    indicatorProjection (s ∪ t) (hs.union ht) =
      indicatorProjection s hs + indicatorProjection t ht := by
  ext ψ
  filter_upwards
    [indicatorProjection_apply_ae (s ∪ t) (hs.union ht) ψ,
     indicatorProjection_apply_ae s hs ψ,
     indicatorProjection_apply_ae t ht ψ,
     Lp.coeFn_add (indicatorProjection s hs ψ)
       (indicatorProjection t ht ψ)] with x hu hsl htl hadd
  rw [hu]
  change
    (s ∪ t).indicator (ψ : Space d → ℂ) x =
      ((indicatorProjection s hs ψ + indicatorProjection t ht ψ :
        SpaceDHilbertSpace d) : Space d → ℂ) x
  rw [hadd]
  change
    (s ∪ t).indicator (ψ : Space d → ℂ) x =
      (indicatorProjection s hs ψ : Space d → ℂ) x +
        (indicatorProjection t ht ψ : Space d → ℂ) x
  rw [hsl, htl]
  exact congrFun (Set.indicator_union_of_disjoint hst ψ) x

@[simp]
theorem indicatorProjection_empty {d : ℕ} :
    indicatorProjection (∅ : Set (Space d)) MeasurableSet.empty = 0 := by
  ext ψ
  filter_upwards
    [indicatorProjection_apply_ae (∅ : Set (Space d)) MeasurableSet.empty ψ] with x hx
  rw [hx]
  simp

@[simp]
theorem indicatorProjection_univ {d : ℕ} :
    indicatorProjection (Set.univ : Set (Space d)) MeasurableSet.univ = 1 := by
  ext ψ
  filter_upwards
    [indicatorProjection_apply_ae (Set.univ : Set (Space d)) MeasurableSet.univ ψ] with x hx
  rw [hx]
  simp

/-- The finite union of a family of measurable spectral sets. -/
def finiteUnion {α : Type*} (s : ℕ → Set α) (t : Finset ℕ) : Set α :=
  ⋃ i : {i // i ∈ t}, s i

theorem mem_finiteUnion {α : Type*} {s : ℕ → Set α}
    {t : Finset ℕ} {x : α} :
    x ∈ finiteUnion s t ↔ ∃ i ∈ t, x ∈ s i := by
  simp [finiteUnion]

theorem measurableSet_finiteUnion {α : Type*} [MeasurableSpace α]
    {s : ℕ → Set α} (hs : ∀ i, MeasurableSet (s i)) (t : Finset ℕ) :
    MeasurableSet (finiteUnion s t) := by
  unfold finiteUnion
  exact MeasurableSet.iUnion fun i => hs i

theorem finiteUnion_insert {α : Type*} (s : ℕ → Set α)
    (a : ℕ) (t : Finset ℕ) :
    finiteUnion s (insert a t) = s a ∪ finiteUnion s t := by
  ext x
  simp [mem_finiteUnion]

theorem indicatorProjection_finset_sum {d : ℕ}
    (s : ℕ → Set (Space d)) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (s i) (s j))
    (t : Finset ℕ) (ψ : SpaceDHilbertSpace d) :
    (∑ i ∈ t, indicatorProjection (s i) (hs i) ψ) =
      indicatorProjection (finiteUnion s t)
        (measurableSet_finiteUnion hs t) ψ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [finiteUnion]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, ih]
      have hU : finiteUnion s (insert a t) = s a ∪ finiteUnion s t :=
        finiteUnion_insert s a t
      have hdis : Disjoint (s a) (finiteUnion s t) := by
        rw [Set.disjoint_left]
        intro x hxa hxt
        rcases mem_finiteUnion.mp hxt with ⟨i, hi, hxi⟩
        exact Set.disjoint_left.1 (hdisj (by aesop)) hxa hxi
      have hu := indicatorProjection_union (hs a)
        (measurableSet_finiteUnion hs t) hdis
      calc
        (indicatorProjection (s a) (hs a)) ψ +
            (indicatorProjection (finiteUnion s t)
              (measurableSet_finiteUnion hs t)) ψ =
            (indicatorProjection (s a ∪ finiteUnion s t)
              ((hs a).union (measurableSet_finiteUnion hs t))) ψ := by
              simpa only [ContinuousLinearMap.add_apply] using
                congrArg
                  (fun T : SpaceDHilbertSpace d →L[ℂ] SpaceDHilbertSpace d => T ψ)
                  hu.symm
        _ = indicatorProjection (finiteUnion s (insert a t))
              (measurableSet_finiteUnion hs (insert a t)) ψ := by
              exact congrArg
                (fun T : SpaceDHilbertSpace d →L[ℂ] SpaceDHilbertSpace d => T ψ)
                (indicatorProjection_congr _ _ hU.symm)

theorem indicatorProjection_partial_tendsto {d : ℕ}
    (s : ℕ → Set (Space d)) (hs : ∀ i, MeasurableSet (s i))
    (ψ : SpaceDHilbertSpace d) :
    Tendsto
      (fun n => indicatorProjection (finiteUnion s (Finset.range n))
        (measurableSet_finiteUnion hs (Finset.range n)) ψ)
      atTop
      (nhds (indicatorProjection (⋃ i, s i) (MeasurableSet.iUnion hs) ψ)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
  let U : Set (Space d) := ⋃ i, s i
  let Ufin : ℕ → Set (Space d) := fun n => finiteUnion s (Finset.range n)
  let D : ℕ → Set (Space d) := fun n => U \ Ufin n
  have hU : MeasurableSet U := MeasurableSet.iUnion hs
  have hUfin : ∀ n, MeasurableSet (Ufin n) :=
    fun n => measurableSet_finiteUnion hs (Finset.range n)
  have hD : ∀ n, MeasurableSet (D n) := fun n => hU.diff (hUfin n)
  have h_integral : ∀ n,
      ∫⁻ x, ‖(indicatorProjection (Ufin n) (hUfin n) ψ -
          indicatorProjection U hU ψ) x‖ₑ ^ 2 =
        ∫⁻ x, ‖(D n).indicator ψ x‖ₑ ^ 2 := by
    intro n
    refine lintegral_congr_ae ?_
    filter_upwards
      [Lp.coeFn_sub
        (indicatorProjection (Ufin n) (hUfin n) ψ)
        (indicatorProjection U hU ψ),
       indicatorProjection_apply_ae (Ufin n) (hUfin n) ψ,
       indicatorProjection_apply_ae U hU ψ] with x hsub hfin hall
    rw [hsub]
    change
      ‖(indicatorProjection (Ufin n) (hUfin n) ψ : Space d → ℂ) x -
          (indicatorProjection U hU ψ : Space d → ℂ) x‖ₑ ^ 2 =
        ‖(D n).indicator ψ x‖ₑ ^ 2
    rw [hfin, hall]
    have hsubset : Ufin n ⊆ U := by
      intro y hy
      rcases mem_finiteUnion.mp hy with ⟨i, -, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    by_cases hxfin : x ∈ Ufin n
    · have hxU : x ∈ U := hsubset hxfin
      simp [D, hxfin, hxU]
    · by_cases hxU : x ∈ U <;> simp [D, hxfin, hxU]
  change Tendsto
    (fun n => ∫⁻ x, ‖(indicatorProjection (Ufin n) (hUfin n) ψ -
      indicatorProjection U hU ψ) x‖ₑ ^ 2) atTop (nhds 0)
  simp_rw [h_integral]
  rw [← MeasureTheory.lintegral_zero (α := Space d) (μ := volume)]
  refine tendsto_lintegral_of_dominated_convergence'
    (fun x => ‖ψ x‖ₑ ^ 2) ?_ ?_ ?_ ?_
  · intro n
    exact ((Lp.aestronglyMeasurable ψ).indicator (hD n)).enorm.pow_const _
  · intro n
    filter_upwards with x
    exact ENNReal.pow_le_pow_left
      (enorm_indicator_le_enorm_self (s := D n) ψ x)
  · have hfinite : ∫⁻ x, ‖‖ψ x‖ ^ 2‖ₑ ≠ ⊤ :=
      (memHS_iff.mp (coe_hilbertSpace_memHS ψ)).2.2.ne
    simpa [enorm_pow] using hfinite
  · filter_upwards with x
    rw [← zero_pow two_ne_zero, ← enorm_zero (E := ℂ)]
    refine ENNReal.Tendsto.pow (Tendsto.enorm ?_)
    refine tendsto_nhds_of_eventually_eq ?_
    by_cases hxU : x ∈ U
    · rcases Set.mem_iUnion.mp hxU with ⟨i, hi⟩
      apply eventually_atTop.mpr
      refine ⟨i + 1, fun n hn => ?_⟩
      have hin : i ∈ Finset.range n :=
        Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self i) hn)
      have hxfin : x ∈ Ufin n := mem_finiteUnion.mpr ⟨i, hin, hi⟩
      simp [D, hxfin]
    · exact Eventually.of_forall fun n => by simp [D, hxU]

theorem inner_indicatorProjection_eq_zero_of_disjoint {d : ℕ}
    {s t : Set (Space d)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (ψ φ : SpaceDHilbertSpace d) :
    inner ℂ (indicatorProjection s hs ψ) (indicatorProjection t ht φ) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards
    [indicatorProjection_apply_ae s hs ψ,
     indicatorProjection_apply_ae t ht φ] with x hψ hφ
  rw [hψ, hφ]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.1 hst hxs
    simp [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxt]
  · simp [Set.indicator_of_notMem hxs]

theorem indicatorProjection_hasSum {d : ℕ}
    (s : ℕ → Set (Space d)) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (s i) (s j))
    (ψ : SpaceDHilbertSpace d) :
    HasSum (fun i => indicatorProjection (s i) (hs i) ψ)
      (indicatorProjection (⋃ i, s i) (MeasurableSet.iUnion hs) ψ) := by
  let V : ℕ → Submodule ℂ (SpaceDHilbertSpace d) :=
    fun i => LinearMap.range (indicatorProjection (s i) (hs i)).toLinearMap
  have hV : OrthogonalFamily ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ :=
    OrthogonalFamily.of_pairwise fun i j hij v hv => by
      intro w hw
      rcases hv with ⟨a, rfl⟩
      rcases hw with ⟨b, rfl⟩
      exact inner_indicatorProjection_eq_zero_of_disjoint
        (hs j) (hs i) (hdisj hij.symm) b a
  let f : ∀ i, V i := fun i =>
    ⟨indicatorProjection (s i) (hs i) ψ, ⟨ψ, rfl⟩⟩
  have hsq : Summable fun i => ‖f i‖ ^ 2 := by
    refine summable_of_sum_le (c := ‖ψ‖ ^ 2)
      (fun i => sq_nonneg ‖f i‖) ?_
    intro t
    rw [← hV.norm_sum f t]
    change
      ‖∑ i ∈ t, indicatorProjection (s i) (hs i) ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2
    rw [indicatorProjection_finset_sum s hs hdisj t ψ]
    have hn := indicatorProjection_norm_le
      (finiteUnion s t) (measurableSet_finiteUnion hs t) ψ
    nlinarith [norm_nonneg
      (indicatorProjection (finiteUnion s t) (measurableSet_finiteUnion hs t) ψ),
      norm_nonneg ψ]
  have hsummable : Summable fun i => indicatorProjection (s i) (hs i) ψ := by
    have h := (hV.summable_iff_norm_sq_summable f).2 hsq
    simpa [V, f] using h
  have htarget : Tendsto
      (fun n => ∑ i ∈ Finset.range n, indicatorProjection (s i) (hs i) ψ)
      atTop
      (nhds (indicatorProjection (⋃ i, s i) (MeasurableSet.iUnion hs) ψ)) := by
    refine (indicatorProjection_partial_tendsto s hs ψ).congr' ?_
    exact Eventually.of_forall fun n =>
      (indicatorProjection_finset_sum s hs hdisj (Finset.range n) ψ).symm
  have hsum := hsummable.hasSum
  have heq :
      (∑' i, indicatorProjection (s i) (hs i) ψ) =
        indicatorProjection (⋃ i, s i) (MeasurableSet.iUnion hs) ψ :=
    tendsto_nhds_unique hsum.tendsto_sum_nat htarget
  rwa [← heq]

theorem indicatorProjection_isStarProjection {d : ℕ}
    (s : Set (Space d)) (hs : MeasurableSet s) :
    IsStarProjection (indicatorProjection s hs) := by
  apply ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mpr
  constructor
  · ext ψ
    change
      (indicatorProjection s hs (indicatorProjection s hs ψ) : Space d → ℂ) =ᵐ[volume]
        (indicatorProjection s hs ψ : Space d → ℂ)
    filter_upwards
      [indicatorProjection_apply_ae s hs (indicatorProjection s hs ψ),
       indicatorProjection_apply_ae s hs ψ] with x htwice honce
    rw [htwice]
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx] using honce
    · simpa only [Set.indicator_of_notMem hx] using honce.symm
  · intro ψ φ
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards
      [indicatorProjection_apply_ae s hs ψ,
       indicatorProjection_apply_ae s hs φ] with x hψ hφ
    change
      inner ℂ ((indicatorProjection s hs ψ : Space d → ℂ) x) (φ x) =
        inner ℂ (ψ x) ((indicatorProjection s hs φ : Space d → ℂ) x)
    rw [hψ, hφ]
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]

/-- Measurable sets act by indicator projection; nonmeasurable sets act by
zero, matching the repository's spectral-measure convention. -/
def measurableIndicatorProjection {d : ℕ} (s : Set (Space d)) :
    SpaceDHilbertSpace d →L[ℂ] SpaceDHilbertSpace d := by
  classical
  exact if hs : MeasurableSet s then indicatorProjection s hs else 0

@[simp]
theorem measurableIndicatorProjection_of_measurable {d : ℕ}
    {s : Set (Space d)} (hs : MeasurableSet s) :
    measurableIndicatorProjection s = indicatorProjection s hs := by
  simp [measurableIndicatorProjection, hs]

@[simp]
theorem measurableIndicatorProjection_of_not_measurable {d : ℕ}
    {s : Set (Space d)} (hs : ¬ MeasurableSet s) :
    measurableIndicatorProjection (d := d) s = 0 := by
  simp [measurableIndicatorProjection, hs]

/-- The canonical strong projection-valued measure on continuum
configuration space `Space d`, acting on `L²(Space d, ℂ)` by measurable-set
restriction. -/
def configurationStrongSpectralMeasure (d : ℕ) :
    StrongSpectralMeasure (Space d) (SpaceDHilbertSpace d) where
  measureOf' := measurableIndicatorProjection
  empty' := by simp
  not_measurable' s hs := measurableIndicatorProjection_of_not_measurable hs
  m_iUnion' s hs hdisj ψ := by
    simpa only
      [measurableIndicatorProjection_of_measurable (MeasurableSet.iUnion hs),
       measurableIndicatorProjection_of_measurable (hs _)] using
      indicatorProjection_hasSum s hs hdisj ψ
  isStarProjection' s := by
    by_cases hs : MeasurableSet s
    · rw [measurableIndicatorProjection_of_measurable hs]
      exact indicatorProjection_isStarProjection s hs
    · rw [measurableIndicatorProjection_of_not_measurable hs]
      exact IsStarProjection.zero _
  univ' := by simp

@[simp]
theorem configurationStrongSpectralMeasure_apply_measurable {d : ℕ}
    {s : Set (Space d)} (hs : MeasurableSet s) :
    configurationStrongSpectralMeasure d s = indicatorProjection s hs :=
  measurableIndicatorProjection_of_measurable hs

theorem configurationStrongSpectralMeasure_apply_ae {d : ℕ}
    {s : Set (Space d)} (hs : MeasurableSet s) (ψ : SpaceDHilbertSpace d) :
    (configurationStrongSpectralMeasure d s ψ : Space d → ℂ) =ᵐ[volume]
      s.indicator ψ := by
  rw [configurationStrongSpectralMeasure_apply_measurable hs]
  exact indicatorProjection_apply_ae s hs ψ

end QuantumMechanics.SpaceDHilbertSpace

end
