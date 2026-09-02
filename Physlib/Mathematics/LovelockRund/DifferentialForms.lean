/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Physlib.SpaceAndTime.Space.Module

/-!
# Lovelock--Rund differential forms on finite and infinite model spaces

This module connects Chapter 5 of Lovelock and Rund, *Tensors,
Differential Forms, and Variational Principles*, to Mathlib's existing
continuous alternating-map differential-form API.

The model space `E` is an arbitrary normed vector space. In particular, none
of the definitions or theorems in the first part requires `E` to be finite
dimensional. This gives the pointwise differential-form layer needed for
continuum fields and infinite-dimensional configuration spaces.

The module reuses:

* `ContinuousAlternatingMap` as the carrier of alternating covariant tensors;
* normalized alternatization and `ContinuousMultilinearMap.uncurrySum` for the
  continuum wedge product;
* `extDeriv` for the exterior derivative;
* `extDeriv_extDeriv` for `d² = 0`;
* `extDeriv_pullback` for naturality under pullback;
* `extDeriv_apply_vectorField` for the vector-field and Lie-bracket formula.

No coordinate-specific replacement for these APIs is introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open Filter Set ContinuousAlternatingMap VectorField
open scoped Topology

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ} {r : WithTop ℕ∞}

/-- A differential `n`-form on a normed model space. The model space may be
infinite dimensional. -/
abbrev DifferentialForm (𝕜 E F : Type*)
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n : ℕ) :=
  E → E [⋀^Fin n]→L[𝕜] F

/-! ## Continuum wedge product -/

/-- The normalization converting full alternatization into the usual shuffle
wedge of a `p`-form and a `q`-form.  The factorials are nonzero over `ℝ`. -/
def continuumWedgeNormalization (p q : ℕ) : ℝ :=
  (((p.factorial * q.factorial : ℕ) : ℝ))⁻¹

private lemma units_smul_mul_left (u : ℤˣ) (c a b : ℝ) :
    u • ((c * a) * b) = c * (u • (a * b)) := by
  simp [Units.smul_def]
  ring

private lemma units_smul_mul_right (u : ℤˣ) (c a b : ℝ) :
    u • (a * (c * b)) = c * (u • (a * b)) := by
  simp [Units.smul_def]
  ring

/-- The pointwise continuum wedge of two continuous alternating maps.

The two maps are first combined into a continuous multilinear map on the sum
of their argument sets, reindexed by `Fin p ⊕ Fin q ≃ Fin (p + q)`, and fully
alternated.  Division by `p! q!` removes the repetitions internal to the two
already-alternating factors, yielding the standard shuffle normalization.
Continuity and alternation are carried by the resulting bundled
`ContinuousAlternatingMap`; no finite coordinate expansion is assumed. -/
def continuumWedgeAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ}
    (α : E [⋀^Fin p]→L[ℝ] ℝ) (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    E [⋀^Fin (p + q)]→L[ℝ] ℝ :=
  continuumWedgeNormalization p q •
    ContinuousMultilinearMap.alternatization
      (ContinuousMultilinearMap.domDomCongr finSumFinEquiv
        ((α.toContinuousMultilinearMap.smulRight β.toContinuousMultilinearMap).uncurrySum))

/-- Evaluation of the continuum wedge as the normalized signed permutation
sum.  For alternating inputs this is equivalent to the usual shuffle sum. -/
theorem continuumWedgeAt_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (α : E [⋀^Fin p]→L[ℝ] ℝ) (β : E [⋀^Fin q]→L[ℝ] ℝ)
    (v : Fin (p + q) → E) :
    continuumWedgeAt α β v = continuumWedgeNormalization p q •
      ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
        (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
          β (fun j => v (σ (finSumFinEquiv (Sum.inr j))))) := by
  simp [continuumWedgeAt, ContinuousMultilinearMap.alternatization_apply_apply,
    Function.comp_def]

@[simp]
theorem continuumWedgeAt_zero_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    continuumWedgeAt (0 : E [⋀^Fin p]→L[ℝ] ℝ) β = 0 := by
  ext v
  simp [continuumWedgeAt_apply]

theorem continuumWedgeAt_add_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (α α' : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    continuumWedgeAt (α + α') β = continuumWedgeAt α β + continuumWedgeAt α' β := by
  ext v
  simp only [continuumWedgeAt_apply, ContinuousAlternatingMap.add_apply]
  simp only [smul_eq_mul]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [add_mul]
  exact smul_add (Equiv.Perm.sign σ)
    (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
      β (fun j => v (σ (finSumFinEquiv (Sum.inr j)))))
    (α' (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
      β (fun j => v (σ (finSumFinEquiv (Sum.inr j)))))

theorem continuumWedgeAt_smul_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (c : ℝ) (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    continuumWedgeAt (c • α) β = c • continuumWedgeAt α β := by
  ext v
  simp only [continuumWedgeAt_apply, ContinuousAlternatingMap.smul_apply]
  simp only [smul_eq_mul]
  have hsum :
      (∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
          ((c * α (fun i => v (σ (finSumFinEquiv (Sum.inl i))))) *
            β (fun j => v (σ (finSumFinEquiv (Sum.inr j)))))) =
        c * ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
          (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
            β (fun j => v (σ (finSumFinEquiv (Sum.inr j))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact units_smul_mul_left (Equiv.Perm.sign σ) c _ _
  rw [hsum]
  ring

@[simp]
theorem continuumWedgeAt_zero_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (α : E [⋀^Fin p]→L[ℝ] ℝ) :
    continuumWedgeAt α (0 : E [⋀^Fin q]→L[ℝ] ℝ) = 0 := by
  ext v
  simp [continuumWedgeAt_apply]

theorem continuumWedgeAt_add_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β β' : E [⋀^Fin q]→L[ℝ] ℝ) :
    continuumWedgeAt α (β + β') = continuumWedgeAt α β + continuumWedgeAt α β' := by
  ext v
  simp only [continuumWedgeAt_apply, ContinuousAlternatingMap.add_apply]
  simp only [smul_eq_mul]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_add]
  exact smul_add (Equiv.Perm.sign σ)
    (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
      β (fun j => v (σ (finSumFinEquiv (Sum.inr j)))))
    (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
      β' (fun j => v (σ (finSumFinEquiv (Sum.inr j)))))

theorem continuumWedgeAt_smul_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (c : ℝ) (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    continuumWedgeAt α (c • β) = c • continuumWedgeAt α β := by
  ext v
  simp only [continuumWedgeAt_apply, ContinuousAlternatingMap.smul_apply]
  simp only [smul_eq_mul]
  have hsum :
      (∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
          (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
            (c * β (fun j => v (σ (finSumFinEquiv (Sum.inr j))))))) =
        c * ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
          (α (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
            β (fun j => v (σ (finSumFinEquiv (Sum.inr j))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact units_smul_mul_right (Equiv.Perm.sign σ) c _ _
  rw [hsum]
  ring

/-- The continuum wedge is natural under continuous linear pullback on the
tangent-space carrier. -/
theorem continuumWedgeAt_compContinuousLinearMap
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {p q : ℕ} (α : E [⋀^Fin p]→L[ℝ] ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) (L : E' →L[ℝ] E) :
    (continuumWedgeAt α β).compContinuousLinearMap L =
      continuumWedgeAt (α.compContinuousLinearMap L)
        (β.compContinuousLinearMap L) := by
  ext v
  simp [continuumWedgeAt_apply, Function.comp_def]

/-- Two continuum two-forms commute under the wedge product, the even-degree
case of graded commutativity.  The proof reindexes the signed permutation sum
by the block-flip permutation, whose sign is positive in degree `(2,2)`. -/
theorem continuumWedgeAt_two_comm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    continuumWedgeAt α β = continuumWedgeAt β α := by
  ext v
  rw [continuumWedgeAt_apply, continuumWedgeAt_apply]
  congr 1
  let τ : Equiv.Perm (Fin (2 + 2)) := finAddFlip
  have hτ : Equiv.Perm.sign τ = 1 := by
    decide
  apply Fintype.sum_equiv (Equiv.mulRight τ)
  intro σ
  rw [show (Equiv.mulRight τ) σ = σ * τ by rfl]
  rw [Equiv.Perm.sign_mul, hτ, mul_one]
  simp only [τ, finAddFlip, Equiv.trans_apply, Equiv.sumComm_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Equiv.Perm.coe_mul, Function.comp_apply, Sum.swap_inl, Sum.swap_inr]
  rw [mul_comm]

/-- The continuum wedge product of scalar-valued differential forms. -/
def continuumWedge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (α : DifferentialForm ℝ E ℝ p)
    (β : DifferentialForm ℝ E ℝ q) : DifferentialForm ℝ E ℝ (p + q) :=
  fun x => continuumWedgeAt (α x) (β x)

/-- The continuum wedge bundled as a bilinear map.  This is the reusable
constructor for Chern--Weil, Yang--Mills, and differential-form products. -/
def continuumWedgeBilinear {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p q : ℕ) :
    DifferentialForm ℝ E ℝ p →ₗ[ℝ]
      DifferentialForm ℝ E ℝ q →ₗ[ℝ] DifferentialForm ℝ E ℝ (p + q) :=
  LinearMap.mk₂ ℝ continuumWedge
    (fun α α' β => by funext x; exact continuumWedgeAt_add_left _ _ _)
    (fun c α β => by funext x; exact continuumWedgeAt_smul_left _ _ _)
    (fun α β β' => by funext x; exact continuumWedgeAt_add_right _ _ _)
    (fun c α β => by funext x; exact continuumWedgeAt_smul_right _ _ _)

@[simp]
theorem continuumWedgeBilinear_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (α : DifferentialForm ℝ E ℝ p)
    (β : DifferentialForm ℝ E ℝ q) :
    continuumWedgeBilinear p q α β = continuumWedge α β := rfl

/-- Independent rescalings of the two factors multiply their weights. -/
theorem continuumWedge_smul_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} (a b : ℝ) (α : DifferentialForm ℝ E ℝ p)
    (β : DifferentialForm ℝ E ℝ q) :
    continuumWedge (a • α) (b • β) = (a * b) • continuumWedge α β := by
  change continuumWedgeBilinear p q (a • α) (b • β) = _
  simp
  rw [smul_smul, mul_comm]

/-- Even-degree graded commutativity for continuum two-forms. -/
theorem continuumWedge_two_comm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α β : DifferentialForm ℝ E ℝ 2) :
    continuumWedge α β = continuumWedge β α := by
  funext x
  exact continuumWedgeAt_two_comm (α x) (β x)

/-- A differential form is closed when its exterior derivative vanishes. -/
def IsClosed (ω : DifferentialForm 𝕜 E F n) : Prop :=
  extDeriv ω = 0

/-- A degree-`n+1` form is smoothly exact when it is the exterior derivative
of a `C^r` degree-`n` form. -/
def IsSmoothlyExact (r : WithTop ℕ∞)
    (ω : DifferentialForm 𝕜 E F (n + 1)) : Prop :=
  ∃ η : DifferentialForm 𝕜 E F n, ContDiff 𝕜 r η ∧ ω = extDeriv η

/-- Exterior differentiation of a sufficiently smooth form produces a closed
form. This is the coordinate-free `d² = 0` identity. -/
theorem extDeriv_isClosed
    {ω : DifferentialForm 𝕜 E F n}
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    IsClosed (extDeriv ω) := by
  unfold IsClosed
  exact extDeriv_extDeriv hω hr

/-- Every smoothly exact form is closed. -/
theorem smoothlyExact_isClosed
    {ω : DifferentialForm 𝕜 E F (n + 1)}
    (hω : IsSmoothlyExact (𝕜 := 𝕜) r ω)
    (hr : minSmoothness 𝕜 2 ≤ r) :
    IsClosed ω := by
  rcases hω with ⟨η, hη, rfl⟩
  exact extDeriv_isClosed hη hr

/-- Pullback of a differential form along a map between normed model spaces. -/
def pullbackForm
    (ω : DifferentialForm 𝕜 F G n) (f : E → F) :
    DifferentialForm 𝕜 E G n :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)

/-- Pullback preserves the constructed continuum wedge product. -/
theorem pullbackForm_continuumWedge
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {p q : ℕ} (α : DifferentialForm ℝ E ℝ p)
    (β : DifferentialForm ℝ E ℝ q) (f : E' → E) :
    pullbackForm (continuumWedge α β) f =
      continuumWedge (pullbackForm α f) (pullbackForm β f) := by
  funext x
  exact continuumWedgeAt_compContinuousLinearMap (α (f x)) (β (f x))
    (fderiv ℝ f x)

/-- Exterior differentiation commutes pointwise with pullback. -/
theorem extDeriv_pullbackForm
    {ω : DifferentialForm 𝕜 F G n} {f : E → F} {x : E}
    (hω : DifferentiableAt 𝕜 ω (f x))
    (hf : ContDiffAt 𝕜 r f x)
    (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (pullbackForm ω f) x =
      (extDeriv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x) := by
  exact extDeriv_pullback hω hf hr

/-- Pointwise closedness is preserved by pullback. -/
theorem pullbackForm_closedAt
    {ω : DifferentialForm 𝕜 F G n} {f : E → F} {x : E}
    (hω : DifferentiableAt 𝕜 ω (f x))
    (hf : ContDiffAt 𝕜 r f x)
    (hr : minSmoothness 𝕜 2 ≤ r)
    (hclosed : extDeriv ω (f x) = 0) :
    extDeriv (pullbackForm ω f) x = 0 := by
  rw [extDeriv_pullbackForm hω hf hr, hclosed]
  rfl

/-- Evaluation formula for the exterior derivative on commuting vector fields.
This is the coordinate-free version of the component formula used throughout
Lovelock--Rund Chapter 5. -/
theorem extDeriv_apply_commuting_vectorFields
    {ω : DifferentialForm 𝕜 E F n}
    {V : Fin (n + 1) → E → E} {x : E}
    (hω : DifferentiableAt 𝕜 ω x)
    (hV : ∀ i, DifferentiableAt 𝕜 (V i) x)
    (hcomm : Pairwise fun i j => lieBracket 𝕜 (V i) (V j) x = 0) :
    extDeriv ω x (V · x) =
      ∑ i, (-1) ^ i.val •
        fderiv 𝕜 (fun y => ω y (i.removeNth (V · y))) x (V i x) :=
  extDeriv_apply_vectorField_of_pairwise_commute hω hV hcomm

/-- Differential forms on ordinary spatial continuum `Space d`. -/
abbrev SpaceDifferentialForm (d n : ℕ) :=
  DifferentialForm ℝ (Space d) ℝ n

/-- The `d² = 0` theorem specialized to the spatial continuum. -/
theorem space_extDeriv_extDeriv_zero
    {d n : ℕ} {ω : SpaceDifferentialForm d n}
    (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r) :
    extDeriv (extDeriv ω) = 0 :=
  extDeriv_extDeriv hω hr

end Physlib.Mathematics.LovelockRund

end
