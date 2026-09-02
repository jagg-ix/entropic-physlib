/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.AffineCollineation
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeAffineReconstruction
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalPreorder
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLightRayPreservation
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
meta import Zil

/-!
# The Alexandrov–Zeeman converse: causal automorphisms are conformal Poincaré

Malament's theorem has two halves.  The *sufficiency* half — a conformal rescaling of
the metric leaves the causal order unchanged — is proved in
`CausalConeLorentzReconstruction` (`conformalFactor_causalCharacter_invariant`).  This
module supplies the *converse* (Alexandrov–Zeeman): a causal automorphism of Minkowski
space is a conformal Poincaré transformation.

The converse decomposes into a geometric reduction and an algebraic conclusion.  This
module now proves substantially more of both stages in physical 3+1 dimensions:

* **Light rays.**  `CausalConeLightRayPreservation` proves null-cone preservation for a
  bare causal automorphism in 3+1 dimensions.  A future-null Alexandrov interval is
  characterized intrinsically as a causal interval that is a chain, so this stage needs
  neither continuity nor chronological preservation; moreover
  `futureNullRay_image_of_causalAutomorphism` upgrades whole-cone preservation to exact
  setwise preservation of each individual nondegenerate future null affine ray, and
  `nullAffineLine_image_of_causalAutomorphism` extends this to complete null affine lines.
  The companion affine-incidence module reconstructs and preserves the tangent null
  hyperplanes from those lines and null separation alone.

* **Fundamental-theorem output.** The affine-incidence module constructs independent null
  normals for spacelike directions, preserves spacelike lines and hyperbolic planes,
  recovers timelike lines as intersections of two such planes, and consequently preserves
  every nondegenerate affine line. The fundamental theorem of real affine geometry then
  supplies an `AffineEquiv` without continuity or affineness being assumed. After this,
  `affine_causalAutomorphism_preserves_nullCone` derives null preservation from the causal
  order and `affine_causalAutomorphism_eq_translation_dilation_lorentz` supplies the
  algebraic classification. `causalAutomorphism_eq_translation_dilation_lorentz` combines
  those stages into the unrestricted result.

* **Null-cone metric rigidity.**  `same_null_cone_proportional` proves directly that a
  symmetric continuous bilinear form on 3+1 Minkowski space with exactly the same null
  cone is a scalar multiple of the Minkowski form.  This replaces the former conformal-form
  premise by a theorem.

* **Algebraic conclusion.**  A conformal-linear map is exactly a positive
  dilation of a Lorentz transformation
  (`conformalLorentz_eq_smul_lorentz`, `smul_lorentz_isConformalLorentz`): normalising by
  `√c` yields a genuine `IsLorentz` map — a `LorentzGroup` element
  (`conformalLorentz_toMatrix_mem_lorentzGroup`).  Together with a spatial translation this
  is a conformal Poincaré transformation.

The order-theoretic **Alexandrov** content — that a causal automorphism preserves the
Alexandrov intervals (causal diamonds) `I[p,q]` — is proved directly
(`causalDiamond_image_of_isCausalAutomorphism`), with spatial translations exhibited as
causal automorphisms (`translation_isCausalAutomorphism`) so the notion is non-vacuous.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace LorentzGroup Filter

variable {d : ℕ}

/-! ## Bilinearity of the Minkowski form under scalar multiplication -/

private lemma mink_smul_left (a : ℝ) (u v : Vector d) : ⟪a • u, v⟫ₘ = a * ⟪u, v⟫ₘ := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma mink_smul_right (a : ℝ) (u v : Vector d) : ⟪u, a • v⟫ₘ = a * ⟪u, v⟫ₘ := by
  simp only [map_smul, smul_eq_mul]

private lemma mink_neg_self (v : Vector d) : ⟪-v, -v⟫ₘ = ⟪v, v⟫ₘ := by
  rw [show -v = (-1 : ℝ) • v by simp, mink_smul_left, mink_smul_right]
  ring

/-! ## The algebraic Alexandrov–Zeeman conclusion: conformal-linear = dilation ∘ Lorentz -/

/-- **Normalising a conformal-linear map yields a Lorentz map.**  If a linear map `f`
scales the Minkowski form by `c > 0` (`⟪f u, f v⟫ₘ = c · ⟪u, v⟫ₘ`), then `(√c)⁻¹ • f`
preserves the Minkowski form exactly — it is `IsLorentz`. -/
@[zil_level physical_theorem]
theorem conformalLorentz_normalized_isLorentz {f : Vector d →ₗ[ℝ] Vector d} {c : ℝ}
    (hc : 0 < c) (hf : ∀ u v, ⟪f u, f v⟫ₘ = c * ⟪u, v⟫ₘ) :
    IsLorentz ((Real.sqrt c)⁻¹ • f) := by
  intro p q
  simp only [LinearMap.smul_apply]
  rw [mink_smul_left, mink_smul_right, hf]
  have ha2 : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ = c⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le]
  calc (Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * (c * ⟪p, q⟫ₘ))
      = ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) * c * ⟪p, q⟫ₘ := by ring
    _ = c⁻¹ * c * ⟪p, q⟫ₘ := by rw [ha2]
    _ = ⟪p, q⟫ₘ := by rw [inv_mul_cancel₀ (ne_of_gt hc), one_mul]

/-- **A conformal-linear map is a positive dilation of a Lorentz transformation.**  The
Alexandrov–Zeeman conclusion at the linear level: `f = √c • g` with `g` an `IsLorentz`
map. -/
@[zil_level bridge_theorem]
theorem conformalLorentz_eq_smul_lorentz {f : Vector d →ₗ[ℝ] Vector d} {c : ℝ}
    (hc : 0 < c) (hf : ∀ u v, ⟪f u, f v⟫ₘ = c * ⟪u, v⟫ₘ) :
    ∃ g : Vector d →ₗ[ℝ] Vector d, IsLorentz g ∧ f = Real.sqrt c • g := by
  refine ⟨(Real.sqrt c)⁻¹ • f, conformalLorentz_normalized_isLorentz hc hf, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc)), one_smul]

/-- **The dilation-normalised conformal map is a `LorentzGroup` element** — its matrix in
the standard basis lies in the Lorentz group, exhibiting `f` explicitly as
`√c · (Lorentz matrix)`. -/
@[zil_level bridge_theorem]
theorem conformalLorentz_toMatrix_mem_lorentzGroup {f : Vector d →ₗ[ℝ] Vector d} {c : ℝ}
    (hc : 0 < c) (hf : ∀ u v, ⟪f u, f v⟫ₘ = c * ⟪u, v⟫ₘ) :
    LinearMap.toMatrix Vector.basis Vector.basis ((Real.sqrt c)⁻¹ • f) ∈ LorentzGroup d :=
  (isLorentz_iff_toMatrix_mem_lorentzGroup _).mp (conformalLorentz_normalized_isLorentz hc hf)

/-- **Converse: a positive dilation of a Lorentz map is conformal-linear** with factor
`a²`.  Together with the previous theorem this characterises the conformal-linear maps as
exactly the positive dilations of Lorentz transformations. -/
@[zil_level physical_theorem]
theorem smul_lorentz_isConformalLorentz {a : ℝ} {g : Vector d →ₗ[ℝ] Vector d}
    (hg : IsLorentz g) (u v : Vector d) :
    ⟪(a • g) u, (a • g) v⟫ₘ = a ^ 2 * ⟪u, v⟫ₘ := by
  simp only [LinearMap.smul_apply]
  rw [mink_smul_left, mink_smul_right, hg]; ring

/-! ## The Alexandrov content: causal automorphisms preserve causal diamonds -/

/-- **Spatial translations are causal automorphisms** — the causal relations depend only
on the difference `q − p`, which translation leaves unchanged.  (Non-vacuity witness.) -/
@[zil_level physical_theorem]
theorem translation_isCausalAutomorphism (t : Vector d) :
    IsCausalAutomorphism (fun v => v + t) := by
  refine ⟨(Equiv.addRight t).bijective, fun p q => ?_⟩
  have h : (q + t) - (p + t) = q - p := by abel
  simp only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary,
    Set.mem_setOf_eq, h]

/-- **A causal automorphism preserves Alexandrov intervals (causal diamonds).**  The image
of the causal diamond `I[p,q]` under a causal automorphism `φ` is the causal diamond
`I[φp, φq]` — the order-theoretic (Alexandrov) content of the Alexandrov–Zeeman
correspondence between the causal order and the interval structure. -/
@[zil_level bridge_theorem]
theorem causalDiamond_image_of_isCausalAutomorphism {φ : Vector d → Vector d}
    (hφ : IsCausalAutomorphism φ) (p q : Vector d) :
    φ '' causalDiamond p q = causalDiamond (φ p) (φ q) := by
  obtain ⟨hbij, hord⟩ := hφ
  ext s
  simp only [Set.mem_image, causalDiamond, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, ⟨hpr, hrq⟩, rfl⟩
    exact ⟨(hord p r).mpr hpr, (hord r q).mpr hrq⟩
  · rintro ⟨hps, hsq⟩
    obtain ⟨r, rfl⟩ := hbij.surjective s
    exact ⟨r, ⟨(hord p r).mp hps, (hord r q).mp hsq⟩, rfl⟩

/-! ## In 3+1 dimensions the null cone determines the metric up to scale -/

/-- The standard future-pointing time basis vector in physical 3+1 Minkowski space. -/
def temporalBasis3 : Vector 3 := basis (Sum.inl 0)

/-- The three standard spatial basis vectors in physical 3+1 Minkowski space. -/
def spatialBasis3 (i : Fin 3) : Vector 3 := basis (Sum.inr i)

private lemma mink_temporal_add_spatial_null (i : Fin 3) :
    ⟪temporalBasis3 + spatialBasis3 i,
      temporalBasis3 + spatialBasis3 i⟫ₘ = 0 := by
  rw [minkowskiProduct_toCoord]
  simp [temporalBasis3, spatialBasis3, basis_apply]

private lemma mink_temporal_sub_spatial_null (i : Fin 3) :
    ⟪temporalBasis3 - spatialBasis3 i,
      temporalBasis3 - spatialBasis3 i⟫ₘ = 0 := by
  rw [minkowskiProduct_toCoord]
  simp [temporalBasis3, spatialBasis3, basis_apply]

private lemma mink_pythagorean_null (i j : Fin 3) (hij : i ≠ j) :
    ⟪temporalBasis3 + (3 / 5 : ℝ) • spatialBasis3 i +
          (4 / 5 : ℝ) • spatialBasis3 j,
      temporalBasis3 + (3 / 5 : ℝ) • spatialBasis3 i +
          (4 / 5 : ℝ) • spatialBasis3 j⟫ₘ = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [minkowskiProduct_toCoord, temporalBasis3, spatialBasis3, basis_apply] <;>
    norm_num

/-- **The null cone determines the metric up to scale in 3+1 dimensions.**
If a symmetric continuous bilinear form `B` vanishes on exactly the Minkowski-null
vectors, then `B = c · η` for a scalar `c`.  The proof reconstructs the matrix entries
from the null vectors `e₀ ± eᵢ` and the rational Pythagorean null vectors
`e₀ + (3/5)eᵢ + (4/5)eⱼ`; no nondegeneracy or conformality premise is assumed. -/
@[zil_level physical_theorem]
theorem same_null_cone_proportional
    (B : Vector 3 →L[ℝ] Vector 3 →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hcone : ∀ v, ⟪v, v⟫ₘ = 0 ↔ B v v = 0) :
    ∃ c : ℝ, ∀ u v, B u v = c * ⟪u, v⟫ₘ := by
  let c := B temporalBasis3 temporalBasis3
  have htimeSpace : ∀ i : Fin 3, B temporalBasis3 (spatialBasis3 i) = 0 := by
    intro i
    have hp := (hcone (temporalBasis3 + spatialBasis3 i)).mp
      (mink_temporal_add_spatial_null i)
    have hm := (hcone (temporalBasis3 - spatialBasis3 i)).mp
      (mink_temporal_sub_spatial_null i)
    simp only [map_add, map_sub, add_apply, sub_apply] at hp hm
    rw [hBsymm (spatialBasis3 i) temporalBasis3] at hp hm
    linarith
  have hspaceDiag : ∀ i : Fin 3, B (spatialBasis3 i) (spatialBasis3 i) = -c := by
    intro i
    have hp := (hcone (temporalBasis3 + spatialBasis3 i)).mp
      (mink_temporal_add_spatial_null i)
    simp only [map_add, add_apply] at hp
    rw [hBsymm (spatialBasis3 i) temporalBasis3, htimeSpace i] at hp
    dsimp [c]
    linarith
  have hspaceCross : ∀ i j : Fin 3, i ≠ j →
      B (spatialBasis3 i) (spatialBasis3 j) = 0 := by
    intro i j hij
    let w := temporalBasis3 + (3 / 5 : ℝ) • spatialBasis3 i +
      (4 / 5 : ℝ) • spatialBasis3 j
    have hw := (hcone w).mp (mink_pythagorean_null i j hij)
    dsimp [w] at hw
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at hw
    rw [hBsymm (spatialBasis3 i) temporalBasis3,
      hBsymm (spatialBasis3 j) temporalBasis3,
      hBsymm (spatialBasis3 j) (spatialBasis3 i),
      htimeSpace i, htimeSpace j, hspaceDiag i, hspaceDiag j] at hw
    norm_num at hw
    linarith
  refine ⟨c, ?_⟩
  have hmaps : B = c • minkowskiProduct := by
    apply ContinuousLinearMap.toLinearMap₁₂_injective
    apply LinearMap.ext_basis basis basis
    intro μ ν
    change B (basis μ) (basis ν) = c * ⟪basis μ, basis ν⟫ₘ
    rcases μ with μ | i
    · fin_cases μ
      rcases ν with ν | j
      · fin_cases ν
        simp [c, temporalBasis3, minkowskiProduct_basis_left,
          minkowskiProduct_basis_right]
      · simpa [temporalBasis3, spatialBasis3, minkowskiProduct_basis_left,
          minkowskiProduct_basis_right] using htimeSpace j
    · rcases ν with ν | j
      · fin_cases ν
        rw [hBsymm]
        simpa [temporalBasis3, spatialBasis3, minkowskiProduct_basis_left,
          minkowskiProduct_basis_right] using htimeSpace i
      · by_cases hij : i = j
        · subst j
          simpa [spatialBasis3, minkowskiProduct_basis_left,
            minkowskiProduct_basis_right] using hspaceDiag i
        · simpa [spatialBasis3, minkowskiProduct_basis_left,
            minkowskiProduct_basis_right, hij] using hspaceCross i j hij
  intro u v
  rw [hmaps]
  simp

private def minkowskiPullback (f : Vector 3 →L[ℝ] Vector 3) :
    Vector 3 →L[ℝ] Vector 3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ f).comp (minkowskiProduct.comp f)

@[simp] private lemma minkowskiPullback_apply
    (f : Vector 3 →L[ℝ] Vector 3) (u v : Vector 3) :
    minkowskiPullback f u v = ⟪f u, f v⟫ₘ := rfl

/-- A continuous linear null-cone automorphism in 3+1 dimensions is conformal-linear.
This is the direct pullback-form consequence of `same_null_cone_proportional`. -/
@[zil_level bridge_theorem]
theorem nullCone_preserving_linear_is_conformal
    (f : Vector 3 →L[ℝ] Vector 3)
    (hcone : ∀ v, ⟪v, v⟫ₘ = 0 ↔ ⟪f v, f v⟫ₘ = 0) :
    ∃ c : ℝ, ∀ u v, ⟪f u, f v⟫ₘ = c * ⟪u, v⟫ₘ := by
  simpa only [minkowskiPullback_apply] using same_null_cone_proportional
    (minkowskiPullback f) (fun u v => minkowskiProduct_symm _ _) hcone

/-- If a null-cone-preserving linear map sends the standard time vector to a timelike
vector, its conformal factor is strictly positive. -/
@[zil_level bridge_theorem]
theorem nullCone_preserving_linear_is_positive_conformal
    (f : Vector 3 →L[ℝ] Vector 3)
    (hcone : ∀ v, ⟪v, v⟫ₘ = 0 ↔ ⟪f v, f v⟫ₘ = 0)
    (htime : 0 < ⟪f temporalBasis3, f temporalBasis3⟫ₘ) :
    ∃ c : ℝ, 0 < c ∧ ∀ u v, ⟪f u, f v⟫ₘ = c * ⟪u, v⟫ₘ := by
  obtain ⟨c, hc⟩ := nullCone_preserving_linear_is_conformal f hcone
  refine ⟨c, ?_, hc⟩
  have hη : ⟪temporalBasis3, temporalBasis3⟫ₘ = 1 := by
    simp [temporalBasis3, minkowskiProduct_basis_left]
  simpa [hc temporalBasis3 temporalBasis3, hη] using htime

/-- A time-orientation-preserving linear null-cone automorphism is a positive dilation
of a Lorentz transformation. -/
@[zil_level bridge_theorem]
theorem nullCone_preserving_linear_eq_dilation_lorentz
    (f : Vector 3 →L[ℝ] Vector 3)
    (hcone : ∀ v, ⟪v, v⟫ₘ = 0 ↔ ⟪f v, f v⟫ₘ = 0)
    (htime : 0 < ⟪f temporalBasis3, f temporalBasis3⟫ₘ) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : Vector 3 →ₗ[ℝ] Vector 3,
      IsLorentz g ∧ f.toLinearMap = Real.sqrt c • g := by
  obtain ⟨c, hc, hform⟩ :=
    nullCone_preserving_linear_is_positive_conformal f hcone htime
  obtain ⟨g, hg, heq⟩ := conformalLorentz_eq_smul_lorentz hc hform
  exact ⟨c, hc, g, hg, heq⟩

/-- A map preserves null separation when every displacement is null exactly when its
image displacement is null. -/
def PreservesNullSeparation (φ : Vector 3 → Vector 3) : Prop :=
  ∀ p q, ⟪q - p, q - p⟫ₘ = 0 ↔ ⟪φ q - φ p, φ q - φ p⟫ₘ = 0

/-- An affine causal and null-separation automorphism is a translation followed by a
positive dilation and a Lorentz transformation.  The null-separation premise is removed
entirely by `affine_causalAutomorphism_eq_translation_dilation_lorentz` below. -/
@[zil_level bridge_theorem]
theorem affine_causal_null_preserver_eq_translation_dilation_lorentz
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e)
    (hnull : PreservesNullSeparation e) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : Vector 3 →ₗ[ℝ] Vector 3,
      IsLorentz g ∧ ∀ x, e x = Real.sqrt c • g x + e 0 := by
  let f : Vector 3 →L[ℝ] Vector 3 := e.linear.toContinuousLinearEquiv.toContinuousLinearMap
  have hf_apply (v : Vector 3) : f v = e v - e 0 := by
    change e.linear v = e v - e 0
    simpa using e.toAffineMap.linearMap_vsub v 0
  have hfcone : ∀ v, ⟪v, v⟫ₘ = 0 ↔ ⟪f v, f v⟫ₘ = 0 := by
    intro v
    rw [hf_apply]
    simpa [PreservesNullSeparation] using hnull 0 v
  have hfuture : causallyFollows (e 0) (e temporalBasis3) := by
    exact (hcausal.2 0 temporalBasis3).2 (by
      simp [causallyFollows, interiorFutureLightCone, futureLightConeBoundary,
        temporalBasis3, causalCharacter, minkowskiProduct_basis_left])
  have hnotnull : ⟪f temporalBasis3, f temporalBasis3⟫ₘ ≠ 0 := by
    intro hzero
    have hsource : ⟪temporalBasis3, temporalBasis3⟫ₘ ≠ 0 := by
      simp [temporalBasis3, minkowskiProduct_basis_left]
    exact hsource ((hfcone temporalBasis3).mpr hzero)
  have htime : 0 < ⟪f temporalBasis3, f temporalBasis3⟫ₘ := by
    rw [hf_apply]
    rcases hfuture with htimelike | hboundary
    · exact (timeLike_iff_norm_sq_pos _).mp htimelike.1
    · exact False.elim (hnotnull (by
        rw [hf_apply]
        exact (lightLike_iff_norm_sq_zero _).mp hboundary.1))
  obtain ⟨c, hc, g, hg, hlinear⟩ :=
    nullCone_preserving_linear_eq_dilation_lorentz f hfcone htime
  refine ⟨c, hc, g, hg, fun x => ?_⟩
  have he_aff : e x = e.linear x + e 0 := congrFun e.toAffineMap.decomp x
  rw [he_aff]
  change e.linear x + e 0 = Real.sqrt c • g x + e 0
  congr 1
  exact LinearMap.congr_fun hlinear x

/-! ## The closed cone, its interior, and automatic null preservation -/

/-- The closed future causal cone in physical 3+1 Minkowski space. -/
def futureCausalCone3 : Set (Vector 3) := {v | IsFutureCausal v}

/-- The open future timelike cone in physical 3+1 Minkowski space. -/
def futureTimelikeCone3 : Set (Vector 3) :=
  {v | 0 < ⟪v, v⟫ₘ ∧ 0 < timeComponent v}

private lemma isOpen_futureTimelikeCone3 : IsOpen futureTimelikeCone3 := by
  have hQ : Continuous (fun v : Vector 3 => ⟪v, v⟫ₘ) := by
    conv =>
      enter [1, v]
      rw [minkowskiProduct_toCoord]
    fun_prop
  have hT : Continuous (fun v : Vector 3 => timeComponent v) :=
    coord_continuous (Sum.inl 0)
  exact (isOpen_lt continuous_const hQ).inter (isOpen_lt continuous_const hT)

private lemma futureTimelikeCone3_subset_futureCausalCone3 :
    futureTimelikeCone3 ⊆ futureCausalCone3 := by
  rintro v ⟨hq, ht⟩
  exact ⟨hq.le, ht.le⟩

private lemma futureTimelikeCone3_subset_interior :
    futureTimelikeCone3 ⊆ interior futureCausalCone3 := by
  exact isOpen_futureTimelikeCone3.subset_interior_iff.mpr
    futureTimelikeCone3_subset_futureCausalCone3

private lemma temporalBasis3_norm : ‖temporalBasis3‖ = 1 := by
  rw [norm_eq_equivEuclid]
  simp [temporalBasis3, basis_apply, PiLp.norm_eq_of_L2]

private lemma mink_sub_temporalBasis3 (v : Vector 3) (a : ℝ) :
    ⟪v - a • temporalBasis3, v - a • temporalBasis3⟫ₘ =
      ⟪v, v⟫ₘ - 2 * a * timeComponent v + a ^ 2 := by
  rw [minkowskiProduct_toCoord]
  simp [temporalBasis3, basis_apply, timeComponent]
  rw [minkowskiProduct_toCoord]
  ring

private lemma interior_futureCausalCone3_subset_futureTimelikeCone3 :
    interior futureCausalCone3 ⊆ futureTimelikeCone3 := by
  intro v hv
  have hvCmem : v ∈ futureCausalCone3 := interior_subset hv
  have hvC : IsFutureCausal v := by simpa [futureCausalCone3] using hvCmem
  have hnhds : futureCausalCone3 ∈ nhds v := mem_interior_iff_mem_nhds.mp hv
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have htpos : 0 < timeComponent v := by
    apply lt_of_le_of_ne hvC.2
    intro ht
    have ht0 : timeComponent v = 0 := ht.symm
    have hsp : ‖spatialPart v‖ = 0 := by
      have hnonneg := hvC.1
      rw [minkowskiProduct_self_eq_timeComponent_spatialPart, ht0] at hnonneg
      norm_num at hnonneg
      exact norm_eq_zero.mpr (by simpa [spatialPart] using hnonneg)
    have hvzero : v = 0 := by
      apply eq_of_apply_eq
      intro i
      rcases i with i | i
      · fin_cases i
        exact ht0
      · have hz : spatialPart v = 0 := norm_eq_zero.mp hsp
        simpa [spatialPart] using congrArg (fun w => w i) hz
    subst v
    let a := ε / 2
    have ha : 0 < a := half_pos hε
    have hwball : -a • temporalBasis3 ∈ Metric.ball (0 : Vector 3) ε := by
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖-a • temporalBasis3‖ = |a| := by
          rw [norm_smul, temporalBasis3_norm, mul_one, Real.norm_eq_abs, abs_neg]
        _ = a := abs_of_pos ha
        _ < ε := by dsimp [a]; linarith
    have hwC := hball hwball
    have hwtime : timeComponent (-a • temporalBasis3) = -a := by
      simp [temporalBasis3, timeComponent, basis_apply]
    linarith [hwC.2]
  refine ⟨?_, htpos⟩
  apply lt_of_le_of_ne hvC.1
  intro hq
  have hq0 : ⟪v, v⟫ₘ = 0 := hq.symm
  let a := min (ε / 2) (timeComponent v)
  have ha_pos : 0 < a := lt_min (half_pos hε) htpos
  have ha_lt_eps : a < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ha_le_time : a ≤ timeComponent v := min_le_right _ _
  have hwball : v - a • temporalBasis3 ∈ Metric.ball v ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left]
    rw [norm_neg, norm_smul, temporalBasis3_norm, mul_one, Real.norm_eq_abs,
      abs_of_pos ha_pos]
    exact ha_lt_eps
  have hwC := hball hwball
  have hqa : ⟪v - a • temporalBasis3, v - a • temporalBasis3⟫ₘ < 0 := by
    rw [mink_sub_temporalBasis3, hq0, zero_sub]
    nlinarith
  exact (not_lt_of_ge hwC.1) hqa

/-- **The interior of the closed future causal cone is exactly the future timelike cone**
in 3+1 Minkowski space.  This is the topological boundary step used to recover null rays
from causal-order preservation for affine maps. -/
@[zil_level physical_theorem]
theorem interior_futureCausalCone3_eq_futureTimelikeCone3 :
    interior futureCausalCone3 = futureTimelikeCone3 :=
  Set.Subset.antisymm interior_futureCausalCone3_subset_futureTimelikeCone3
    futureTimelikeCone3_subset_interior

/-- **Affine causal automorphisms preserve the null cone automatically.**
The linear part maps the closed future causal cone bijectively to itself.  Being a
continuous linear equivalence, it also maps its topological interior—the timelike cone—to
itself; hence it maps the boundary null cone to itself.  This removes the former explicit
null-preservation premise after the fundamental theorem of affine geometry has supplied
the affine map. -/
@[zil_level physical_theorem]
theorem affine_causalAutomorphism_preserves_nullCone
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) :
    ∀ v, ⟪v, v⟫ₘ = 0 ↔ ⟪e.linear v, e.linear v⟫ₘ = 0 := by
  let L : Vector 3 ≃L[ℝ] Vector 3 := e.linear.toContinuousLinearEquiv
  let f : Vector 3 →L[ℝ] Vector 3 := L.toContinuousLinearMap
  have hf_apply (v : Vector 3) : f v = e v - e 0 := by
    change e.linear v = e v - e 0
    simpa using e.toAffineMap.linearMap_vsub v 0
  have hfuture (v : Vector 3) : IsFutureCausal (f v) ↔ IsFutureCausal v := by
    calc
      IsFutureCausal (f v) ↔ causallyFollows (e 0) (e v) := by
        rw [hf_apply, causallyFollows_iff_isFutureCausal]
      _ ↔ causallyFollows 0 v := hcausal.2 0 v
      _ ↔ IsFutureCausal v := by
        simpa only [sub_zero] using causallyFollows_iff_isFutureCausal 0 v
  have himage : L '' futureCausalCone3 = futureCausalCone3 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change IsFutureCausal x at hx
      change IsFutureCausal (L x)
      change IsFutureCausal (f x)
      exact (hfuture x).mpr hx
    · intro hy
      change IsFutureCausal y at hy
      refine ⟨L.symm y, (hfuture (L.symm y)).mp ?_, by simp⟩
      simpa [f] using hy
  have hinterior : L '' futureTimelikeCone3 = futureTimelikeCone3 := by
    calc
      L '' futureTimelikeCone3 = L '' interior futureCausalCone3 := by
        rw [interior_futureCausalCone3_eq_futureTimelikeCone3]
      _ = interior (L '' futureCausalCone3) := by
        simpa using L.toHomeomorph.image_interior futureCausalCone3
      _ = interior futureCausalCone3 := by rw [himage]
      _ = futureTimelikeCone3 := interior_futureCausalCone3_eq_futureTimelikeCone3
  have hinterior_iff (v : Vector 3) :
      f v ∈ futureTimelikeCone3 ↔ v ∈ futureTimelikeCone3 := by
    constructor
    · intro hfi
      have hfi' : f v ∈ L '' futureTimelikeCone3 := by
        rw [hinterior]
        exact hfi
      rcases hfi' with ⟨w, hw, hwv⟩
      have hw_eq : w = v := L.injective (by simpa [f] using hwv)
      simpa [hw_eq] using hw
    · intro hv
      have hvImage : L v ∈ L '' futureTimelikeCone3 := ⟨v, hv, rfl⟩
      have hLv : L v ∈ futureTimelikeCone3 := by
        rw [← hinterior]
        exact hvImage
      simpa [f] using hLv
  have hboundary (v : Vector 3) (hvC : IsFutureCausal v) :
      ⟪v, v⟫ₘ = 0 ↔ v ∉ futureTimelikeCone3 := by
    constructor
    · intro hq hv
      exact (ne_of_gt hv.1) hq
    · intro hnot
      have hnotpos : ¬ 0 < ⟪v, v⟫ₘ := by
        intro hpos
        apply hnot
        refine ⟨hpos, ?_⟩
        have hc : causalCharacter v = .timeLike :=
          (timeLike_iff_norm_sq_pos v).mpr hpos
        have htne : timeComponent v ≠ 0 := time_component_ne_zero_of_timelike hc
        exact lt_of_le_of_ne hvC.2 (fun hzero => htne hzero.symm)
      exact le_antisymm (not_lt.mp hnotpos) hvC.1
  have hfutureNullIff (v : Vector 3) :
      (⟪v, v⟫ₘ = 0 ∧ 0 ≤ timeComponent v) ↔
        (⟪f v, f v⟫ₘ = 0 ∧ 0 ≤ timeComponent (f v)) := by
    have hvC_iff : IsFutureCausal (f v) ↔ IsFutureCausal v := hfuture v
    constructor
    · rintro ⟨hq, ht⟩
      have hvC : IsFutureCausal v := ⟨hq.ge, ht⟩
      have hfC : IsFutureCausal (f v) := hvC_iff.mpr hvC
      exact ⟨(hboundary (f v) hfC).mpr (fun hfi =>
        ((hboundary v hvC).mp hq) ((hinterior_iff v).mp hfi)), hfC.2⟩
    · rintro ⟨hq, ht⟩
      have hfC : IsFutureCausal (f v) := ⟨hq.ge, ht⟩
      have hvC : IsFutureCausal v := hvC_iff.mp hfC
      exact ⟨(hboundary v hvC).mpr (fun hvi =>
        ((hboundary (f v) hfC).mp hq) ((hinterior_iff v).mpr hvi)), hvC.2⟩
  intro v
  change ⟪v, v⟫ₘ = 0 ↔ ⟪f v, f v⟫ₘ = 0
  constructor
  · intro hv
    by_cases ht : 0 ≤ timeComponent v
    · exact (hfutureNullIff v).mp ⟨hv, ht⟩ |>.1
    · have hn := (hfutureNullIff (-v)).mp ⟨by simpa using hv, by
        change 0 ≤ -timeComponent v
        exact neg_nonneg.mpr (le_of_not_ge ht)⟩
      simpa using hn.1
  · intro hv
    by_cases ht : 0 ≤ timeComponent (f v)
    · exact (hfutureNullIff v).mpr ⟨hv, ht⟩ |>.1
    · have hn := (hfutureNullIff (-v)).mpr ⟨by simpa using hv, by
        rw [map_neg]
        change 0 ≤ -timeComponent (f v)
        exact neg_nonneg.mpr (le_of_not_ge ht)⟩
      simpa using hn.1

/-- **The affine Alexandrov–Zeeman classification in 3+1 dimensions.**
Every affine causal automorphism is a translation followed by a positive dilation and a
Lorentz transformation.  Unlike the earlier algebraic theorem, this result assumes
neither conformality nor null preservation: both are derived from the causal order.  In
the general nonlinear theorem, the fundamental theorem of affine geometry is precisely
the preceding step that supplies the `AffineEquiv` used here. -/
@[zil_level physical_theorem]
theorem affine_causalAutomorphism_eq_translation_dilation_lorentz
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : Vector 3 →ₗ[ℝ] Vector 3,
      IsLorentz g ∧ ∀ x, e x = Real.sqrt c • g x + e 0 := by
  apply affine_causal_null_preserver_eq_translation_dilation_lorentz e hcausal
  intro p q
  let v := q - p
  have hlin : e q - e p = e.linear v := by
    change e q - e p = e.linear (q - p)
    symm
    simpa using e.toAffineMap.linearMap_vsub q p
  rw [hlin]
  exact affine_causalAutomorphism_preserves_nullCone e hcausal v

/-- **The unrestricted Alexandrov–Zeeman theorem in physical 3+1 dimensions.** Every
causal-order automorphism, with no continuity, measurability, differentiability, affine,
conformal, or null-preservation premise, is a translation followed by a positive dilation
and a Lorentz transformation. -/
@[zil_level physical_theorem]
theorem causalAutomorphism_eq_translation_dilation_lorentz
    {φ : Vector 3 → Vector 3} (hcausal : IsCausalAutomorphism φ) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : Vector 3 →ₗ[ℝ] Vector 3,
      IsLorentz g ∧ ∀ x, φ x = Real.sqrt c • g x + φ 0 := by
  obtain ⟨e, he⟩ := exists_affineEquiv_of_causalAutomorphism hcausal
  have heCausal : IsCausalAutomorphism e := by
    have hefun : (e : Vector 3 → Vector 3) = φ := funext he
    rw [hefun]
    exact hcausal
  obtain ⟨c, hc, g, hg, hform⟩ :=
    affine_causalAutomorphism_eq_translation_dilation_lorentz e heCausal
  exact ⟨c, hc, g, hg, fun x => by simpa only [he] using hform x⟩

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach conformalLorentz_eq_smul_lorentz where
  supported_by @ "lean:Lorentz.Vector.conformalLorentz_normalized_isLorentz",
  supported_by @ "lean:HermitianMat.sqrt_pos",
  formalizes @ "claim:a-linear-map-preserving-the-minkowski-form-up-to-a-positive-\
conformal-factor-is-a-positive-dilation-of-a-lorentz-transformation-the-algebraic-\
alexandrov-zeeman-conclusion",
  supported_by @ "lean:Lorentz.Vector.IsLorentz",
  caveat @ "claim:for-a-general-nonlinear-causal-automorphism-the-collineation-step-of-\
the-fundamental-theorem-of-affine-geometry-must-still-supply-the-affine-equivalence"

zil attach same_null_cone_proportional where
  formalizes @ "claim:in-three-plus-one-minkowski-space-any-symmetric-continuous-\
bilinear-form-with-exactly-the-same-null-cone-is-a-scalar-multiple-of-the-minkowski-form",
  supported_by @ "lean:Lorentz.Vector.minkowskiProduct",
  caveat @ "claim:this-is-the-physical-three-spatial-dimensional-theorem-not-a-\
dimension-polymorphic-null-cone-rigidity-result"

zil attach nullCone_preserving_linear_is_conformal where
  supported_by @ "lean:same_null_cone_proportional",
  supported_by @ "lean:Vector.minkowskiProduct_symm",
  formalizes @ "claim:a-continuous-linear-map-preserving-null-vectors-in-both-directions-\
pulls-the-minkowski-form-back-to-a-scalar-multiple-of-it",
  supported_by @ "lean:Lorentz.Vector.same_null_cone_proportional"

zil attach interior_futureCausalCone3_eq_futureTimelikeCone3 where
  formalizes @ "claim:the-topological-interior-of-the-closed-future-causal-cone-in-\
three-plus-one-minkowski-space-is-exactly-the-future-timelike-cone"

zil attach affine_causalAutomorphism_preserves_nullCone where
  supported_by @ "lean:interior_futureCausalCone3_eq_futureTimelikeCone3",
  formalizes @ "claim:the-linear-part-of-an-affine-causal-automorphism-preserves-the-\
null-cone-without-a-separate-null-preservation-assumption",
  supported_by @ "lean:Lorentz.Vector.interior_futureCausalCone3_eq_futureTimelikeCone3",
  caveat @ "claim:affineness-is-the-output-expected-from-the-fundamental-theorem-of-\
affine-geometry-and-is-not-derived-here-for-an-arbitrary-nonlinear-causal-bijection"

zil attach affine_causalAutomorphism_eq_translation_dilation_lorentz where
  supported_by @ "lean:affine_causalAutomorphism_preserves_nullCone",
  formalizes @ "claim:every-affine-causal-automorphism-of-three-plus-one-minkowski-space-\
is-a-translation-followed-by-a-positive-dilation-and-a-lorentz-transformation",
  supported_by @ "lean:Lorentz.Vector.affine_causalAutomorphism_preserves_nullCone",
  supported_by @ "lean:Lorentz.Vector.same_null_cone_proportional",
  caveat @ "claim:this-closes-the-post-collineation-affine-stage-of-alexandrov-zeeman-\
the-unrestricted-theorem-additionally-uses-the-proved-incidence-to-affine-reconstruction"

zil attach causalAutomorphism_eq_translation_dilation_lorentz where
  supported_by @ "lean:affine_causalAutomorphism_eq_translation_dilation_lorentz",
  supported_by @ "lean:exists_affineEquiv_of_causalAutomorphism",
  formalizes @ "claim:every-causal-order-automorphism-of-three-plus-one-minkowski-space-\
without-regularity-or-affine-premises-is-a-translation-positive-dilation-and-lorentz-\
transformation",
  supported_by @ "lean:Lorentz.Vector.exists_affineEquiv_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz",
  caveat @ "claim:this-is-the-physical-three-plus-one-dimensional-alexandrov-zeeman-\
classification-not-a-dimension-polymorphic-statement"

zil attach conformalLorentz_toMatrix_mem_lorentzGroup where
  supported_by @ "lean:Lorentz.Vector.conformalLorentz_normalized_isLorentz",
  supported_by @ "lean:Vector.isLorentz_iff_toMatrix_mem_lorentzGroup",
  formalizes @ "claim:the-dilation-normalised-conformal-linear-map-has-its-standard-basis-\
matrix-in-the-lorentz-group",
  supported_by @ "lean:Lorentz.Vector.isLorentz_iff_toMatrix_mem_lorentzGroup"

zil attach causalDiamond_image_of_isCausalAutomorphism where
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:a-causal-automorphism-preserves-alexandrov-intervals-mapping-the-\
causal-diamond-of-p-and-q-onto-the-causal-diamond-of-their-images"

zil attach translation_isCausalAutomorphism where
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:spatial-translations-are-causal-automorphisms-since-the-causal-\
relations-depend-only-on-the-difference-of-events"

zil_file_contract physlib.causalConeAlexandrovZeeman where
  promises "The unrestricted Alexandrov-Zeeman theorem is proved in physical 3+1 Minkowski \
space. Every bare causal-order automorphism preserves complete null lines and null tangent \
hyperplanes from incidence, then spacelike lines, hyperbolic planes, timelike lines, and all \
nondegenerate affine lines. Real affine reconstruction supplies an AffineEquiv without a \
continuity, measurability, differentiability, or affine premise. Null-cone rigidity and the \
causal orientation then classify it as a translation followed by a positive dilation and a \
Lorentz transformation. The dimension-specific scope is stated explicitly."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Lorentz.Vector.IsLorentz",
    "lean:Lorentz.Vector.causalDiamond",
    "lean:Lorentz.Vector.causallyFollows",
    "lean:Lorentz.Vector.IsFutureCausal",
    "lean:Lorentz.Vector.minkowskiProduct"
  ]
  forbids_substitutes [
    "omitting the incidence-to-affine reconstruction when applying the unrestricted result",
    "claiming a dimension-polymorphic same-null-cone rigidity theorem when the proved \
reconstruction is specifically 3+1 dimensional"
  ]
  witnessed_by [
    conformalLorentz_normalized_isLorentz,
    conformalLorentz_eq_smul_lorentz,
    conformalLorentz_toMatrix_mem_lorentzGroup,
    smul_lorentz_isConformalLorentz,
    translation_isCausalAutomorphism,
    causalDiamond_image_of_isCausalAutomorphism,
    nullSeparation_iff_of_causalAutomorphism,
    nullConeAt_image_of_causalAutomorphism,
    same_null_cone_proportional,
    nullCone_preserving_linear_is_conformal,
    nullCone_preserving_linear_is_positive_conformal,
    nullCone_preserving_linear_eq_dilation_lorentz,
    interior_futureCausalCone3_eq_futureTimelikeCone3,
    affine_causalAutomorphism_preserves_nullCone,
    affine_causalAutomorphism_eq_translation_dilation_lorentz,
    affineLine_image_of_causalAutomorphism,
    exists_affineEquiv_of_causalAutomorphism,
    causalAutomorphism_eq_translation_dilation_lorentz
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.causalConeAlexandrovZeeman
