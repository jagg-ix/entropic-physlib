/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Tactic
public import Mathlib.Topology.ContinuousMap.Compact

meta import Zil

/- Consolidated from Physlib.Mathematics.DynamicalSystems.MatherSpectrum -/

/-!
# The Mather vector-field operator of a diffeomorphism

For a diffeomorphism `Φ`, Mather's operator on vector fields is
`(Φ_* V)(y) = DΦ_(Φ⁻¹y) (V(Φ⁻¹y))`.

This module identifies `Φ_*` with Mathlib's native pullback of vector fields by `Φ⁻¹` and proves:

1. the displayed pointwise derivative formula;
2. preservation of genuine continuous tangent sections;
3. linear invertibility, with inverse `(Φ⁻¹)_*`.

These are the algebraic and regularity prerequisites for the Mather spectrum in Gogolev's
periodic-spectrum comparison.

## Layer boundary

This module constructs the exact continuous-section automorphism to which Mather's spectrum
belongs.  The successor module `MatherSpectrum` supplies the compact supremum-norm Banach carrier
and genuine complex spectrum under explicit global-frame and complexification data.  Keeping the
algebraic operator here separate prevents an unnormed algebraic spectrum from being relabelled as
Mather's.
-/

set_option autoImplicit false

noncomputable section

open scoped Bundle Manifold ContDiff
open Bundle Manifold

@[expose] public section

namespace Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator

universe u v

variable {E : Type u} {H M : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)

/-! ## A. The pointwise Mather pushforward -/

/-- Mather's pushforward of a tangent vector field, implemented as the native manifold pullback
by the inverse diffeomorphism. -/
def matherPushforward (Φ : Diffeomorph I I M M 1)
    (V : (x : M) → TangentSpace I x) (y : M) : TangentSpace I y :=
  VectorField.mpullback I I Φ.symm V y

/-- The inverse of `DΦ⁻¹_y` is `DΦ_(Φ⁻¹y)`. -/
lemma mfderiv_symm_inverse_eq (Φ : Diffeomorph I I M M 1) (y : M) :
    (mfderiv I I Φ.symm y).inverse = mfderiv I I Φ (Φ.symm y) := by
  apply ContinuousLinearMap.inverse_eq
  · have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := Φ.symm y)
      (Φ.symm.mdifferentiable one_ne_zero (Φ (Φ.symm y)))
      (Φ.mdifferentiable one_ne_zero (Φ.symm y))
    rw [show (Φ.symm : M → M) ∘ Φ = id by funext x; simp, mfderiv_id] at h
    rw [Φ.apply_symm_apply] at h
    exact h.symm
  · have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := y)
      (Φ.mdifferentiable one_ne_zero (Φ.symm y))
      (Φ.symm.mdifferentiable one_ne_zero y)
    rw [show (Φ : M → M) ∘ Φ.symm = id by funext x; simp, mfderiv_id] at h
    exact h.symm

/-- Mather's intrinsic formula:
`(Φ_*V)(y) = DΦ_(Φ⁻¹y)(V(Φ⁻¹y))`. -/
lemma matherPushforward_apply (Φ : Diffeomorph I I M M 1)
    (V : (x : M) → TangentSpace I x) (y : M) :
    matherPushforward I Φ V y =
      mfderiv I I Φ (Φ.symm y) (V (Φ.symm y)) := by
  rw [matherPushforward, VectorField.mpullback_apply,
    mfderiv_symm_inverse_eq]
  rfl

/-- The derivative of the inverse cancels the derivative of a diffeomorphism. -/
lemma mfderiv_symm_apply_mfderiv (Φ : Diffeomorph I I M M 1) (x : M)
    (v : TangentSpace I x) :
    mfderiv I I Φ.symm (Φ x) (mfderiv I I Φ x v) = v := by
  have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := x)
    (Φ.symm.mdifferentiable one_ne_zero (Φ x))
    (Φ.mdifferentiable one_ne_zero x)
  rw [show (Φ.symm : M → M) ∘ Φ = id by funext y; simp, mfderiv_id] at h
  have hv := congrArg (fun L => L v) h.symm
  exact hv

/-- The derivative of a diffeomorphism cancels the derivative of its inverse. -/
lemma mfderiv_apply_mfderiv_symm (Φ : Diffeomorph I I M M 1) (y : M)
    (v : TangentSpace I y) :
    mfderiv I I Φ (Φ.symm y) (mfderiv I I Φ.symm y v) = v := by
  have h := mfderiv_comp (I := I) (I' := I) (I'' := I) (x := y)
    (Φ.mdifferentiable one_ne_zero (Φ.symm y))
    (Φ.symm.mdifferentiable one_ne_zero y)
  rw [show (Φ : M → M) ∘ Φ.symm = id by funext x; simp, mfderiv_id] at h
  have hv := congrArg (fun L => L v) h.symm
  exact hv

/-- Mather pushforward is additive. -/
lemma matherPushforward_add (Φ : Diffeomorph I I M M 1)
    (V W : (x : M) → TangentSpace I x) :
    matherPushforward I Φ (V + W) =
      matherPushforward I Φ V + matherPushforward I Φ W := by
  exact VectorField.mpullback_add

/-- Mather pushforward preserves the zero vector field. -/
lemma matherPushforward_zero (Φ : Diffeomorph I I M M 1) :
    matherPushforward I Φ (0 : (x : M) → TangentSpace I x) = 0 := by
  exact VectorField.mpullback_zero

/-- Mather pushforward is homogeneous over real scalars. -/
lemma matherPushforward_smul (Φ : Diffeomorph I I M M 1) (c : ℝ)
    (V : (x : M) → TangentSpace I x) :
    matherPushforward I Φ (c • V) = c • matherPushforward I Φ V := by
  ext y
  simp [matherPushforward, VectorField.mpullback_apply]

/-- Pushforward by the inverse cancels pushforward by the original diffeomorphism. -/
lemma matherPushforward_symm_apply (Φ : Diffeomorph I I M M 1)
    (V : (x : M) → TangentSpace I x) :
    matherPushforward I Φ.symm (matherPushforward I Φ V) = V := by
  funext y
  rw [matherPushforward_apply, matherPushforward_apply]
  rw [show Φ.symm.symm = Φ by ext; rfl]
  rw [Φ.symm_apply_apply]
  exact mfderiv_symm_apply_mfderiv I Φ y (V y)

/-- Every manifold derivative of a diffeomorphism is invertible. -/
lemma mfderiv_isInvertible (Φ : Diffeomorph I I M M 1) (x : M) :
    (mfderiv I I Φ x).IsInvertible := by
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
    (x := x) Φ one_ne_zero]
  simp

/-! ## B. The operator on continuous tangent sections -/

variable [CompleteSpace E] [IsManifold I 1 M]

/-- Continuous tangent sections, represented by Mathlib's bundled `C⁰` sections of the genuine
tangent bundle. -/
abbrev ContinuousTangentSection :=
  ContMDiffSection I E 0 (fun x : M => TangentSpace I x)

/-- The Mather pushforward of a continuous tangent section is again a continuous tangent section.
This uses the native pullback regularity theorem at `C⁰ ← C¹`. -/
def matherPushforwardSection (Φ : Diffeomorph I I M M 1)
    (V : ContinuousTangentSection (M := M) I) :
    ContinuousTangentSection (M := M) I where
  toFun := matherPushforward I Φ V
  contMDiff_toFun := by
    exact V.contMDiff.mpullback_vectorField Φ.symm.contMDiff
      (fun x => mfderiv_isInvertible I Φ.symm x) (by norm_num)

/-- Evaluation of the bundled section agrees with the pointwise Mather pushforward. -/
@[simp] lemma matherPushforwardSection_apply (Φ : Diffeomorph I I M M 1)
    (V : ContinuousTangentSection (M := M) I) (y : M) :
    matherPushforwardSection I Φ V y = matherPushforward I Φ V y := rfl

/-- Mather pushforward bundled as a real-linear operator on continuous tangent sections. -/
def matherOperator (Φ : Diffeomorph I I M M 1) :
    ContinuousTangentSection (M := M) I →ₗ[ℝ]
      ContinuousTangentSection (M := M) I where
  toFun := matherPushforwardSection I Φ
  map_add' V W := by
    ext y
    exact congrFun (matherPushforward_add I Φ V W) y
  map_smul' c V := by
    ext y
    exact congrFun (matherPushforward_smul I Φ c V) y

/-- Evaluation of the bundled linear operator agrees with the pointwise pushforward. -/
@[simp] lemma matherOperator_apply (Φ : Diffeomorph I I M M 1)
    (V : ContinuousTangentSection (M := M) I) (y : M) :
    matherOperator I Φ V y = matherPushforward I Φ V y := rfl

/-! ## C. Automorphism structure -/

/-- The Mather operator is a linear equivalence whose inverse is induced by `Φ⁻¹`. -/
def matherOperatorEquiv (Φ : Diffeomorph I I M M 1) :
    ContinuousTangentSection (M := M) I ≃ₗ[ℝ]
      ContinuousTangentSection (M := M) I where
  toLinearMap := matherOperator I Φ
  invFun := matherOperator I Φ.symm
  left_inv V := by
    ext y
    exact congrFun (matherPushforward_symm_apply I Φ V) y
  right_inv V := by
    ext y
    exact congrFun (matherPushforward_symm_apply I Φ.symm V) y

end Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherPushforward_apply where
  formalizes @ "claim:mather-pushforward-is-Df-at-f-inverse-applied-to-the-vector-field-at-f-inverse",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms",
  supported_by @ "lean:VectorField.mpullback",
  caveat @ "claim:this-constructs-the-operator-underlying-the-mather-spectrum-not-the-spectrum-itself"

zil attach Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherOperator where
  formalizes @ "claim:a-C1-diffeomorphism-induces-a-real-linear-operator-on-continuous-tangent-sections",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ContMDiff.mpullback_vectorField",
  caveat @ "claim:boundedness-in-the-compact-supremum-norm-is-established-in-the-successor-mather-spectrum-module-under-explicit-global-frame-data"

zil attach Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherOperatorEquiv where
  formalizes @ "claim:the-mather-vector-field-operator-is-invertible-with-inverse-induced-by-the-inverse-diffeomorphism",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:mfderiv_comp",
  caveat @ "claim:the-genuine-complex-banach-spectrum-is-constructed-in-the-successor-mather-spectrum-module-from-an-explicit-complexification-witness"

zil_file_contract physlib.matherVectorFieldOperator where
  promises "The exact Mather vector-field automorphism underlying the periodic-spectrum versus Mather-spectrum comparison: its pointwise derivative formula, preservation of continuous tangent sections, real linearity, and inverse induced by the inverse diffeomorphism."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:VectorField.mpullback", "lean:ContMDiffSection",
    "lean:Diffeomorph.mfderivToContinuousLinearEquiv"]
  forbids_substitutes ["calling an unnormed algebraic spectrum the Mather spectrum",
    "assuming continuity of pushed-forward sections without the native pullback regularity theorem",
    "replacing the tangent bundle by a constant finite-dimensional carrier"]
  witnessed_by [
    Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherPushforward_apply,
    Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherOperator,
    Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherOperatorEquiv]

/- ZIL-END -/

/- Consolidated from Physlib.Mathematics.DynamicalSystems.MatherSpectrum -/

/-!
# The compact Banach carrier and genuine Mather spectrum

For a compact base `M`, a continuous operator cocycle `A : M → (X →L[𝕜] X)`, and a
homeomorphism `g`, this module constructs the bounded weighted-composition operator

`(T[A,g]f)(y) = A(y) (f(g⁻¹y))`

on the complete supremum-norm space `M →ᵇ X`.  It then connects this construction to the
intrinsic Mather vector-field operator from `MatherVectorFieldOperator`:

1. a global linear tangent trivialization identifies genuine continuous tangent sections with
   the compact sup-norm carrier;
2. the coordinate derivative cocycle conjugates the intrinsic Mather operator to `T[A,g]`;
3. an explicit complexification witness produces the genuine complex Banach-algebra spectrum;
4. that spectrum is nonempty, compact, norm-bounded, and excludes zero when a continuous inverse
   cocycle is supplied.

## Honest scope

The global tangent trivialization and continuity of its coordinate derivative cocycle are explicit
data.  They hold for the globally framed situations used in the toral Anosov application, but are
not silently asserted for every tangent bundle.  Likewise, `ComplexCocycleExtension` records the
actual complexification/intertwining map; no unrelated complex operator is relabelled as the
complexified Mather operator.  The deeper Mather criterion `1 ∉ σ(T) ↔ Anosov` is not proved here.
-/

set_option autoImplicit false

noncomputable section

open scoped Bundle Manifold ContDiff Topology BoundedContinuousFunction
open Bundle Manifold

@[expose] public section

namespace Physlib.Mathematics.DynamicalSystems.MatherSpectrum

universe u v w

/-! ## A. Bounded weighted composition on the compact supremum-norm carrier -/

variable {𝕜 : Type u} {M : Type v} {X : Type w}
variable [NontriviallyNormedField 𝕜]
variable [TopologicalSpace M] [CompactSpace M]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The pointwise weighted-composition map
`f ↦ (y ↦ A y (f (g⁻¹ y)))` on bounded continuous functions. -/
def weightedCompositionMap (g : M ≃ₜ M) (A : C(M, X →L[𝕜] X))
    (f : M →ᵇ X) : M →ᵇ X :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun y => A y (f (g.symm y))
      continuous_toFun :=
        A.continuous.clm_apply (f.continuous.comp g.symm.continuous) }

/-- Evaluation of the weighted-composition map. -/
@[simp] lemma weightedCompositionMap_apply (g : M ≃ₜ M)
    (A : C(M, X →L[𝕜] X)) (f : M →ᵇ X) (y : M) :
    weightedCompositionMap g A f y = A y (f (g.symm y)) := rfl

/-- The weighted-composition map bundled as a linear endomorphism. -/
def weightedCompositionLinearMap (g : M ≃ₜ M) (A : C(M, X →L[𝕜] X)) :
    (M →ᵇ X) →ₗ[𝕜] (M →ᵇ X) where
  toFun := weightedCompositionMap g A
  map_add' f h := by
    ext y
    simp [weightedCompositionMap]
  map_smul' c f := by
    ext y
    simp [weightedCompositionMap]

/-- The pointwise cocycle sup norm bounds weighted composition. -/
lemma weightedCompositionLinearMap_bound (g : M ≃ₜ M)
    (A : C(M, X →L[𝕜] X)) (f : M →ᵇ X) :
    ‖weightedCompositionLinearMap g A f‖ ≤ ‖A‖ * ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg A) (norm_nonneg f))]
  intro y
  calc
    ‖A y (f (g.symm y))‖ ≤ ‖A y‖ * ‖f (g.symm y)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖f‖ := mul_le_mul
      (ContinuousMap.norm_coe_le_norm A y)
      (BoundedContinuousFunction.norm_coe_le_norm f (g.symm y))
      (norm_nonneg _) (norm_nonneg _)

/-- The bounded Mather-type weighted-composition operator on the compact sup-norm carrier. -/
def weightedComposition (g : M ≃ₜ M) (A : C(M, X →L[𝕜] X)) :
    (M →ᵇ X) →L[𝕜] (M →ᵇ X) :=
  (weightedCompositionLinearMap g A).mkContinuous (‖A‖) <|
    weightedCompositionLinearMap_bound g A

/-- Evaluation of the bounded weighted-composition operator. -/
@[simp] lemma weightedComposition_apply (g : M ≃ₜ M)
    (A : C(M, X →L[𝕜] X)) (f : M →ᵇ X) (y : M) :
    weightedComposition g A f y = A y (f (g.symm y)) := rfl

/-- Its operator norm is at most the compact supremum norm of the cocycle. -/
lemma weightedComposition_norm_le (g : M ≃ₜ M) (A : C(M, X →L[𝕜] X)) :
    ‖weightedComposition g A‖ ≤ ‖A‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-! ## B. A global tangent frame gives the exact compact section carrier -/

variable {E : Type u} {H : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [TopologicalSpace H] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 1 M]

open Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator

/-- Coordinates of a continuous tangent section in a global linear tangent trivialization.
Compactness turns the resulting continuous map into a bounded continuous function with its native
supremum norm. -/
def tangentSectionCoordinates
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (V : ContinuousTangentSection (M := M) I) : M →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun x => e.continuousLinearMapAt ℝ x (V x)
      continuous_toFun := by
        have hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)) :=
          V.contMDiff.continuous
        have he' : Continuous (fun x => e (⟨x, V x⟩ : TangentBundle I M)) := by
          exact e.continuousOn.comp_continuous hV (fun x => by
            rw [e.mem_source, he]
            exact Set.mem_univ x)
        apply Continuous.congr he'.snd
        intro x
        exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
          (R := ℝ) e (by simpa [he]) (V x)).symm }

/-- Evaluation of global-frame coordinates. -/
@[simp] lemma tangentSectionCoordinates_apply
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (V : ContinuousTangentSection (M := M) I) (x : M) :
    tangentSectionCoordinates I e he V x =
      e.continuousLinearMapAt ℝ x (V x) := rfl

/-- Reconstruct a genuine continuous tangent section from its global-frame coordinates. -/
def tangentSectionOfCoordinates
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (f : M →ᵇ E) : ContinuousTangentSection (M := M) I where
  toFun := fun x => e.symmL ℝ x (f x)
  contMDiff_toFun := by
    rw [contMDiff_zero_iff]
    have hpair : Continuous (fun x : M => (x, f x)) :=
      continuous_id.prodMk f.continuous
    have hcont := e.continuousOn_symm.comp_continuous hpair (fun x => by
        rw [he]
        exact ⟨Set.mem_univ x, Set.mem_univ (f x)⟩)
    refine hcont.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [e.symmL_apply (by simp [he])]

/-- Evaluation of the reconstructed section. -/
@[simp] lemma tangentSectionOfCoordinates_apply
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (f : M →ᵇ E) (x : M) :
    tangentSectionOfCoordinates I e he f x = e.symmL ℝ x (f x) := rfl

/-- A global linear tangent frame identifies continuous tangent sections with the complete compact
sup-norm carrier `M →ᵇ E`. -/
def tangentSectionCoordinatesLinearEquiv
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ) :
    ContinuousTangentSection (M := M) I ≃ₗ[ℝ] (M →ᵇ E) where
  toFun := tangentSectionCoordinates I e he
  invFun := tangentSectionOfCoordinates I e he
  map_add' V W := by
    ext x
    simp [tangentSectionCoordinates]
  map_smul' c V := by
    ext x
    simp [tangentSectionCoordinates]
  left_inv V := by
    ext x
    simp [tangentSectionCoordinates, tangentSectionOfCoordinates, he]
  right_inv f := by
    ext x
    simp [tangentSectionCoordinates, tangentSectionOfCoordinates, he]

/-- The compact global-frame supremum norm of a continuous tangent section. -/
def tangentSectionSupNorm
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (V : ContinuousTangentSection (M := M) I) : ℝ :=
  ‖tangentSectionCoordinates I e he V‖

/-- The global-frame supremum norm vanishes exactly on the zero section. -/
lemma tangentSectionSupNorm_eq_zero_iff
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (V : ContinuousTangentSection (M := M) I) :
    tangentSectionSupNorm I e he V = 0 ↔ V = 0 := by
  rw [tangentSectionSupNorm, norm_eq_zero]
  have hzero :
      tangentSectionCoordinates I e he
        (0 : ContinuousTangentSection (M := M) I) = 0 := by
    ext x
    simp [tangentSectionCoordinates]
  constructor
  · intro h
    apply (tangentSectionCoordinatesLinearEquiv I e he).injective
    change tangentSectionCoordinates I e he V =
      tangentSectionCoordinates I e he 0
    rw [hzero]
    exact h
  · rintro rfl
    exact hzero

/-! ## C. The intrinsic Mather operator in global-frame coordinates -/

/-- The coordinate derivative cocycle
`e_y ∘ DΦ_(Φ⁻¹y) ∘ e⁻¹_(Φ⁻¹y)`. -/
def realMatherCocycleAt
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (Φ : Diffeomorph I I M M 1) (y : M) : E →L[ℝ] E :=
  (e.continuousLinearMapAt ℝ y).comp <|
    (mfderiv I I Φ (Φ.symm y)).comp <|
      e.symmL ℝ (Φ.symm y)

/-- The coordinate derivative cocycle bundled as a continuous operator-valued map.
Continuity is explicit because the chosen global frame itself is only assumed continuous. -/
def realMatherCocycle
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (Φ : Diffeomorph I I M M 1)
    (hcont : Continuous (realMatherCocycleAt I e Φ)) : C(M, E →L[ℝ] E) :=
  ⟨realMatherCocycleAt I e Φ, hcont⟩

/-- Pointwise, global-frame coordinates turn the intrinsic Mather operator into the coordinate
derivative cocycle followed by composition with `Φ⁻¹`. -/
lemma tangentSectionCoordinates_matherOperator_apply
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (Φ : Diffeomorph I I M M 1)
    (hcont : Continuous (realMatherCocycleAt I e Φ))
    (V : ContinuousTangentSection (M := M) I) (y : M) :
    tangentSectionCoordinates I e he (matherOperator I Φ V) y =
      realMatherCocycle I e Φ hcont y
        (tangentSectionCoordinates I e he V (Φ.toHomeomorph.symm y)) := by
  rw [tangentSectionCoordinates_apply, tangentSectionCoordinates_apply]
  rw [matherOperator_apply, matherPushforward_apply]
  change e.continuousLinearMapAt ℝ y
      (mfderiv I I Φ (Φ.symm y) (V (Φ.symm y))) =
    e.continuousLinearMapAt ℝ y
      (mfderiv I I Φ (Φ.symm y)
        (e.symmL ℝ (Φ.symm y)
          (e.continuousLinearMapAt ℝ (Φ.symm y) (V (Φ.symm y)))))
  rw [e.symmL_continuousLinearMapAt (by simpa [he])]

/-- **Exact conjugacy theorem.**  The intrinsic Mather vector-field operator is the bounded
weighted-composition operator after passage to a global tangent frame. -/
theorem tangentSectionCoordinates_matherOperator
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (Φ : Diffeomorph I I M M 1)
    (hcont : Continuous (realMatherCocycleAt I e Φ))
    (V : ContinuousTangentSection (M := M) I) :
    tangentSectionCoordinates I e he (matherOperator I Φ V) =
      weightedComposition Φ.toHomeomorph (realMatherCocycle I e Φ hcont)
        (tangentSectionCoordinates I e he V) := by
  ext y
  exact tangentSectionCoordinates_matherOperator_apply I e he Φ hcont V y

/-- The inverse-diffeomorphism coordinate cocycle is a left inverse of the original cocycle. -/
lemma realMatherCocycleAt_inverse_left
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (Φ : Diffeomorph I I M M 1) (x : M) (v : E) :
    realMatherCocycleAt I e Φ.symm x
        (realMatherCocycleAt I e Φ (Φ x) v) = v := by
  simp only [realMatherCocycleAt]
  rw [show Φ.symm.symm = Φ by ext; rfl, Φ.symm_apply_apply]
  change e.continuousLinearMapAt ℝ x
      (mfderiv I I Φ.symm (Φ x)
        (e.symmL ℝ (Φ x)
          (e.continuousLinearMapAt ℝ (Φ x)
            (mfderiv I I Φ x (e.symmL ℝ x v))))) = v
  rw [e.symmL_continuousLinearMapAt (by simpa [he])]
  rw [mfderiv_symm_apply_mfderiv]
  rw [e.continuousLinearMapAt_symmL (by simpa [he])]

/-- The inverse-diffeomorphism coordinate cocycle is also a right inverse. -/
lemma realMatherCocycleAt_inverse_right
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ)
    (Φ : Diffeomorph I I M M 1) (y : M) (v : E) :
    realMatherCocycleAt I e Φ y
        (realMatherCocycleAt I e Φ.symm (Φ.symm y) v) = v := by
  simp only [realMatherCocycleAt]
  rw [show Φ.symm.symm = Φ by ext; rfl, Φ.apply_symm_apply]
  change e.continuousLinearMapAt ℝ y
      (mfderiv I I Φ (Φ.symm y)
        (e.symmL ℝ (Φ.symm y)
          (e.continuousLinearMapAt ℝ (Φ.symm y)
            (mfderiv I I Φ.symm y (e.symmL ℝ y v))))) = v
  rw [e.symmL_continuousLinearMapAt (by simpa [he])]
  rw [mfderiv_apply_mfderiv_symm]
  rw [e.continuousLinearMapAt_symmL (by simpa [he])]

/-! ## D. Invertibility and the genuine complex Banach spectrum -/

variable [CompleteSpace X]

private instance boundedContinuousFunction_nontrivial
    [Nonempty M] [Nontrivial X] : Nontrivial (M →ᵇ X) := by
  let x : M := Classical.choice ‹Nonempty M›
  rcases exists_pair_ne X with ⟨u, v, huv⟩
  refine ⟨⟨BoundedContinuousFunction.const M u,
    BoundedContinuousFunction.const M v, ?_⟩⟩
  intro h
  have hx := congrArg (fun f : M →ᵇ X => f x) h
  exact huv hx

/-- A pointwise inverse cocycle gives a left inverse to weighted composition. -/
lemma weightedComposition_inverse_left (g : M ≃ₜ M)
    (A B : C(M, X →L[𝕜] X))
    (hBA : ∀ x v, B x (A (g x) v) = v) :
    Function.LeftInverse (weightedComposition g.symm B)
      (weightedComposition g A) := by
  intro f
  ext x
  simp [hBA]

/-- A pointwise inverse cocycle gives a right inverse to weighted composition. -/
lemma weightedComposition_inverse_right (g : M ≃ₜ M)
    (A B : C(M, X →L[𝕜] X))
    (hAB : ∀ y v, A y (B (g.symm y) v) = v) :
    Function.RightInverse (weightedComposition g.symm B)
      (weightedComposition g A) := by
  intro f
  ext y
  simp [hAB]

/-- A continuous two-sided inverse cocycle makes weighted composition a unit in the bounded
operator algebra. -/
lemma weightedComposition_isUnit (g : M ≃ₜ M)
    (A B : C(M, X →L[𝕜] X))
    (hBA : ∀ x v, B x (A (g x) v) = v)
    (hAB : ∀ y v, A y (B (g.symm y) v) = v) :
    IsUnit (weightedComposition g A) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨(weightedComposition_inverse_left g A B hBA).injective,
    (weightedComposition_inverse_right g A B hAB).surjective⟩

section Complex

variable [NormedSpace ℂ X] [Nonempty M] [Nontrivial X]

/-- The genuine complex Banach-algebra spectrum of a complex Mather cocycle. -/
def matherSpectrum (g : M ≃ₜ M) (A : C(M, X →L[ℂ] X)) : Set ℂ :=
  spectrum ℂ (weightedComposition g A)

/-- The complex Mather spectrum is compact. -/
theorem matherSpectrum_isCompact (g : M ≃ₜ M)
    (A : C(M, X →L[ℂ] X)) :
    IsCompact (matherSpectrum g A) :=
  spectrum.isCompact _

/-- The complex Mather spectrum is nonempty. -/
theorem matherSpectrum_nonempty (g : M ≃ₜ M)
    (A : C(M, X →L[ℂ] X)) :
    (matherSpectrum g A).Nonempty :=
  spectrum.nonempty _

/-- Every spectral value is bounded by the supremum norm of the operator cocycle. -/
theorem norm_le_cocycleNorm_of_mem_matherSpectrum
    (g : M ≃ₜ M) (A : C(M, X →L[ℂ] X)) {z : ℂ}
    (hz : z ∈ matherSpectrum g A) :
    ‖z‖ ≤ ‖A‖ :=
  (spectrum.norm_le_norm_of_mem hz).trans (weightedComposition_norm_le g A)

/-- A continuous inverse cocycle excludes zero from the Mather spectrum. -/
theorem zero_not_mem_matherSpectrum
    (g : M ≃ₜ M) (A B : C(M, X →L[ℂ] X))
    (hBA : ∀ x v, B x (A (g x) v) = v)
    (hAB : ∀ y v, A y (B (g.symm y) v) = v) :
    (0 : ℂ) ∉ matherSpectrum g A :=
  spectrum.zero_notMem ℂ (weightedComposition_isUnit g A B hBA hAB)

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

/-- Explicit data witnessing that a complex cocycle is the complexification of a real cocycle.
The intertwining equation is the load-bearing link that prevents an unrelated complex operator
from being used as the Mather spectrum carrier. -/
structure ComplexCocycleExtension (A : C(M, E₀ →L[ℝ] E₀)) where
  /-- Real-linear inclusion into the complex fiber. -/
  embed : E₀ →L[ℝ] X
  /-- The inclusion loses no real tangent information. -/
  embed_injective : Function.Injective embed
  /-- The complex-linear extension of the coordinate derivative cocycle. -/
  cocycle : C(M, X →L[ℂ] X)
  /-- The real and complex cocycles intertwine pointwise. -/
  intertwines : ∀ y v, embed (A y v) = cocycle y (embed v)

/-- Apply the complexification embedding pointwise to a real compact section. -/
def ComplexCocycleExtension.embedSection
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := X) A)
    (f : M →ᵇ E₀) : M →ᵇ X :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun x => J.embed (f x)
      continuous_toFun := J.embed.continuous.comp f.continuous }

/-- Evaluation of the pointwise complexification map. -/
@[simp] lemma ComplexCocycleExtension.embedSection_apply
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := X) A)
    (f : M →ᵇ E₀) (x : M) :
    J.embedSection f x = J.embed (f x) := rfl

/-- **Complexification commutes with Mather evolution.**  This is the exact bridge from the
real coordinate operator to its complex Banach-space extension. -/
lemma ComplexCocycleExtension.weightedComposition_intertwines
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := X) A)
    (g : M ≃ₜ M) (f : M →ᵇ E₀) :
    J.embedSection (weightedComposition g A f) =
      weightedComposition g J.cocycle (J.embedSection f) := by
  ext y
  simp [J.intertwines]

/-- The spectrum carried by an explicit complexification witness. -/
def ComplexCocycleExtension.spectrum
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := X) A)
    (g : M ≃ₜ M) : Set ℂ :=
  matherSpectrum g J.cocycle

/-- An explicitly complexified Mather cocycle has nonempty spectrum. -/
theorem ComplexCocycleExtension.spectrum_nonempty
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := X) A)
    (g : M ≃ₜ M) :
    (J.spectrum g).Nonempty :=
  matherSpectrum_nonempty g J.cocycle

/-- An explicitly complexified Mather cocycle has compact spectrum. -/
theorem ComplexCocycleExtension.spectrum_isCompact
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := X) A)
    (g : M ≃ₜ M) :
    IsCompact (J.spectrum g) :=
  matherSpectrum_isCompact g J.cocycle

end Complex

end Physlib.Mathematics.DynamicalSystems.MatherSpectrum

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.DynamicalSystems.MatherSpectrum.tangentSectionCoordinatesLinearEquiv where
  formalizes @ "claim:a-global-linear-tangent-frame-identifies-continuous-vector-fields-with-the-compact-supremum-norm-banach-carrier",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:BoundedContinuousFunction",
  supported_by @ "lean:Bundle.Trivialization",
  caveat @ "claim:the-global-frame-is-explicit-data-and-is-not-asserted-for-an-arbitrary-tangent-bundle"

zil attach Physlib.Mathematics.DynamicalSystems.MatherSpectrum.tangentSectionCoordinates_matherOperator where
  formalizes @ "claim:the-intrinsic-mather-vector-field-operator-is-exactly-the-coordinate-derivative-weighted-composition-operator",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherPushforward_apply",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms",
  caveat @ "claim:continuity-of-the-coordinate-derivative-cocycle-is-an-explicit-premise-for-the-chosen-global-frame"

zil attach Physlib.Mathematics.DynamicalSystems.MatherSpectrum.matherSpectrum_nonempty where
  formalizes @ "claim:the-complexified-mather-operator-has-a-genuine-nonempty-complex-banach-algebra-spectrum",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:spectrum.nonempty",
  caveat @ "claim:this-is-the-spectrum-of-an-explicit-complex-linear-cocycle-not-a-proof-of-the-mather-anosov-spectral-criterion"

zil attach Physlib.Mathematics.DynamicalSystems.MatherSpectrum.ComplexCocycleExtension.weightedComposition_intertwines where
  formalizes @ "claim:the-explicit-fiber-complexification-intertwines-real-and-complex-mather-evolution",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherSpectrum.weightedComposition",
  caveat @ "claim:construction-of-a-complexification-witness-for-every-nontrivial-tangent-bundle-is-outside-this-module"

zil_file_contract physlib.matherSpectrum where
  promises "The compact supremum-norm Banach carrier for globally framed continuous tangent sections, exact conjugacy of the intrinsic Mather vector-field operator with its derivative-cocycle weighted-composition operator, and the genuine nonempty compact norm-controlled complex spectrum carried by an explicit complexification witness."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:BoundedContinuousFunction", "lean:Bundle.Trivialization",
    "lean:Physlib.Mathematics.DynamicalSystems.MatherVectorFieldOperator.matherOperator",
    "lean:spectrum.nonempty"]
  forbids_substitutes ["calling an algebraic spectrum the Mather spectrum",
    "replacing continuous tangent sections by an unrelated finite carrier",
    "silently assuming a global tangent frame",
    "using a complex operator without a real-to-complex cocycle intertwiner",
    "claiming the full Mather Anosov criterion"]
  witnessed_by [
    Physlib.Mathematics.DynamicalSystems.MatherSpectrum.tangentSectionCoordinatesLinearEquiv,
    Physlib.Mathematics.DynamicalSystems.MatherSpectrum.tangentSectionCoordinates_matherOperator,
    Physlib.Mathematics.DynamicalSystems.MatherSpectrum.matherSpectrum_nonempty,
    Physlib.Mathematics.DynamicalSystems.MatherSpectrum.ComplexCocycleExtension.weightedComposition_intertwines]

/- ZIL-END -/
