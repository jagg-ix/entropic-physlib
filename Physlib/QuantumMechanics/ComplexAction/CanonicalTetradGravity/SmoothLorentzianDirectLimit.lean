/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HarmonicGaugeLocalEinstein
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
meta import Zil

/-!
# Smooth Lorentzian descent through the Cauchy-development direct limit

`DevelopmentDirectLimit` constructs the correct quotient carrier and descends
causality, the Einstein predicate, the Cauchy surface, and compact causal
diamonds.  This module supplies the missing smooth-geometric layer.

For a directed system whose canonical component maps are open embeddings,
component charts lift to open partial homeomorphisms on the quotient.  These
lifted charts cover the quotient and therefore define an actual Mathlib
`ChartedSpace`.  Pairwise smooth compatibility of those concrete lifted
charts then constructs an actual `IsManifold`.

A compatible family of continuous bilinear metric forms descends by
Mathlib's `DirectLimit.lift`.  Symmetry, nondegeneracy, and constant
Lorentzian index are proved on quotient representatives.  With the local
chart smoothness of that descended family, the result is an actual
`PseudoRiemannianMetric`, not merely a matrix field labelled as one.

The harmonic-gauge uniqueness theorem in the preceding module is the source
of the open metric-preserving transition maps in Einstein applications.
This file is deliberately generic: it proves the quotient construction once
and exposes only the standard local smoothness obligations needed by any
manifold gluing theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity

namespace SmoothLorentzianDirectLimit

open DevelopmentDirectLimit
open DevelopmentDirectLimit.DirectedDevelopmentSystem
open PseudoRiemannianMetric

universe u v w

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {S : Type v}

/-! ## A. A genuine quotient atlas -/

/-- Component chart structures and the open-embedding property needed to
lift their charts to the direct-limit carrier. -/
structure OpenChartedDevelopmentSystem
    (D : DirectedDevelopmentSystem ι S)
    (H : Type (max u v)) [TopologicalSpace H] [Nonempty H] where
  componentChartedSpace :
    ∀ i, @ChartedSpace H _ (D.Point i) (D.topology i)
  of_isOpenEmbedding :
    ∀ i,
      @IsOpenEmbedding (D.Point i) D.GluedCarrier
        (D.topology i) D.instTopologicalSpaceGluedCarrier (D.of i)

namespace OpenChartedDevelopmentSystem

variable {H : Type (max u v)} [TopologicalSpace H] [Nonempty H]
variable {D : DirectedDevelopmentSystem ι S}

/-- The preferred component chart at `x`, with the component topology and
charted-space structures installed explicitly. -/
noncomputable def componentChart
    (A : OpenChartedDevelopmentSystem D H)
    (i : ι) (x : D.Point i) :
    @OpenPartialHomeomorph (D.Point i) H (D.topology i) _ := by
  letI : TopologicalSpace (D.Point i) := D.topology i
  letI : ChartedSpace H (D.Point i) := A.componentChartedSpace i
  exact chartAt H x

/-- Lift a component chart along its canonical open embedding into the
direct limit. -/
noncomputable def liftedChart
    (A : OpenChartedDevelopmentSystem D H)
    (i : ι) (x : D.Point i) :
    @OpenPartialHomeomorph D.GluedCarrier H
      D.instTopologicalSpaceGluedCarrier _ := by
  letI : TopologicalSpace (D.Point i) := D.topology i
  exact (A.componentChart i x).lift_openEmbedding
    (A.of_isOpenEmbedding i)

/-- Every point of the direct limit comes from one of its component
developments.  This is the coverage theorem used by the quotient atlas. -/
theorem exists_representative
    (A : OpenChartedDevelopmentSystem D H)
    (p : D.GluedCarrier) :
    ∃ ix : Σ i, D.Point i, D.of ix.1 ix.2 = p := by
  obtain ⟨i, x, h⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j h => D.map i j h) p
  exact ⟨⟨i, x⟩, h.symm⟩

/-- Choose one representative of a direct-limit point. -/
noncomputable def representative
    (A : OpenChartedDevelopmentSystem D H)
    (p : D.GluedCarrier) : Σ i, D.Point i :=
  Classical.choose (A.exists_representative p)

/-- The chosen representative maps to the original quotient point. -/
theorem of_representative
    (A : OpenChartedDevelopmentSystem D H)
    (p : D.GluedCarrier) :
    D.of (A.representative p).1 (A.representative p).2 = p := by
  exact Classical.choose_spec (A.exists_representative p)

/-- Lifted component charts cover the direct limit and define a genuine
Mathlib charted-space structure. -/
@[reducible] noncomputable def gluedChartedSpace
    (A : OpenChartedDevelopmentSystem D H) :
    @ChartedSpace H _ D.GluedCarrier
      D.instTopologicalSpaceGluedCarrier where
  atlas := Set.range fun ix : Σ i, D.Point i =>
    A.liftedChart ix.1 ix.2
  chartAt p :=
    A.liftedChart (A.representative p).1 (A.representative p).2
  mem_chart_source := by
    intro p
    change p ∈ D.of (A.representative p).1 ''
      (A.componentChart (A.representative p).1
        (A.representative p).2).source
    refine ⟨(A.representative p).2, ?_, A.of_representative p⟩
    letI : TopologicalSpace (D.Point (A.representative p).1) :=
      D.topology (A.representative p).1
    letI : ChartedSpace H (D.Point (A.representative p).1) :=
      A.componentChartedSpace (A.representative p).1
    exact mem_chart_source H _
  chart_mem_atlas := by
    intro p
    exact ⟨A.representative p, rfl⟩

/-- Smooth compatibility stated on the concrete lifted component charts.
This is precisely the local transition-map obligation supplied by harmonic
local isometries in the Einstein application. -/
structure SmoothCompatibility
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞)
    (A : OpenChartedDevelopmentSystem D H) : Prop where
  compatible :
    ∀ i (x : D.Point i) j (y : D.Point j),
      ContDiffOn ℝ n
        (I ∘ (A.liftedChart i x).symm ≫ₕ
          A.liftedChart j y ∘ I.symm)
        (I.symm ⁻¹' ((A.liftedChart i x).symm ≫ₕ
          A.liftedChart j y).source ∩ Set.range I)

/-- Pairwise compatibility of the lifted charts constructs the actual
smooth manifold structure on the direct limit. -/
@[zil_level physical_theorem, reducible]
noncomputable def gluedIsManifold
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞)
    (A : OpenChartedDevelopmentSystem D H)
    (C : SmoothCompatibility I n A) :
    @IsManifold ℝ _ E _ _ H _ I n D.GluedCarrier
      D.instTopologicalSpaceGluedCarrier A.gluedChartedSpace := by
  letI : TopologicalSpace D.GluedCarrier :=
    D.instTopologicalSpaceGluedCarrier
  letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
  refine isManifold_of_contDiffOn I n D.GluedCarrier ?_
  intro e e' he he'
  change e ∈ Set.range (fun ix : Σ i, D.Point i =>
    A.liftedChart ix.1 ix.2) at he
  change e' ∈ Set.range (fun ix : Σ i, D.Point i =>
    A.liftedChart ix.1 ix.2) at he'
  obtain ⟨⟨i, x⟩, rfl⟩ := he
  obtain ⟨⟨j, y⟩, rfl⟩ := he'
  exact C.compatible i x j y

/-! ## B. Descent of the Lorentzian metric -/

/-- A metric-valued family on the components, invariant under every
extension embedding.  Equality is in common model coordinates; the harmonic
chart transition is the identity there. -/
structure CompatibleMetricFamily
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : DirectedDevelopmentSystem ι S) where
  componentMetric :
    ∀ i, D.Point i → E →L[ℝ] (E →L[ℝ] ℝ)
  metric_map :
    ∀ i j (hij : i ≤ j) (p : D.Point i),
      componentMetric i p =
        componentMetric j (D.map i j hij p)

namespace CompatibleMetricFamily

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ChartedSpace H E]

/-- The quadratic form canonically associated with a continuous bilinear
form on the common model space.  Keeping this construction on `E` lets the
constant-index hypothesis be checked componentwise, before the quotient
manifold structure is installed. -/
noncomputable def bilinearQuadraticForm
    (b : E →L[ℝ] (E →L[ℝ] ℝ)) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ (fun v w => b v w)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp))

/-- The well-defined metric bilinear form on the direct-limit carrier. -/
noncomputable def gluedMetricVal
    (G : CompatibleMetricFamily (E := E) D) :
    D.GluedCarrier → E →L[ℝ] (E →L[ℝ] ℝ) :=
  DirectLimit.lift
    (fun i j h => D.map i j h)
    G.componentMetric
    (fun i j hij p => G.metric_map i j hij p)

@[simp]
theorem gluedMetricVal_of
    (G : CompatibleMetricFamily (E := E) D)
    (i : ι) (p : D.Point i) :
    G.gluedMetricVal (D.of i p) = G.componentMetric i p :=
  rfl

/-- The local metric facts which turn the descended bilinear family into an
actual smooth pseudo-Riemannian metric. -/
structure SmoothPseudoRiemannianData
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞)
    (A : OpenChartedDevelopmentSystem D H)
    (C : SmoothCompatibility I (n + 1) A)
    (G : CompatibleMetricFamily (E := E) D)
    [FiniteDimensional ℝ E] where
  component_symm :
    ∀ i (p : D.Point i) v w,
      G.componentMetric i p v w = G.componentMetric i p w v
  component_nondegenerate :
    ∀ i (p : D.Point i) v,
      (∀ w, G.componentMetric i p v w = 0) → v = 0
  index : ℕ
  component_index :
    ∀ i (p : D.Point i),
      (bilinearQuadraticForm (G.componentMetric i p)).negDim = index
  smooth_in_glued_charts :
    letI : TopologicalSpace D.GluedCarrier :=
      D.instTopologicalSpaceGluedCarrier
    letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
    letI : IsManifold I (n + 1) D.GluedCarrier :=
      A.gluedIsManifold I (n + 1) C
    ∀ (x₀ : D.GluedCarrier) (v w : E),
      let e := extChartAt I x₀
      ContDiffWithinAt ℝ n
        (fun y =>
          G.gluedMetricVal (e.symm y)
            (mfderiv I I e.symm y v)
            (mfderiv I I e.symm y w))
        e.target (e x₀)

/-- Symmetry descends from every representative. -/
theorem gluedMetricVal_symm
    {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {A : OpenChartedDevelopmentSystem D H}
    {C : SmoothCompatibility I (n + 1) A}
    (G : CompatibleMetricFamily (E := E) D)
    [FiniteDimensional ℝ E]
    (L : SmoothPseudoRiemannianData I n A C G)
    (p : D.GluedCarrier) (v w : E) :
    G.gluedMetricVal p v w = G.gluedMetricVal p w v := by
  refine DirectLimit.induction
    (f := fun i j h => D.map i j h) (fun i x => ?_) p
  exact L.component_symm i x v w

/-- Nondegeneracy descends from every representative. -/
theorem gluedMetricVal_nondegenerate
    {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {A : OpenChartedDevelopmentSystem D H}
    {C : SmoothCompatibility I (n + 1) A}
    (G : CompatibleMetricFamily (E := E) D)
    [FiniteDimensional ℝ E]
    (L : SmoothPseudoRiemannianData I n A C G)
    (p : D.GluedCarrier) (v : E)
    (hzero : ∀ w, G.gluedMetricVal p v w = 0) :
    v = 0 := by
  refine DirectLimit.induction
    (f := fun i j h => D.map i j h) (fun i x hx => ?_) p hzero
  apply L.component_nondegenerate i x v
  intro w
  exact hx w

/-- The descended metric has the declared constant index at every quotient
point, so its index is locally constant. -/
theorem gluedMetricVal_index_eq
    {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {A : OpenChartedDevelopmentSystem D H}
    {C : SmoothCompatibility I (n + 1) A}
    (G : CompatibleMetricFamily (E := E) D)
    [FiniteDimensional ℝ E]
    (L : SmoothPseudoRiemannianData I n A C G)
    (tangentFinite :
      letI : TopologicalSpace D.GluedCarrier :=
        D.instTopologicalSpaceGluedCarrier
      letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
      ∀ x : D.GluedCarrier, FiniteDimensional ℝ (TangentSpace I x))
    (p : D.GluedCarrier) :
    letI : TopologicalSpace D.GluedCarrier :=
      D.instTopologicalSpaceGluedCarrier
    letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
    letI : ∀ x : D.GluedCarrier, FiniteDimensional ℝ (TangentSpace I x) :=
      tangentFinite
    (pseudoRiemannianMetricValToQuadraticForm
      (E := E) (H := H) (M := D.GluedCarrier) (I := I)
      (fun x => G.gluedMetricVal x)
      (G.gluedMetricVal_symm L) p).negDim = L.index := by
  letI : TopologicalSpace D.GluedCarrier :=
    D.instTopologicalSpaceGluedCarrier
  letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
  letI : ∀ x : D.GluedCarrier, FiniteDimensional ℝ (TangentSpace I x) :=
    tangentFinite
  obtain ⟨⟨i, x⟩, hp⟩ := A.exists_representative p
  subst p
  have hform :
      pseudoRiemannianMetricValToQuadraticForm
          (E := E) (H := H) (M := D.GluedCarrier) (I := I)
          (fun x => G.gluedMetricVal x)
          (G.gluedMetricVal_symm L) (D.of i x) =
        bilinearQuadraticForm (G.componentMetric i x) := by
    ext v
    rfl
  rw [hform]
  exact L.component_index i x

/-- **The actual smooth pseudo-Riemannian metric on the glued maximal
development.** -/
@[zil_level physical_theorem]
noncomputable def gluedPseudoRiemannianMetric
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞)
    (A : OpenChartedDevelopmentSystem D H)
    (C : SmoothCompatibility I (n + 1) A)
    (G : CompatibleMetricFamily (E := E) D)
    [FiniteDimensional ℝ E]
    (L : SmoothPseudoRiemannianData I n A C G) :
    (tangentFinite :
      letI : TopologicalSpace D.GluedCarrier :=
        D.instTopologicalSpaceGluedCarrier
      letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
      ∀ x : D.GluedCarrier, FiniteDimensional ℝ (TangentSpace I x)) →
    letI : TopologicalSpace D.GluedCarrier :=
      D.instTopologicalSpaceGluedCarrier
    letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
    letI : IsManifold I (n + 1) D.GluedCarrier :=
      A.gluedIsManifold I (n + 1) C
    PseudoRiemannianMetric E H D.GluedCarrier n I := by
  intro tangentFinite
  letI : TopologicalSpace D.GluedCarrier :=
    D.instTopologicalSpaceGluedCarrier
  letI : ChartedSpace H D.GluedCarrier := A.gluedChartedSpace
  letI : IsManifold I (n + 1) D.GluedCarrier :=
    A.gluedIsManifold I (n + 1) C
  letI : ∀ x : D.GluedCarrier, FiniteDimensional ℝ (TangentSpace I x) :=
    tangentFinite
  exact
    { val := G.gluedMetricVal
      symm := G.gluedMetricVal_symm L
      nondegenerate := G.gluedMetricVal_nondegenerate L
      smooth_in_charts' := L.smooth_in_glued_charts
      negDim_isLocallyConstant := by
        have hfun :
            (fun p : D.GluedCarrier =>
              (pseudoRiemannianMetricValToQuadraticForm
                (E := E) (H := H) (M := D.GluedCarrier) (I := I)
                (fun x => G.gluedMetricVal x)
                (G.gluedMetricVal_symm L) p).negDim) =
              fun _ => L.index := by
          funext p
          exact G.gluedMetricVal_index_eq L tangentFinite p
        rw [hfun]
        exact IsLocallyConstant.const L.index }

end CompatibleMetricFamily

end OpenChartedDevelopmentSystem

/- ZIL-BEGIN -/

zil attach OpenChartedDevelopmentSystem.gluedIsManifold where
  formalizes @ "claim:open-component-embeddings-and-pairwise-smooth-lifted-chart-transitions-give-the-cauchy-development-direct-limit-an-actual-smooth-manifold-structure",
  epistemic_status @ "risky",
  supported_by @ "lean:OpenPartialHomeomorph.lift_openEmbedding",
  supported_by @ "lean:isManifold_of_contDiffOn",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.DevelopmentDirectLimit.DirectedDevelopmentSystem.GluedCarrier",
  caveat @ "premise:canonical-component-maps-are-open-embeddings-and-the-concrete-lifted-chart-transitions-are-smooth"

zil attach OpenChartedDevelopmentSystem.CompatibleMetricFamily.gluedPseudoRiemannianMetric where
  formalizes @ "claim:a-compatible-smooth-nondegenerate-symmetric-constant-index-metric-family-descends-through-the-directed-quotient-to-an-actual-pseudo-riemannian-metric",
  epistemic_status @ "risky",
  supported_by @ "lean:DirectLimit.lift",
  supported_by @ "lean:PseudoRiemannianMetric",
  caveat @ "premise:local-chart-smoothness-of-the-descended-bilinear-family-and-constant-component-index-are-explicit-geometric-data",
  caveat @ "the-harmonic-local-isometry-layer-supplies-metric-compatible-transitions-in-the-einstein-instantiation"

zil_file_contract physlib.smoothLorentzianDirectLimit where
  promises "The varying-carrier Cauchy-development quotient now admits a genuine smooth-geometric promotion. Component charts lift along open canonical embeddings and cover the direct limit, forming an actual ChartedSpace. Pairwise smooth compatibility constructs an actual IsManifold. A metric family compatible with all extension embeddings descends by Mathlib DirectLimit.lift; symmetry, nondegeneracy and constant index descend by quotient induction, and local chart smoothness packages the result as an actual PseudoRiemannianMetric."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:OpenPartialHomeomorph.lift_openEmbedding",
    "lean:isManifold_of_contDiffOn",
    "lean:DirectLimit.lift",
    "lean:PseudoRiemannianMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HarmonicGaugeLocalEinstein.local_harmonicEinstein_unique_up_to_fixedCauchy_isometry"
  ]
  forbids_substitutes [
    "calling-the-topological-direct-limit-a-smooth-manifold-without-constructing-a-charted-space-and-proving-chart-compatibility",
    "defining-a-metric-on-representatives-without-the-direct-limit-compatibility-law",
    "calling-a-symmetric-matrix-field-a-pseudo-riemannian-metric-without-nondegeneracy-smoothness-and-constant-index"
  ]
  witnessed_by [
    OpenChartedDevelopmentSystem.gluedChartedSpace,
    OpenChartedDevelopmentSystem.gluedIsManifold,
    OpenChartedDevelopmentSystem.CompatibleMetricFamily.gluedMetricVal,
    OpenChartedDevelopmentSystem.CompatibleMetricFamily.gluedMetricVal_symm,
    OpenChartedDevelopmentSystem.CompatibleMetricFamily.gluedMetricVal_nondegenerate,
    OpenChartedDevelopmentSystem.CompatibleMetricFamily.gluedPseudoRiemannianMetric
  ]

/- ZIL-END -/

end SmoothLorentzianDirectLimit

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity
