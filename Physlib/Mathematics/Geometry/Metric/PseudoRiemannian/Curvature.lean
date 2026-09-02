/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.LeviCivita
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
public import Mathlib.LinearAlgebra.Trace

/-!
# Coordinate independence of Levi-Civita curvature

The intrinsic Levi-Civita uniqueness theorem determines the connection on
differentiable vector fields.  This file propagates that uniqueness through
the three covariant derivatives in the curvature commutator.  Consequently,
two atlas representatives of the same pseudo-Riemannian Levi-Civita
connection have the same curvature action on chart overlaps.

The regularity hypotheses on the two first-covariant-derivative sections are
explicit.  They are exactly what the outer covariant derivatives need; no
coordinate transition law or curvature identity is assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle FiberBundle Module
open scoped Manifold
open
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

namespace PseudoRiemannianMetric

universe v w

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- The first covariant-derivative section used by the curvature commutator. -/
def firstCovariantSection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (Y σ : ∀ x : M, TangentSpace I x) : ∀ x : M, TangentSpace I x :=
  fun x ↦ cov σ x (Y x)

/-- Atlas representatives of one Levi-Civita connection give the same first
covariant-derivative section on globally differentiable fields. -/
lemma firstCovariantSection_atlas_eq
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (Y σ : ∀ x : M, TangentSpace I x)
    (hY : ∀ x, MDiffAt (T% Y) x) (hσ : ∀ x, MDiffAt (T% σ) x) :
    firstCovariantSection I (cov a) Y σ =
      firstCovariantSection I (cov b) Y σ := by
  funext x
  exact leviCivitaAtlas_overlap I g cov hatlas a b Y σ x (hY x) (hσ x)

/-- **Coordinate independence of Levi-Civita curvature.** Two representatives
of a Levi-Civita atlas have identical coordinate-free curvature action on
differentiable vector fields.  Smoothness of the two first-derivative sections
at `x` is stated explicitly because it is the analytic input needed by the
outer covariant derivatives. -/
theorem leviCivitaAtlas_curvature_overlap
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (σ X Y : ∀ x : M, TangentSpace I x) (x : M)
    (hσ : ∀ y, MDiffAt (T% σ) y)
    (hX : ∀ y, MDiffAt (T% X) y)
    (hY : ∀ y, MDiffAt (T% Y) y)
    (hNablaY : MDiffAt (T% (firstCovariantSection I (cov b) Y σ)) x)
    (hNablaX : MDiffAt (T% (firstCovariantSection I (cov b) X σ)) x)
    (hbracket : MDiffAt (T% (VectorField.mlieBracket I X Y)) x) :
    manifoldCovariantCurvatureAction (cov a) σ X Y x =
      manifoldCovariantCurvatureAction (cov b) σ X Y x := by
  have hYsection := firstCovariantSection_atlas_eq I g cov hatlas a b Y σ hY hσ
  have hXsection := firstCovariantSection_atlas_eq I g cov hatlas a b X σ hX hσ
  have houterY :
      cov a (firstCovariantSection I (cov b) Y σ) x (X x) =
        cov b (firstCovariantSection I (cov b) Y σ) x (X x) :=
    leviCivitaAtlas_overlap I g cov hatlas a b X
      (firstCovariantSection I (cov b) Y σ) x (hX x) hNablaY
  have houterX :
      cov a (firstCovariantSection I (cov b) X σ) x (Y x) =
        cov b (firstCovariantSection I (cov b) X σ) x (Y x) :=
    leviCivitaAtlas_overlap I g cov hatlas a b Y
      (firstCovariantSection I (cov b) X σ) x (hY x) hNablaX
  have hlast :
      cov a σ x (VectorField.mlieBracket I X Y x) =
        cov b σ x (VectorField.mlieBracket I X Y x) :=
    leviCivitaAtlas_overlap I g cov hatlas a b
      (VectorField.mlieBracket I X Y) σ x hbracket (hσ x)
  unfold manifoldCovariantCurvatureAction
  change
    cov a (firstCovariantSection I (cov a) Y σ) x (X x) -
          cov a (firstCovariantSection I (cov a) X σ) x (Y x) -
        cov a σ x (VectorField.mlieBracket I X Y x) = _
  rw [hYsection, hXsection, houterY, houterX, hlast]
  rfl

/-! ## Frame contractions -/

/-- The pseudo-orthonormal-frame contraction
`sum_i epsilon_i g(R(e_i,Y)V,e_i)`.  Supplying the frame signs explicitly
allows the same carrier to cover Riemannian and pseudo-Riemannian signatures. -/
def frameRicciContractionAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V Y : ∀ x : M, TangentSpace I x) (x : M) : ℝ :=
  ∑ i, sign i * g.val x
    (manifoldCovariantCurvatureAction cov V (frame i) Y x) (frame i x)

/-- The frame-contracted Ricci expression is independent of the
Levi-Civita atlas representative.  This is the invariant contraction needed
by the Ricci-coupled Maxwell operator; it is obtained by contracting the
preceding curvature-overlap theorem, not by assuming a coordinate Ricci law. -/
theorem leviCivitaAtlas_frameRicci_overlap {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V Y : ∀ x : M, TangentSpace I x) (x : M)
    (hV : ∀ y, MDiffAt (T% V) y)
    (hY : ∀ y, MDiffAt (T% Y) y)
    (hframe : ∀ i y, MDiffAt (T% (frame i)) y)
    (hNablaY : MDiffAt (T% (firstCovariantSection I (cov b) Y V)) x)
    (hNablaFrame : ∀ i,
      MDiffAt (T% (firstCovariantSection I (cov b) (frame i) V)) x)
    (hbracket : ∀ i,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) Y)) x) :
    frameRicciContractionAt I g (cov a) sign frame V Y x =
      frameRicciContractionAt I g (cov b) sign frame V Y x := by
  unfold frameRicciContractionAt
  apply Finset.sum_congr rfl
  intro i _
  rw [leviCivitaAtlas_curvature_overlap I g cov hatlas a b V (frame i) Y x
    hV (hframe i) hY hNablaY (hNablaFrame i) (hbracket i)]

/-! ## Basis-independent metric contractions -/

/-- A basis is pseudo-orthonormal for `g` at `x` with the supplied signature
signs. Requiring every sign to square to one excludes degenerate frame
weights and covers both positive and negative metric directions. -/
def IsPseudoOrthonormalBasisAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (sign : Fin d → ℝ) (b : Basis (Fin d) ℝ (TangentSpace I x)) : Prop :=
  (∀ i j, g.val x (b i) (b j) = if i = j then sign i else 0) ∧
    ∀ i, sign i * sign i = 1

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- Coordinates in a pseudo-orthonormal basis are obtained by the signed
metric pairing. -/
lemma pseudoOrthonormalBasis_repr_eq_sign_mul_inner {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (sign : Fin d → ℝ) (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (v : TangentSpace I x) (i : Fin d) :
    b.repr v i = sign i * g.val x v (b i) := by
  have hsum : (∑ j, b.repr v j * g.val x (b j) (b i)) =
      b.repr v i * sign i := by
    calc
      _ = b.repr v i * g.val x (b i) (b i) := by
        rw [Finset.sum_eq_single i]
        · intro j _ hji
          rw [hb.1 j i, if_neg hji]
          ring
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = b.repr v i * sign i := by rw [hb.1 i i, if_pos rfl]
  have hpair : g.val x v (b i) = b.repr v i * sign i := by
    calc
      _ = g.val x (∑ j, b.repr v j • b j) (b i) :=
        congrArg (fun w => g.val x w (b i)) (b.sum_repr v).symm
      _ = ∑ j, b.repr v j * g.val x (b j) (b i) := by
        rw [map_sum]
        rw [_root_.sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        rw [smul_apply]
        rfl
      _ = b.repr v i * sign i := hsum
  rw [hpair]
  calc
    b.repr v i = (sign i * sign i) * b.repr v i := by rw [hb.2 i]; ring
    _ = sign i * (b.repr v i * sign i) := by ring

/-- The Ricci contraction of a curvature endomorphism is its linear trace.
This definition is independent of every basis by construction. -/
def curvatureRicciTraceAt (x : M)
    (R : TangentSpace I x →ₗ[ℝ] TangentSpace I x) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) R

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A pseudo-orthonormal frame contraction computes the basis-independent
linear trace of the represented curvature endomorphism. -/
lemma frameRicciContractionAt_eq_curvatureRicciTraceAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V Y : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (hframe : ∀ i, b i = frame i x)
    (R : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hR : ∀ i, R (b i) =
      manifoldCovariantCurvatureAction cov V (frame i) Y x) :
    frameRicciContractionAt I g cov sign frame V Y x =
      curvatureRicciTraceAt I x R := by
  rw [curvatureRicciTraceAt, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold frameRicciContractionAt
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change sign i * g.val x
      (manifoldCovariantCurvatureAction cov V (frame i) Y x) (frame i x) =
    b.repr (R (b i)) i
  rw [hR i, ← hframe i]
  exact (pseudoOrthonormalBasis_repr_eq_sign_mul_inner I g x sign b hb
    (manifoldCovariantCurvatureAction cov V (frame i) Y x) i).symm

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Any two pseudo-orthonormal frame contractions representing the same
curvature endomorphism agree. -/
lemma frameRicciContractionAt_independent {d e : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ) (sign' : Fin e → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (frame' : Fin e → ∀ x : M, TangentSpace I x)
    (V Y : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (b' : Basis (Fin e) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (hb' : IsPseudoOrthonormalBasisAt I g x sign' b')
    (hframe : ∀ i, b i = frame i x) (hframe' : ∀ i, b' i = frame' i x)
    (R : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hR : ∀ i, R (b i) =
      manifoldCovariantCurvatureAction cov V (frame i) Y x)
    (hR' : ∀ i, R (b' i) =
      manifoldCovariantCurvatureAction cov V (frame' i) Y x) :
    frameRicciContractionAt I g cov sign frame V Y x =
      frameRicciContractionAt I g cov sign' frame' V Y x := by
  rw [frameRicciContractionAt_eq_curvatureRicciTraceAt I g cov sign frame
    V Y x b hb hframe R hR]
  rw [frameRicciContractionAt_eq_curvatureRicciTraceAt I g cov sign' frame'
    V Y x b' hb' hframe' R hR']

/-- The intrinsic Ricci covector obtained by tracing the curvature
endomorphism assigned to each second curvature argument. -/
def curvatureRicciCovectorAt (x : M)
    (R : TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x)) :
    TangentSpace I x →L[ℝ] ℝ := by
  letI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  exact LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (TangentSpace I x)).comp R)

/-- The basis-free raised Ricci action, obtained by applying the metric sharp
map to the curvature-trace covector. -/
def raisedCurvatureRicciAt
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (R : TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x)) : TangentSpace I x :=
  g.sharpL x (curvatureRicciCovectorAt I x R)

/-- Turn a vector-valued bilinear form into the endomorphism whose trace is
its metric contraction after testing the output against a covector. -/
def metricTraceEndomorphismAt (g : PseudoRiemannianMetric E H M n I) (x : M)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun X := g.sharpL x (ω.comp (Hess X))
  map_add' X Y := by
    apply g.flatL_inj x
    simp
  map_smul' c X := by
    apply g.flatL_inj x
    simp

/-- The double-dual functional obtained by tracing a vector-valued bilinear
form after testing its output against an arbitrary covector. Finite-dimensional
reflexivity turns this functional into the intrinsic metric trace below. -/
def metricTraceDualAt (g : PseudoRiemannianMetric E H M n I) (x : M)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x) :
    Module.Dual ℝ (Module.Dual ℝ (TangentSpace I x)) := by
  letI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  exact {
    toFun ω := LinearMap.trace ℝ (TangentSpace I x)
      (metricTraceEndomorphismAt I g x Hess
        (LinearMap.toContinuousLinearMap ω))
    map_add' ω η := by
      rw [show LinearMap.toContinuousLinearMap (ω + η) =
        LinearMap.toContinuousLinearMap ω + LinearMap.toContinuousLinearMap η by rfl]
      rw [show metricTraceEndomorphismAt I g x Hess
          (LinearMap.toContinuousLinearMap ω + LinearMap.toContinuousLinearMap η) =
        metricTraceEndomorphismAt I g x Hess (LinearMap.toContinuousLinearMap ω) +
          metricTraceEndomorphismAt I g x Hess (LinearMap.toContinuousLinearMap η) by
        ext X
        apply g.flatL_inj x
        ext Y
        simp [metricTraceEndomorphismAt]]
      exact map_add _ _ _
    map_smul' c ω := by
      rw [show LinearMap.toContinuousLinearMap (c • ω) =
        c • LinearMap.toContinuousLinearMap ω by rfl]
      rw [show metricTraceEndomorphismAt I g x Hess
          (c • LinearMap.toContinuousLinearMap ω) =
        c • metricTraceEndomorphismAt I g x Hess (LinearMap.toContinuousLinearMap ω) by
        ext X
        apply g.flatL_inj x
        ext Y
        simp [metricTraceEndomorphismAt]]
      exact map_smul _ _ _ }

/-- The basis-free metric trace of a vector-valued bilinear form. It is the
unique tangent vector whose evaluation by every covector is the linear trace
of the corresponding raised endomorphism. -/
def metricTraceAt (g : PseudoRiemannianMetric E H M n I) (x : M)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x) : TangentSpace I x :=
  (Module.evalEquiv ℝ (TangentSpace I x)).symm (metricTraceDualAt I g x Hess)

/-- A tangent vector is the basis-independent metric trace of a
vector-valued bilinear form when all covectors evaluate it as the trace of the
corresponding raised endomorphism. -/
def IsMetricTraceAt (g : PseudoRiemannianMetric E H M n I) (x : M)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (traceValue : TangentSpace I x) : Prop :=
  ∀ ω : TangentSpace I x →L[ℝ] ℝ,
    ω traceValue = LinearMap.trace ℝ (TangentSpace I x)
      (metricTraceEndomorphismAt I g x Hess ω)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The bidual construction `metricTraceAt` satisfies the intrinsic trace
specification. -/
lemma metricTraceAt_isMetricTraceAt
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x) :
    IsMetricTraceAt I g x Hess (metricTraceAt I g x Hess) := by
  intro ω
  exact Module.apply_evalEquiv_symm_apply ℝ (TangentSpace I x)
    ω.toLinearMap (metricTraceDualAt I g x Hess)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The basis-independent metric trace is unique. -/
lemma IsMetricTraceAt.unique
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    {Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x}
    {u v : TangentSpace I x} (hu : IsMetricTraceAt I g x Hess u)
    (hv : IsMetricTraceAt I g x Hess v) : u = v := by
  apply sub_eq_zero.mp
  apply g.nondegenerate x (u - v)
  intro z
  have h := (hu (g.val x z)).trans (hv (g.val x z)).symm
  rw [g.symm x z u, g.symm x z v] at h
  simpa only [map_sub, sub_apply, sub_eq_zero] using h

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The signed sum in any pseudo-orthonormal basis satisfies the intrinsic
metric-trace specification. -/
lemma pseudoOrthonormalBasis_sum_isMetricTraceAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (sign : Fin d → ℝ) (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x) :
    IsMetricTraceAt I g x Hess (∑ i, sign i • Hess (b i) (b i)) := by
  intro ω
  rw [map_sum, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change sign i * ω (Hess (b i) (b i)) =
    b.repr (g.sharpL x (ω.comp (Hess (b i)))) i
  rw [pseudoOrthonormalBasis_repr_eq_sign_mul_inner I g x sign b hb]
  have hflat :
      g.val x (g.sharpL x (ω.comp (Hess (b i)))) (b i) =
        ω (Hess (b i) (b i)) := by
    exact congrArg (fun f : TangentSpace I x →L[ℝ] ℝ => f (b i))
      (g.flatL_apply_sharpL x (ω.comp (Hess (b i))))
  rw [hflat]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- Signed pseudo-orthonormal contractions of one bilinear tensor agree for
any two pseudo-orthonormal bases. -/
lemma pseudoOrthonormalBasis_metricTrace_independent {d e : ℕ}
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (sign : Fin d → ℝ) (sign' : Fin e → ℝ)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (b' : Basis (Fin e) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (hb' : IsPseudoOrthonormalBasisAt I g x sign' b')
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x) :
    (∑ i, sign i • Hess (b i) (b i)) =
      ∑ i, sign' i • Hess (b' i) (b' i) :=
  IsMetricTraceAt.unique I g x
    (pseudoOrthonormalBasis_sum_isMetricTraceAt I g x sign b hb Hess)
    (pseudoOrthonormalBasis_sum_isMetricTraceAt I g x sign' b' hb' Hess)

/-! ## Intrinsic Ricci-coupled Maxwell operator -/

/-- The frame trace of the covariant Hessian,
`sum_i epsilon_i (∇_{e_i}∇_{e_i}V - ∇_{∇_{e_i}e_i}V)`.
The correction term makes this the intrinsic rough wave operator rather than
the coordinate-only sum of second derivatives. -/
def frameBochnerWaveAt {d : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  ∑ i, sign i •
    (cov (firstCovariantSection I cov (frame i) V) x (frame i x) -
      cov V x (cov (frame i) x (frame i x)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [ChartedSpace H E]
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- If a bilinear covariant Hessian represents the displayed second
covariant derivatives on a pseudo-orthonormal frame, the existing frame
Bochner expression is its signed metric-trace sum. -/
lemma frameBochnerWaveAt_eq_metricTraceSum {d : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ i, Hess (b i) (b i) =
      cov (firstCovariantSection I cov (frame i) V) x (frame i x) -
        cov V x (cov (frame i) x (frame i x))) :
    frameBochnerWaveAt I cov sign frame V x =
      ∑ i, sign i • Hess (b i) (b i) := by
  unfold frameBochnerWaveAt
  apply Finset.sum_congr rfl
  intro i _
  rw [hHess i]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The existing frame Bochner expression satisfies the basis-independent
metric-trace specification whenever it represents one covariant Hessian. -/
lemma frameBochnerWaveAt_isMetricTraceAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ i, Hess (b i) (b i) =
      cov (firstCovariantSection I cov (frame i) V) x (frame i x) -
        cov V x (cov (frame i) x (frame i x))) :
    IsMetricTraceAt I g x Hess (frameBochnerWaveAt I cov sign frame V x) := by
  rw [frameBochnerWaveAt_eq_metricTraceSum I cov sign frame V x b Hess hHess]
  exact pseudoOrthonormalBasis_sum_isMetricTraceAt I g x sign b hb Hess

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A signed pseudo-orthonormal-frame Bochner sum computes the actual
basis-free metric trace of the represented covariant Hessian. -/
lemma frameBochnerWaveAt_eq_metricTraceAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ i, Hess (b i) (b i) =
      cov (firstCovariantSection I cov (frame i) V) x (frame i x) -
        cov V x (cov (frame i) x (frame i x))) :
    frameBochnerWaveAt I cov sign frame V x = metricTraceAt I g x Hess :=
  IsMetricTraceAt.unique I g x
    (frameBochnerWaveAt_isMetricTraceAt I g cov sign frame V x b hb Hess hHess)
    (metricTraceAt_isMetricTraceAt I g x Hess)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The repository's Bochner wave expression is independent of the chosen
pseudo-orthonormal frame when both frames represent the same covariant
Hessian at the point. -/
lemma frameBochnerWaveAt_independent {d e : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ) (sign' : Fin e → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (frame' : Fin e → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (b' : Basis (Fin e) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (hb' : IsPseudoOrthonormalBasisAt I g x sign' b')
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ i, Hess (b i) (b i) =
      cov (firstCovariantSection I cov (frame i) V) x (frame i x) -
        cov V x (cov (frame i) x (frame i x)))
    (hHess' : ∀ i, Hess (b' i) (b' i) =
      cov (firstCovariantSection I cov (frame' i) V) x (frame' i x) -
        cov V x (cov (frame' i) x (frame' i x))) :
    frameBochnerWaveAt I cov sign frame V x =
      frameBochnerWaveAt I cov sign' frame' V x := by
  apply IsMetricTraceAt.unique I g x
  · exact frameBochnerWaveAt_isMetricTraceAt I g cov sign frame V x b hb Hess hHess
  · exact frameBochnerWaveAt_isMetricTraceAt I g cov sign' frame' V x b' hb' Hess hHess'

/-- The intrinsic rough wave operator does not depend on the chosen
Levi-Civita atlas representative. -/
theorem leviCivitaAtlas_frameBochnerWave_overlap {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (hV : ∀ y, MDiffAt (T% V) y)
    (hframe : ∀ i y, MDiffAt (T% (frame i)) y)
    (hNablaFrame : ∀ i,
      MDiffAt (T% (firstCovariantSection I (cov b) (frame i) V)) x) :
    frameBochnerWaveAt I (cov a) sign frame V x =
      frameBochnerWaveAt I (cov b) sign frame V x := by
  unfold frameBochnerWaveAt
  apply Finset.sum_congr rfl
  intro i _
  have hsection := firstCovariantSection_atlas_eq I g cov hatlas a b
    (frame i) V (hframe i) hV
  have houter :
      cov a (firstCovariantSection I (cov b) (frame i) V) x (frame i x) =
        cov b (firstCovariantSection I (cov b) (frame i) V) x (frame i x) :=
    leviCivitaAtlas_overlap I g cov hatlas a b (frame i)
      (firstCovariantSection I (cov b) (frame i) V) x
      (hframe i x) (hNablaFrame i)
  have hdirection : cov a (frame i) x (frame i x) =
      cov b (frame i) x (frame i x) :=
    leviCivitaAtlas_overlap I g cov hatlas a b (frame i) (frame i) x
      (hframe i x) (hframe i x)
  let D : ∀ y : M, TangentSpace I y :=
    extend E (cov b (frame i) x (frame i x))
  have hD : MDiffAt (T% D) x :=
    mdifferentiableAt_extend I E (cov b (frame i) x (frame i x))
  have hDvalue : D x = cov b (frame i) x (frame i x) := by simp [D]
  have hcorrection :
      cov a V x (cov b (frame i) x (frame i x)) =
        cov b V x (cov b (frame i) x (frame i x)) := by
    have h := leviCivitaAtlas_overlap I g cov hatlas a b D V x hD (hV x)
    simpa [hDvalue] using h
  rw [hsection, houter, hdirection, hcorrection]

/-- Raise the frame Ricci contraction to a tangent vector using the same
pseudo-orthonormal frame. -/
def frameRaisedRicciActionAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  ∑ i, (sign i * frameRicciContractionAt I g cov sign frame V (frame i) x) •
    frame i x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A raised Ricci sum in a pseudo-orthonormal frame computes the
basis-independent sharp of the curvature trace covector. -/
lemma frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (hframe : ∀ i, b i = frame i x)
    (R : TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (hR : ∀ i j, R (b j) (b i) =
      manifoldCovariantCurvatureAction cov V (frame i) (frame j) x) :
    frameRaisedRicciActionAt I g cov sign frame V x =
      raisedCurvatureRicciAt I g x R := by
  let u := raisedCurvatureRicciAt I g x R
  rw [show raisedCurvatureRicciAt I g x R = u by rfl]
  rw [← b.sum_repr u]
  unfold frameRaisedRicciActionAt
  apply Finset.sum_congr rfl
  intro j _
  rw [← hframe j]
  congr 1
  rw [pseudoOrthonormalBasis_repr_eq_sign_mul_inner I g x sign b hb]
  rw [show g.val x u (b j) = curvatureRicciCovectorAt I x R (b j) by
    rw [g.symm]
    exact g.apply_vec_sharp x (b j) (curvatureRicciCovectorAt I x R)]
  rw [curvatureRicciCovectorAt]
  change sign j * frameRicciContractionAt I g cov sign frame V (frame j) x =
    sign j * LinearMap.trace ℝ (TangentSpace I x) (R (b j))
  congr 1
  exact frameRicciContractionAt_eq_curvatureRicciTraceAt I g cov sign frame
    V (frame j) x b hb hframe (R (b j)) (hR · j)

/-- The raised Ricci action is independent of the Levi-Civita atlas
representative. -/
theorem leviCivitaAtlas_frameRaisedRicci_overlap {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) (x : M)
    (hV : ∀ y, MDiffAt (T% V) y)
    (hframe : ∀ i y, MDiffAt (T% (frame i)) y)
    (hNablaFrame : ∀ i,
      MDiffAt (T% (firstCovariantSection I (cov b) (frame i) V)) x)
    (hbracket : ∀ i j,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    frameRaisedRicciActionAt I g (cov a) sign frame V x =
      frameRaisedRicciActionAt I g (cov b) sign frame V x := by
  unfold frameRaisedRicciActionAt
  apply Finset.sum_congr rfl
  intro j _
  rw [leviCivitaAtlas_frameRicci_overlap I g cov hatlas a b sign frame V
    (frame j) x hV (hframe j) hframe (hNablaFrame j) hNablaFrame
    (fun i => hbracket i j)]

/-! ## Frame-free intrinsic Maxwell equation -/

/-- The Ricci-coupled Maxwell equation at a point, expressed only through
tensor contractions: the metric trace of the covariant Hessian minus the
raised linear trace of the curvature endomorphism equals the source. -/
def TensorRicciCoupledMaxwellAt
    (g : PseudoRiemannianMetric E H M n I) (x : M)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (R : TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (J : TangentSpace I x) : Prop :=
  metricTraceAt I g x Hess - raisedCurvatureRicciAt I g x R = J

/-- The frame-free Ricci-coupled Maxwell equation imposed at every manifold
point. The dependent families `Hess` and `R` are the intrinsic Hessian and
curvature-endomorphism data of the field. -/
def TensorRicciCoupledMaxwellOn
    (g : PseudoRiemannianMetric E H M n I)
    (Hess : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (R : ∀ x : M, TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (J : ∀ x : M, TangentSpace I x) : Prop :=
  ∀ x, TensorRicciCoupledMaxwellAt I g x (Hess x) (R x) (J x)

/-- Restrict the frame-free intrinsic Maxwell equation to one chart source. -/
def TensorRicciCoupledMaxwellOnChart
    (g : PseudoRiemannianMetric E H M n I) (s : Set M)
    (Hess : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (R : ∀ x : M, TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (J : ∀ x : M, TangentSpace I x) : Prop :=
  ∀ x, x ∈ s → TensorRicciCoupledMaxwellAt I g x (Hess x) (R x) (J x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- A frame-free intrinsic equation is global exactly when it holds on every
member of an actual cover. This is the atlas-level local-to-global statement;
it uses only coverage and therefore cannot hide coordinate-transition
assumptions. -/
lemma tensorRicciCoupledMaxwellOn_iff_onChart_of_cover {a : Type*}
    (g : PseudoRiemannianMetric E H M n I) (s : a → Set M)
    (hcover : ⋃ i, s i = Set.univ)
    (Hess : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (R : ∀ x : M, TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (J : ∀ x : M, TangentSpace I x) :
    TensorRicciCoupledMaxwellOn I g Hess R J ↔
      ∀ i, TensorRicciCoupledMaxwellOnChart I g (s i) Hess R J := by
  constructor
  · intro h i x _
    exact h x
  · intro h x
    have hx : x ∈ ⋃ i, s i := by rw [hcover]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact h i x hi

/-- The intrinsic Lorenz-gauge Ricci-coupled Maxwell wave equation at a
manifold point.  This is a geometric PDE identity; no Cauchy well-posedness or
Green-hyperbolicity claim is included. -/
def IntrinsicRicciCoupledMaxwellAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x) (x : M) : Prop :=
  frameBochnerWaveAt I cov sign frame V x -
      frameRaisedRicciActionAt I g cov sign frame V x = J x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A pseudo-orthonormal-frame expression is exactly the frame-free tensor
equation whenever the supplied bilinear map and curvature family represent
the covariant Hessian and curvature action on that basis. -/
lemma intrinsicRicciCoupledMaxwellAt_iff_tensor {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : IsPseudoOrthonormalBasisAt I g x sign b)
    (hframe : ∀ i, b i = frame i x)
    (Hess : TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ i, Hess (b i) (b i) =
      cov (firstCovariantSection I cov (frame i) V) x (frame i x) -
        cov V x (cov (frame i) x (frame i x)))
    (R : TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (hR : ∀ i j, R (b j) (b i) =
      manifoldCovariantCurvatureAction cov V (frame i) (frame j) x) :
    IntrinsicRicciCoupledMaxwellAt I g cov sign frame V J x ↔
      TensorRicciCoupledMaxwellAt I g x Hess R (J x) := by
  unfold IntrinsicRicciCoupledMaxwellAt TensorRicciCoupledMaxwellAt
  rw [frameBochnerWaveAt_eq_metricTraceAt I g cov sign frame V x b hb Hess hHess]
  rw [frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt I g cov sign frame
    V x b hb hframe R hR]

/-- **Global coordinate independence of the curved Maxwell wave equation.**
For a Levi-Civita atlas, the intrinsic Ricci-coupled equation holds for one
representative exactly when it holds for any other representative. -/
theorem intrinsicRicciCoupledMaxwellAt_atlas_iff {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x) (x : M)
    (hV : ∀ y, MDiffAt (T% V) y)
    (hframe : ∀ i y, MDiffAt (T% (frame i)) y)
    (hNablaFrame : ∀ i,
      MDiffAt (T% (firstCovariantSection I (cov b) (frame i) V)) x)
    (hbracket : ∀ i j,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    IntrinsicRicciCoupledMaxwellAt I g (cov a) sign frame V J x ↔
      IntrinsicRicciCoupledMaxwellAt I g (cov b) sign frame V J x := by
  unfold IntrinsicRicciCoupledMaxwellAt
  rw [leviCivitaAtlas_frameBochnerWave_overlap I g cov hatlas a b sign frame V x
    hV hframe hNablaFrame]
  rw [leviCivitaAtlas_frameRaisedRicci_overlap I g cov hatlas a b sign frame V x
    hV hframe hNablaFrame hbracket]

/-! ## Global intrinsic Maxwell evolution identity -/

/-- The intrinsic Ricci-coupled Maxwell wave equation imposed at every point
of the manifold. This is the global geometric equation, not a claim of Cauchy
existence or Green-hyperbolicity. -/
def IntrinsicRicciCoupledMaxwellOn {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x) : Prop :=
  ∀ x, IntrinsicRicciCoupledMaxwellAt I g cov sign frame V J x

/-- The global intrinsic Maxwell equation is independent of the chosen
representative of a Levi-Civita atlas. -/
theorem intrinsicRicciCoupledMaxwellOn_atlas_iff {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x)
    (hV : ∀ x, MDiffAt (T% V) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x,
      MDiffAt (T% (firstCovariantSection I (cov b) (frame i) V)) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    IntrinsicRicciCoupledMaxwellOn I g (cov a) sign frame V J ↔
      IntrinsicRicciCoupledMaxwellOn I g (cov b) sign frame V J := by
  constructor
  · intro h x
    exact (intrinsicRicciCoupledMaxwellAt_atlas_iff I g cov hatlas a b sign
      frame V J x hV hframe (fun i => hNablaFrame i x)
      (fun i j => hbracket i j x)).mp (h x)
  · intro h x
    exact (intrinsicRicciCoupledMaxwellAt_atlas_iff I g cov hatlas a b sign
      frame V J x hV hframe (fun i => hNablaFrame i x)
      (fun i j => hbracket i j x)).mpr (h x)

/-- Global intrinsic Maxwell evolution obtained from independently chosen
local Levi-Civita atlases is the same equation. The regularity premise for the
iterated derivative is stated for the second selected connection. -/
theorem localLeviCivitaAtlas_intrinsicMaxwellOn_iff {d : ℕ} {α β : Type*}
    (g : PseudoRiemannianMetric E H M n I)
    (D : LocalLeviCivitaAtlasData I g α)
    (D' : LocalLeviCivitaAtlasData I g β)
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x)
    (hV : ∀ x, MDiffAt (T% V) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (D'.covariantDerivative (I := I))
        (frame i) V)) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    IntrinsicRicciCoupledMaxwellOn I g (D.covariantDerivative (I := I))
        sign frame V J ↔
      IntrinsicRicciCoupledMaxwellOn I g (D'.covariantDerivative (I := I))
        sign frame V J := by
  let cov : Bool → CovariantDerivative I E (TangentSpace I : M → Type _) :=
    fun q => if q then D.covariantDerivative (I := I)
      else D'.covariantDerivative (I := I)
  have hatlas : IsLeviCivitaAtlas I g cov := by
    intro q
    cases q
    · simpa [cov] using D'.covariantDerivative_isLeviCivita (I := I)
    · simpa [cov] using D.covariantDerivative_isLeviCivita (I := I)
  simpa [cov] using
    intrinsicRicciCoupledMaxwellOn_atlas_iff I g cov hatlas true false sign
      frame V J hV hframe hNablaFrame hbracket

/-! ## Global Green-operator realization -/

/-- The global intrinsic Ricci-coupled Maxwell wave expression as a tangent
vector field. This is the operator whose equation against `J` is represented
by `IntrinsicRicciCoupledMaxwellOn`. -/
def intrinsicRicciCoupledMaxwellOperator {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V : ∀ x : M, TangentSpace I x) : ∀ x : M, TangentSpace I x :=
  fun x => frameBochnerWaveAt I cov sign frame V x -
    frameRaisedRicciActionAt I g cov sign frame V x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The global intrinsic Maxwell predicate is exactly equality of the global
geometric wave expression with the source field. -/
lemma intrinsicRicciCoupledMaxwellOn_iff_operator_eq {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (V J : ∀ x : M, TangentSpace I x) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame V J ↔
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame V = J := by
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- Analytic Green data for the intrinsic Maxwell wave operator, separating
the source carrier `𝓢` from the propagated-field carrier `𝓕`. These carriers
can encode compact support, smoothness, boundary conditions, or Sobolev
completions. Green right-inversion and retarded-sector injectivity are the
explicit global analytic inputs. -/
structure IntrinsicMaxwellGreenData {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (𝓢 𝓕 : Type*)
    [AddCommGroup 𝓢] [Module ℝ 𝓢]
    [AddCommGroup 𝓕] [Module ℝ 𝓕] where
  /-- Realization of a propagated field as a tangent vector field. -/
  realizeField : 𝓕 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  /-- Realization of a source as a tangent vector field. -/
  realizeSource : 𝓢 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  /-- Distinct analytic sources have distinct tangent-field realizations. -/
  realizeSource_injective : Function.Injective realizeSource
  /-- The analytic Maxwell wave operator. -/
  waveOperator : 𝓕 →ₗ[ℝ] 𝓢
  /-- The retarded Green operator. -/
  retarded : 𝓢 →ₗ[ℝ] 𝓕
  /-- The advanced Green operator. -/
  advanced : 𝓢 →ₗ[ℝ] 𝓕
  /-- The analytic operator realizes the intrinsic geometric expression. -/
  realizes_wave : ∀ u,
    realizeSource (waveOperator u) =
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame (realizeField u)
  /-- The retarded operator is a right inverse of the wave operator. -/
  wave_retarded : Function.RightInverse retarded waveOperator
  /-- The advanced operator is a right inverse of the wave operator. -/
  wave_advanced : Function.RightInverse advanced waveOperator
  /-- The subspace carrying the retarded support or boundary condition. -/
  retardedSector : Submodule ℝ 𝓕
  /-- Retarded Green solutions lie in the retarded sector. -/
  retarded_mem : ∀ source, retarded source ∈ retardedSector
  /-- The wave operator is injective after imposing the retarded condition. -/
  wave_injectiveOn_retarded : Set.InjOn waveOperator retardedSector

/-- Well-posed causal Cauchy data for the intrinsic Maxwell wave operator.

Unlike `IntrinsicMaxwellGreenData`, this structure does not assume that the
retarded and advanced solution selectors are linear.  It records existence,
the wave equation, causal support sectors, and uniqueness in those sectors.
Linearity of both Green operators is then a theorem.  A globally hyperbolic
PDE existence theorem supplies precisely this interface; pseudo-Riemannian
geometry by itself does not. -/
structure WellPosedIntrinsicMaxwellCauchyData {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (𝒮 𝒯 : Type*)
    [AddCommGroup 𝒮] [Module ℝ 𝒮]
    [AddCommGroup 𝒯] [Module ℝ 𝒯] where
  /-- Realization of an analytic field as a tangent vector field. -/
  realizeField : 𝒯 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  /-- Realization of an analytic source as a tangent vector field. -/
  realizeSource : 𝒮 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  /-- Source realization is faithful. -/
  realizeSource_injective : Function.Injective realizeSource
  /-- The analytic realization of the intrinsic Maxwell wave operator. -/
  waveOperator : 𝒯 →ₗ[ℝ] 𝒮
  /-- Chosen retarded solution supplied by causal Cauchy well-posedness. -/
  retardedSolution : 𝒮 → 𝒯
  /-- Chosen advanced solution supplied by causal Cauchy well-posedness. -/
  advancedSolution : 𝒮 → 𝒯
  /-- The analytic wave operator realizes the intrinsic geometric expression. -/
  realizes_wave : ∀ u,
    realizeSource (waveOperator u) =
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame (realizeField u)
  /-- Every chosen retarded solution solves the sourced equation. -/
  wave_retarded : Function.RightInverse retardedSolution waveOperator
  /-- Every chosen advanced solution solves the sourced equation. -/
  wave_advanced : Function.RightInverse advancedSolution waveOperator
  /-- The subspace encoding retarded causal support and boundary conditions. -/
  retardedSector : Submodule ℝ 𝒯
  /-- The subspace encoding advanced causal support and boundary conditions. -/
  advancedSector : Submodule ℝ 𝒯
  /-- Retarded solutions have retarded causal support. -/
  retarded_mem : ∀ source, retardedSolution source ∈ retardedSector
  /-- Advanced solutions have advanced causal support. -/
  advanced_mem : ∀ source, advancedSolution source ∈ advancedSector
  /-- The sourced equation has at most one retarded solution. -/
  wave_injectiveOn_retarded : Set.InjOn waveOperator retardedSector
  /-- The sourced equation has at most one advanced solution. -/
  wave_injectiveOn_advanced : Set.InjOn waveOperator advancedSector

namespace WellPosedIntrinsicMaxwellCauchyData

variable {d : ℕ} {𝒮 𝒯 : Type*}
variable [AddCommGroup 𝒮] [Module ℝ 𝒮]
variable [AddCommGroup 𝒯] [Module ℝ 𝒯]
variable {g : PseudoRiemannianMetric E H M n I}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {sign : Fin d → ℝ}
variable {frame : Fin d → ∀ x : M, TangentSpace I x}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Causal existence and uniqueness force the retarded solution selector to
preserve addition. -/
lemma retardedSolution_add
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯)
    (source₁ source₂ : 𝒮) :
    D.retardedSolution (source₁ + source₂) =
      D.retardedSolution source₁ + D.retardedSolution source₂ := by
  apply D.wave_injectiveOn_retarded
  · exact D.retarded_mem _
  · exact D.retardedSector.add_mem (D.retarded_mem _) (D.retarded_mem _)
  · rw [D.wave_retarded, map_add, D.wave_retarded, D.wave_retarded]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Causal existence and uniqueness force the retarded solution selector to
preserve real scalar multiplication. -/
lemma retardedSolution_smul
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯)
    (r : ℝ) (source : 𝒮) :
    D.retardedSolution (r • source) = r • D.retardedSolution source := by
  apply D.wave_injectiveOn_retarded
  · exact D.retarded_mem _
  · exact D.retardedSector.smul_mem r (D.retarded_mem _)
  · rw [D.wave_retarded, map_smul, D.wave_retarded]

/-- The intrinsic retarded Green operator derived from causal Cauchy
existence and uniqueness. -/
def retarded
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →ₗ[ℝ] 𝒯 where
  toFun := D.retardedSolution
  map_add' := D.retardedSolution_add
  map_smul' := D.retardedSolution_smul

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Causal existence and uniqueness force the advanced solution selector to
preserve addition. -/
lemma advancedSolution_add
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯)
    (source₁ source₂ : 𝒮) :
    D.advancedSolution (source₁ + source₂) =
      D.advancedSolution source₁ + D.advancedSolution source₂ := by
  apply D.wave_injectiveOn_advanced
  · exact D.advanced_mem _
  · exact D.advancedSector.add_mem (D.advanced_mem _) (D.advanced_mem _)
  · rw [D.wave_advanced, map_add, D.wave_advanced, D.wave_advanced]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Causal existence and uniqueness force the advanced solution selector to
preserve real scalar multiplication. -/
lemma advancedSolution_smul
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯)
    (r : ℝ) (source : 𝒮) :
    D.advancedSolution (r • source) = r • D.advancedSolution source := by
  apply D.wave_injectiveOn_advanced
  · exact D.advanced_mem _
  · exact D.advancedSector.smul_mem r (D.advanced_mem _)
  · rw [D.wave_advanced, map_smul, D.wave_advanced]

/-- The intrinsic advanced Green operator derived from causal Cauchy
existence and uniqueness. -/
def advanced
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →ₗ[ℝ] 𝒯 where
  toFun := D.advancedSolution
  map_add' := D.advancedSolution_add
  map_smul' := D.advancedSolution_smul

/-- Package the Green operators proved linear from causal Cauchy
well-posedness into the repository's intrinsic Maxwell Green interface. -/
def toIntrinsicMaxwellGreenData
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯) :
    IntrinsicMaxwellGreenData I g cov sign frame 𝒮 𝒯 where
  realizeField := D.realizeField
  realizeSource := D.realizeSource
  realizeSource_injective := D.realizeSource_injective
  waveOperator := D.waveOperator
  retarded := D.retarded
  advanced := D.advanced
  realizes_wave := D.realizes_wave
  wave_retarded := D.wave_retarded
  wave_advanced := D.wave_advanced
  retardedSector := D.retardedSector
  retarded_mem := D.retarded_mem
  wave_injectiveOn_retarded := D.wave_injectiveOn_retarded

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma toIntrinsicMaxwellGreenData_retarded_apply
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.toIntrinsicMaxwellGreenData.retarded source = D.retardedSolution source := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma toIntrinsicMaxwellGreenData_advanced_apply
    (D : WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.toIntrinsicMaxwellGreenData.advanced source = D.advancedSolution source := rfl

end WellPosedIntrinsicMaxwellCauchyData

namespace IntrinsicMaxwellGreenData

variable {d : ℕ} {𝓢 𝓕 : Type*}
variable [AddCommGroup 𝓢] [Module ℝ 𝓢]
variable [AddCommGroup 𝓕] [Module ℝ 𝓕]
variable {g : PseudoRiemannianMetric E H M n I}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {sign : Fin d → ℝ}
variable {frame : Fin d → ∀ x : M, TangentSpace I x}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Applying the retarded Green operator to a source produces a global
solution of the intrinsic curved Maxwell wave equation. -/
lemma retarded_solves
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) (source : 𝓢) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
      (G.realizeField (G.retarded source)) (G.realizeSource source) := by
  rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
  calc
    intrinsicRicciCoupledMaxwellOperator I g cov sign frame
        (G.realizeField (G.retarded source)) =
        G.realizeSource (G.waveOperator (G.retarded source)) :=
      (G.realizes_wave (G.retarded source)).symm
    _ = G.realizeSource source :=
      congrArg G.realizeSource (G.wave_retarded source)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A conditional retarded Green solution also solves the frame-free tensor
Maxwell equation whenever the supplied Hessian and curvature families realize
that solution's covariant Hessian and curvature action. The Green datum, rather
than pseudo-Riemannian geometry alone, supplies causal evolution. -/
lemma retarded_solves_tensor
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) (source : 𝓢)
    (b : ∀ x, Basis (Fin d) ℝ (TangentSpace I x))
    (hb : ∀ x, IsPseudoOrthonormalBasisAt I g x sign (b x))
    (hframe : ∀ x i, b x i = frame i x)
    (Hess : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ x i, Hess x (b x i) (b x i) =
      cov (firstCovariantSection I cov (frame i)
        (G.realizeField (G.retarded source))) x (frame i x) -
      cov (G.realizeField (G.retarded source)) x
        (cov (frame i) x (frame i x)))
    (R : ∀ x : M, TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (hR : ∀ x i j, R x (b x j) (b x i) =
      manifoldCovariantCurvatureAction cov
        (G.realizeField (G.retarded source)) (frame i) (frame j) x) :
    TensorRicciCoupledMaxwellOn I g Hess R (G.realizeSource source) := by
  intro x
  unfold TensorRicciCoupledMaxwellAt
  rw [← frameBochnerWaveAt_eq_metricTraceAt I g cov sign frame
    (G.realizeField (G.retarded source)) x (b x) (hb x) (Hess x) (hHess x)]
  rw [← frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt I g cov sign frame
    (G.realizeField (G.retarded source)) x (b x) (hb x) (hframe x) (R x) (hR x)]
  exact retarded_solves I G source x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Applying the advanced Green operator to a source produces a global
solution of the same intrinsic curved Maxwell wave equation. -/
lemma advanced_solves
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) (source : 𝓢) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
      (G.realizeField (G.advanced source)) (G.realizeSource source) := by
  rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
  calc
    intrinsicRicciCoupledMaxwellOperator I g cov sign frame
        (G.realizeField (G.advanced source)) =
        G.realizeSource (G.waveOperator (G.advanced source)) :=
      (G.realizes_wave (G.advanced source)).symm
    _ = G.realizeSource source :=
      congrArg G.realizeSource (G.wave_advanced source)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Within the selected retarded sector, the retarded Green field is the
unique solution with the chosen source. -/
lemma eq_retarded_of_solves
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕)
    (u : 𝓕) (source : 𝓢) (hu : u ∈ G.retardedSector)
    (h : IntrinsicRicciCoupledMaxwellOn I g cov sign frame
      (G.realizeField u) (G.realizeSource source)) :
    u = G.retarded source := by
  have hop : intrinsicRicciCoupledMaxwellOperator I g cov sign frame
      (G.realizeField u) = G.realizeSource source :=
    (intrinsicRicciCoupledMaxwellOn_iff_operator_eq I g cov sign frame
      (G.realizeField u) (G.realizeSource source)).mp h
  have hP : G.waveOperator u = source := G.realizeSource_injective <| by
    rw [G.realizes_wave]
    exact hop
  exact G.wave_injectiveOn_retarded hu (G.retarded_mem source) <| by
    rw [hP, G.wave_retarded source]

/-- The causal propagator is the difference of retarded and advanced Green
operators, matching the Pauli--Jordan construction at operator level. -/
def causalPropagator
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) : 𝓢 →ₗ[ℝ] 𝓕 :=
  G.retarded - G.advanced

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The causal propagator sends every source to a homogeneous Maxwell wave. -/
lemma waveOperator_causalPropagator_eq_zero
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) (source : 𝓢) :
    G.waveOperator (causalPropagator I G source) = 0 := by
  rw [causalPropagator, LinearMap.sub_apply, map_sub,
    G.wave_retarded source, G.wave_advanced source, sub_self]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The retarded-minus-advanced Maxwell propagator is an intrinsic global
homogeneous solution. This promotes the analytic kernel identity above to the
coordinate-free geometric equation on the manifold. -/
lemma causalPropagator_solves_homogeneous
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) (source : 𝓢) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
      (G.realizeField (causalPropagator I G source)) 0 := by
  rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
  calc
    intrinsicRicciCoupledMaxwellOperator I g cov sign frame
        (G.realizeField (causalPropagator I G source)) =
        G.realizeSource (G.waveOperator (causalPropagator I G source)) :=
      (G.realizes_wave (causalPropagator I G source)).symm
    _ = G.realizeSource 0 := by rw [waveOperator_causalPropagator_eq_zero]
    _ = 0 := map_zero G.realizeSource

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The causal Maxwell propagator satisfies the genuinely frame-free tensor
equation whenever the supplied Hessian and curvature endomorphisms realize
its intrinsic covariant derivatives. This is the tensorial Pauli--Jordan
counterpart of `retarded_solves_tensor`. -/
lemma causalPropagator_solves_tensor_homogeneous
    (G : IntrinsicMaxwellGreenData I g cov sign frame 𝓢 𝓕) (source : 𝓢)
    (b : ∀ x, Basis (Fin d) ℝ (TangentSpace I x))
    (hb : ∀ x, IsPseudoOrthonormalBasisAt I g x sign (b x))
    (hframe : ∀ x i, b x i = frame i x)
    (Hess : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x)
    (hHess : ∀ x i, Hess x (b x i) (b x i) =
      cov (firstCovariantSection I cov (frame i)
        (G.realizeField (causalPropagator I G source))) x (frame i x) -
      cov (G.realizeField (causalPropagator I G source)) x
        (cov (frame i) x (frame i x)))
    (R : ∀ x : M, TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (hR : ∀ x i j, R x (b x j) (b x i) =
      manifoldCovariantCurvatureAction cov
        (G.realizeField (causalPropagator I G source))
        (frame i) (frame j) x) :
    TensorRicciCoupledMaxwellOn I g Hess R 0 := by
  intro x
  exact (intrinsicRicciCoupledMaxwellAt_iff_tensor I g cov sign frame
    (G.realizeField (causalPropagator I G source)) 0 x (b x) (hb x)
    (hframe x) (Hess x) (hHess x) (R x) (hR x)).mp
      (causalPropagator_solves_homogeneous I G source x)

/-- A retarded solution constructed for one representative of a Levi-Civita
atlas solves the same global intrinsic Maxwell equation for every other
representative, under the regularity needed by curvature comparison. -/
lemma retarded_solves_for_leviCivitaAtlas {α : Type*}
    (covAtlas : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g covAtlas) (a b : α)
    (G : IntrinsicMaxwellGreenData I g (covAtlas b) sign frame 𝓢 𝓕)
    (source : 𝓢)
    (hV : ∀ x, MDiffAt (T% (G.realizeField (G.retarded source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x,
      MDiffAt (T% (firstCovariantSection I (covAtlas b) (frame i)
        (G.realizeField (G.retarded source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    IntrinsicRicciCoupledMaxwellOn I g (covAtlas a) sign frame
      (G.realizeField (G.retarded source)) (G.realizeSource source) := by
  exact (intrinsicRicciCoupledMaxwellOn_atlas_iff I g covAtlas hatlas a b sign
    frame (G.realizeField (G.retarded source)) (G.realizeSource source)
    hV hframe hNablaFrame hbracket).mpr (retarded_solves I G source)

/-- A Green operator built from the global connection selected by one local
Levi-Civita atlas solves the same intrinsic Maxwell equation for the global
connection selected by any other local atlas. This is the causal-evolution
capstone of atlas independence: the analytic Green datum remains an explicit
premise, while no chart or pointwise selection survives in the conclusion. -/
lemma retarded_solves_for_localLeviCivitaAtlas {α β : Type*}
    (D : LocalLeviCivitaAtlasData I g α)
    (D' : LocalLeviCivitaAtlasData I g β)
    (G : IntrinsicMaxwellGreenData I g
      (D'.covariantDerivative (I := I)) sign frame 𝓢 𝓕)
    (source : 𝓢)
    (hV : ∀ x, MDiffAt (T% (G.realizeField (G.retarded source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (D'.covariantDerivative (I := I))
        (frame i) (G.realizeField (G.retarded source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    IntrinsicRicciCoupledMaxwellOn I g (D.covariantDerivative (I := I))
      sign frame (G.realizeField (G.retarded source))
      (G.realizeSource source) := by
  exact (localLeviCivitaAtlas_intrinsicMaxwellOn_iff I g D D' sign frame
    (G.realizeField (G.retarded source)) (G.realizeSource source)
    hV hframe hNablaFrame hbracket).mpr (retarded_solves I G source)

/-- The Pauli--Jordan/causal Maxwell field constructed using one global
Levi-Civita representative is a homogeneous intrinsic solution for every
other representative obtained from compatible local atlases. -/
lemma causalPropagator_solves_homogeneous_for_localLeviCivitaAtlas
    {α β : Type*}
    (D : LocalLeviCivitaAtlasData I g α)
    (D' : LocalLeviCivitaAtlasData I g β)
    (G : IntrinsicMaxwellGreenData I g
      (D'.covariantDerivative (I := I)) sign frame 𝓢 𝓕)
    (source : 𝓢)
    (hV : ∀ x, MDiffAt
      (T% (G.realizeField (causalPropagator I G source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (D'.covariantDerivative (I := I))
        (frame i) (G.realizeField (causalPropagator I G source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    IntrinsicRicciCoupledMaxwellOn I g (D.covariantDerivative (I := I))
      sign frame (G.realizeField (causalPropagator I G source)) 0 := by
  exact (localLeviCivitaAtlas_intrinsicMaxwellOn_iff I g D D' sign frame
    (G.realizeField (causalPropagator I G source)) 0
    hV hframe hNablaFrame hbracket).mpr
      (causalPropagator_solves_homogeneous I G source)

end IntrinsicMaxwellGreenData

end PseudoRiemannianMetric

end
