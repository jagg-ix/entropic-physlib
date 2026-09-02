/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.VolumeMeasure
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Curvature
public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
public import Mathlib.Analysis.Calculus.ParametricIntegral
meta import Zil

/-!
# Global Einstein--Hilbert action

This module closes the gap between the existing chartwise Palatini
variation and a continuum, atlas-independent action:

* scalar curvature is the linear trace of the raised Ricci endomorphism;
* certified pseudo-orthonormal frame sums compute that trace and are
  therefore frame independent;
* Levi-Civita atlas representatives give the same scalar;
* the action is integrated against the metric-built Lorentzian measure;
* the shared curved path-integral interface uses exactly that measure;
* a dominated pointwise Palatini derivative passes through the continuum
  integral, and an almost-everywhere zero bulk derivative gives stationarity.

No Newton constant occurs in the geometric action carrier.  Coupling
normalizations belong to the downstream complex Einstein equations.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle FiberBundle Module MeasureTheory Set Filter
open scoped Manifold Topology

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction

universe v w

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [MeasurableSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Scalar curvature is the basis-independent trace of the raised Ricci
endomorphism. -/
def intrinsicScalarCurvatureAt (x : M)
    (RicSharp : TangentSpace I x →ₗ[ℝ] TangentSpace I x) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) RicSharp

/-- Scalar curvature written in a pseudo-orthonormal frame. -/
def frameScalarCurvatureAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (x : M) : ℝ :=
  ∑ j, sign j *
    PseudoRiemannianMetric.frameRicciContractionAt
      I g cov sign frame (frame j) (frame j) x

/-- The signed frame scalar is exactly the linear trace of the represented
raised Ricci endomorphism. -/
@[zil_level bridge_theorem]
lemma frameScalarCurvatureAt_eq_intrinsicScalarCurvatureAt {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (hb : PseudoRiemannianMetric.IsPseudoOrthonormalBasisAt I g x sign b)
    (hframe : ∀ i, b i = frame i x)
    (RicSharp : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hRic : ∀ j, RicSharp (b j) =
      PseudoRiemannianMetric.frameRaisedRicciActionAt
        I g cov sign frame (frame j) x) :
    frameScalarCurvatureAt I g cov sign frame x =
      intrinsicScalarCurvatureAt I x RicSharp := by
  rw [intrinsicScalarCurvatureAt, LinearMap.trace_eq_matrix_trace ℝ b,
    Matrix.trace]
  unfold frameScalarCurvatureAt
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [PseudoRiemannianMetric.pseudoOrthonormalBasis_repr_eq_sign_mul_inner
    I g x sign b hb]
  rw [hRic j]
  unfold PseudoRiemannianMetric.frameRaisedRicciActionAt
  rw [map_sum]
  rw [_root_.sum_apply]
  simp only [map_smul, smul_apply]
  simp_rw [← hframe]
  rw [Finset.sum_eq_single j]
  · rw [hb.1 j j, if_pos rfl]
    simp only [smul_eq_mul]
    calc
      sign j * PseudoRiemannianMetric.frameRicciContractionAt I g cov sign frame
          (frame j) (frame j) x =
          (sign j * sign j) *
            (sign j * PseudoRiemannianMetric.frameRicciContractionAt I g cov sign frame
              (frame j) (frame j) x) := by rw [hb.2 j]; ring
      _ = sign j *
          (sign j * PseudoRiemannianMetric.frameRicciContractionAt I g cov sign frame
            (frame j) (frame j) x * sign j) := by ring
  · intro i _ hij
    rw [hb.1 i j, if_neg hij]
    ring
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Frame independence follows because every valid frame computes the same
linear trace. -/
@[zil_level bridge_theorem]
lemma frameScalarCurvatureAt_independent {d e : ℕ}
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ) (sign' : Fin e → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (frame' : Fin e → ∀ x : M, TangentSpace I x)
    (x : M)
    (b : Basis (Fin d) ℝ (TangentSpace I x))
    (b' : Basis (Fin e) ℝ (TangentSpace I x))
    (hb : PseudoRiemannianMetric.IsPseudoOrthonormalBasisAt I g x sign b)
    (hb' : PseudoRiemannianMetric.IsPseudoOrthonormalBasisAt I g x sign' b')
    (hframe : ∀ i, b i = frame i x)
    (hframe' : ∀ i, b' i = frame' i x)
    (RicSharp : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hRic : ∀ j, RicSharp (b j) =
      PseudoRiemannianMetric.frameRaisedRicciActionAt
        I g cov sign frame (frame j) x)
    (hRic' : ∀ j, RicSharp (b' j) =
      PseudoRiemannianMetric.frameRaisedRicciActionAt
        I g cov sign' frame' (frame' j) x) :
    frameScalarCurvatureAt I g cov sign frame x =
      frameScalarCurvatureAt I g cov sign' frame' x := by
  rw [frameScalarCurvatureAt_eq_intrinsicScalarCurvatureAt
    I g cov sign frame x b hb hframe RicSharp hRic]
  rw [frameScalarCurvatureAt_eq_intrinsicScalarCurvatureAt
    I g cov sign' frame' x b' hb' hframe' RicSharp hRic']

/-- Scalar curvature is independent of the Levi-Civita atlas
representative. -/
@[zil_level bridge_theorem]
theorem frameScalarCurvatureAt_atlas_eq {d : ℕ}
    (g : PseudoRiemannianMetric E H M n I) {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : PseudoRiemannianMetric.IsLeviCivitaAtlas I g cov)
    (a b : α) (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x) (x : M)
    (hframe : ∀ i y, MDiffAt (T% (frame i)) y)
    (hNabla : ∀ i j,
      MDiffAt
        (T% (PseudoRiemannianMetric.firstCovariantSection
          I (cov b) (frame i) (frame j))) x)
    (hbracket : ∀ i j,
      MDiffAt
        (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    frameScalarCurvatureAt I g (cov a) sign frame x =
      frameScalarCurvatureAt I g (cov b) sign frame x := by
  unfold frameScalarCurvatureAt
  apply Finset.sum_congr rfl
  intro j _
  rw [PseudoRiemannianMetric.leviCivitaAtlas_frameRicci_overlap
    I g cov hatlas a b sign frame (frame j) (frame j) x
    (hframe j) (hframe j) hframe
    (hNabla j j) (fun i => hNabla i j)
    (fun i => hbracket i j)]

section CanonicalMeasure

variable {E M : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
variable [IsManifold 𝓘(ℝ, E) 2 M]
variable [IsManifold 𝓘(ℝ, E) (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x)]
variable [T2Space M] [SigmaCompactSpace M]

/-- The intrinsic Einstein--Hilbert action integrated against the canonical
metric-built Lorentzian measure. -/
def canonicalEinsteinHilbertAction
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (RicSharp : ∀ x : M,
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  ∫ x, intrinsicScalarCurvatureAt 𝓘(ℝ, E) x (RicSharp x)
    ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure g)

/-- The frame expression integrated against the same canonical metric
measure. -/
def canonicalFrameEinsteinHilbertAction {d : ℕ}
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (cov : CovariantDerivative 𝓘(ℝ, E) E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  ∫ x, frameScalarCurvatureAt 𝓘(ℝ, E) g cov sign frame x
    ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure g)

/-- The coordinate-frame Einstein--Hilbert action equals the intrinsic
trace action when the supplied raised Ricci endomorphism represents that
frame pointwise. -/
@[zil_level physical_theorem]
theorem canonicalFrameEinsteinHilbertAction_eq_intrinsic {d : ℕ}
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (cov : CovariantDerivative 𝓘(ℝ, E) E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (RicSharp : ∀ x : M,
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
    (basis : ∀ x : M, Basis (Fin d) ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hbasis : ∀ x,
      PseudoRiemannianMetric.IsPseudoOrthonormalBasisAt
        𝓘(ℝ, E) g x sign (basis x))
    (hframe : ∀ x i, basis x i = frame i x)
    (hRic : ∀ x j, RicSharp x (basis x j) =
      PseudoRiemannianMetric.frameRaisedRicciActionAt
        𝓘(ℝ, E) g cov sign frame (frame j) x) :
    canonicalFrameEinsteinHilbertAction g cov sign frame =
      canonicalEinsteinHilbertAction g RicSharp := by
  unfold canonicalFrameEinsteinHilbertAction canonicalEinsteinHilbertAction
  apply integral_congr_ae
  filter_upwards with x
  exact frameScalarCurvatureAt_eq_intrinsicScalarCurvatureAt
    𝓘(ℝ, E) g cov sign frame x (basis x) (hbasis x)
      (hframe x) (RicSharp x) (hRic x)

/-- Install the metric-built Lorentzian measure in the shared curved
path-integral interface without a second density factor. -/
def canonicalLorentzianCurvedMeasureDatum
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) :
    Physlib.QFT.PathIntegral.CurvedMeasureDatum M where
  baseMeasure := PseudoRiemannianMetric.lorentzianVolumeMeasure g
  volumeDensity := fun _ => 1
  measurable_volumeDensity := measurable_const
  volumeDensity_nonneg := fun _ => zero_le_one

/-- The shared path-integral wrapper recovers exactly the metric-built
Lorentzian measure. -/
@[zil_level bridge_theorem]
lemma canonicalLorentzianCurvedMeasureDatum_volumeMeasure
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) :
    (canonicalLorentzianCurvedMeasureDatum g).volumeMeasure =
      PseudoRiemannianMetric.lorentzianVolumeMeasure g := by
  exact
    Physlib.QFT.PathIntegral.CurvedMeasureDatum.volumeMeasure_eq_base_of_density_one
      (canonicalLorentzianCurvedMeasureDatum g) rfl

end CanonicalMeasure

section Parametric

variable {X : Type*} [MeasurableSpace X]

/-- A dominated pointwise Palatini derivative differentiates the actual
continuum action under the integral sign. -/
@[zil_level bridge_theorem]
theorem globalAction_hasDerivAt_of_dominated
    (μ : Measure X) (F F' : ℝ → X → ℝ) (bound : X → ℝ)
    (s : Set ℝ) (t₀ : ℝ)
    (hs : s ∈ 𝓝 t₀)
    (hFmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) μ)
    (hFint : Integrable (F t₀) μ)
    (hF'meas : AEStronglyMeasurable (F' t₀) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖F' t x‖ ≤ bound x)
    (hboundInt : Integrable bound μ)
    (hpointwise : ∀ᵐ x ∂μ, ∀ t ∈ s,
      HasDerivAt (fun u => F u x) (F' t x) t) :
    Integrable (F' t₀) μ ∧
      HasDerivAt (fun t => ∫ x, F t x ∂μ)
        (∫ x, F' t₀ x ∂μ) t₀ :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas hFint hF'meas hbound hboundInt hpointwise

/-- If the dominated Palatini bulk derivative vanishes almost everywhere,
the global action is stationary. -/
@[zil_level physical_theorem]
theorem globalAction_hasDerivAt_zero_of_palatini_bulk_zero
    (μ : Measure X) (F F' : ℝ → X → ℝ) (bound : X → ℝ)
    (s : Set ℝ) (t₀ : ℝ)
    (hs : s ∈ 𝓝 t₀)
    (hFmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) μ)
    (hFint : Integrable (F t₀) μ)
    (hF'meas : AEStronglyMeasurable (F' t₀) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖F' t x‖ ≤ bound x)
    (hboundInt : Integrable bound μ)
    (hpointwise : ∀ᵐ x ∂μ, ∀ t ∈ s,
      HasDerivAt (fun u => F u x) (F' t x) t)
    (hzero : F' t₀ =ᵐ[μ] 0) :
    HasDerivAt (fun t => ∫ x, F t x ∂μ) 0 t₀ := by
  have h := (globalAction_hasDerivAt_of_dominated
    μ F F' bound s t₀ hs hFmeas hFint hF'meas
    hbound hboundInt hpointwise).2
  convert h using 1
  simpa using (integral_congr_ae hzero).symm

end Parametric

section CanonicalPalatiniPath

variable {E M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
variable [IsManifold 𝓘(ℝ, E) 2 M]
variable [IsManifold 𝓘(ℝ, E) (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x)]
variable [T2Space M] [SigmaCompactSpace M]

/-- A Radon-density representation relative to the background metric
measure turns dominated pointwise Palatini differentiation into a derivative
of the actual metric-built Einstein--Hilbert action path. -/
@[zil_level physical_theorem]
theorem canonicalEinsteinHilbertActionPath_hasDerivAt_of_dominated
    (gPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (RicSharpPath : ∀ t x,
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
    (F F' : ℝ → M → ℝ) (bound : M → ℝ)
    (s : Set ℝ) (t₀ : ℝ)
    (hrepresent : ∀ t,
      canonicalEinsteinHilbertAction (gPath t) (RicSharpPath t) =
        ∫ x, F t x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hs : s ∈ 𝓝 t₀)
    (hFmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (F t)
        (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hFint : Integrable (F t₀)
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hF'meas : AEStronglyMeasurable (F' t₀)
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hbound : ∀ᵐ x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)),
      ∀ t ∈ s, ‖F' t x‖ ≤ bound x)
    (hboundInt : Integrable bound
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hpointwise :
      ∀ᵐ x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)),
        ∀ t ∈ s, HasDerivAt (fun u => F u x) (F' t x) t) :
    HasDerivAt
      (fun t => canonicalEinsteinHilbertAction (gPath t) (RicSharpPath t))
      (∫ x, F' t₀ x
        ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀))) t₀ := by
  rw [funext hrepresent]
  exact (globalAction_hasDerivAt_of_dominated
    (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀))
    F F' bound s t₀ hs hFmeas hFint hF'meas
    hbound hboundInt hpointwise).2

/-- Under the same continuum hypotheses, an almost-everywhere vanishing
Palatini density makes the actual canonical Einstein--Hilbert action path
stationary. -/
@[zil_level physical_theorem]
theorem canonicalEinsteinHilbertActionPath_stationary_of_palatini_zero
    (gPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (RicSharpPath : ∀ t x,
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
    (F F' : ℝ → M → ℝ) (bound : M → ℝ)
    (s : Set ℝ) (t₀ : ℝ)
    (hrepresent : ∀ t,
      canonicalEinsteinHilbertAction (gPath t) (RicSharpPath t) =
        ∫ x, F t x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hs : s ∈ 𝓝 t₀)
    (hFmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (F t)
        (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hFint : Integrable (F t₀)
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hF'meas : AEStronglyMeasurable (F' t₀)
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hbound : ∀ᵐ x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)),
      ∀ t ∈ s, ‖F' t x‖ ≤ bound x)
    (hboundInt : Integrable bound
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)))
    (hpointwise :
      ∀ᵐ x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)),
        ∀ t ∈ s, HasDerivAt (fun u => F u x) (F' t x) t)
    (hzero : F' t₀ =ᵐ[
      PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀)] 0) :
    HasDerivAt
      (fun t => canonicalEinsteinHilbertAction (gPath t) (RicSharpPath t))
      0 t₀ := by
  rw [funext hrepresent]
  exact globalAction_hasDerivAt_zero_of_palatini_bulk_zero
    (PseudoRiemannianMetric.lorentzianVolumeMeasure (gPath t₀))
    F F' bound s t₀ hs hFmeas hFint hF'meas
    hbound hboundInt hpointwise hzero

end CanonicalPalatiniPath

/- ZIL-BEGIN -/

zil_theorem_intent PseudoRiemannianMetric.pseudoVolumeDensity_comp where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.pseudoVolumeDensity]

zil_theorem_intent
    PseudoRiemannianMetric.absoluteDeterminantDensity_eq_sqrt_neg_det where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.absoluteDeterminantDensity]

zil_theorem_intent
    PseudoRiemannianMetric.canonicalChartPartition_sum_eq_one where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.canonicalChartPartition]

zil attach PseudoRiemannianMetric.pseudoVolumeDensity_comp where
  formalizes @ "claim:the-pseudo-riemannian-density-sqrt-absolute-det-g-transforms-by-the-absolute-jacobian-under-every-linear-coordinate-change",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:QuadraticForm.discr_comp",
  caveat @ "scope:finite-dimensional-real-model-space-the-global-measure-is-assembled-below-with-a-smooth-chart-partition"

zil attach PseudoRiemannianMetric.absoluteDeterminantDensity_eq_sqrt_neg_det where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:on-the-negative-determinant-lorentzian-branch-the-invariant-absolute-determinant-density-is-exactly-sqrt-minus-det-g",
  epistemic_status @ "consistency-identity",
  caveat @ "premise:negative-determinant-selects-the-relevant-even-dimensional-lorentzian-branch-but-does-not-by-itself-classify-the-full-signature"

zil attach frameScalarCurvatureAt_eq_intrinsicScalarCurvatureAt where
  formalizes @ "claim:the-signed-pseudo-orthonormal-frame-scalar-curvature-is-the-basis-independent-linear-trace-of-the-raised-ricci-endomorphism",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:PseudoRiemannianMetric.frameRicciContractionAt_eq_curvatureRicciTraceAt"

zil attach canonicalFrameEinsteinHilbertAction_eq_intrinsic where
  formalizes @ "claim:the-frame-einstein-hilbert-action-equals-the-intrinsic-ricci-trace-action-when-both-are-integrated-against-the-canonical-metric-built-lorentzian-measure",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:PseudoRiemannianMetric.lorentzianVolumeMeasure",
  caveat @ "premise:the-pointwise-raised-ricci-endomorphism-and-pseudo-orthonormal-frame-represent-the-same-curvature-contraction"

zil attach canonicalLorentzianCurvedMeasureDatum_volumeMeasure where
  formalizes @ "claim:the-existing-curved-path-integral-interface-recovers-exactly-the-metric-built-lorentzian-measure-with-no-second-supplied-density-factor",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QFT.PathIntegral.CurvedMeasureDatum.volumeMeasure_eq_base_of_density_one"

zil attach globalAction_hasDerivAt_zero_of_palatini_bulk_zero where
  formalizes @ "claim:a-dominated-continuum-palatini-variation-with-almost-everywhere-zero-bulk-derivative-makes-the-global-action-stationary",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "mathlib:hasDerivAt_integral_of_dominated_loc_of_deriv_le",
  caveat @ "premise:measurability-integrability-a-common-dominating-function-and-the-pointwise-analytic-palatini-derivative-are-explicit"

zil attach canonicalEinsteinHilbertActionPath_stationary_of_palatini_zero where
  formalizes @ "claim:the-actual-metric-built-einstein-hilbert-action-path-is-stationary-when-its-radon-density-has-a-dominated-palatini-derivative-that-vanishes-almost-everywhere",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction.globalAction_hasDerivAt_zero_of_palatini_bulk_zero",
  caveat @ "premise:the-action-path-has-the-stated-radon-density-representation-relative-to-the-background-metric-measure"

zil_file_contract physlib.globalEinsteinHilbertCanonicalMeasure where
  promises "The pseudo-Riemannian metric constructs an actual Lorentzian manifold measure by chart pullback, sqrt-absolute-det density, Euclidean Haar measure, chart pushforward and a smooth subordinate partition. The density has the exact absolute-Jacobian covariance law and reduces to sqrt-minus-det on the Lorentzian branch. Scalar curvature is the basis-free trace of raised Ricci; certified frame and atlas representatives compute the same scalar. The resulting Einstein-Hilbert action uses the metric-built measure, installs directly in the curved path-integral interface, and admits dominated Palatini differentiation and a continuum stationarity theorem."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:PseudoRiemannianMetric.toQuadraticForm",
    "lean:QuadraticForm.discr_comp",
    "lean:SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source",
    "lean:PseudoRiemannianMetric.curvatureRicciTraceAt",
    "lean:hasDerivAt_integral_of_dominated_loc_of_deriv_le"
  ]
  forbids_substitutes [
    "supplying-an-unrelated-background-measure-or-coordinate-volume-weight",
    "calling-a-frame-sum-coordinate-independent-without-reducing-it-to-linear-trace",
    "interchanging-metric-variation-and-continuum-integration-without-dominated-differentiation-hypotheses",
    "claiming-that-negative-determinant-alone-proves-a-complete-lorentzian-signature-classification"
  ]
  witnessed_by [
    PseudoRiemannianMetric.pseudoVolumeDensity_comp,
    PseudoRiemannianMetric.absoluteDeterminantDensity_eq_sqrt_neg_det,
    PseudoRiemannianMetric.canonicalChartPartition_sum_eq_one,
    frameScalarCurvatureAt_eq_intrinsicScalarCurvatureAt,
    frameScalarCurvatureAt_independent,
    frameScalarCurvatureAt_atlas_eq,
    canonicalFrameEinsteinHilbertAction_eq_intrinsic,
    canonicalLorentzianCurvedMeasureDatum_volumeMeasure,
    globalAction_hasDerivAt_of_dominated,
    globalAction_hasDerivAt_zero_of_palatini_bulk_zero,
    canonicalEinsteinHilbertActionPath_hasDerivAt_of_dominated,
    canonicalEinsteinHilbertActionPath_stationary_of_palatini_zero
  ]

#zil_formalization_lint physlib.globalEinsteinHilbertCanonicalMeasure

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
