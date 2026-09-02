/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Physlib.QFT.PathIntegral.Lorentzian
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicciFromMetric
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Probability.Distributions.Cauchy

meta import Zil

/-!
# Paszko's perturbative Schwarzschild Feynman propagator

This file formalizes the main mathematical spine of R. Paszko,
*Perturbative path-integral evaluation of the Feynman propagator in Schwarzschild spacetime*,
Class. Quantum Grav. **29** (2012) 045005.

The paper works in geometric units `G = ℏ = c = 1`, uses the isotropic weak-field metric through first
order in `M/r`, time-slices the parametrized worldline action, evaluates the flat Gaussian kernel, and
then gives a nonlocal closed form for the massless scalar Feynman propagator through first order in `M`.

The implementation deliberately reuses:

* `WeakFieldEinstein3Plus1.weakFieldMetric4` for the paper's isotropic metric (Eq. 7);
* `SchwarzschildRicci.schwarzschild_ricci_eq_zero` for the exact vacuum background behind `R = 0`;
* `lorentzianKernel` for every real-time slice and for the `iε` damping prescription;
* `CurvedMeasurePathIntegralModel` for the continuum curved-measure carrier.

The paper-specific content is organized as follows.

* **A. Weak Schwarzschild geometry:** Eq. 7, the first-order volume density, and an actual Ricci-to-scalar
  contraction proving that the `ξR` term in Eq. 2 vanishes.
* **B. Time slicing:** Eqs. 8--10 as finite sums of explicit slice actions and measure corrections.
* **C. Proper-time kernel:** Eqs. 3--5 and 15 at the scalar-kernel level, with `iε` as genuine
  complex-action damping.
* **D. Error-function response:** a contour-integral definition of the complex error function and the
  bounded-integral form of the first-order Fock-kernel response in Eq. 33.
* **E. Closed propagator:** Eq. 35, including its exact affine-in-`M` expansion, flat limit, endpoint,
  time-reversal and spatial-reflection symmetries, source-mass derivative, imaginary boundary-value
  contribution, and the honest pointwise `ε → 0` limit away from the light cone.
* **F. Operator check:** the flat invariant profile has explicit complex derivatives, a finite-regulator
  Klein--Gordon residual, and a homogeneous zero-regulator equation away from the light cone.
* **G. Program bridge:** one capstone combining weak geometry, unitary Lorentzian slicing, and the
  first-order nonlocal propagator.

The `i0⁺` distribution is represented by a strictly positive finite `ε`; no equality with an untyped
principal-value distribution is asserted. Likewise, the massive and higher-spin extensions mentioned by
the paper are outside its calculation and are not claimed here.

## References

* R. Paszko (2012), Class. Quantum Grav. 29 045005, Eqs. 1--35.
* J. B. Hartle and S. W. Hawking (1976), parametrized path integrals in curved spacetime.
* B. S. DeWitt (1975), proper-time/Schwinger--DeWitt representation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators Interval Topology
open Filter Matrix MeasureTheory Topology Bornology Module

namespace Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure

/-! # A. Weak Schwarzschild geometry -/

/-- **[Paszko Eq. 7]** The existing isotropic Newtonian-gauge metric, specialized to the point-mass
potential `Φ = -M/r` and `c = 1`, is exactly
`diag(1 - 2M/r, -(1 + 2M/r), -(1 + 2M/r), -(1 + 2M/r))`. -/
lemma weakFieldMetric4_pointMass_eq (M r : ℝ) :
    weakFieldMetric4 (-(M / r)) 1 =
      !![1 - 2 * M / r, 0, 0, 0;
         0, -(1 + 2 * M / r), 0, 0;
         0, 0, -(1 + 2 * M / r), 0;
         0, 0, 0, -(1 + 2 * M / r)] := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldMetric4, weakFieldPerturbation4, minkowskiMetric4] <;> ring

/-- **[Paszko Eq. 9]** First-order isotropic Schwarzschild volume density `√(-g) = 1 + 2M/r + O(M²)`.
This definition is the coefficient retained by the paper's perturbative truncation. -/
def weakSchwarzschildVolumeDensity (M r : ℝ) : ℝ :=
  1 + 2 * M / r

/-- The weak Schwarzschild density is the flat density when the source mass vanishes. -/
@[simp]
lemma weakSchwarzschildVolumeDensity_zero (r : ℝ) :
    weakSchwarzschildVolumeDensity 0 r = 1 := by
  simp [weakSchwarzschildVolumeDensity]

/-- The volume-density perturbation is exactly linear in the source mass. -/
lemma weakSchwarzschildVolumeDensity_sub_one (M r : ℝ) :
    weakSchwarzschildVolumeDensity M r - 1 = M * (2 / r) := by
  simp [weakSchwarzschildVolumeDensity]
  ring

/-- The paper's first-order Schwarzschild density installed in the shared curved-measure carrier.
The nonnegativity premise is precisely the condition needed for `Measure.withDensity`; in the weak-field
regime with positive mass and radius it follows automatically. -/
def weakSchwarzschildMeasureDatum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (M : ℝ) (radius : α → ℝ) (hradius : Measurable radius)
    (hρ : ∀ x, 0 ≤ weakSchwarzschildVolumeDensity M (radius x)) :
    CurvedMeasureDatum α where
  baseMeasure := μ
  volumeDensity := fun x => weakSchwarzschildVolumeDensity M (radius x)
  measurable_volumeDensity := by
    change Measurable ((fun _ : α => (1 : ℝ)) + (fun _ => 2 * M) / radius)
    exact measurable_const.add (measurable_const.div hradius)
  volumeDensity_nonneg := hρ

/-- The perturbative Schwarzschild path measure is absolutely continuous with respect to the flat
reference measure. This is the measure-theoretic form of the density insertion in Paszko Eq. 9. -/
lemma weakSchwarzschildVolumeMeasure_absolutelyContinuous
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (M : ℝ) (radius : α → ℝ) (hradius : Measurable radius)
    (hρ : ∀ x, 0 ≤ weakSchwarzschildVolumeDensity M (radius x)) :
    (weakSchwarzschildMeasureDatum μ M radius hradius hρ).volumeMeasure ≪ μ :=
  (weakSchwarzschildMeasureDatum μ M radius hradius hρ).volumeMeasure_absolutelyContinuous

/-- At zero source mass the Eq. 9 curved measure reduces exactly to its flat reference measure. -/
lemma weakSchwarzschildVolumeMeasure_zero
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (radius : α → ℝ) (hradius : Measurable radius) :
    (weakSchwarzschildMeasureDatum μ 0 radius hradius
      (fun x => by simp [weakSchwarzschildVolumeDensity])).volumeMeasure = μ := by
  apply CurvedMeasureDatum.volumeMeasure_eq_base_of_density_one
  funext x
  simp [weakSchwarzschildMeasureDatum, weakSchwarzschildVolumeDensity]

/-! ## A.1. Continuum path-space measure carrier -/

/-- Install the weak Schwarzschild density on an arbitrary measurable continuum path space. The path
type may be an actual continuous/Sobolev worldline carrier; only its already constructed base measure
and measurable action/radius functionals are required here. -/
def weakSchwarzschildContinuumPathIntegralModel
    {Path : Type*} [MeasurableSpace Path]
    (μ : Measure Path) (M : ℝ) (radius actionRe actionIm : Path → ℝ)
    (hbar : ℝ) (hM : 0 ≤ M) (hradius : Measurable radius)
    (hradius_pos : ∀ path, 0 < radius path)
    (hactionRe : Measurable actionRe) (hactionIm : Measurable actionIm)
    (hbar_pos : 0 < hbar) (hactionIm_nonneg : ∀ path, 0 ≤ actionIm path) :
    CurvedMeasurePathIntegralModel Path where
  geom := weakSchwarzschildMeasureDatum μ M radius hradius fun path => by
    unfold weakSchwarzschildVolumeDensity
    exact add_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (by norm_num) hM) (hradius_pos path).le)
  hbar := hbar
  hbar_pos := hbar_pos
  actionRe := actionRe
  actionIm := actionIm
  measurable_actionRe := hactionRe
  measurable_actionIm := hactionIm
  actionIm_nonneg := hactionIm_nonneg

/-- The genuine continuum partition functional is an integral over the supplied path-space measure,
with Paszko's first-order volume density appearing explicitly under that integral. -/
lemma weakSchwarzschildContinuum_partition_eq_baseIntegral
    {Path : Type*} [MeasurableSpace Path]
    (μ : Measure Path) (M : ℝ) (radius actionRe actionIm : Path → ℝ)
    (hbar : ℝ) (hM : 0 ≤ M) (hradius : Measurable radius)
    (hradius_pos : ∀ path, 0 < radius path)
    (hactionRe : Measurable actionRe) (hactionIm : Measurable actionIm)
    (hbar_pos : 0 < hbar) (hactionIm_nonneg : ∀ path, 0 ≤ actionIm path) :
    (weakSchwarzschildContinuumPathIntegralModel μ M radius actionRe actionIm hbar hM
      hradius hradius_pos hactionRe hactionIm hbar_pos hactionIm_nonneg).partition =
      ∫ path, weakSchwarzschildVolumeDensity M (radius path) •
        (CurvedMeasurePathIntegralModel.toMeasurePathIntegralModel
          (weakSchwarzschildContinuumPathIntegralModel μ M radius actionRe actionIm hbar hM
            hradius hradius_pos hactionRe hactionIm hbar_pos hactionIm_nonneg)).weight path ∂μ := by
  exact CurvedMeasurePathIntegralModel.partition_eq_base_integral_density_smul _

/-- At zero source mass the continuum model integrates its complex-action weight against the original
flat path-space measure; no finite history carrier remains in the statement. -/
lemma weakSchwarzschildContinuum_partition_zeroMass
    {Path : Type*} [MeasurableSpace Path]
    (μ : Measure Path) (radius actionRe actionIm : Path → ℝ)
    (hbar : ℝ) (hradius : Measurable radius)
    (hradius_pos : ∀ path, 0 < radius path)
    (hactionRe : Measurable actionRe) (hactionIm : Measurable actionIm)
    (hbar_pos : 0 < hbar) (hactionIm_nonneg : ∀ path, 0 ≤ actionIm path) :
    (weakSchwarzschildContinuumPathIntegralModel μ 0 radius actionRe actionIm hbar
      (by positivity) hradius hradius_pos hactionRe hactionIm hbar_pos hactionIm_nonneg).partition =
      ∫ path,
        (CurvedMeasurePathIntegralModel.toMeasurePathIntegralModel
          (weakSchwarzschildContinuumPathIntegralModel μ 0 radius actionRe actionIm hbar
            (by positivity) hradius hradius_pos hactionRe hactionIm hbar_pos
            hactionIm_nonneg)).weight path ∂μ := by
  apply CurvedMeasurePathIntegralModel.partition_eq_base_integral_of_density_one
  funext path
  simp [weakSchwarzschildContinuumPathIntegralModel, weakSchwarzschildMeasureDatum,
    weakSchwarzschildVolumeDensity]

/-- The exact Schwarzschild background imported by this module is Ricci-flat on every regular chart
point. This is the paper's `R = 0` premise strengthened to all sixteen Ricci components. -/
lemma schwarzschildBackground_ricciFlat (M r sθ cθ : ℝ)
    (hr : r ≠ 0) (hsθ : sθ ≠ 0) (hf : schwF M r ≠ 0) (μ ν : Fin 4) :
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r sθ cθ)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r sθ cθ) μ ν = 0 :=
  schwarzschild_ricci_eq_zero M r sθ cθ hr hsθ hf μ ν

/-- Ricci matrix of the exact Schwarzschild connection used by the paper's Klein--Gordon operator. -/
def schwarzschildBackgroundRicci (M r sθ cθ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν =>
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r sθ cθ)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r sθ cθ) μ ν

/-- Scalar-curvature contraction `R = g⁻¹{}^{μν}R_{μν}` on the exact Schwarzschild chart. -/
noncomputable def schwarzschildBackgroundScalarCurvature (M r sθ cθ : ℝ) : ℝ :=
  ricciScalarContraction (metricInv (schwF M r) r sθ)
    (schwarzschildBackgroundRicci M r sθ cθ)

/-- **[Paszko Eq. 2, vacuum premise]** The scalar curvature vanishes because every component of the
Schwarzschild Ricci tensor vanishes. This is an actual metric contraction, not a declared `R = 0`. -/
lemma schwarzschildBackground_scalarCurvature_zero (M r sθ cθ : ℝ)
    (hr : r ≠ 0) (hsθ : sθ ≠ 0) (hf : schwF M r ≠ 0) :
    schwarzschildBackgroundScalarCurvature M r sθ cθ = 0 := by
  have hRic : schwarzschildBackgroundRicci M r sθ cθ = 0 := by
    ext μ ν
    exact schwarzschildBackground_ricciFlat M r sθ cθ hr hsθ hf μ ν
  simp [schwarzschildBackgroundScalarCurvature, hRic, ricciScalarContraction]

/-- The mass/curvature potential `m² + ξR` occurring in the curved Klein--Gordon equation. -/
noncomputable def schwarzschildKleinGordonPotential
    (mass ξ M r sθ cθ : ℝ) : ℝ :=
  mass ^ 2 + ξ * schwarzschildBackgroundScalarCurvature M r sθ cθ

/-- **[Paszko Eq. 2]** On the regular vacuum Schwarzschild chart, nonminimal scalar coupling contributes
nothing: `m² + ξR = m²` for every coupling `ξ`. -/
lemma schwarzschildKleinGordonPotential_eq_massSq
    (mass ξ M r sθ cθ : ℝ)
    (hr : r ≠ 0) (hsθ : sθ ≠ 0) (hf : schwF M r ≠ 0) :
    schwarzschildKleinGordonPotential mass ξ M r sθ cθ = mass ^ 2 := by
  simp [schwarzschildKleinGordonPotential,
    schwarzschildBackground_scalarCurvature_zero M r sθ cθ hr hsθ hf]

/-! # B. Time-sliced parametrized action and measure -/

/-- **[Paszko Eq. 8]** One time slice of the parametrized weak-Schwarzschild action. `dt` is the
coordinate-time increment and `dxSq` is the squared Euclidean spatial increment. -/
def weakSchwarzschildSliceAction (M r ε dt dxSq : ℝ) : ℝ :=
  -(dt ^ 2 - dxSq) / (2 * ε) + M * (dt ^ 2 + dxSq) / (ε * r)

/-- Continuum worldline Lagrangian density whose uniform slices are Paszko's Eq. 8.  The
`spatialSpeedSq` argument is `|ẋ|²`; keeping it abstract permits both pointwise smooth and Sobolev
worldline carriers to use the same definition. -/
def weakSchwarzschildWorldlineLagrangian
    (M radius timeVelocity spatialSpeedSq : ℝ) : ℝ :=
  -(timeVelocity ^ 2 - spatialSpeedSq) / 2 +
    M * (timeVelocity ^ 2 + spatialSpeedSq) / radius

/-- Every nondegenerate time slice is exactly `ε` times the continuum Lagrangian evaluated on its
coordinate velocities.  This is the local consistency statement needed by any mesh-refinement
theorem; it is not a continuum limit postulate. -/
lemma weakSchwarzschildSliceAction_of_velocities
    (M radius ε timeVelocity spatialSpeedSq : ℝ) (hε : ε ≠ 0) :
    weakSchwarzschildSliceAction M radius ε (ε * timeVelocity)
        (ε ^ 2 * spatialSpeedSq) =
      ε * weakSchwarzschildWorldlineLagrangian
        M radius timeVelocity spatialSpeedSq := by
  unfold weakSchwarzschildSliceAction weakSchwarzschildWorldlineLagrangian
  field_simp [hε]

/-- The continuum weak-Schwarzschild action on a genuine parameter interval. -/
noncomputable def weakSchwarzschildContinuumAction
    (M T : ℝ) (radius timeVelocity spatialSpeedSq : ℝ → ℝ) : ℝ :=
  ∫ τ in 0..T, weakSchwarzschildWorldlineLagrangian M (radius τ)
    (timeVelocity τ) (spatialSpeedSq τ)

/-- The continuum action of constant-radius, constant-velocity trajectories is the duration times
the local worldline Lagrangian.  Thus the continuum carrier agrees exactly with all uniform affine
worldlines, independently of a discretization. -/
lemma weakSchwarzschildContinuumAction_const
    (M T radius timeVelocity spatialSpeedSq : ℝ) :
    weakSchwarzschildContinuumAction M T (fun _ => radius) (fun _ => timeVelocity)
        (fun _ => spatialSpeedSq) =
      T * weakSchwarzschildWorldlineLagrangian
        M radius timeVelocity spatialSpeedSq := by
  simp [weakSchwarzschildContinuumAction]

/-- The continuum Lagrangian is still exactly first order in the source mass. -/
lemma weakSchwarzschildWorldlineLagrangian_firstOrder
    (M radius timeVelocity spatialSpeedSq : ℝ) :
    weakSchwarzschildWorldlineLagrangian M radius timeVelocity spatialSpeedSq =
      weakSchwarzschildWorldlineLagrangian 0 radius timeVelocity spatialSpeedSq +
        M * ((timeVelocity ^ 2 + spatialSpeedSq) / radius) := by
  simp [weakSchwarzschildWorldlineLagrangian]
  ring

/-- At the continuum level the exact pointwise first-order decomposition is integrated over the
whole worldline.  This formulation remains meaningful before separately discharging Bochner
integrability hypotheses needed to split the integral into two terms. -/
lemma weakSchwarzschildContinuumAction_firstOrder_integrand
    (M T : ℝ) (radius timeVelocity spatialSpeedSq : ℝ → ℝ) :
    weakSchwarzschildContinuumAction M T radius timeVelocity spatialSpeedSq =
      ∫ τ in 0..T,
        (weakSchwarzschildWorldlineLagrangian 0 (radius τ) (timeVelocity τ)
          (spatialSpeedSq τ) +
        M * (((timeVelocity τ) ^ 2 + spatialSpeedSq τ) / radius τ)) := by
  apply intervalIntegral.integral_congr
  intro τ _
  exact weakSchwarzschildWorldlineLagrangian_firstOrder M (radius τ)
    (timeVelocity τ) (spatialSpeedSq τ)

/-- The slice action is the free Minkowski action at `M = 0`. -/
@[simp]
lemma weakSchwarzschildSliceAction_zero (r ε dt dxSq : ℝ) :
    weakSchwarzschildSliceAction 0 r ε dt dxSq = -(dt ^ 2 - dxSq) / (2 * ε) := by
  simp [weakSchwarzschildSliceAction]

/-- The gravitational insertion in one slice is exactly the coefficient of `M`. -/
lemma weakSchwarzschildSliceAction_firstOrder (M r ε dt dxSq : ℝ) :
    weakSchwarzschildSliceAction M r ε dt dxSq =
      weakSchwarzschildSliceAction 0 r ε dt dxSq +
        M * ((dt ^ 2 + dxSq) / (ε * r)) := by
  simp [weakSchwarzschildSliceAction]
  ring

/-- Finite time-sliced action used before the `N → ∞`, `ε → 0` continuum limit. -/
def weakSchwarzschildDiscretizedAction {N : ℕ} (M ε : ℝ)
    (radius dt dxSq : Fin N → ℝ) : ℝ :=
  ∑ j, weakSchwarzschildSliceAction M (radius j) ε (dt j) (dxSq j)

/-- **[Paszko Eqs. 8 and 10]** The full finite sliced action is the flat action plus one sum of
first-order gravitational insertions; no `M²` term is generated at the action level. -/
lemma weakSchwarzschildDiscretizedAction_firstOrder {N : ℕ} (M ε : ℝ)
    (radius dt dxSq : Fin N → ℝ) :
    weakSchwarzschildDiscretizedAction M ε radius dt dxSq =
      weakSchwarzschildDiscretizedAction 0 ε radius dt dxSq +
        M * ∑ j, ((dt j) ^ 2 + dxSq j) / (ε * radius j) := by
  simp only [weakSchwarzschildDiscretizedAction, weakSchwarzschildSliceAction,
    zero_mul, zero_div, add_zero]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **[Paszko Eqs. 9--10]** The measure factor retained through first order is `1 + 2M Σ_j 1/r_j`.
Products of two density perturbations are consistently discarded as `O(M²)`. -/
def weakSchwarzschildMeasureCorrection {N : ℕ} (M : ℝ) (radius : Fin N → ℝ) : ℝ :=
  1 + 2 * M * ∑ j, (radius j)⁻¹

/-- The sliced curved measure reduces to the flat Gaussian measure at zero source mass. -/
@[simp]
lemma weakSchwarzschildMeasureCorrection_zero {N : ℕ} (radius : Fin N → ℝ) :
    weakSchwarzschildMeasureCorrection 0 radius = 1 := by
  simp [weakSchwarzschildMeasureCorrection]

/-! # C. Proper-time/Fock kernel and the `iε` prescription -/

/-- The convergent four-dimensional Gaussian underlying one regulated path-integral slice. Its
coefficient has Feynman real part `ε` and Lorentzian imaginary part `1/(2Λ)`. -/
def regulatedFourDimensionalGaussian (ε Λ : ℝ) : ℂ :=
  let b : ℂ := (ε : ℂ) + Complex.I / (2 * (Λ : ℂ))
  ∫ v : Fin 4 → ℝ, Complex.exp (-b * ∑ μ, (v μ : ℂ) ^ 2)

/-- **[Paszko Eqs. 11, 14--15, regulated form]** The actual four-dimensional Gaussian integration
produces the determinant power `(π/b)²`. Positivity of `ε` is exactly the convergence premise; the
unregulated oscillatory expression is only a boundary value, not a Lebesgue integral. -/
lemma regulatedFourDimensionalGaussian_eq (ε Λ : ℝ) (hε : 0 < ε) :
    regulatedFourDimensionalGaussian ε Λ =
      ((Real.pi : ℂ) / ((ε : ℂ) + Complex.I / (2 * (Λ : ℂ)))) ^ 2 := by
  let b : ℂ := (ε : ℂ) + Complex.I / (2 * (Λ : ℂ))
  have hb : 0 < b.re := by
    have him : (Complex.I / (2 * (Λ : ℂ))).re = 0 := by
      rw [Complex.div_re]
      simp
    simpa [b, him] using hε
  have hgauss := GaussianFourier.integral_cexp_neg_mul_sum_add
    (b := b) hb (fun _ : Fin 4 => (0 : ℂ))
  norm_num at hgauss
  change (∫ v : Fin 4 → ℝ, Complex.exp (-b * ∑ μ, (v μ : ℂ) ^ 2)) =
    ((Real.pi : ℂ) / b) ^ 2
  convert hgauss using 1 with v
  ring_nf

/-- Minkowski interval variable `s = Δt² - |Δx|²` used throughout the paper. -/
def minkowskiSeparationSq (dt dx : ℝ) : ℝ :=
  dt ^ 2 - dx ^ 2

/-- **[Paszko Eq. 15]** The massless flat Fock kernel
`F₀(s; Λ) = -i (2πΛ)⁻² exp(-is/(2Λ))`. -/
def flatFockKernel (s Λ : ℝ) : ℂ :=
  (-Complex.I) / ((2 * Real.pi * Λ : ℝ) : ℂ) ^ 2 *
    Complex.exp (-(Complex.I * ((s / (2 * Λ) : ℝ) : ℂ)))

/-- The flat Fock kernel depends on its endpoints only through the Lorentz invariant `s`. -/
lemma flatFockKernel_lorentzInvariant (dt dx Λ : ℝ) :
    flatFockKernel (minkowskiSeparationSq dt dx) Λ =
      flatFockKernel (dt ^ 2 - dx ^ 2) Λ := rfl

/-- The oscillatory exponential in the flat Fock kernel is the repository's Lorentzian complex-action
kernel with zero imaginary action. -/
lemma flatFockKernel_phase_eq_lorentzianKernel (s Λ : ℝ) :
    Complex.exp (-(Complex.I * ((s / (2 * Λ) : ℝ) : ℂ))) =
      lorentzianKernel (-(s / (2 * Λ))) 0 1 := by
  simp [lorentzianKernel]
  congr 1
  ring

/-- A proper-time path weight with finite Feynman regulator `ε > 0`. The real part is the worldline
action and the imaginary part `εΛ` supplies exponential convergence. -/
def regulatedProperTimeWeight (action ε Λ : ℝ) : ℂ :=
  lorentzianKernel action (ε * Λ) 1

/-- The `iε` prescription is exactly entropic/complex-action damping `exp(-εΛ)`. -/
lemma regulatedProperTimeWeight_norm (action ε Λ : ℝ) :
    ‖regulatedProperTimeWeight action ε Λ‖ = Real.exp (-(ε * Λ)) := by
  simp [regulatedProperTimeWeight, lorentzianKernel_norm_is_damping]

/-- Positive proper time and positive regulator give strict damping, hence convergence rather than a
purely formal oscillatory prescription. -/
lemma regulatedProperTimeWeight_norm_lt_one (action ε Λ : ℝ) (hε : 0 < ε) (hΛ : 0 < Λ) :
    ‖regulatedProperTimeWeight action ε Λ‖ < 1 := by
  rw [regulatedProperTimeWeight_norm]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hε hΛ])

/-- The finite Feynman regulator is exactly the repository's complex-action master weight with
imaginary action `S_I = εΛ` and `ℏ = 1`; it is not a second, paper-specific convention. -/
lemma regulatedProperTimeWeight_eq_complexAction (action ε Λ : ℝ) :
    regulatedProperTimeWeight action ε Λ =
      complexActionPathIntegralWeight action (ε * Λ) 1 := by
  rw [complexActionPathIntegralWeight_eq_lorentzianKernel]
  rfl

/-- The same regulated proper-time slice is the Nagao--Nielsen weight of complex action
`action + i(εΛ)`. Thus the `iε` convergence factor is the entropic/imaginary-action sector. -/
lemma regulatedProperTimeWeight_eq_nagaoNielsen (action ε Λ : ℝ) :
    regulatedProperTimeWeight action ε Λ =
      nagaoNielsenComplexActionWeight action (ε * Λ) 1 := by
  rw [nagaoNielsen_eq_master action (ε * Λ) 1 (by norm_num)]
  exact regulatedProperTimeWeight_eq_complexAction action ε Λ

/-- **[Paszko Eq. 4]** Schwinger--DeWitt/Fock proper-time transform. The positive finite regulator is
kept explicit; `F` is the parametrized kernel solving the first-order Fock equation. -/
def schwingerProperTimeTransform (mass ε : ℝ) (F : ℝ → ℂ) : ℂ :=
  -(Complex.I / 2) *
    ∫ Λ in Set.Ioi (0 : ℝ),
      Complex.exp (-(Complex.I * (((mass ^ 2 + ε) * Λ / 2 : ℝ) : ℂ))) * F Λ

/-- The proper-time transform of the zero kernel vanishes. -/
@[simp]
lemma schwingerProperTimeTransform_zero (mass ε : ℝ) :
    schwingerProperTimeTransform mass ε (fun _ => 0) = 0 := by
  simp [schwingerProperTimeTransform]

/-! # D. Complex error function and the Eq. 33 Fock response -/

/-- Entire complex error function, defined by integrating along the straight segment from `0` to `z`:
`erf(z) = 2z/√π ∫₀¹ exp(-(tz)²) dt`. This is the analytic continuation of the paper's Eq. 19. -/
def complexErf (z : ℂ) : ℂ :=
  (2 : ℂ) / (Real.sqrt Real.pi : ℂ) *
    ∫ t in (0 : ℝ)..1, z * Complex.exp (-(((t : ℂ) * z) ^ 2))

/-- Complementary complex error function `erfc(z) = 1 - erf(z)`. -/
def complexErfc (z : ℂ) : ℂ :=
  1 - complexErf z

/-- `erf(0) = 0`. -/
@[simp]
lemma complexErf_zero : complexErf 0 = 0 := by
  simp [complexErf]

/-- `erfc(0) = 1`. -/
@[simp]
lemma complexErfc_zero : complexErfc 0 = 1 := by
  simp [complexErfc]

/-- Oddness of the contour-defined entire error function. This is the symmetry used when the
endpoint interpolation in Eqs. 28--32 reverses orientation. -/
lemma complexErf_neg (z : ℂ) : complexErf (-z) = -complexErf z := by
  simp only [complexErf, neg_mul, intervalIntegral.integral_neg]
  ring_nf

/-- Reflection of the complementary error function: `erfc(-z) = 1 + erf(z)`. -/
lemma complexErfc_neg (z : ℂ) : complexErfc (-z) = 1 + complexErf z := by
  rw [complexErfc, complexErf_neg]
  ring

/-- The exact complementary-error reflection identity used to exchange the two Gaussian tails. -/
lemma complexErfc_neg_add (z : ℂ) : complexErfc (-z) + complexErfc z = 2 := by
  rw [complexErfc_neg]
  simp [complexErfc]
  norm_num

/-- **[Paszko Eq. 33]** First-order response of the parametrized Fock kernel. The paper has reduced all
time-sliced Gaussian integrals to this expression, leaving only one bounded `α ∈ [0,1]` integral. -/
def schwarzschildFockResponse (dt dx rIn rOut Λ : ℝ) : ℂ :=
  Complex.sqrt (((2 * Real.pi : ℝ) : ℂ) / (Complex.I * Λ)) *
      Complex.exp ((((dx ^ 2 : ℝ) : ℂ) / (2 * Complex.I * Λ))) *
      complexErfc ((((rIn + rOut : ℝ) : ℂ) /
        Complex.sqrt (2 * Complex.I * Λ))) +
    (((dt ^ 2 + dx ^ 2 : ℝ) : ℂ) *
      Complex.sqrt ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) / (Λ : ℂ) ^ 3) *
      ∫ α in (0 : ℝ)..1,
        Complex.exp (((((α ^ 2 * dx ^ 2 : ℝ) : ℂ) /
          (2 * Complex.I * Λ)))) *
        complexErfc (((α * (rIn + rOut) : ℝ) : ℂ) /
          Complex.sqrt (2 * Complex.I * Λ)))

/-- **[Paszko Eq. 33]** Parametrized Schwarzschild kernel through first order in `M`. -/
def schwarzschildFockKernel (M dt dx rIn rOut Λ : ℝ) : ℂ :=
  flatFockKernel (minkowskiSeparationSq dt dx) Λ *
    (1 + (M : ℂ) * schwarzschildFockResponse dt dx rIn rOut Λ)

/-- The parametrized kernel reduces exactly to the flat Fock kernel when `M = 0`. -/
@[simp]
lemma schwarzschildFockKernel_zero (dt dx rIn rOut Λ : ℝ) :
    schwarzschildFockKernel 0 dt dx rIn rOut Λ =
      flatFockKernel (minkowskiSeparationSq dt dx) Λ := by
  simp [schwarzschildFockKernel]

/-- The Fock kernel is exactly affine in `M`, which records that every `O(M²)` term was discarded. -/
lemma schwarzschildFockKernel_firstOrder (M dt dx rIn rOut Λ : ℝ) :
    schwarzschildFockKernel M dt dx rIn rOut Λ =
      flatFockKernel (minkowskiSeparationSq dt dx) Λ +
        M * (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
          schwarzschildFockResponse dt dx rIn rOut Λ) := by
  simp [schwarzschildFockKernel]
  ring

/-- Exact source-mass sensitivity of the parametrized kernel. For any two masses the finite difference
is their mass difference times the same first-order response; this is stronger than a merely formal
Taylor label. -/
lemma schwarzschildFockKernel_sourceMassDifference
    (M₁ M₂ dt dx rIn rOut Λ : ℝ) :
    schwarzschildFockKernel M₂ dt dx rIn rOut Λ -
        schwarzschildFockKernel M₁ dt dx rIn rOut Λ =
      (M₂ - M₁) * (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
        schwarzschildFockResponse dt dx rIn rOut Λ) := by
  rw [schwarzschildFockKernel_firstOrder, schwarzschildFockKernel_firstOrder]
  ring

/-- Shared affine calculus fact for the two source-mass derivative results below. -/
private lemma realAffine_hasDerivAt (a b x : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b) b x := by
  have h := (hasDerivAt_const (x := x) a).add
    ((hasDerivAt_id x).mul_const b)
  have hfun : (fun t : ℝ => a + t * b) =
      (fun _ : ℝ => a) + fun t => t * b := by rfl
  rw [hfun]
  exact h.congr_deriv (by simp)

/-- The real and imaginary components of the parametrized kernel are differentiable in the physical
real source mass, with derivative given by the corresponding components of the gravitational response. -/
lemma schwarzschildFockKernel_sourceMassDerivative
    (M dt dx rIn rOut Λ : ℝ) :
    HasDerivAt (fun mass : ℝ =>
        (schwarzschildFockKernel mass dt dx rIn rOut Λ).re)
      (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
        schwarzschildFockResponse dt dx rIn rOut Λ).re M ∧
    HasDerivAt (fun mass : ℝ =>
        (schwarzschildFockKernel mass dt dx rIn rOut Λ).im)
      (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
        schwarzschildFockResponse dt dx rIn rOut Λ).im M := by
  have hre : (fun mass : ℝ =>
      (schwarzschildFockKernel mass dt dx rIn rOut Λ).re) =
      fun mass : ℝ =>
        (flatFockKernel (minkowskiSeparationSq dt dx) Λ).re +
          mass * (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
            schwarzschildFockResponse dt dx rIn rOut Λ).re := by
    funext mass
    rw [schwarzschildFockKernel_firstOrder]
    simp
  have him : (fun mass : ℝ =>
      (schwarzschildFockKernel mass dt dx rIn rOut Λ).im) =
      fun mass : ℝ =>
        (flatFockKernel (minkowskiSeparationSq dt dx) Λ).im +
          mass * (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
            schwarzschildFockResponse dt dx rIn rOut Λ).im := by
    funext mass
    rw [schwarzschildFockKernel_firstOrder]
    simp
  rw [hre, him]
  exact ⟨realAffine_hasDerivAt _ _ M, realAffine_hasDerivAt _ _ M⟩

/-- Exchanging the two endpoint radii leaves the first-order Fock response invariant. -/
lemma schwarzschildFockResponse_swap (dt dx rIn rOut Λ : ℝ) :
    schwarzschildFockResponse dt dx rIn rOut Λ =
      schwarzschildFockResponse dt dx rOut rIn Λ := by
  simp only [schwarzschildFockResponse]
  ring_nf

/-- **[Paszko Eqs. 4 and 33]** Schwinger's proper-time transform preserves the paper's first-order
decomposition. The hypotheses are the two genuine Bochner-integrability obligations; no formal
linearity of a divergent oscillatory integral is used. -/
lemma schwingerProperTimeTransform_schwarzschild_firstOrder
    (mass ε M dt dx rIn rOut : ℝ)
    (hflat : IntegrableOn (fun Λ : ℝ =>
      Complex.exp (-(Complex.I * (((mass ^ 2 + ε) * Λ / 2 : ℝ) : ℂ))) *
        flatFockKernel (minkowskiSeparationSq dt dx) Λ) (Set.Ioi 0))
    (hcorr : IntegrableOn (fun Λ : ℝ =>
      Complex.exp (-(Complex.I * (((mass ^ 2 + ε) * Λ / 2 : ℝ) : ℂ))) *
        (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
          schwarzschildFockResponse dt dx rIn rOut Λ)) (Set.Ioi 0)) :
    schwingerProperTimeTransform mass ε
        (fun Λ => schwarzschildFockKernel M dt dx rIn rOut Λ) =
      schwingerProperTimeTransform mass ε
        (fun Λ => flatFockKernel (minkowskiSeparationSq dt dx) Λ) +
      M * schwingerProperTimeTransform mass ε
        (fun Λ => flatFockKernel (minkowskiSeparationSq dt dx) Λ *
          schwarzschildFockResponse dt dx rIn rOut Λ) := by
  unfold schwingerProperTimeTransform
  have hfun :
      (fun Λ : ℝ =>
        Complex.exp (-(Complex.I * (((mass ^ 2 + ε) * Λ / 2 : ℝ) : ℂ))) *
          schwarzschildFockKernel M dt dx rIn rOut Λ) =
      (fun Λ : ℝ =>
        Complex.exp (-(Complex.I * (((mass ^ 2 + ε) * Λ / 2 : ℝ) : ℂ))) *
          flatFockKernel (minkowskiSeparationSq dt dx) Λ +
        (M : ℂ) *
          (Complex.exp (-(Complex.I * (((mass ^ 2 + ε) * Λ / 2 : ℝ) : ℂ))) *
            (flatFockKernel (minkowskiSeparationSq dt dx) Λ *
              schwarzschildFockResponse dt dx rIn rOut Λ))) := by
    funext Λ
    rw [schwarzschildFockKernel_firstOrder]
    push_cast
    ring
  rw [hfun, MeasureTheory.integral_add hflat (hcorr.const_mul (M : ℂ)),
    MeasureTheory.integral_const_mul]
  ring

/-! # E. Closed massless Feynman propagator -/

/-- Finite-`ε` massless flat Feynman propagator corresponding to the paper's Eq. 16:
`Δ₀^F(s;ε) = i/[4π²(s-iε)]`. -/
def flatMasslessFeynmanPropagator (ε s : ℝ) : ℂ :=
  Complex.I /
    ((((4 * Real.pi ^ 2 : ℝ) : ℂ) * ((s : ℂ) - Complex.I * (ε : ℂ))))

/-- The finite-`ε` Feynman denominator cannot vanish when `ε > 0`. -/
lemma feynmanBoundaryValue_ne_zero (ε s : ℝ) (hε : 0 < ε) :
    (s : ℂ) - Complex.I * (ε : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- The regularized flat propagator is nonsingular for every real separation when `ε > 0`. -/
lemma flatMasslessFeynmanPropagator_ne_zero (ε s : ℝ) (hε : 0 < ε) :
    flatMasslessFeynmanPropagator ε s ≠ 0 := by
  unfold flatMasslessFeynmanPropagator
  apply div_ne_zero Complex.I_ne_zero
  have hcoef : (4 * Real.pi ^ 2 : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)
  exact mul_ne_zero (by exact_mod_cast hcoef) (feynmanBoundaryValue_ne_zero ε s hε)

/-- **[Paszko Eq. 16, finite-`ε` real part]** The regularized delta contribution is the Cauchy
kernel `-ε/[4π²(s²+ε²)]`. This is an ordinary function identity, before any distributional limit. -/
lemma flatMasslessFeynmanPropagator_re (ε s : ℝ) (hε : 0 < ε) :
    (flatMasslessFeynmanPropagator ε s).re =
      -ε / (4 * Real.pi ^ 2 * (s ^ 2 + ε ^ 2)) := by
  unfold flatMasslessFeynmanPropagator
  rw [Complex.div_re]
  simp only [Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    zero_mul, one_mul, mul_zero, zero_sub, add_zero, Complex.normSq_apply]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : s ^ 2 + ε ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **[Paszko Eq. 16, finite-`ε` imaginary part]** The regularized principal-value contribution is
`s/[4π²(s²+ε²)]`, exposing the exact pre-distributional real/imaginary split. -/
lemma flatMasslessFeynmanPropagator_im (ε s : ℝ) (hε : 0 < ε) :
    (flatMasslessFeynmanPropagator ε s).im =
      s / (4 * Real.pi ^ 2 * (s ^ 2 + ε ^ 2)) := by
  unfold flatMasslessFeynmanPropagator
  rw [Complex.div_im]
  simp only [Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    zero_mul, one_mul, mul_zero, zero_sub, add_zero, Complex.normSq_apply]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : s ^ 2 + ε ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ## E.1. Distributional light-cone limit -/

/-- The normalized unit-scale Cauchy profile.  This is not a new regulator convention: its rescalings
are exactly the real parts of the paper's finite-`ε` Feynman denominator. -/
noncomputable def feynmanDeltaProfile (s : ℝ) : ℝ :=
  ProbabilityTheory.cauchyPDFReal 0 1 s

lemma feynmanDeltaProfile_nonneg (s : ℝ) : 0 ≤ feynmanDeltaProfile s :=
  (ProbabilityTheory.cauchyPDF_pos 0 one_ne_zero s).le

/-- The Feynman Cauchy profile has unit mass. -/
lemma integral_feynmanDeltaProfile_eq_one :
    ∫ s, feynmanDeltaProfile s = 1 := by
  exact ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 one_ne_zero

/-- The profile satisfies Mathlib's peak-function decay hypothesis. -/
lemma feynmanDeltaProfile_peak_decay :
    Tendsto (fun s : ℝ =>
      ‖s‖ ^ Module.finrank ℝ ℝ * feynmanDeltaProfile s)
      (Bornology.cobounded ℝ) (nhds 0) := by
  simp only [Module.finrank_self, pow_one]
  have hinv : Tendsto (fun s : ℝ => ‖s‖⁻¹)
      (Bornology.cobounded ℝ) (nhds 0) := by
    rw [Metric.cobounded_eq_cocompact]
    exact tendsto_norm_cocompact_atTop.inv_tendsto_atTop
  have hbound : Tendsto (fun s : ℝ => Real.pi⁻¹ * ‖s‖⁻¹)
      (Bornology.cobounded ℝ) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun s =>
      mul_nonneg (norm_nonneg s) (feynmanDeltaProfile_nonneg s)) ?_ hbound
  have hevent : ∀ᶠ s : ℝ in Bornology.cobounded ℝ, 0 < ‖s‖ := by
    rw [Metric.cobounded_eq_cocompact]
    exact tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop 0)
  filter_upwards [hevent] with s hs
  rw [feynmanDeltaProfile, ProbabilityTheory.cauchyPDFReal_def]
  norm_num
  have hnorm : ‖s‖ ^ 2 ≤ 1 + ‖s‖ ^ 2 := by linarith
  have hsquare : s ^ 2 = ‖s‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hsquare]
  have hden : 0 < 1 + ‖s‖ ^ 2 := by positivity
  rw [← Real.norm_eq_abs]
  field_simp [ne_of_gt hs, ne_of_gt hden, Real.pi_ne_zero]
  nlinarith [sq_nonneg ‖s‖, Real.pi_pos]

/-- **Distributional completion of Paszko Eq. 16.**  The rescaled finite-`ε` Cauchy kernels
converge to evaluation at the light cone against every integrable test function continuous at zero.
This is a genuine weak/distributional limit, unlike the separate off-light-cone pointwise theorem. -/
lemma feynmanDeltaProfile_tendsto_delta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (hg : Integrable g) (hgc : ContinuousAt g 0) :
    Tendsto (fun c : ℝ =>
      ∫ s, (c * feynmanDeltaProfile (c * s)) • g s)
      atTop (nhds (g 0)) := by
  simpa only [Module.finrank_self, pow_one, smul_eq_mul] using
    (tendsto_integral_comp_smul_smul_of_integrable
      (F := ℝ) (E := E) (μ := volume) (φ := feynmanDeltaProfile)
      feynmanDeltaProfile_nonneg integral_feynmanDeltaProfile_eq_one
      feynmanDeltaProfile_peak_decay hg hgc)

/-- At reciprocal regulator `ε = 1/c`, the real Feynman denominator is exactly `-1/(4π)` times
the normalized Cauchy approximate identity. -/
lemma flatMasslessFeynmanPropagator_re_recip_eq_feynmanDeltaProfile
    (c s : ℝ) (hc : 0 < c) :
    (flatMasslessFeynmanPropagator (1 / c) s).re =
      -(1 / (4 * Real.pi)) * (c * feynmanDeltaProfile (c * s)) := by
  rw [flatMasslessFeynmanPropagator_re (1 / c) s (one_div_pos.mpr hc)]
  rw [feynmanDeltaProfile, ProbabilityTheory.cauchyPDFReal_def]
  norm_num
  field_simp [hc.ne', Real.pi_ne_zero]

/-- The real part of the actual reciprocal-regulator Feynman propagator converges weakly to
`-(4π)⁻¹ δ₀`.  The test class is all integrable functions continuous at the light cone, so in
particular it covers Schwartz test functions without introducing a parallel distribution carrier. -/
lemma flatMasslessFeynmanPropagator_re_tendsto_delta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (hg : Integrable g) (hgc : ContinuousAt g 0) :
    Tendsto (fun c : ℝ =>
      ∫ s, (flatMasslessFeynmanPropagator (1 / c) s).re • g s)
      atTop (nhds ((-(1 / (4 * Real.pi))) • g 0)) := by
  have hpeak := feynmanDeltaProfile_tendsto_delta g hg hgc
  have hscaled := hpeak.const_smul (-(1 / (4 * Real.pi)))
  have hprofile : Tendsto (fun c : ℝ =>
      ∫ s, (-(1 / (4 * Real.pi)) *
        (c * feynmanDeltaProfile (c * s))) • g s)
      atTop (nhds ((-(1 / (4 * Real.pi))) • g 0)) := by
    apply hscaled.congr'
    filter_upwards with c
    rw [← MeasureTheory.integral_smul]
    apply integral_congr_ae
    filter_upwards with s
    rw [smul_smul]
  apply hprofile.congr'
  filter_upwards [eventually_gt_atTop 0] with c hc
  apply integral_congr_ae
  filter_upwards with s
  rw [flatMasslessFeynmanPropagator_re_recip_eq_feynmanDeltaProfile c s hc]

/-! ## E.2. Shifted retarded/advanced distributional boundary values -/

/-- The finite Cauchy regulator evaluated around an arbitrary time `x₀`.
This is the translated approximate identity needed at the retarded and
advanced light-cone times. -/
noncomputable def shiftedFeynmanDeltaRegulatorAction
    (q x₀ : ℝ) (η : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x, (q * feynmanDeltaProfile (q • (x₀ - x))) • η x

/-- The translated finite Feynman regulator converges, on every complex
Schwartz test function, to the shifted Dirac distribution. -/
theorem shiftedFeynmanDeltaRegulator_tendsto_dirac
    (x₀ : ℝ) (η : SchwartzMap ℝ ℂ) :
    Tendsto (fun q : ℝ => shiftedFeynmanDeltaRegulatorAction q x₀ η)
      atTop (nhds (η x₀)) := by
  simpa only [shiftedFeynmanDeltaRegulatorAction, Module.finrank_self,
    pow_one] using
    (tendsto_integral_comp_smul_smul_of_integrable'
      (F := ℝ) (E := ℂ) (μ := volume) (φ := feynmanDeltaProfile)
      feynmanDeltaProfile_nonneg integral_feynmanDeltaProfile_eq_one
      feynmanDeltaProfile_peak_decay η.integrable
      η.continuous.continuousAt (x₀ := x₀))

/-- Finite-`iε` Cauchy action centered at the physical retarded time. -/
noncomputable def retardedFeynmanDeltaRegulatorAction
    (q t r c : ℝ) (η : SchwartzMap ℝ ℂ) : ℂ :=
  shiftedFeynmanDeltaRegulatorAction q (retardedTime t r c) η

/-- The retarded finite regulator converges weakly to the actual retarded
Schwartz distribution constructed from the light-cone Dirac measure. -/
theorem retardedFeynmanDeltaRegulator_tendsto_distribution
    (t r c : ℝ) (η : SchwartzMap ℝ ℂ) :
    Tendsto
      (fun q : ℝ => retardedFeynmanDeltaRegulatorAction q t r c η)
      atTop (nhds (retardedDistribution t r c η)) := by
  simpa only [retardedFeynmanDeltaRegulatorAction,
    retardedDistribution_apply] using
    shiftedFeynmanDeltaRegulator_tendsto_dirac (retardedTime t r c) η

/-- Finite-`iε` Cauchy action centered at the advanced time obtained by
time reversal. -/
noncomputable def advancedFeynmanDeltaRegulatorAction
    (q t r c : ℝ) (η : SchwartzMap ℝ ℂ) : ℂ :=
  shiftedFeynmanDeltaRegulatorAction q (advancedTime t r c) η

/-- The advanced finite regulator converges weakly to the actual advanced
Schwartz distribution. -/
theorem advancedFeynmanDeltaRegulator_tendsto_distribution
    (t r c : ℝ) (η : SchwartzMap ℝ ℂ) :
    Tendsto
      (fun q : ℝ => advancedFeynmanDeltaRegulatorAction q t r c η)
      atTop (nhds (advancedDistribution t r c η)) := by
  simpa only [advancedFeynmanDeltaRegulatorAction,
    advancedDistribution_apply] using
    shiftedFeynmanDeltaRegulator_tendsto_dirac (advancedTime t r c) η

/-- The Coulomb-weighted retarded-minus-advanced finite-regulator action.
It is an ordinary Bochner integral for every finite scale `q`. -/
noncomputable def causalFeynmanDeltaRegulatorAction
    (q t r c : ℝ) (η : SchwartzMap ℝ ℂ) : ℂ :=
  (retardedAmplitude r : ℂ) *
      retardedFeynmanDeltaRegulatorAction q t r c η -
    (retardedAmplitude r : ℂ) *
      advancedFeynmanDeltaRegulatorAction q t r c η

/-- The finite Cauchy path-integral boundary values converge to the explicit
radial Pauli--Jordan Schwartz distribution.  This closes the model-specific
analytic junction between Paszko's finite regulator and the repository's
retarded/advanced Green carrier. -/
theorem causalFeynmanDeltaRegulator_tendsto_pauliJordanDistribution
    (t r c : ℝ) (η : SchwartzMap ℝ ℂ) :
    Tendsto
      (fun q : ℝ => causalFeynmanDeltaRegulatorAction q t r c η)
      atTop (nhds (causalKernelDistribution t r c η)) := by
  have hret :=
    (retardedFeynmanDeltaRegulator_tendsto_distribution t r c η).const_mul
      (retardedAmplitude r : ℂ)
  have hadv :=
    (advancedFeynmanDeltaRegulator_tendsto_distribution t r c η).const_mul
      (retardedAmplitude r : ℂ)
  simpa only [causalFeynmanDeltaRegulatorAction,
    causalKernelDistribution_apply, retardedDistribution_apply,
    advancedDistribution_apply, mul_sub] using hret.sub hadv

/-- Ordinary off-light-cone boundary value of the flat massless propagator. This is the pointwise
function represented by the paper's `i0⁺` notation when `s ≠ 0`; it deliberately makes no assertion at
the distributional singularity `s = 0`. -/
def flatMasslessFeynmanBoundaryValue (s : ℝ) : ℂ :=
  Complex.I / ((((4 * Real.pi ^ 2 : ℝ) : ℂ) * (s : ℂ)))

/-- **[Paszko Eq. 16, honest `ε → 0` limit]** Away from the light cone, the finite Feynman regulator
converges pointwise to `i/(4π²s)`. -/
lemma flatMasslessFeynmanPropagator_tendsto_boundaryValue
    (s : ℝ) (hs : s ≠ 0) :
    Tendsto (fun ε : ℝ => flatMasslessFeynmanPropagator ε s) (𝓝 0)
      (𝓝 (flatMasslessFeynmanBoundaryValue s)) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hπ : (4 * Real.pi ^ 2 : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)
  have hπC : ((4 * Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ
  have hden0 : (s : ℂ) - Complex.I * (0 : ℂ) ≠ 0 := by
    simpa using hsC
  have hcont : ContinuousAt (fun ε : ℝ =>
      ((4 * Real.pi ^ 2 : ℝ) : ℂ) *
        ((s : ℂ) - Complex.I * (ε : ℂ))) 0 := by
    fun_prop
  have hI : Tendsto (fun _ : ℝ => Complex.I) (nhds 0) (nhds Complex.I) :=
    tendsto_const_nhds
  have hlim : Tendsto (fun ε : ℝ => Complex.I /
      (((4 * Real.pi ^ 2 : ℝ) : ℂ) *
        ((s : ℂ) - Complex.I * (ε : ℂ)))) (nhds 0)
      (nhds (Complex.I / (((4 * Real.pi ^ 2 : ℝ) : ℂ) *
        ((s : ℂ) - Complex.I * (0 : ℂ))))) :=
    hI.div hcont (mul_ne_zero hπC hden0)
  unfold flatMasslessFeynmanPropagator flatMasslessFeynmanBoundaryValue
  simpa using hlim

/-! # F. Operator-level flat Klein--Gordon check -/

/-- Holomorphic invariant-separation profile underlying the flat propagator. Restricting `z` to a real
Minkowski separation recovers `flatMasslessFeynmanPropagator`. -/
def flatFeynmanInvariantProfile (ε : ℝ) (z : ℂ) : ℂ :=
  (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
    (z - Complex.I * (ε : ℂ))⁻¹

/-- The real-separation propagator is the restriction of the holomorphic invariant profile. -/
lemma flatMasslessFeynmanPropagator_eq_invariantProfile (ε s : ℝ) :
    flatMasslessFeynmanPropagator ε s = flatFeynmanInvariantProfile ε (s : ℂ) := by
  simp only [flatMasslessFeynmanPropagator, flatFeynmanInvariantProfile, div_eq_mul_inv]
  rw [_root_.mul_inv_rev]
  ring

/-- First invariant-profile derivative `dΔ/ds`. -/
def flatFeynmanInvariantProfileDeriv (ε : ℝ) (z : ℂ) : ℂ :=
  -(Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
    ((z - Complex.I * (ε : ℂ))⁻¹) ^ 2

/-- Second invariant-profile derivative `d²Δ/ds²`. -/
def flatFeynmanInvariantProfileSecondDeriv (ε : ℝ) (z : ℂ) : ℂ :=
  2 * (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
    ((z - Complex.I * (ε : ℂ))⁻¹) ^ 3

/-- The regularized invariant profile has the stated first complex derivative away from its displaced
pole `z = iε`. -/
lemma flatFeynmanInvariantProfile_hasDerivAt (ε : ℝ) (z : ℂ)
    (hz : z - Complex.I * (ε : ℂ) ≠ 0) :
    HasDerivAt (flatFeynmanInvariantProfile ε)
      (flatFeynmanInvariantProfileDeriv ε z) z := by
  have hlin : HasDerivAt (fun w : ℂ => w - Complex.I * (ε : ℂ)) 1 z :=
    (hasDerivAt_id z).sub_const _
  have hinv := hlin.inv hz
  have hcoeff : flatFeynmanInvariantProfileDeriv ε z =
      (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
        (-1 / (z - Complex.I * (ε : ℂ)) ^ 2) := by
    unfold flatFeynmanInvariantProfileDeriv
    field_simp [hz]
  rw [hcoeff]
  change HasDerivAt
    (fun w : ℂ => (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
      (w - Complex.I * (ε : ℂ))⁻¹) _ z
  exact hinv.const_mul (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ))

/-- The first derivative differentiates once more to the stated second derivative. -/
lemma flatFeynmanInvariantProfileDeriv_hasDerivAt (ε : ℝ) (z : ℂ)
    (hz : z - Complex.I * (ε : ℂ) ≠ 0) :
    HasDerivAt (flatFeynmanInvariantProfileDeriv ε)
      (flatFeynmanInvariantProfileSecondDeriv ε z) z := by
  have hlin : HasDerivAt (fun w : ℂ => w - Complex.I * (ε : ℂ)) 1 z :=
    (hasDerivAt_id z).sub_const _
  have hinv := hlin.inv hz
  have hprod := hinv.mul hinv
  have hcoeff : flatFeynmanInvariantProfileSecondDeriv ε z =
      -(Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
        ((-1 / (z - Complex.I * (ε : ℂ)) ^ 2) *
          (z - Complex.I * (ε : ℂ))⁻¹ +
        (z - Complex.I * (ε : ℂ))⁻¹ *
          (-1 / (z - Complex.I * (ε : ℂ)) ^ 2)) := by
    unfold flatFeynmanInvariantProfileSecondDeriv
    field_simp [hz]
    ring
  have hfun : flatFeynmanInvariantProfileDeriv ε = fun w : ℂ =>
      -(Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
        ((w - Complex.I * (ε : ℂ))⁻¹ * (w - Complex.I * (ε : ℂ))⁻¹) := by
    funext w
    simp only [flatFeynmanInvariantProfileDeriv, pow_two]
  rw [hcoeff, hfun]
  exact hprod.const_mul (-(Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)))

/-- For a four-dimensional radial profile `f(s)`, with `s=t²-r²`, the flat d'Alembertian is
`□f = 8 f'(s) + 4s f''(s)`. This definition packages that invariant-profile operator. -/
def radialWaveOnInvariantProfile (z first second : ℂ) : ℂ :=
  8 * first + 4 * z * second

/-- The finite Feynman regulator produces an explicit displaced-source residual. It is proportional
to `ε`; this is the exact operator-level distinction between the regularized function and its
distributional boundary value. -/
lemma flatFeynmanInvariantProfile_radialWave_residual (ε : ℝ) (z : ℂ)
    (hz : z - Complex.I * (ε : ℂ) ≠ 0) :
    radialWaveOnInvariantProfile z
        (flatFeynmanInvariantProfileDeriv ε z)
        (flatFeynmanInvariantProfileSecondDeriv ε z) =
      8 * (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
        (Complex.I * (ε : ℂ)) * ((z - Complex.I * (ε : ℂ))⁻¹) ^ 3 := by
  simp only [radialWaveOnInvariantProfile, flatFeynmanInvariantProfileDeriv,
    flatFeynmanInvariantProfileSecondDeriv]
  field_simp [hz]
  ring

/-- **Homogeneous massless Klein--Gordon equation away from the light cone.** At zero regulator the
radial d'Alembertian of the flat Feynman invariant profile vanishes for `z ≠ 0`. -/
lemma flatFeynmanInvariantProfile_radialWave_zero (z : ℂ) (hz : z ≠ 0) :
    radialWaveOnInvariantProfile z
        (flatFeynmanInvariantProfileDeriv 0 z)
        (flatFeynmanInvariantProfileSecondDeriv 0 z) = 0 := by
  simpa using flatFeynmanInvariantProfile_radialWave_residual 0 z (by simpa using hz)

/-- The derivative data and regulated Klein--Gordon residual form one checked analytic package. -/
theorem flatFeynmanInvariantProfile_kg_chain (ε : ℝ) (z : ℂ)
    (hz : z - Complex.I * (ε : ℂ) ≠ 0) :
    HasDerivAt (flatFeynmanInvariantProfile ε)
        (flatFeynmanInvariantProfileDeriv ε z) z ∧
      HasDerivAt (flatFeynmanInvariantProfileDeriv ε)
        (flatFeynmanInvariantProfileSecondDeriv ε z) z ∧
      radialWaveOnInvariantProfile z
          (flatFeynmanInvariantProfileDeriv ε z)
          (flatFeynmanInvariantProfileSecondDeriv ε z) =
        8 * (Complex.I / ((4 * Real.pi ^ 2 : ℝ) : ℂ)) *
          (Complex.I * (ε : ℂ)) * ((z - Complex.I * (ε : ℂ))⁻¹) ^ 3 :=
  ⟨flatFeynmanInvariantProfile_hasDerivAt ε z hz,
    flatFeynmanInvariantProfileDeriv_hasDerivAt ε z hz,
    flatFeynmanInvariantProfile_radialWave_residual ε z hz⟩

/-- The boundary value `artanh(u) - iπ/2` appearing in the closed Schwarzschild correction. -/
def feynmanArtanhBoundary (u : ℝ) : ℂ :=
  (Real.artanh u : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)

/-- The imaginary part of the Feynman `artanh` boundary value is `-π/2`. -/
@[simp]
lemma feynmanArtanhBoundary_im (u : ℝ) :
    (feynmanArtanhBoundary u).im = -(Real.pi / 2) := by
  simp [feynmanArtanhBoundary]

/-- The nonsingular nonlocal domain of Paszko Eq. 35. It records exactly the four analytic exclusions:
nonzero time separation, off the Minkowski light cone, off the radial denominator pole, and inside the
real principal branch `|(r+r')/|Δt|| < 1` of `artanh`. -/
structure PaszkoRegularDomain (dt dx rIn rOut : ℝ) : Prop where
  /-- The endpoint time separation is nonzero. -/
  time_ne_zero : dt ≠ 0
  /-- The two points are off the flat light cone. -/
  separation_ne_zero : minkowskiSeparationSq dt dx ≠ 0
  /-- The rational radial denominator in Eq. 35 is nonzero. -/
  radialPole_ne_zero : dt ^ 2 - (rIn + rOut) ^ 2 ≠ 0
  /-- The boundary-value `artanh` argument lies on its real principal branch. -/
  artanhRatio_mem : (rIn + rOut) / |dt| ∈ Set.Ioo (-1) 1

/-- The absolute time separation is nonzero throughout the regular domain. -/
lemma PaszkoRegularDomain.abs_time_ne_zero
    {dt dx rIn rOut : ℝ} (h : PaszkoRegularDomain dt dx rIn rOut) : |dt| ≠ 0 :=
  abs_ne_zero.mpr h.time_ne_zero

/-- On the regular branch the real part of the Feynman boundary value is genuinely inverse to `tanh`.
This pins the closed Eq. 35 expression to Mathlib's principal real `artanh`, rather than a formal symbol. -/
lemma PaszkoRegularDomain.tanh_feynmanArtanhBoundary_re
    {dt dx rIn rOut : ℝ} (h : PaszkoRegularDomain dt dx rIn rOut) :
    Real.tanh (feynmanArtanhBoundary ((rIn + rOut) / |dt|)).re =
      (rIn + rOut) / |dt| := by
  simpa [feynmanArtanhBoundary] using Real.tanh_artanh h.artanhRatio_mem

/-- Endpoint exchange preserves the complete nonsingular domain. -/
lemma PaszkoRegularDomain.swap
    {dt dx rIn rOut : ℝ} (h : PaszkoRegularDomain dt dx rIn rOut) :
    PaszkoRegularDomain dt dx rOut rIn := by
  constructor
  · exact h.time_ne_zero
  · exact h.separation_ne_zero
  · simpa [add_comm] using h.radialPole_ne_zero
  · simpa [add_comm] using h.artanhRatio_mem

/-- **[Paszko Eq. 35]** Coefficient of the source mass in the nonlocal first-order propagator. -/
def schwarzschildPropagatorResponse (dt dx rIn rOut : ℝ) : ℂ :=
  let s := minkowskiSeparationSq dt dx
  let rSum := rIn + rOut
  4 * (((rSum / (dt ^ 2 - rSum ^ 2) : ℝ) : ℂ) +
    ((2 * |dt| / s : ℝ) : ℂ) * feynmanArtanhBoundary (rSum / |dt|))

/-- **[Paszko Eq. 35]** The massless scalar Schwarzschild Feynman propagator, nonlocal in its two
endpoints and correct through first order in `M`. -/
def schwarzschildMasslessFeynmanPropagator
    (M ε dt dx rIn rOut : ℝ) : ℂ :=
  let s := minkowskiSeparationSq dt dx
  flatMasslessFeynmanPropagator ε s *
    (1 + (M : ℂ) * schwarzschildPropagatorResponse dt dx rIn rOut)

/-- Eq. 35 reduces to the regularized Minkowski propagator when the source mass vanishes. -/
@[simp]
lemma schwarzschildMasslessFeynmanPropagator_zero (ε dt dx rIn rOut : ℝ) :
    schwarzschildMasslessFeynmanPropagator 0 ε dt dx rIn rOut =
      flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) := by
  simp [schwarzschildMasslessFeynmanPropagator]

/-- Eq. 35 is exactly the flat propagator plus `M` times one nonlocal response. -/
lemma schwarzschildMasslessFeynmanPropagator_firstOrder (M ε dt dx rIn rOut : ℝ) :
    schwarzschildMasslessFeynmanPropagator M ε dt dx rIn rOut =
      flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) +
        M * (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
          schwarzschildPropagatorResponse dt dx rIn rOut) := by
  simp [schwarzschildMasslessFeynmanPropagator]
  ring

/-- Exact source-mass finite difference of the closed propagator. The response is independent of the
base mass because Eq. 35 has already been consistently truncated at first order. -/
lemma schwarzschildMasslessFeynmanPropagator_sourceMassDifference
    (M₁ M₂ ε dt dx rIn rOut : ℝ) :
    schwarzschildMasslessFeynmanPropagator M₂ ε dt dx rIn rOut -
        schwarzschildMasslessFeynmanPropagator M₁ ε dt dx rIn rOut =
      (M₂ - M₁) *
        (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
          schwarzschildPropagatorResponse dt dx rIn rOut) := by
  rw [schwarzschildMasslessFeynmanPropagator_firstOrder,
    schwarzschildMasslessFeynmanPropagator_firstOrder]
  ring

/-- Both complex components of the closed Eq. 35 propagator have the exact first-order correction as
their physical source-mass derivative. -/
lemma schwarzschildMasslessFeynmanPropagator_sourceMassDerivative
    (M ε dt dx rIn rOut : ℝ) :
    HasDerivAt (fun mass : ℝ =>
        (schwarzschildMasslessFeynmanPropagator mass ε dt dx rIn rOut).re)
      (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
        schwarzschildPropagatorResponse dt dx rIn rOut).re M ∧
    HasDerivAt (fun mass : ℝ =>
        (schwarzschildMasslessFeynmanPropagator mass ε dt dx rIn rOut).im)
      (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
        schwarzschildPropagatorResponse dt dx rIn rOut).im M := by
  have hre : (fun mass : ℝ =>
      (schwarzschildMasslessFeynmanPropagator mass ε dt dx rIn rOut).re) =
      fun mass : ℝ =>
        (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx)).re +
          mass * (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
            schwarzschildPropagatorResponse dt dx rIn rOut).re := by
    funext mass
    rw [schwarzschildMasslessFeynmanPropagator_firstOrder]
    simp
  have him : (fun mass : ℝ =>
      (schwarzschildMasslessFeynmanPropagator mass ε dt dx rIn rOut).im) =
      fun mass : ℝ =>
        (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx)).im +
          mass * (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
            schwarzschildPropagatorResponse dt dx rIn rOut).im := by
    funext mass
    rw [schwarzschildMasslessFeynmanPropagator_firstOrder]
    simp
  rw [hre, him]
  exact ⟨realAffine_hasDerivAt _ _ M, realAffine_hasDerivAt _ _ M⟩

/-- Pointwise off-light-cone boundary value of Paszko Eq. 35. It multiplies the ordinary flat boundary
value by the exact first-order Schwarzschild response and remains distinct from a distribution on the
light cone. -/
def schwarzschildMasslessFeynmanBoundaryValue
    (M dt dx rIn rOut : ℝ) : ℂ :=
  flatMasslessFeynmanBoundaryValue (minkowskiSeparationSq dt dx) *
    (1 + (M : ℂ) * schwarzschildPropagatorResponse dt dx rIn rOut)

/-- **[Paszko Eqs. 16 and 35]** Away from the light cone, the finite-`ε` first-order Schwarzschild
propagator converges pointwise to its ordinary boundary value. The singular distribution at `s = 0`
is not smuggled into this statement. -/
lemma schwarzschildMasslessFeynmanPropagator_tendsto_boundaryValue
    (M dt dx rIn rOut : ℝ)
    (hs : minkowskiSeparationSq dt dx ≠ 0) :
    Tendsto (fun ε : ℝ =>
        schwarzschildMasslessFeynmanPropagator M ε dt dx rIn rOut) (𝓝 0)
      (𝓝 (schwarzschildMasslessFeynmanBoundaryValue M dt dx rIn rOut)) := by
  simpa [schwarzschildMasslessFeynmanPropagator,
    schwarzschildMasslessFeynmanBoundaryValue] using
    (flatMasslessFeynmanPropagator_tendsto_boundaryValue
      (minkowskiSeparationSq dt dx) hs).mul tendsto_const_nhds

/-- The boundary-value propagator retains the exact first-order mass decomposition after the regulator
has been removed off the light cone. -/
lemma schwarzschildMasslessFeynmanBoundaryValue_firstOrder
    (M dt dx rIn rOut : ℝ) :
    schwarzschildMasslessFeynmanBoundaryValue M dt dx rIn rOut =
      flatMasslessFeynmanBoundaryValue (minkowskiSeparationSq dt dx) +
        M * (flatMasslessFeynmanBoundaryValue (minkowskiSeparationSq dt dx) *
          schwarzschildPropagatorResponse dt dx rIn rOut) := by
  simp [schwarzschildMasslessFeynmanBoundaryValue]
  ring

/-- The discarded higher-order remainder is identically zero in the first-order model. -/
lemma schwarzschildMasslessFeynmanPropagator_remainder (M ε dt dx rIn rOut : ℝ) :
    schwarzschildMasslessFeynmanPropagator M ε dt dx rIn rOut -
        flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) -
        M * (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
          schwarzschildPropagatorResponse dt dx rIn rOut) = 0 := by
  rw [schwarzschildMasslessFeynmanPropagator_firstOrder]
  ring

/-- Endpoint exchange symmetry: only the symmetric radial combination `rIn + rOut` occurs. -/
lemma schwarzschildPropagatorResponse_swap (dt dx rIn rOut : ℝ) :
    schwarzschildPropagatorResponse dt dx rIn rOut =
      schwarzschildPropagatorResponse dt dx rOut rIn := by
  simp [schwarzschildPropagatorResponse, add_comm]

/-- Time-reversal symmetry of the scalar response: it depends on `dt` through `dt²` and `|dt|`. -/
lemma schwarzschildPropagatorResponse_timeReversal (dt dx rIn rOut : ℝ) :
    schwarzschildPropagatorResponse (-dt) dx rIn rOut =
      schwarzschildPropagatorResponse dt dx rIn rOut := by
  simp [schwarzschildPropagatorResponse, minkowskiSeparationSq]

/-- Spatial-reflection symmetry: the response depends on the displacement through `dx²`. -/
lemma schwarzschildPropagatorResponse_spatialReflection (dt dx rIn rOut : ℝ) :
    schwarzschildPropagatorResponse dt (-dx) rIn rOut =
      schwarzschildPropagatorResponse dt dx rIn rOut := by
  simp [schwarzschildPropagatorResponse, minkowskiSeparationSq]

/-- The imaginary part of the first-order response is fixed entirely by the Feynman boundary value.
This isolates the paper's `-iπ/2` contribution from its real radial and `artanh` terms. -/
lemma schwarzschildPropagatorResponse_im (dt dx rIn rOut : ℝ) :
    (schwarzschildPropagatorResponse dt dx rIn rOut).im =
      -(4 * |dt| * Real.pi / minkowskiSeparationSq dt dx) := by
  simp only [schwarzschildPropagatorResponse, minkowskiSeparationSq,
    Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    feynmanArtanhBoundary_im, zero_mul, add_zero]
  norm_num
  ring

/-- Away from `dt = 0` and the light cone `s = 0`, the source response is genuinely nonzero. Thus the
Schwarzschild result is not merely the flat propagator relabeled. -/
lemma schwarzschildPropagatorResponse_ne_zero (dt dx rIn rOut : ℝ)
    (hdt : dt ≠ 0) (hs : minkowskiSeparationSq dt dx ≠ 0) :
    schwarzschildPropagatorResponse dt dx rIn rOut ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [schwarzschildPropagatorResponse_im] at him
  simp only [Complex.zero_im] at him
  have habs : |dt| ≠ 0 := abs_ne_zero.mpr hdt
  have hnum : 4 * |dt| * Real.pi ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) habs) Real.pi_ne_zero
  exact (div_ne_zero hnum hs) (neg_eq_zero.mp him)

/-- **Loss of translation invariance, by witness.** Keeping the coordinate displacement fixed but
translating both endpoint radii from `(1,1)` to `(2,2)` changes the gravitational response. This
formalizes the qualitative distinction from the flat kernel emphasized after Eqs. 16 and 35. -/
lemma schwarzschildPropagatorResponse_not_translationInvariant :
    schwarzschildPropagatorResponse 0 1 1 1 ≠
      schwarzschildPropagatorResponse 0 1 2 2 := by
  norm_num [schwarzschildPropagatorResponse, minkowskiSeparationSq,
    feynmanArtanhBoundary]

/-- The full propagator inherits endpoint exchange symmetry. -/
lemma schwarzschildMasslessFeynmanPropagator_swap (M ε dt dx rIn rOut : ℝ) :
    schwarzschildMasslessFeynmanPropagator M ε dt dx rIn rOut =
      schwarzschildMasslessFeynmanPropagator M ε dt dx rOut rIn := by
  simp [schwarzschildMasslessFeynmanPropagator,
    schwarzschildPropagatorResponse_swap]

/-! # G. Complex-action/entropic-time capstone -/

/-- The paper's main structural chain on existing repository carriers: the weak point-mass metric is the
isotropic Schwarzschild metric, every regulated proper-time slice has strictly subunit norm, and the
closed propagator is exactly flat plus its nonzero first-order source response. -/
theorem paszkoSchwarzschild_complexAction_chain
    (M r action ε Λ dt dx rIn rOut : ℝ)
    (hε : 0 < ε) (hΛ : 0 < Λ) (hdt : dt ≠ 0)
    (hs : minkowskiSeparationSq dt dx ≠ 0) :
    weakFieldMetric4 (-(M / r)) 1 =
        !![1 - 2 * M / r, 0, 0, 0;
           0, -(1 + 2 * M / r), 0, 0;
           0, 0, -(1 + 2 * M / r), 0;
           0, 0, 0, -(1 + 2 * M / r)] ∧
      ‖regulatedProperTimeWeight action ε Λ‖ < 1 ∧
      regulatedProperTimeWeight action ε Λ =
        complexActionPathIntegralWeight action (ε * Λ) 1 ∧
      schwarzschildMasslessFeynmanPropagator M ε dt dx rIn rOut =
        flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) +
          M * (flatMasslessFeynmanPropagator ε (minkowskiSeparationSq dt dx) *
            schwarzschildPropagatorResponse dt dx rIn rOut) ∧
      schwarzschildPropagatorResponse dt dx rIn rOut ≠ 0 := by
  exact ⟨weakFieldMetric4_pointMass_eq M r,
    regulatedProperTimeWeight_norm_lt_one action ε Λ hε hΛ,
    regulatedProperTimeWeight_eq_complexAction action ε Λ,
    schwarzschildMasslessFeynmanPropagator_firstOrder M ε dt dx rIn rOut,
    schwarzschildPropagatorResponse_ne_zero dt dx rIn rOut hdt hs⟩

end Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator

end

/- ZIL-BEGIN -/

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakFieldMetric4_pointMass_eq where
  formalizes @ "claim:paszko-eq-7-isotropic-schwarzschild-metric-through-first-order-in-M-over-r",
  supported_by @ "paper:paszko-2012-perturbative-path-integral-feynman-propagator-schwarzschild"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildKleinGordonPotential_eq_massSq where
  formalizes @ "claim:paszko-eq-2-schwarzschild-ricci-flatness-contracts-to-zero-scalar-curvature-so-the-xi-R-klein-gordon-potential-reduces-to-mass-squared",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildBackground_scalarCurvature_zero"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildDiscretizedAction_firstOrder where
  formalizes @ "claim:paszko-eqs-8-10-time-sliced-worldline-action-is-flat-action-plus-one-linear-gravitational-insertion",
  supported_by @ "paper:paszko-2012-perturbative-path-integral-feynman-propagator-schwarzschild"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildSliceAction_of_velocities where
  formalizes @ "claim:every-nondegenerate-paszko-time-slice-is-exactly-step-size-times-the-continuum-weak-schwarzschild-worldline-lagrangian",
  caveat @ "claim:this-is-local-mesh-consistency-not-by-itself-a-general-sobolev-worldline-convergence-theorem"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildContinuumAction_firstOrder_integrand where
  formalizes @ "claim:the-continuum-interval-integrated-worldline-action-retains-the-exact-flat-plus-linear-source-mass-integrand-decomposition",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildWorldlineLagrangian_firstOrder"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildVolumeMeasure_absolutelyContinuous where
  formalizes @ "claim:paszko-eq-9-weak-schwarzschild-volume-density-defines-a-curved-measure-absolutely-continuous-with-respect-to-the-flat-reference-measure",
  supported_by @ "lean:Physlib.QFT.PathIntegral.CurvedMeasureDatum.volumeMeasure_absolutelyContinuous"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildContinuum_partition_eq_baseIntegral where
  formalizes @ "claim:paszko-weak-schwarzschild-density-defines-a-genuine-continuum-path-space-partition-functional-over-any-supplied-measurable-worldline-measure",
  supported_by @ "lean:Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.partition_eq_base_integral_density_smul",
  caveat @ "claim:the-theorem-installs-an-existing-continuum-path-measure-and-does-not-assert-existence-of-a-universal-flat-lebesgue-measure-on-infinite-dimensional-path-space"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedFourDimensionalGaussian_eq where
  formalizes @ "claim:paszko-eqs-11-and-14-four-dimensional-time-slice-gaussian-has-the-determinant-normalization-pi-over-b-squared-under-positive-feynman-regulator",
  supported_by @ "lean:GaussianFourier.integral_cexp_neg_mul_sum_add",
  caveat @ "claim:the-unregulated-oscillatory-gaussian-is-a-boundary-value-not-a-lebesgue-integral"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedProperTimeWeight_norm_lt_one where
  formalizes @ "claim:the-feynman-i-epsilon-prescription-is-strict-complex-action-damping-on-positive-proper-time",
  supported_by @ "lean:Physlib.QFT.PathIntegral.lorentzianKernel_norm_is_damping"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedProperTimeWeight_eq_nagaoNielsen where
  formalizes @ "claim:paszko-finite-i-epsilon-proper-time-weight-is-the-nagao-nielsen-complex-action-weight-with-imaginary-action-epsilon-times-lambda",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsen_eq_master"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildFockKernel_firstOrder where
  formalizes @ "claim:paszko-eq-33-parametrized-fock-kernel-is-affine-in-source-mass-after-first-order-truncation",
  supported_by @ "paper:paszko-2012-perturbative-path-integral-feynman-propagator-schwarzschild"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildFockKernel_sourceMassDerivative where
  formalizes @ "claim:paszko-eq-33-first-order-Fock-response-is-the-exact-real-source-mass-derivative-of-both-complex-components",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildFockKernel_sourceMassDifference"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwingerProperTimeTransform_schwarzschild_firstOrder where
  formalizes @ "claim:paszko-proper-time-transform-preserves-the-flat-plus-first-order-schwarzschild-fock-kernel-decomposition-under-bochner-integrability",
  supported_by @ "lean:MeasureTheory.integral_add",
  caveat @ "claim:integrability-is-explicit-and-linearity-of-a-divergent-formal-integral-is-not-assumed"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_re where
  formalizes @ "claim:paszko-eq-16-finite-epsilon-real-part-is-the-negative-cauchy-delta-regularization"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_im where
  supported_by @ "lean:ProbDistribution.normalized",
  formalizes @ "claim:paszko-eq-16-finite-epsilon-imaginary-part-is-the-regularized-principal-value-kernel"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_tendsto_boundaryValue where
  formalizes @ "claim:off-the-light-cone-paszko-eq-16-finite-epsilon-converges-pointwise-to-i-over-four-pi-squared-s",
  caveat @ "claim:this-is-the-ordinary-pointwise-sector-for-nonzero-s-the-real-delta-sector-is-proved-separately-and-the-full-principal-value-distribution-is-not-claimed"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_re_tendsto_delta where
  formalizes @ "claim:the-real-part-of-paszko-eq-16-with-reciprocal-feynman-regulator-converges-weakly-to-minus-one-over-four-pi-times-the-dirac-delta-on-the-light-cone",
  supported_by @ "lean:tendsto_integral_comp_smul_smul_of_integrable",
  caveat @ "claim:this-proves-the-cauchy-delta-sector-against-integrable-test-functions-continuous-at-zero-not-the-imaginary-principal-value-sector"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.retardedFeynmanDeltaRegulator_tendsto_distribution where
  formalizes @ "claim:the-translated-finite-feynman-cauchy-regulator-converges-on-every-complex-schwartz-test-to-the-retarded-light-cone-dirac-distribution",
  epistemic_status @ "risky",
  supported_by @ "lean:tendsto_integral_comp_smul_smul_of_integrable'",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.retardedDistribution_apply",
  caveat @ "claim:this-is-a-proved-one-dimensional-time-distribution-limit-at-fixed-radius-not-a-construction-of-a-global-curved-spacetime-green-operator"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.causalFeynmanDeltaRegulator_tendsto_pauliJordanDistribution where
  formalizes @ "claim:the-coulomb-weighted-difference-of-the-retarded-and-advanced-finite-feynman-regulators-converges-to-the-explicit-radial-pauli-jordan-schwartz-distribution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.retardedFeynmanDeltaRegulator_tendsto_distribution",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.advancedFeynmanDeltaRegulator_tendsto_distribution",
  caveat @ "claim:model-specific-radial-boundary-value-theorem-not-the-full-four-dimensional-principal-value-distribution-or-hadamard-wavefront-equality"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.complexErfc_neg_add where
  formalizes @ "claim:paszko-complex-erfc-reflection-identity-controls-the-paired-gaussian-tails-in-eqs-28-through-32",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.complexErf_neg"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.PaszkoRegularDomain.tanh_feynmanArtanhBoundary_re where
  formalizes @ "claim:on-the-regular-domain-of-paszko-eq-35-the-real-feynman-artanh-boundary-is-the-principal-inverse-of-tanh",
  caveat @ "claim:requires-the-explicit-principal-branch-ratio-to-lie-strictly-between-minus-one-and-one"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatFeynmanInvariantProfile_kg_chain where
  formalizes @ "claim:the-finite-epsilon-flat-feynman-profile-has-explicit-first-and-second-complex-derivatives-and-a-regulator-proportional-radial-klein-gordon-residual",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatFeynmanInvariantProfile_radialWave_residual",
  caveat @ "claim:the-homogeneous-equation-is-recovered-at-zero-regulator-away-from-the-light-cone"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatFeynmanInvariantProfile_radialWave_zero where
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatFeynmanInvariantProfile_radialWave_residual",
  formalizes @ "claim:the-zero-regulator-massless-feynman-profile-solves-the-homogeneous-four-dimensional-radial-wave-equation-away-from-the-light-cone"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_firstOrder where
  formalizes @ "claim:paszko-eq-35-nonlocal-massless-schwarzschild-feynman-propagator-is-flat-propagator-plus-first-order-source-response",
  supported_by @ "paper:paszko-2012-perturbative-path-integral-feynman-propagator-schwarzschild",
  caveat @ "claim:first-order-weak-field-result-not-an-exact-all-orders-schwarzschild-green-function"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_sourceMassDerivative where
  formalizes @ "claim:paszko-eq-35-gravitational-correction-is-the-exact-real-source-mass-derivative-of-both-complex-propagator-components",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_sourceMassDifference"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_tendsto_boundaryValue where
  formalizes @ "claim:off-the-light-cone-the-complete-first-order-paszko-eq-35-propagator-has-a-rigorous-epsilon-to-zero-boundary-value",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_tendsto_boundaryValue",
  caveat @ "claim:the-full-complex-light-cone-distribution-remains-outside-this-pointwise-theorem"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildPropagatorResponse_ne_zero where
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildPropagatorResponse_im",
  formalizes @ "claim:away-from-zero-time-separation-and-the-light-cone-the-schwarzschild-source-response-is-genuinely-nonzero"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildPropagatorResponse_not_translationInvariant where
  formalizes @ "claim:the-first-order-schwarzschild-response-is-not-translation-invariant-unlike-the-flat-feynman-kernel"

zil attach Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.paszkoSchwarzschild_complexAction_chain where
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedProperTimeWeight_norm_lt_one",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_firstOrder",
  supported_by @ "lean:Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildPropagatorResponse_ne_zero",
  formalizes @ "claim:paszko-weak-schwarzschild-geometry-regulated-proper-time-complex-action-and-nonlocal-first-order-propagator-form-one-chain",
  caveat @ "claim:finite-epsilon-boundary-value-used-instead-of-an-untyped-i-zero-principal-value-distribution"

zil_file_contract physlib.paszkoSchwarzschildFeynmanPropagator where
  promises "Paszko's perturbative path-integral evaluation of the massless scalar Feynman propagator in Schwarzschild spacetime: the existing isotropic weak-field metric specializes to Eq. 7; the exact Ricci-flat matrix contracts to R equals zero and removes the xi-R potential in Eq. 2; the weak density is installed on a supplied measurable continuum path-space measure and its partition is reduced to the base measure; finite time slicing gives the Eq. 8 action and Eq. 9 measure insertions, while every nonzero slice agrees exactly with the interval-integrated continuum worldline Lagrangian; the regulated four-dimensional Gaussian is evaluated with its determinant normalization; the complex erf and erfc reflection identities organize the paired Gaussian tails; the flat Fock kernel is the zero-imaginary-action Lorentzian kernel; finite i-epsilon is strict complex-action damping and has the exact Cauchy/principal-value real-imaginary split; the real Cauchy sector converges weakly to minus one over four pi times the Dirac delta against every integrable test function continuous at the light cone; translation of that approximate identity to the retarded and advanced light-cone times converges on every complex Schwartz test function to the corresponding actual Dirac distributions, and their Coulomb-weighted difference converges to the explicit radial Pauli-Jordan distribution; away from the light cone both the flat kernel and complete first-order Schwarzschild propagator have rigorous pointwise epsilon-to-zero boundary values; the Bochner-integrable proper-time transform preserves the first-order decomposition; the Eq. 33 Fock response and Eq. 35 closed propagator are exactly affine in M with exact finite differences and real source-mass derivatives on an explicit nonsingular principal-artanh domain, recover the flat kernel at M=0, respect endpoint/time/spatial symmetries, and carry a nonzero Feynman boundary-value response away from dt=0 and the light cone; the invariant flat profile has checked first and second complex derivatives, an exact finite-regulator Klein-Gordon residual, and a homogeneous zero-regulator equation away from the light cone."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QFT.PathIntegral.lorentzianKernel",
    "lean:Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldMetric4",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.schwarzschild_ricci_eq_zero"]
  forbids_substitutes ["an exact all-orders Schwarzschild propagator",
    "a massive or higher-spin propagator not evaluated in the cited paper",
    "an untyped identification of finite epsilon with the full distributional principal-value plus delta boundary value",
    "a universal translation-invariant Lebesgue measure on infinite-dimensional path space"]
  witnessed_by [Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakFieldMetric4_pointMass_eq,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildKleinGordonPotential_eq_massSq,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildContinuum_partition_eq_baseIntegral,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildSliceAction_of_velocities,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildContinuumAction_firstOrder_integrand,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildDiscretizedAction_firstOrder,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.weakSchwarzschildVolumeMeasure_absolutelyContinuous,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedFourDimensionalGaussian_eq,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedProperTimeWeight_norm_lt_one,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.regulatedProperTimeWeight_eq_nagaoNielsen,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildFockKernel_firstOrder,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildFockKernel_sourceMassDerivative,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwingerProperTimeTransform_schwarzschild_firstOrder,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_re,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_im,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_re_tendsto_delta,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.retardedFeynmanDeltaRegulator_tendsto_distribution,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.causalFeynmanDeltaRegulator_tendsto_pauliJordanDistribution,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatMasslessFeynmanPropagator_tendsto_boundaryValue,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.complexErfc_neg_add,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.PaszkoRegularDomain.tanh_feynmanArtanhBoundary_re,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatFeynmanInvariantProfile_kg_chain,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.flatFeynmanInvariantProfile_radialWave_zero,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_firstOrder,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_sourceMassDerivative,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildMasslessFeynmanPropagator_tendsto_boundaryValue,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildPropagatorResponse_ne_zero,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.schwarzschildPropagatorResponse_not_translationInvariant,
    Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator.paszkoSchwarzschild_complexAction_chain]

/- ZIL-END -/
