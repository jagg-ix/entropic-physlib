/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux
public import Physlib.SpaceAndTime.Space.Integrals.SphereZonal

/-!
# Finite Newton fields through one spherical screen

This module supplies the compositional layer required for a genuine one-screen finite-source
Gauss law. It defines the pointwise finite superposition of translated isolated Newton fields and
proves that, provided no source lies on the screen, its actual spherical flux is the sum of the
actual off-center single-source fluxes.

The normalized Newton kernel integrates to `2` for an interior source and `0` for an exterior
source. The geometric bridge is the proved pushforward of `volume.toSphere` on `S²` to `2π` times
Lebesgue measure on `[-1,1]`. Together they prove `NewtonSphereFluxLaw3` and make the finite-source
enclosing-screen conclusions unconditional apart from their displayed geometric hypotheses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux

open MeasureTheory
open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources
open
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00
open
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
open
  Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open
  Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-! ## A. Finite exterior field and screen regularity -/

/-- The pointwise superposition of the exterior fields of finitely many Newton point sources. -/
def finiteNewtonExteriorField3 {ι : Type*} [Fintype ι]
    (G : ℝ) (M : ι → ℝ) (x : ι → Space 3) (y : Space 3) : Space 3 :=
  ∑ i, isolatedNewtonExteriorField3At G (M i) (x i) y

/--
A positive-radius screen point cannot coincide with a source whose distance from the screen center
is different from the screen radius.
-/
lemma spherePoint_sub_source_ne_zero
    (center source : Space 3) (R : ℝ) (hR : 0 < R)
    (hsource : ‖source - center‖ ≠ R) (n : UnitSphere3) :
    center + R • n.1 - source ≠ 0 := by
  intro hzero
  have hpoint : center + R • n.1 = source := sub_eq_zero.mp hzero
  have hdisplacement : source - center = R • n.1 := by
    rw [← hpoint]
    abel
  apply hsource
  rw [hdisplacement, norm_smul, mem_sphere_zero_iff_norm.mp n.2, mul_one,
    Real.norm_eq_abs, abs_of_pos hR]

/--
The normal flux integrand of one translated point source is integrable whenever the source is not
on the spherical screen.
-/
lemma isolatedNewtonExteriorField3At_sphereFlux_integrable
    (G M R : ℝ) (center source : Space 3) (hR : 0 < R)
    (hsource : ‖source - center‖ ≠ R) :
    Integrable
      (fun n : UnitSphere3 =>
        R ^ 2 *
          inner ℝ
            (isolatedNewtonExteriorField3At G M source (center + R • n.1))
            n.1)
      (volume (α := Space 3)).toSphere := by
  have hfield :
      Continuous
        (fun n : UnitSphere3 =>
          isolatedNewtonExteriorField3At G M source (center + R • n.1)) := by
    have hval : Continuous (fun n : UnitSphere3 => (n.1 : Space 3)) :=
      continuous_subtype_val
    have hdisplacement :
        Continuous (fun n : UnitSphere3 => center + R • n.1 - source) :=
      by fun_prop
    rw [continuous_iff_continuousAt]
    intro n
    have hne : center + R • n.1 - source ≠ 0 :=
      spherePoint_sub_source_ne_zero center source R hR hsource n
    have hden : ‖center + R • n.1 - source‖ ^ 3 ≠ 0 :=
      pow_ne_zero 3 (norm_ne_zero_iff.mpr hne)
    have hcoefficient :
        ContinuousAt
          (fun n : UnitSphere3 => G * M / ‖center + R • n.1 - source‖ ^ 3) n :=
      continuousAt_const.div₀ (hdisplacement.norm.pow 3).continuousAt hden
    unfold isolatedNewtonExteriorField3At isolatedNewtonExteriorField3
    exact hcoefficient.smul hdisplacement.continuousAt
  have hintegrand :
      Continuous
        (fun n : UnitSphere3 =>
          R ^ 2 *
            inner ℝ
              (isolatedNewtonExteriorField3At G M source (center + R • n.1))
              n.1) := by
    fun_prop
  simpa using
    hintegrand.continuousOn.integrableOn_compact
      (μ := (volume (α := Space 3)).toSphere) isCompact_univ

/-! ## B. Actual flux linearity on one screen -/

/--
The actual spherical flux of a finite sum of fields is the sum of their fluxes, assuming the
individual normal integrands are integrable.
-/
lemma sphereFluxIntegral3At_finset_sum
    {ι : Type*} (s : Finset ι) (center : Space 3) (R : ℝ)
    (F : ι → Space 3 → Space 3)
    (hF : ∀ i ∈ s,
      Integrable
        (fun n : UnitSphere3 =>
          R ^ 2 * inner ℝ (F i (center + R • n.1)) n.1)
        (volume (α := Space 3)).toSphere) :
    sphereFluxIntegral3At center R (fun y => ∑ i ∈ s, F i y) =
      ∑ i ∈ s, sphereFluxIntegral3At center R (F i) := by
  unfold sphereFluxIntegral3At sphereSurfaceIntegral3
  simp_rw [sum_inner, Finset.mul_sum]
  exact integral_finsetSum s hF

/--
If no source lies on the screen, the actual flux of the finite superposed Newton field is exactly
the sum of the actual off-center single-source fluxes.
-/
lemma finiteNewtonExteriorField3_sphereFlux_decompose
    {ι : Type*} [Fintype ι] (G R : ℝ) (M : ι → ℝ)
    (x : ι → Space 3) (center : Space 3) (hR : 0 < R)
    (hboundary : ∀ i, ‖x i - center‖ ≠ R) :
    sphereFluxIntegral3At center R (finiteNewtonExteriorField3 G M x) =
      ∑ i, sphereFluxIntegral3At center R
        (isolatedNewtonExteriorField3At G (M i) (x i)) := by
  change sphereFluxIntegral3At center R
      (fun y => ∑ i, isolatedNewtonExteriorField3At G (M i) (x i) y) =
    ∑ i, sphereFluxIntegral3At center R
      (isolatedNewtonExteriorField3At G (M i) (x i))
  exact sphereFluxIntegral3At_finset_sum Finset.univ center R
    (fun i => isolatedNewtonExteriorField3At G (M i) (x i))
    (fun i _ => isolatedNewtonExteriorField3At_sphereFlux_integrable
      G (M i) R center (x i) hR (hboundary i))

/-! ## C. The isolated off-center analytic target -/

/-- The squared source-to-screen distance after reducing the angular
dependence to `t = ⟨u,n⟩`. -/
def offCenterNewtonRadicand (R r t : ℝ) : ℝ :=
  R ^ 2 + r ^ 2 - 2 * R * r * t

/-- The elementary primitive whose endpoint jump computes the off-center
Newton solid-angle integral. -/
def offCenterNewtonZonalPrimitive (R r t : ℝ) : ℝ :=
  (R * t - r) / Real.sqrt (offCenterNewtonRadicand R r t)

/-- The normalized one-variable Newton flux kernel. -/
def offCenterNewtonZonalKernel (R r t : ℝ) : ℝ :=
  R ^ 2 * (R - r * t) /
    Real.sqrt (offCenterNewtonRadicand R r t) ^ 3

/-- Away from the boundary case `r = R`, the angular radicand is strictly
positive throughout `[-1,1]`. -/
lemma offCenterNewtonRadicand_pos
    (R r t : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (hrt : r ≠ R)
    (ht : t ∈ Set.uIcc (-1 : ℝ) 1) :
    0 < offCenterNewtonRadicand R r t := by
  have ht' : -1 ≤ t ∧ t ≤ 1 := by
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    exact ht
  have hsquare : 0 < (R - r) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hrt.symm)
  have hnonneg : 0 ≤ 2 * R * r * (1 - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR.le) hr) (by linarith)
  rw [offCenterNewtonRadicand]
  nlinarith

/-- The reduced Newton kernel has the displayed elementary primitive. -/
lemma offCenterNewtonZonalPrimitive_hasDerivAt
    (R r t : ℝ) (hpos : 0 < offCenterNewtonRadicand R r t) :
    HasDerivAt (offCenterNewtonZonalPrimitive R r)
      (offCenterNewtonZonalKernel R r t) t := by
  have hrad : HasDerivAt (offCenterNewtonRadicand R r) (-2 * R * r) t := by
    unfold offCenterNewtonRadicand
    convert ((hasDerivAt_id' t).const_mul (2 * R * r)).const_sub
      (R ^ 2 + r ^ 2) using 1 <;> first | rfl | ring
  have hsqrt := hrad.sqrt hpos.ne'
  have hnum : HasDerivAt (fun s : ℝ => R * s - r) R t := by
    simpa only [mul_one] using ((hasDerivAt_id' t).const_mul R).sub_const r
  have hquot := hnum.div hsqrt (Real.sqrt_pos.2 hpos).ne'
  apply hquot.congr_deriv
  unfold offCenterNewtonZonalKernel
  have hsqrtSq : Real.sqrt (offCenterNewtonRadicand R r t) ^ 2 =
      offCenterNewtonRadicand R r t := Real.sq_sqrt hpos.le
  have hsqrtNe : Real.sqrt (offCenterNewtonRadicand R r t) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  field_simp [hsqrtNe]
  rw [hsqrtSq]
  unfold offCenterNewtonRadicand
  ring

lemma offCenterNewtonZonalKernel_intervalIntegrable
    (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (hrt : r ≠ R) :
    IntervalIntegrable (offCenterNewtonZonalKernel R r) volume (-1 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have htpos := offCenterNewtonRadicand_pos R r t hR hr hrt ht
  have hden : Real.sqrt (offCenterNewtonRadicand R r t) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (Real.sqrt_ne_zero'.mpr htpos)
  have hradCont : ContinuousAt (offCenterNewtonRadicand R r) t := by
    unfold offCenterNewtonRadicand
    fun_prop
  have hdenCont : ContinuousAt
      (fun s : ℝ => Real.sqrt (offCenterNewtonRadicand R r s) ^ 3) t :=
    hradCont.sqrt.pow 3
  exact ContinuousAt.continuousWithinAt
    ((by fun_prop : ContinuousAt (fun s : ℝ => R ^ 2 * (R - r * s)) t).div₀
      hdenCont hden)

/-- The complete one-variable calculus part of the off-center solid-angle
law.  The jump is `2` inside and `0` outside; multiplying by the azimuthal
factor `2π` gives `4π` and `0`, respectively. -/
lemma offCenterNewtonZonalKernel_intervalIntegral
    (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (hrt : r ≠ R) :
    (∫ t in (-1 : ℝ)..1, offCenterNewtonZonalKernel R r t) =
      if r < R then 2 else 0 := by
  have hpos : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      0 < offCenterNewtonRadicand R r t :=
    fun t ht => offCenterNewtonRadicand_pos R r t hR hr hrt ht
  have hderiv : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (offCenterNewtonZonalPrimitive R r)
        (offCenterNewtonZonalKernel R r t) t :=
    fun t ht => offCenterNewtonZonalPrimitive_hasDerivAt R r t (hpos t ht)
  have hint := offCenterNewtonZonalKernel_intervalIntegrable R r hR hr hrt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hminus : offCenterNewtonZonalPrimitive R r (-1) = -1 := by
    rw [offCenterNewtonZonalPrimitive, offCenterNewtonRadicand]
    have hsum : 0 < R + r := by linarith
    rw [show R ^ 2 + r ^ 2 - 2 * R * r * (-1) = (R + r) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hsum]
    field_simp
    ring
  rw [hminus]
  by_cases hin : r < R
  · rw [if_pos hin, offCenterNewtonZonalPrimitive, offCenterNewtonRadicand]
    rw [show R ^ 2 + r ^ 2 - 2 * R * r * 1 = (R - r) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (sub_pos.mpr hin)]
    field_simp
    ring
  · have hout : R < r := lt_of_le_of_ne (le_of_not_gt hin) hrt.symm
    rw [if_neg hin, offCenterNewtonZonalPrimitive, offCenterNewtonRadicand]
    rw [show R ^ 2 + r ^ 2 - 2 * R * r * 1 = (R - r) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_neg (sub_neg.mpr hout)]
    field_simp
    ring

lemma isolatedNewtonExteriorField3At_sphereFluxIntegrand_eq_zonal
    (G M R : ℝ) (center source : Space 3) (hR : 0 < R)
    (hsource : source - center ≠ 0) (hboundary : ‖source - center‖ ≠ R)
    (n : UnitSphere3) :
    R ^ 2 * inner ℝ
        (isolatedNewtonExteriorField3At G M source (center + R • n.1)) n.1 =
      G * M * offCenterNewtonZonalKernel R ‖source - center‖
        (inner ℝ (‖source - center‖⁻¹ • (source - center)) n.1) := by
  let d : Space 3 := source - center
  let r : ℝ := ‖d‖
  let u : Space 3 := r⁻¹ • d
  change R ^ 2 * inner ℝ
      (isolatedNewtonExteriorField3At G M source (center + R • n.1)) n.1 =
    G * M * offCenterNewtonZonalKernel R r (inner ℝ u n.1)
  have hr : 0 < r := norm_pos_iff.mpr hsource
  have hn : ‖(n.1 : Space 3)‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
  have hu : ‖u‖ = 1 := by
    change ‖r⁻¹ • d‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹ * r = 1
    exact inv_mul_cancel₀ hr.ne'
  have hdu : r • u = d := by
    simp [u, smul_smul, hr.ne']
  have hdisplacement : center + R • n.1 - source = R • n.1 - r • u := by
    rw [hdu]
    dsimp [d]
    abel
  have hnormSq : ‖R • n.1 - r • u‖ ^ 2 =
      offCenterNewtonRadicand R r (inner ℝ u n.1) := by
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, abs_of_pos hr, hn, hu,
      mul_one, inner_smul_left, inner_smul_right, conj_trivial]
    rw [real_inner_comm n.1 u]
    unfold offCenterNewtonRadicand
    ring
  have hdiff : R • n.1 - r • u ≠ 0 := by
    rw [← hdisplacement]
    exact spherePoint_sub_source_ne_zero center source R hR hboundary n
  have hradPos : 0 < offCenterNewtonRadicand R r (inner ℝ u n.1) := by
    rw [← hnormSq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hdiff)
  have hnorm : ‖R • n.1 - r • u‖ =
      Real.sqrt (offCenterNewtonRadicand R r (inner ℝ u n.1)) := by
    rw [← hnormSq, Real.sqrt_sq (norm_nonneg _)]
  unfold isolatedNewtonExteriorField3At isolatedNewtonExteriorField3
  rw [hdisplacement, hnorm]
  simp only [inner_smul_left, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hn,
    one_pow, mul_one, conj_trivial]
  unfold offCenterNewtonZonalKernel
  ring

/--
The complete off-center spherical flux law for a three-dimensional Newton point source.

The boundary case is excluded because the exterior field is singular where the source lies on the
screen. The proposition is inhabited below using the `S²` zonal pushforward theorem.
-/
def NewtonSphereFluxLaw3 : Prop :=
  ∀ (G M R : ℝ) (center source : Space 3), 0 < R →
    ‖source - center‖ ≠ R →
    sphereFluxIntegral3At center R
        (isolatedNewtonExteriorField3At G M source) =
      if ‖source - center‖ < R then 4 * Real.pi * G * M else 0

/-- The finite-radius off-centre Newton flux law, proved from the spherical-coordinate
pushforward and the elementary zonal kernel integral. -/
theorem newtonSphereFluxLaw3 : NewtonSphereFluxLaw3 := by
  intro G M R center source hR hboundary
  by_cases hcenter : source - center = 0
  · have hsource : source = center := sub_eq_zero.mp hcenter
    subst source
    simpa [hR] using isolatedNewtonExteriorField3At_sphereFlux G M R center hR
  · let r : ℝ := ‖source - center‖
    let u : Space 3 := r⁻¹ • (source - center)
    have hr : 0 < r := norm_pos_iff.mpr hcenter
    have hu : ‖u‖ = 1 := by
      change ‖r⁻¹ • (source - center)‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      change r⁻¹ * r = 1
      exact inv_mul_cancel₀ hr.ne'
    have hrBoundary : r ≠ R := by simpa [r] using hboundary
    have hint := offCenterNewtonZonalKernel_intervalIntegrable R r hR hr.le hrBoundary
    have hzonal := Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral
      u hu (offCenterNewtonZonalKernel R r) hint
    unfold sphereFluxIntegral3At sphereSurfaceIntegral3
    simp_rw [isolatedNewtonExteriorField3At_sphereFluxIntegrand_eq_zonal
      G M R center source hR hcenter hboundary]
    change (∫ n : UnitSphere3,
        G * M * offCenterNewtonZonalKernel R r (inner ℝ u n.1)
          ∂(volume : Measure (Space 3)).toSphere) = _
    rw [integral_const_mul, hzonal,
      offCenterNewtonZonalKernel_intervalIntegral R r hR hr.le hrBoundary]
    by_cases hin : r < R
    · rw [if_pos hin]
      change G * M * (2 * Real.pi * 2) =
        if ‖source - center‖ < R then 4 * Real.pi * G * M else 0
      rw [if_pos (by simpa [r] using hin)]
      ring
    · rw [if_neg hin]
      change G * M * (2 * Real.pi * 0) =
        if ‖source - center‖ < R then 4 * Real.pi * G * M else 0
      rw [if_neg (by simpa [r] using hin)]
      ring

/--
Under the off-center analytic law, a point source strictly inside a positive-radius spherical
screen contributes `4πGM`.
-/
lemma NewtonSphereFluxLaw3.inside
    (hflux : NewtonSphereFluxLaw3) (G M R : ℝ)
    (center source : Space 3) (hR : 0 < R)
    (hinside : ‖source - center‖ < R) :
    sphereFluxIntegral3At center R
        (isolatedNewtonExteriorField3At G M source) =
      4 * Real.pi * G * M := by
  rw [hflux G M R center source hR (ne_of_lt hinside), if_pos hinside]

/--
Under the off-center analytic law, a point source strictly outside a positive-radius spherical
screen contributes zero flux.
-/
lemma NewtonSphereFluxLaw3.outside
    (hflux : NewtonSphereFluxLaw3) (G M R : ℝ)
    (center source : Space 3) (hR : 0 < R)
    (houtside : R < ‖source - center‖) :
    sphereFluxIntegral3At center R
        (isolatedNewtonExteriorField3At G M source) = 0 := by
  rw [hflux G M R center source hR (ne_of_gt houtside),
    if_neg (not_lt_of_ge houtside.le)]

/-! ## D. Finite-source enclosing-screen theorem -/

/--
Every finite configuration strictly inside one positive-radius spherical screen has actual total
flux `4πG` times its total mass.
-/
lemma finiteNewtonExteriorField3_enclosingSphereFlux
    {ι : Type*} [Fintype ι] (G R : ℝ) (M : ι → ℝ)
    (x : ι → Space 3) (center : Space 3) (hR : 0 < R)
    (hinside : ∀ i, ‖x i - center‖ < R) :
    sphereFluxIntegral3At center R (finiteNewtonExteriorField3 G M x) =
      4 * Real.pi * G * finiteTotalMass M := by
  rw [finiteNewtonExteriorField3_sphereFlux_decompose G R M x center hR
    (fun i => ne_of_lt (hinside i))]
  simp_rw [newtonSphereFluxLaw3.inside G (M _) R center (x _) hR (hinside _)]
  rw [finiteTotalMass, Finset.mul_sum]

/-! ## E. Einstein-to-one-screen-to-entropic chain -/

/--
The distributional finite-source Einstein `00` equation, actual one-screen enclosing flux, and
total-mass entropic identities form one chain.

No arbitrary-surface divergence theorem or nonlinear multi-body Einstein solution is claimed.
-/
lemma finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain
    {ι : Type*} [Fintype ι] (S_R G ℏ c N R : ℝ)
    (M : ι → ℝ) (x : ι → Space 3) (center : Space 3)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : 0 < R)
    (hinside : ∀ i, ‖x i - center‖ < R)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    DistributionalWeakFieldEinstein00Equation3 G c
        (finiteNewtonPotentialDistribution3 G M x)
        (finitePointMassDistribution3 M x)
      ∧ sphereFluxIntegral3At center R (finiteNewtonExteriorField3 G M x) =
        4 * Real.pi * G * finiteTotalMass M
      ∧ Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
        (4 * Real.pi * G) • finitePointMassDistribution3 M x
      ∧ G * finiteTotalMass M / R ^ 2 =
        4 * Real.pi * finiteTotalMass M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
        Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hChain :=
    finiteNewtonPointSources_distributionalEinstein00_bitCount_chain
      S_R G ℏ c N R M x hℏ hc hG hR hbits
  exact ⟨hChain.1,
    finiteNewtonExteriorField3_enclosingSphereFlux G R M x center hR hinside,
    hChain.2.1, hChain.2.2.2.1, hChain.2.2.2.2.1, hChain.2.2.2.2.2⟩

/-! ## F. Independent Compton-cell coupling for finite source systems -/

/-- **[The inference-variance coupling reaches finite-source Gauss and Einstein
`00`].**  Tile the entanglement screen by Compton cells at the inference mass
`m = 1/σ₀²`.  The resulting `G`-free count fixes `G = ℏcσ₀⁴`; when every
source lies strictly inside that same screen, the existing finite-source theorem
then gives the actual spherical flux, distributional weak-field Einstein `00`
equation, Nagao--Nielsen horizon damping, and Einstein coupling in one chain.

The result remains a round-screen, finite-source, weak-field statement.  It does
not infer an arbitrary-surface divergence theorem, solve a nonlinear many-body
spacetime, or independently determine the numerical value of `σ₀`. -/
lemma comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain
    {ι : Type*} [Fintype ι] (S_R ℏ c σ₀ η : ℝ)
    (M : ι → ℝ) (x : ι → Space 3) (center : Space 3)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hσ : 0 < σ₀) (hη : 0 < η)
    (hinside : ∀ i, ‖x i - center‖ <
      entropicProperDistance (inferenceMass σ₀) c ℏ η) :
    let m := inferenceMass σ₀
    let R := entropicProperDistance m c ℏ η
    let N := comptonCellBits m c ℏ η
    let G := ℏ * c * σ₀ ^ 4
    G = sphereArea R * c ^ 3 / (ℏ * N)
      ∧ DistributionalWeakFieldEinstein00Equation3 G c
          (finiteNewtonPotentialDistribution3 G M x)
          (finitePointMassDistribution3 M x)
      ∧ sphereFluxIntegral3At center R (finiteNewtonExteriorField3 G M x) =
          4 * Real.pi * G * finiteTotalMass M
      ∧ Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
          (4 * Real.pi * G) • finitePointMassDistribution3 M x
      ∧ G * finiteTotalMass M / R ^ 2 =
          4 * Real.pi * finiteTotalMass M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
          Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
          8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  dsimp only
  have hm : 0 < inferenceMass σ₀ := by
    rw [inferenceMass]
    positivity
  have hR : 0 < entropicProperDistance (inferenceMass σ₀) c ℏ η :=
    entropicProperDistance_pos (inferenceMass σ₀) c ℏ η hm hc hℏ hη
  have hG : ℏ * c * σ₀ ^ 4 ≠ 0 := by positivity
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    ne_of_gt (Real.log_pos (schmidtNumber_gt_one η hη))
  have hArea :
      ℏ * c * σ₀ ^ 4 =
        sphereArea (entropicProperDistance (inferenceMass σ₀) c ℏ η) * c ^ 3 /
          (ℏ * comptonCellBits (inferenceMass σ₀) c ℏ η) :=
    (newtonG_from_positionVariance
      σ₀ c ℏ η hσ.ne' hc.ne' hℏ.ne' hlog).symm
  have hbits :
      comptonCellBits (inferenceMass σ₀) c ℏ η =
        holographicBits
          (sphereArea (entropicProperDistance (inferenceMass σ₀) c ℏ η))
          (ℏ * c * σ₀ ^ 4) ℏ c :=
    (holographicBits_eq_comptonCellBits_of_inferenceVariance
      c ℏ σ₀ η hσ.ne' hc.ne' hℏ.ne').symm
  exact ⟨hArea,
    finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain
      S_R (ℏ * c * σ₀ ^ 4) ℏ c
      (comptonCellBits (inferenceMass σ₀) c ℏ η)
      (entropicProperDistance (inferenceMass σ₀) c ℏ η)
      M x center hℏ.ne' hc.ne' hG hR hinside hbits⟩

end
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux

end
