/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux
meta import Zil

/-!
# Newton's shell theorem: the spherical average of the Newton potential kernel

For a uniform spherical shell of radius `R` centered at `center`, the surface integral of the
Newtonian potential kernel `1/‖source − y‖` over the shell is

  `∮_{‖y−center‖ = R} 1/‖source − y‖ dσ(y) = 4πR² / max(‖source − center‖, R)`,

i.e. the shell acts on an exterior point exactly as a point mass at its center (`4πR²/‖source−center‖`
for `‖source−center‖ > R`) and produces a constant interior potential (`4πR²/R = 4πR` for
`‖source−center‖ < R`). This is **Newton's shell theorem** — the mean-value form of the potential,
the `n`-dimensional harmonic mean value that the flux law `newtonSphereFluxLaw3` carries only in its
derivative's jump.

This is the potential-kernel (`−1/2`-power) companion of the proved flux-kernel (`−3/2`-power)
`offCenterNewtonZonalKernel_intervalIntegral`: it reuses the same law-of-cosines radicand
`offCenterNewtonRadicand`, the same `S²` zonal pushforward
`Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral`, and the same surface integral
`sphereSurfaceIntegral3`. The only new content is the elementary primitive
`−√(offCenterNewtonRadicand)/(R·r)` of the `1/√radicand` kernel, whose endpoint jump is `2/max(R,r)`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Space
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential

/-! ## A. The one-variable potential-kernel calculus -/

/-- The elementary primitive whose endpoint jump computes the off-center Newton potential
solid-angle integral: `−√(offCenterNewtonRadicand R r t)/(R·r)`. -/
def offCenterNewtonPotentialPrimitive (R r t : ℝ) : ℝ :=
  -(Real.sqrt (offCenterNewtonRadicand R r t) / (R * r))

/-- The normalized one-variable Newton potential kernel `1/√(offCenterNewtonRadicand R r t)`. -/
def offCenterNewtonPotentialKernel (R r t : ℝ) : ℝ :=
  (Real.sqrt (offCenterNewtonRadicand R r t))⁻¹

/-- The reduced Newton potential kernel has the displayed elementary primitive. -/
lemma offCenterNewtonPotentialPrimitive_hasDerivAt
    (R r t : ℝ) (hR : R ≠ 0) (hr : r ≠ 0) (hpos : 0 < offCenterNewtonRadicand R r t) :
    HasDerivAt (offCenterNewtonPotentialPrimitive R r)
      (offCenterNewtonPotentialKernel R r t) t := by
  have hrad : HasDerivAt (offCenterNewtonRadicand R r) (-2 * R * r) t := by
    unfold offCenterNewtonRadicand
    convert ((hasDerivAt_id' t).const_mul (2 * R * r)).const_sub (R ^ 2 + r ^ 2) using 1 <;>
      first | rfl | ring
  have hsqrt := hrad.sqrt hpos.ne'
  have hprim := (hsqrt.div_const (R * r)).neg
  apply hprim.congr_deriv
  unfold offCenterNewtonPotentialKernel
  have hsqrtNe : Real.sqrt (offCenterNewtonRadicand R r t) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  field_simp
  try ring

lemma offCenterNewtonPotentialKernel_intervalIntegrable
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrt : r ≠ R) :
    IntervalIntegrable (offCenterNewtonPotentialKernel R r) volume (-1 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have htpos := offCenterNewtonRadicand_pos R r t hR hr.le hrt ht
  have hden : Real.sqrt (offCenterNewtonRadicand R r t) ≠ 0 := Real.sqrt_ne_zero'.mpr htpos
  have hradCont : ContinuousAt (offCenterNewtonRadicand R r) t := by
    unfold offCenterNewtonRadicand; fun_prop
  exact ContinuousAt.continuousWithinAt (hradCont.sqrt.inv₀ hden)

/-- **[The potential solid-angle integral is `2/max`]** the endpoint jump of the primitive gives
`∫_{-1}^1 1/√(offCenterNewtonRadicand R r t) dt = 2/max(R,r)` — the continuous `1/max` structure of
Newton's shell theorem (compare the flux kernel's `if r<R then 2 else 0`). -/
@[zil_level physical_theorem]
lemma offCenterNewtonPotentialKernel_intervalIntegral
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrt : r ≠ R) :
    (∫ t in (-1 : ℝ)..1, offCenterNewtonPotentialKernel R r t) = 2 / max R r := by
  have hpos : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, 0 < offCenterNewtonRadicand R r t :=
    fun t ht => offCenterNewtonRadicand_pos R r t hR hr.le hrt ht
  have hderiv : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (offCenterNewtonPotentialPrimitive R r)
        (offCenterNewtonPotentialKernel R r t) t :=
    fun t ht => offCenterNewtonPotentialPrimitive_hasDerivAt R r t hR.ne' hr.ne' (hpos t ht)
  have hint := offCenterNewtonPotentialKernel_intervalIntegrable R r hR hr hrt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hminus : offCenterNewtonPotentialPrimitive R r (-1) = -((R + r) / (R * r)) := by
    rw [offCenterNewtonPotentialPrimitive, offCenterNewtonRadicand,
      show R ^ 2 + r ^ 2 - 2 * R * r * (-1) = (R + r) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < R + r)]
  have hplus : offCenterNewtonPotentialPrimitive R r 1 = -(|R - r| / (R * r)) := by
    rw [offCenterNewtonPotentialPrimitive, offCenterNewtonRadicand,
      show R ^ 2 + r ^ 2 - 2 * R * r * 1 = (R - r) ^ 2 by ring, Real.sqrt_sq_eq_abs]
  rw [hplus, hminus]
  rcases lt_or_ge r R with hin | hout
  · rw [abs_of_pos (sub_pos.mpr hin), max_eq_left hin.le]
    field_simp
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr hout), max_eq_right hout]
    field_simp
    ring

/-! ## B. Newton's shell theorem -/

/-- The Newton potential surface-integrand reduces to the one-variable zonal kernel through the law
of cosines. -/
@[zil_level physical_theorem]
lemma newtonPotentialShellIntegrand_eq_zonal
    (R : ℝ) (center source : Space 3) (hR : 0 < R)
    (hsource : source - center ≠ 0) (n : UnitSphere3) :
    (‖source - (center + R • n.1)‖)⁻¹ =
      offCenterNewtonPotentialKernel R ‖source - center‖
        (inner ℝ (‖source - center‖⁻¹ • (source - center)) n.1) := by
  set d : Space 3 := source - center with hd
  set r : ℝ := ‖d‖ with hrdef
  set u : Space 3 := r⁻¹ • d with hudef
  have hr : 0 < r := norm_pos_iff.mpr hsource
  have hn : ‖(n.1 : Space 3)‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hdu : r • u = d := by rw [hudef, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hdisp : source - (center + R • n.1) = -(R • n.1 - r • u) := by
    rw [hdu, hd]; abel
  have hnormSq : ‖R • n.1 - r • u‖ ^ 2 =
      offCenterNewtonRadicand R r (inner ℝ u n.1) := by
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, abs_of_pos hr, hn, hu,
      mul_one, inner_smul_left, inner_smul_right, conj_trivial]
    rw [real_inner_comm n.1 u]
    unfold offCenterNewtonRadicand
    ring
  have hnorm : ‖source - (center + R • n.1)‖ =
      Real.sqrt (offCenterNewtonRadicand R r (inner ℝ u n.1)) := by
    rw [hdisp, norm_neg, ← hnormSq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, offCenterNewtonPotentialKernel]

/-- **[Newton's shell theorem for the potential]** the surface integral of the Newton potential kernel
`1/‖source − y‖` over the radius-`R` sphere centered at `center` is `4πR²/max(‖source−center‖, R)` — the
shell acts as a point mass at its center for an exterior point and gives a constant interior potential.
The boundary case `‖source−center‖ = R` is excluded (singular integrand). -/
@[zil_level physical_theorem]
theorem newtonShellPotential3
    (R : ℝ) (center source : Space 3) (hR : 0 < R) (hboundary : ‖source - center‖ ≠ R) :
    sphereSurfaceIntegral3 R (fun n => (‖source - (center + R • n.1)‖)⁻¹) =
      4 * Real.pi * R ^ 2 / max ‖source - center‖ R := by
  by_cases hcenter : source - center = 0
  · have hnc : ∀ n : UnitSphere3, (‖source - (center + R • n.1)‖)⁻¹ = R⁻¹ := by
      intro n
      have hn : ‖(n.1 : Space 3)‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
      have hsn : source - (center + R • n.1) = -(R • n.1) := by
        rw [sub_eq_zero] at hcenter; rw [hcenter]; abel
      rw [hsn, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hn, mul_one]
    rw [show (fun n : UnitSphere3 => (‖source - (center + R • n.1)‖)⁻¹) = fun _ => R⁻¹ from
        funext hnc, sphereSurfaceIntegral3_const, sphereArea]
    rw [sub_eq_zero.mp hcenter, sub_self, norm_zero, max_eq_right hR.le]
    field_simp
    try ring
  · set r : ℝ := ‖source - center‖ with hrdef
    set u : Space 3 := r⁻¹ • (source - center) with hudef
    have hr : 0 < r := norm_pos_iff.mpr hcenter
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact inv_mul_cancel₀ hr.ne'
    have hrBoundary : r ≠ R := hboundary
    have hint := offCenterNewtonPotentialKernel_intervalIntegrable R r hR hr hrBoundary
    have hzonal := Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral
      u hu (offCenterNewtonPotentialKernel R r) hint
    have hmax : 0 < max r R := lt_of_lt_of_le hr (le_max_left r R)
    unfold sphereSurfaceIntegral3
    simp_rw [newtonPotentialShellIntegrand_eq_zonal R center source hR hcenter]
    change (∫ n : UnitSphere3,
        R ^ 2 * offCenterNewtonPotentialKernel R r (inner ℝ u n.1)
          ∂(volume : Measure (Space 3)).toSphere) = _
    rw [integral_const_mul, hzonal,
      offCenterNewtonPotentialKernel_intervalIntegral R r hR hr hrBoundary, max_comm R r]
    field_simp
    try ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential

end

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.newtonShellPotential3 where
  formalizes @ "claim:newtons-shell-theorem-for-the-potential-the-surface-integral-of-the-newton-potential-kernel-one-over-norm-source-minus-y-over-the-radius-r-sphere-centered-at-center-equals-four-pi-r-squared-over-max-of-norm-source-minus-center-and-r-the-shell-acts-as-a-point-mass-at-its-center-for-an-exterior-point-and-a-constant-interior-potential",
  supported_by @ "lean:Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonRadicand_pos",
  caveat @ "claim:the-boundary-case-norm-source-minus-center-equals-r-is-excluded-because-the-integrand-is-singular-there-and-this-is-the-single-shell-average-not-yet-integrated-over-a-radial-density-profile"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.offCenterNewtonPotentialKernel_intervalIntegral where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.offCenterNewtonPotentialKernel_intervalIntegrable",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.offCenterNewtonPotentialPrimitive_hasDerivAt",
  formalizes @ "claim:the-one-variable-newton-potential-solid-angle-integral-of-one-over-sqrt-radicand-from-minus-one-to-one-equals-two-over-max-r-r-the-continuous-one-over-max-structure-of-newtons-shell-theorem"

zil_file_contract physlib.newtonShellPotential where
  promises "Newton's shell theorem for the gravitational potential: newtonShellPotential3 proves that the surface integral of the Newton potential kernel 1/norm(source - y) over the radius-R sphere centered at center equals 4 pi R^2 / max(norm(source - center), R). The shell acts on an exterior point (norm(source-center) > R) exactly as a point mass 4 pi R^2 / norm(source-center) at its center, and produces a constant interior potential 4 pi R^2 / R = 4 pi R (norm(source-center) < R); the boundary case norm(source-center) = R is excluded (singular integrand). This is the n-dimensional harmonic mean-value / spherical average of the Newton kernel, the potential-kernel companion of the flux-form shell law newtonSphereFluxLaw3. It reuses the law-of-cosines radicand offCenterNewtonRadicand and its positivity, the S^2 zonal pushforward Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral, and the R^2-Jacobian surface integral sphereSurfaceIntegral3; the only new content is the elementary primitive -sqrt(offCenterNewtonRadicand)/(R r) of the 1/sqrt(radicand) kernel, whose endpoint jump gives the solid-angle integral offCenterNewtonPotentialKernel_intervalIntegral = 2/max(R,r). Honest: this is the single-shell average; integrating it over a radial density profile radialBallMass to obtain the full varying-density potential is a further step."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonRadicand",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonRadicand_pos",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereSurfaceIntegral3"]
  forbids_substitutes ["the flux-form shell law alone, whose 1/max structure appears only as the derivative's inside/outside jump, whereas this exposes the continuous 4 pi R^2/max potential",
    "a point-source kernel, whereas this is the genuine surface average over a shell of positive radius R"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.offCenterNewtonPotentialKernel_intervalIntegral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.newtonPotentialShellIntegrand_eq_zonal,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.newtonShellPotential3]

/- ZIL-END -/
