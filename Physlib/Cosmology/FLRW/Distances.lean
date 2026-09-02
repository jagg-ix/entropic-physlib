/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
public import Physlib.Cosmology.FLRW.ConformalTime
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!

# Distances and redshift in FLRW cosmology

Distances and redshift in FLRW cosmology.  Formalized here: the Hubble radius
`R_H = c/H` and the recession-velocity law (`recession_at_hubbleRadius`,
`v = c` there), the proper distance `D = a·χ` with the Hubble–Lemaître law
`Ḋ = H·D` (`hubbleLemaitre`), the redshift `1 + z = a₀/a` (`onePlusRedshift`),
the transverse comoving distance through the existing `SpatialGeometry.S`
(`transverseComoving_flat`), and the observational distances with **Etherington's
distance-duality relation** `d_L = (1+z)²d_A` (`etherington_duality`).  §D adds the
integral notions: the line-of-sight comoving distance `χ = c·η` (via
`ConformalTime.conformalTime`), the particle and event horizons, and the
redshift-space comoving distance with the **low-`z` (Hubble-law) leading
coefficient** `χ′(0) = c/H₀` and the **`q₀` second-order coefficient**
`χ″(0) = −c(1+q₀)/H₀`.  §E adds the lookback time and its leading `z/H₀` term.

-/

@[expose] public section


namespace Cosmology.FLRW.Distances

open Time
open Cosmology
open Cosmology.FLRW.FriedmannEquation
open Cosmology.FLRW.ConformalTime
open MeasureTheory

/-- **The Hubble radius** `R_H = c/H` — the proper distance at which the
Hubble–Lemaître recession velocity equals the speed of light. -/
noncomputable def hubbleRadius (c H : ℝ) : ℝ := c / H

/-- **The recession velocity** `v = H·D` of a source at proper distance `D`
(Hubble–Lemaître law). -/
noncomputable def recessionVelocity (H D : ℝ) : ℝ := H * D

/-- **[The recession velocity equals `c` at the Hubble radius]** `v(R_H) = c`. -/
theorem recession_at_hubbleRadius (c H : ℝ) (hH : H ≠ 0) :
    recessionVelocity H (hubbleRadius c H) = c := by
  unfold recessionVelocity hubbleRadius
  field_simp

/-- **The proper distance** `D = a·χ` to a source at fixed comoving distance `χ`. -/
noncomputable def properDistance (a : Time → ℝ) (χ : ℝ) : Time → ℝ :=
  fun t => a t * χ

/-- **[The Hubble–Lemaître law] `Ḋ = H·D`.** At fixed comoving distance the proper
distance recedes at the Hubble rate: `∂ₜ(aχ) = χ·ȧ = (ȧ/a)(aχ) = H·D`. -/
theorem hubbleLemaitre (a : Time → ℝ) (χ : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (haz : a t ≠ 0) :
    ∂ₜ (properDistance a χ) t = hubbleConstant a t * properDistance a χ t := by
  unfold properDistance
  rw [show (fun t => a t * χ) = (fun t => χ * a t) from by funext s; ring,
    Time.deriv_const_mul χ t ha]
  simp only [hubbleConstant]
  field_simp

/-- **The redshift** `z = a₀/a − 1` of light emitted at scale factor `a` and
observed at `a₀`. -/
noncomputable def redshift (a₀ a : ℝ) : ℝ := a₀ / a - 1

/-- **[`1 + z = a₀/a`]** the standard redshift–scale-factor relation. -/
theorem onePlusRedshift (a₀ a : ℝ) : 1 + redshift a₀ a = a₀ / a := by
  unfold redshift; ring

/-- **[The photon energy redshifts as `1/a`]** `E_obs/E_emit = a_emit/a_obs = 1/(1+z)`
— the cosmological redshift of a photon's energy, expressed through
`onePlusRedshift`. -/
theorem photonEnergy_redshift (a₀ a Eemit : ℝ) (ha₀ : a₀ ≠ 0) :
    Eemit / (1 + redshift a₀ a) = Eemit * a / a₀ := by
  rw [onePlusRedshift]
  field_simp

/-- **The transverse comoving distance** `r(χ) = S(χ)` — the curvature-corrected
angular distance, via the existing FLRW spatial-geometry function
`SpatialGeometry.S`. -/
noncomputable def transverseComoving (s : SpatialGeometry) (χ : ℝ) : ℝ :=
  SpatialGeometry.S s χ

/-- **[Flat transverse comoving distance] `r(χ) = χ`.** In a spatially flat
universe the transverse comoving distance is the line-of-sight comoving distance
itself. -/
theorem transverseComoving_flat (χ : ℝ) :
    transverseComoving SpatialGeometry.Flat χ = χ := rfl

/-- **The luminosity distance** `d_L = (1+z)·r`. -/
noncomputable def luminosityDistance (z r : ℝ) : ℝ := (1 + z) * r

/-- **The angular-diameter distance** `d_A = r/(1+z)`. -/
noncomputable def angularDiameterDistance (z r : ℝ) : ℝ := r / (1 + z)

/-- **[Etherington's distance-duality relation] `d_L = (1+z)²·d_A`.**  A purely
kinematic identity (reciprocity theorem): valid for any metric theory with photon
number conservation, independent of the cosmological dynamics. -/
theorem etherington_duality (z r : ℝ) (hz : 1 + z ≠ 0) :
    luminosityDistance z r = (1 + z) ^ 2 * angularDiameterDistance z r := by
  unfold luminosityDistance angularDiameterDistance
  field_simp


/-! ## §D — the comoving distance, horizons, and low-`z` expansion -/

/-- **The line-of-sight comoving distance** `χ = c·η = c∫dt/a` — the conformal time
of `ConformalTime` scaled by the speed of light (leveraged, not re-derived). -/
noncomputable def comovingDistance (A : ℝ → ℝ) (t₀ c t : ℝ) : ℝ :=
  c * conformalTime A t₀ t

/-- **[`χ′ = c/a`]** the comoving distance grows at rate `c/a` in cosmic time — the
scaled fundamental theorem of calculus of `conformalTime_hasDerivAt`. -/
theorem comovingDistance_hasDerivAt (A : ℝ → ℝ) (t₀ c t : ℝ)
    (hA : Continuous A) (hAz : ∀ s, A s ≠ 0) :
    HasDerivAt (comovingDistance A t₀ c) (c / A t) t := by
  have h := (conformalTime_hasDerivAt A t₀ t hA hAz).const_mul c
  rw [mul_one_div] at h
  exact h

/-- **The particle (comoving) horizon** `χ_p(t) = c∫₀ᵗ dt'/a` — the comoving
distance light has travelled since the initial singularity `t = 0`. -/
noncomputable def particleHorizonAt (A : ℝ → ℝ) (c t : ℝ) : ℝ :=
  comovingDistance A 0 c t

/-- **[The particle horizon grows at `c/a`]** its cosmic-time derivative is `c/a`. -/
theorem particleHorizon_hasDerivAt (A : ℝ → ℝ) (c t : ℝ)
    (hA : Continuous A) (hAz : ∀ s, A s ≠ 0) :
    HasDerivAt (particleHorizonAt A c) (c / A t) t :=
  comovingDistance_hasDerivAt A 0 c t hA hAz

/-- **The event horizon** `χ_e(t) = c∫_t^∞ dt'/a` — the comoving distance beyond
which light emitted now can never reach us (an improper integral over `(t, ∞)`). -/
noncomputable def eventHorizon (A : ℝ → ℝ) (c t : ℝ) : ℝ :=
  c * ∫ s in Set.Ioi t, 1 / A s

/-- **[The event horizon is nonnegative]** for a positive scale factor and
`c ≥ 0` the event horizon is `≥ 0` (the improper integral of a nonnegative
integrand). -/
theorem eventHorizon_nonneg (A : ℝ → ℝ) (c t : ℝ) (hc : 0 ≤ c)
    (hA : ∀ s, 0 < A s) : 0 ≤ eventHorizon A c t :=
  mul_nonneg hc (integral_nonneg (fun s => div_nonneg zero_le_one (hA s).le))

/-- **The redshift-space comoving distance** `χ(z) = c∫₀ᶻ dz'/H(z')`. -/
noncomputable def comovingDistanceRedshift (H : ℝ → ℝ) (c z : ℝ) : ℝ :=
  c * ∫ zp in (0 : ℝ)..z, 1 / H zp

/-- **[`dχ/dz = c/H`]** the redshift-space comoving distance grows at `c/H(z)` —
the fundamental theorem of calculus in redshift space. -/
theorem comovingDistanceRedshift_hasDerivAt (H : ℝ → ℝ) (c z : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0) :
    HasDerivAt (comovingDistanceRedshift H c) (c / H z) z := by
  have hcont : Continuous (fun zp => 1 / H zp) := continuous_const.div hH hHz
  have hI := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 z) (hcont.stronglyMeasurableAtFilter _ _)
    hcont.continuousAt
  have h := hI.const_mul c
  rw [mul_one_div] at h
  exact h

/-- **[The Hubble law is the leading low-`z` coefficient] `χ′(0) = c/H₀`.**
`χ(z) = (c/H₀)·z + O(z²)` — the linear Hubble–Lemaître distance–redshift relation
is the derivative of the comoving distance at zero redshift. -/
theorem comovingDistance_hubbleLaw (H : ℝ → ℝ) (c : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0) :
    deriv (comovingDistanceRedshift H c) 0 = c / H 0 :=
  (comovingDistanceRedshift_hasDerivAt H c 0 hH hHz).deriv

/-- **[The `q₀` second-order coefficient] `χ″(0) = −c(1+q₀)/H₀`.**  With the Hubble
function satisfying `H′(0) = H₀(1 + q₀)` (the definition of the deceleration
parameter at present), the second Taylor coefficient of the comoving distance is
`−c(1+q₀)/H₀`, so `χ(z) = (c/H₀)[z − ½(1+q₀)z² + …]` — the low-redshift expansion in
powers of `z` with the deceleration parameter in its coefficient. -/
theorem comovingDistanceRedshift_secondDeriv_zero (H : ℝ → ℝ) (c H₀ q₀ : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0)
    (hHderiv : HasDerivAt H (H₀ * (1 + q₀)) 0) (hH0 : H 0 = H₀) (hH0z : H₀ ≠ 0) :
    deriv (deriv (comovingDistanceRedshift H c)) 0 = -(c * (1 + q₀) / H₀) := by
  have hderiv1 : deriv (comovingDistanceRedshift H c) = fun z => c / H z :=
    funext fun z => (comovingDistanceRedshift_hasDerivAt H c z hH hHz).deriv
  rw [hderiv1]
  have hne : H 0 ≠ 0 := hH0 ▸ hH0z
  have hd : HasDerivAt (fun z => c / H z)
      (c * (-(H₀ * (1 + q₀)) / (H 0) ^ 2)) 0 := by
    have h := (hHderiv.inv hne).const_mul c
    simpa [div_eq_mul_inv] using h
  rw [hd.deriv, hH0]
  field_simp

/-- **The redshift-space luminosity distance** `d_L(z) = (1+z)·χ(z)` (spatially
flat, `r = χ`). -/
noncomputable def luminosityDistanceRedshift (H : ℝ → ℝ) (c z : ℝ) : ℝ :=
  (1 + z) * comovingDistanceRedshift H c z

/-- **The redshift-space angular-diameter distance** `d_A(z) = χ(z)/(1+z)`. -/
noncomputable def angularDiameterDistanceRedshift (H : ℝ → ℝ) (c z : ℝ) : ℝ :=
  comovingDistanceRedshift H c z / (1 + z)

/-- **[The luminosity distance obeys the Hubble law at leading order]
`d_L′(0) = c/H₀`.**  Since `χ(0) = 0`, `d_L(z) = (1+z)χ(z)` has the same linear
distance–redshift slope `c/H₀` as the comoving distance. -/
theorem luminosityDistance_hubbleLaw (H : ℝ → ℝ) (c : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0) :
    deriv (luminosityDistanceRedshift H c) 0 = c / H 0 := by
  have hchi0 : comovingDistanceRedshift H c 0 = 0 := by
    simp [comovingDistanceRedshift, intervalIntegral.integral_same]
  have h : HasDerivAt (luminosityDistanceRedshift H c)
      (1 * comovingDistanceRedshift H c 0 + (1 + 0) * (c / H 0)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add 1).mul
      (comovingDistanceRedshift_hasDerivAt H c 0 hH hHz)
  rw [h.deriv, hchi0]; ring

/-- **[The angular-diameter distance obeys the Hubble law at leading order]
`d_A′(0) = c/H₀`.**  At low redshift `d_L`, `d_A` and `χ` share the linear
Hubble–Lemaître slope `c/H₀`; they diverge only at the `q₀` (second) order. -/
theorem angularDiameterDistance_hubbleLaw (H : ℝ → ℝ) (c : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0) :
    deriv (angularDiameterDistanceRedshift H c) 0 = c / H 0 := by
  have hchi0 : comovingDistanceRedshift H c 0 = 0 := by
    simp [comovingDistanceRedshift, intervalIntegral.integral_same]
  have h : HasDerivAt (angularDiameterDistanceRedshift H c)
      ((c / H 0 * (1 + 0) - comovingDistanceRedshift H c 0 * 1) / (1 + 0) ^ 2) 0 :=
    (comovingDistanceRedshift_hasDerivAt H c 0 hH hHz).div
      ((hasDerivAt_id (0 : ℝ)).const_add 1) (by norm_num)
  rw [h.deriv, hchi0]; norm_num

/-- **[The `q₀` second-order coefficient of the luminosity distance]
`d_L″(0) = c(1−q₀)/H₀`.**  With `H′(0) = H₀(1+q₀)`,
`d_L(z) = (c/H₀)[z + ½(1−q₀)z² + …]` — the standard low-redshift Hubble diagram
expansion with the deceleration parameter in its coefficient. -/
theorem luminosityDistanceRedshift_secondDeriv_zero (H : ℝ → ℝ) (c H₀ q₀ : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0)
    (hHderiv : HasDerivAt H (H₀ * (1 + q₀)) 0) (hH0 : H 0 = H₀) (hH0z : H₀ ≠ 0) :
    deriv (deriv (luminosityDistanceRedshift H c)) 0 = c * (1 - q₀) / H₀ := by
  have hne : H 0 ≠ 0 := hH0 ▸ hH0z
  have hderiv : deriv (luminosityDistanceRedshift H c)
      = fun z => 1 * comovingDistanceRedshift H c z + (1 + z) * (c / H z) := by
    funext z
    exact (((hasDerivAt_id z).const_add 1).mul
      (comovingDistanceRedshift_hasDerivAt H c z hH hHz)).deriv
  rw [hderiv]
  have hG' : HasDerivAt (fun z => c / H z) (c * (-(H₀ * (1 + q₀)) / (H 0) ^ 2)) 0 := by
    have h := (hHderiv.inv hne).const_mul c
    simpa [div_eq_mul_inv] using h
  have hsum : HasDerivAt
      (fun z => 1 * comovingDistanceRedshift H c z + (1 + z) * (c / H z))
      (1 * (c / H 0) + (1 * (c / H 0)
        + (1 + 0) * (c * (-(H₀ * (1 + q₀)) / (H 0) ^ 2)))) 0 :=
    ((comovingDistanceRedshift_hasDerivAt H c 0 hH hHz).const_mul 1).add
      (((hasDerivAt_id (0 : ℝ)).const_add 1).mul hG')
  rw [hsum.deriv, hH0]
  field_simp
  ring

/-- **[The `q₀` second-order coefficient of the angular-diameter distance]
`d_A″(0) = −c(3+q₀)/H₀`.**  `d_A(z) = (c/H₀)[z − ½(3+q₀)z² + …]` — the
angular-diameter distance turns over at high redshift (its `z²` coefficient is the
most negative of the three), the geometric root of the `d_A` maximum. -/
theorem angularDiameterDistanceRedshift_secondDeriv_zero (H : ℝ → ℝ) (c H₀ q₀ : ℝ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0)
    (hHderiv : HasDerivAt H (H₀ * (1 + q₀)) 0) (hH0 : H 0 = H₀) (hH0z : H₀ ≠ 0) :
    deriv (deriv (angularDiameterDistanceRedshift H c)) 0 = -(c * (3 + q₀) / H₀) := by
  have hne : H 0 ≠ 0 := hH0 ▸ hH0z
  set φ : ℝ → ℝ :=
    fun z => (c / H z * (1 + z) - comovingDistanceRedshift H c z) / (1 + z) ^ 2 with hφ
  -- deriv d_A agrees with φ on a neighborhood of 0 (where 1 + z ≠ 0)
  have hev : deriv (angularDiameterDistanceRedshift H c) =ᶠ[nhds 0] φ := by
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with z hz
    have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
    have h : HasDerivAt (angularDiameterDistanceRedshift H c)
        ((c / H z * (1 + z) - comovingDistanceRedshift H c z * 1) / (1 + z) ^ 2) z :=
      (comovingDistanceRedshift_hasDerivAt H c z hH hHz).div
        ((hasDerivAt_id z).const_add 1) hz1
    rw [h.deriv, hφ]
    ring_nf
  rw [Filter.EventuallyEq.deriv_eq hev]
  -- compute deriv φ 0 with the numerator N and denominator (1+z)²
  have hG' : HasDerivAt (fun z => c / H z) (c * (-(H₀ * (1 + q₀)) / (H 0) ^ 2)) 0 := by
    have h := (hHderiv.inv hne).const_mul c
    simpa [div_eq_mul_inv] using h
  have hchi0 : comovingDistanceRedshift H c 0 = 0 := by
    simp [comovingDistanceRedshift, intervalIntegral.integral_same]
  have hN : HasDerivAt (fun z => c / H z * (1 + z) - comovingDistanceRedshift H c z)
      ((c * (-(H₀ * (1 + q₀)) / (H 0) ^ 2)) * (1 + 0) + (c / H 0) * 1 - (c / H 0)) 0 :=
    (hG'.mul ((hasDerivAt_id (0 : ℝ)).const_add 1)).sub
      (comovingDistanceRedshift_hasDerivAt H c 0 hH hHz)
  have hD : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + 0) ^ 1 * 1) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2
  have hφd : HasDerivAt φ
      ((((c * (-(H₀ * (1 + q₀)) / (H 0) ^ 2)) * (1 + 0) + (c / H 0) * 1 - (c / H 0))
          * (1 + 0) ^ 2
        - (c / H 0 * (1 + 0) - comovingDistanceRedshift H c 0) * (2 * (1 + 0) ^ 1 * 1))
        / ((1 + 0) ^ 2) ^ 2) 0 :=
    hN.div hD (by norm_num)
  rw [hφd.deriv, hH0, hchi0]
  field_simp
  ring

/-! ## §E — the lookback time -/

/-- **The lookback time** `t₀ − t` — how long ago light observed now was emitted. -/
noncomputable def lookbackTime (t₀ t : ℝ) : ℝ := t₀ - t

/-- **[`d(lookback)/dt = −1`]** the lookback time decreases with emission time. -/
theorem lookbackTime_hasDerivAt (t₀ t : ℝ) :
    HasDerivAt (lookbackTime t₀) (-1) t :=
  (hasDerivAt_id t).const_sub t₀

/-- **[`d(lookback)/dt = −1`]** the lookback time to an event decreases with the
event's emission time. -/
theorem lookbackTime_deriv (t₀ t : ℝ) : deriv (lookbackTime t₀) t = -1 :=
  (lookbackTime_hasDerivAt t₀ t).deriv

end Cosmology.FLRW.Distances

