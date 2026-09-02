/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.Basic
public import Physlib.QFT.ConformalWelding.MatterLiouvilleGhostFactorization
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularAdS
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra -/

/-!
# Algebraic identities for the Ryu-Takayanagi area formula

This module records algebraic and pointwise continuum formulae that appear in the
Ryu-Takayanagi setting: `area / (4 * G)`, the Brown-Henneaux prefactor
`3 * R / (2 * G)`, the Poincaré-half-plane line density pulled back along the
semicircular interval geodesic, a logarithm identity for the cutoff expression,
and invariance of that area expression under the existing modular-AdS
norm-square identity.

It does not construct a CFT density matrix, prove global length minimality of the
semicircle, evaluate the improper endpoint limit, or derive the RT proposal
from a bulk path integral. It does prove the actual pointwise continuum metric
integrand and evaluate its finite-cutoff interval integral, rather than merely
relabeling the final logarithm.  It also removes the universal logarithmic
divergence and proves the resulting finite renormalized cutoff limit, proves
the adjacent-interval strong-subadditivity inequality for the vacuum-line
entropy, and derives the zero-temperature limit of the BTZ expression.
-/

set_option autoImplicit false
open scoped Topology

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra

open Real
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularAdS
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum


/-- **[Ryu–Takayanagi Eq. 1.5] The RT area expression** `S_A = Area(γ_A) / (4 G_N)` — the
Bekenstein–Hawking form (Eq. 1.1) of the area expression, the area of the minimal bulk surface `γ_A`
over `4 G_N`. -/
noncomputable def rtAreaEntropy (area G : ℝ) : ℝ := area / (4 * G)

/-- **[Eq. 2.1] The Brown–Henneaux central charge** `c = 3R/(2G)` of `AdS₃`. -/
noncomputable def brownHenneaux (R G : ℝ) : ℝ := 3 * R / (2 * G)

/-- The area expression is non-negative (the area is non-negative). -/
lemma rtAreaEntropy_nonneg (area G : ℝ) (ha : 0 ≤ area) (hG : 0 < G) :
    0 ≤ rtAreaEntropy area G := by
  unfold rtAreaEntropy; positivity

/-- `c/3 = R/2G` — the central-charge prefactor of the CFT area expression. -/
lemma brownHenneaux_third (R G : ℝ) (hG : G ≠ 0) : brownHenneaux R G / 3 = R / (2 * G) := by
  unfold brownHenneaux; field_simp


/-- **[Calabrese–Cardy Eq. 1.3] The CFT₂ area expression** `S_A = (c/3) log((L/πa) sin(πl/L))`. -/
noncomputable def cftEntropy (c l L a : ℝ) : ℝ :=
  (c / 3) * Real.log (L / (π * a) * Real.sin (π * l / L))

/-- **[Ryu–Takayanagi Eqs. 2.4–2.5 → 1.3] The geodesic-length entropy reproduces the CFT result.** In the
large-cutoff limit the the following logarithm expression satisfies `S_A = (R/4G) log(e^{2ρ₀} sin²(πl/L))`, which equals
the Calabrese–Cardy `(c/3) log(e^{ρ₀} sin(πl/L))` with `c = 3R/2G` — the area-formula derivation of the
area expression. -/
@[zil_level bridge_theorem]
lemma rt_log_square_prefactor_identity (R G ρ₀ l L : ℝ) (hG : G ≠ 0) :
    rtAreaEntropy (R * Real.log (Real.exp (2 * ρ₀) * Real.sin (π * l / L) ^ 2)) G
      = (brownHenneaux R G / 3) * Real.log (Real.exp ρ₀ * Real.sin (π * l / L)) := by
  unfold rtAreaEntropy brownHenneaux
  rw [show Real.exp (2 * ρ₀) * Real.sin (π * l / L) ^ 2
        = (Real.exp ρ₀ * Real.sin (π * l / L)) ^ 2 by
    rw [mul_pow]; congr 1; rw [two_mul, Real.exp_add, sq]]
  rw [Real.log_pow]
  push_cast; field_simp; ring

/-! ## §C — the continuum Poincaré-semicircle line element -/

/-- The horizontal coordinate of the standard Poincaré-half-plane semicircle
anchored at boundary separation `ell`: `x(s)=(ell/2) cos s`. -/
noncomputable def rtSemicircleX (ell s : ℝ) : ℝ :=
  ell / 2 * Real.cos s

/-- The positive radial coordinate of the standard Poincaré-half-plane
semicircle: `z(s)=(ell/2) sin s`. -/
noncomputable def rtSemicircleZ (ell s : ℝ) : ℝ :=
  ell / 2 * Real.sin s

/-- The squared Euclidean coordinate speed
`(dx/ds)²+(dz/ds)²` of the semicircle. The displayed derivatives are the
pointwise derivatives of `rtSemicircleX` and `rtSemicircleZ`. -/
noncomputable def rtSemicircleEuclideanSpeedSq (ell s : ℝ) : ℝ :=
  (-(ell / 2) * Real.sin s) ^ 2 + (ell / 2 * Real.cos s) ^ 2

/-- The Poincaré line density pulled back along the semicircle:
`R sqrt((dx/ds)²+(dz/ds)²)/z(s)`. This is the continuum integrand whose
regulated integral gives the AdS₃ geodesic length. -/
noncomputable def rtPoincareLineDensity (R ell s : ℝ) : ℝ :=
  R * Real.sqrt (rtSemicircleEuclideanSpeedSq ell s) / rtSemicircleZ ell s

/-- The semicircle has constant Euclidean coordinate speed squared
`(ell/2)²`. -/
lemma rtSemicircleEuclideanSpeedSq_eq (ell s : ℝ) :
    rtSemicircleEuclideanSpeedSq ell s = (ell / 2) ^ 2 := by
  unfold rtSemicircleEuclideanSpeedSq
  nlinarith [Real.sin_sq_add_cos_sq s]

/-- **[Ryu–Takayanagi Eq. 2.10–2.11, pointwise continuum core]**
the Poincaré metric `ds²=R²(dx²+dz²)/z²`, pulled back along
`(x,z)=((ell/2)cos s,(ell/2)sin s)`, has line density exactly
`R/sin s`.

The interval size cancels locally between coordinate speed and radial depth.
The logarithmic cutoff dependence comes from integrating this proved
`csc(s)` density; global minimality and the improper endpoint limit remain
separate analytic statements. -/
@[zil_level bridge_theorem]
lemma rtPoincareLineDensity_eq (R ell s : ℝ)
    (hell : 0 < ell) (hsin : 0 < Real.sin s) :
    rtPoincareLineDensity R ell s = R / Real.sin s := by
  have hsqrt : Real.sqrt (rtSemicircleEuclideanSpeedSq ell s) = ell / 2 := by
    rw [rtSemicircleEuclideanSpeedSq_eq, Real.sqrt_sq]
    positivity
  unfold rtPoincareLineDensity rtSemicircleZ
  rw [hsqrt]
  field_simp

/-! ## §D — the regulated continuum geodesic length -/

/-- On the open interval `(0,π)`, `log(tan(s/2))` is an antiderivative
of `csc(s)`.  This is the analytic step behind the logarithmic endpoint
dependence of the regulated AdS₃ interval geodesic. -/
lemma hasDerivAt_log_tan_half (s : ℝ) (hs : 0 < s) (hsp : s < Real.pi) :
    HasDerivAt (fun t : ℝ => Real.log (Real.tan (t / 2)))
      (1 / Real.sin s) s := by
  have hu0 : 0 < s / 2 := by linarith
  have hupi : s / 2 < Real.pi / 2 := by linarith
  have huI : s / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htpos : 0 < Real.tan (s / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hu0 hupi
  have ht : HasDerivAt (fun t : ℝ => Real.tan (t / 2))
      ((1 / Real.cos (s / 2) ^ 2) * (1 / 2)) s := by
    change HasDerivAt (Real.tan ∘ fun t : ℝ => t / 2)
      ((1 / Real.cos (s / 2) ^ 2) * (1 / 2)) s
    exact (Real.hasDerivAt_tan_of_mem_Ioo huI).comp s
      ((hasDerivAt_id s).div_const 2)
  have hlog := ht.log (ne_of_gt htpos)
  convert hlog using 1
  have hsin : Real.sin s =
      2 * Real.sin (s / 2) * Real.cos (s / 2) := by
    conv_lhs => rw [show s = 2 * (s / 2) by ring]
    exact Real.sin_two_mul (s / 2)
  rw [Real.tan_eq_sin_div_cos, hsin]
  have hsinhalf : Real.sin (s / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith))
  have hcoshalf : Real.cos (s / 2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo huI)
  field_simp

/-- **[Ryu–Takayanagi Eqs. 2.10–2.11, regulated continuum integral]**
the Poincaré line density of the interval semicircle integrates on the finite
cutoff interval `[ε,π-ε]` to the exact difference of endpoint logarithms.

This closes the finite-cutoff analytic calculation.  It neither takes the
improper `ε → 0` limit nor proves that the semicircle globally minimizes length
among all curves with the same boundary anchors. -/
@[zil_level bridge_theorem]
lemma rtPoincareLineDensity_regulated_integral (R ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepspi : eps < Real.pi / 2) :
    (∫ s in eps..(Real.pi - eps), rtPoincareLineDensity R ell s) =
      R * Real.log (Real.tan ((Real.pi - eps) / 2)) -
        R * Real.log (Real.tan (eps / 2)) := by
  have hbounds : eps ≤ Real.pi - eps := by linarith
  have hpoint : Set.EqOn (fun s => rtPoincareLineDensity R ell s)
      (fun s => R / Real.sin s) (Set.uIcc eps (Real.pi - eps)) := by
    intro s hs
    rw [Set.uIcc_of_le hbounds] at hs
    apply rtPoincareLineDensity_eq R ell s hell
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le heps hs.1)
      (lt_of_le_of_lt hs.2 (by linarith))
  rw [intervalIntegral.integral_congr hpoint]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => R * Real.log (Real.tan (t / 2)))
    (f' := fun t => R / Real.sin t)
  · intro s hs
    rw [Set.uIcc_of_le hbounds] at hs
    convert (hasDerivAt_log_tan_half s (lt_of_lt_of_le heps hs.1)
      (lt_of_le_of_lt hs.2 (by linarith))).const_mul R using 1
    all_goals first | rfl | ring
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div Real.continuous_sin.continuousOn
    intro s hs
    rw [Set.uIcc_of_le hbounds] at hs
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (lt_of_lt_of_le heps hs.1) (lt_of_le_of_lt hs.2 (by linarith)))

/-- The symmetric finite-cutoff integral is equivalently
`-2R log(tan(ε/2))`. -/
lemma rtPoincareLineDensity_regulated_integral_eq_neg_two_log
    (R ell eps : ℝ) (hell : 0 < ell)
    (heps : 0 < eps) (hepspi : eps < Real.pi / 2) :
    (∫ s in eps..(Real.pi - eps), rtPoincareLineDensity R ell s) =
      -2 * R * Real.log (Real.tan (eps / 2)) := by
  rw [rtPoincareLineDensity_regulated_integral R ell eps hell heps hepspi]
  rw [show (Real.pi - eps) / 2 =
      Real.pi / 2 - eps / 2 by ring,
    Real.tan_pi_div_two_sub, Real.log_inv]
  ring

/-- The finite remainder after subtracting the universal logarithmic
geodesic-length divergence. -/
noncomputable def rtRenormalizedSemicircleLength (R eps : ℝ) : ℝ :=
  -2 * R * Real.log (Real.tan (eps / 2) / eps)

/-- The elementary small-cutoff ratio `tan(ε/2)/ε` tends to `1/2`.
This is obtained from the actual derivative of tangent at the origin. -/
lemma tan_half_div_tendsto :
    Filter.Tendsto (fun eps : ℝ => Real.tan (eps / 2) / eps)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hI : 0 / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hinner := (hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ)
  have houter :
      HasDerivAt Real.tan 1 ((fun eps : ℝ => eps / 2) 0) := by
    simpa using Real.hasDerivAt_tan_of_mem_Ioo hI
  have hcomp := houter.comp 0 hinner
  have hslope := hcomp.tendsto_slope_zero_right
  simpa [slope, Real.tan_zero, div_eq_mul_inv, mul_comm] using
    hslope

/-- **[Renormalized RT geodesic length]**
after subtracting the logarithmic cutoff divergence, the finite semicircle
remainder tends to `2R log 2`.

Unlike a formal endpoint rewrite, this is a genuine right-filter limit.  It
does not prove global length minimality or derive the RT entropy proposal. -/
@[zil_level bridge_theorem]
lemma rtRenormalizedSemicircleLength_tendsto (R : ℝ) :
    Filter.Tendsto (rtRenormalizedSemicircleLength R)
      (𝓝[>] 0) (𝓝 (2 * R * Real.log 2)) := by
  have hlog :
      Filter.Tendsto
        (fun eps : ℝ => Real.log (Real.tan (eps / 2) / eps))
        (𝓝[>] 0) (𝓝 (Real.log (1 / 2 : ℝ))) :=
    (Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp
      tan_half_div_tendsto
  have hmul :
      Filter.Tendsto
        (fun eps : ℝ =>
          (-2 * R) * Real.log (Real.tan (eps / 2) / eps))
        (𝓝[>] 0) (𝓝 ((-2 * R) * Real.log (1 / 2 : ℝ))) :=
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => -2 * R) (𝓝[>] 0) (𝓝 (-2 * R))).mul hlog
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  change Filter.Tendsto
    (fun eps : ℝ =>
      (-2 * R) * Real.log (Real.tan (eps / 2) / eps))
    (𝓝[>] 0) (𝓝 (2 * R * Real.log 2))
  convert hmul using 1
  rw [hhalf]
  ring

/-- The regulated continuum integral itself, with counterterm
`2R log ε`, converges to the same finite remainder `2R log 2`. -/
lemma rtPoincareLineDensity_renormalized_tendsto
    (R ell : ℝ) (hell : 0 < ell) :
    Filter.Tendsto
      (fun eps =>
        (∫ s in eps..(Real.pi - eps),
          rtPoincareLineDensity R ell s) + 2 * R * Real.log eps)
      (𝓝[>] 0) (𝓝 (2 * R * Real.log 2)) := by
  have hupper :
      ∀ᶠ eps : ℝ in (𝓝[>] 0), eps < Real.pi / 2 :=
    (eventually_lt_nhds (by linarith [Real.pi_pos] :
      (0 : ℝ) < Real.pi / 2)).filter_mono inf_le_left
  have heq :
      (fun eps =>
        (∫ s in eps..(Real.pi - eps),
          rtPoincareLineDensity R ell s) + 2 * R * Real.log eps) =ᶠ[(𝓝[>] 0)]
        rtRenormalizedSemicircleLength R := by
    filter_upwards [self_mem_nhdsWithin, hupper] with eps heps hlt
    have heps : 0 < eps := heps
    rw [rtPoincareLineDensity_regulated_integral_eq_neg_two_log
      R ell eps hell heps hlt]
    unfold rtRenormalizedSemicircleLength
    have htan : 0 < Real.tan (eps / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
    rw [Real.log_div htan.ne' heps.ne']
    ring
  exact (rtRenormalizedSemicircleLength_tendsto R).congr' heq.symm

/-! ## §E — finite temperature -/

/-- The vacuum CFT₂ interval entropy on the infinite line,
`S(l)=(c/3) log(l/a)`.  This is the zero-temperature target of the BTZ
expression below. -/
noncomputable def cftEntropyVacuumLine (c l a : ℝ) : ℝ :=
  (c / 3) * Real.log (l / a)

/-- **[Vacuum interval strong subadditivity]**
for three adjacent positive segments of lengths `p`, `q`, and `r`, the vacuum
CFT₂ interval entropy obeys
`S(p+q)+S(q+r) ≥ S(q)+S(p+q+r)`.

This proves the adjacent-interval scalar inequality directly from the
Calabrese–Cardy logarithm.  It is not the general von Neumann-entropy SSA
theorem for arbitrary regions or states. -/
@[zil_level bridge_theorem]
lemma cftEntropyVacuumLine_strongSubadditivity
    (c a p q r : ℝ)
    (hc : 0 ≤ c) (ha : 0 < a)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    cftEntropyVacuumLine c (p + q) a +
        cftEntropyVacuumLine c (q + r) a ≥
      cftEntropyVacuumLine c q a +
        cftEntropyVacuumLine c (p + q + r) a := by
  have hpq : 0 < p + q := by linarith
  have hqr : 0 < q + r := by linarith
  have hpqr : 0 < p + q + r := by linarith
  have hprod :
      q * (p + q + r) ≤ (p + q) * (q + r) := by
    nlinarith
  have hlog :
      Real.log (q * (p + q + r)) ≤
        Real.log ((p + q) * (q + r)) :=
    Real.log_le_log (mul_pos hq hpqr) hprod
  rw [Real.log_mul hq.ne' hpqr.ne',
    Real.log_mul hpq.ne' hqr.ne'] at hlog
  unfold cftEntropyVacuumLine
  rw [Real.log_div hpq.ne' ha.ne',
    Real.log_div hqr.ne' ha.ne',
    Real.log_div hq.ne' ha.ne',
    Real.log_div hpqr.ne' ha.ne']
  have hfactor : 0 ≤ c / 3 := by positivity
  nlinarith

/-- **[Eq. 2.9] The finite-temperature (BTZ) area expression** `S_A(β) = (c/3) log((β/πa) sinh(πl/β))`
— the thermal area expression of an interval, the AdS-black-hole (BTZ) area-formula dual. -/
noncomputable def cftEntropyFiniteT (c l β a : ℝ) : ℝ :=
  (c / 3) * Real.log (β / (π * a) * Real.sinh (π * l / β))

/-- **[Thermal entanglement exceeds the vacuum interval value]**
for positive interval length, cutoff, and inverse temperature, the BTZ
finite-temperature entropy is no smaller than the vacuum-line entropy.

The proof uses the exact analytic inequality `u ≤ sinh u`; it does not compare
general thermal and vacuum density matrices. -/
@[zil_level bridge_theorem]
lemma cftEntropyVacuumLine_le_finiteT
    (c l β a : ℝ)
    (hc : 0 ≤ c) (hl : 0 < l) (hβ : 0 < β) (ha : 0 < a) :
    cftEntropyVacuumLine c l a ≤ cftEntropyFiniteT c l β a := by
  have hu : 0 ≤ Real.pi * l / β := by positivity
  have hsinh : Real.pi * l / β ≤ Real.sinh (Real.pi * l / β) :=
    Real.self_le_sinh_iff.mpr hu
  have hscale : 0 ≤ β / (Real.pi * a) := by positivity
  have harg :
      l / a ≤ β / (Real.pi * a) * Real.sinh (Real.pi * l / β) := by
    calc
      l / a = β / (Real.pi * a) * (Real.pi * l / β) := by
        field_simp [Real.pi_ne_zero, ha.ne', hβ.ne']
      _ ≤ β / (Real.pi * a) * Real.sinh (Real.pi * l / β) :=
        mul_le_mul_of_nonneg_left hsinh hscale
  have hlog := Real.log_le_log (div_pos hl ha) harg
  unfold cftEntropyVacuumLine cftEntropyFiniteT
  have hfactor : 0 ≤ c / 3 := by positivity
  nlinarith

/-- The hyperbolic product inequality behind adjacent-interval thermal strong
subadditivity.  Its positive remainder is exactly `sinh A * sinh C`. -/
lemma sinh_adjacentInterval_product_le
    (A B C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    Real.sinh B * Real.sinh (A + B + C) ≤
      Real.sinh (A + B) * Real.sinh (B + C) := by
  have hid :
      Real.sinh (A + B) * Real.sinh (B + C) =
        Real.sinh B * Real.sinh (A + B + C) +
          Real.sinh A * Real.sinh C := by
    have hBunit : Real.cosh B ^ 2 = Real.sinh B ^ 2 + 1 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq B]
    rw [Real.sinh_add A B, Real.sinh_add B C,
      Real.sinh_add (A + B) C, Real.sinh_add A B,
      Real.cosh_add A B]
    ring_nf
    rw [hBunit]
    ring
  rw [hid]
  exact le_add_of_nonneg_right
    (mul_nonneg (Real.sinh_nonneg_iff.mpr hA)
      (Real.sinh_nonneg_iff.mpr hC))

/-- **[BTZ interval strong subadditivity]**
the finite-temperature CFT₂ interval entropy obeys the adjacent-interval SSA
inequality for every positive inverse temperature and cutoff.

This is the exact scalar inequality for the BTZ/Calabrese–Cardy expression,
not a construction of the thermal density matrix or the general operator
strong-subadditivity theorem. -/
@[zil_level bridge_theorem]
lemma cftEntropyFiniteT_strongSubadditivity
    (c a β p q r : ℝ)
    (hc : 0 ≤ c) (ha : 0 < a) (hβ : 0 < β)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    cftEntropyFiniteT c (p + q) β a +
        cftEntropyFiniteT c (q + r) β a ≥
      cftEntropyFiniteT c q β a +
        cftEntropyFiniteT c (p + q + r) β a := by
  let A := Real.pi * p / β
  let B := Real.pi * q / β
  let C := Real.pi * r / β
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hpq : 0 < p + q := by linarith
  have hqr : 0 < q + r := by linarith
  have hpqr : 0 < p + q + r := by linarith
  have hscale : 0 < β / (Real.pi * a) := by positivity
  have hhyper :
      Real.sinh B * Real.sinh (A + B + C) ≤
        Real.sinh (A + B) * Real.sinh (B + C) :=
    sinh_adjacentInterval_product_le A B C hA.le hC.le
  have hprod :
      (β / (Real.pi * a) * Real.sinh (Real.pi * q / β)) *
          (β / (Real.pi * a) *
            Real.sinh (Real.pi * (p + q + r) / β)) ≤
        (β / (Real.pi * a) *
            Real.sinh (Real.pi * (p + q) / β)) *
          (β / (Real.pi * a) *
            Real.sinh (Real.pi * (q + r) / β)) := by
    have hAB : Real.pi * (p + q) / β = A + B := by
      dsimp [A, B]
      ring
    have hBC : Real.pi * (q + r) / β = B + C := by
      dsimp [B, C]
      ring
    have hABC : Real.pi * (p + q + r) / β = A + B + C := by
      dsimp [A, B, C]
      ring
    rw [hAB, hBC, hABC, show Real.pi * q / β = B by rfl]
    nlinarith [sq_nonneg (β / (Real.pi * a))]
  have hleftpos :
      0 < (β / (Real.pi * a) * Real.sinh (Real.pi * q / β)) *
        (β / (Real.pi * a) *
          Real.sinh (Real.pi * (p + q + r) / β)) := by
    positivity
  have hlog := Real.log_le_log hleftpos hprod
  rw [Real.log_mul
      (mul_ne_zero hscale.ne' (Real.sinh_ne_zero.mpr
        (div_ne_zero (mul_ne_zero Real.pi_ne_zero hq.ne') hβ.ne')))
      (mul_ne_zero hscale.ne' (Real.sinh_ne_zero.mpr
        (div_ne_zero (mul_ne_zero Real.pi_ne_zero hpqr.ne') hβ.ne'))),
    Real.log_mul
      (mul_ne_zero hscale.ne' (Real.sinh_ne_zero.mpr
        (div_ne_zero (mul_ne_zero Real.pi_ne_zero hpq.ne') hβ.ne')))
      (mul_ne_zero hscale.ne' (Real.sinh_ne_zero.mpr
        (div_ne_zero (mul_ne_zero Real.pi_ne_zero hqr.ne') hβ.ne')))] at hlog
  unfold cftEntropyFiniteT
  have hfactor : 0 ≤ c / 3 := by positivity
  nlinarith

/-- The dimensionless BTZ interval argument converges to `l/a` as inverse
temperature tends to infinity.  This reuses the repository's FLRW proof of
`sinh(rx)/x → r`. -/
lemma cftThermalArgument_tendsto (l a : ℝ)
    (hl : 0 < l) (ha : 0 < a) :
    Filter.Tendsto
      (fun β : ℝ => β / (Real.pi * a) * Real.sinh (Real.pi * l / β))
      Filter.atTop (𝓝 (l / a)) := by
  have hcore :
      Filter.Tendsto
        (fun β : ℝ =>
          Real.sinh ((Real.pi * l) * β⁻¹) / β⁻¹)
        Filter.atTop (𝓝 (Real.pi * l)) := by
    have hinv :
        Filter.Tendsto (fun β : ℝ => β⁻¹)
          Filter.atTop (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_inv_atTop_nhdsGT_zero.mono_right
      apply nhdsWithin_mono
      intro y hy
      simp only [Set.mem_Ioi] at hy
      simp [hy.ne']
    exact (Cosmology.SpatialGeometry.tendsto_sinh_rx_over_x
      (Real.pi * l)).comp hinv
  have hscaled :
      Filter.Tendsto
        (fun β : ℝ =>
          (1 / (Real.pi * a)) *
            (Real.sinh ((Real.pi * l) * β⁻¹) / β⁻¹))
        Filter.atTop
        (𝓝 ((1 / (Real.pi * a)) * (Real.pi * l))) :=
    tendsto_const_nhds.mul hcore
  have heq :
      (fun β : ℝ => β / (Real.pi * a) *
          Real.sinh (Real.pi * l / β)) =ᶠ[Filter.atTop]
        (fun β : ℝ =>
          (1 / (Real.pi * a)) *
            (Real.sinh ((Real.pi * l) * β⁻¹) / β⁻¹)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
    field_simp
  convert hscaled.congr' heq.symm using 1
  field_simp [Real.pi_ne_zero, ha.ne']

/-- **[BTZ to vacuum AdS₃/CFT₂ limit]**
the finite-temperature interval entropy converges to the vacuum-line
Calabrese–Cardy entropy as `β → +∞`.

The theorem controls the explicit continuum entropy expression; it does not
construct the BTZ state, its density matrix, or a bulk Euclidean saddle. -/
@[zil_level bridge_theorem]
lemma cftEntropyFiniteT_tendsto_vacuumLine
    (c l a : ℝ) (hl : 0 < l) (ha : 0 < a) :
    Filter.Tendsto (fun β : ℝ => cftEntropyFiniteT c l β a)
      Filter.atTop (𝓝 (cftEntropyVacuumLine c l a)) := by
  have harg := cftThermalArgument_tendsto l a hl ha
  have hlog :
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (β / (Real.pi * a) * Real.sinh (Real.pi * l / β)))
        Filter.atTop (𝓝 (Real.log (l / a))) :=
    (Real.continuousAt_log (div_ne_zero hl.ne' ha.ne')).tendsto.comp harg
  simpa [cftEntropyFiniteT, cftEntropyVacuumLine] using
    (tendsto_const_nhds.mul hlog :
      Filter.Tendsto
        (fun β : ℝ => (c / 3) *
          Real.log (β / (Real.pi * a) * Real.sinh (Real.pi * l / β)))
        Filter.atTop (𝓝 ((c / 3) * Real.log (l / a))))

/-! ## §F — modular-flow invariance -/

/-- **[Link] The area expression is invariant under the imported norm-square identity.** The RT area is the modular-flow horizon
area `W² = ‖adSComplexCoord W θ‖²` of `PTSymmetricQFT.ModularAdS`, which is **time-reversal invariant**
(`adS_area_timeReversal_invariant`); hence the RT area expression `S_A = W²/4G` is unchanged
by the antiunitary time reversal — the area expression is a modular-flow / entanglement (RT) invariant. -/
@[zil_level bridge_theorem]
lemma areaEntropy_timeReversal_normSq_identity (W θ G : ℝ) :
    rtAreaEntropy (Complex.normSq (conjFactor true (adSComplexCoord W θ))) G
      = rtAreaEntropy (W ^ 2) G := by
  rw [adS_area_timeReversal_invariant]

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtPoincareLineDensity_eq where
  formalizes @ "claim:the-poincare-half-plane-metric-pulled-back-along-the-ads3-interval-semicircle-has-pointwise-line-density-r-over-sine-s",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equations-2-10-2-11",
  caveat @ "claim:pointwise-continuum-pullback-identity-not-a-proof-of-global-geodesic-minimality-the-improper-endpoint-limit-a-cft-density-matrix-or-the-rt-proposal"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtPoincareLineDensity_regulated_integral where
  formalizes @ "claim:the-ads3-interval-semicircle-poincare-line-density-has-the-exact-finite-cutoff-logarithmic-interval-integral",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equations-2-10-2-11",
  caveat @ "claim:proper-finite-cutoff-integral-not-the-improper-epsilon-to-zero-limit-global-geodesic-minimality-a-cft-density-matrix-or-a-derivation-of-the-rt-proposal"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtRenormalizedSemicircleLength_tendsto where
  formalizes @ "claim:after-subtracting-the-universal-logarithmic-cutoff-divergence-the-ads3-semicircle-length-has-finite-remainder-two-r-log-two",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equations-2-10-2-11",
  caveat @ "claim:genuine-right-filter-limit-of-the-proved-regulated-integral-not-global-geodesic-minimality-a-cft-density-matrix-or-a-derivation-of-the-rt-proposal"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyVacuumLine_strongSubadditivity where
  formalizes @ "claim:the-vacuum-cft2-logarithmic-interval-entropy-obeys-strong-subadditivity-for-three-adjacent-positive-intervals",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:headrick-takayanagi-2007-holographic-proof-of-strong-subadditivity",
  supported_by @ "paper:ads-cft-review-1501.00007v2-section-entanglement-entropy",
  caveat @ "claim:direct-scalar-inequality-for-the-calabrese-cardy-vacuum-line-formula-not-the-general-von-neumann-entropy-ssa-theorem-for-arbitrary-regions-or-states"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyVacuumLine_le_finiteT where
  formalizes @ "claim:the-btz-finite-temperature-interval-entropy-is-no-smaller-than-the-vacuum-cft2-interval-entropy",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equation-2-9",
  supported_by @ "lean:Real.self_le_sinh_iff",
  caveat @ "claim:analytic-comparison-of-the-explicit-calabrese-cardy-formulas-not-an-operator-ordering-or-relative-entropy-theorem-for-general-density-matrices"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyFiniteT_strongSubadditivity where
  formalizes @ "claim:the-btz-finite-temperature-cft2-interval-entropy-obeys-strong-subadditivity-for-three-adjacent-positive-intervals",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equation-2-9",
  supported_by @ "paper:headrick-takayanagi-2007-holographic-proof-of-strong-subadditivity",
  caveat @ "claim:exact-hyperbolic-scalar-inequality-for-the-btz-entropy-formula-not-a-construction-of-the-thermal-density-matrix-or-general-operator-ssa"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyFiniteT_tendsto_vacuumLine where
  formalizes @ "claim:the-btz-finite-temperature-cft2-interval-entropy-converges-to-the-vacuum-line-entropy-as-beta-tends-to-infinity",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equation-2-9",
  supported_by @ "lean:Cosmology.SpatialGeometry.tendsto_sinh_rx_over_x",
  caveat @ "claim:continuum-limit-of-the-explicit-entropy-expression-not-a-construction-of-the-btz-density-matrix-or-bulk-euclidean-saddle"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rt_log_square_prefactor_identity where
  formalizes @ "claim:the-ryu-takayanagi-cutoff-log-square-and-brown-henneaux-prefactor-reduce-to-the-cft-logarithm",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ryu-takayanagi-hep-th-0603001v2-equations-2-4-2-5",
  caveat @ "claim:exact-logarithm-and-prefactor-algebra-after-the-geodesic-length-asymptotic-is-supplied-not-a-derivation-of-that-asymptotic"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.areaEntropy_timeReversal_normSq_identity where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularAdS.adS_area_timeReversal_invariant",
  formalizes @ "claim:the-rt-area-expression-is-invariant-under-the-existing-modular-ads-time-reversal-norm-square-identity",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:reuse-of-an-imported-norm-square-invariance-not-a-proof-that-a-general-rt-extremal-surface-is-modular-flow-invariant"

zil_file_contract physlib.ryuTakayanagiFormulaAlgebra where
  promises "The honest Ryu-Takayanagi formula layer: the area-over-four-G and Brown-Henneaux prefactors, the exact pointwise continuum pullback of the Poincare metric along the AdS3 interval semicircle with line density R over sin s, its exact finite-cutoff interval integral, subtraction of its universal logarithmic divergence with a genuine finite right-filter limit, the adjacent-interval strong-subadditivity inequalities for both the vacuum and finite-temperature CFT2 entropies, the finite-temperature entropy lower bound by the vacuum value and its zero-temperature convergence to that value, and the imported modular-AdS norm-square invariance."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtSemicircleX",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtSemicircleZ",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtPoincareLineDensity"]
  forbids_substitutes ["a derivation of the Ryu-Takayanagi proposal from a bulk path integral",
    "global minimality of the semicircle or a finite value for its unrenormalized improper length",
    "construction of a CFT reduced density matrix or the general von Neumann strong-subadditivity theorem"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtPoincareLineDensity_eq,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtPoincareLineDensity_regulated_integral,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtRenormalizedSemicircleLength_tendsto,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyVacuumLine_strongSubadditivity,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyVacuumLine_le_finiteT,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyFiniteT_strongSubadditivity,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.cftEntropyFiniteT_tendsto_vacuumLine,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rt_log_square_prefactor_identity,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.areaEntropy_timeReversal_normSq_identity]

/- ZIL-END -/

#zil_formalization_lint physlib.ryuTakayanagiFormulaAlgebra

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine -/

/-!
# The Liouville path-integral-complexity central-charge spine (AdS/CFT)

Following Caputa–Kundu–Miyaji–Takayanagi–Watanabe, *Liouville action as path-integral
complexity* (JHEP 11(2017)097, arXiv:1706.07056): the path-integral optimization of a 2D CFT
vacuum is measured by the Liouville action `S_L = (c/24π)∫[(∂φ)² + μe^{2φ}]` (their eq. 2.7),
whose on-shell vacuum value is `S_L = (c/6)(1/ε − 1)` (their eq. 6.16).  The whole physical
content is a single central charge `c` threading the Liouville prefactor `c/24π`, the
Calabrese–Cardy slope `c/3`, the Brown–Henneaux relation `c = 3R/2G`, and the Ryu–Takayanagi
entropy `A/4G`.

The repo has all downstream anchors (RT `rtAreaEntropy`, Brown–Henneaux `brownHenneaux`,
Calabrese–Cardy `cftEntropyVacuumLine`, and the `c/24π` welding prefactor
`matterWeldingExponent`) but not the Caputa–Takayanagi complexity object itself.  This module
adds it and ties the spine together.

* `liouvilleComplexityPrefactor c = c/24π` — the Liouville-action complexity prefactor (eq. 2.7).
* `vacuumLiouvilleComplexity c ε = (c/6)(1/ε − 1)` — the on-shell vacuum path-integral complexity
  (eq. 6.16).
* `matterWeldingExponent_eq_liouvilleComplexityPrefactor` — the repo's welding exponent is exactly
  `prefactor · S₁`.
* `brownHenneaux_sixth_eq_rtAreaEntropy` — `c/6 = R/4G` is the RT area-entropy coefficient.
* `vacuumLiouvilleComplexity_brownHenneaux` — at `c = 3R/2G` the vacuum complexity is
  `S_RT(R) · (1/ε − 1)`: the path-integral complexity coefficient is the Ryu–Takayanagi entropy of
  the AdS radius.
* `liouville_complexity_brownHenneaux_spine` — the single central charge threading all four.

Honest scope: this is the central-charge normalization spine and the on-shell vacuum value.  It
does *not* formalize the path-integral optimization / minimality itself (which needs the
position-dependent Weyl-curvature transform `R̃ = e^{-2φ}(R − 2Δφ)` and a variational argument).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QFT.ConformalWelding.MatterLiouvilleGhostFactorization

/-- **The Liouville-action complexity prefactor** `c/24π` (Caputa–Takayanagi eq. 2.7). -/
def liouvilleComplexityPrefactor (c : ℝ) : ℝ := c / (24 * Real.pi)

/-- **The on-shell vacuum path-integral complexity** `S_L = (c/6)(1/ε − 1)` of a 2D CFT vacuum
(Caputa–Takayanagi eq. 6.16), with UV cutoff `ε`. -/
def vacuumLiouvilleComplexity (c ε : ℝ) : ℝ := (c / 6) * (1 / ε - 1)

/-- **The welding exponent is the complexity prefactor times the Liouville action.**  The repo's
`matterWeldingExponent c S₁ = c·S₁/24π` is exactly `liouvilleComplexityPrefactor c · S₁`. -/
@[zil_level physical_theorem]
theorem matterWeldingExponent_eq_liouvilleComplexityPrefactor (c S1 : ℝ) :
    matterWeldingExponent c S1 = liouvilleComplexityPrefactor c * S1 := by
  unfold matterWeldingExponent liouvilleComplexityPrefactor
  ring

/-- **The complexity prefactor recovers the central charge:** `24π · (c/24π) = c`. -/
@[zil_level physical_theorem]
theorem liouvilleComplexityPrefactor_carries_centralCharge (c : ℝ) :
    24 * Real.pi * liouvilleComplexityPrefactor c = c := by
  unfold liouvilleComplexityPrefactor
  field_simp [Real.pi_ne_zero]

/-- **`c/6 = R/4G` is the Ryu–Takayanagi area-entropy coefficient** — the Brown–Henneaux central
charge over six is the RT entropy of the AdS radius. -/
@[zil_level bridge_theorem]
theorem brownHenneaux_sixth_eq_rtAreaEntropy (R G : ℝ) (hG : G ≠ 0) :
    brownHenneaux R G / 6 = rtAreaEntropy R G := by
  unfold brownHenneaux rtAreaEntropy
  field_simp
  ring

/-- **The vacuum path-integral complexity is the RT entropy of the AdS radius, times the cutoff
factor.**  At the Brown–Henneaux central charge `c = 3R/2G`, the Caputa–Takayanagi vacuum
complexity `(c/6)(1/ε − 1)` equals `S_RT(R) · (1/ε − 1)` — the complexity coefficient is exactly
the Ryu–Takayanagi entanglement entropy of the AdS radius. -/
@[zil_level bridge_theorem]
theorem vacuumLiouvilleComplexity_brownHenneaux (R G ε : ℝ) (hG : G ≠ 0) :
    vacuumLiouvilleComplexity (brownHenneaux R G) ε = rtAreaEntropy R G * (1 / ε - 1) := by
  unfold vacuumLiouvilleComplexity
  rw [brownHenneaux_sixth_eq_rtAreaEntropy R G hG]

/-- **The vacuum path-integral complexity is positive (UV-divergent).**  For a positive central
charge and cutoff `0 < ε < 1`, the complexity `(c/6)(1/ε − 1) > 0`, diverging as `ε → 0`. -/
@[zil_level physical_theorem]
theorem vacuumLiouvilleComplexity_pos (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < vacuumLiouvilleComplexity c ε := by
  unfold vacuumLiouvilleComplexity
  have h1 : 1 < 1 / ε := by rw [lt_div_iff₀ hε, one_mul]; exact hε1
  have h2 : 0 < 1 / ε - 1 := by linarith
  positivity

/-- **The Liouville-complexity central-charge spine.**  The single Brown–Henneaux central charge
`c = 3R/2G` threads (i) the Liouville complexity prefactor `c/24π`, (ii) the Brown–Henneaux
relation `c/3 = R/2G`, and (iii) the on-shell vacuum path-integral complexity, whose coefficient
is the Ryu–Takayanagi entropy of the AdS radius. -/
@[zil_level bridge_theorem]
theorem liouville_complexity_brownHenneaux_spine (R G ε : ℝ) (hG : G ≠ 0) :
    24 * Real.pi * liouvilleComplexityPrefactor (brownHenneaux R G) = brownHenneaux R G
      ∧ brownHenneaux R G / 3 = R / (2 * G)
      ∧ vacuumLiouvilleComplexity (brownHenneaux R G) ε = rtAreaEntropy R G * (1 / ε - 1) := by
  refine ⟨liouvilleComplexityPrefactor_carries_centralCharge (brownHenneaux R G), ?_,
    vacuumLiouvilleComplexity_brownHenneaux R G ε hG⟩
  unfold brownHenneaux
  field_simp

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine

zil attach matterWeldingExponent_eq_liouvilleComplexityPrefactor where
  formalizes @ "claim:the-conformal-welding-exponent-is-the-liouville-complexity-prefactor-c-over-twenty-four-pi-times-the-liouville-action"

zil attach vacuumLiouvilleComplexity_brownHenneaux where
  formalizes @ "claim:at-the-brown-henneaux-central-charge-the-caputa-takayanagi-vacuum-path-integral-complexity-equals-the-ryu-takayanagi-entropy-of-the-ads-radius-times-the-cutoff-factor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.brownHenneaux"

zil attach liouville_complexity_brownHenneaux_spine where
  formalizes @ "claim:a-single-brown-henneaux-central-charge-threads-the-liouville-complexity-prefactor-the-brown-henneaux-relation-and-the-vacuum-path-integral-complexity-whose-coefficient-is-the-ryu-takayanagi-entropy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy"

zil_file_contract physlib.liouvilleComplexityHolographicSpine where
  promises "The Liouville path-integral-complexity central-charge spine of AdS/CFT, following Caputa Kundu Miyaji Takayanagi Watanabe. The Liouville-action complexity prefactor c over twenty four pi and the on-shell vacuum path-integral complexity c over six times one over epsilon minus one are the genuine Caputa-Takayanagi objects, added to the repo. The repo's conformal welding exponent is exactly the complexity prefactor times the Liouville action. At the Brown-Henneaux central charge c equals three R over two G, the vacuum path-integral complexity equals the Ryu-Takayanagi entropy of the AdS radius times the cutoff factor, since c over six equals R over four G is the RT area-entropy coefficient. The vacuum complexity is positive and UV-divergent. A single Brown-Henneaux central charge threads the Liouville complexity prefactor, the Brown-Henneaux relation, and the vacuum complexity whose coefficient is the RT entropy. This is the central-charge normalization spine and the on-shell vacuum value, not a formalization of the path-integral optimization or minimality, which needs the position-dependent Weyl-curvature transform and a variational argument."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.brownHenneaux",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy",
    "lean:Physlib.QFT.ConformalWelding.MatterLiouvilleGhostFactorization.matterWeldingExponent"
  ]
  forbids_substitutes [
    "claiming the path-integral optimization or minimality is formalized here rather than only the central-charge normalization and the on-shell vacuum value",
    "omitting the position-dependent Weyl-curvature derivative correction needed for the optimization step"
  ]
  witnessed_by [
    matterWeldingExponent_eq_liouvilleComplexityPrefactor,
    liouvilleComplexityPrefactor_carries_centralCharge,
    brownHenneaux_sixth_eq_rtAreaEntropy,
    vacuumLiouvilleComplexity_brownHenneaux,
    vacuumLiouvilleComplexity_pos,
    liouville_complexity_brownHenneaux_spine
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.liouvilleComplexityHolographicSpine

