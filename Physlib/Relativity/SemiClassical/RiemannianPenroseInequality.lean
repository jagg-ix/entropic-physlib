/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
public import Mathlib.Tactic

/-!
# Riemannian Penrose inequality: algebraic core of Bray's proof

This file formalizes Lean-checkable kernels from Hubert L. Bray,
*Proof of the Riemannian Penrose Conjecture Using the Positive Mass Theorem*,
arXiv:math/9911173v1 (1999).

The paper proves the full geometric theorem by constructing a conformal flow of
asymptotically flat 3-metrics, proving that horizon area is constant, ADM mass is
non-increasing, and the large-time geometry is Schwarzschild.  The PDE,
regularity, inverse-mean-curvature, and positive-mass theorem arguments are not
asserted here.  What is formalized is the finite algebraic skeleton that those
geometric results feed:

* the time-symmetric constraint reduction: nonnegative local energy density is
  equivalent to nonnegative scalar curvature;
* Bray's harmonically flat ADM mass coefficient `m = 2ab`;
* conformal horizon-area scaling for `g_t = u_t^4 g_0`;
* the coefficient calculation behind Bray equations (109)--(113);
* the Schwarzschild equality case `m = sqrt(A / (16*pi))`;
* the implication from a constant-area, non-increasing-mass conformal flow with
  Schwarzschild endpoint to the Riemannian Penrose inequality.

The module also links the geometric-unit Schwarzschild area `16*pi*m^2` to the
existing semiclassical Schwarzschild horizon area at `G = c = 1`, and transports
the same area data through the repository's Bekenstein-Verlinde bit and
Schwarzschild Hawking-rate structures.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.SemiClassical.RiemannianPenroseInequality

open Real
open Physlib.Thermodynamics

/-! ## Constants and geometric-unit mass/area formulas -/

/-- The positive denominator `16*pi` in the Riemannian Penrose inequality. -/
theorem sixteen_pi_pos : 0 < 16 * Real.pi := by
  positivity

/-- The black-hole mass contributed by a horizon of total area `A`:
`sqrt(A / (16*pi))`, in geometric units. -/
def blackHoleMassContribution (A : ℝ) : ℝ :=
  Real.sqrt (A / (16 * Real.pi))

/-- In geometric units, the spatial Schwarzschild horizon area is `16*pi*m^2`. -/
def riemannianSchwarzschildHorizonArea (m : ℝ) : ℝ :=
  16 * Real.pi * m^2

/-- Bray Definition 2: for a harmonically flat end
`U = a + b/r + O(r^-2)`, the ADM mass is `2ab`. -/
def harmonicFlatADMmass (a b : ℝ) : ℝ :=
  2 * a * b

/-- In the time-symmetric case `h = 0`, equation (2) reduces to
`mu = R/(16*pi)`. -/
def timeSymmetricLocalEnergyDensity (scalarR : ℝ) : ℝ :=
  scalarR / (16 * Real.pi)

/-- Under a 3-dimensional conformal metric change `g' = u^4 g`, a two-surface
area scales by `u^4`. -/
def conformalSurfaceAreaScale (u A : ℝ) : ℝ :=
  u^4 * A

/-- Bray equations (109)--(112): if the asymptotic end has
`u_t = alpha(t) + beta(t)/r + O(r^-2)` and the initial harmonically flat mass
is `m0`, then the mass coefficient is
`2 alpha(t) (beta(t) + m0 alpha(t)/2)`. -/
def brayAsymptoticMassFromCoefficients (alpha beta m0 : ℝ) : ℝ :=
  2 * alpha * (beta + m0 / 2 * alpha)

/-- Section 14, equation (233): Bray's quasi-local mass along the conformal
flow, written as `m/m(t) * sqrt(A(t)/(16*pi))`. -/
def brayQuasiLocalMass (totalMass flowMass horizonArea : ℝ) : ℝ :=
  totalMass / flowMass * blackHoleMassContribution horizonArea

/-- The Penrose quotient `m / sqrt(A/(16*pi))`.  The inequality is exactly
`1 <= penroseQuotient m A` when `A > 0`. -/
def penroseQuotient (m A : ℝ) : ℝ :=
  m / blackHoleMassContribution A

theorem blackHoleMassContribution_nonneg (A : ℝ) :
    0 ≤ blackHoleMassContribution A := by
  exact Real.sqrt_nonneg _

theorem blackHoleMassContribution_pos {A : ℝ} (hA : 0 < A) :
    0 < blackHoleMassContribution A := by
  unfold blackHoleMassContribution
  exact Real.sqrt_pos.mpr (div_pos hA sixteen_pi_pos)

theorem riemannianSchwarzschildHorizonArea_nonneg (m : ℝ) :
    0 ≤ riemannianSchwarzschildHorizonArea m := by
  unfold riemannianSchwarzschildHorizonArea
  positivity

/-- The horizon mass squared recovers `A/(16*pi)` for nonnegative area. -/
theorem blackHoleMassContribution_sq {A : ℝ} (hA : 0 ≤ A) :
    blackHoleMassContribution A ^ 2 = A / (16 * Real.pi) := by
  unfold blackHoleMassContribution
  exact Real.sq_sqrt (div_nonneg hA (le_of_lt sixteen_pi_pos))

/-- For the Schwarzschild area `A = 16*pi*m^2`, the black-hole mass contribution
is exactly `m` when `m >= 0`.  This is the equality case in the Riemannian
Penrose inequality. -/
theorem blackHoleMassContribution_schwarzschild {m : ℝ} (hm : 0 ≤ m) :
    blackHoleMassContribution (riemannianSchwarzschildHorizonArea m) = m := by
  unfold blackHoleMassContribution riemannianSchwarzschildHorizonArea
  have hden : 16 * Real.pi ≠ 0 := ne_of_gt sixteen_pi_pos
  have hquot : 16 * Real.pi * m ^ 2 / (16 * Real.pi) = m ^ 2 := by
    field_simp [hden]
  rw [hquot, Real.sqrt_sq_eq_abs, abs_of_nonneg hm]

/-- The geometric-unit Schwarzschild area is the existing semiclassical
Schwarzschild area at `G = c = 1`. -/
theorem riemannianSchwarzschildHorizonArea_eq_semiclassical (m : ℝ) :
    riemannianSchwarzschildHorizonArea m = schwarzschildArea m 1 1 := by
  unfold riemannianSchwarzschildHorizonArea schwarzschildArea
  ring

/-- The harmonically flat Schwarzschild coefficient `U = 1 + m/(2r)` has ADM
mass `m` by Bray's `2ab` definition. -/
theorem harmonicFlatADMmass_schwarzschild (m : ℝ) :
    harmonicFlatADMmass 1 (m / 2) = m := by
  unfold harmonicFlatADMmass
  ring

/-! ## Conformal-area and asymptotic-mass coefficient algebra -/

/-- If the conformal factor is `1` on the horizon, Bray's conformal metric
`g_t = u_t^4 g_0` leaves the horizon area unchanged at that instant. -/
theorem conformalSurfaceAreaScale_unit (A : ℝ) :
    conformalSurfaceAreaScale 1 A = A := by
  unfold conformalSurfaceAreaScale
  ring

/-- Exact expansion of the conformal surface-area scaling near a horizon.
The linear coefficient is `4 v A`, so if Bray's velocity satisfies `v = 0` on
the horizon, the first-order area change from the metric is zero. -/
theorem conformalSurfaceAreaScale_expansion (s v A : ℝ) :
    conformalSurfaceAreaScale (1 + s * v) A =
      A + 4 * s * v * A + s^2 * (6 * v^2 + 4 * s * v^3 + s^2 * v^4) * A := by
  unfold conformalSurfaceAreaScale
  ring

/-- The mass coefficient at the initial values `alpha = 1`, `beta = 0` is the
initial ADM mass `m0`. -/
theorem brayAsymptoticMass_initial (m0 : ℝ) :
    brayAsymptoticMassFromCoefficients 1 0 m0 = m0 := by
  unfold brayAsymptoticMassFromCoefficients
  ring

/-- Exact finite expansion behind Bray equations (110)--(113).  With
`alpha(s) = 1 - s` and `beta(s) = s E/2`, the mass coefficient is
`m0 + s(E - 2m0) + s^2(m0 - E)`. -/
theorem brayAsymptoticMass_linearized_expansion (s E m0 : ℝ) :
    brayAsymptoticMassFromCoefficients (1 - s) (s * (E / 2)) m0 =
      m0 + s * (E - 2 * m0) + s^2 * (m0 - E) := by
  unfold brayAsymptoticMassFromCoefficients
  ring

/-- Bray equation (113), algebraic sign step: the positive-mass-theorem input
`E <= 2 m0` makes the first-order mass slope nonpositive. -/
theorem bray_mass_slope_nonpos_of_capacity_bound {E m0 : ℝ}
    (hE : E ≤ 2 * m0) :
    E - 2 * m0 ≤ 0 := by
  linarith

/-- In the time-symmetric constraint equation, nonnegative local energy density
is exactly nonnegative scalar curvature. -/
theorem timeSymmetricLocalEnergyDensity_nonneg_iff (scalarR : ℝ) :
    0 ≤ timeSymmetricLocalEnergyDensity scalarR ↔ 0 ≤ scalarR := by
  unfold timeSymmetricLocalEnergyDensity
  have hden : 0 < 16 * Real.pi := sixteen_pi_pos
  constructor
  · intro h
    have hmul := mul_nonneg h (le_of_lt hden)
    have hcancel : scalarR = scalarR / (16 * Real.pi) * (16 * Real.pi) := by
      field_simp [ne_of_gt hden]
    rw [hcancel]
    exact hmul
  · intro h
    exact div_nonneg h (le_of_lt hden)

/-! ## Penrose inequality from Bray's conformal-flow outputs -/

/-- A compact witness for the outputs of Bray's conformal flow used in the final
inequality step: the horizon area is fixed at `horizonArea`, the ADM mass is
non-increasing, and at `finalTime` the metric has reached the Schwarzschild
equality value. -/
structure BrayConformalFlowWitness where
  admMass : ℝ → ℝ
  horizonArea : ℝ
  finalTime : ℝ
  finalTime_nonneg : 0 ≤ finalTime
  mass_nonincreasing : ∀ {s t : ℝ}, s ≤ t → admMass t ≤ admMass s
  final_schwarzschild :
    admMass finalTime = blackHoleMassContribution horizonArea

/-- Bray's monotone conformal-flow outputs imply the Riemannian Penrose
inequality for the initial metric:
`sqrt(A/(16*pi)) <= m(0)`. -/
theorem penrose_inequality_from_bray_flow (flow : BrayConformalFlowWitness) :
    blackHoleMassContribution flow.horizonArea ≤ flow.admMass 0 := by
  have hmono : flow.admMass flow.finalTime ≤ flow.admMass 0 :=
    flow.mass_nonincreasing flow.finalTime_nonneg
  rw [flow.final_schwarzschild] at hmono
  exact hmono

/-- Equivalent linearized form: if a non-increasing mass path reaches the
Schwarzschild mass contribution at some nonnegative time, then its initial mass
already bounds the horizon contribution. -/
theorem penrose_inequality_from_monotone_mass
    {admMass : ℝ → ℝ} {A T : ℝ}
    (hT : 0 ≤ T)
    (hmono : ∀ {s t : ℝ}, s ≤ t → admMass t ≤ admMass s)
    (hfinal : admMass T = blackHoleMassContribution A) :
    blackHoleMassContribution A ≤ admMass 0 := by
  exact penrose_inequality_from_bray_flow
    { admMass := admMass
      horizonArea := A
      finalTime := T
      finalTime_nonneg := hT
      mass_nonincreasing := hmono
      final_schwarzschild := hfinal }

/-- If area is fixed and positive, non-increasing mass makes the Penrose
quotient non-increasing along Bray's flow. -/
theorem penroseQuotient_mass_monotone {A m_late m_early : ℝ}
    (hA : 0 < A) (hm : m_late ≤ m_early) :
    penroseQuotient m_late A ≤ penroseQuotient m_early A := by
  unfold penroseQuotient
  exact div_le_div_of_nonneg_right hm (le_of_lt (blackHoleMassContribution_pos hA))

/-- The Schwarzschild endpoint has Penrose quotient exactly `1`. -/
theorem penroseQuotient_schwarzschild {m : ℝ} (hm : 0 < m) :
    penroseQuotient m (riemannianSchwarzschildHorizonArea m) = 1 := by
  unfold penroseQuotient
  rw [blackHoleMassContribution_schwarzschild (le_of_lt hm)]
  exact div_self (ne_of_gt hm)

/-- Bray's conformal-flow outputs imply that the initial Penrose quotient is at
least `1`, the quotient form of the Penrose inequality. -/
theorem penroseQuotient_initial_ge_one_from_bray_flow
    (flow : BrayConformalFlowWitness) (hA : 0 < flow.horizonArea) :
    1 ≤ penroseQuotient (flow.admMass 0) flow.horizonArea := by
  have hineq := penrose_inequality_from_bray_flow flow
  unfold penroseQuotient
  rw [le_div_iff₀ (blackHoleMassContribution_pos hA)]
  simpa using hineq

/-! ## Quasi-local mass monotonicity algebra -/

/-- Bray equation (233) at the initial time: when `flowMass = totalMass`, the
quasi-local mass equals the black-hole mass contribution. -/
theorem brayQuasiLocalMass_initial {M A : ℝ} (hM : M ≠ 0) :
    brayQuasiLocalMass M M A = blackHoleMassContribution A := by
  unfold brayQuasiLocalMass
  field_simp [hM]

/-- With fixed total mass and horizon area, if the flow mass decreases while
remaining positive, Bray's quasi-local mass formula is nondecreasing. -/
theorem brayQuasiLocalMass_nondec_of_mass_noninc
    {totalMass A m_late m_early : ℝ}
    (hM : 0 ≤ totalMass) (hm_late : 0 < m_late) (hm_early : 0 < m_early)
    (hm : m_late ≤ m_early) :
    brayQuasiLocalMass totalMass m_early A
      ≤ brayQuasiLocalMass totalMass m_late A := by
  unfold brayQuasiLocalMass
  have hinv : m_early⁻¹ ≤ m_late⁻¹ :=
    (inv_le_inv₀ hm_early hm_late).2 hm
  have hdiv : totalMass / m_early ≤ totalMass / m_late := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hM
  exact mul_le_mul_of_nonneg_right hdiv (blackHoleMassContribution_nonneg A)

/-- Squared Penrose inequality: for nonnegative horizon area, the mass bound
implies `A <= 16*pi*m^2`.  This is often the algebraic form used when comparing
with area monotonicity. -/
theorem area_bound_of_penrose_inequality {m A : ℝ}
    (hA : 0 ≤ A) (hmass : blackHoleMassContribution A ≤ m) :
    A ≤ 16 * Real.pi * m^2 := by
  have hbh_nonneg : 0 ≤ blackHoleMassContribution A :=
    blackHoleMassContribution_nonneg A
  have hm_nonneg : 0 ≤ m := le_trans hbh_nonneg hmass
  have hsquare :=
    (sq_le_sq₀ hbh_nonneg hm_nonneg).2 hmass
  rw [blackHoleMassContribution_sq hA] at hsquare
  have hden : 0 < 16 * Real.pi := sixteen_pi_pos
  have hmul := mul_le_mul_of_nonneg_right hsquare (le_of_lt hden)
  have hleft : A / (16 * Real.pi) * (16 * Real.pi) = A := by
    field_simp [ne_of_gt hden]
  rw [hleft] at hmul
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Conversely, for nonnegative mass and area, the squared area bound is
equivalent to the Penrose mass inequality. -/
theorem penrose_inequality_of_area_bound {m A : ℝ}
    (hA : 0 ≤ A) (hm : 0 ≤ m) (harea : A ≤ 16 * Real.pi * m^2) :
    blackHoleMassContribution A ≤ m := by
  have hden : 0 < 16 * Real.pi := sixteen_pi_pos
  have hdiv : A / (16 * Real.pi) ≤ m^2 := by
    rw [div_le_iff₀ hden]
    simpa [mul_assoc, mul_comm, mul_left_comm] using harea
  have hsquare : blackHoleMassContribution A ^ 2 ≤ m^2 := by
    rw [blackHoleMassContribution_sq hA]
    exact hdiv
  exact (sq_le_sq₀ (blackHoleMassContribution_nonneg A) hm).1 hsquare

/-! ## Bridges to horizon entropy, holographic bits, and Hawking rate -/

/-- In geometric units, Verlinde's holographic bit count is numerically the
screen area.  This is the `G = ℏ = c = 1` specialization of the repository's
`holographicBits` structure. -/
theorem holographicBits_geometric_units (A : ℝ) :
    holographicBits A 1 1 1 = A := by
  unfold holographicBits
  ring

/-- The Riemannian Schwarzschild equality area is the same object counted by
the repository's Verlinde holographic-bit structure in geometric units. -/
theorem riemannianSchwarzschildHorizonArea_holographicBits (m : ℝ) :
    holographicBits (riemannianSchwarzschildHorizonArea m) 1 1 1 =
      riemannianSchwarzschildHorizonArea m := by
  rw [holographicBits_geometric_units]

/-- Explicitly reuse the existing Schwarzschild-Verlinde bridge:
`N(A_Schw) = 16*pi*m^2` in geometric units. -/
theorem riemannianSchwarzschildHorizonArea_holographicBits_explicit (m : ℝ) :
    holographicBits (riemannianSchwarzschildHorizonArea m) 1 1 1 =
      16 * Real.pi * m^2 := by
  rw [riemannianSchwarzschildHorizonArea_eq_semiclassical]
  have h :=
    Physlib.Relativity.SemiClassical.schwarzschildArea_holographicBits
      (M := m) (G := 1) (ℏ := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- In Planck geometric units, Bekenstein entropic time is one quarter of the
horizon area. -/
theorem bekensteinTauEnt_geometric_units (A : ℝ) :
    bekensteinTauEnt A 1 = A / 4 := by
  unfold bekensteinTauEnt
  ring

/-- The Penrose horizon area and the Bekenstein horizon-clock differential use
the same quarter-area normalization at unit Planck length. -/
theorem horizonClock_diff_from_area_eq_bekensteinTauEnt_geometric (dA : ℝ) :
    horizonClock_diff_from_area dA 1 = bekensteinTauEnt dA 1 := by
  unfold horizonClock_diff_from_area bekensteinTauEnt
  ring

/-- Geometric-unit specialization of the repository's general
Bekenstein-Verlinde bridge:
`tau_ent(A) = holographicBits(A)/4`. -/
theorem bekensteinTauEnt_eq_holographicBits_div_four_geometric (A : ℝ) :
    bekensteinTauEnt A 1 = holographicBits A 1 1 1 / 4 := by
  simpa using
    (Physlib.Relativity.SemiClassical.bekensteinTauEnt_eq_holographicBits_div_four
      (A := A) (G := 1) (ℏ := 1) (c := 1) (ℓP := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))

/-- The Bekenstein quarter-area scalar equals `4*pi` times the square of the
Penrose black-hole mass contribution. -/
theorem bekensteinTauEnt_eq_four_pi_blackHoleMassContribution_sq
    {A : ℝ} (hA : 0 ≤ A) :
    bekensteinTauEnt A 1 =
      4 * Real.pi * blackHoleMassContribution A ^ 2 := by
  rw [bekensteinTauEnt_geometric_units, blackHoleMassContribution_sq hA]
  field_simp [Real.pi_ne_zero]
  ring

/-- At the Schwarzschild equality case, the Bekenstein scalar is
`4*pi*m^2`. -/
theorem bekensteinTauEnt_riemannianSchwarzschildHorizonArea (m : ℝ) :
    bekensteinTauEnt (riemannianSchwarzschildHorizonArea m) 1 =
      4 * Real.pi * m^2 := by
  unfold bekensteinTauEnt riemannianSchwarzschildHorizonArea
  ring

/-- The Penrose inequality also bounds the geometric-unit Verlinde bit count. -/
theorem holographicBits_bound_of_penrose_inequality {m A : ℝ}
    (hA : 0 ≤ A) (hmass : blackHoleMassContribution A ≤ m) :
    holographicBits A 1 1 1 ≤ 16 * Real.pi * m^2 := by
  rw [holographicBits_geometric_units]
  exact area_bound_of_penrose_inequality hA hmass

/-- The Penrose inequality also bounds the Bekenstein quarter-area scalar. -/
theorem bekensteinTauEnt_bound_of_penrose_inequality {m A : ℝ}
    (hA : 0 ≤ A) (hmass : blackHoleMassContribution A ≤ m) :
    bekensteinTauEnt A 1 ≤ 4 * Real.pi * m^2 := by
  rw [bekensteinTauEnt_geometric_units]
  have harea := area_bound_of_penrose_inequality hA hmass
  nlinarith [harea, Real.pi_pos]

/-- A positive Penrose horizon contribution can be used directly as the mass
input to the existing Schwarzschild Hawking-temperature positivity theorem. -/
theorem schwarzschildHawkingTemperature_pos_at_penrose_mass
    {A ℏ G c kB : ℝ} (hA : 0 < A) (hℏ : 0 < ℏ) (hG : 0 < G)
    (hc : 0 < c) (hkB : 0 < kB) :
    0 < schwarzschildHawkingTemperature
      ℏ G (blackHoleMassContribution A) c kB :=
  schwarzschildHawkingTemperature_pos hℏ hG
    (blackHoleMassContribution_pos hA) hc hkB

/-- A positive Penrose horizon contribution can be used directly as the mass
input to the repository's Schwarzschild entropic-rate structure. -/
theorem schwarzschildEntropicRate_pos_at_penrose_mass
    {A G c : ℝ} (hA : 0 < A) (hG : 0 < G) (hc : 0 < c) :
    0 < schwarzschildEntropicRate
      G (blackHoleMassContribution A) c :=
  schwarzschildEntropicRate_pos hG (blackHoleMassContribution_pos hA) hc

end Physlib.Relativity.SemiClassical.RiemannianPenroseInequality

end
