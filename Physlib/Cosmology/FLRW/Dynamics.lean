/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.HubbleEvolution
public import Physlib.Cosmology.FLRW.DensityParameters
public import Mathlib.Topology.Order.IntermediateValue
public import Physlib.ClassicalMechanics.HerglotzLazoContact

meta import Zil
/-!

# Dynamical criteria for FLRW cosmology

Qualitative consequences of the Friedmann and acceleration equations.  Formalized
here: the pointwise energy conditions of the cosmic perfect fluid (null, weak,
strong, dominant) and the acceleration criterion — the expansion accelerates
*iff* the fluid violates the strong energy condition,
`0 < ∂ₜ∂ₜa ↔ ρ + 3P/c² < 0` (`acceleration_iff_strong_energy_violation`,
`Λ = 0`; a cosmological constant enters as a `w = −1` component of the total).
The remaining items (deceleration parameter from density parameters, eternal
expansion, Big-Bang singularity) stay as TODOs.

-/

@[expose] public section

namespace Cosmology.FLRW.Dynamics

open Time
open Cosmology.FLRW.FriedmannEquation
open Cosmology.FLRW.DensityParameters

/-! ## §A — the energy conditions of the cosmic perfect fluid -/

/-- **The null energy condition** `ρ + P/c² ≥ 0` — the hypothesis of the
horizon-entropy/expansion equivalence (`HorizonEntropyExpansion`). -/
def NullEnergyCondition (ρ p : Time → ℝ) (c : ℝ) : Prop :=
  ∀ t, 0 ≤ ρ t + p t / c ^ 2

/-- **The weak energy condition** `ρ ≥ 0 ∧ ρ + P/c² ≥ 0`. -/
def WeakEnergyCondition (ρ p : Time → ℝ) (c : ℝ) : Prop :=
  ∀ t, 0 ≤ ρ t ∧ 0 ≤ ρ t + p t / c ^ 2

/-- **The strong energy condition** `ρ + P/c² ≥ 0 ∧ ρ + 3P/c² ≥ 0` — the
condition whose *violation* is accelerated expansion. -/
def StrongEnergyCondition (ρ p : Time → ℝ) (c : ℝ) : Prop :=
  ∀ t, 0 ≤ ρ t + p t / c ^ 2 ∧ 0 ≤ ρ t + 3 * p t / c ^ 2

/-- **The dominant energy condition** `ρ ≥ 0 ∧ |P| ≤ ρc²`. -/
def DominantEnergyCondition (ρ p : Time → ℝ) (c : ℝ) : Prop :=
  ∀ t, 0 ≤ ρ t ∧ |p t| ≤ ρ t * c ^ 2

/-! ## §B — acceleration ⟺ strong-energy-condition violation -/

/-- **[Acceleration ⟺ SEC violation] `0 < ä ↔ ρ + 3P/c² < 0`** — from the
second Friedmann equation at `Λ = 0` (a cosmological constant enters as a
`w = −1` component of the total fluid): the expansion accelerates exactly when
the active gravitational mass `ρ + 3P/c²` (the Tolman combination of
`PairAnnihilationGravitationalWave.annihilation_doubles_poisson_source`) turns
negative. -/
theorem acceleration_iff_strong_energy_violation (a ρ p : Time → ℝ) (G c : ℝ)
    (t : Time)
    (hsecond : SecondOrderFriedmann a ρ p 0 G c t)
    (hapos : 0 < a t) (hG : 0 < G) :
    0 < ∂ₜ (∂ₜ a) t ↔ ρ t + 3 * p t / c ^ 2 < 0 := by
  unfold SecondOrderFriedmann at hsecond
  rw [div_eq_iff hapos.ne'] at hsecond
  have hdd : ∂ₜ (∂ₜ a) t
      = -(4 * Real.pi * G / 3) * (ρ t + 3 * p t / c ^ 2) * a t := by
    rw [hsecond]
    ring
  rw [hdd]
  have hpos : 0 < 4 * Real.pi * G / 3 * a t :=
    mul_pos (div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hG)
      (by norm_num)) hapos
  constructor
  · intro h
    by_contra hle
    push Not at hle
    nlinarith
  · intro h
    nlinarith


/-! ## §C — the deceleration parameter and eternal expansion -/

/-- **[Flat single-fluid deceleration parameter] `q = ½(1 + 3w)`.**  For a spatially
flat (`k = 0`, `Λ = 0`) universe filled with one barotropic fluid `p = wρc²`,
the deceleration parameter reduces to `½(1 + 3w)`: dust (`w = 0`) gives `q = ½`,
radiation (`w = 1/3`) gives `q = 1`, and `w < −1/3` gives acceleration (`q < 0`).
Derived from `decelerationParameter_eq_friedmann` and the flat Friedmann equation
`H² = (8πG/3)ρ`. -/
theorem decelerationParameter_flat_single_fluid (a ρ p : Time → ℝ) (w G c : ℝ)
    (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0)
    (hρz : ρ t ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ 0 0 G c t)
    (hsecond : SecondOrderFriedmann a ρ p 0 G c t)
    (hw : p t = w * ρ t * c ^ 2) :
    decelerationParameter a t = (1 + 3 * w) / 2 := by
  rw [decelerationParameter_eq_friedmann ha hd_a haz hd_az hfirst hsecond, hw]
  have hH2 : (hubbleConstant a t) ^ 2 = 8 * Real.pi * G / 3 * ρ t := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    simp only [hubbleConstant, zero_mul, zero_div, sub_zero, add_zero] at h ⊢
    linarith [h]
  rw [hH2]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **[The Friedmann right-hand side is positive]** for `K ≤ 0`, `ρ > 0`, `Λ ≥ 0`
and `G > 0` the squared Hubble rate is strictly positive: `0 < H²`.  The curvature
term `−kc²/a²` is nonnegative (open/flat), the matter term is positive, and the
cosmological term is nonnegative — nothing can make the expansion stall. -/
theorem friedmann_rhs_pos (a ρ : Time → ℝ) (k Λ G c : ℝ) (t : Time)
    (hfirst : FirstOrderFriedmann a ρ k Λ G c t)
    (hk : k ≤ 0) (hρ : 0 < ρ t) (hΛ : 0 ≤ Λ) (hG : 0 < G) :
    0 < (hubbleConstant a t) ^ 2 := by
  have h := hfirst
  unfold FirstOrderFriedmann at h
  simp only [hubbleConstant]
  rw [h]
  have hkc : k * c ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg c)
  have h2 : 0 ≤ -(k * c ^ 2) / (a t) ^ 2 :=
    div_nonneg (neg_nonneg.mpr hkc) (sq_nonneg _)
  have h1 : (0 : ℝ) < 8 * Real.pi * G / 3 * ρ t := by positivity
  have h3 : (0 : ℝ) ≤ Λ * c ^ 2 / 3 := by positivity
  have hrw : 8 * Real.pi * G / 3 * ρ t - k * c ^ 2 / (a t) ^ 2 + Λ * c ^ 2 / 3
      = 8 * Real.pi * G / 3 * ρ t + -(k * c ^ 2) / (a t) ^ 2 + Λ * c ^ 2 / 3 := by
    rw [neg_div]; ring
  rw [hrw]; linarith

/-- **[The expansion never halts] `ȧ ≠ 0`.**  Whenever the squared Hubble rate is
positive (in particular under the `friedmann_rhs_pos` hypotheses) the scale factor
has nonzero time derivative — the expansion cannot come to an instantaneous stop.
Combined with `friedmann_rhs_pos`: an open/flat universe with positive density and
`Λ ≥ 0` expands (or contracts) monotonically, never turning around. -/
theorem expansion_never_halts (a : Time → ℝ) (t : Time)
    (hHpos : 0 < (hubbleConstant a t) ^ 2) : ∂ₜ a t ≠ 0 := by
  intro h
  have hzero : (hubbleConstant a t) ^ 2 = 0 := by
    simp only [hubbleConstant, h, zero_div, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  rw [hzero] at hHpos
  exact lt_irrefl 0 hHpos


/-! ## §D — the ΛCDM deceleration parameter, eternal expansion, and the Big Bang -/

/-- **[The ΛCDM deceleration parameter] `q₀ = ½(Ω_m + 2Ω_r − 2Ω_Λ)`.**  For a
spatially flat (`k = 0`, `Λ` folded into the fluid) universe with matter
(`w = 0`), radiation (`w = 1/3`) and dark energy (`w = −1`), the deceleration
parameter is the density-parameter combination `½(Ω_m + 2Ω_r − 2Ω_Λ)` — dark
energy (`Ω_Λ`) drives acceleration, matter and radiation drive deceleration. -/
theorem decelerationParameter_LCDM (a ρm ρr ρΛ ρ p : Time → ℝ) (G c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0)
    (hρz : ρ t ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ 0 0 G c t)
    (hsecond : SecondOrderFriedmann a ρ p 0 G c t)
    (hρsum : ρ t = ρm t + ρr t + ρΛ t)
    (hpsum : p t = ρr t * c ^ 2 / 3 - ρΛ t * c ^ 2) :
    decelerationParameter a t
      = (densityParameter (ρm t) (hubbleConstant a t) G
          + 2 * densityParameter (ρr t) (hubbleConstant a t) G
          - 2 * densityParameter (ρΛ t) (hubbleConstant a t) G) / 2 := by
  rw [decelerationParameter_eq_friedmann ha hd_a haz hd_az hfirst hsecond]
  have hH2 : (hubbleConstant a t) ^ 2 = 8 * Real.pi * G / 3 * ρ t := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    simp only [hubbleConstant, zero_mul, zero_div, sub_zero, add_zero] at h ⊢
    linarith [h]
  have hHz : (hubbleConstant a t) ^ 2 ≠ 0 := by rw [hH2]; positivity
  unfold densityParameter
  rw [hH2, hρsum, hpsum]
  have hsumz : ρm t + ρr t + ρΛ t ≠ 0 := hρsum ▸ hρz
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **[The expansion velocity keeps its sign]** a continuous, nowhere-vanishing
velocity `v` that is positive at one time is positive at *every* time.  Applied to
`v = ȧ` (never zero under the `friedmann_rhs_pos` hypotheses), an expanding
universe expands forever — it never turns around.  Proof by the intermediate value
theorem: a sign change would force a zero. -/
theorem velocity_no_sign_change (v : ℝ → ℝ) (hv : Continuous v)
    (hne : ∀ s, v s ≠ 0) (t₀ t₁ : ℝ) (hpos : 0 < v t₀) : 0 < v t₁ := by
  by_contra hle
  push Not at hle
  have hlt : v t₁ < 0 := lt_of_le_of_ne hle (hne t₁)
  rcases le_total t₀ t₁ with h | h
  · obtain ⟨cc, _, hc0⟩ :=
      intermediate_value_Icc' h hv.continuousOn ⟨hlt.le, hpos.le⟩
    exact hne cc hc0
  · obtain ⟨cc, _, hc0⟩ :=
      intermediate_value_Icc h hv.continuousOn ⟨hlt.le, hpos.le⟩
    exact hne cc hc0

/-- **[The Big-Bang singularity and the age bound]** a currently expanding
(`A′(t₀) = H₀·A(t₀) > 0`), decelerating (concave — `A` lies below its tangent)
scale factor reaches `A = 0` at a finite past time `t_bb ≤ t₀`, and the age is
bounded by the Hubble time, `t₀ − t_bb ≤ 1/H₀`.  The tangent line at `t₀` hits zero
at `t₀ − 1/H₀`; concavity puts `A` at or below it there, and the intermediate value
theorem supplies the zero.  (The concavity hypothesis is the decelerating
condition `Ä ≤ 0`.) -/
theorem bigBang_of_concave (A : ℝ → ℝ) (t₀ H₀ : ℝ)
    (hA : Continuous A) (hA0 : 0 < A t₀) (hH₀ : 0 < H₀)
    (hslope : deriv A t₀ = H₀ * A t₀)
    (htangent : ∀ t, A t ≤ A t₀ + deriv A t₀ * (t - t₀)) :
    ∃ t_bb, t_bb ≤ t₀ ∧ A t_bb = 0 ∧ t₀ - t_bb ≤ 1 / H₀ := by
  set tstar := t₀ - 1 / H₀ with htstar
  have hle : tstar ≤ t₀ := by
    have : 0 < 1 / H₀ := by positivity
    simp only [htstar]; linarith
  have hAstar : A tstar ≤ 0 := by
    have h := htangent tstar
    rw [hslope] at h
    have hts : tstar - t₀ = -(1 / H₀) := by simp only [htstar]; ring
    rw [hts] at h
    have hcancel : H₀ * A t₀ * -(1 / H₀) = -(A t₀) := by
      field_simp
    rw [hcancel] at h
    linarith
  obtain ⟨t_bb, hmem, hbb0⟩ :=
    intermediate_value_Icc hle hA.continuousOn ⟨hAstar, hA0.le⟩
  refine ⟨t_bb, hmem.2, hbb0, ?_⟩
  have hle_bb : tstar ≤ t_bb := hmem.1
  simp only [htstar] at hle_bb ⊢
  linarith


/-- **[The general multi-fluid deceleration parameter] `q = ½ Σ_x Ω_x(1+3w_x)`.**
For a spatially flat universe with an arbitrary finite family of barotropic
components (densities `ρ_x`, equation-of-state coefficients `w_x`), the
deceleration parameter is the density-parameter-weighted sum `½ Σ_x Ω_x(1+3w_x)` —
the `decelerationParameter_LCDM` formula for any component content. -/
theorem decelerationParameter_multifluid {ι : Type*} [Fintype ι]
    (a : Time → ℝ) (ρc wc : ι → ℝ) (ρ p : Time → ℝ) (G c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0)
    (hρz : ρ t ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ 0 0 G c t)
    (hsecond : SecondOrderFriedmann a ρ p 0 G c t)
    (hρsum : ρ t = ∑ i, ρc i)
    (hpsum : p t = (∑ i, wc i * ρc i) * c ^ 2) :
    decelerationParameter a t
      = (∑ i, densityParameter (ρc i) (hubbleConstant a t) G * (1 + 3 * wc i)) / 2 := by
  rw [decelerationParameter_eq_friedmann ha hd_a haz hd_az hfirst hsecond]
  have hH2 : (hubbleConstant a t) ^ 2 = 8 * Real.pi * G / 3 * ρ t := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    simp only [hubbleConstant, zero_mul, zero_div, sub_zero, add_zero] at h ⊢
    linarith [h]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hΩ : ∀ i, densityParameter (ρc i) (hubbleConstant a t) G = ρc i / ρ t := by
    intro i; unfold densityParameter; rw [hH2]; field_simp
  have hsumΩ :
      (∑ i, densityParameter (ρc i) (hubbleConstant a t) G * (1 + 3 * wc i))
        = (∑ i, ρc i * (1 + 3 * wc i)) / ρ t := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [hΩ i]; ring
  have hexpand : (∑ i, ρc i * (1 + 3 * wc i)) = ρ t + 3 * (p t / c ^ 2) := by
    have hsplit : (∑ i, ρc i * (1 + 3 * wc i))
        = (∑ i, ρc i) + 3 * (∑ i, wc i * ρc i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, ← hρsum]
    have hp : (∑ i, wc i * ρc i) = p t / c ^ 2 := by rw [hpsum]; field_simp
    rw [hp]
  rw [hsumΩ, hexpand, hH2]
  field_simp
  ring

/-- **[The expansion velocity never vanishes]** under the `friedmann_rhs_pos`
hypotheses holding at every time (`K ≤ 0`, `ρ > 0`, `Λ ≥ 0`, `G > 0`), the scale
factor's time derivative is nonzero everywhere — the non-vanishing hypothesis of
`velocity_no_sign_change`, derived from the Friedmann equation.  With continuity of
`ȧ` (physical smoothness of the scale factor), `velocity_no_sign_change` then gives
eternal expansion. -/
theorem scaleFactorVelocity_ne_zero (a ρ : Time → ℝ) (k Λ G c : ℝ)
    (hfirst : ∀ t, FirstOrderFriedmann a ρ k Λ G c t)
    (hk : k ≤ 0) (hρ : ∀ t, 0 < ρ t) (hΛ : 0 ≤ Λ) (hG : 0 < G) :
    ∀ t, ∂ₜ a t ≠ 0 :=
  fun t => expansion_never_halts a t
    (friedmann_rhs_pos a ρ k Λ G c t (hfirst t) hk (hρ t) hΛ hG)

noncomputable section Herglotz

/-! ## Nonconservative (Herglotz) Friedmann dynamics

Wazny–Csillag–Pinto–Harko (arXiv:2511.16304) reformulate `f(R,T)` gravity through the
Herglotz action-dependent variational principle.  In a cosmological setting the
Herglotz one-form reduces to a single function of time `φ(t)`, and at `f = R` the field
equations become the nonconservative Friedmann pair carried here, together with its
reduction to `FirstOrderFriedmann` at `φ = 0`, its effective-source form, and the
condition under which the Herglotz function acts as a cosmological constant.  The
covariant field equations are `Relativity.SemiClassical.HerglotzGravity`. -/

/-! ### §A — the nonconservative Friedmann pair at `f = R` -/

/-- **The first nonconservative Friedmann equation**: `3H² − 3φH = 8πρ` — the Herglotz
function drains the expansion side. -/
def HerglotzFriedmannI (H φ ρ : ℝ) : Prop :=
  3 * H ^ 2 - 3 * φ * H = 8 * Real.pi * ρ

/-- **The second nonconservative Friedmann equation**:
`2Ḣ + φH − φ̇ + φ² = −8π(ρ + p)`. -/
def HerglotzFriedmannII (H H' φ φ' ρ p : ℝ) : Prop :=
  2 * H' + φ * H - φ' + φ ^ 2 = -(8 * Real.pi) * (ρ + p)

/-- At `φ = 0` the pair is the standard flat pair `3H² = 8πρ`, `2Ḣ = −8π(ρ+p)`. -/
theorem herglotzFriedmann_zero (H H' ρ p : ℝ) :
    (HerglotzFriedmannI H 0 ρ ↔ 3 * H ^ 2 = 8 * Real.pi * ρ)
      ∧ (HerglotzFriedmannII H H' 0 0 ρ p ↔ 2 * H' = -(8 * Real.pi) * (ρ + p)) := by
  constructor
  · unfold HerglotzFriedmannI
    constructor <;> intro h <;> linarith [h]
  · unfold HerglotzFriedmannII
    constructor <;> intro h <;> linarith [h]

/-- **The weld to the repository's Friedmann equation**: at `φ = 0`, flat spatial
sections, zero cosmological constant, and `G = c = 1`, the first nonconservative
equation *is* `FriedmannEquation.FirstOrderFriedmann` for the Hubble rate of the scale
factor. -/
theorem herglotzFriedmannI_zero_iff_firstOrder (a ρ : Time → ℝ) (t : Time) :
    HerglotzFriedmannI (∂ₜ a t / a t) 0 (ρ t)
      ↔ FirstOrderFriedmann a ρ 0 0 1 1 t := by
  unfold HerglotzFriedmannI FirstOrderFriedmann
  constructor <;> intro h <;> (ring_nf at h ⊢; linarith [h])

/-! ### §B — the effective source and the cosmological-constant condition -/

/-- **The Herglotz effective density** `ρ_eff = 3φH/(8π)`. -/
def herglotzEffectiveDensity (φ H : ℝ) : ℝ := 3 * φ * H / (8 * Real.pi)

/-- **The Herglotz effective pressure** `p_eff = (−2φH − φ̇ + φ²)/(8π)`. -/
def herglotzEffectivePressure (φ φ' H : ℝ) : ℝ :=
  (-(2 * φ * H) - φ' + φ ^ 2) / (8 * Real.pi)

/-- The first equation in effective-source form:
`3H² = 8π(ρ + ρ_eff)` — the Herglotz drain read as dark source. -/
theorem herglotzFriedmannI_iff_effective (H φ ρ : ℝ) :
    HerglotzFriedmannI H φ ρ
      ↔ 3 * H ^ 2 = 8 * Real.pi * (ρ + herglotzEffectiveDensity φ H) := by
  unfold HerglotzFriedmannI herglotzEffectiveDensity
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor <;> intro h
  · field_simp
    linarith [h]
  · field_simp at h
    linarith [h]

/-- **The Herglotz function is a cosmological constant exactly on the Riccati flow**:
`ρ_eff + p_eff = 0` (the `w = −1` vacuum equation of state) if and only if

  `φ̇ = φH + φ²`.

This is the paper's "the Herglotz vector can play the role of a cosmological constant,
providing an alternative mechanism for accelerated expansion", as an exact
condition. -/
theorem herglotz_vacuum_equationOfState_iff (φ φ' H : ℝ) :
    herglotzEffectiveDensity φ H + herglotzEffectivePressure φ φ' H = 0
      ↔ φ' = φ * H + φ ^ 2 := by
  unfold herglotzEffectiveDensity herglotzEffectivePressure
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor <;> intro h
  · field_simp at h
    linarith [h]
  · field_simp
    linarith [h]

/- ZIL-BEGIN -/


zil attach Cosmology.FLRW.Dynamics.herglotzFriedmannI_zero_iff_firstOrder where
  formalizes @ "claim:the-nonconservative-friedmann-pair-at-vanishing-herglotz-function-is-the-repositorys-friedmann-equation-the-dissipative-cosmology-welds-to-the-existing-flrw-sector",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304",
  supported_by @ "lean:ClassicalMechanics.HerglotzContactSlice.effectiveLagrangian"

zil attach Cosmology.FLRW.Dynamics.herglotz_vacuum_equationOfState_iff where
  derives @ "claim:the-herglotz-function-acts-as-a-cosmological-constant-exactly-when-its-flow-satisfies-the-riccati-equation-phi-dot-equals-phi-h-plus-phi-squared-the-papers-accelerated-expansion-mechanism-as-an-exact-condition",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304",
  caveat @ "claim:the-covariant-herglotz-f-r-t-field-equations-at-general-f-the-generalized-balance-current-and-the-numerical-cosmological-fits-are-not-formalized-the-pointwise-pair-is-the-formalized-face"

/- ZIL-END -/

end Herglotz

end Cosmology.FLRW.Dynamics

