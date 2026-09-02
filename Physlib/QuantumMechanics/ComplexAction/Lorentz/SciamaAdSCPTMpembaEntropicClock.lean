/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
public import Physlib.Optics.TemporalDoubleSlit
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
meta import Zil

/-!
# The Mpemba clock is the entropic clock: `k_BT/ℏ` under both experiments

The Mpemba chain so far computed the *rates* (dipolar `b`, GKSL spectrum, ab-initio inputs) but left
temperature as an external dial.  This module routes both experiments through the arc's **entropic clock**
`ω_E = k_BT/ℏ` (`thermalEntropicRate`) — temperature enters the dynamics *only* as the tick rate of
entropic time:

* **§1 — occupation bounds** (`boseOccupation_entropic_bounds`): for `x = ω/ω_E > 0` the thermal occupation
  obeys  `ω_E/ω − 1 < n̄ < ω_E/ω`  — exact two-sided bounds from `x + 1 < eˣ` alone.
* **§2 — the ion assumption derived** (`decoherence_rate_entropic_clock_window`): a bath-coupled qubit has
  `γ = A·n̄(ω₀, T)`, so  `(A/ω₀)·ω_E − A < γ < (A/ω₀)·ω_E`:  the decoherence rate is **entropic-clock
  linear with a temperature-independent bounded offset**.  The trapped-ion paper's *only* physical
  assumption — "the qubit's decoherence rate is monotonically increasing with the bath's temperature" — is
  a theorem of the entropic clock: hotter means the entropic clock ticks faster, in exact ratio, and the
  Mpemba temperature diagram `(γ_i′, γ_f′)` is a *temperature* diagram `T_i/T_f = γ_i′/γ_f′`.
* **§3 — the NMR arrow bracketed** (`polarization_is_clock_ratio`, `detailed_balance_entropic_arrow`): the
  rate-matrix polarization is the clock ratio `ε = ω₀/(2ω_E)`, and the paper's first-order detailed-balance
  factors bracket the exact Boltzmann arrow:  `1 − 2ε < e^{−ℏω₀/k_BT} < 1 − ε`  (for `0 < ε < ½`) — the
  asymmetry that makes the thermal state the attractor *is* the entropic clock's arrow.
* **§4 — crossing covariance** (`mpembaCrossingTime_entropic_units`, `tick_count_is_rate_ratio`):
  measuring rates per entropic tick (`λ/ω_E`) rescales the crossing to entropic time exactly:
  `t*_ent = ω_E·t*` — the Mpemba crossing is a statement about a number of entropic ticks, invariant of the
  laboratory second; and conversions between any two clocks' counts are pure rate ratios, independent of
  the event — no absolute duration survives a translation.  The SI second is not a neutral duration but a
  **very specific description**: `9 192 631 770` periods of the *unperturbed* ground-state hyperfine
  transition of `¹³³Cs` — one isotope, one magnetic electron–nucleus transition (an `α⁴(m_e/m_p)`-rung
  magnetic clock, kin to the dipolar `b`), with "unperturbed" removing the bath *by convention* (real
  realizations subtract the blackbody/thermal shift — the entropic clock's own intrusion — plus Zeeman,
  collisional, Doppler), referenced to geoid proper time (TAI's relativistic convention).  The second is
  defined in the reversible-sector idealization with the bath explicitly subtracted; the e-fold
  self-calibration is complementary precisely because it needs no such idealization
  (cf. `Clock/EntropicAgreement`: the action-rate calibration is a visible model premise, never a claim
  that entropy alone defines an SI second).  **Absolute by convention, relative in use**
  (`realizedClockRate`, `absolute_anchor_cancels_in_translation`, `translation_is_relative_shift`,
  `rapidity_realization_shift`): every laboratory realizes the unperturbed anchor as `ν₀(1+δ)` with a
  *computed* relative shift `δ` (bath/blackbody — entering through `ω_E`; motion — `δ = 1/cosh η − 1`;
  potential — `Φ/c²`, cited), and the anchor `ν₀` **cancels from every translation between realized
  clocks**: what translates is only the relative changes.  The absolute unit is a gauge choice; the
  computed `δ`'s are the physical content; the crossing needs neither.
* **§4'' — heating as rapidity** (`heating_scales_entropic_clock`, `thermal_rapidity_occupation`, with the
  `complexBoost_group` law ZIL-linked — importing it would cycle through the four-clocks chain): adding
  energy changes entropic time **as a group action**.  On the clock,
  heating is linear: `ω_E(cT) = c·ω_E(T)`.  On the second-quantized vacuum, heating is a **hyperbolic
  rotation**: the thermofield Bogoliubov angle at `x = ω/ω_E` (with `tanh θ = e^{−x/2}`) satisfies
  `cosh 2θ = 1 + 2n̄` — the occupation is `sinh²θ`, so raising `T` raises the thermal rapidity, and
  successive boosts **compose additively** (`Λ(θ₁)Λ(θ₂) = Λ(θ₁+θ₂)`, the same `SO(1,1)` cosh/sinh group as
  the special-relativistic `lorentzFactor` and the BW strip — acceleration rapidity and thermal rapidity
  are one group, which is the Unruh connection at the group level).
* **§5 — contraction** (reused `entropic_generator_flow_contracts`): the dissipative sector doing the
  relaxing is the `Re λ < 0` entropic component of the three-clock split.

Numerical closure (`mpemba_ab_initio_inputs.py` §entropic-time): at `T = 295 K`, `ω_E = 3.86×10¹³ s⁻¹`;
NMR: `2ε = 8.1×10⁻⁵` and the exact arrow `e^{−ℏω₀/k_BT}` sits inside the `(1−2ε, 1−ε)` bracket to
`O(ε²) ≈ 10⁻⁹`; `K₀/ω_E = 6.1×10⁻¹⁵`, crossing `τ* = ω_E t* ≈ 2.7×10¹⁴` entropic ticks; ION: the
strong-ME dial ratio maps to `T_SME/T_f = γ′_{SME}/γ_f′ = 5.1×10⁻³`.

Honest scope: `γ = A·n̄` is the standard weak-coupling bath rate (cited; the paper's own blackbody example);
the bounds are exact but the identification of `A` with a specific atomic rate is the ab-initio scripts'
content; §2 gives the high-`T` window, not the full Planck curve.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
  (matsubaraFreqBoson matsubaraFreqBoson_zero)

open Physlib.Optics.TemporalDoubleSlit
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing

/-! ## §1. Two-sided entropic-clock bounds on the thermal occupation -/

/-- **[Occupation bounds from the entropic clock]** — for `x > 0`,
`1/x − 1 < 1/(eˣ − 1) < 1/x`: the thermal occupation is the inverse clock ratio up to a bounded unit.
Both sides come from `x + 1 < eˣ` alone. -/
theorem boseOccupation_entropic_bounds {x : ℝ} (hx : 0 < x) :
    1 / x - 1 < 1 / (Real.exp x - 1) ∧ 1 / (Real.exp x - 1) < 1 / x := by
  have hexp : x + 1 < Real.exp x := Real.add_one_lt_exp hx.ne'
  have hden : 0 < Real.exp x - 1 := by linarith
  constructor
  · by_cases h1 : 1 ≤ x
    · have hle : 1 / x ≤ 1 := by
        rw [div_le_one hx]
        exact h1
      have hR : 0 < 1 / (Real.exp x - 1) := by positivity
      linarith
    · rw [not_le] at h1
      have hneg : (1 - x) * Real.exp x < 1 := by
        have h2 : -x + 1 < Real.exp (-x) := Real.add_one_lt_exp (by linarith : -x ≠ 0)
        have h3 : (1 - x) < Real.exp (-x) := by linarith
        have h4 := mul_lt_mul_of_pos_right h3 (Real.exp_pos x)
        rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h4
      rw [div_sub_one hx.ne', div_lt_div_iff₀ hx hden]
      nlinarith [Real.exp_pos x]
  · rw [div_lt_div_iff₀ hden hx]
    linarith

/-! ## §2. The trapped-ion assumption derived: γ is entropic-clock linear -/

/-- **[The decoherence rate is the entropic clock, windowed]** — a bath-coupled qubit with transition
frequency `ω₀` and coupling rate `A` has `γ = A·n̄`, hence
`(A/ω₀)·ω_E − A < γ < (A/ω₀)·ω_E` with `ω_E = k_BT/ℏ` (`thermalEntropicRate`): temperature enters the
decoherence rate **only through the entropic clock**, up to a temperature-independent offset bounded by
`A`.  The trapped-ion paper's sole physical assumption (γ monotone in `T`) is this linearity; the Mpemba
dial diagram is a temperature diagram `T_i/T_f = γ_i′/γ_f′`. -/
theorem decoherence_rate_entropic_clock_window
    {A ω₀ kB T ℏ : ℝ} (hA : 0 < A) (hω : 0 < ω₀)
    (hE : 0 < thermalEntropicRate kB T ℏ) :
    A / ω₀ * thermalEntropicRate kB T ℏ - A
        < A * boseEinstein (thermalEntropicRate kB T ℏ)⁻¹ ω₀
      ∧ A * boseEinstein (thermalEntropicRate kB T ℏ)⁻¹ ω₀
        < A / ω₀ * thermalEntropicRate kB T ℏ := by
  set ωE := thermalEntropicRate kB T ℏ with hωE
  have hx : 0 < ωE⁻¹ * ω₀ := by positivity
  obtain ⟨hlo, hhi⟩ := boseOccupation_entropic_bounds hx
  have hinv : 1 / (ωE⁻¹ * ω₀) = ωE / ω₀ := by
    field_simp
  rw [hinv] at hlo hhi
  unfold boseEinstein
  constructor
  · have heq : A / ω₀ * ωE - A = A * (ωE / ω₀ - 1) := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_left hlo hA
  · have heq : A / ω₀ * ωE = A * (ωE / ω₀) := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_left hhi hA

/-! ## §3. The NMR arrow: polarization = clock ratio, detailed balance bracketed -/

/-- **[The polarization is the clock ratio]** — `ε = ℏω₀/(2k_BT) = ω₀/(2ω_E)`: the rate-matrix asymmetry
parameter is the qubit frequency measured in entropic ticks. -/
theorem polarization_is_clock_ratio {kB T ℏ ω₀ : ℝ} (hk : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0) :
    ℏ * ω₀ / (2 * (kB * T)) = ω₀ / (2 * thermalEntropicRate kB T ℏ) := by
  unfold thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
  field_simp

/-- **[First-order detailed balance brackets the exact entropic arrow]** — for `0 < ε < ½`:
`1 − 2ε < e^{−2ε} < 1 − ε`.  The paper's linearized down-rate factor `(1−ε)` overestimates and `(1−2ε)`
underestimates the exact Boltzmann factor `e^{−ℏω₀/k_BT}` — the relaxation arrow is the entropic clock's,
to `O(ε²)`. -/
theorem detailed_balance_entropic_arrow {ε : ℝ} (h0 : 0 < ε) (h2 : ε < 1 / 2) :
    1 - 2 * ε < Real.exp (-(2 * ε)) ∧ Real.exp (-(2 * ε)) < 1 - ε := by
  constructor
  · have hlow := Real.add_one_lt_exp (x := -(2 * ε)) (by linarith)
    linarith
  · have hup : 1 + 2 * ε < Real.exp (2 * ε) := by
      have hup' := Real.add_one_lt_exp (x := 2 * ε) (by linarith)
      linarith
    have hstep : Real.exp (-(2 * ε)) * (1 + 2 * ε) < 1 := by
      have hh : Real.exp (-(2 * ε)) * (1 + 2 * ε)
          < Real.exp (-(2 * ε)) * Real.exp (2 * ε) :=
        mul_lt_mul_of_pos_left hup (Real.exp_pos _)
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
    nlinarith [Real.exp_pos (-(2 * ε)), hstep]

/-! ## §4. Crossing covariance: entropic-time units -/

/-- **[The crossing time is entropic-tick covariant]** — measuring the two rates per entropic tick
(`λ/ω_E`) rescales the crossing time to entropic time exactly: `t*_ent = ω_E · t*`.  The Mpemba crossing
is a count of entropic ticks, independent of the laboratory second. -/
theorem mpembaCrossingTime_entropic_units (a b lam2 lam3 ωE : ℝ) :
    mpembaCrossingTime a b (lam2 / ωE) (lam3 / ωE) = ωE * mpembaCrossingTime a b lam2 lam3 := by
  unfold mpembaCrossingTime
  rw [div_sub_div_same, div_div_eq_mul_div]
  ring

/-- **[No absolute duration survives a conversion]** — for any event of duration `t ≠ 0`, the ratio of two
clocks' tick counts is the ratio of their rates, independent of the event: translating "to seconds" is
re-expressing one clock's count in another's — where "the second" is itself a specific clock's count (the
unperturbed `¹³³Cs` hyperfine transition, bath subtracted by convention, geoid-referenced), not an absolute
duration. -/
theorem tick_count_is_rate_ratio (ω₁ ω₂ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (ω₂ * t) / (ω₁ * t) = ω₂ / ω₁ :=
  mul_div_mul_right ω₂ ω₁ ht

/-- A laboratory's realization of the absolute (unperturbed, bath-removed) anchor `ν₀` under total
fractional shift `δ`: `ν = ν₀(1+δ)`.  The shifts are computed physics — bath/blackbody through `ω_E`,
motion through `1/cosh η − 1`, potential through `Φ/c²` (cited). -/
def realizedClockRate (ν₀ sh : ℝ) : ℝ := ν₀ * (1 + sh)

/-- **[The absolute anchor cancels from every translation]** — the ratio of two realized clocks is the
ratio of their shift factors alone: `ν₀` drops out.  The bath-removed absolute unit is a gauge choice;
translations between laboratories are computed entirely from relative changes. -/
theorem absolute_anchor_cancels_in_translation (ν₀ s₁ s₂ : ℝ) (hν : ν₀ ≠ 0) :
    realizedClockRate ν₀ s₁ / realizedClockRate ν₀ s₂ = (1 + s₁) / (1 + s₂) := by
  unfold realizedClockRate
  rw [mul_div_mul_left _ _ hν]

/-- **[The translation factor is the relative shift difference]** — exactly,
`(1+δ₁)/(1+δ₂) − 1 = (δ₁−δ₂)/(1+δ₂)`: what a translation adds to unity is the *difference* of the computed
shifts (rescaled by the reference realization) — first-order metrology, stated exactly. -/
theorem translation_is_relative_shift (s₁ s₂ : ℝ) (h : 1 + s₂ ≠ 0) :
    (1 + s₁) / (1 + s₂) - 1 = (s₁ - s₂) / (1 + s₂) := by
  field_simp
  ring

/-- **[The rapidity shift is a realized-clock shift]** — a clock moving at rapidity `η` realizes the anchor
at `ν₀/cosh η`, i.e. with computed relative shift `δ = 1/cosh η − 1`: the special-relativistic correction
enters the realization dictionary as one more computed `δ`. -/
theorem rapidity_realization_shift (ν₀ η : ℝ) :
    realizedClockRate ν₀ (1 / lorentzFactor η - 1) = ν₀ / lorentzFactor η := by
  unfold realizedClockRate lorentzFactor
  have hc : Real.cosh η ≠ 0 := (Real.cosh_pos η).ne'
  field_simp
  ring

/-- **[The Mpemba differential gravimeter]** — two stations with *equal proper physics* (same molecule,
same bath: the self-calibration fixes one shared proper crossing `tstar`) at heights `h₁, h₂`, timed by one
common coordinate clock, have coordinate crossings `tᵢ = tstar/(1 + g·hᵢ/c²)`.  Then exactly:
**(i)** the ratio is pure redshift, `t₁/t₂ = (1+g·h₂/c²)/(1+g·h₁/c²)`; **(ii)** the recovery identity
`g·(h₂−h₁)/c² = (t₁/t₂ − 1)·(1+g·h₁/c²)` — every right-hand quantity is measured, so the planet's
effective `g` is recovered.  The self-calibration removes local-physics systematics: no calibrated unit is
needed at either station.  Feasibility (script `[GRAVIMETER]`): per metre on Earth the crossing shifts by
`≈ 7.4×10⁻¹⁶ s` of the NMR `t* = 6.78 s` — exact in principle, optical-clock-level timing in practice. -/
theorem mpemba_differential_gravimeter (g h₁ h₂ c tstar t₁ t₂ : ℝ)
    (h1 : 1 + g * h₁ / c ^ 2 ≠ 0) (h2 : 1 + g * h₂ / c ^ 2 ≠ 0) (hts : tstar ≠ 0)
    (ht₁ : t₁ = tstar / (1 + g * h₁ / c ^ 2)) (ht₂ : t₂ = tstar / (1 + g * h₂ / c ^ 2)) :
    t₁ / t₂ = (1 + g * h₂ / c ^ 2) / (1 + g * h₁ / c ^ 2)
      ∧ g * (h₂ - h₁) / c ^ 2 = (t₁ / t₂ - 1) * (1 + g * h₁ / c ^ 2) := by
  subst ht₁ ht₂
  have hr : tstar / (1 + g * h₁ / c ^ 2) / (tstar / (1 + g * h₂ / c ^ 2))
      = (1 + g * h₂ / c ^ 2) / (1 + g * h₁ / c ^ 2) := by
    rw [div_div_div_eq]
    rw [mul_comm tstar (1 + g * h₂ / c ^ 2), mul_div_mul_right _ _ hts]
  refine ⟨hr, ?_⟩
  rw [hr]
  field_simp
  ring

/-- Thermal surface-roughness spectrum (equipartition): `S(k) = k_BT/(A·(ρg + σk²))` — the thermally
excited capillary–gravity wave amplitude at wavenumber `k` over area `A`, measurable by surface light
scattering.  Gravity is the **infrared cutoff** of the bath's surface fluctuations. -/
def thermalRoughness (kB T ρ g σ k A : ℝ) : ℝ := kB * T / (A * (ρ * g + σ * k ^ 2))

/-- **[Optical roughness reads the entropic clock, capped by gravity]** —
`A·(ρg + σk²)·S(k) = ℏ·ω_E`: the scattered-light spectrum is the entropic clock's equipartition output,
with gravity setting the long-wavelength plateau. -/
theorem roughness_reads_entropic_clock (kB T ρ g σ k A ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (hden : A * (ρ * g + σ * k ^ 2) ≠ 0) :
    A * (ρ * g + σ * k ^ 2) * thermalRoughness kB T ρ g σ k A
      = ℏ * thermalEntropicRate kB T ℏ := by
  unfold thermalRoughness thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
  field_simp
  have hgrp : A * (ρ * g + σ * k ^ 2) * kB * T = (A * (ρ * g + σ * k ^ 2)) * (kB * T) := by
    ring
  rw [hgrp]
  exact mul_div_cancel_left₀ _ hden

/-- **[The roughness gravimeter]** — at the long-wavelength plateau (`k = 0`):
`g = k_BT/(ρ·A·S₀)`: optically measured thermal surface roughness computes effective gravity, with the
bath itself (the entropic clock) as the source. -/
theorem roughness_gravimeter (kB T ρ g A : ℝ)
    (hρ : ρ ≠ 0) (hg : g ≠ 0) (hA : A ≠ 0) (hkT : kB * T ≠ 0) :
    kB * T / (ρ * A * thermalRoughness kB T ρ g 0 0 A) = g := by
  obtain ⟨hkB, hT⟩ := mul_ne_zero_iff.mp hkT
  unfold thermalRoughness
  field_simp
  ring

/-! ## §4''. Heating as rapidity: the group action on the clock and the vacuum -/

/-- **[Heating is linear on the clock]** — scaling the temperature scales the entropic tick rate:
`ω_E(cT) = c·ω_E(T)`.  Adding energy changes entropic time; on the clock rate the action is the scaling
representation. -/
theorem heating_scales_entropic_clock (kB T ℏ c : ℝ) :
    thermalEntropicRate kB (c * T) ℏ = c * thermalEntropicRate kB T ℏ := by
  unfold thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
  ring

/-- **Time-dilation decoherence rate** (Pikovski–Zych–Costa–Brukner): a composite with `N` internal
thermal modes, in superposition across height `x` in gravity `g`, decoheres at
`Γ = (gx/c²)·√(N/2)·ω_E` — the gravitational redshift **multiplied by the entropic clock and by the
collective factor `√N`**, not by a dissipative rate.  This is the entropic-time observable with practical
gravimetric sensitivity: `Γ ≈ 10³ s⁻¹` for a gram over a micrometre at room temperature. -/
def dilationDecoherenceRate (g x c ωE N : ℝ) : ℝ := g * x / c ^ 2 * Real.sqrt (N / 2) * ωE

/-- **[The dilation-decoherence gravimeter]** — `Γ` is linear in `g`, and inverts exactly:
`g = c²·Γ/(x·√(N/2)·ω_E)`.  Measuring a *rate* (an entropic-sector observable, fractional precision
`δΓ/Γ` at the percent level) computes the planet's effective gravity at the same fractional precision —
the amplification over crossing-timing is `ω_E·√(N/2)·(x/c²)` replacing `t*·Φ/c²`: the redshift rides the
entropic clock instead of the dissipative rate. -/
theorem dilation_gravimeter_recovery (g x c ωE N : ℝ)
    (hx : x ≠ 0) (hc : c ≠ 0) (hω : ωE ≠ 0) (hN : 0 < N) :
    dilationDecoherenceRate g x c ωE N * c ^ 2 / (x * Real.sqrt (N / 2) * ωE) = g := by
  have hs : Real.sqrt (N / 2) ≠ 0 := by
    have : (0:ℝ) < N / 2 := by linarith
    positivity
  unfold dilationDecoherenceRate
  field_simp

/-- **[Temperature enters the gravimeter only through the entropic clock]** — heating scales the
dilation-decoherence rate linearly, `Γ(cT) = c·Γ(T)`: the bath's sole entry point is `ω_E`
(`heating_scales_entropic_clock`), so the temperature systematic of the entropic gravimeter is the
clock-scaling law itself. -/
theorem dilation_rate_heating_scaling (g x c kB T ℏ c₀ N : ℝ) :
    dilationDecoherenceRate g x c (thermalEntropicRate kB (c₀ * T) ℏ) N
      = c₀ * dilationDecoherenceRate g x c (thermalEntropicRate kB T ℏ) N := by
  unfold dilationDecoherenceRate
  rw [heating_scales_entropic_clock]
  ring

/-- **[The planet-ratio gravimeter is unit-free]** — the same apparatus (`x, N, T` fixed) transported
between two planets measures the gravity *ratio* with everything else cancelling:
`Γ₁/Γ₂ = g₁/g₂` exactly.  No calibration, no unit, no clock: the ratio of two measured decoherence rates
is the ratio of the two effective gravities. -/
theorem planet_ratio_gravimeter (g₁ g₂ x c ωE N : ℝ)
    (hx : x ≠ 0) (hc : c ≠ 0) (hω : ωE ≠ 0) (hN : 0 < N) (hg₂ : g₂ ≠ 0) :
    dilationDecoherenceRate g₁ x c ωE N / dilationDecoherenceRate g₂ x c ωE N = g₁ / g₂ := by
  have hs : Real.sqrt (N / 2) ≠ 0 := by
    have hN2 : (0:ℝ) < N / 2 := by linarith
    positivity
  unfold dilationDecoherenceRate
  field_simp

/-- **[Tolman–Ehrenfest is the heating-scaling law at the redshift factor]** — in thermal equilibrium in
gravity the temperature redshifts, `T(h) = T₀·(1 + s)` with `s` the potential shift, so the entropic clock
in an equilibrium column obeys `ω_E(h) = (1+s)·ω_E(0)` — exactly `heating_scales_entropic_clock` at
`c₀ = 1+s`: the bath in a gravitational field *is* a redshifted clock, by equilibrium alone. -/
theorem tolman_entropic_clock (kB T₀ ℏ s : ℝ) :
    thermalEntropicRate kB ((1 + s) * T₀) ℏ = (1 + s) * thermalEntropicRate kB T₀ ℏ :=
  heating_scales_entropic_clock kB T₀ ℏ (1 + s)


/-- **[Heating is a hyperbolic rotation on the vacuum]** — the thermofield Bogoliubov angle `θ` at
`x = ω/ω_E` (defined by `tanh θ = e^{−x/2}`) satisfies **`cosh 2θ = 1 + 2n̄(x)`**: the second-quantized
occupation is `sinh²θ`, and raising the temperature (lowering `x`) raises the thermal rapidity.  Heating
acts on the vacuum in the same `SO(1,1)` cosh/sinh group as a Lorentz boost — additive composition is
`complexBoost_group` (ZIL-linked; an import would cycle through the four-clocks chain). -/
theorem thermal_rapidity_occupation {θ x : ℝ} (hx : 0 < x)
    (hθ : Real.tanh θ = Real.exp (-(x / 2))) :
    Real.cosh (2 * θ) = 1 + 2 * boseEinstein 1 x := by
  have hgt : x + 1 < Real.exp x := Real.add_one_lt_exp hx.ne'
  have hex : Real.exp x - 1 ≠ 0 := by
    intro h0
    nlinarith
  have hch : Real.cosh θ ≠ 0 := (Real.cosh_pos θ).ne'
  have hsinh : Real.sinh θ = Real.exp (-(x / 2)) * Real.cosh θ := by
    rw [← hθ, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hexp2 : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hid := Real.cosh_sq_sub_sinh_sq θ
  rw [hsinh, mul_pow, hexp2] at hid
  have hexpx : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg, inv_eq_one_div]
  rw [hexpx] at hid
  have hexpos : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hA : Real.cosh θ ^ 2 * (Real.exp x - 1) = Real.exp x := by
    field_simp at hid
    nlinarith [hid]
  have hcv : Real.cosh θ ^ 2 = Real.exp x / (Real.exp x - 1) :=
    eq_div_of_mul_eq hex hA
  have hS : Real.sinh θ ^ 2 * (Real.exp x - 1) = 1 := by
    linear_combination hA + (1 - Real.exp x) * (Real.cosh_sq_sub_sinh_sq θ)
  rw [Real.cosh_two_mul]
  unfold boseEinstein
  rw [one_mul, hcv]
  field_simp
  linear_combination hS

/-- **[The Mpemba clock is the entropic clock]** — **(i)** the decoherence rate is entropic-clock linear
with a bounded offset (the ion paper's assumption, derived); **(ii)** the NMR polarization is the clock
ratio; **(iii)** first-order detailed balance brackets the exact entropic arrow; **(iv)** the crossing time
is a count of entropic ticks; **(v)** the relaxing sector contracts (`Re λ < 0`, the entropic component of
the three-clock split).  Temperature never enters the Mpemba chain except as the tick rate of entropic
time. -/
theorem mpemba_entropic_clock_synthesis
    {A ω₀ kB T ℏ : ℝ} (hA : 0 < A) (hω : 0 < ω₀) (hE : 0 < thermalEntropicRate kB T ℏ)
    (hk : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0)
    {ε : ℝ} (h0 : 0 < ε) (h2 : ε < 1 / 2)
    (a b lam2 lam3 : ℝ) (l : ℂ) (t : ℝ) (hl : l.re < 0) (ht : 0 < t) :
    (A / ω₀ * thermalEntropicRate kB T ℏ - A
        < A * boseEinstein (thermalEntropicRate kB T ℏ)⁻¹ ω₀
      ∧ A * boseEinstein (thermalEntropicRate kB T ℏ)⁻¹ ω₀
        < A / ω₀ * thermalEntropicRate kB T ℏ)
      ∧ (ℏ * ω₀ / (2 * (kB * T)) = ω₀ / (2 * thermalEntropicRate kB T ℏ))
      ∧ (1 - 2 * ε < Real.exp (-(2 * ε)) ∧ Real.exp (-(2 * ε)) < 1 - ε)
      ∧ (mpembaCrossingTime a b (lam2 / thermalEntropicRate kB T ℏ)
            (lam3 / thermalEntropicRate kB T ℏ)
          = thermalEntropicRate kB T ℏ * mpembaCrossingTime a b lam2 lam3)
      ∧ ‖Complex.exp (l * t)‖ < 1 :=
  ⟨decoherence_rate_entropic_clock_window hA hω hE,
    polarization_is_clock_ratio hk hT hℏ,
    detailed_balance_entropic_arrow h0 h2,
    mpembaCrossingTime_entropic_units a b lam2 lam3 _,
    Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.entropic_generator_flow_contracts
      l t hl ht⟩

/-! ## §5. The Sagnac effect: rotation as a synchronization observable (Spavieri–Gillies–Haug 2021)

The realized-clock dictionary (§4) and its absolute anchor have a classical twin: the choice between
**relative** simultaneity (Einstein synchronization, the Lorentz transform `t' = γ(t − ux/c²)`, `x`-
dependent) and **absolute** simultaneity (Tangherlini–Selleri, `t' = t/γ`, `x`-independent) — the same
`t/γ = ν₀/cosh η` that the realized clock reads (`rapidity_realization_shift`).  The Sagnac effect is
where the two are discriminated: on a rotating platform the counter-propagating light times differ by
`ΔT = 4Aω/(c²−v²)`, a direct reading of the angular velocity `ω` — the rotational sibling of the
gravimeter recoveries of §4'.  (Spavieri, Gillies & Haug, *The Sagnac effect and the role of
simultaneity in relativity theory*, J. Mod. Opt. 68 (2021) 202.) -/

/-- **[Lorentz-transform time — relative simultaneity]** — `t' = γ(t − ux/c²)`: the transformed time
depends on position `x`, so equal-`t` events are *not* synchronous in the moving frame. -/
def ltTime (γ u c t x : ℝ) : ℝ := γ * (t - u * x / c ^ 2)

/-- **[Tangherlini–Selleri time — absolute simultaneity]** — `t' = t/γ`: no position dependence,
simultaneity conserved.  This is the realized-clock anchor `ν₀/cosh η` read as a time transform. -/
def ltaTime (γ t : ℝ) : ℝ := t / γ

/-- **[the simultaneity gap of the Lorentz transform]** — two events at equal coordinate time `t` but
positions `x₁, x₂` acquire Lorentz times differing by `γu(x₂−x₁)/c²`: relative simultaneity. -/
theorem lt_relative_simultaneity (γ u c t x₁ x₂ : ℝ) :
    ltTime γ u c t x₁ - ltTime γ u c t x₂ = γ * u * (x₂ - x₁) / c ^ 2 := by
  unfold ltTime
  ring

/-- **[the simultaneity dichotomy]** — the absolute (LTA) time of an event is a function of `t` alone,
independent of position, while the Lorentz time of two equal-`t` events at different positions genuinely
differs (`u ≠ 0`, `x₁ ≠ x₂`): the paper's central contrast, absolute vs relative simultaneity. -/
theorem simultaneity_dichotomy {γ u c : ℝ} (hu : u ≠ 0) (hc : c ≠ 0) (hγ : γ ≠ 0)
    {x₁ x₂ : ℝ} (hx : x₁ ≠ x₂) (t : ℝ) :
    ltaTime γ t = ltaTime γ t ∧ ltTime γ u c t x₁ - ltTime γ u c t x₂ ≠ 0 := by
  refine ⟨rfl, ?_⟩
  rw [lt_relative_simultaneity]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hγ hu) (sub_ne_zero.mpr (Ne.symm hx)))
    (pow_ne_zero 2 hc)

/-- **[the missing-section length]** — the Einstein-synchronization time gap between clocks a distance
`L` apart, `δt' = γuL/c²`, corresponds to a missing contour length `BK = c·δt' = γuL/c`: the
space-time discontinuity relative simultaneity introduces on a closed path. -/
theorem missing_section_from_gap {c : ℝ} (hc : c ≠ 0) (γ u L : ℝ) :
    c * (γ * u * L / c ^ 2) = γ * u * L / c := by
  field_simp

/-- **[absolute simultaneity closes the contour]** — the two ground-path legs `L(1+v/c)` (outward) and
`L(1−v/c)` (return) sum to the full closed contour `2L`: with absolute synchronization no section goes
missing. -/
theorem absolute_sync_closes_contour (L v c : ℝ) :
    L * (1 + v / c) + L * (1 - v / c) = 2 * L := by
  ring

/-- **[relative simultaneity opens the contour]** — with Einstein synchronization the covered ground
path is `2L(1−v/c)`, short of `2L` by exactly the missing section `2Lv/c = BK`. -/
theorem relative_contour_deficit (L v c : ℝ) :
    2 * L - 2 * L * (1 - v / c) = 2 * L * v / c := by
  ring

/-- **[Eq. (2): the Sagnac time delay]** — the counter- minus co-propagating flight time around a ring
of radius `r`, `ΔT = 2πr/(c−v) − 2πr/(c+v)`. -/
def sagnacTimeDelay (c v r : ℝ) : ℝ := 2 * Real.pi * r / (c - v) - 2 * Real.pi * r / (c + v)

/-- **[the closed-form Sagnac delay]** — `ΔT = 4πrv/(c²−v²)`, exact. -/
theorem sagnac_time_delay_closed {c v r : ℝ} (h1 : c - v ≠ 0) (h2 : c + v ≠ 0) :
    sagnacTimeDelay c v r = 4 * Real.pi * r * v / (c ^ 2 - v ^ 2) := by
  unfold sagnacTimeDelay
  rw [div_sub_div _ _ h1 h2, show (c - v) * (c + v) = c ^ 2 - v ^ 2 by ring]
  congr 1
  ring

/-- **[the Sagnac delay reads area × angular velocity]** — substituting `v = ωr` gives
`ΔT = 4Aω/(c²−v²)` with `A = πr²`: the delay is proportional to the enclosed area and the angular
velocity — the ring is a gyroscope. -/
theorem sagnac_delay_area_omega {c ω r : ℝ} (h1 : c - ω * r ≠ 0) (h2 : c + ω * r ≠ 0) :
    sagnacTimeDelay c (ω * r) r = 4 * (Real.pi * r ^ 2) * ω / (c ^ 2 - (ω * r) ^ 2) := by
  rw [sagnac_time_delay_closed h1 h2]
  congr 1
  ring

/-- **[the rotation readout]** — inverting the first-order delay `ΔT = 4Aω/c²`: the angular velocity is
recovered as `ω = c²ΔT/(4πr²)`, every right-hand quantity measured.  The exact analogue of the
gravimeter recoveries — a Sagnac ring measures `ω` as an entropic/simultaneity observable. -/
theorem sagnac_first_order_reads_rotation {r c ΔT ω : ℝ} (hr : r ≠ 0) (hc : c ≠ 0)
    (h : ΔT = 4 * (Real.pi * r ^ 2) * ω / c ^ 2) :
    ω = c ^ 2 * ΔT / (4 * Real.pi * r ^ 2) := by
  rw [h]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **[a single ring reads its normal component]** — a Sagnac ring of effective area `A` senses the
projection `ω_n = n̂·ω` of the rotation onto its normal via `ΔT = 4A·ω_n/c²`, inverting to
`ω_n = c²ΔT/(4A)`.  A strapdown gyroscope bolts the ring to a moving platform and reads one component of
its angular velocity. -/
theorem ring_delay_reads_component {A c ΔT ω : ℝ} (hA : A ≠ 0) (hc : c ≠ 0)
    (h : ΔT = 4 * A * ω / c ^ 2) : ω = c ^ 2 * ΔT / (4 * A) := by
  rw [h]
  field_simp

/-- **[three orthogonal rings reconstruct the rotation-rate magnitude]** — a triad of Sagnac rings along
an orthonormal frame reads `ΔTᵢ = 4A·ωᵢ/c²`, and the magnitude is recovered as
`(c²/4A)·√(ΔT₁²+ΔT₂²+ΔT₃²) = √(ω₁²+ω₂²+ω₃²) = |ω|`: the strapdown optical gyroscope reconstructs the full
angular-velocity vector from the loop holonomies on three axes.  This is how a Sagnac ring triad tracks a
mechanical gyroscope's rotation without contact. -/
theorem sagnac_triad_reconstructs_magnitude {A c ω₁ ω₂ ω₃ : ℝ} (hA : 0 < A) (hc : 0 < c) :
    c ^ 2 / (4 * A)
        * Real.sqrt ((4 * A * ω₁ / c ^ 2) ^ 2 + (4 * A * ω₂ / c ^ 2) ^ 2
          + (4 * A * ω₃ / c ^ 2) ^ 2)
      = Real.sqrt (ω₁ ^ 2 + ω₂ ^ 2 + ω₃ ^ 2) := by
  have hfac : (4 * A * ω₁ / c ^ 2) ^ 2 + (4 * A * ω₂ / c ^ 2) ^ 2 + (4 * A * ω₃ / c ^ 2) ^ 2
      = (4 * A / c ^ 2) ^ 2 * (ω₁ ^ 2 + ω₂ ^ 2 + ω₃ ^ 2) := by ring
  rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), ← mul_assoc,
    show c ^ 2 / (4 * A) * (4 * A / c ^ 2) = 1 by field_simp, one_mul]

/-- **[Eqs. (7)–(9): the linear Sagnac round trip]** — the outward leg `L/(c+v)` and the return leg
`L/c − (v/c)·L/(c+v)` sum to `2L/(c+v)`, the measured round-trip time — the linear (conveyor-belt)
equivalent of the circular delay. -/
theorem linear_sagnac_roundtrip {c v L : ℝ} (hc : c ≠ 0) (hcv : c + v ≠ 0) :
    L / (c + v) + (L / c - v / c * (L / (c + v))) = 2 * L / (c + v) := by
  field_simp
  ring

/-- **[Eq. (20): the Langevin null condition factors into the two Sagnac speeds]** — the rotating-frame
(Langevin–Landau–Lifshitz) null condition `s² + 2ωr·s − (c²−ω²r²) = 0` for the local coordinate light
speed `s` factors as `(s − (c−ωr))(s + (c+ωr))`: the two roots are `c − ωr` and `−(c+ωr)`, i.e. local
speeds `c ∓ v` — the metric *derives* the `c±v` of the Sagnac delay. -/
theorem langevin_null_factorization (s ω r c : ℝ) :
    s ^ 2 + 2 * (ω * r) * s - (c ^ 2 - (ω * r) ^ 2)
      = (s - (c - ω * r)) * (s + (c + ω * r)) := by
  ring

/-- **[the delay follows from the metric]** — the two Langevin local speeds `c−ωr` and `c+ωr`
round-trip to the closed-form Sagnac delay `4Aω/(c²−v²)`: the effect is a consequence of the
rotating-frame metric. -/
theorem sagnac_delay_from_langevin {c ω r : ℝ} (h1 : c - ω * r ≠ 0) (h2 : c + ω * r ≠ 0) :
    2 * Real.pi * r / (c - ω * r) - 2 * Real.pi * r / (c + ω * r)
      = 4 * (Real.pi * r ^ 2) * ω / (c ^ 2 - (ω * r) ^ 2) := by
  have h := sagnac_delay_area_omega (c := c) (ω := ω) (r := r) h1 h2
  unfold sagnacTimeDelay at h
  exact h

/-- **[§3: the general-relativistic circumference dilation]** — the rotating circumference is
`2πr/√(1−ω²r²/c²)`, strictly longer than the flat `2πr` (a second-order effect): the corrections to the
Sagnac proper time are of order `v²/c²`, so the first-order delay is a pure synchronization effect,
unrelated to the platform's acceleration. -/
def rotatingCircumference (r ω c : ℝ) : ℝ := 2 * Real.pi * r / Real.sqrt (1 - (ω * r / c) ^ 2)

/-- **[the rotating circumference exceeds the flat one]** — for `0 < ωr < c`. -/
theorem gr_circumference_exceeds_flat {r ω c : ℝ} (hr : 0 < r) (hωr : 0 < ω * r) (hlt : ω * r < c) :
    2 * Real.pi * r < rotatingCircumference r ω c := by
  unfold rotatingCircumference
  have hc : 0 < c := hωr.trans hlt
  have hx : (ω * r / c) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith
  have hpos : 0 < 1 - (ω * r / c) ^ 2 := by linarith
  have hs1 : Real.sqrt (1 - (ω * r / c) ^ 2) < 1 := by
    have hlt1 : 1 - (ω * r / c) ^ 2 < 1 := by nlinarith [div_pos hωr hc]
    calc Real.sqrt (1 - (ω * r / c) ^ 2) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt hpos.le hlt1
      _ = 1 := Real.sqrt_one
  have hspos : 0 < Real.sqrt (1 - (ω * r / c) ^ 2) := Real.sqrt_pos.mpr hpos
  rw [lt_div_iff₀ hspos]
  exact mul_lt_of_lt_one_right (by positivity) hs1

/-- **[Sagnac synthesis]** — the rotating platform is a clock-synchronization laboratory: **(i)** absolute
simultaneity is position-independent while the Lorentz transform gaps equal-`t` events; **(ii)** the
counter-propagating delay is `4πrv/(c²−v²)`, reading `ω`; **(iii)** absolute synchronization closes the
contour `L(1+v/c)+L(1−v/c) = 2L`.  The Sagnac effect measures rotation the way the entropic clock
measures a bath — through the synchronization it forces. -/
theorem sagnac_simultaneity_synthesis {c v r L : ℝ} (h1 : c - v ≠ 0) (h2 : c + v ≠ 0)
    {γ u : ℝ} (hu : u ≠ 0) (hc : c ≠ 0) (hγ : γ ≠ 0) {x₁ x₂ : ℝ} (hx : x₁ ≠ x₂) (t : ℝ) :
    (ltaTime γ t = ltaTime γ t ∧ ltTime γ u c t x₁ - ltTime γ u c t x₂ ≠ 0)
      ∧ sagnacTimeDelay c v r = 4 * Real.pi * r * v / (c ^ 2 - v ^ 2)
      ∧ L * (1 + v / c) + L * (1 - v / c) = 2 * L :=
  ⟨simultaneity_dichotomy hu hc hγ hx t, sagnac_time_delay_closed h1 h2,
    absolute_sync_closes_contour L v c⟩

/-! ## §6. The Minkowski interval beneath the synchronization convention

The simultaneity dichotomy (§5) is a choice of *time coordinate*; the **Minkowski interval** is what both
choices agree on, because it is read by a single clock and needs no distant synchronization.  Two exact
facts make the link: the interval is Lorentz-invariant, and the absolute-simultaneity time `t/γ` *is* the
proper time of the co-moving clock — so absolute synchronization is the one that reads the invariant,
while relative simultaneity is the convention layered on top.  This is the same invariant that Wick-rotates
onto the Nagao–Nielsen contour (imaginary modular time) where the entropic modulus `e^{−ρt}` lives, and the
same local-unobservability that the equivalence principle expresses for the gravitational potential. -/

/-- **[the Lorentz spatial transform]** — `x' = γ(x − ut)`, shared by the LT and the LTA. -/
def ltSpace (γ u t x : ℝ) : ℝ := γ * (x - u * t)

/-- **[the Minkowski interval is Lorentz-invariant]** — `c²t'² − x'² = c²t² − x²` under the Lorentz
transform, using the defining relation `γ²(c²−u²) = c²`.  The interval is the synchronization-independent
content: it does not depend on how the `t = const` surfaces are drawn. -/
theorem minkowski_interval_lorentz_invariant {γ u c : ℝ} (hγ : γ ^ 2 * (c ^ 2 - u ^ 2) = c ^ 2)
    (hc : c ≠ 0) (t x : ℝ) :
    c ^ 2 * ltTime γ u c t x ^ 2 - ltSpace γ u t x ^ 2 = c ^ 2 * t ^ 2 - x ^ 2 := by
  unfold ltTime ltSpace
  have key : c ^ 2 * (γ * (t - u * x / c ^ 2)) ^ 2 - (γ * (x - u * t)) ^ 2
      = γ ^ 2 * (c ^ 2 - u ^ 2) * (t ^ 2 - x ^ 2 / c ^ 2) := by
    field_simp
    ring
  rw [key, hγ]
  field_simp

/-- **[absolute-simultaneity time is the Minkowski proper time]** — for a clock co-moving at speed `u`
(worldline `x = ut`), the Tangherlini–Selleri time `t/γ` equals the proper time
`√(c²t² − (ut)²)/c` along that worldline.  The absolute anchor of the realized-clock dictionary is
exactly the invariant interval read by a single clock — no synchronization enters. -/
theorem lta_time_is_minkowski_proper_time {γ u c t : ℝ} (hγ : γ ^ 2 * (c ^ 2 - u ^ 2) = c ^ 2)
    (hc : 0 < c) (hγ0 : 0 < γ) (ht : 0 ≤ t) :
    Real.sqrt (c ^ 2 * t ^ 2 - (u * t) ^ 2) / c = ltaTime γ t := by
  unfold ltaTime
  have hcu : c ^ 2 - u ^ 2 = c ^ 2 / γ ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hγ0.ne')]
    linear_combination hγ
  have hfact : c ^ 2 * t ^ 2 - (u * t) ^ 2 = t ^ 2 * (c ^ 2 - u ^ 2) := by ring
  rw [hfact, hcu, show t ^ 2 * (c ^ 2 / γ ^ 2) = (t * c / γ) ^ 2 by rw [div_pow]; ring,
    Real.sqrt_sq (div_nonneg (mul_nonneg ht hc.le) hγ0.le)]
  field_simp

/-- **[the light cone is synchronization-independent]** — a null interval `c²t² = x²` (a light ray, the
two-way speed `c`) stays null under the Lorentz transform: the one thing both simultaneity conventions and
every observer agree on is the cone.  The conventional part is the *slicing*, never the cone. -/
theorem minkowski_null_invariant {γ u c : ℝ} (hγ : γ ^ 2 * (c ^ 2 - u ^ 2) = c ^ 2) (hc : c ≠ 0)
    (t x : ℝ) (hnull : c ^ 2 * t ^ 2 - x ^ 2 = 0) :
    c ^ 2 * ltTime γ u c t x ^ 2 - ltSpace γ u t x ^ 2 = 0 := by
  rw [minkowski_interval_lorentz_invariant hγ hc t x]
  exact hnull

/-! ## §7. The synchronization holonomy: quantifying the convention

The invariant beneath the convention (§6) is locally unobservable, but the convention leaves a *measurable
residue*: the closed-loop integral of the locally-removable offset.  The synchronization gap between two
clocks a distance `dl` apart moving at speed `u` is `u·dl/c²` (`lt_relative_simultaneity`); this density
can be zeroed at any single point by re-synchronizing (choosing the rest frame), but its **loop integral —
the holonomy — cannot**.  Around a ring of radius `r` rotating at `ω` (tangential `v = ωr`),
`∮ (v/c²) dl = 2Aω/c²` with `A = πr²`, and the Sagnac delay is exactly twice this holonomy (to first
order): the quantification method — read the convention off its loop integral. -/

/-- **[the local synchronization offset density]** — `u/c²` per unit length: the removable
first-order gap of `lt_relative_simultaneity`. -/
def syncOffsetDensity (u c : ℝ) : ℝ := u / c ^ 2

/-- **[the ring synchronization holonomy]** — `∮ (v/c²) dl = (ωr/c²)·2πr` around a rotating ring: the
loop integral of the offset density with `v = ωr`. -/
def ringSyncHolonomy (ω r c : ℝ) : ℝ := ω * r / c ^ 2 * (2 * Real.pi * r)

/-- **[the holonomy is area × angular velocity]** — `∮ (v/c²) dl = 2Aω/c²`, `A = πr²`: the loop residue
depends only on the enclosed area and the rotation, not on any point (Stokes for rigid rotation). -/
theorem ring_sync_holonomy_area (ω r c : ℝ) :
    ringSyncHolonomy ω r c = 2 * (Real.pi * r ^ 2) * ω / c ^ 2 := by
  unfold ringSyncHolonomy
  ring

/-- **[the Sagnac delay is twice the holonomy]** — the first-order Sagnac delay `4Aω/c²` is exactly
`2·∮(v/c²)dl`: the delay *measures* the synchronization holonomy.  The relativistic correction (the
`c²−v²` denominator of `sagnac_delay_area_omega`) is second order (`gr_circumference_exceeds_flat`), so to
first order the ring is a holonomy meter. -/
theorem sagnac_delay_first_order_twice_holonomy (ω r c : ℝ) :
    4 * (Real.pi * r ^ 2) * ω / c ^ 2 = 2 * ringSyncHolonomy ω r c := by
  rw [ring_sync_holonomy_area]
  ring

/-- **[the holonomy is a nonzero measurable]** — although the offset density is removable at every point,
the loop holonomy is nonzero whenever the ring actually rotates (`ω ≠ 0`): the quantity that makes the
convention observable. -/
theorem sync_holonomy_nonzero {ω r c : ℝ} (hω : ω ≠ 0) (hr : r ≠ 0) (hc : c ≠ 0) :
    ringSyncHolonomy ω r c ≠ 0 := by
  rw [ring_sync_holonomy_area]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hr))) hω)
    (pow_ne_zero 2 hc)

/-- **[the holonomy inverts to the rotation]** — reading `ω` off the measured holonomy `H = 2Aω/c²`:
`ω = c²H/(2πr²)`.  The method: integrate the local offset around the loop, divide by twice the area over
`c²`.  (Equivalently `ω = c²ΔT/(4πr²)` from the Sagnac delay, `sagnac_first_order_reads_rotation`.) -/
theorem holonomy_reads_rotation {r c H ω : ℝ} (hr : r ≠ 0) (hc : c ≠ 0)
    (h : H = 2 * (Real.pi * r ^ 2) * ω / c ^ 2) :
    ω = c ^ 2 * H / (2 * Real.pi * r ^ 2) := by
  rw [h]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## §8. The optical Sagnac effect: phase, interference, and beat

A real Sagnac gyroscope does not time the light — it reads the **phase** the delay imprints on it.  The two
counter-propagating beams pick up a relative Sagnac phase `Δφ = ω_opt·ΔT = 8πAω/(wlc)` (`ω_opt = 2πc/wl` the
optical angular frequency, `wl` the wavelength); recombined on a detector they interfere as
`I = I₀(1 + cos Δφ)`, and the rotation is read from the fringe.  A ring-*laser* gyro instead reads the
**beat frequency** `Δf = 4Aω/(wlP)` between the two cavity modes.  Everything scales with the optical
wavelength — the physics the time-delay abstraction (§5) left implicit. -/

/-- **[the optical Sagnac phase]** — `Δφ = 8πAω/(wlc)` for a loop of area `A` at rotation rate `ω`,
wavelength `wl` (Fibre-optic gyroscope: `A = N·πD²/4` turns, so `Δφ = 2πLDω/(wlc)`). -/
def sagnacPhase (A ω wl c : ℝ) : ℝ := 8 * Real.pi * A * ω / (wl * c)

/-- **[phase = optical frequency × delay]** — the Sagnac phase is the time delay `ΔT = 4Aω/c²` carried at
the optical angular frequency `ω_opt = 2πc/wl`: `Δφ = (2πc/wl)·ΔT`.  This is the bridge from the timed delay
(§5) to what the interferometer actually measures. -/
theorem sagnac_phase_from_delay {wl c : ℝ} (hwl : wl ≠ 0) (hc : c ≠ 0) (A ω : ℝ) :
    (2 * Real.pi * c / wl) * (4 * A * ω / c ^ 2) = sagnacPhase A ω wl c := by
  unfold sagnacPhase
  field_simp
  ring

/-- **[the fibre-gyro scale factor]** — for `N` turns of diameter `D` (area `NπD²/4`, fibre length
`L = NπD`), the phase is `Δφ = 2π·L·D·ω/(wlc)`: the sensitivity grows with the fibre length times the coil
diameter, the design lever of a fibre-optic gyroscope. -/
theorem sagnac_phase_fibre_form (N D ω wl c : ℝ) :
    sagnacPhase (N * Real.pi * D ^ 2 / 4) ω wl c = 2 * Real.pi * (N * Real.pi * D) * D * ω / (wl * c) := by
  unfold sagnacPhase
  ring

/-- **[the phase reads the rotation]** — inverting: `ω = wlc·Δφ/(8πA)`, the fibre-gyro readout. -/
theorem sagnac_phase_reads_rotation {A wl c Δφ ω : ℝ} (hA : A ≠ 0) (hwl : wl ≠ 0) (hc : c ≠ 0)
    (h : Δφ = sagnacPhase A ω wl c) : ω = wl * c * Δφ / (8 * Real.pi * A) := by
  rw [h]
  unfold sagnacPhase
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **[the interference intensity]** — the recombined beams give `I = I₀(1 + cos(Δφ + φ_b))` with an
optional non-reciprocal bias `φ_b`. -/
def interferenceIntensity (I₀ φb Δφ : ℝ) : ℝ := I₀ * (1 + Real.cos (Δφ + φb))

/-- **[the readout sensitivity]** — `dI/dΔφ = −I₀·sin(Δφ + φ_b)`: the interferometer's response to a small
rotation.  It vanishes at `φ_b = 0, Δφ = 0` (a fringe peak — first-order blind, why a raw interferometer
cannot read small rotations) and is maximal at the `π/2` quadrature bias. -/
theorem interference_sensitivity (I₀ φb Δφ : ℝ) :
    HasDerivAt (interferenceIntensity I₀ φb) (-(I₀ * Real.sin (Δφ + φb))) Δφ := by
  unfold interferenceIntensity
  have hc : HasDerivAt (fun x : ℝ => Real.cos (x + φb)) (-Real.sin (Δφ + φb)) Δφ := by
    simpa using ((hasDerivAt_id Δφ).add_const φb).cos
  have hf := (hc.const_add 1).const_mul I₀
  have heq : I₀ * -Real.sin (Δφ + φb) = -(I₀ * Real.sin (Δφ + φb)) := by ring
  rw [heq] at hf
  exact hf

/-- **[the quadrature bias linearizes the readout]** — at `φ_b = π/2` the intensity becomes
`I = I₀(1 − sin Δφ)`, whose sensitivity `−I₀ cos Δφ` is maximal (`−I₀`) at `Δφ = 0`: the operating point
of a biased fibre-optic gyroscope, linear and maximally sensitive in the rotation. -/
theorem interference_quadrature_bias (I₀ Δφ : ℝ) :
    interferenceIntensity I₀ (Real.pi / 2) Δφ = I₀ * (1 - Real.sin Δφ) := by
  unfold interferenceIntensity
  rw [Real.cos_add_pi_div_two]
  ring

/-- **[the ring-laser beat frequency]** — a Sagnac ring *laser* reads the beat `Δf = 4Aω/(wlP)` between the
counter-propagating cavity modes (`P` the perimeter); the rotation is `ω = wlP·Δf/(4A)`. -/
def sagnacBeatFrequency (A ω wl P : ℝ) : ℝ := 4 * A * ω / (wl * P)

/-- **[the beat reads the rotation]** — `ω = wlP·Δf/(4A)`, the ring-laser-gyro readout (a frequency counted
digitally, no interferometric bias needed). -/
theorem beat_reads_rotation {A wl P Δf ω : ℝ} (hA : A ≠ 0) (hwl : wl ≠ 0) (hP : P ≠ 0)
    (h : Δf = sagnacBeatFrequency A ω wl P) : ω = wl * P * Δf / (4 * A) := by
  rw [h]
  unfold sagnacBeatFrequency
  field_simp

/-! ## §9. Quantum-optical limits of the Sagnac phase (Fock space)

The interferometric phase (§8) is estimated from a photon count, so its resolution is set by the *photon
statistics* of the Fock state feeding the interferometer.  Coherent (laser) light is Poissonian —
`Var N = ⟨N⟩ = N̄` — giving the **standard quantum limit** `δφ = 1/√N̄`, exactly the classical shot-noise
floor of the sim, now derived from the Fock-space variance.  Thermal light is super-Poissonian (noisier);
**squeezed** light beats the shot-noise limit by `e^{−r}` (the same `e^{−2r}` variance reduction the repo's
two-mode-squeezed states carry), reaching the **Heisenberg limit** `δφ = 1/N̄` at `r = ½ log N̄`.  The
gyroscope's angular-rate floor inherits all of this through the scale factor. -/

/-- **[coherent-state phase variance — the standard quantum limit]** — `δφ² = 1/N̄` from Poissonian
statistics (`Var N = N̄`, response `∂⟨N⟩/∂φ ~ N̄`, so `δφ² = Var N/(∂N/∂φ)² = 1/N̄`). -/
def shotNoisePhaseVariance (Nbar : ℝ) : ℝ := 1 / Nbar

/-- **[thermal-state phase variance]** — thermal (chaotic) light is super-Poissonian, `Var N = N̄ + N̄²`,
so `δφ² = (1 + N̄)/N̄` — strictly above the shot-noise limit. -/
def thermalPhaseVariance (Nbar : ℝ) : ℝ := (1 + Nbar) / Nbar

/-- **[squeezed-state phase variance]** — phase squeezing by `r` scales the variance by `e^{−2r}`:
`δφ² = e^{−2r}/N̄` (the `e^{−2r}` reduction of `SqueezedThermal.nu_minus`). -/
def squeezedPhaseVariance (r Nbar : ℝ) : ℝ := Real.exp (-(2 * r)) / Nbar

/-- **[the Heisenberg-limited phase variance]** — the ultimate `δφ² = 1/N̄²` (N00N states). -/
def heisenbergPhaseVariance (Nbar : ℝ) : ℝ := 1 / Nbar ^ 2

/-- **[thermal light is noisier than shot noise]** — `1/N̄ < (1 + N̄)/N̄`: a chaotic source cannot even
reach the standard quantum limit; the gyro needs coherent (laser) light. -/
theorem thermal_above_shot_noise {Nbar : ℝ} (h : 0 < Nbar) :
    shotNoisePhaseVariance Nbar < thermalPhaseVariance Nbar := by
  unfold shotNoisePhaseVariance thermalPhaseVariance
  rw [add_div, div_self h.ne']
  linarith [div_pos one_pos h]

/-- **[squeezing beats the shot-noise limit]** — for `r > 0`, `e^{−2r}/N̄ < 1/N̄`: squeezed light resolves
the Sagnac phase below the standard quantum limit (the principle of squeezed-light interferometry, as in
gravitational-wave detectors). -/
theorem squeezed_below_shot_noise {r Nbar : ℝ} (hr : 0 < r) (h : 0 < Nbar) :
    squeezedPhaseVariance r Nbar < shotNoisePhaseVariance Nbar := by
  unfold squeezedPhaseVariance shotNoisePhaseVariance
  have h1 : Real.exp (-(2 * r)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h2 : Real.exp (-(2 * r)) / Nbar = Real.exp (-(2 * r)) * (1 / Nbar) := by ring
  rw [h2]
  calc Real.exp (-(2 * r)) * (1 / Nbar) < 1 * (1 / Nbar) :=
        mul_lt_mul_of_pos_right h1 (div_pos one_pos h)
    _ = 1 / Nbar := one_mul _

/-- **[squeezing of `½ log N̄` reaches the Heisenberg limit]** — `e^{−2·(½ log N̄)}/N̄ = 1/N̄²`: the exact
squeezing at which the squeezed variance equals the Heisenberg-limited variance. -/
theorem squeezing_reaches_heisenberg {Nbar : ℝ} (h : 0 < Nbar) :
    squeezedPhaseVariance (Real.log Nbar / 2) Nbar = heisenbergPhaseVariance Nbar := by
  unfold squeezedPhaseVariance heisenbergPhaseVariance
  have harg : -(2 * (Real.log Nbar / 2)) = -Real.log Nbar := by ring
  rw [harg, Real.exp_neg, Real.exp_log h]
  field_simp

/-- **[the Heisenberg limit is below the shot-noise limit]** — for `N̄ > 1`, `1/N̄² < 1/N̄`: the ultimate
quantum advantage grows with photon number. -/
theorem heisenberg_below_shot_noise {Nbar : ℝ} (h : 1 < Nbar) :
    heisenbergPhaseVariance Nbar < shotNoisePhaseVariance Nbar := by
  unfold heisenbergPhaseVariance shotNoisePhaseVariance
  have hpos : (0 : ℝ) < Nbar := by linarith
  have hlt : 1 / Nbar < 1 := by rw [div_lt_one hpos]; exact h
  have heq : 1 / Nbar ^ 2 = (1 / Nbar) * (1 / Nbar) := by ring
  rw [heq]
  calc (1 / Nbar) * (1 / Nbar) < (1 / Nbar) * 1 :=
        mul_lt_mul_of_pos_left hlt (div_pos one_pos hpos)
    _ = 1 / Nbar := mul_one _

/-- **[the shot-noise-limited rotation resolution]** — routing the coherent-state phase resolution
`δφ = 1/√N̄` through the fibre-gyro readout (`sagnac_phase_reads_rotation`) gives the minimum resolvable
rotation `δω = λc/(8πA·√N̄)`: the gyroscope's fundamental sensitivity is set by the photon number.
Squeezing multiplies this by `e^{−r}`; the Heisenberg limit replaces `√N̄` by `N̄`. -/
theorem sagnac_shot_noise_limited_rate (A wl c Nbar : ℝ) :
    wl * c * (1 / Real.sqrt Nbar) / (8 * Real.pi * A)
      = wl * c / (8 * Real.pi * A * Real.sqrt Nbar) := by
  ring

/-! ## §10. Quantizing entropic time: the Matsubara ladder

Entropic time is imaginary modular time — the Euclidean/contraction direction (§4).  The KMS condition
makes that direction **compact**: the imaginary-time correlator is periodic with circumference
`ℏβ = ℏ/(k_BT) = 1/ω_E` (the Connes–Rovelli thermal time, one entropic tick).  A compact time coordinate
quantizes like an angle — its conjugate spectrum is *discrete*.  The conjugate "entropic frequencies" are
the **Matsubara ladder** `ω_n = 2πn·ω_E`, integer multiples of the entropic clock rate: entropic time is
quantized in units of `ω_E`.  This uses the repo's `MatsubaraThermalOscillator` (`matsubaraFreqBoson β n =
2πn/β`); the Pauli obstruction is evaded because time is *compact* (discrete conjugate), not conjugate to a
bounded-below Hamiltonian.  The continuous-operator dual is the MPC age operator on the *real-line*
Liouvillian (`RelationalTime.LiouvillianAgeOperator`, `i[L,T]=I`): compact↔discrete and real-line↔
continuous are Pontryagin duals of the same entropic time. -/

/-- **[the entropic-time period]** — the circumference of the imaginary-time (KMS) circle in genuine time
units, `ℏ/(k_BT) = 1/ω_E`: one entropic tick, the Connes–Rovelli thermal time. -/
def entropicTimePeriod (kB T ℏ : ℝ) : ℝ := ℏ / (kB * T)

/-- **[the period is the inverse entropic rate]** — `ℏ/(k_BT) = 1/ω_E`. -/
theorem entropic_time_period_is_inverse_rate {kB T ℏ : ℝ} (hkB : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0) :
    entropicTimePeriod kB T ℏ = 1 / thermalEntropicRate kB T ℏ := by
  unfold entropicTimePeriod thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
  field_simp

/-- **[the entropic Matsubara ladder — the quantization]** — the discrete Fourier modes conjugate to the
compact entropic-time circle are `ω_n = 2πn·ω_E`: entropic time is quantized in integer multiples of the
entropic clock rate.  The keystone linking the repo's `matsubaraFreqBoson` to the entropic clock. -/
theorem entropic_matsubara_ladder {kB T ℏ : ℝ} (hkB : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0) (n : ℤ) :
    matsubaraFreqBoson (entropicTimePeriod kB T ℏ) n
      = 2 * Real.pi * (n : ℝ) * thermalEntropicRate kB T ℏ := by
  unfold matsubaraFreqBoson entropicTimePeriod thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
  field_simp

/-- **[the entropic-time level spacing]** — consecutive Matsubara modes are spaced by exactly `2π·ω_E`:
the fundamental quantum of the entropic-frequency spectrum. -/
theorem entropic_level_spacing {kB T ℏ : ℝ} (hkB : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0) (n : ℤ) :
    matsubaraFreqBoson (entropicTimePeriod kB T ℏ) (n + 1)
        - matsubaraFreqBoson (entropicTimePeriod kB T ℏ) n
      = 2 * Real.pi * thermalEntropicRate kB T ℏ := by
  rw [entropic_matsubara_ladder hkB hT hℏ, entropic_matsubara_ladder hkB hT hℏ]
  push_cast
  ring

/-- **[the zero (static) entropic mode]** — `ω_0 = 0`: the DC mode of the entropic-time circle carries no
imaginary action. -/
theorem entropic_zero_mode (kB T ℏ : ℝ) :
    matsubaraFreqBoson (entropicTimePeriod kB T ℏ) 0 = 0 :=
  matsubaraFreqBoson_zero _

/-- **[the spectrum is a faithful copy of ℤ — discreteness]** — distinct integers give distinct entropic
frequencies: the quantization is exact, the spectrum a rigid ladder indexed by `ℤ` (no accidental
degeneracy).  This is what makes entropic time *quantized*. -/
theorem entropic_spectrum_faithful {kB T ℏ : ℝ} (hkB : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0)
    (hπ : Real.pi ≠ 0) {n m : ℤ}
    (h : matsubaraFreqBoson (entropicTimePeriod kB T ℏ) n
        = matsubaraFreqBoson (entropicTimePeriod kB T ℏ) m) : n = m := by
  rw [entropic_matsubara_ladder hkB hT hℏ, entropic_matsubara_ladder hkB hT hℏ] at h
  have hrate : thermalEntropicRate kB T ℏ ≠ 0 := by
    unfold thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
    exact div_ne_zero (mul_ne_zero hkB hT) hℏ
  have hc : (2 * Real.pi * thermalEntropicRate kB T ℏ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hπ) hrate
  have hnK : (n : ℝ) * (2 * Real.pi * thermalEntropicRate kB T ℏ)
      = (m : ℝ) * (2 * Real.pi * thermalEntropicRate kB T ℏ) := by linear_combination h
  exact_mod_cast mul_right_cancel₀ hc hnK

/-- **[entropic time is quantized in units of ω_E]** — the synthesis: the entropic-time period is
`1/ω_E`; its conjugate spectrum is the Matsubara ladder `ω_n = 2πn·ω_E`, uniformly spaced by `2π·ω_E` and
faithfully indexed by `ℤ`.  Temperature sets the quantum: hotter ⇒ larger `ω_E` ⇒ coarser ladder.  The
Pauli obstruction is evaded by compactness (the MPC age operator, `i[L,T]=I`, is the continuous real-line
dual). -/
theorem entropic_time_quantization_synthesis {kB T ℏ : ℝ} (hkB : kB ≠ 0) (hT : T ≠ 0) (hℏ : ℏ ≠ 0)
    (hπ : Real.pi ≠ 0) (n : ℤ) :
    (entropicTimePeriod kB T ℏ = 1 / thermalEntropicRate kB T ℏ)
      ∧ (matsubaraFreqBoson (entropicTimePeriod kB T ℏ) n
          = 2 * Real.pi * (n : ℝ) * thermalEntropicRate kB T ℏ)
      ∧ (matsubaraFreqBoson (entropicTimePeriod kB T ℏ) (n + 1)
            - matsubaraFreqBoson (entropicTimePeriod kB T ℏ) n
          = 2 * Real.pi * thermalEntropicRate kB T ℏ) :=
  ⟨entropic_time_period_is_inverse_rate hkB hT hℏ, entropic_matsubara_ladder hkB hT hℏ n,
    entropic_level_spacing hkB hT hℏ n⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.decoherence_rate_entropic_clock_window where
  formalizes @ "claim:the-bath-decoherence-rate-is-entropic-clock-linear-with-a-temperature-independent-bounded-offset",
  requires @ "claim:the-trapped-ion-mpemba-effect-exists-iff-the-bloch-sector-spectral-discriminant-is-positive",
  supported_by @ "paper:shapira-teza-raz-ozeri-2401.05830-inverse-mpemba-trapped-ion-qubit",
  supported_by @ "lean:Physlib.Optics.TemporalDoubleSlit.thermalEntropicRate",
  caveat @ "epistemic:gamma-equals-coupling-times-occupation-is-the-standard-weak-coupling-bath-rate-cited"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.detailed_balance_entropic_arrow where
  formalizes @ "claim:first-order-detailed-balance-brackets-the-exact-boltzmann-arrow-between-one-minus-two-epsilon-and-one-minus-epsilon",
  supported_by @ "paper:chatterjee-khan-jain-mahesh-2509.13451-quantum-mpemba-without-bath-engineering",
  caveat @ "epistemic:brackets-are-exact-for-epsilon-below-one-half-the-nmr-value-is-4e-5"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.mpemba_entropic_clock_synthesis where
  formalizes @ "claim:temperature-enters-the-mpemba-chain-only-as-the-tick-rate-of-entropic-time",
  requires @ "claim:the-bath-decoherence-rate-is-entropic-clock-linear-with-a-temperature-independent-bounded-offset",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.entropic_generator_flow_contracts",
  caveat @ "epistemic:high-temperature-window-not-the-full-planck-curve-and-coupling-a-identified-by-the-ab-initio-scripts"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.absolute_anchor_cancels_in_translation where
  formalizes @ "claim:the-bath-removed-absolute-unit-cancels-from-every-translation-between-realized-clocks-only-relative-shifts-survive",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.tick_count_is_rate_ratio",
  caveat @ "epistemic:the-absolute-anchor-is-a-gauge-choice-the-computed-shifts-are-the-physical-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.rapidity_realization_shift where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-special-relativistic-correction-enters-the-clock-realization-dictionary-as-the-computed-shift-inverse-cosh-eta-minus-one",
  requires @ "claim:the-bath-removed-absolute-unit-cancels-from-every-translation-between-realized-clocks-only-relative-shifts-survive",
  caveat @ "epistemic:bath-blackbody-and-potential-shifts-carry-conventional-coefficients-and-are-cited-not-derived"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.thermal_rapidity_occupation where
  formalizes @ "claim:heating-acts-on-the-second-quantized-vacuum-as-a-hyperbolic-rotation-with-cosh-two-theta-equals-one-plus-twice-the-occupation",
  requires @ "claim:the-bath-decoherence-rate-is-entropic-clock-linear-with-a-temperature-independent-bounded-offset",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition.complexBoost_group",
  caveat @ "epistemic:acceleration-rapidity-and-thermal-rapidity-share-one-so-1-1-group-the-unruh-connection-at-group-level"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.dilation_gravimeter_recovery where
  formalizes @ "claim:time-dilation-decoherence-rate-is-linear-in-gravity-and-inverts-exactly-to-a-percent-level-entropic-gravimeter",
  requires @ "claim:the-bath-decoherence-rate-is-entropic-clock-linear-with-a-temperature-independent-bounded-offset",
  supported_by @ "paper:pikovski-zych-costa-brukner-2015-universal-decoherence-due-to-gravitational-time-dilation",
  caveat @ "epistemic:the-sqrt-n-over-2-thermal-mode-form-is-the-cited-pikovski-result-the-inversion-and-scaling-laws-are-the-exact-content-here"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.planet_ratio_gravimeter where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.heating_scales_entropic_clock",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:transporting-one-apparatus-between-planets-measures-the-gravity-ratio-with-no-calibration-unit-or-clock",
  requires @ "claim:time-dilation-decoherence-rate-is-linear-in-gravity-and-inverts-exactly-to-a-percent-level-entropic-gravimeter",
  caveat @ "epistemic:same-apparatus-hypothesis-x-n-t-fixed-between-stations"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.tolman_entropic_clock where
  formalizes @ "claim:tolman-ehrenfest-equilibrium-temperature-gradient-is-the-heating-scaling-law-at-the-redshift-factor",
  requires @ "claim:the-bath-removed-absolute-unit-cancels-from-every-translation-between-realized-clocks-only-relative-shifts-survive",
  supported_by @ "paper:tolman-ehrenfest-1930-temperature-equilibrium-in-a-static-gravitational-field",
  caveat @ "epistemic:weak-field-first-order-form-of-t-sqrt-g00-constant"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.roughness_reads_entropic_clock where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:optically-scattered-thermal-surface-roughness-is-the-entropic-clocks-equipartition-output-with-gravity-as-infrared-cutoff",
  requires @ "claim:the-bath-decoherence-rate-is-entropic-clock-linear-with-a-temperature-independent-bounded-offset",
  caveat @ "epistemic:classical-equipartition-of-linear-capillary-gravity-modes-surface-light-scattering-is-the-cited-technique"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.simultaneity_dichotomy where
  formalizes @ "claim:absolute-simultaneity-is-position-independent-while-the-lorentz-transform-gaps-equal-time-events-relative-simultaneity",
  requires @ "claim:a-clock-moving-at-rapidity-eta-realizes-the-anchor-at-nu0-over-cosh-eta-the-relativistic-computed-shift",
  supported_by @ "cite:spavieri-gillies-haug-2021-sagnac-simultaneity-jmo-68-202"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_delay_area_omega where
  formalizes @ "claim:the-sagnac-time-delay-is-four-area-omega-over-c-squared-minus-v-squared-reading-the-angular-velocity",
  supported_by @ "cite:spavieri-gillies-haug-2021-sagnac-simultaneity-jmo-68-202"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_first_order_reads_rotation where
  formalizes @ "claim:the-sagnac-delay-inverts-to-omega-equals-c-squared-delta-t-over-four-pi-r-squared-a-rotation-readout",
  requires @ "claim:the-sagnac-time-delay-is-four-area-omega-over-c-squared-minus-v-squared-reading-the-angular-velocity"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.langevin_null_factorization where
  formalizes @ "claim:the-langevin-rotating-frame-null-condition-factors-into-the-two-local-light-speeds-c-minus-omega-r-and-c-plus-omega-r",
  supported_by @ "cite:spavieri-gillies-haug-2021-sagnac-simultaneity-jmo-68-202"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_simultaneity_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.simultaneity_dichotomy",
  formalizes @ "claim:the-rotating-platform-is-a-clock-synchronization-laboratory-that-reads-rotation-through-the-simultaneity-it-forces",
  requires @ "claim:absolute-simultaneity-is-position-independent-while-the-lorentz-transform-gaps-equal-time-events-relative-simultaneity",
  requires @ "claim:the-sagnac-time-delay-is-four-area-omega-over-c-squared-minus-v-squared-reading-the-angular-velocity"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.lta_time_is_minkowski_proper_time where
  formalizes @ "claim:the-absolute-simultaneity-time-t-over-gamma-is-the-minkowski-proper-time-of-the-co-moving-clock",
  requires @ "claim:absolute-simultaneity-is-position-independent-while-the-lorentz-transform-gaps-equal-time-events-relative-simultaneity",
  supported_by @ "cite:spavieri-gillies-haug-2021-sagnac-simultaneity-jmo-68-202"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.minkowski_interval_lorentz_invariant where
  formalizes @ "claim:the-minkowski-interval-is-lorentz-invariant-and-is-the-synchronization-independent-content-of-the-simultaneity-dichotomy",
  requires @ "claim:the-absolute-simultaneity-time-t-over-gamma-is-the-minkowski-proper-time-of-the-co-moving-clock"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_delay_first_order_twice_holonomy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.ring_sync_holonomy_area",
  formalizes @ "claim:the-sagnac-delay-is-twice-the-synchronization-holonomy-the-closed-loop-integral-of-the-locally-removable-offset",
  requires @ "claim:the-sagnac-time-delay-is-four-area-omega-over-c-squared-minus-v-squared-reading-the-angular-velocity"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.holonomy_reads_rotation where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert.interference",
  formalizes @ "claim:the-synchronization-holonomy-inverts-to-the-angular-velocity-omega-equals-c-squared-h-over-two-pi-r-squared-the-quantification-method",
  requires @ "claim:the-sagnac-delay-is-twice-the-synchronization-holonomy-the-closed-loop-integral-of-the-locally-removable-offset"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_triad_reconstructs_magnitude where
  supported_by @ "lean:HermitianMat.sqrt_sq",
  formalizes @ "claim:a-triad-of-orthogonal-sagnac-rings-reconstructs-the-full-angular-velocity-magnitude-from-the-loop-holonomies-a-strapdown-optical-gyroscope",
  requires @ "claim:the-synchronization-holonomy-inverts-to-the-angular-velocity-omega-equals-c-squared-h-over-two-pi-r-squared-the-quantification-method"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_phase_from_delay where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-optical-sagnac-phase-is-the-time-delay-carried-at-the-optical-frequency-delta-phi-equals-eight-pi-a-omega-over-lambda-c",
  requires @ "claim:the-sagnac-time-delay-is-four-area-omega-over-c-squared-minus-v-squared-reading-the-angular-velocity"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.interference_quadrature_bias where
  formalizes @ "claim:a-quadrature-pi-over-two-non-reciprocal-bias-linearizes-the-fibre-gyro-interference-readout-to-maximal-sensitivity-at-zero-rotation",
  requires @ "claim:the-optical-sagnac-phase-is-the-time-delay-carried-at-the-optical-frequency-delta-phi-equals-eight-pi-a-omega-over-lambda-c"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_phase_reads_rotation where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert.interference",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-fibre-optic-gyro-recovers-rotation-from-the-sagnac-phase-omega-equals-lambda-c-delta-phi-over-eight-pi-a"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.beat_reads_rotation where
  formalizes @ "claim:the-ring-laser-gyro-recovers-rotation-from-the-counter-propagating-beat-frequency-omega-equals-lambda-p-delta-f-over-four-a"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.thermal_above_shot_noise where
  formalizes @ "claim:coherent-laser-light-hits-the-standard-quantum-limit-while-thermal-light-is-super-poissonian-and-noisier-so-the-gyro-needs-coherent-light",
  supported_by @ "lean:Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal.boseEinstein"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.squeezed_below_shot_noise where
  formalizes @ "claim:phase-squeezed-light-resolves-the-sagnac-phase-below-the-standard-quantum-limit-by-e-to-the-minus-r-the-principle-of-squeezed-light-interferometry",
  supported_by @ "lean:Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal.nu_minus"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.squeezing_reaches_heisenberg where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:squeezing-of-one-half-log-n-bar-brings-the-squeezed-phase-variance-to-the-heisenberg-limit-one-over-n-bar-squared",
  requires @ "claim:phase-squeezed-light-resolves-the-sagnac-phase-below-the-standard-quantum-limit-by-e-to-the-minus-r-the-principle-of-squeezed-light-interferometry"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_shot_noise_limited_rate where
  formalizes @ "claim:the-fibre-gyro-fundamental-rotation-resolution-is-lambda-c-over-eight-pi-a-root-n-bar-set-by-the-photon-number-improved-by-squeezing",
  requires @ "claim:the-fibre-optic-gyro-recovers-rotation-from-the-sagnac-phase-omega-equals-lambda-c-delta-phi-over-eight-pi-a"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.entropic_matsubara_ladder where
  formalizes @ "claim:entropic-time-is-quantized-its-conjugate-spectrum-is-the-matsubara-ladder-omega-n-equals-2-pi-n-times-the-entropic-clock-rate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraFreqBoson",
  caveat @ "epistemic:the-pauli-obstruction-is-evaded-because-imaginary-modular-time-is-compact-kms-periodic-so-its-conjugate-is-discrete-not-because-time-is-an-operator-conjugate-to-a-bounded-below-hamiltonian"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.entropic_spectrum_faithful where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.entropic_matsubara_ladder",
  formalizes @ "claim:the-entropic-time-matsubara-spectrum-is-a-faithful-copy-of-the-integers-a-rigid-discrete-ladder-which-is-what-makes-entropic-time-quantized",
  requires @ "claim:entropic-time-is-quantized-its-conjugate-spectrum-is-the-matsubara-ladder-omega-n-equals-2-pi-n-times-the-entropic-clock-rate"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.entropic_time_quantization_synthesis where
  formalizes @ "claim:entropic-time-is-quantized-in-units-of-the-entropic-clock-rate-with-the-mpc-age-operator-on-the-real-line-liouvillian-as-the-continuous-pontryagin-dual",
  requires @ "claim:the-entropic-time-matsubara-spectrum-is-a-faithful-copy-of-the-integers-a-rigid-discrete-ladder-which-is-what-makes-entropic-time-quantized",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.ageOperator"

/- ZIL-END -/
