/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

meta import Zil

/-!
# The directly observed Zitterbewegung: a Bose–Einstein condensate as a Dirac particle

LeBlanc, Beeler, Jiménez-García, Perry, Sugawa, Williams and Spielman, *Direct observation of
zitterbewegung in a Bose–Einstein condensate*, New J. Phys. **15** (2013) 073011.

Two counter-propagating Raman lasers couple two Zeeman states of a `⁸⁷Rb` condensate that
differ in velocity, so each atom obeys the one-dimensional Dirac equation with an *engineered*
light speed and rest energy.  The trembling is then micrometre-scale and kilohertz-slow instead
of `10⁻¹³ m` and `10²¹ Hz`, and the cloud's position can simply be imaged.  The paper reports
the first direct measurement of Zitterbewegung in both position and velocity.

Why this matters to the repository: the entropic clock is *anchored* at the Compton/Zitterbewegung
frequency (`EntropicClockComptonAnchor`), and `FrequencyTrinity.zitterbewegung_rest_eq_two_compton`
already states `ω_Z = 2ω_C` at rest.  Here that relation is not inferred — it is the analogue's
defining calibration `m*c*² = ℏΩ/2` (Eq. (5)), measured across a range of coupling strengths
(`Ω/2π` from 2.4 to 4.3 kHz).  The anchor gains an experiment in which the rest energy is a
tunable knob rather than a fixed property of the electron.

* **§A — the analogue calibration** (Eq. (5)): `analogueLightSpeed = 2ℏk_R/m` (twice the recoil
  velocity) and `analogueRestEnergy = ℏΩ/2`.  `analogue_zitterbewegungFrequency_eq_coupling`
  identifies the Raman coupling `Ω` as the analogue's Zitterbewegung frequency, through the
  repository's own `zitterbewegungFrequency` at zero momentum.
* **§B — the trembling** (Eq. (3)): `⟨x(t)⟩ = x₀ + (λ*_C/4π)·sin Ωt` and `⟨v(t)⟩ = c*·cos Ωt`.
  `zbwAmplitude_eq_half_comptonWavelength` — the amplitude is **half the reduced Compton
  wavelength**; `zbwAmplitude_mul_frequency` — amplitude times frequency is exactly `c*`, so the
  trembling traverses its own amplitude at the analogue light speed;
  `zbwPosition_hasDerivAt_velocity` — position and velocity are the two quadratures of one
  oscillation, `π/2` out of phase, the paper's "out-of-phase oscillation of conjugate
  quantities".
* **§B′ — Eq. (3) derived from Eq. (2)**: `heisenberg_velocity_solution` and
  `heisenberg_position_solution`.  At `pₓ = 0` the Heisenberg source term vanishes and the
  velocity obeys the bare harmonic equation; the deviation from `c*·cos Ωt` carries a conserved
  `Ω²w² + (w′)²` that starts at zero, so the solution is unique.
* **§C — the time-of-flight quadrature rotation** (Eq. (6)): imaging after a flight time `t_TOF`
  reads the combination `sin(Ωt)/Ω + t_TOF·cos(Ωt)`.  `tofSignal_quadrature_norm` shows the two
  quadratures have squared lengths summing to `1 + (t_TOF Ω)²`, so time of flight *rotates* the readout
  continuously from position (`t_TOF = 0`) toward velocity — one oscillation seen in two
  quadratures, which is exactly how the paper measures both.
* **§D — attenuation** (§3.1): atoms that do not participate — a fraction `f₀` left at rest by
  imperfect preparation, and a thermal fraction `f_k` that drifts — scale the observed amplitude
  by `(1−f₀)(1−f_k)`.  `observedAmplitude_le_ideal` bounds the observed amplitude by the ideal
  one, and `observedAmplitude_eq_ideal_iff` says the trembling is seen at full amplitude exactly
  when every atom participates.

**Honest layering.**  Equation (3) is **derived**, not assumed: §B′ takes Eq. (2) — the
Heisenberg equation for the velocity operator — with the prepared state's `pₓ = 0` (which
switches off its source term) and the paper's initial data, and forces `⟨v̂⟩ = c*·cos Ωt` by an
energy-conservation uniqueness argument, then integrates once for the position.  What remains
taken from the paper: the Heisenberg equation itself is the hypothesis (no Raman level
structure or spin-operator algebra is constructed, so `σ̌ₓ` enters only as the scalar
coefficient that the `pₓ = 0` state annihilates), and the attenuation model is Eq. (6)'s
algebra rather than a finite-temperature derivation of the two fractions.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — the analogue calibration (Eq. (5)) -/

/-- **The analogue light speed** `c* = 2ℏk_R/m` — twice the atomic recoil velocity, `11.6 mm s⁻¹`
in the experiment, a factor `≈10¹⁰` below the true speed of light. -/
noncomputable def analogueLightSpeed (ħ kR m : ℝ) : ℝ := 2 * ħ * kR / m

/-- **The analogue rest energy** `m*c*² = ℏΩ/2` — *half* the four-photon Raman coupling strength.
The laser field plays the role of the mass term: switching the coupling on gives the atoms a
rest energy. -/
noncomputable def analogueRestEnergy (ħ Ω : ℝ) : ℝ := ħ * Ω / 2

/-- **The Raman coupling is the analogue's Zitterbewegung frequency.**  With the rest energy
calibrated to `ℏΩ/2`, the repository's `zitterbewegungFrequency` at zero momentum — the
`E₊ − E₋` Dirac splitting over `ℏ` — returns exactly `Ω`.  This is
`zitterbewegung_rest_eq_two_compton` read in the analogue's units: the trembling frequency is
twice the rest energy over `ℏ`, and the experiment sets that rest energy with a laser. -/
theorem analogue_zitterbewegungFrequency_eq_coupling (mStar cStar ħ Ω : ℝ)
    (hm : 0 ≤ mStar) (hħ : ħ ≠ 0) (hrest : mStar * cStar ^ 2 = analogueRestEnergy ħ Ω) :
    zitterbewegungFrequency 0 mStar cStar ħ = Ω := by
  rw [zitterbewegung_rest_eq_two_compton mStar cStar ħ hm]
  unfold comptonFrequency
  rw [hrest]
  unfold analogueRestEnergy
  field_simp

/-! ### §B — the trembling motion (Eq. (3)) -/

/-- **The Zitterbewegung amplitude** `λ*_C/4π = ℏ/(2m*c*)`, the paper's fitted amplitude. -/
noncomputable def zbwAmplitude (mStar cStar ħ : ℝ) : ℝ := ħ / (2 * (mStar * cStar))

/-- **The amplitude is half the reduced Compton wavelength.**  The paper writes the amplitude as
`λ*_C/4π` with `λ*_C = h/(m*c*)` the *unreduced* wavelength; dividing by `4π` halves the reduced
one.  In the experiment `λ*_C ≈ 1 μm`, larger than an electron's by `≈10⁶`, which is what made
the motion directly imageable. -/
theorem zbwAmplitude_eq_half_comptonWavelength (mStar cStar ħ : ℝ) :
    zbwAmplitude mStar cStar ħ = comptonWavelength mStar cStar ħ / 2 := by
  unfold zbwAmplitude comptonWavelength
  ring

/-- **Amplitude times frequency is the analogue light speed**: `(λ*_C/4π)·Ω = c*`.  The trembling
crosses its own amplitude at exactly the speed the massless branches travel — the velocity
oscillation of Eq. (3) has amplitude `c*` precisely because the position oscillation has
amplitude `ℏ/(2m*c*)`.  This is the `λ_C ω_C = c` identity of `FrequencyTrinity` carried through
the factor of two that separates Compton from Zitterbewegung. -/
theorem zbwAmplitude_mul_frequency (mStar cStar ħ Ω : ℝ)
    (hm : mStar ≠ 0) (hc : cStar ≠ 0) (hħ : ħ ≠ 0)
    (hrest : mStar * cStar ^ 2 = analogueRestEnergy ħ Ω) :
    zbwAmplitude mStar cStar ħ * Ω = cStar := by
  have hΩ : Ω = 2 * (mStar * cStar ^ 2) / ħ := by
    rw [hrest]; unfold analogueRestEnergy; field_simp
  unfold zbwAmplitude
  rw [hΩ]
  field_simp

/-- **The trembling position** `⟨x(t)⟩ = x₀ + A·sin(Ωt)` (Eq. (3)). -/
noncomputable def zbwPosition (x₀ A Ω t : ℝ) : ℝ := x₀ + A * Real.sin (Ω * t)

/-- **The trembling velocity** `⟨v(t)⟩ = c*·cos(Ωt)` (Eq. (3)). -/
noncomputable def zbwVelocity (cStar Ω t : ℝ) : ℝ := cStar * Real.cos (Ω * t)

/-- **Position and velocity are the two quadratures of one oscillation.**  Differentiating the
position of Eq. (3) returns its velocity exactly, provided the amplitude and frequency satisfy
`A·Ω = c*` — which `zbwAmplitude_mul_frequency` supplies.  The `sin`/`cos` pair is the paper's
"out-of-phase oscillation of these conjugate quantities": the cloud is furthest from centre
exactly when it is momentarily at rest. -/
theorem zbwPosition_hasDerivAt_velocity (x₀ A Ω cStar t : ℝ) (hAΩ : A * Ω = cStar) :
    HasDerivAt (fun u => zbwPosition x₀ A Ω u) (zbwVelocity cStar Ω t) t := by
  have hlin : HasDerivAt (fun u : ℝ => Ω * u) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (Ω * u)) (Real.cos (Ω * t) * Ω) t :=
    (Real.hasDerivAt_sin (Ω * t)).comp t hlin
  have h : HasDerivAt (fun u : ℝ => x₀ + A * Real.sin (Ω * u))
      (A * (Real.cos (Ω * t) * Ω)) t := (hsin.const_mul A).const_add x₀
  have heq : A * (Real.cos (Ω * t) * Ω) = zbwVelocity cStar Ω t := by
    unfold zbwVelocity; rw [← hAΩ]; ring
  unfold zbwPosition
  rw [← heq]
  exact h

/-! ### §B′ — the trembling *derived* from the Heisenberg equation (Eq. (2)) -/

/-- **The Zitterbewegung velocity solves a harmonic equation, and the trembling follows.**
Equation (2) of the paper is the Heisenberg equation of motion for the velocity operator,
`d²v̂/dt² + Ω²v̂ = (2Ωc*²/ℏ)·p̂ σ̌ₓ`.  For the prepared state `|↑, pₓ = 0⟩` the source term on the
right vanishes — *that* is what the choice of initial state buys — and the velocity obeys the
bare harmonic equation.  With the paper's initial data `⟨v̂⟩(0) = c*` and `⟨dv̂/dt⟩(0) = 0`, the
solution is forced: `⟨v̂(t)⟩ = c*·cos Ωt`.

The uniqueness is the energy argument: the deviation `w` from the claimed solution satisfies the
same equation with vanishing initial data, so `Ω²w² + (w′)²` has zero derivative, is therefore
constant at its initial value `0`, and — being a sum of squares with `Ω ≠ 0` — forces `w ≡ 0`. -/
theorem heisenberg_velocity_solution (Ω cStar ħ p σx : ℝ) (hΩ : Ω ≠ 0) (hp : p = 0)
    (v a : ℝ → ℝ)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hEq2 : ∀ t, HasDerivAt a (-(Ω ^ 2) * v t + 2 * Ω * cStar ^ 2 / ħ * (p * σx)) t)
    (hv0 : v 0 = cStar) (ha0 : a 0 = 0) :
    ∀ t, v t = zbwVelocity cStar Ω t := by
  -- the source term is switched off by the prepared state
  have hsrc : ∀ t, HasDerivAt a (-(Ω ^ 2) * v t) t := by
    intro t
    have ht := hEq2 t
    rwa [hp, zero_mul, mul_zero, add_zero] at ht
  -- deviation from the claimed solution
  set w : ℝ → ℝ := fun s => v s - cStar * Real.cos (Ω * s) with hw
  set dw : ℝ → ℝ := fun s => a s + cStar * (Ω * Real.sin (Ω * s)) with hdw
  have hlin : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Ω * u) Ω s := by
    intro s; simpa using (hasDerivAt_id s).const_mul Ω
  have hcos : ∀ s, HasDerivAt (fun u : ℝ => cStar * Real.cos (Ω * u))
      (cStar * (-(Real.sin (Ω * s)) * Ω)) s := fun s =>
    (((Real.hasDerivAt_cos (Ω * s)).comp s (hlin s)).const_mul cStar)
  have hsin : ∀ s, HasDerivAt (fun u : ℝ => cStar * (Ω * Real.sin (Ω * u)))
      (cStar * (Ω * (Real.cos (Ω * s) * Ω))) s := fun s =>
    ((((Real.hasDerivAt_sin (Ω * s)).comp s (hlin s)).const_mul Ω).const_mul cStar)
  have hwd : ∀ s, HasDerivAt w (dw s) s := by
    intro s
    have hd := (hv s).sub (hcos s)
    exact hd.congr_deriv (by simp only [hdw]; ring)
  have hdwd : ∀ s, HasDerivAt dw (-(Ω ^ 2) * w s) s := by
    intro s
    have hd := (hsrc s).add (hsin s)
    exact hd.congr_deriv (by simp only [hw]; ring)
  -- energy of the deviation is conserved and initially zero
  set E : ℝ → ℝ := fun s => Ω ^ 2 * w s ^ 2 + dw s ^ 2 with hE
  have hEd : ∀ s, HasDerivAt E 0 s := by
    intro s
    have h1 : HasDerivAt (fun u => Ω ^ 2 * w u ^ 2) (Ω ^ 2 * (2 * w s * dw s)) s :=
      (((hwd s).pow 2).const_mul (Ω ^ 2)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u => dw u ^ 2) (2 * dw s * (-(Ω ^ 2) * w s)) s :=
      ((hdwd s).pow 2).congr_deriv (by ring)
    exact (h1.add h2).congr_deriv (by ring)
  have hEconst : ∀ s, E s = E 0 :=
    fun s => is_const_of_deriv_eq_zero (fun u => (hEd u).differentiableAt)
      (fun u => (hEd u).deriv) s 0
  have hE0 : E 0 = 0 := by
    simp [hE, hw, hdw, hv0, ha0]
  -- a vanishing sum of squares kills the deviation
  intro t
  have hEt : Ω ^ 2 * w t ^ 2 + dw t ^ 2 = 0 := by rw [← hE0]; exact hEconst t
  have hΩ2 : 0 < Ω ^ 2 := by positivity
  have hsq : w t ^ 2 = 0 := by nlinarith [sq_nonneg (w t), sq_nonneg (dw t)]
  have hwt : w t = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  simp only [hw, sub_eq_zero] at hwt
  rw [zbwVelocity, hwt]

/-- **The trembling position follows by one integration.**  Any position whose derivative is the
velocity just derived differs from `x₀ + (c*/Ω)·sin Ωt` by a constant, fixed by its value at
`t = 0`.  Together with `zbwAmplitude_mul_frequency` this is exactly Eq. (3): the amplitude
`c*/Ω` is the Zitterbewegung amplitude `λ*_C/4π`. -/
theorem heisenberg_position_solution (Ω cStar : ℝ) (hΩ : Ω ≠ 0) (x : ℝ → ℝ)
    (hx : ∀ t, HasDerivAt x (zbwVelocity cStar Ω t) t) :
    ∀ t, x t = zbwPosition (x 0) (cStar / Ω) Ω t := by
  set g : ℝ → ℝ := fun s => x s - cStar / Ω * Real.sin (Ω * s) with hg
  have hlin : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Ω * u) Ω s := by
    intro s; simpa using (hasDerivAt_id s).const_mul Ω
  have hgd : ∀ s, HasDerivAt g 0 s := by
    intro s
    have hs : HasDerivAt (fun u : ℝ => cStar / Ω * Real.sin (Ω * u))
        (cStar / Ω * (Real.cos (Ω * s) * Ω)) s :=
      (((Real.hasDerivAt_sin (Ω * s)).comp s (hlin s)).const_mul (cStar / Ω))
    have hd := (hx s).sub hs
    refine hd.congr_deriv ?_
    rw [zbwVelocity]
    field_simp
    ring
  have hconst : ∀ s, g s = g 0 :=
    fun s => is_const_of_deriv_eq_zero (fun u => (hgd u).differentiableAt)
      (fun u => (hgd u).deriv) s 0
  intro t
  have hct := hconst t
  simp only [hg, Real.sin_zero, mul_zero, sub_zero] at hct
  rw [zbwPosition]
  linarith [hct]

/-! ### §C — the time-of-flight quadrature rotation (Eq. (6)) -/

/-- **The measured signal after a flight time** `t_TOF`: the in-situ position and the velocity
enter in quadrature, `sin(Ωt)/Ω + t_TOF·cos(Ωt)`, scaled by `c*` (Eq. (6), with the
non-participating terms dropped). -/
noncomputable def tofSignal (cStar Ω tTOF t : ℝ) : ℝ :=
  cStar * (Real.sin (Ω * t) / Ω + tTOF * Real.cos (Ω * t))

/-- **Time of flight rotates the readout from position to velocity.**  Written division-free,
the two quadratures `sin + (t_TOF Ω)·cos` and `(t_TOF Ω)·sin − cos` have squared lengths summing
to `1 + (t_TOF Ω)²`: they are one oscillation seen at a rotated phase.  At `t_TOF = 0` the first
is the position signal; as the flight time grows the `cos` term dominates it, so the image
reports velocity.  That is how the paper extracts both observables from the same experiment. -/
theorem tofSignal_quadrature_norm (Ω tTOF t : ℝ) :
    (Real.sin (Ω * t) + tTOF * Ω * Real.cos (Ω * t)) ^ 2
        + (tTOF * Ω * Real.sin (Ω * t) - Real.cos (Ω * t)) ^ 2
      = 1 + (tTOF * Ω) ^ 2 := by
  linear_combination (1 + (tTOF * Ω) ^ 2) * Real.sin_sq_add_cos_sq (Ω * t)

/-- The measured signal is that first quadrature, scaled by `c*/Ω`. -/
theorem tofSignal_eq_quadrature (cStar Ω tTOF t : ℝ) (hΩ : Ω ≠ 0) :
    tofSignal cStar Ω tTOF t
      = cStar / Ω * (Real.sin (Ω * t) + tTOF * Ω * Real.cos (Ω * t)) := by
  unfold tofSignal
  field_simp

/-- At zero time of flight the signal is the in-situ trembling of amplitude `c*/Ω`, which by
`zbwAmplitude_mul_frequency` is the Zitterbewegung amplitude itself. -/
theorem tofSignal_at_zero (cStar Ω t : ℝ) :
    tofSignal cStar Ω 0 t = cStar / Ω * Real.sin (Ω * t) := by
  unfold tofSignal
  ring

/-! ### §D — amplitude attenuation by non-participating atoms (§3.1) -/

/-- **The observed amplitude**: atoms left at rest by imperfect preparation (fraction `f₀`, about
`0.15` in the experiment) and thermally drifting atoms that never enter the coupled pair
(fraction `f_k`, about `0.4`) both dilute the signal, giving `(1−f₀)(1−f_k)` times the ideal
amplitude. -/
noncomputable def observedAmplitude (f₀ fk A : ℝ) : ℝ := (1 - f₀) * (1 - fk) * A

/-- **Non-participation can only attenuate.**  With both fractions in `[0,1]` and a nonnegative
ideal amplitude, the observed amplitude never exceeds the ideal one — the paper's factor of
about `2.5` between predicted and fitted amplitudes is this dilution, not a failure of Eq. (3). -/
theorem observedAmplitude_le_ideal {f₀ fk A : ℝ} (h₀ : 0 ≤ f₀) (h₀' : f₀ ≤ 1)
    (hk : 0 ≤ fk) (hk' : fk ≤ 1) (hA : 0 ≤ A) :
    observedAmplitude f₀ fk A ≤ A := by
  have h1 : (1 - f₀) * (1 - fk) ≤ 1 := by nlinarith
  unfold observedAmplitude
  exact mul_le_of_le_one_left hA h1

/-- **Full amplitude is seen exactly when every atom participates.**  For a strictly positive
ideal amplitude the observed amplitude equals it precisely when both non-participating fractions
vanish. -/
theorem observedAmplitude_eq_ideal_iff {f₀ fk A : ℝ} (hA : A ≠ 0) :
    observedAmplitude f₀ fk A = A ↔ (1 - f₀) * (1 - fk) = 1 := by
  unfold observedAmplitude
  constructor
  · intro h
    have hz : ((1 - f₀) * (1 - fk) - 1) * A = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · linarith
    · exact absurd h' hA
  · intro h; rw [h, one_mul]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.analogue_zitterbewegungFrequency_eq_coupling where
  formalizes @ "claim:in-the-condensate-analogue-the-four-photon-raman-coupling-is-exactly-the-zitterbewegung-frequency-because-the-engineered-rest-energy-is-half-the-coupling-strength",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:leblanc-spielman-2013-direct-observation-of-zitterbewegung-in-a-bose-einstein-condensate-new-j-phys-15-073011",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton",
  experimental_bound @ "value:leblanc-2013-coupling-frequency-omega-over-two-pi-between-2.4-and-4.3-kilohertz-with-analogue-light-speed-11.6-millimetres-per-second-and-compton-wavelength-about-one-micrometre;test:the-fitted-trembling-frequency-must-track-twice-the-independently-set-raman-coupling-rest-energy-over-hbar-across-the-coupling-range"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.zbwAmplitude_mul_frequency where
  formalizes @ "claim:the-zitterbewegung-amplitude-times-its-frequency-is-the-analogue-light-speed-so-the-trembling-crosses-its-own-amplitude-at-the-massless-branch-velocity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.zbwAmplitude_eq_half_comptonWavelength where
  formalizes @ "claim:the-observed-zitterbewegung-amplitude-is-half-the-reduced-compton-wavelength-of-the-engineered-mass",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.zbwPosition_hasDerivAt_velocity where
  formalizes @ "claim:the-trembling-position-and-velocity-are-two-quadratures-of-one-oscillation-a-quarter-cycle-out-of-phase",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.heisenberg_velocity_solution"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.heisenberg_velocity_solution where
  derives @ "claim:the-trembling-velocity-cosine-of-equation-three-is-forced-by-the-heisenberg-equation-for-the-velocity-operator-once-the-prepared-zero-momentum-state-switches-off-its-source-term",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:leblanc-spielman-2013-direct-observation-of-zitterbewegung-in-a-bose-einstein-condensate-new-j-phys-15-073011",
  caveat @ "claim:the-heisenberg-equation-of-motion-is-the-hypothesis-no-raman-level-structure-or-spin-operator-algebra-is-constructed-so-the-pauli-factor-enters-only-as-a-scalar-coefficient-annihilated-by-the-zero-momentum-state"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.heisenberg_position_solution where
  derives @ "claim:the-trembling-position-sine-of-equation-three-follows-from-the-derived-velocity-by-a-single-integration-with-amplitude-the-light-speed-over-the-trembling-frequency",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.heisenberg_velocity_solution"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.tofSignal_quadrature_norm where
  formalizes @ "claim:time-of-flight-rotates-the-imaged-signal-continuously-from-the-position-quadrature-to-the-velocity-quadrature-of-a-single-oscillation",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:leblanc-spielman-2013-direct-observation-of-zitterbewegung-in-a-bose-einstein-condensate-new-j-phys-15-073011"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.observedAmplitude_le_ideal where
  formalizes @ "claim:atoms-that-do-not-participate-can-only-attenuate-the-observed-trembling-amplitude-never-enhance-it",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-attenuation-is-the-papers-fitted-two-fraction-model-not-a-finite-temperature-derivation-of-the-fractions",
  experimental_bound @ "value:leblanc-2013-rest-fraction-f0-0.15-plus-minus-0.10-and-thermal-drifting-fraction-fk-about-0.4-giving-roughly-a-factor-2.5-attenuation;test:improved-state-preparation-and-colder-clouds-must-raise-the-observed-amplitude-toward-the-ideal-half-reduced-compton-wavelength"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation

end
