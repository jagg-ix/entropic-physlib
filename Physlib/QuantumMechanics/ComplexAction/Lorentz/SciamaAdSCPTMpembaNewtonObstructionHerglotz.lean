/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNavierStokesHerglotzHolographicG
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock
public import Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
meta import Zil

/-!
# What Newton cannot model: the Mpemba crossing needs the Herglotz replacement

Inspects the Newtonian obstruction to the quantum Mpemba effect (`SciamaAdSCPTQuantumMpembaCrossing`) and
supplies the Lagrangian–Hamiltonian–Herglotz replacement, on the repo's own carriers:

* **§1 — the obstruction, proved** (`newton_reversible_ordering_frozen`): conservative Newton flow is the
  *reversible* sector — a real generator gives `‖e^{−iκt}‖ = 1` (`reversible_generator_flow_unitary`,
  `Re λ = 0`), so distances from equilibrium are **constant in time** and their initial ordering is **frozen
  forever**: `b < a` stays `b·‖e^{−iκ₂t}‖ < a·‖e^{−iκ₁t}‖` for every `t`.  A crossing toward equilibrium —
  the defining Mpemba phenomenon — is *impossible* for `F = ma` from a conservative Lagrangian: energy
  conservation and Liouville volume preservation leave nothing to relax.
* **§2 — the variational face of the obstruction** (`frictionless_lagrangian_is_reversible`): the
  frictionless slice (`ν = 0`) has `L_eff = L_R` — the standard Lagrangian–Hamiltonian sector *is* the
  reversible sector (exactly as the Bohm slice is frictionless): no contact friction, no contraction, no
  Mpemba.  Adding `−γẋ` by hand to Newton exits the standard variational principle — that is the classical
  obstruction the Herglotz principle exists to solve.
* **§3 — the replacement, and the crossing it restores** (`herglotz_friction_crossing`): the Herglotz contact
  slice with friction — the repo's damped-Newton equation `mẍ + kx = −γẋ` as `dampedOscillatorContactSlice`
  (`ρ = γ/m`) — produces contracting envelopes `e^{−ρt}`, and **two different frictions cross**: for
  `0 < ρ₂ < ρ₃`, the higher-friction state overtakes after the explicit `t*` even starting farther — the
  Mpemba crossing (`mpemba_crossing` at `λ = −ρ`) realized *inside* the dissipative variational framework.
* **§4 — the quantum-exact agreement** (`nsHerglotz_quantum_exact`, reused in the capstone): the friction
  slice is *exactly* a Lindblad open-quantum contact slice at calibrated jump rate — so the replacement agrees
  with the Mpemba module's setting (Lindblad relaxation, spectral rates, per-trajectory Petz monotonicity).

`mpemba_selects_herglotz` bundles the verdict: **the Mpemba effect cannot be modeled by Newton's conservative
equations** (ordering frozen in the reversible/frictionless sector) **and is modeled by the Herglotz
replacement** (contact friction ⟹ contraction ⟹ explicit crossing), whose quantum-exact form is the Lindblad
slice — one dissipative variational framework from the damped oscillator through Navier–Stokes to the quantum
Mpemba effect.

The Herglotz friction is further welded across the campaign's clock structure:

* **§5 — Nagao–Nielsen contours** (`contact_damping_is_nagaoNielsen_modulus`): the damping envelope
  `e^{−ρt}` is the complex-action modulus at `S_I = ℏρt` — the friction accumulates imaginary action at
  rate `ℏρ`.
* **§6 — Misra age** (`misra_age_prices_imaginary_action`): the Misra internal-time operator reads the
  elapsed flow time, and the friction **prices that age into imaginary action**.
* **§7 — special relativity and calibration** (`herglotz_crossing_dilates_with_rapidity`,
  `herglotz_efolds_lorentz_invariant`, `mpemba_crossing_self_calibrates`,
  `crossing_calibration_rapidity_invariant`): rates red-shift by `1/cosh η`, crossings dilate like proper
  time, and the e-fold count `S_I/ℏ` is the boost invariant — the imaginary action is a Lorentz scalar.
  Consequently the crossing **self-calibrates**: `(λ₂−λ₃)·t* = log(a/b)` exactly — the crossing occurs at a
  differential e-fold count fixed by the preparation amplitudes alone, the same pure number in every
  boosted frame.  Calibration protocol: amplitudes from spectroscopy fix `log(a/b)`; the crossing event
  then fixes the rate-gap × duration product with no calibrated clock needed (the Misra age supplies the
  operational duration reading, which the friction prices — §6); residual disagreement in raw seconds
  between two laboratories measures their relative rapidity `cosh η = t*₁/t*₂`.
* **§8 — the laboratory-bath's fourth role** (`herglotz_contact_clocks_synthesis`): after clock, record,
  and arrow, the bath supplies the **variational friction** (`nsHerglotz_quantum_exact`).
* **§9 — entropic time as a group action** (`misra_age_is_group_coordinate`,
  `crossing_calibration_scaling_invariant`, `entropic_time_group_action_synthesis`): the Liouville flow is
  a one-parameter group (`liouvilleEvolve_add`) and the **Misra age is its additive coordinate** — flows
  compose, ages add — the same additivity as rapidity (`complexBoost_group`) and as heating
  (`heating_scales_entropic_clock` is the scaling representation, `thermal_rapidity_occupation` the
  hyperbolic one).  The Herglotz friction prices the coordinate into imaginary action (§6), and the priced
  coordinate at crossing is the **group invariant**: `log(a/b)` is unchanged by boosts
  (`crossing_calibration_rapidity_invariant`) *and* by heating/rate-scaling
  (`crossing_calibration_scaling_invariant`) — entropic time is a group action with Misra coordinate,
  Herglotz pricing, and a log-amplitude invariant.

Honest scope: the obstruction is the reversible-sector norm/ordering freeze (the exact finite face of energy
conservation); the crossing is the two-mode envelope theorem at contact-friction rates; the damped-oscillator
Euler–Lagrange derivation from the Herglotz principle is the cited classical content
(`ClassicalMechanics.HerglotzLazoContact`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open ClassicalMechanics

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz

open Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
open Physlib.QuantumMechanics.Lindblad.HerglotzContactCalibration
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNavierStokesHerglotzHolographicG
open Physlib.Optics.TemporalDoubleSlit
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock
open Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass

/-! ## §1. The Newtonian obstruction: the reversible sector freezes the ordering -/

/-- **[Conservative Newton flow cannot Mpemba-cross]** — under reversible (real-generator, `Re λ = 0`) flow
the norms are constant (`‖e^{−iκt}‖ = 1`), so distances from equilibrium keep their initial ordering **for
every `t`**: `b < a` stays `b·‖e^{−iκ₂t}‖ < a·‖e^{−iκ₁t}‖`.  Energy-conserving `F = ma` has nothing to relax
— the Mpemba crossing is impossible in the conservative sector. -/
theorem newton_reversible_ordering_frozen {a b : ℝ} (hba : b < a)
    (κ₁ κ₂ t : ℝ) :
    b * ‖Complex.exp (-Complex.I * (κ₂ : ℂ) * (t : ℂ))‖
      < a * ‖Complex.exp (-Complex.I * (κ₁ : ℂ) * (t : ℂ))‖ := by
  rw [reversible_generator_flow_unitary κ₁ t, reversible_generator_flow_unitary κ₂ t]
  simpa using hba

/-! ## §2. The variational face: frictionless = reversible -/

/-- **[The frictionless Lagrangian–Hamiltonian sector is the reversible sector]** `ν = 0 ⟹ L_eff = L_R` — the
standard (conservative) variational principle is exactly the zero-contact-friction slice: no contraction, no
Mpemba.  Adding `−γẋ` by hand exits the standard principle — the obstruction Herglotz solves. -/
theorem frictionless_lagrangian_is_reversible (L_R s : ℝ → ℝ) (t : ℝ) :
    (nsHerglotzSlice L_R s 0).effectiveLagrangian t = L_R t :=
  nsHerglotz_euler_limit L_R s t

/-! ## §3. The Herglotz replacement restores the crossing -/

/-- **[Two contact frictions Mpemba-cross]** — the Herglotz damped-Newton slices (`ρ = γ/m`,
`dampedOscillatorContactSlice`) produce contracting envelopes `e^{−ρt}`, and for `0 < ρ₂ < ρ₃` the
higher-friction state overtakes after `t* = log(a/b)/(ρ₃−ρ₂)`, even starting farther: the Mpemba crossing
realized inside the dissipative variational framework (`mpemba_crossing` at `λ = −ρ`). -/
theorem herglotz_friction_crossing {a b ρ₂ ρ₃ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hρ : ρ₂ < ρ₃) {t : ℝ} (ht : mpembaCrossingTime a b (-ρ₂) (-ρ₃) < t) :
    a * Real.exp (-ρ₃ * t) < b * Real.exp (-ρ₂ * t) :=
  mpemba_crossing ha hb (neg_lt_neg hρ) ht

/-! ## §4. The verdict -/

/-- **[The Mpemba effect selects Herglotz over Newton]** — **(i)** the obstruction: under the
reversible/conservative flow the ordering is frozen for all time (no crossing possible); **(ii)** the
frictionless variational sector is exactly that reversible sector (`L_eff = L_R` at `ν = 0`); **(iii)** the
Herglotz contact friction restores the crossing, with the explicit `t*`; **(iv)** the friction slice is
quantum-exactly a Lindblad contact slice at calibrated jump rate — agreeing with the Mpemba module's Lindblad
setting.  Newton's conservative equations cannot model the Mpemba effect; the
Lagrangian–Hamiltonian–Herglotz replacement models it exactly. -/
theorem mpemba_selects_herglotz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {a b ρ₂ ρ₃ : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hρ : ρ₂ < ρ₃)
    {t : ℝ} (ht : mpembaCrossingTime a b (-ρ₂) (-ρ₃) < t)
    (κ₁ κ₂ s' : ℝ)
    (L : H →L[ℂ] H) (ℏbar : ℝ) (ψ : H) (L_R sfn : ℝ → ℝ) (ν : ℝ)
    (hcal : lindbladRate L ℏbar ψ = ν) :
    (b * ‖Complex.exp (-Complex.I * (κ₂ : ℂ) * (s' : ℂ))‖
        < a * ‖Complex.exp (-Complex.I * (κ₁ : ℂ) * (s' : ℂ))‖)
      ∧ (nsHerglotzSlice L_R sfn 0).effectiveLagrangian s' = L_R s'
      ∧ a * Real.exp (-ρ₃ * t) < b * Real.exp (-ρ₂ * t)
      ∧ lindbladContactSlice L ℏbar ψ L_R sfn = nsHerglotzSlice L_R sfn ν :=
  ⟨newton_reversible_ordering_frozen hba κ₁ κ₂ s',
    frictionless_lagrangian_is_reversible L_R sfn s',
    herglotz_friction_crossing ha hb hρ ht,
    nsHerglotz_quantum_exact L ℏbar ψ L_R sfn ν hcal⟩

/-! ## §5. The contact damping is the Nagao–Nielsen contour modulus -/

/-- **[The Herglotz friction is an imaginary-action rate]** — the contact damping envelope `e^{−ρt}` is the
Nagao–Nielsen complex-action modulus at `S_I = ℏ·ρt`: the friction accumulates imaginary action at rate
`ℏρ`, for any real-action (Lorentzian, contour-phase) content `S_R`. -/
theorem contact_damping_is_nagaoNielsen_modulus (S_R ρ t ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ‖nagaoNielsenComplexActionWeight S_R (ℏ * (ρ * t)) ℏ‖ = Real.exp (-(ρ * t)) := by
  rw [nagaoNielsen_eq_master S_R (ℏ * (ρ * t)) ℏ hℏ, master_modulus_is_kuiken]
  unfold kuikenWeight
  congr 1
  field_simp

/-! ## §6. The Misra age, priced into imaginary action -/

/-- **[The Misra age is what the friction prices]** — **(i)** the Misra internal-time operator reads the
elapsed flow time as its eigenvalue on the Liouville evolution factor; **(ii)** the Herglotz contact
friction converts exactly that age into imaginary action, `S_I = ℏρ·t`, whose Nagao–Nielsen modulus is the
damping envelope.  The dissipation weight is a priced age. -/
theorem misra_age_prices_imaginary_action (S_R ρ t ℏ lam : ℝ) (hℏ : ℏ ≠ 0) :
    (ageOperator (liouvilleEvolve t (fun _ => 1)) lam
        = (t : ℂ) * liouvilleEvolve t (fun _ => 1) lam)
      ∧ ‖nagaoNielsenComplexActionWeight S_R (ℏ * (ρ * t)) ℏ‖ = Real.exp (-(ρ * t)) :=
  ⟨ageOperator_reads_evolution_time t lam,
    contact_damping_is_nagaoNielsen_modulus S_R ρ t ℏ hℏ⟩

/-! ## §7. Special relativity: rates red-shift, the e-fold count is invariant -/

/-- **[The crossing dilates like proper time]** — under a boost of rapidity `η` the contact rates
red-shift by `1/cosh η` and the Mpemba crossing time dilates by `lorentzFactor η = cosh η`, exactly. -/
theorem herglotz_crossing_dilates_with_rapidity (a b ρ₂ ρ₃ η : ℝ) :
    mpembaCrossingTime a b (-ρ₂ / lorentzFactor η) (-ρ₃ / lorentzFactor η)
      = lorentzFactor η * mpembaCrossingTime a b (-ρ₂) (-ρ₃) :=
  mpembaCrossingTime_entropic_units a b (-ρ₂) (-ρ₃) (lorentzFactor η)

/-- **[The e-fold count is the boost invariant]** — red-shifted rate × dilated duration is exact:
`(ρ/cosh η)·(cosh η·t) = ρt` — the accumulated imaginary action `S_I = ℏρt` is a Lorentz scalar, as an
action must be. -/
theorem herglotz_efolds_lorentz_invariant (ρ t η : ℝ) :
    ρ / lorentzFactor η * (lorentzFactor η * t) = ρ * t := by
  have hγ : lorentzFactor η ≠ 0 := by
    unfold lorentzFactor
    exact (Real.cosh_pos η).ne'
  field_simp

/-- **[The crossing self-calibrates]** — `(λ₂−λ₃)·t* = log(a/b)` exactly: the Mpemba crossing occurs at a
differential e-fold count fixed by the preparation amplitudes alone — a pure number, unit-free and
clock-free.  The crossing event calibrates the rate-gap × duration product instead of requiring a
calibrated clock to time it. -/
theorem mpemba_crossing_self_calibrates (a b : ℝ) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (lam2 - lam3) * mpembaCrossingTime a b lam2 lam3 = Real.log (a / b) := by
  unfold mpembaCrossingTime
  rw [mul_comm]
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr hne)

/-- **[The calibration point is rapidity-invariant]** — in a frame boosted by rapidity `η` the rates
red-shift by `1/cosh η` and the crossing dilates, but the differential e-fold count at crossing is the same
pure number `log(a/b)`: two laboratories calibrate on the amplitudes, and their residual disagreement in
raw seconds measures `cosh η`. -/
theorem crossing_calibration_rapidity_invariant (a b η : ℝ) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (lam2 / lorentzFactor η - lam3 / lorentzFactor η)
        * mpembaCrossingTime a b (lam2 / lorentzFactor η) (lam3 / lorentzFactor η)
      = Real.log (a / b) := by
  have hγ : lorentzFactor η ≠ 0 := by
    unfold lorentzFactor
    exact (Real.cosh_pos η).ne'
  refine mpemba_crossing_self_calibrates a b ?_
  intro h
  exact hne (by field_simp at h; exact h)

/-! ## §9'. Entropic time as a group action (placed with §7's invariants) -/

/-- **[The Misra age is the additive group coordinate of the flow]** — the Liouville evolution is a
one-parameter group (`liouvilleEvolve_add`) and the age operator reads its additive coordinate: evolving by
`t₁` then `t₂` composes to `t₁ + t₂`, and the age eigenvalue is exactly that sum.  The same additive
structure as rapidity (`complexBoost_group`, ZIL-linked) and as the heating action on the clock: entropic
time is a group action and the Misra operator supplies its coordinate. -/
theorem misra_age_is_group_coordinate (t₁ t₂ lam : ℝ) :
    liouvilleEvolve t₁ (liouvilleEvolve t₂ (fun _ => 1)) = liouvilleEvolve (t₁ + t₂) (fun _ => 1)
      ∧ ageOperator (liouvilleEvolve (t₁ + t₂) (fun _ => 1)) lam
          = ((t₁ + t₂ : ℝ) : ℂ) * liouvilleEvolve (t₁ + t₂) (fun _ => 1) lam :=
  ⟨liouvilleEvolve_add t₁ t₂ (fun _ => 1),
    ageOperator_reads_evolution_time (t₁ + t₂) lam⟩

/-- **[The calibration point is invariant under heating]** — scaling all rates by `c ≠ 0` (the heating
action, `heating_scales_entropic_clock`) rescales the crossing time inversely, and the differential e-fold
count at crossing is the same pure number `log(a/b)`: together with
`crossing_calibration_rapidity_invariant`, the calibration point is invariant under the **full group
action** — boosts and heating alike. -/
theorem crossing_calibration_scaling_invariant (a b c : ℝ) (hc : c ≠ 0)
    {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (c * lam2 - c * lam3) * mpembaCrossingTime a b (c * lam2) (c * lam3) = Real.log (a / b) :=
  mpemba_crossing_self_calibrates a b (fun h => hne (mul_left_cancel₀ hc h))

/-- **[The Gaussian crossing self-calibrates in squared time]** — for Gaussian (dilation-decoherence)
envelopes the calibration identity reads `(Γ₃² − Γ₂²)·t*² = log(a/b)`: the crossing occurs at a fixed
squared-time e-fold count, still clock-free and unit-free — the entropic gravimeter's differential version
inherits the whole calibration structure under `u = t²`. -/
theorem gaussian_crossing_self_calibrates (a b : ℝ) {Γ₂ Γ₃ : ℝ} (hne : Γ₂ ^ 2 ≠ Γ₃ ^ 2) :
    (Γ₃ ^ 2 - Γ₂ ^ 2) * mpembaCrossingTime a b (-Γ₂ ^ 2) (-Γ₃ ^ 2) = Real.log (a / b) := by
  have h := mpemba_crossing_self_calibrates a b
    (fun hcontra => hne (neg_injective hcontra)) (lam2 := -Γ₂ ^ 2) (lam3 := -Γ₃ ^ 2)
  linarith [h]

/-- **[A single station cannot see gravity]** — the gravitational redshift acts on all local rates as one
common scaling `1/(1+s)` (`s = Φ/c²`) in coordinate time, and the calibration point is scaling-invariant:
the coordinate-rate-scaled crossing still calibrates at `log(a/b)`.  The equivalence principle, as a
corollary of `crossing_calibration_scaling_invariant`: Mpemba gravimetry must be differential
(`mpemba_differential_gravimeter`). -/
theorem mpemba_local_gravity_blind (a b s : ℝ) (hs : 1 + s ≠ 0)
    {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (1 / (1 + s) * lam2 - 1 / (1 + s) * lam3)
        * mpembaCrossingTime a b (1 / (1 + s) * lam2) (1 / (1 + s) * lam3)
      = Real.log (a / b) :=
  crossing_calibration_scaling_invariant a b (1 / (1 + s)) (one_div_ne_zero hs) hne

/-- **[Mpemba gravimetry]** — **(i)** locally blind: the equivalence principle as scaling invariance of the
calibration point; **(ii)** differentially sharp: two stations at heights `h₁, h₂` with a common clock
recover `g` exactly; **(iii)** the recovery rests on the clock-free self-calibration `(λ₂−λ₃)t* = log(a/b)`
that fixes the shared proper crossing.  The acceleration face (`crossing_ticks_laboratory_relative`,
`UnruhFourClocks`) is the ZIL-linked Unruh reading of the same structure. -/
theorem mpemba_gravimetry_synthesis (a b s g h₁ h₂ c tstar t₁ t₂ : ℝ)
    (hs : 1 + s ≠ 0) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3)
    (h1 : 1 + g * h₁ / c ^ 2 ≠ 0) (h2 : 1 + g * h₂ / c ^ 2 ≠ 0) (hts : tstar ≠ 0)
    (ht₁ : t₁ = tstar / (1 + g * h₁ / c ^ 2)) (ht₂ : t₂ = tstar / (1 + g * h₂ / c ^ 2)) :
    ((1 / (1 + s) * lam2 - 1 / (1 + s) * lam3)
        * mpembaCrossingTime a b (1 / (1 + s) * lam2) (1 / (1 + s) * lam3)
      = Real.log (a / b))
      ∧ (t₁ / t₂ = (1 + g * h₂ / c ^ 2) / (1 + g * h₁ / c ^ 2)
          ∧ g * (h₂ - h₁) / c ^ 2 = (t₁ / t₂ - 1) * (1 + g * h₁ / c ^ 2))
      ∧ (lam2 - lam3) * mpembaCrossingTime a b lam2 lam3 = Real.log (a / b) :=
  ⟨mpemba_local_gravity_blind a b s hs hne,
    mpemba_differential_gravimeter g h₁ h₂ c tstar t₁ t₂ h1 h2 hts ht₁ ht₂,
    mpemba_crossing_self_calibrates a b hne⟩

/-! ## §9''. Optical gravimetry: the rainbow reads the capillary length -/

/-- Capillary length `ℓ_c = √(σ/(ρg))` — the scale below which surface tension beats gravity.  Raindrop
flattening (which shapes the rainbow's angular structure) is governed by `(r/ℓ_c)²`; water on Earth:
`ℓ_c = 2.71 mm`. -/
noncomputable def capillaryLength (σ ρ g : ℝ) : ℝ := Real.sqrt (σ / (ρ * g))

/-- Bond number `Bd = gρr²/σ` — buoyancy/gravity against surface tension at drop radius `r`. -/
def bondNumber (g ρ r σ : ℝ) : ℝ := g * ρ * r ^ 2 / σ

/-- **[The Bond number is the squared capillary ratio]** — `Bd = (r/ℓ_c)²`: drop flattening is set by the
drop radius in capillary-length units.  The rainbow's flattening onset *is* an ℓ_c reading. -/
theorem bond_is_capillary_ratio (g ρ r σ : ℝ) (hσ : 0 < σ) (hρ : 0 < ρ) (hg : 0 < g) :
    bondNumber g ρ r σ = (r / capillaryLength σ ρ g) ^ 2 := by
  unfold bondNumber capillaryLength
  rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ σ / (ρ * g))]
  field_simp

/-- **[The rainbow gravimeter]** — the capillary length inverts exactly: `g = σ/(ρ·ℓ_c²)`.  Reading the
drop-flattening scale from a rainbow's angular structure (fluid properties `σ, ρ` known) computes the
planet's effective gravity — no apparatus, only optics on falling rain. -/
theorem rainbow_gravimeter (σ ρ g : ℝ) (hσ : 0 < σ) (hρ : 0 < ρ) (hg : 0 < g) :
    σ / (ρ * capillaryLength σ ρ g ^ 2) = g := by
  unfold capillaryLength
  rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ σ / (ρ * g))]
  field_simp

/-- **[Capillary–gravity dispersion has a gravity-fixed minimum]** — the squared phase speed
`v(k) = g/k + (σ/ρ)k` obeys `v(k)² ≥ 4gσ/ρ` for all `k > 0`, with equality at `k_c = √(gρ/σ) = 1/ℓ_c`.
The minimum phase speed of surface waves — measurable optically on any pond — satisfies
`c_min⁴ = 4gσ/ρ`. -/
theorem capillary_gravity_min_speed (g σ ρ : ℝ) (hg : 0 < g) (hσ : 0 < σ) (hρ : 0 < ρ) :
    (∀ k : ℝ, 0 < k → (g / k + σ * k / ρ) ^ 2 ≥ 4 * (g * σ / ρ))
      ∧ (g / Real.sqrt (g * ρ / σ) + σ * Real.sqrt (g * ρ / σ) / ρ) ^ 2 = 4 * (g * σ / ρ) := by
  constructor
  · intro k hk
    have hx : g / k * (σ * k / ρ) = g * σ / ρ := by
      field_simp
    nlinarith [sq_nonneg (g / k - σ * k / ρ), hx]
  · have hkc : Real.sqrt (g * ρ / σ) ^ 2 = g * ρ / σ :=
      Real.sq_sqrt (by positivity)
    have hkpos : 0 < Real.sqrt (g * ρ / σ) := Real.sqrt_pos.mpr (by positivity)
    have hσk : σ * Real.sqrt (g * ρ / σ) ^ 2 = g * ρ := by
      rw [hkc]
      field_simp
    have heq : g / Real.sqrt (g * ρ / σ) = σ * Real.sqrt (g * ρ / σ) / ρ := by
      rw [div_eq_div_iff hkpos.ne' (by positivity : (ρ:ℝ) ≠ 0)]
      linear_combination -hσk
    rw [heq]
    have hterm : (σ * Real.sqrt (g * ρ / σ) / ρ) ^ 2 = g * σ / ρ := by
      rw [div_pow, mul_pow, hkc]
      field_simp
    nlinarith [hterm]

/-- **[The pond gravimeter]** — the measured minimum squared phase speed `v_min = c_min²` inverts:
`g = ρ·v_min²/(4σ)`.  Optical measurement of the slowest surface ripples computes effective gravity. -/
theorem pond_gravimeter (g σ ρ v : ℝ) (hσ : 0 < σ) (hρ : 0 < ρ) (hg : 0 < g)
    (hv : v ^ 2 = 4 * (g * σ / ρ)) :
    ρ * v ^ 2 / (4 * σ) = g := by
  rw [hv]
  field_simp

/-- Dimensionless vapor velocity `J_g = xG/√(gDρ_gΔρ)` — the shear-vs-buoyancy group governing when a
condensing film's relaxation physics is gravity-influenced (`J_g < 1`) or gravity-blind (`J_g > 1`).
Flight anchor (Mudawar et al., IJHMT 254 (2026) 127602, ISS/FBCE, nPFH in `D = 7.24 mm`, `Bd = (D/ℓ_c)²
≈ 101` at `1g`): the `J_g = 1` boundary sits at `xG ≈ 39 kg/m²s`; measured orientation spread `~35%` at
`G ≈ 97` collapsing to `~5%` by `G ≈ 194` — and g-free correlations predict the μg database at `7.1%`
while g-dependent forms fail at up to `100%`: the empirical classical-channel blindness test. -/
noncomputable def dimensionlessVaporVelocity (x G g D ρg Δρ : ℝ) : ℝ :=
  x * G / Real.sqrt (g * D * ρg * Δρ)

/-- **[The blindness boundary scales as `√g`]** — `J_g(c·g) = J_g(g)/√c`: the classical channel's
gravity-influence boundary `xG* = √(gDρ_gΔρ)` moves as `√g` between planets (Earth 39 → Mars 24 → Moon
16 kg/m²s for the FBCE geometry). -/
theorem vapor_velocity_gravity_scaling (x G g D ρg Δρ c : ℝ) (hc : 0 ≤ c) :
    dimensionlessVaporVelocity x G (c * g) D ρg Δρ
      = dimensionlessVaporVelocity x G g D ρg Δρ / Real.sqrt c := by
  unfold dimensionlessVaporVelocity
  rw [show c * g * D * ρg * Δρ = c * (g * D * ρg * Δρ) by ring, Real.sqrt_mul hc]
  rw [div_div]
  ring

/-- **[The blindness boundary]** — `J_g = 1` exactly when `xG = √(gDρ_gΔρ)`: above the boundary the film
is shear-dominated and its proper relaxation physics is gravity-blind (the classical validity condition
for the differential gravimeter's equal-proper-physics hypothesis); below it, gravity is a classical
percent-level channel. -/
theorem shear_blindness_boundary (x G g D ρg Δρ : ℝ)
    (hs : Real.sqrt (g * D * ρg * Δρ) ≠ 0) :
    dimensionlessVaporVelocity x G g D ρg Δρ = 1 ↔ x * G = Real.sqrt (g * D * ρg * Δρ) := by
  unfold dimensionlessVaporVelocity
  rw [div_eq_one_iff_eq hs]

/-- **[The regime classification]** — `J_g < 1` exactly when `xG` is below the boundary (gravity
influences the film), `J_g > 1` exactly when above it (shear dominates, gravity-blind): the two-sided
version of `shear_blindness_boundary`. -/
theorem shear_regime_classification (x G g D ρg Δρ : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hρg : 0 < ρg) (hΔρ : 0 < Δρ) :
    (dimensionlessVaporVelocity x G g D ρg Δρ < 1 ↔ x * G < Real.sqrt (g * D * ρg * Δρ))
      ∧ (1 < dimensionlessVaporVelocity x G g D ρg Δρ
          ↔ Real.sqrt (g * D * ρg * Δρ) < x * G) := by
  have hS : 0 < Real.sqrt (g * D * ρg * Δρ) := Real.sqrt_pos.mpr (by positivity)
  unfold dimensionlessVaporVelocity
  exact ⟨div_lt_one hS, one_lt_div hS⟩

/-- **[The boundary orders with gravity]** — heavier planets need more flow to reach blindness:
`g₁ < g₂ ⟹ xG*(g₁) < xG*(g₂)` (Moon 16 < Mars 24 < Earth 39 kg/m²s for the FBCE geometry). -/
theorem blindness_boundary_monotone (g₁ g₂ D ρg Δρ : ℝ)
    (hD : 0 < D) (hρg : 0 < ρg) (hΔρ : 0 < Δρ) (hg₁ : 0 ≤ g₁) (h12 : g₁ < g₂) :
    Real.sqrt (g₁ * D * ρg * Δρ) < Real.sqrt (g₂ * D * ρg * Δρ) := by
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith [mul_pos (mul_pos hD hρg) hΔρ]

/-- **[More gravity, more influence]** — at fixed flow, increasing gravity decreases `J_g`
(`J_g(c·g) = J_g/√c < J_g` for `c > 1`): gravity pushes the system toward the influenced regime, flow
pushes it out. -/
theorem gravity_influence_monotone (x G g D ρg Δρ c : ℝ) (hc : 1 < c)
    (hJ : 0 < dimensionlessVaporVelocity x G g D ρg Δρ) :
    dimensionlessVaporVelocity x G (c * g) D ρg Δρ
      < dimensionlessVaporVelocity x G g D ρg Δρ := by
  rw [vapor_velocity_gravity_scaling x G g D ρg Δρ c (by linarith)]
  have h1 : 1 < Real.sqrt c := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hc
  exact div_lt_self hJ h1

/-- **[Gated gravimetry, complete]** — the full chain of the flight-anchored story: **(i)** the system
sits in the gravity-blind regime exactly when `xG` exceeds the boundary (`J_g > 1`; classical channel
off, flight-tested by the FBCE correlation tournament); **(ii)** there, gravity enters only as the
redshift common scaling — invisible to a single station (`mpemba_local_gravity_blind`); **(iii)** two
such stations with one common clock recover `g` exactly (`mpemba_differential_gravimeter`).  When the
classical channel is off, the relativistic channel is all that remains — and it suffices. -/
theorem gated_gravimetry_synthesis (x G g D ρg Δρ : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hρg : 0 < ρg) (hΔρ : 0 < Δρ)
    (a b s : ℝ) (hs : 1 + s ≠ 0) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3)
    (g' h₁ h₂ c' tstar t₁ t₂ : ℝ)
    (hden1 : 1 + g' * h₁ / c' ^ 2 ≠ 0) (hden2 : 1 + g' * h₂ / c' ^ 2 ≠ 0) (hts : tstar ≠ 0)
    (ht₁ : t₁ = tstar / (1 + g' * h₁ / c' ^ 2)) (ht₂ : t₂ = tstar / (1 + g' * h₂ / c' ^ 2)) :
    (1 < dimensionlessVaporVelocity x G g D ρg Δρ
        ↔ Real.sqrt (g * D * ρg * Δρ) < x * G)
      ∧ ((1 / (1 + s) * lam2 - 1 / (1 + s) * lam3)
            * mpembaCrossingTime a b (1 / (1 + s) * lam2) (1 / (1 + s) * lam3)
          = Real.log (a / b))
      ∧ g' * (h₂ - h₁) / c' ^ 2 = (t₁ / t₂ - 1) * (1 + g' * h₁ / c' ^ 2) :=
  ⟨(shear_regime_classification x G g D ρg Δρ hg hD hρg hΔρ).2,
    mpemba_local_gravity_blind a b s hs hne,
    (mpemba_differential_gravimeter g' h₁ h₂ c' tstar t₁ t₂ hden1 hden2 hts ht₁ ht₂).2⟩

/-- **[The moiré dispersion gravimeter]** — two surface-wave trains obeying the capillary–gravity
dispersion `ω² = gk + (σ/ρ)k³` yield the exact difference quotient
`(ω₁²−ω₂²)/(k₁−k₂) = g + (σ/ρ)(k₁² + k₁k₂ + k₂²)` — and `k₁−k₂` is precisely what the moiré envelope
measures best (`moire_envelope_modulus`: the difference is the observable, magnified by `k̄/Δk`).  In the
gravity branch (`σ → 0` or long waves) the quotient **is** `g`: moiré-read dispersion computes effective
gravity. -/
theorem moire_dispersion_gravimeter (g σ ρ ω₁ ω₂ k₁ k₂ : ℝ) (hρ : ρ ≠ 0) (hk : k₁ ≠ k₂)
    (hω₁ : ω₁ ^ 2 = g * k₁ + σ / ρ * k₁ ^ 3) (hω₂ : ω₂ ^ 2 = g * k₂ + σ / ρ * k₂ ^ 3) :
    (ω₁ ^ 2 - ω₂ ^ 2) / (k₁ - k₂) = g + σ / ρ * (k₁ ^ 2 + k₁ * k₂ + k₂ ^ 2) := by
  have hnum : ω₁ ^ 2 - ω₂ ^ 2
      = (k₁ - k₂) * (g + σ / ρ * (k₁ ^ 2 + k₁ * k₂ + k₂ ^ 2)) := by
    linear_combination hω₁ - hω₂
  rw [hnum, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hk)]

/-- **[The entropic gravimeter, complete]** — **(i)** the dilation-decoherence rate inverts to `g`
exactly; **(ii)** its visibility loss is the Nagao–Nielsen contour modulus at `S_I = ℏΓt` (the arc's
imaginary-action sector — this *is* an entropic-time effect); **(iii)** two composites with rates
`Γ₂ < Γ₃` (different `N`, `x`, or `T`) exhibit the Mpemba crossing of visibilities at the explicit `t*` —
the self-calibrating, clock-free differential version of the measurement. -/
theorem entropic_gravimeter_synthesis (g x c ωE N : ℝ)
    (hx : x ≠ 0) (hc : c ≠ 0) (hω : ωE ≠ 0) (hN : 0 < N)
    (S_R t ℏ : ℝ) (hℏ : ℏ ≠ 0) (Γ : ℝ)
    {a b Γ₂ Γ₃ : ℝ} (ha : 0 < a) (hb : 0 < b) (hΓ : Γ₂ < Γ₃)
    {t' : ℝ} (ht' : mpembaCrossingTime a b (-Γ₂) (-Γ₃) < t') :
    (dilationDecoherenceRate g x c ωE N * c ^ 2 / (x * Real.sqrt (N / 2) * ωE) = g)
      ∧ ‖nagaoNielsenComplexActionWeight S_R (ℏ * (Γ * t)) ℏ‖ = Real.exp (-(Γ * t))
      ∧ a * Real.exp (-Γ₃ * t') < b * Real.exp (-Γ₂ * t') :=
  ⟨dilation_gravimeter_recovery g x c ωE N hx hc hω hN,
    contact_damping_is_nagaoNielsen_modulus S_R Γ t ℏ hℏ,
    herglotz_friction_crossing ha hb hΓ ht'⟩


/-! ## §8. The synthesis: the bath's fourth role is the friction -/

/-- **[The Herglotz friction across the clocks]** — **(i)** the laboratory-bath supplies the friction: the
calibrated Lindblad jump rate *is* the contact rate of the slice (its fourth role, after clock, record,
arrow); **(ii)** the damping is the Nagao–Nielsen contour modulus at `S_I = ℏρt`; **(iii)** the Misra age
is what the friction prices; **(iv)** rates red-shift with rapidity, the crossing dilates like proper time,
and the e-fold count `S_I/ℏ` is the boost invariant; **(v)** the friction crossing follows at the explicit
`t*`. -/
theorem herglotz_contact_clocks_synthesis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : H →L[ℂ] H) (ℏbar : ℝ) (ψ : H) (L_R sfn : ℝ → ℝ) (ν : ℝ)
    (hcal : lindbladRate L ℏbar ψ = ν)
    (S_R t ℏ lam η : ℝ) (hℏ : ℏ ≠ 0)
    {a b ρ₂ ρ₃ : ℝ} (ha : 0 < a) (hb : 0 < b) (hρ : ρ₂ < ρ₃)
    {t' : ℝ} (ht' : mpembaCrossingTime a b (-ρ₂) (-ρ₃) < t') :
    lindbladContactSlice L ℏbar ψ L_R sfn = nsHerglotzSlice L_R sfn ν
      ∧ ‖nagaoNielsenComplexActionWeight S_R (ℏ * (ν * t)) ℏ‖ = Real.exp (-(ν * t))
      ∧ (ageOperator (liouvilleEvolve t (fun _ => 1)) lam
          = (t : ℂ) * liouvilleEvolve t (fun _ => 1) lam)
      ∧ (mpembaCrossingTime a b (-ρ₂ / lorentzFactor η) (-ρ₃ / lorentzFactor η)
            = lorentzFactor η * mpembaCrossingTime a b (-ρ₂) (-ρ₃)
          ∧ ν / lorentzFactor η * (lorentzFactor η * t) = ν * t)
      ∧ a * Real.exp (-ρ₃ * t') < b * Real.exp (-ρ₂ * t') :=
  ⟨nsHerglotz_quantum_exact L ℏbar ψ L_R sfn ν hcal,
    contact_damping_is_nagaoNielsen_modulus S_R ν t ℏ hℏ,
    ageOperator_reads_evolution_time t lam,
    ⟨herglotz_crossing_dilates_with_rapidity a b ρ₂ ρ₃ η,
      herglotz_efolds_lorentz_invariant ν t η⟩,
    herglotz_friction_crossing ha hb hρ ht'⟩

/-- **[Entropic time is a group action: Misra coordinate, Herglotz pricing, log-amplitude invariant]** —
**(i)** heating acts linearly on the clock and hyperbolically on the vacuum (`cosh 2θ = 1 + 2n̄`);
**(ii)** the Misra age is the additive coordinate of the flow group; **(iii)** the Herglotz friction prices
the coordinate into imaginary action (NN modulus); **(iv)** the priced coordinate at crossing is the group
invariant: `log(a/b)` under heating *and* under boosts. -/
theorem entropic_time_group_action_synthesis
    (kB T ℏc c₀ : ℝ) {θ x : ℝ} (hx : 0 < x) (hθ : Real.tanh θ = Real.exp (-(x / 2)))
    (t₁ t₂ lam : ℝ) (S_R ρ t ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (a b c η : ℝ) (hc : c ≠ 0) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (thermalEntropicRate kB (c₀ * T) ℏc = c₀ * thermalEntropicRate kB T ℏc
        ∧ Real.cosh (2 * θ) = 1 + 2 * boseEinstein 1 x)
      ∧ (liouvilleEvolve t₁ (liouvilleEvolve t₂ (fun _ => 1))
            = liouvilleEvolve (t₁ + t₂) (fun _ => 1)
          ∧ ageOperator (liouvilleEvolve (t₁ + t₂) (fun _ => 1)) lam
            = ((t₁ + t₂ : ℝ) : ℂ) * liouvilleEvolve (t₁ + t₂) (fun _ => 1) lam)
      ∧ ‖nagaoNielsenComplexActionWeight S_R (ℏ * (ρ * t)) ℏ‖ = Real.exp (-(ρ * t))
      ∧ ((c * lam2 - c * lam3) * mpembaCrossingTime a b (c * lam2) (c * lam3) = Real.log (a / b)
          ∧ (lam2 / lorentzFactor η - lam3 / lorentzFactor η)
              * mpembaCrossingTime a b (lam2 / lorentzFactor η) (lam3 / lorentzFactor η)
            = Real.log (a / b)) :=
  ⟨⟨heating_scales_entropic_clock kB T ℏc c₀, thermal_rapidity_occupation hx hθ⟩,
    misra_age_is_group_coordinate t₁ t₂ lam,
    contact_damping_is_nagaoNielsen_modulus S_R ρ t ℏ hℏ,
    ⟨crossing_calibration_scaling_invariant a b c hc hne,
      crossing_calibration_rapidity_invariant a b η hne⟩⟩

/-! ## §11. One invariant, three conventions: interval, potential, contour -/

/-- **[A global convention is locally unobservable — the three faces]** — the simultaneity dichotomy, the
equivalence principle, and the Nagao–Nielsen contour are one structure: a globally-chosen convention that
no local measurement resolves, standing over a synchronization-independent invariant.

* **(i) Simultaneity ↔ the Minkowski interval.**  The absolute-simultaneity time `t/γ` *is* the proper
  time `√(c²t² − (ut)²)/c` of the co-moving clock (`lta_time_is_minkowski_proper_time`): the choice of
  `t = const` surfaces is a convention, but the interval a single clock reads is not.
* **(ii) Equivalence principle ↔ the calibration `log(a/b)`.**  The gravitational potential enters every
  local rate as one common scaling `1/(1+s)`, and the Mpemba calibration is scaling-invariant
  (`mpemba_local_gravity_blind`): a single station cannot see the potential, exactly as a single frame
  cannot see the synchronization.
* **(iii) Nagao–Nielsen contour ↔ the entropic modulus `e^{−ρt}`.**  The friction prices imaginary
  action onto the Euclidean (imaginary-modular-time) contour, where the modulus is
  `‖NN‖ = e^{−ρt}` (`contact_damping_is_nagaoNielsen_modulus`) — the real-time slicing convention of (i)
  never touches it; the entropic decay is what survives the Wick rotation of the interval.

The invariant under all three conventions is the interval / proper time (i), read as the calibration
`log(a/b)` (ii) and as the imaginary-time modulus (iii). -/
theorem simultaneity_potential_contour_synthesis
    {γ u c t : ℝ} (hγ : γ ^ 2 * (c ^ 2 - u ^ 2) = c ^ 2) (hc : 0 < c) (hγ0 : 0 < γ) (ht : 0 ≤ t)
    (a b s : ℝ) (hs : 1 + s ≠ 0) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3)
    (S_R ρ ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    (Real.sqrt (c ^ 2 * t ^ 2 - (u * t) ^ 2) / c = ltaTime γ t)
      ∧ ((1 / (1 + s) * lam2 - 1 / (1 + s) * lam3)
          * mpembaCrossingTime a b (1 / (1 + s) * lam2) (1 / (1 + s) * lam3)
        = Real.log (a / b))
      ∧ (‖nagaoNielsenComplexActionWeight S_R (ℏ * (ρ * t)) ℏ‖ = Real.exp (-(ρ * t))) :=
  ⟨lta_time_is_minkowski_proper_time hγ hc hγ0 ht,
    mpemba_local_gravity_blind a b s hs hne,
    contact_damping_is_nagaoNielsen_modulus S_R ρ t ℏ hℏ⟩

/-! ## §12. The quantification method: one holonomy per convention -/

/-- **[The convention is measured by its holonomy — the quantification method]** — each locally-
unobservable convention of §11 is read off a **closed-loop or differential integral** of the removable
offset, and every such integral is an exact identity in an *observable* right-hand side.  This is the
method to quantify what §11 says cannot be seen locally:

* **(i) Rotation — the synchronization holonomy.**  The Sagnac delay is twice the loop integral
  `∮(v/c²)dl = 2Aω/c²` (`sagnac_delay_first_order_twice_holonomy`); the rotation is recovered as
  `ω = c²H/(2πr²)` (`holonomy_reads_rotation`).  Read the convention off the ring.
* **(ii) Gravity — the differential redshift.**  Two stations at heights `h₁, h₂` timed by one clock
  return the potential difference exactly, `g(h₂−h₁)/c² = (t₁/t₂ − 1)(1 + gh₁/c²)`
  (`mpemba_differential_gravimeter`): the vertical loop reads the potential a single station cannot.
* **(iii) Contour — the crossing calibration.**  The imaginary-action rate is read from the crossing,
  `(λ₂−λ₃)t* = log(a/b)` (`mpemba_crossing_self_calibrates`): the Nagao–Nielsen modulus `e^{−ρt}` is
  quantified by the clock-free calibration.

Three conventions, three loop/differential observables, one method: integrate the removable offset over
the loop the convention lives on. -/
theorem convention_holonomy_quantifier
    (ω r c : ℝ)
    (g h₁ h₂ tstar t₁ t₂ : ℝ) (hd1 : 1 + g * h₁ / c ^ 2 ≠ 0) (hd2 : 1 + g * h₂ / c ^ 2 ≠ 0)
    (hts : tstar ≠ 0) (ht₁ : t₁ = tstar / (1 + g * h₁ / c ^ 2))
    (ht₂ : t₂ = tstar / (1 + g * h₂ / c ^ 2))
    (a b : ℝ) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (4 * (Real.pi * r ^ 2) * ω / c ^ 2 = 2 * ringSyncHolonomy ω r c)
      ∧ (g * (h₂ - h₁) / c ^ 2 = (t₁ / t₂ - 1) * (1 + g * h₁ / c ^ 2))
      ∧ ((lam2 - lam3) * mpembaCrossingTime a b lam2 lam3 = Real.log (a / b)) :=
  ⟨sagnac_delay_first_order_twice_holonomy ω r c,
    (mpemba_differential_gravimeter g h₁ h₂ c tstar t₁ t₂ hd1 hd2 hts ht₁ ht₂).2,
    mpemba_crossing_self_calibrates a b hne⟩

/-! ## §13. The differential channel: common-mode rejection as the arc's signal model

Every recovery in this arc is a two-input difference in which the shared part cancels — the same
structure a USB / LVDS / RS-485 pair uses to carry data as `V+ − V−` and reject common-mode noise.  The
convention that §11 shows is locally unobservable is exactly the **common-mode**: a differential channel
rejects it, and only the difference is signal.  This section makes that structure a first-class object and
recovers the Sagnac delay, the self-calibration, and the differential gravimeter as instances. -/

/-- **[the additive differential channel]** — output `y = x₁ − x₂` (the USB `D+ − D−`). -/
def differentialChannel (x₁ x₂ : ℝ) : ℝ := x₁ - x₂

/-- **[common-mode rejection]** — a shared offset `m` added to both inputs is rejected exactly:
`D(x₁+m, x₂+m) = D(x₁, x₂)`.  The common-mode (drift, coupled noise, an absolute reference) never reaches
the output. -/
theorem differential_common_mode_rejection (x₁ x₂ m : ℝ) :
    differentialChannel (x₁ + m) (x₂ + m) = differentialChannel x₁ x₂ := by
  unfold differentialChannel
  ring

/-- **[no signal without a difference]** — pure common-mode gives zero: `D(x, x) = 0`.  The raw input is
not the data; the difference is. -/
theorem differential_zero_on_common (x : ℝ) : differentialChannel x x = 0 := by
  unfold differentialChannel
  ring

/-- **[CMRR / mismatch leakage]** — if the two channels have mismatched gains `g₁ ≠ g₂`, the common-mode
leaks into the output proportionally to the mismatch: `D(g₁·x, g₂·x) = (g₁−g₂)·x`.  A perfect subtraction
needs matched channels; the common-mode rejection ratio is finite exactly when `g₁ ≠ g₂`.  (In the
gravimeter this is the "equal proper physics" hypothesis; break it and the potential reappears as a
systematic.) -/
theorem differential_mismatch_leakage (g₁ g₂ x : ℝ) :
    differentialChannel (g₁ * x) (g₂ * x) = (g₁ - g₂) * x := by
  unfold differentialChannel
  ring

/-- **[matched channels reject perfectly]** — with `g₁ = g₂ = g` the common-mode leakage is zero
(infinite CMRR). -/
theorem matched_channels_reject (g x : ℝ) : differentialChannel (g * x) (g * x) = 0 :=
  differential_zero_on_common (g * x)

/-- **[the log-differential channel]** — `y = log(a/b)`: the multiplicative common-mode is a shared scale
factor (a gain, an absolute anchor), rejected as `log(ka/kb) = log(a/b)`. -/
def logDifferentialChannel (a b : ℝ) : ℝ := Real.log (a / b)

/-- **[multiplicative common-mode rejection]** — a shared scale `k > 0` on both inputs cancels: the
self-calibration's scale-invariance is common-mode rejection in the log domain. -/
theorem log_differential_scale_rejection {a b k : ℝ} (hk : k ≠ 0) :
    logDifferentialChannel (k * a) (k * b) = logDifferentialChannel a b := by
  unfold logDifferentialChannel
  rw [mul_div_mul_left a b hk]

/-- **[instance: the Sagnac delay is a differential channel]** — `ΔT = D(2πr/(c−v), 2πr/(c+v))`, the two
counter-propagating flight times differenced; the common-mode round-trip time is rejected. -/
theorem sagnac_is_differential_channel (c v r : ℝ) :
    sagnacTimeDelay c v r
      = differentialChannel (2 * Real.pi * r / (c - v)) (2 * Real.pi * r / (c + v)) := rfl

/-- **[instance: the self-calibration is a log-differential channel]** — the clock-free calibration
`(λ₂−λ₃)t* = log(a/b) = D_log(a, b)`; the absolute anchor `ν₀` is the multiplicative common-mode,
rejected. -/
theorem self_calibration_is_log_differential (a b : ℝ) {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) :
    (lam2 - lam3) * mpembaCrossingTime a b lam2 lam3 = logDifferentialChannel a b := by
  rw [mpemba_crossing_self_calibrates a b hne]
  rfl

/-- **[instance: the differential gravimeter is a differential channel]** — the recovered potential
difference `g(h₂−h₁)/c² = D(gh₂/c², gh₁/c²)`; the proper crossing time is the common-mode. -/
theorem gravimeter_is_differential_channel (g h₁ h₂ c : ℝ) :
    g * (h₂ - h₁) / c ^ 2 = differentialChannel (g * h₂ / c ^ 2) (g * h₁ / c ^ 2) := by
  unfold differentialChannel
  ring

/-- **[the differential signal model]** — the arc's observables are differential-channel readings: **(i)**
common-mode rejection (additive); **(ii)** scale-invariance = common-mode rejection (multiplicative,
`self_calibration_is_log_differential`); **(iii)** the Sagnac delay is such a channel; **(iv)** mismatched
channels leak the common-mode (finite CMRR).  The convention §11 cannot see locally is the common-mode
this model rejects — and the difference, as in every serial protocol, is the data. -/
theorem differential_signal_model_synthesis
    (x₁ x₂ m : ℝ) {k : ℝ} (hk : k ≠ 0) (a b : ℝ) (c v r : ℝ) (g₁ g₂ xcm : ℝ) :
    (differentialChannel (x₁ + m) (x₂ + m) = differentialChannel x₁ x₂)
      ∧ (logDifferentialChannel (k * a) (k * b) = logDifferentialChannel a b)
      ∧ (sagnacTimeDelay c v r
          = differentialChannel (2 * Real.pi * r / (c - v)) (2 * Real.pi * r / (c + v)))
      ∧ (differentialChannel (g₁ * xcm) (g₂ * xcm) = (g₁ - g₂) * xcm) :=
  ⟨differential_common_mode_rejection x₁ x₂ m, log_differential_scale_rejection hk,
    sagnac_is_differential_channel c v r, differential_mismatch_leakage g₁ g₂ xcm⟩

/-! ## §14. Delta encoding: the difference is the data, in time

The differential channel (§13) differences two channels *at once*; its temporal twin differences a channel
*across time* — delta encoding, as USB packet framing, delta-sigma modulators, incremental encoders, and
video codecs transmit `xₙ − xₙ₋₁` rather than the raw sample.  The two share the same content: the shared
part (a spatial common-mode / a temporal reference) is rejected, and the difference is the signal.  Delta
encoding also closes the strapdown-gyroscope loop: attitude is reconstructed by *summing* rate increments,
and its random walk is the accumulated per-delta error. -/

/-- **[the delta-encoding channel]** — the `n`-th temporal increment `dₙ = xₙ₊₁ − xₙ`. -/
def deltaEncode (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - x n

/-- **[telescoping reconstruction]** — the deltas sum to the absolute change: `Σ_{i<n} dᵢ = xₙ − x₀`.
The raw stream is recovered from the deltas up to the initial reference. -/
theorem delta_telescoping_reconstruction (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, deltaEncode x i) = x n - x 0 := by
  unfold deltaEncode
  exact Finset.sum_range_sub x n

/-- **[the reference is rejected]** — a shared temporal reference (an initial offset `c` on the whole
stream) leaves every delta unchanged: `Δ(x + c) = Δx`.  The temporal common-mode is rejected exactly, as
the spatial one is in `differential_common_mode_rejection`. -/
theorem delta_reference_blind (x : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    deltaEncode (fun i => x i + c) n = deltaEncode x n := by
  unfold deltaEncode
  ring

/-- **[no data without change]** — a constant stream has zero deltas: nothing is transmitted when nothing
moves (the temporal twin of `differential_zero_on_common`). -/
theorem delta_zero_on_constant (v : ℝ) (n : ℕ) : deltaEncode (fun _ => v) n = 0 := by
  unfold deltaEncode
  ring

/-- **[absolute value needs one reference]** — `xₙ = x₀ + Σ_{i<n} dᵢ`: the deltas alone give only the
change; recovering the absolute stream needs one reference sample — a keyframe (video), a start-of-frame
(USB), an initial attitude (strapdown). -/
theorem delta_needs_reference (x : ℕ → ℝ) (n : ℕ) :
    x n = x 0 + ∑ i ∈ Finset.range n, deltaEncode x i := by
  rw [delta_telescoping_reconstruction]
  ring

/-- **[error accumulates as a random walk]** — a per-delta error `εᵢ` accumulates *additively* in the
reconstruction: `Σ(dᵢ + εᵢ) = (xₙ − x₀) + Σ εᵢ`.  This is exactly the strapdown gyroscope's attitude
drift — the reconstructed orientation from noisy rate-deltas departs from truth by the summed error, the
`√n` random walk observed in `sagnac_triad_reconstructs_magnitude`'s integration. -/
theorem delta_error_accumulates (x eps : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (deltaEncode x i + eps i))
      = (x n - x 0) + ∑ i ∈ Finset.range n, eps i := by
  rw [Finset.sum_add_distrib, delta_telescoping_reconstruction]

/-- **[delta-encoding synthesis]** — the temporal delta and the spatial differential are one principle:
**(i)** the temporal reference is rejected; **(ii)** the deltas telescope to the absolute change;
**(iii)** the spatial common-mode is rejected (the §13 twin).  "The difference is the data" holds across
channels and across time. -/
theorem delta_encoding_synthesis (x : ℕ → ℝ) (c : ℝ) (n : ℕ) (x₁ x₂ m : ℝ) :
    (deltaEncode (fun i => x i + c) n = deltaEncode x n)
      ∧ ((∑ i ∈ Finset.range n, deltaEncode x i) = x n - x 0)
      ∧ (differentialChannel (x₁ + m) (x₂ + m) = differentialChannel x₁ x₂) :=
  ⟨delta_reference_blind x c n, delta_telescoping_reconstruction x n,
    differential_common_mode_rejection x₁ x₂ m⟩

/-! ## §15. The macroscopic Mpemba effect: Newton's law of cooling vs the Herglotz crossing -/

/-- **[Newton's law of cooling cannot cross]** — a *single* dissipative mode (Newton's `dT/dt = −k(T−T_env)`,
one relaxation rate `k`) preserves the initial ordering for all time: `b·e^{−kt} < a·e^{−kt}` whenever
`b < a`.  Even *with* dissipation, one rate means the hotter sample stays hotter — no Mpemba.  This is the
Newtonian baseline: the crossing needs a *second* mode, not merely dissipation. -/
theorem newton_single_mode_no_crossing {a b : ℝ} (hab : b < a) (k t : ℝ) :
    b * Real.exp (-k * t) < a * Real.exp (-k * t) :=
  mul_lt_mul_of_pos_right hab (Real.exp_pos _)

/-- **[macroscopic Mpemba vs Newton — the full contrast]** — for a two-station cooling experiment:
**(i)** Newton's single-rate law never crosses (`b·e^{−kt} < a·e^{−kt}`, ordering frozen);
**(ii)** two Herglotz contact frictions `ρ₂ < ρ₃` do cross, the hotter (higher-friction) state overtaking
after `t* = log(a/b)/(ρ₃−ρ₂)`; **(iii)** the crossing self-calibrates at `log(a/b)` (clock-free);
**(iv)** at the crossing the relaxation has priced imaginary action `S_I = ℏ·ρ₃·t`, the Nagao–Nielsen
modulus `e^{−ρ₃t}` (the Misra age of the dissipative flow).  Newton predicts no Mpemba window; the Herglotz
replacement predicts the crossing — this is what a macroscopic measurement discriminates. -/
theorem macroscopic_mpemba_vs_newton {a b ρ₂ ρ₃ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b < a) (hρ : ρ₂ < ρ₃) {t : ℝ} (ht : mpembaCrossingTime a b (-ρ₂) (-ρ₃) < t)
    {lam2 lam3 : ℝ} (hne : lam2 ≠ lam3) (k : ℝ) (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    (b * Real.exp (-k * t) < a * Real.exp (-k * t))
      ∧ (a * Real.exp (-ρ₃ * t) < b * Real.exp (-ρ₂ * t))
      ∧ ((lam2 - lam3) * mpembaCrossingTime a b lam2 lam3 = Real.log (a / b))
      ∧ (‖nagaoNielsenComplexActionWeight S_R (ℏ * (ρ₃ * t)) ℏ‖ = Real.exp (-(ρ₃ * t))) :=
  ⟨newton_single_mode_no_crossing hab k t, herglotz_friction_crossing ha hb hρ ht,
    mpemba_crossing_self_calibrates a b hne, contact_damping_is_nagaoNielsen_modulus S_R ρ₃ t ℏ hℏ⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.newton_reversible_ordering_frozen where
  formalizes @ "claim:conservative-newton-flow-freezes-the-distance-ordering-for-all-time-so-the-mpemba-crossing-is-impossible-in-the-reversible-sector",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.reversible_generator_flow_unitary",
  caveat @ "epistemic:the-exact-finite-face-of-energy-conservation-norm-preserving-spectral-flow"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_selects_herglotz where
  formalizes @ "claim:the-mpemba-effect-cannot-be-modeled-by-conservative-newton-equations-and-is-modeled-exactly-by-the-herglotz-contact-replacement-with-lindblad-quantum-form",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  requires @ "claim:the-navier-stokes-dissipative-lagrangian-is-realized-exactly-by-a-lindblad-open-quantum-contact-slice-at-calibrated-jump-rate",
  supported_by @ "lean:ClassicalMechanics.dampedOscillatorContactSlice",
  caveat @ "epistemic:the-damped-oscillator-euler-lagrange-derivation-from-the-herglotz-principle-is-the-cited-classical-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.contact_damping_is_nagaoNielsen_modulus where
  formalizes @ "claim:the-herglotz-contact-friction-accumulates-nagao-nielsen-imaginary-action-at-rate-hbar-rho",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  caveat @ "epistemic:modulus-level-identity-for-any-real-action-contour-phase-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.misra_age_prices_imaginary_action where
  formalizes @ "claim:the-misra-internal-time-eigenvalue-is-what-the-herglotz-friction-prices-into-imaginary-action",
  requires @ "claim:the-herglotz-contact-friction-accumulates-nagao-nielsen-imaginary-action-at-rate-hbar-rho",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy.ageOperator_reads_evolution_time",
  caveat @ "epistemic:age-read-on-the-trivial-liouville-mode-the-operator-misra-prigogine-theory-is-the-cited-continuum-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_efolds_lorentz_invariant where
  formalizes @ "claim:the-accumulated-imaginary-action-of-the-contact-friction-is-a-lorentz-scalar-rates-redshift-crossings-dilate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass.lorentzFactor",
  caveat @ "epistemic:boost-acts-on-rates-as-inverse-cosh-eta-time-dilation-of-a-comoving-damping"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_contact_clocks_synthesis where
  formalizes @ "claim:the-bath-fourth-role-is-the-variational-friction-welded-to-misra-age-nagao-nielsen-contours-and-rapidity-dilation",
  requires @ "claim:the-laboratory-enters-the-dynamics-as-the-bath-in-three-roles-clock-rate-record-content-and-relaxation-arrow",
  requires @ "claim:the-mpemba-effect-cannot-be-modeled-by-conservative-newton-equations-and-is-modeled-exactly-by-the-herglotz-contact-replacement-with-lindblad-quantum-form",
  requires @ "claim:the-misra-internal-time-eigenvalue-is-what-the-herglotz-friction-prices-into-imaginary-action",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.HerglotzContactCalibration.lindbladContactSlice",
  caveat @ "epistemic:the-covariant-contact-geometry-is-the-cited-continuum-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates where
  formalizes @ "claim:the-mpemba-crossing-occurs-at-differential-efold-count-log-a-over-b-a-clock-free-self-calibration",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  caveat @ "epistemic:amplitudes-fix-the-calibration-point-from-preparation-spectroscopy-never-from-the-timing-data"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_rapidity_invariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
  formalizes @ "claim:the-crossing-calibration-point-is-the-same-pure-number-in-every-boosted-frame-residual-seconds-measure-rapidity",
  requires @ "claim:the-mpemba-crossing-occurs-at-differential-efold-count-log-a-over-b-a-clock-free-self-calibration",
  requires @ "claim:the-accumulated-imaginary-action-of-the-contact-friction-is-a-lorentz-scalar-rates-redshift-crossings-dilate",
  caveat @ "epistemic:the-misra-age-supplies-the-operational-duration-reading-which-the-friction-prices"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.misra_age_is_group_coordinate where
  formalizes @ "claim:the-misra-age-is-the-additive-group-coordinate-of-the-liouville-flow-matching-rapidity-additivity",
  requires @ "claim:the-misra-internal-time-eigenvalue-is-what-the-herglotz-friction-prices-into-imaginary-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz.liouvilleEvolve_add",
  caveat @ "epistemic:the-same-additive-structure-as-complexboost-group-zil-linked-across-the-import-cycle"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_scaling_invariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
  formalizes @ "claim:the-crossing-calibration-point-is-invariant-under-the-heating-rate-scaling-action",
  requires @ "claim:the-mpemba-crossing-occurs-at-differential-efold-count-log-a-over-b-a-clock-free-self-calibration",
  caveat @ "epistemic:with-the-rapidity-version-the-invariance-covers-the-full-group-action"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.entropic_time_group_action_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.contact_damping_is_nagaoNielsen_modulus",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_rapidity_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_scaling_invariant",
  formalizes @ "claim:entropic-time-is-a-group-action-with-misra-coordinate-herglotz-pricing-and-log-amplitude-invariant",
  requires @ "claim:heating-acts-on-the-second-quantized-vacuum-as-a-hyperbolic-rotation-with-cosh-two-theta-equals-one-plus-twice-the-occupation",
  requires @ "claim:the-misra-age-is-the-additive-group-coordinate-of-the-liouville-flow-matching-rapidity-additivity",
  requires @ "claim:the-crossing-calibration-point-is-invariant-under-the-heating-rate-scaling-action",
  caveat @ "epistemic:one-so-1-1-orbit-heating-and-boosting-compose-additively-in-rapidity"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_local_gravity_blind where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_scaling_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks.crossing_ticks_laboratory_relative",
  formalizes @ "claim:a-single-station-mpemba-measurement-cannot-detect-gravity-the-equivalence-principle-as-scaling-invariance-of-the-calibration-point",
  requires @ "claim:the-crossing-calibration-point-is-invariant-under-the-heating-rate-scaling-action",
  caveat @ "epistemic:redshift-as-common-rate-scaling-is-the-weak-field-clock-reading-of-the-equivalence-principle"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_gravimetry_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_local_gravity_blind",
  formalizes @ "claim:a-planets-effective-gravity-is-measurable-from-two-mpemba-stations-with-a-common-clock-while-locally-blind",
  requires @ "claim:a-single-station-mpemba-measurement-cannot-detect-gravity-the-equivalence-principle-as-scaling-invariance-of-the-calibration-point",
  requires @ "claim:the-mpemba-crossing-occurs-at-differential-efold-count-log-a-over-b-a-clock-free-self-calibration",
  requires @ "claim:entropic-tick-counts-of-the-same-event-are-laboratory-relative-in-the-exact-ratio-of-proper-accelerations",
  caveat @ "epistemic:equal-proper-physics-at-both-stations-is-the-stated-hypothesis-feasibility-is-optical-clock-territory"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.entropic_gravimeter_synthesis where
  formalizes @ "claim:gravity-is-computed-from-an-entropic-time-observable-the-dilation-decoherence-rate-with-nagao-nielsen-visibility-and-a-mpemba-crossing-version",
  requires @ "claim:time-dilation-decoherence-rate-is-linear-in-gravity-and-inverts-exactly-to-a-percent-level-entropic-gravimeter",
  requires @ "claim:the-herglotz-contact-friction-accumulates-nagao-nielsen-imaginary-action-at-rate-hbar-rho",
  supported_by @ "paper:pikovski-zych-costa-brukner-2015-universal-decoherence-due-to-gravitational-time-dilation",
  caveat @ "epistemic:percent-level-not-competitive-with-atom-interferometers-but-genuinely-entropic-sector-visibility-not-phase"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.gaussian_crossing_self_calibrates where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_scaling_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
  formalizes @ "claim:the-gaussian-dilation-decoherence-crossing-self-calibrates-at-squared-time-efold-count-log-a-over-b",
  requires @ "claim:the-mpemba-crossing-occurs-at-differential-efold-count-log-a-over-b-a-clock-free-self-calibration",
  requires @ "claim:the-mpemba-crossing-transfers-exactly-to-gaussian-envelopes-under-squared-time-the-dilation-decoherence-shape",
  caveat @ "epistemic:squared-time-is-the-natural-flow-parameter-of-gaussian-decoherence"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.rainbow_gravimeter where
  formalizes @ "claim:a-planets-effective-gravity-is-computed-from-a-rainbows-drop-flattening-scale-via-the-capillary-length-inversion",
  requires @ "claim:a-planets-effective-gravity-is-measurable-from-two-mpemba-stations-with-a-common-clock-while-locally-blind",
  caveat @ "epistemic:the-flattening-to-angular-structure-map-is-the-cited-drop-shape-optics-the-inversion-g-equals-sigma-over-rho-lc-squared-is-exact"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.capillary_gravity_min_speed where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:capillary-gravity-dispersion-has-minimum-phase-speed-c-fourth-equals-4-g-sigma-over-rho-an-optical-gravimeter-on-any-pond",
  requires @ "claim:a-planets-effective-gravity-is-computed-from-a-rainbows-drop-flattening-scale-via-the-capillary-length-inversion",
  caveat @ "epistemic:deep-water-linear-dispersion-the-am-gm-minimum-is-exact"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.moire_dispersion_gravimeter where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  formalizes @ "claim:moire-read-dispersion-difference-quotients-compute-effective-gravity-exactly-on-the-capillary-gravity-branch",
  requires @ "claim:the-moire-envelope-is-the-modulus-of-a-two-phase-superposition-and-depends-only-on-the-wavenumber-difference",
  requires @ "claim:capillary-gravity-dispersion-has-minimum-phase-speed-c-fourth-equals-4-g-sigma-over-rho-an-optical-gravimeter-on-any-pond",
  caveat @ "epistemic:linear-deep-water-dispersion-the-difference-quotient-identity-is-exact"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.vapor_velocity_gravity_scaling where
  formalizes @ "claim:the-classical-gravity-influence-boundary-of-condensing-films-scales-as-sqrt-g-between-planets",
  supported_by @ "paper:mudawar-darges-hasan-nahra-balasubramaniam-mackey-ijhmt-254-2026-iss-flow-condensation",
  caveat @ "epistemic:the-j-g-group-and-its-unity-threshold-are-the-cited-two-phase-flow-criteria"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.shear_blindness_boundary where
  formalizes @ "claim:above-the-shear-boundary-the-films-proper-relaxation-physics-is-gravity-blind-the-classical-validity-condition-for-equal-proper-physics",
  requires @ "claim:a-single-station-mpemba-measurement-cannot-detect-gravity-the-equivalence-principle-as-scaling-invariance-of-the-calibration-point",
  supported_by @ "paper:mudawar-darges-hasan-nahra-balasubramaniam-mackey-ijhmt-254-2026-iss-flow-condensation",
  caveat @ "epistemic:flight-anchor-g-free-correlations-transfer-at-7-percent-g-dependent-forms-fail-at-up-to-100-percent"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.shear_regime_classification where
  supported_by @ "lean:HermitianMat.sqrt_pos",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-vapor-velocity-group-classifies-gravity-influenced-below-one-and-gravity-blind-above-one-two-sided",
  requires @ "claim:above-the-shear-boundary-the-films-proper-relaxation-physics-is-gravity-blind-the-classical-validity-condition-for-equal-proper-physics",
  caveat @ "epistemic:regime-labels-are-the-flight-tested-two-phase-criteria"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.gated_gravimetry_synthesis where
  formalizes @ "claim:when-the-classical-channel-is-off-gravity-enters-only-as-common-scaling-invisible-locally-and-recoverable-differentially",
  requires @ "claim:the-vapor-velocity-group-classifies-gravity-influenced-below-one-and-gravity-blind-above-one-two-sided",
  requires @ "claim:a-single-station-mpemba-measurement-cannot-detect-gravity-the-equivalence-principle-as-scaling-invariance-of-the-calibration-point",
  requires @ "claim:a-planets-effective-gravity-is-measurable-from-two-mpemba-stations-with-a-common-clock-while-locally-blind",
  supported_by @ "paper:mudawar-darges-hasan-nahra-balasubramaniam-mackey-ijhmt-254-2026-iss-flow-condensation",
  caveat @ "epistemic:the-classical-channel-off-premise-is-the-flight-tested-j-g-criterion-not-a-derived-fact"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.simultaneity_potential_contour_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.contact_damping_is_nagaoNielsen_modulus",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.lta_time_is_minkowski_proper_time",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_local_gravity_blind",
  formalizes @ "claim:the-simultaneity-dichotomy-the-equivalence-principle-and-the-nagao-nielsen-contour-are-three-faces-of-a-locally-unobservable-global-convention-over-the-minkowski-invariant",
  requires @ "claim:the-absolute-simultaneity-time-t-over-gamma-is-the-minkowski-proper-time-of-the-co-moving-clock",
  requires @ "claim:the-mpemba-crossing-calibration-is-scaling-invariant-so-a-single-station-is-blind-to-the-gravitational-potential-the-equivalence-principle",
  requires @ "claim:the-contact-friction-damping-envelope-is-the-nagao-nielsen-complex-action-modulus-e-to-the-minus-rho-t"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.convention_holonomy_quantifier where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_delay_first_order_twice_holonomy",
  formalizes @ "claim:each-locally-unobservable-convention-is-quantified-by-a-closed-loop-or-differential-integral-of-the-removable-offset-rotation-by-the-sagnac-holonomy-gravity-by-the-differential-redshift-and-the-contour-by-the-crossing-calibration",
  requires @ "claim:the-sagnac-delay-is-twice-the-synchronization-holonomy-the-closed-loop-integral-of-the-locally-removable-offset",
  requires @ "claim:the-simultaneity-dichotomy-the-equivalence-principle-and-the-nagao-nielsen-contour-are-three-faces-of-a-locally-unobservable-global-convention-over-the-minkowski-invariant"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_common_mode_rejection where
  formalizes @ "claim:a-differential-channel-rejects-a-shared-common-mode-offset-exactly-carrying-only-the-difference-as-data-like-a-usb-differential-pair"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_mismatch_leakage where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:mismatched-channel-gains-leak-the-common-mode-into-the-difference-proportionally-to-the-mismatch-a-finite-common-mode-rejection-ratio",
  requires @ "claim:a-differential-channel-rejects-a-shared-common-mode-offset-exactly-carrying-only-the-difference-as-data-like-a-usb-differential-pair"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.sagnac_is_differential_channel where
  formalizes @ "claim:the-sagnac-delay-is-a-differential-channel-on-the-two-counter-propagating-flight-times-rejecting-the-common-mode-round-trip-time",
  requires @ "claim:a-differential-channel-rejects-a-shared-common-mode-offset-exactly-carrying-only-the-difference-as-data-like-a-usb-differential-pair",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_wavevector_difference"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_signal_model_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_common_mode_rejection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_mismatch_leakage",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.sagnac_is_differential_channel",
  formalizes @ "claim:the-arc-observables-are-differential-channel-readings-that-reject-the-locally-unobservable-convention-as-common-mode-and-carry-the-difference-as-data",
  requires @ "claim:the-sagnac-delay-is-a-differential-channel-on-the-two-counter-propagating-flight-times-rejecting-the-common-mode-round-trip-time",
  requires @ "claim:the-simultaneity-dichotomy-the-equivalence-principle-and-the-nagao-nielsen-contour-are-three-faces-of-a-locally-unobservable-global-convention-over-the-minkowski-invariant"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.delta_telescoping_reconstruction where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_common_mode_rejection",
  formalizes @ "claim:temporal-delta-encoding-telescopes-to-the-absolute-change-x-n-minus-x-zero-recovering-the-stream-up-to-the-initial-reference",
  requires @ "claim:a-differential-channel-rejects-a-shared-common-mode-offset-exactly-carrying-only-the-difference-as-data-like-a-usb-differential-pair"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.delta_error_accumulates where
  formalizes @ "claim:per-delta-errors-accumulate-additively-in-the-delta-encoding-reconstruction-the-strapdown-gyroscope-attitude-random-walk",
  requires @ "claim:temporal-delta-encoding-telescopes-to-the-absolute-change-x-n-minus-x-zero-recovering-the-stream-up-to-the-initial-reference",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.sagnac_triad_reconstructs_magnitude"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.delta_encoding_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.delta_telescoping_reconstruction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.differential_common_mode_rejection",
  formalizes @ "claim:temporal-delta-encoding-and-spatial-differential-signaling-are-one-principle-the-difference-is-the-data-across-channels-and-across-time",
  requires @ "claim:temporal-delta-encoding-telescopes-to-the-absolute-change-x-n-minus-x-zero-recovering-the-stream-up-to-the-initial-reference",
  requires @ "claim:the-arc-observables-are-differential-channel-readings-that-reject-the-locally-unobservable-convention-as-common-mode-and-carry-the-difference-as-data"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.newton_single_mode_no_crossing where
  supported_by @ "lean:HermitianMat.exp_pos",
  formalizes @ "claim:newtons-law-of-cooling-a-single-dissipative-relaxation-rate-preserves-ordering-for-all-time-so-it-cannot-produce-the-mpemba-crossing",
  requires @ "claim:the-mpemba-effect-cannot-be-modeled-by-newtons-conservative-equations-and-is-modeled-by-the-herglotz-contact-friction-replacement"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.macroscopic_mpemba_vs_newton where
  formalizes @ "claim:a-macroscopic-cooling-measurement-discriminates-newton-no-crossing-from-the-herglotz-two-friction-mpemba-crossing-self-calibrated-and-priced-as-misra-age-imaginary-action",
  requires @ "claim:newtons-law-of-cooling-a-single-dissipative-relaxation-rate-preserves-ordering-for-all-time-so-it-cannot-produce-the-mpemba-crossing",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.entropic_matsubara_ladder"

/- ZIL-END -/
