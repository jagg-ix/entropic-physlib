/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
meta import Zil

/-!
# The trapped-ion inverse-Mpemba spectrum: rates, ellipse, cancellation point, threshold

Shapira–Shapira–Markov–Teza–Akerman–Raz–Ozeri (arXiv:2401.05830) demonstrate the inverse quantum Mpemba
effect on a single ⁸⁸Sr⁺ Zeeman qubit: coherent drive `Ω σ_x` plus decay/dephasing branching `α` at
decoherence rate `γ`.  Numerical reconstruction of their GKSL model (script `shapira_predict2.py`)
reproduced their Eq. 4 spectrum to six decimals, their steady-state locus exactly, the strong-ME
cancellation point (`0.0762` vs their `≈ 0.07`), and the Fig-5 crossing (two-mode `t* = 0.677 γ_f⁻¹` vs
measured `≈ 0.6 γ_f⁻¹`).  This module formalizes the *exact algebraic core* behind those numbers:

* **§1 — the relaxation rates** (`slowRate`, `fastRate` = their Eq. 4,
  `λ± = −γ_f(α + ½ ± √((α−½)² − 1/γ_f′²))`): `rate_sum` gives the trace `λ₊ + λ₋ = −γ_f(2α+1)` with no
  condition; `rate_product` gives the determinant `λ₊λ₋ = γ_f²(2α + 1/γ_f′²)` on the real-spectrum domain;
  `rates_split_iff` — a slow/fast **gap exists iff the discriminant is positive**, the existence condition
  for the Mpemba effect in this system.
* **§2 — the steady-state ellipse** (`steady_state_ellipse`): the measured locus
  `y(u) = 2αu/(1+2αu²)`, `z(u)+½ = (1−2αu²)/(2(1+2αu²))` satisfies
  `(y/√(α/2))² + ((z+½)/½)² = 1` **exactly** — the identity `8αu² + (1−2αu²)² = (1+2αu²)²`.  (Their printed
  semiaxis "√α/2" is `√(α/2)`; this is the proof.)
* **§3 — the strong-ME cancellation point** (`strongMeCancellation`, their
  `γ′_{i,SME} = γ_f′((α−½) − √((α−½)² − γ_f′⁻²))`): `strongMeCancellation_pos` — it is strictly positive on
  the α > ½ real-spectrum domain, so a *physical* initial temperature with vanishing slow-mode coefficient
  exists: the strong (exponentially faster) inverse-ME is realizable.
* **§4 — the coherence threshold** (`strong_me_threshold`): the discriminant is positive **iff**
  `α > ½ + 1/γ_f′` — the correct strong-ME coherence threshold.  At `γ_f′ = 15` this is `α > 0.567`: the
  blue data set (`α = 0.94 ± 0.07`) is above it, and the paper's `α = 1/3` comparison curve is below `½`,
  hence below *every* threshold — `1/3` is a sub-threshold example, not the threshold (this corrects the
  `alpha_strong_me_threshold = 1/3` mislabel in the catept-main PaperData sibling).
* **§5 — the crossing** (`trapped_ion_crossing`): `mpemba_crossing` at the Eq. 4 rates — on the split
  domain, the fast-mode state overtakes after the explicit `t*`; with the Fig-5 amplitudes this is the
  `0.677 γ_f⁻¹` prediction against the measured `≈ 0.6 γ_f⁻¹`.

`inverse_mpemba_spectrum_synthesis` bundles trace, determinant, gap-iff, cancellation positivity, ellipse,
and crossing.  Honest scope: the Bloch-sector reduction of the GKSL generator to these two rates and the
locus parametrization are the paper's (numerically verified) results — this module formalizes their exact
algebra, positivity, and threshold structure, not the operator-level derivation; the convention `γ` =
coherence-decay rate (Lindblad channel rates `2αγ`, `2(1−α)γ`) is recorded from the reconstruction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing

/-! ## §1. The relaxation rates (Eq. 4) -/

/-- Spectral discriminant `(α − ½)² − 1/γ_f′²` of the driven-dissipative qubit's y–z Bloch sector. -/
def spectralDiscriminant (α gf' : ℝ) : ℝ := (α - 1 / 2) ^ 2 - 1 / gf' ^ 2

/-- Slow relaxation rate `λ₋ = −γ_f(α + ½ − √disc)` (Eq. 4 of Shapira et al.). -/
def slowRate (γf α gf' : ℝ) : ℝ :=
  -(γf * (α + 1 / 2 - Real.sqrt (spectralDiscriminant α gf')))

/-- Fast relaxation rate `λ₊ = −γ_f(α + ½ + √disc)` (Eq. 4 of Shapira et al.). -/
def fastRate (γf α gf' : ℝ) : ℝ :=
  -(γf * (α + 1 / 2 + Real.sqrt (spectralDiscriminant α gf')))

/-- **[Rate trace]** — `λ₋ + λ₊ = −γ_f(2α + 1)`: the total damping is branching-weighted decoherence,
independent of the drive and of the discriminant's sign. -/
theorem rate_sum (γf α gf' : ℝ) :
    slowRate γf α gf' + fastRate γf α gf' = -(γf * (2 * α + 1)) := by
  unfold slowRate fastRate
  ring

/-- **[Rate determinant]** — on the real-spectrum domain, `λ₋·λ₊ = γ_f²(2α + 1/γ_f′²)`: the square of the
geometric-mean relaxation rate, drive and dissipation combined. -/
theorem rate_product {α gf' : ℝ} (γf : ℝ) (hd : 0 ≤ spectralDiscriminant α gf') :
    slowRate γf α gf' * fastRate γf α gf' = γf ^ 2 * (2 * α + 1 / gf' ^ 2) := by
  have hs : Real.sqrt (spectralDiscriminant α gf') ^ 2 = spectralDiscriminant α gf' :=
    Real.sq_sqrt hd
  unfold slowRate fastRate
  unfold spectralDiscriminant at hs ⊢
  linear_combination (-(γf ^ 2)) * hs

/-- **[The Mpemba gap exists iff the discriminant is positive]** — `λ₊ < λ₋` (a strict slow/fast split,
the existence condition for the Mpemba effect in this system) iff `0 < disc`, given `γ_f > 0`. -/
theorem rates_split_iff {γf α gf' : ℝ} (hγ : 0 < γf) :
    fastRate γf α gf' < slowRate γf α gf' ↔ 0 < spectralDiscriminant α gf' := by
  unfold slowRate fastRate
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    rw [Real.sqrt_eq_zero_of_nonpos hle] at h
    simp at h
  · intro h
    have hs : 0 < Real.sqrt (spectralDiscriminant α gf') := Real.sqrt_pos.mpr h
    nlinarith

/-! ## §2. The steady-state ellipse -/

/-- **[The steady-state locus is exactly the ellipse]** — the measured locus `y = 2αu/(1+2αu²)`,
`z + ½ = (1−2αu²)/(2(1+2αu²))` satisfies `(y/√(α/2))²+((z+½)/½)² = 1`, i.e.
`(2αu/(1+2αu²))²·(2/α) + ((1−2αu²)/(1+2αu²))² = 1`: the identity `8αu² + (1−2αu²)² = (1+2αu²)²`.  The
printed semiaxis "√α/2" of the paper is `√(α/2)`. -/
theorem steady_state_ellipse {α : ℝ} (u : ℝ) (hα : 0 < α) :
    (2 * α * u / (1 + 2 * α * u ^ 2)) ^ 2 * (2 / α)
      + ((1 - 2 * α * u ^ 2) / (1 + 2 * α * u ^ 2)) ^ 2 = 1 := by
  have hden : (1 + 2 * α * u ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-! ## §3. The strong-ME cancellation point -/

/-- Initial temperature at which the slow-mode coefficient `a₋` vanishes:
`γ′_{i,SME} = γ_f′((α−½) − √disc)` (Shapira et al.). -/
def strongMeCancellation (α gf' : ℝ) : ℝ :=
  gf' * ((α - 1 / 2) - Real.sqrt (spectralDiscriminant α gf'))

/-- **[The cancellation point is physical]** — on the coherent real-spectrum domain (`α > ½`, `disc ≥ 0`,
`γ_f′ > 0`) the slow-mode-free initial temperature is strictly positive: the strong (exponentially faster)
inverse Mpemba effect is realizable at a real bath setting. -/
theorem strongMeCancellation_pos {α gf' : ℝ} (hg : 0 < gf') (hα : 1 / 2 < α)
    (hd : 0 ≤ spectralDiscriminant α gf') :
    0 < strongMeCancellation α gf' := by
  unfold strongMeCancellation
  have hlt : spectralDiscriminant α gf' < (α - 1 / 2) ^ 2 := by
    unfold spectralDiscriminant
    have hpos : 0 < 1 / gf' ^ 2 := by positivity
    linarith
  have h1 : Real.sqrt (spectralDiscriminant α gf') < α - 1 / 2 :=
    calc Real.sqrt (spectralDiscriminant α gf')
        < Real.sqrt ((α - 1 / 2) ^ 2) := Real.sqrt_lt_sqrt hd hlt
      _ = α - 1 / 2 := Real.sqrt_sq (by linarith)
  exact mul_pos hg (by linarith)

/-! ## §4. The coherence threshold -/

/-- **[The strong-ME coherence threshold is `α > ½ + 1/γ_f′`]** — for `α ≥ ½` and `γ_f′ > 0` the
discriminant is positive iff `α` exceeds `½ + 1/γ_f′`.  At `γ_f′ = 15` this is `α > 0.567`: the `α = 0.94`
data set qualifies, and `α = 1/3 < ½` is below every threshold — a sub-threshold comparison curve, not the
threshold itself. -/
theorem strong_me_threshold {α gf' : ℝ} (hα : 1 / 2 ≤ α) (hg : 0 < gf') :
    0 < spectralDiscriminant α gf' ↔ 1 / 2 + 1 / gf' < α := by
  unfold spectralDiscriminant
  have hinv : 0 < 1 / gf' := by positivity
  have hatom : 1 / gf' ^ 2 = (1 / gf') ^ 2 := by ring
  rw [hatom]
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have hA : 0 ≤ α - 1 / 2 := by linarith
    have hsq := mul_self_le_mul_self hA (by linarith : α - 1 / 2 ≤ 1 / gf')
    nlinarith [hsq]
  · intro h
    have hfac := mul_pos (by linarith : 0 < α - 1 / 2 - 1 / gf')
      (by linarith : (0 : ℝ) < α - 1 / 2 + 1 / gf')
    nlinarith [hfac]

/-! ## §5. The crossing -/

/-- **[The trapped-ion Mpemba crossing]** — `mpemba_crossing` at the Eq. 4 rates: on the split domain the
fast-mode (strong-ME-prepared) state overtakes the slow-mode state after the explicit
`t* = log(a/b)/(λ₋ − λ₊)`; with the Fig-5 amplitudes this is the `0.677 γ_f⁻¹` prediction against the
measured `≈ 0.6 γ_f⁻¹`. -/
theorem trapped_ion_crossing {a b γf α gf' : ℝ} (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γf)
    (hd : 0 < spectralDiscriminant α gf')
    {t : ℝ} (ht : mpembaCrossingTime a b (slowRate γf α gf') (fastRate γf α gf') < t) :
    a * Real.exp (fastRate γf α gf' * t) < b * Real.exp (slowRate γf α gf' * t) :=
  mpemba_crossing ha hb ((rates_split_iff hγ).mpr hd) ht

/-! ## §6. The synthesis -/

/-- **[The trapped-ion inverse-Mpemba spectrum, complete]** — **(i)** rate trace `−γ_f(2α+1)`;
**(ii)** rate determinant `γ_f²(2α+1/γ_f′²)`; **(iii)** slow/fast gap iff positive discriminant;
**(iv)** the slow-mode-free initial temperature is physical on the coherent domain; **(v)** the measured
steady-state locus is exactly the `(√(α/2), ½)` ellipse; **(vi)** the crossing follows at the explicit
`t*`.  The exact algebra behind the numerically verified reconstruction of Shapira et al. -/
theorem inverse_mpemba_spectrum_synthesis {a b γf α gf' : ℝ} (u : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γf) (hα : 1 / 2 < α) (hg : 0 < gf')
    (hd : 0 < spectralDiscriminant α gf')
    {t : ℝ} (ht : mpembaCrossingTime a b (slowRate γf α gf') (fastRate γf α gf') < t) :
    (slowRate γf α gf' + fastRate γf α gf' = -(γf * (2 * α + 1)))
      ∧ (slowRate γf α gf' * fastRate γf α gf' = γf ^ 2 * (2 * α + 1 / gf' ^ 2))
      ∧ (fastRate γf α gf' < slowRate γf α gf')
      ∧ (0 < strongMeCancellation α gf')
      ∧ ((2 * α * u / (1 + 2 * α * u ^ 2)) ^ 2 * (2 / α)
          + ((1 - 2 * α * u ^ 2) / (1 + 2 * α * u ^ 2)) ^ 2 = 1)
      ∧ a * Real.exp (fastRate γf α gf' * t) < b * Real.exp (slowRate γf α gf' * t) :=
  ⟨rate_sum γf α gf',
    rate_product γf hd.le,
    (rates_split_iff hγ).mpr hd,
    strongMeCancellation_pos hg hα hd.le,
    steady_state_ellipse u (by linarith),
    trapped_ion_crossing ha hb hγ hd ht⟩

/-! ## §7. The spectrum in entropic time: existence is clock-free, timing is clock-set

Measuring every rate per entropic tick means rescaling the overall rate `γ_f → γ_f/ω_E` (the entropic
clock `ω_E = k_BT/ℏ` is the only place temperature enters — `heating_scales_entropic_clock`).  The two
relaxation rates carry that clock (they are linear in `γ_f`), but the **spectral geometry** — the gap, the
slow/fast ratio, the discriminant `(α−½)²−1/γ_f′²`, and hence the *existence* of the Mpemba effect — is a
function of the dimensionless ratios `α, γ_f′` alone, so it is entropic-time-invariant.  *Whether* the
Mpemba effect occurs is a clock-free spectral fact; only *when* the crossing happens is set by `ω_E ∝ T`.
A hotter sample's faster entropic clock shortens the lab crossing time by `1/ω_E` while leaving the
entropic-tick count — and the existence — unchanged. -/

/-- **[the slow rate carries the clock]** — `λ₋` is linear in the overall rate: `λ₋(c·γ_f) = c·λ₋(γ_f)`.
Measuring in entropic ticks (`c = 1/ω_E`) divides the rate by the clock. -/
theorem slowRate_scaling (c γf α gf' : ℝ) :
    slowRate (c * γf) α gf' = c * slowRate γf α gf' := by
  unfold slowRate
  ring

/-- **[the fast rate carries the clock]** — `λ₊(c·γ_f) = c·λ₊(γ_f)`. -/
theorem fastRate_scaling (c γf α gf' : ℝ) :
    fastRate (c * γf) α gf' = c * fastRate γf α gf' := by
  unfold fastRate
  ring

/-- **[the Mpemba gap exists independently of the clock]** — rescaling the overall rate by any `c > 0`
(a change of entropic clock) does not change whether the slow/fast gap exists: the *existence condition*
of the Mpemba effect is entropic-time-invariant. -/
theorem rates_split_scaling_invariant {c γf α gf' : ℝ} (hc : 0 < c) :
    (fastRate (c * γf) α gf' < slowRate (c * γf) α gf')
      ↔ (fastRate γf α gf' < slowRate γf α gf') := by
  rw [fastRate_scaling, slowRate_scaling]
  constructor
  · intro h; exact lt_of_mul_lt_mul_left h hc.le
  · intro h; exact mul_lt_mul_of_pos_left h hc

/-- **[the slow/fast ratio is clock-free]** — the spectral geometry `λ₊/λ₋` is unchanged by the entropic
clock: the mode structure that produces the effect is a pure number, temperature-dial-independent. -/
theorem spectral_gap_ratio_entropic_invariant {c γf α gf' : ℝ} (hc : c ≠ 0) :
    fastRate (c * γf) α gf' / slowRate (c * γf) α gf'
      = fastRate γf α gf' / slowRate γf α gf' := by
  rw [fastRate_scaling, slowRate_scaling, mul_div_mul_left _ _ hc]

/-- **[the crossing time is set by the clock]** — the timing half: rescaling the rates by `c = ω_E`
divides the crossing time by `ω_E`, `t* = t*_ent/ω_E`.  So the *entropic-tick count* `ω_E·t*` is invariant
while the lab-frame `t*` scales as `1/T` — the hot sample's faster clock is exactly why it crosses sooner
in lab time. -/
theorem mpemba_crossing_scales_inversely (c a b l2 l3 : ℝ) :
    mpembaCrossingTime a b (c * l2) (c * l3) = mpembaCrossingTime a b l2 l3 / c := by
  unfold mpembaCrossingTime
  rw [show c * l2 - c * l3 = (l2 - l3) * c by ring, ← div_div]

/-- **[entropic-time re-evaluation of the mechanism]** — the Mpemba mechanism in entropic time:
**(i)** the rates carry the clock (`λ(c·γ_f) = c·λ`); **(ii)** the gap-existence is clock-invariant (the
spectral discriminant condition is a dimensionless fact); **(iii)** the slow/fast ratio is clock-free;
**(iv)** the crossing time scales as `1/ω_E ∝ 1/T`, so the entropic-tick count is invariant.  The
*existence* of the Mpemba effect is temperature-dial-free spectral geometry; temperature only sets the
*rate* of the entropic clock, hence the lab-frame *timescale*. -/
theorem mpemba_entropic_time_synthesis {c γf α gf' : ℝ} (hc : 0 < c) (a b l2 l3 : ℝ) :
    (slowRate (c * γf) α gf' = c * slowRate γf α gf')
      ∧ ((fastRate (c * γf) α gf' < slowRate (c * γf) α gf')
          ↔ (fastRate γf α gf' < slowRate γf α gf'))
      ∧ (fastRate (c * γf) α gf' / slowRate (c * γf) α gf'
          = fastRate γf α gf' / slowRate γf α gf')
      ∧ (mpembaCrossingTime a b (c * l2) (c * l3) = mpembaCrossingTime a b l2 l3 / c) :=
  ⟨slowRate_scaling c γf α gf', rates_split_scaling_invariant hc,
    spectral_gap_ratio_entropic_invariant hc.ne', mpemba_crossing_scales_inversely c a b l2 l3⟩

/-! ## §8. The Lorentz (Bisognano–Wichmann) interpretation: existence is a boost invariant

In the Bisognano–Wichmann picture the entropic clock is the wedge **modular flow**, which *is* the Lorentz
boost, and entropic time is *imaginary* modular time (the Euclidean continuation of the boost — where the
BW ladder `Δ(κ) = e^{−2πκ}` decays).  A wedge-axis boost of rapidity `η` Doppler-shifts the Unruh
temperature — the entropic clock rate `ω_E` — by `e^η`, so it rescales every rate `γ_f → e^η·γ_f`.  The
§7 clock factor is therefore a *boost factor* `c = e^η`.  Under it: the slow/fast gap (Mpemba's existence)
is **Lorentz-invariant**; the crossing, living in imaginary modular time, **dilates with rapidity**; and
the imaginary action `2πκ·s*` (the Unruh–Boltzmann exponent) is the **Lorentz invariant** — the rate
blueshifts and the modular time dilates in exact compensation. -/

/-- **[Mpemba existence is a Lorentz-boost invariant]** — a wedge-axis boost `γ_f → e^η·γ_f` (the Doppler
shift of the Unruh temperature / entropic clock) leaves the slow/fast gap unchanged: *whether* the Mpemba
effect exists is boost-independent, a Lorentz invariant of the modular (BW) flow. -/
theorem mpemba_gap_boost_invariant {η γf α gf' : ℝ} :
    (fastRate (Real.exp η * γf) α gf' < slowRate (Real.exp η * γf) α gf')
      ↔ (fastRate γf α gf' < slowRate γf α gf') :=
  rates_split_scaling_invariant (Real.exp_pos η)

/-- **[the wedge modular crossing dilates with rapidity]** — the crossing in imaginary modular time,
`s* = log(a/b)/(2π(κ₃−κ₂))` (`wedge_modular_mpemba_crossing`), contracts by `e^{−η}` under the boost: the
entropic (imaginary-modular) crossing time is rapidity-dependent. -/
theorem wedge_crossing_boost_dilation (η a b κ₂ κ₃ : ℝ) :
    mpembaCrossingTime a b (Real.exp η * -(2 * Real.pi * κ₂)) (Real.exp η * -(2 * Real.pi * κ₃))
      = mpembaCrossingTime a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃)) / Real.exp η :=
  mpemba_crossing_scales_inversely (Real.exp η) a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃))

/-- **[the imaginary action at the crossing is the Lorentz invariant]** — the Unruh–Boltzmann exponent
`2πκ₃·s*` is boost-invariant: the boost blueshifts the rate by `e^η` and dilates the modular time by
`e^{−η}`, and the product — the e-fold count — is unchanged.  *When* the crossing happens is
rapidity-dependent; *how many e-folds* it takes is Lorentz-invariant. -/
theorem wedge_imaginary_action_boost_invariant (η a b κ₂ κ₃ : ℝ) :
    (Real.exp η * (2 * Real.pi * κ₃))
        * mpembaCrossingTime a b (Real.exp η * -(2 * Real.pi * κ₂))
            (Real.exp η * -(2 * Real.pi * κ₃))
      = (2 * Real.pi * κ₃)
        * mpembaCrossingTime a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃)) := by
  rw [wedge_crossing_boost_dilation]
  have he : Real.exp η ≠ 0 := (Real.exp_pos η).ne'
  field_simp

/-- **[the Lorentz–Wichmann re-evaluation]** — the Mpemba mechanism in the boost (modular) frame:
**(i)** its existence is a Lorentz invariant (the gap survives every boost); **(ii)** its crossing time,
in imaginary modular time, dilates with rapidity; **(iii)** the imaginary action (e-fold count) it takes
is the Lorentz invariant.  Existence and e-folds are boost-frozen; only the modular-time *scale* is
rapidity-set — the Wichmann reading of "existence clock-free, timing clock-set." -/
theorem mpemba_lorentz_wichmann_synthesis {η γf α gf' : ℝ} (a b κ₂ κ₃ : ℝ) :
    ((fastRate (Real.exp η * γf) α gf' < slowRate (Real.exp η * γf) α gf')
        ↔ (fastRate γf α gf' < slowRate γf α gf'))
      ∧ (mpembaCrossingTime a b (Real.exp η * -(2 * Real.pi * κ₂)) (Real.exp η * -(2 * Real.pi * κ₃))
          = mpembaCrossingTime a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃)) / Real.exp η)
      ∧ ((Real.exp η * (2 * Real.pi * κ₃))
            * mpembaCrossingTime a b (Real.exp η * -(2 * Real.pi * κ₂))
                (Real.exp η * -(2 * Real.pi * κ₃))
          = (2 * Real.pi * κ₃)
            * mpembaCrossingTime a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃))) :=
  ⟨mpemba_gap_boost_invariant, wedge_crossing_boost_dilation η a b κ₂ κ₃,
    wedge_imaginary_action_boost_invariant η a b κ₂ κ₃⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.rates_split_iff where
  formalizes @ "claim:the-trapped-ion-mpemba-effect-exists-iff-the-bloch-sector-spectral-discriminant-is-positive",
  supported_by @ "paper:shapira-teza-raz-ozeri-2401.05830-inverse-mpemba-trapped-ion-qubit",
  caveat @ "epistemic:the-bloch-sector-reduction-to-two-rates-is-the-papers-numerically-verified-result-not-derived-at-operator-level-here"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.steady_state_ellipse where
  formalizes @ "claim:the-driven-qubit-steady-state-locus-is-exactly-the-half-ellipse-with-semiaxes-sqrt-alpha-over-2-and-one-half",
  supported_by @ "paper:shapira-teza-raz-ozeri-2401.05830-inverse-mpemba-trapped-ion-qubit",
  caveat @ "epistemic:resolves-the-papers-ambiguous-printed-semiaxis-sqrt-alpha-slash-2-as-sqrt-of-alpha-over-2"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.strong_me_threshold where
  formalizes @ "claim:the-strong-inverse-mpemba-coherence-threshold-is-alpha-greater-than-one-half-plus-inverse-final-temperature",
  supported_by @ "paper:shapira-teza-raz-ozeri-2401.05830-inverse-mpemba-trapped-ion-qubit",
  caveat @ "epistemic:corrects-the-catept-main-paperdata-mislabel-of-the-one-third-subthreshold-example-as-the-threshold"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.inverse_mpemba_spectrum_synthesis where
  formalizes @ "claim:the-trapped-ion-inverse-mpemba-spectrum-trace-determinant-gap-cancellation-ellipse-and-crossing-are-exact-algebra-over-the-eq4-rates",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  requires @ "claim:the-trapped-ion-mpemba-effect-exists-iff-the-bloch-sector-spectral-discriminant-is-positive",
  supported_by @ "paper:shapira-teza-raz-ozeri-2401.05830-inverse-mpemba-trapped-ion-qubit",
  caveat @ "epistemic:cancellation-point-0.0762-vs-paper-0.07-and-two-mode-crossing-0.677-vs-measured-0.6-gamma-f-inverse-live-in-the-companion-script"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.rates_split_scaling_invariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.fastRate_scaling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.slowRate_scaling",
  formalizes @ "claim:whether-the-mpemba-effect-exists-is-entropic-time-invariant-the-spectral-gap-condition-is-a-dimensionless-fact-independent-of-the-clock",
  requires @ "claim:the-mpemba-gap-exists-iff-the-spectral-discriminant-is-positive-the-existence-condition"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.mpemba_entropic_time_synthesis where
  formalizes @ "claim:in-entropic-time-the-mpemba-existence-is-clock-free-spectral-geometry-while-the-crossing-timescale-is-set-by-the-entropic-clock-rate-omega-e-proportional-to-temperature",
  requires @ "claim:whether-the-mpemba-effect-exists-is-entropic-time-invariant-the-spectral-gap-condition-is-a-dimensionless-fact-independent-of-the-clock",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaEntropicClock.heating_scales_entropic_clock"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.mpemba_gap_boost_invariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.rates_split_scaling_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.wedge_modular_mpemba_crossing",
  formalizes @ "claim:in-the-bisognano-wichmann-picture-whether-the-mpemba-effect-exists-is-a-lorentz-boost-invariant-since-a-boost-only-doppler-shifts-the-unruh-temperature-entropic-clock-rate",
  requires @ "claim:whether-the-mpemba-effect-exists-is-entropic-time-invariant-the-spectral-gap-condition-is-a-dimensionless-fact-independent-of-the-clock"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.wedge_imaginary_action_boost_invariant where
  formalizes @ "claim:the-imaginary-action-e-fold-count-of-the-wedge-mpemba-crossing-is-the-lorentz-invariant-the-rate-blueshifts-and-the-modular-time-dilates-in-compensation",
  requires @ "claim:the-mpemba-crossing-time-in-imaginary-modular-time-dilates-with-rapidity-under-a-wedge-axis-boost",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.wedge_modular_mpemba_crossing"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.mpemba_lorentz_wichmann_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.mpemba_gap_boost_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTrappedIonMpembaSpectrum.wedge_imaginary_action_boost_invariant",
  formalizes @ "claim:the-wichmann-reading-of-the-mpemba-mechanism-existence-and-e-folds-are-boost-frozen-lorentz-invariants-only-the-imaginary-modular-time-scale-is-rapidity-set",
  requires @ "claim:in-the-bisognano-wichmann-picture-whether-the-mpemba-effect-exists-is-a-lorentz-boost-invariant-since-a-boost-only-doppler-shifts-the-unruh-temperature-entropic-clock-rate"

/- ZIL-END -/
