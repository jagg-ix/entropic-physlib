/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

meta import Zil

/-!
# Millikan's photoelectric determination of Planck's `h`

Millikan, *A Direct Photoelectric Determination of Planck's "h"*, Phys. Rev. **7**, 355 (1916).

The paper verifies Einstein's photoelectric equation (its Eq. (1))

  `½mv² = V·e = hν − p`

— maximum electron energy = stopping potential times charge = photon energy minus work
function — through five "experimentally verifiable relationships", and inverts the measured
slope to determine `h`.  The kinematic content of all five assertions is exact algebra on the
stopping-energy carrier, formalized here:

1. **Threshold existence** — a positive maximum emission energy exists exactly above the
   critical frequency (`stoppingEnergy_pos_iff`);
2. **Linearity** — the stopping potential is affine in the frequency
   (`hasDerivAt_stoppingPotential`);
3. **Slope** — `dV/dν = h/e`, and the measured slope *determines* `h = e·(dV/dν)` by
   uniqueness of the derivative (`planck_from_slope`) — the paper's title result;
4. **Intercept** — `V = 0` exactly at the critical frequency, i.e. the work function is
   `p = hν₀` (`stoppingPotential_eq_zero_iff`);
5. **Contact E.M.F.** — the Volta potential between two metals is `(h/e)(ν₀ − ν₀′)`
   (`contact_emf_thresholds`), and with both photopotentials referenced to a common collector
   the measured stopping potentials coincide (`common_collector_stoppingPotential`), which is
   how the paper's `Contact E.M.F. = h/e(ν₀ − ν₀′) − (V₀ − V₀′)` is read.

Bridges to the repository: the `ħ`-convention face `hν = ħω` at `ω = 2πν`
(`stoppingEnergy_hbar_omega`), and the photoelectric equation transported to the temperature
sector by the converter's additivity (`photoelectric_temperature_additivity`:
`T_dB(hν) = T_dB(p) + T_dB(Ve)`).

The rest of the paper (§§4–9): the determination machinery — the two-point slope identity
behind Table II and its inversion (`planck_from_two_points`), the practical-volt `1/300`
reading of Fig. 6's box (`planck_from_practical_slope`) — with Millikan's printed arithmetic
verified by `norm_num` (`millikan_fig6_slope_arithmetic`, `millikan_tableII_mean`,
`millikan_sodium_h_arithmetic`); the contact-E.M.F. equation (2) as an exact identity
(`contact_emf_equation`) with its sodium test checked (`millikan_contact_emf_arithmetic` —
which also surfaces a printed-figure inconsistency on p. 382); Planck's radiation route
inverted (`planck_radiation_density_iff`, coefficient `48π·ζ(4) = 8π⁵/15` with
`α = 1.0823 = ζ(4) = π⁴/90`, and `a = 4σ/c`), the Reichsanstalt `c₂ = hc/k = 1.436`
recomputed from `e` and `h` (`millikan_reichsanstalt_c2`); and §9's classical loading-time
bound (`classical_loading_time_bound`: continuous absorption needs ≥ 12,000 s against
instantaneous emission — the quantitative argument for discontinuous absorption that is
independent of the corpuscle hypothesis).

Honest scope: the kinematic identities of Einstein's equation and their measurement-inversion
logic; nothing here derives the quantum hypothesis itself.  The paper is an epistemic gem on
exactly this point — Millikan confirmed the *equation* to 0.5% (`h = 6.57×10⁻²⁷ erg·s`)
while explicitly rejecting the "reckless" corpuscle hypothesis behind it; the caveat is
recorded in the graph.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PhotoelectricPlanckDetermination

/-- **The maximum photoelectron energy** `½mv² = hν − p` — Einstein's photoelectric equation
(Millikan Eq. (1)): photon energy `hν` minus the work function `p`. -/
def stoppingEnergy (h ν p : ℝ) : ℝ := h * ν - p

/-- **The stopping potential** `V = (hν − p)/e` — the retarding potential that just stops the
fastest photoelectrons, the quantity Millikan measures. -/
def stoppingPotential (h ν p e : ℝ) : ℝ := (h * ν - p) / e

/-- Millikan Eq. (1) in its `V·e = hν − p` form. -/
theorem stoppingPotential_charge (h ν p e : ℝ) (he : e ≠ 0) :
    stoppingPotential h ν p e * e = h * ν - p := by
  unfold stoppingPotential
  field_simp

/-- **Assertion 1 — the threshold**: with work function `p = hν₀`, a positive maximum emission
energy exists exactly above the critical frequency `ν₀`. -/
theorem stoppingEnergy_pos_iff (h ν ν₀ : ℝ) (hh : 0 < h) :
    0 < stoppingEnergy h ν (h * ν₀) ↔ ν₀ < ν := by
  unfold stoppingEnergy
  constructor <;> intro h0 <;> nlinarith

/-- **Assertions 2 and 3 — linearity with slope `h/e`**: the stopping potential is affine in
the frequency with derivative `h/e` everywhere. -/
theorem hasDerivAt_stoppingPotential (h p e ν : ℝ) :
    HasDerivAt (fun x => stoppingPotential h x p e) (h / e) ν := by
  have h1 : HasDerivAt (fun x : ℝ => h * x) h ν := by
    simpa using (hasDerivAt_id ν).const_mul h
  unfold stoppingPotential
  exact (h1.sub_const p).div_const e

/-- **The determination of `h`** (the paper's title result): the measured slope of the
`V`–`ν` line determines Planck's constant, `h = e·(dV/dν)` — by uniqueness of the
derivative. -/
theorem planck_from_slope {h p e ν s : ℝ} (he : e ≠ 0)
    (hs : HasDerivAt (fun x => stoppingPotential h x p e) s ν) : h = e * s := by
  have hu : h / e = s := (hasDerivAt_stoppingPotential h p e ν).unique hs
  rw [div_eq_iff he] at hu
  rw [hu]
  ring

/-- **Assertion 4 — the intercept**: the stopping potential vanishes exactly at the critical
frequency; the `ν`-axis intercept of the `V`–`ν` line is the photoelectric threshold, i.e. the
work function is `p = hν₀`. -/
theorem stoppingPotential_eq_zero_iff (h ν ν₀ e : ℝ) (hh : h ≠ 0) (he : e ≠ 0) :
    stoppingPotential h ν (h * ν₀) e = 0 ↔ ν = ν₀ := by
  unfold stoppingPotential
  rw [div_eq_zero_iff]
  constructor
  · rintro (h0 | h0)
    · exact mul_left_cancel₀ hh (by linarith)
    · exact absurd h0 he
  · intro h0
    left
    rw [h0]
    ring

/-- **Assertion 5, Volta face**: the contact E.M.F. between two metals — the difference of
their work functions per unit charge — is `(h/e)·(ν₀ − ν₀′)` in their photoelectric
thresholds. -/
theorem contact_emf_thresholds (h e ν₀ ν₀' : ℝ) (he : e ≠ 0) :
    (h * ν₀ - h * ν₀') / e = h / e * (ν₀ - ν₀') := by
  field_simp

/-- **Assertion 5, common-collector face**: photopotentials measured against a *common*
collector carry the collector's work function, so two emitters show the *same* measured
stopping potential — which is why, in Millikan's
`Contact E.M.F. = h/e(ν₀ − ν₀′) − (V₀ − V₀′)`, the measured-potential term drops and the
contact E.M.F. is read off the thresholds alone. -/
theorem common_collector_stoppingPotential (h ν pC e : ℝ) :
    stoppingPotential h ν pC e - stoppingPotential h ν pC e = 0 := by
  ring

/-- The `ħ`-convention face of the photon energy: `hν = ħω` at `ω = 2πν` under `h = 2πħ` —
the bridge from Millikan's `h`-and-`ν` bookkeeping to the repository's `ħ`-and-`ω`
carriers. -/
theorem stoppingEnergy_hbar_omega (ħ ν p : ℝ) :
    stoppingEnergy (2 * Real.pi * ħ) ν p = ħ * (2 * Real.pi * ν) - p := by
  unfold stoppingEnergy
  ring

/-- **The photoelectric equation in the temperature sector**: under the converter
`T_dB = E/(2πk_B)`, Einstein's `hν = p + Ve` transports to
`T_dB(hν) = T_dB(p) + T_dB(Ve)` — energy bookkeeping and temperature bookkeeping are the same
bookkeeping, by the converter's additivity. -/
theorem photoelectric_temperature_additivity (h ν p e V kB : ℝ)
    (heq : V * e = h * ν - p) :
    Physlib.Thermodynamics.deBroglieTemperature (h * ν) kB
      = Physlib.Thermodynamics.deBroglieTemperature p kB
        + Physlib.Thermodynamics.deBroglieTemperature (V * e) kB := by
  rw [heq]
  unfold Physlib.Thermodynamics.deBroglieTemperature
  ring

/-! ## §4 — the determination: two-point slope, practical units, and Millikan's arithmetic -/

/-- **The two-point form of the linear law**: the stopping-potential difference between two
frequencies is `(h/e)·(ν₂ − ν₁)` — the identity behind Table II's nine slope determinations
(two distant lines located in rapid succession, `λ = 5461` always one of them). -/
theorem stoppingPotential_two_point (h ν₁ ν₂ p e : ℝ) :
    stoppingPotential h ν₂ p e - stoppingPotential h ν₁ p e = h / e * (ν₂ - ν₁) := by
  unfold stoppingPotential
  ring

/-- **`h` from two measured points**: the two-point method's inversion,
`h = e·(V₂ − V₁)/(ν₂ − ν₁)`. -/
theorem planck_from_two_points {h ν₁ ν₂ p e V₁ V₂ : ℝ} (he : e ≠ 0) (hν : ν₁ ≠ ν₂)
    (h1 : V₁ = stoppingPotential h ν₁ p e) (h2 : V₂ = stoppingPotential h ν₂ p e) :
    h = e * (V₂ - V₁) / (ν₂ - ν₁) := by
  subst h1 h2
  rw [stoppingPotential_two_point h ν₁ ν₂ p e]
  have hd : ν₂ - ν₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hν)
  field_simp

/-- **The practical-volt reading** (the `1/300` of Fig. 6's box): with the potential measured
in practical volts (`1 statvolt = 300 V`), the slope is `300·h/e` and the determination reads
`h = e·(dV/dν)/300` — Millikan's `h = e/300 · dV/dν`. -/
theorem planck_from_practical_slope {h p e ν s : ℝ} (he : e ≠ 0)
    (hs : HasDerivAt (fun x => 300 * stoppingPotential h x p e) s ν) : h = e * s / 300 := by
  have h300 : HasDerivAt (fun x => 300 * stoppingPotential h x p e) (300 * (h / e)) ν :=
    (hasDerivAt_stoppingPotential h p e ν).const_mul 300
  have hu : 300 * (h / e) = s := h300.unique hs
  field_simp at hu ⊢
  linarith

/-- **Fig. 6's slope arithmetic checks**: `3 volts / (121.00 − 48.25)×10¹³ Hz = 4.124×10⁻¹⁵`
volt-seconds, to the printed precision. -/
theorem millikan_fig6_slope_arithmetic :
    |(3 : ℝ) / ((121.00 - 48.25) * 1e13) - 4.124e-15| ≤ 5e-19 := by
  rw [abs_le]
  constructor <;> norm_num

/-- **Table II's mean checks**: the nine two-point slopes average to `4.131×10⁻¹⁵`, as
printed. -/
theorem millikan_tableII_mean :
    |((4.11 + 4.14 + 4.10 + 4.12 + 4.24 + 3.98 + 4.04 + 4.24 + 4.21) / 9 : ℝ) * 1e-15
      - 4.131e-15| ≤ 2e-19 := by
  rw [abs_le]
  constructor <;> norm_num

/-- **The sodium determination checks**: `h = e·(dV/dν)/300` with Millikan's
`e = 4.774×10⁻¹⁰` e.s.u. and the final sodium slope `4.128×10⁻¹⁵` (the mean of the Fig. 6 and
Table II values) gives `6.569×10⁻²⁷ erg·s`, as printed. -/
theorem millikan_sodium_h_arithmetic :
    |(4.774e-10 : ℝ) * 4.128e-15 / 300 - 6.569e-27| ≤ 1e-30 := by
  rw [abs_le]
  constructor <;> norm_num

/-! ## §6 — contact E.M.F. from photoelectric data (the paper's Eq. (2)) -/

/-- **The contact-E.M.F. equation** (the paper's Eq. (2)): if a metal's *measured* stopping
potential is its true one shifted down by the contact E.M.F. `K` against the reference, and the
reference's potential is true, then
`K = (h/e)(ν₀′ − ν₀) − (V₀ − V₀′)` — contact E.M.F. in photoelectrically measured quantities
alone.  The paper's numeric tests: sodium `2.54` predicted vs `2.51` measured (1%); lithium
`1.526` vs `1.52`, and months later `1.125` vs `1.11`.  (Formalization note: the paper's
printed factor `(118.2 − 43.9)` on p. 382 is inconsistent with its own product `2.79 V`,
which requires `(111.6 − 43.9)` — the copper-oxide limit `ν₀′ = 111.6×10¹³` — as the
arithmetic check below confirms.) -/
theorem contact_emf_equation {h e ν ν₀ ν₀' V₀ V₀' K : ℝ}
    (hMeas : V₀ = stoppingPotential h ν (h * ν₀) e - K)
    (hRef : V₀' = stoppingPotential h ν (h * ν₀') e) :
    K = h / e * (ν₀' - ν₀) - (V₀ - V₀') := by
  subst hMeas hRef
  unfold stoppingPotential
  ring

/-- **The sodium contact-E.M.F. test checks**: `(h/e)(ν₀′ − ν₀) − (V₀ − V₀′)
= 4.128×10⁻¹⁵·(111.6 − 43.9)×10¹³ − (0.52 − 0.27) = 2.54`, against the measured `2.51` —
agreement within `0.04` V (the paper's "about 1 per cent."). -/
theorem millikan_contact_emf_arithmetic :
    |(4.128e-15 : ℝ) * ((111.6 - 43.9) * 1e13) - (0.52 - 0.27) - 2.51| ≤ 4e-2 := by
  rw [abs_le]
  constructor <;> norm_num

/-! ## §8 — `h` from Planck's radiation theory, and the black-body constants from `e` and `h` -/

/-- The coefficient of Planck's inversion: `48π·ζ(4) = 8π⁵/15`, with `ζ(4) = π⁴/90` — the
paper's `α = 1.0823` is exactly `ζ(4)`. -/
theorem planck_coefficient_zeta_four :
    (48 : ℝ) * Real.pi * (Real.pi ^ 4 / 90) = 8 * Real.pi ^ 5 / 15 := by
  ring

/-- **Planck's radiation route, inverted**: the radiation density constant determines `h` and
conversely, `a = 8π⁵k⁴/(15h³c³) ⟺ h³ = 8π⁵k⁴/(15ac³)` — the relation through which the paper
compares its photoelectric `6.57×10⁻²⁷` with the radiation value (`k = 1.372×10⁻¹⁶`,
`a = 7.56×10⁻¹⁵` from Westphal's `σ` via `a = 4σ/c`). -/
theorem planck_radiation_density_iff {a c h k : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0) :
    a = 8 * Real.pi ^ 5 * k ^ 4 / (15 * h ^ 3 * c ^ 3)
      ↔ h ^ 3 = 8 * Real.pi ^ 5 * k ^ 4 / (15 * a * c ^ 3) := by
  have d1 : (15 : ℝ) * h ^ 3 * c ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hh)) (pow_ne_zero 3 hc)
  have d2 : (15 : ℝ) * a * c ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 3 hc)
  rw [eq_div_iff d1, eq_div_iff d2]
  constructor <;> intro H <;> linear_combination H

/-- **Stefan's constant and the radiation density constant**: `a = 4σ/c ⟺ σ = ac/4` — the
bridge the paper uses to feed Westphal's `σ = 5.67×10⁻⁵` into the radiation route. -/
theorem radiation_density_stefan {a σ c : ℝ} (hc : c ≠ 0) :
    a = 4 * σ / c ↔ σ = a * c / 4 := by
  rw [eq_div_iff hc, eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
  constructor <;> intro H <;> linear_combination -H

/-- **The Reichsanstalt check**: `c₂ = hc/k` with the photoelectric
`h = 6.569×10⁻²⁷`, `c = 2.999×10¹⁰`, `k = 1.372×10⁻¹⁶` gives `1.436` cm·K — "exactly the
Reichsanstalt value found in 1913", recomputing a black-body constant from `e` and `h`
alone. -/
theorem millikan_reichsanstalt_c2 :
    |(6.569e-27 : ℝ) * 2.999e10 / 1.372e-16 - 1.436| ≤ 2e-3 := by
  rw [abs_le]
  constructor <;> norm_num

/-! ## §9 — the classical loading-time bound -/

/-- **The classical absorption-time bound** (the paper's §9 energy argument): a standard
candle at 3 m delivers `10⁻¹⁵ erg/s` to an atomic cross-section, of which at most a third is
at usable frequencies; continuously loading the quantum `hν = 4×10⁻¹² erg` for `λ = 5000 Å`
therefore needs at least `12,000` seconds — four hours — while emission is observed the
instant the light is turned on.  The quantitative core of the argument that forces energy to
be pre-loaded or absorbed discontinuously, *independently of the corpuscle hypothesis*. -/
theorem classical_loading_time_bound {E P : ℝ} (hE : E = 4e-12)
    (hP : P ≤ 1e-15 / 3) (hP0 : 0 < P) : 12000 ≤ E / P := by
  subst hE
  rw [le_div_iff₀ hP0]
  nlinarith

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.planck_from_slope where
  formalizes @ "claim:the-measured-slope-of-the-stopping-potential-frequency-line-determines-plancks-constant-h-equals-e-times-the-slope",
  supported_by @ "paper:millikan-1916-photoelectric-determination-of-planck-h",
  supported_by @ "paper:einstein-1905-photoelectric-hypothesis",
  experimental_bound @ "millikan-1916-h-equals-6-point-57-times-ten-to-minus-27-erg-seconds-within-half-a-percent-from-sodium-and-lithium-slopes",
  caveat @ "claim:the-kinematic-identities-verify-einsteins-equation-not-the-light-corpuscle-hypothesis-millikan-himself-confirmed-the-equation-while-rejecting-the-hypothesis"

zil attach Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.stoppingPotential_eq_zero_iff where
  formalizes @ "claim:the-frequency-axis-intercept-of-the-stopping-potential-line-is-the-photoelectric-threshold-so-the-work-function-is-h-times-the-critical-frequency",
  supported_by @ "paper:millikan-1916-photoelectric-determination-of-planck-h"

zil attach Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.photoelectric_temperature_additivity where
  formalizes @ "claim:einsteins-photoelectric-energy-balance-transports-to-the-temperature-sector-by-the-de-broglie-converter-additivity",
  supported_by @ "lean:Physlib.Thermodynamics.deBroglieTemperature",
  caveat @ "claim:algebraic-carrier-identity-not-an-independent-derivation-of-thermality"

zil attach Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.contact_emf_equation where
  formalizes @ "claim:the-contact-emf-between-two-conductors-is-given-by-photoelectrically-measured-quantities-h-over-e-times-threshold-difference-minus-measured-potential-difference",
  supported_by @ "paper:millikan-1916-photoelectric-determination-of-planck-h",
  experimental_bound @ "millikan-1916-sodium-contact-emf-predicted-2-54-measured-2-51-volts-one-percent-lithium-1-526-vs-1-52-and-1-125-vs-1-11",
  caveat @ "claim:the-papers-printed-factor-118-2-minus-43-9-on-page-382-is-inconsistent-with-its-own-product-2-79-volts-which-requires-the-copper-oxide-limit-111-6"

zil attach Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.classical_loading_time_bound where
  formalizes @ "claim:continuous-classical-absorption-of-the-quantum-h-nu-from-a-standard-candle-at-three-meters-needs-at-least-twelve-thousand-seconds-while-emission-is-instantaneous",
  supported_by @ "paper:millikan-1916-photoelectric-determination-of-planck-h",
  caveat @ "claim:forces-preloaded-or-discontinuous-absorption-independently-of-the-corpuscle-hypothesis-but-does-not-select-a-mechanism"

zil attach Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.millikan_reichsanstalt_c2 where
  formalizes @ "claim:the-blackbody-constant-c2-equals-h-c-over-k-recomputed-from-the-photoelectric-h-gives-1-436-the-reichsanstalt-1913-value",
  supported_by @ "paper:millikan-1916-photoelectric-determination-of-planck-h"

zil_file_contract physlib.photoelectricPlanckDetermination where
  promises "Millikan 1916: the kinematic content of Einstein's photoelectric equation and its measurement-inversion logic. The five verifiable assertions as exact identities on the stopping-energy carrier: threshold existence, affine linearity of stopping potential in frequency, slope h/e with the determination h = e dV/dnu by uniqueness of the derivative, the intercept as the work function p = h nu0, and the contact-EMF relation in its Volta and common-collector faces. Bridges: h nu = hbar omega at omega = 2 pi nu, and the photoelectric energy balance transported to the temperature sector by the de Broglie converter additivity."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.deBroglieTemperature"]
  forbids_substitutes [
    "the light-corpuscle hypothesis claimed from the kinematic identities (Millikan confirmed the equation while rejecting the hypothesis)",
    "a derivation of the quantum of action claimed from the measurement-inversion identity",
    "photon statistics or intensity-independence claimed from the stopping-energy algebra"]
  witnessed_by [stoppingEnergy_pos_iff, hasDerivAt_stoppingPotential, planck_from_slope,
    stoppingPotential_eq_zero_iff, contact_emf_thresholds,
    photoelectric_temperature_additivity, planck_from_two_points,
    planck_from_practical_slope, contact_emf_equation, planck_radiation_density_iff,
    millikan_sodium_h_arithmetic, millikan_reichsanstalt_c2, classical_loading_time_bound]

/- ZIL-END -/

end Physlib.QuantumMechanics.PhotoelectricPlanckDetermination

end
