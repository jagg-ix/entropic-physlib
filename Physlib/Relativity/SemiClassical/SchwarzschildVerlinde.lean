/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.SemiClassical.SchwarzschildHorizonEntropicTime
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
meta import Zil

/-!
# Bridge: Schwarzschild horizon ↔ Verlinde holographic bits + Einstein hyperbolic-orbit deflection

Connects three previously independent strands in physlib:

1. **Schwarzschild horizon entropic time** (commit `1b5171d2`,
   `Physlib.Relativity.SemiClassical.SchwarzschildHorizonEntropicTime`)
   — `dτ_hor = dA / (4·ℓ_P²)`, with `A = 16π·G²·M²/c⁴`.

2. **Verlinde holographic bits / entropic gravity** (existing
   `Physlib.Thermodynamics.VerlindeNewtonGravity`) — bit count
   `N = A·c³/(G·ℏ)` on a holographic screen.

3. **Einstein's hyperbolic-orbit light deflection**
   `θ_def = 4·G·M / (b·c²)` — the deflection angle of a light
   ray with impact parameter `b` passing a mass `M`, the
   geodesic-bending paradigm of Einstein 1916 and the load-bearing
   prediction confirmed by Eddington 1919.  Algebraic content
   ported from the Grok survey
   (`tau/Grok-Lean4_Code__Einstein_Thought_Experiments (2) copy.md`
   line ~697).

The substantive identifications:

* **Bekenstein–Verlinde bridge**: under `ℓ_P² = ℏ·G/c³`, the
  Verlinde holographic bit count IS the horizon area in Planck
  units: `holographicBits A G ℏ c = A / ℓ_P²`.

* **Schwarzschild Bekenstein-entropic time** equals the
  **Verlinde holographic bit count** at the Schwarzschild horizon
  (up to a factor of 4): `bekensteinTauEnt A ℓ_P = holographicBits / 4`.

* **Einstein deflection** at the Schwarzschild horizon scale: the
  light-deflection angle equals **twice the Schwarzschild
  radius over the impact parameter**: `θ_def = 2·r_s/b` with
  `r_s = 2GM/c²`.

* **Rotating-disk rim Lorentz factor**
  `γ_rim(ω, r) := 1 / √(1 − (ωr)²/c²)` — the Ehrenfest-rotating-disk
  rapidity (from Grok line ~714) — interpreted as `cosh` of the
  rim rapidity, the hyperbolic-rotation parameter linking
  Special-relativistic boosts to Rindler/Unruh entropic-time
  rates already in physlib (`RindlerEntropicTime`).

## Contents


* **`holographicBits_eq_area_over_ℓPsq`** — `N = A / ℓ_P²` under
  `ℓ_P² = ℏ·G/c³`.
* **`bekensteinTauEnt_eq_holographicBits_div_four`** — Bekenstein
  entropic time = Verlinde bits / 4 (algebraic identity).
* `schwarzschildArea_holographicBits` — explicit form for
  Schwarzschild: `N = 16π·G·M² / (ℏ·c)`.


* `einsteinLightDeflection M G c b := 4·G·M / (b·c²)`.
* `einsteinLightDeflection_pos`.
* **`einsteinLightDeflection_eq_two_schwarzschildRadius_over_b`** —
  `θ_def = 2·r_s/b` where `r_s = 2GM/c²`.


* `rotatingDiskRimLorentzFactor ω r c := 1 / √(1 − (ωr)²/c²)`.
* `rotatingDiskRimLorentzFactor_pos` — under `|ωr| < c`.
* `rotatingDiskRimLorentzFactor_at_zero_rapidity` — `γ_rim(0, r) = 1`.

## Honest scope

This file provides **algebraic identities only**:
* Schwarzschild geodesic deflection is *not* derived from the
  Einstein field equations — only the algebraic
  `θ_def = 4GM/(b·c²)` formula and its relation to `r_s`.
* The rotating-disk Lorentz factor is the **special-relativistic**
  rim contraction, not the full Ehrenfest paradox resolution
  (which requires a curved spatial metric on the rotating frame).
* The Bekenstein–Verlinde bridge identities rely on the
  Planck-length relation `ℓ_P² = ℏ·G/c³` as a hypothesis
  (consistent with `Physlib.Units.PlanckBasis`).

## References

* Einstein 1916 — light deflection in GR.
* Eddington 1919 — solar-eclipse verification.
* Ehrenfest 1909 — rotating-disk paradox.
* Verlinde 2011 (arXiv:1001.0785) — entropic gravity, holographic
  bit count.
* Bekenstein 1973 *Phys. Rev. D* 7, 2333.
* Source: `tau/Grok-Lean4_Code__Einstein_Thought_Experiments (2) copy.md`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.SemiClassical

open Real Physlib.Thermodynamics


/-- **Holographic bit count equals area in Planck units**
under the standard Planck-length relation `ℓ_P² = ℏ·G/c³`.

  `holographicBits A G ℏ c = A / ℓ_P²`.

This is the **Bekenstein–Verlinde algebraic bridge** — the
Verlinde Eq. (the "bits"-form) of Verlinde 2011 §3 is *literally*
the horizon area divided by the Planck area, certifying that
both formalisms count the same thing. -/
lemma holographicBits_eq_area_over_ℓPsq
    {A G ℏ c ℓP : ℝ}
    (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (h_ℓP_sq : ℓP^2 = ℏ * G / c^3) :
    holographicBits A G ℏ c = A / ℓP^2 := by
  unfold holographicBits
  rw [h_ℓP_sq]
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hc_ne : c ≠ 0 := ne_of_gt hc
  field_simp

/-- **Bekenstein entropic time = (1/4) × Verlinde holographic bits**.

Algebraic identity at the horizon: the Bekenstein entropic time
`τ_ent = A/(4·ℓ_P²)` equals one-quarter of the Verlinde holographic
bit count `N = A/ℓ_P²`.

This is the **quarter-area law** of black-hole entropy expressed
as a bit/entropic-time identity — Bekenstein 1973 + Verlinde 2011
agree on the same horizon. -/
lemma bekensteinTauEnt_eq_holographicBits_div_four
    {A G ℏ c ℓP : ℝ}
    (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hℓP : ℓP ≠ 0)
    (h_ℓP_sq : ℓP^2 = ℏ * G / c^3) :
    bekensteinTauEnt A ℓP = holographicBits A G ℏ c / 4 := by
  rw [holographicBits_eq_area_over_ℓPsq hG hℏ hc h_ℓP_sq]
  unfold bekensteinTauEnt
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  field_simp

/-- **Schwarzschild holographic bits**:
`N(M) := holographicBits (schwarzschildArea M G c) G ℏ c
       = 16π·G·M² / (ℏ·c)`. -/
lemma schwarzschildArea_holographicBits
    {M G ℏ c : ℝ}
    (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c) :
    holographicBits (schwarzschildArea M G c) G ℏ c
      = 16 * Real.pi * G * M^2 / (ℏ * c) := by
  unfold holographicBits schwarzschildArea
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hc_ne : c ≠ 0 := ne_of_gt hc
  field_simp


/-- **Einstein light-deflection angle** for a photon with impact
parameter `b` passing a mass `M`:

  `θ_def := 4·G·M / (b·c²)`.

The hyperbolic-orbit deflection prediction of Einstein 1916
verified by Eddington 1919.  Twice the Newtonian (Soldner 1801)
value — the factor of 2 is the load-bearing GR signature.

Algebraic-only port from the Grok survey
(line ~697 of the source file). -/
def einsteinLightDeflection (M G c b : ℝ) : ℝ :=
  4 * G * M / (b * c^2)

/-- **Einstein deflection is positive** at positive mass and
positive impact parameter. -/
lemma einsteinLightDeflection_pos
    {M G c b : ℝ}
    (hM : 0 < M) (hG : 0 < G) (hc : 0 < c) (hb : 0 < b) :
    0 < einsteinLightDeflection M G c b := by
  unfold einsteinLightDeflection
  have h_num : 0 < 4 * G * M := by positivity
  have h_den : 0 < b * c^2 := by positivity
  exact div_pos h_num h_den

/-- **Schwarzschild radius** `r_s := 2·G·M / c²` — the
characteristic horizon scale of a mass `M`. -/
def schwarzschildRadius (M G c : ℝ) : ℝ := 2 * G * M / c^2

/-- **Schwarzschild radius is positive** at positive mass, `G`, `c`. -/
lemma schwarzschildRadius_pos
    {M G c : ℝ} (hM : 0 < M) (hG : 0 < G) (hc : 0 < c) :
    0 < schwarzschildRadius M G c := by
  unfold schwarzschildRadius
  exact div_pos (by positivity) (by positivity)

/-- **Einstein deflection in Schwarzschild-radius form**:

  `θ_def = 2 · r_s / b`,

where `r_s = 2·G·M/c²` is the Schwarzschild radius and `b` the
impact parameter.  The deflection is **twice the Schwarzschild
radius over the impact parameter** — a clean geometric statement
of the GR factor of 2. -/
lemma einsteinLightDeflection_eq_two_schwarzschildRadius_over_b
    {M G c b : ℝ}
    (hc : c ≠ 0) (hb : b ≠ 0) :
    einsteinLightDeflection M G c b = 2 * schwarzschildRadius M G c / b := by
  unfold einsteinLightDeflection schwarzschildRadius
  have hc_sq : c^2 ≠ 0 := pow_ne_zero 2 hc
  field_simp
  ring


/-- **Rotating-disk rim Lorentz factor**

  `γ_rim(ω, r) := 1 / √(1 − (ω·r)² / c²)`,

the Ehrenfest 1909 rapidity factor at the rim of a rigidly
rotating disk of radius `r` and angular velocity `ω`.

Algebraic-only port from the Grok survey (line ~714). -/
def rotatingDiskRimLorentzFactor (ω r c : ℝ) : ℝ :=
  1 / Real.sqrt (1 - (ω * r)^2 / c^2)

/-- **Rotating-disk rim Lorentz factor is positive** under
sub-luminal rim speed (`(ω·r)² < c²`). -/
lemma rotatingDiskRimLorentzFactor_pos
    {ω r c : ℝ} (hsub : (ω * r)^2 < c^2) (hc : 0 < c) :
    0 < rotatingDiskRimLorentzFactor ω r c := by
  unfold rotatingDiskRimLorentzFactor
  apply div_pos one_pos
  apply Real.sqrt_pos.mpr
  have hc_sq_pos : 0 < c^2 := pow_pos hc 2
  have h_quot_lt_one : (ω * r)^2 / c^2 < 1 := by
    rw [div_lt_one hc_sq_pos]
    simpa using hsub
  linarith

/-- **Rotating-disk rim Lorentz factor at zero rapidity**:
when `ω · r = 0` (no rim motion), `γ_rim = 1`. -/
lemma rotatingDiskRimLorentzFactor_at_zero_rapidity
    {ω r c : ℝ} (h_zero : ω * r = 0) (_hc : 0 < c) :
    rotatingDiskRimLorentzFactor ω r c = 1 := by
  unfold rotatingDiskRimLorentzFactor
  rw [h_zero]
  simp

/-- **Rotating-disk rim circumference contraction**:

  `C_rim(r, ω) := 2π·r·√(1 − (ω·r)²/c²)`,

the rim circumference of a rigidly rotating disk in special
relativity — the inverse of the rim Lorentz factor.  Port from
Grok survey (line ~711). -/
def rotatingDiskRimCircumference (r ω c : ℝ) : ℝ :=
  2 * Real.pi * r * Real.sqrt (1 - (ω * r)^2 / c^2)

/-- **Rim circumference × rim Lorentz factor = 2π·r**, the
non-relativistic circumference — Ehrenfest's contraction
identity. -/
lemma rotatingDiskRimCircumference_mul_rimLorentzFactor
    {ω r c : ℝ} (hsub : (ω * r)^2 < c^2) (hc : 0 < c) :
    rotatingDiskRimCircumference r ω c
        * rotatingDiskRimLorentzFactor ω r c
      = 2 * Real.pi * r := by
  unfold rotatingDiskRimCircumference rotatingDiskRimLorentzFactor
  have hc_sq_pos : 0 < c^2 := pow_pos hc 2
  have h_arg_pos : 0 < 1 - (ω * r)^2 / c^2 := by
    have : (ω * r)^2 / c^2 < 1 := by
      rw [div_lt_one hc_sq_pos]
      simpa using hsub
    linarith
  have h_sqrt_pos : 0 < Real.sqrt (1 - (ω * r)^2 / c^2) :=
    Real.sqrt_pos.mpr h_arg_pos
  have h_sqrt_ne : Real.sqrt (1 - (ω * r)^2 / c^2) ≠ 0 := ne_of_gt h_sqrt_pos
  rw [show 2 * Real.pi * r * Real.sqrt (1 - (ω * r)^2 / c^2)
        * (1 / Real.sqrt (1 - (ω * r)^2 / c^2))
        = 2 * Real.pi * r
          * (Real.sqrt (1 - (ω * r)^2 / c^2)
              / Real.sqrt (1 - (ω * r)^2 / c^2)) from by ring]
  rw [div_self h_sqrt_ne]
  ring

/-! ## The horizon closes the Verlinde circle: screen temperature = Hawking temperature,
and the Smarr relation in entropic-time form -/

/-- **[Surface gravity is half `c²` over the radius]** `κ = c²/(2·r_s)` — the standard horizon
form of the Schwarzschild surface gravity (`schwarzschildSurfaceGravity`, the existing
`SchwarzschildEntropicRate` carrier). -/
lemma schwarzschildSurfaceGravity_eq_halfc2_over_radius
    {M G c : ℝ} (hM : M ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) :
    schwarzschildSurfaceGravity G M c = c^2 / (2 * schwarzschildRadius M G c) := by
  unfold schwarzschildSurfaceGravity schwarzschildRadius
  field_simp
  ring

/-- **[The Verlinde screen temperature at the horizon IS the Hawking temperature]**
`T_screen(r_s) = T_H`. Evaluating the equipartition screen temperature (Verlinde, over
`N = holographicBits` — `G` in its area-per-bit role) at the Schwarzschild radius gives exactly the
Kay–Wald/Hawking KMS temperature at the horizon surface gravity `κ = c⁴/(4GM)`: both equal
`ℏc³/(8π G M k_B)`. The entropic-gravity screen and the modular-flow KMS state assign the horizon
the *same* temperature — Verlinde's screen thermodynamics meets the entropic-time face on the
same carrier as `ModularErasureCost` and `unruhTemperature_eq_hawkingTemperature`. -/
theorem verlindeTemperature_at_horizon_is_hawking
    {M G ℏ c kB : ℝ} (hM : M ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0) :
    Physlib.Thermodynamics.verlindeGravityTemperature M G ℏ c
        (schwarzschildRadius M G c) kB
      = hawkingTemperature ℏ (schwarzschildSurfaceGravity G M c) c kB := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Physlib.Thermodynamics.verlindeGravityTemperature_def, hawkingTemperature_def]
  unfold schwarzschildRadius schwarzschildSurfaceGravity
  field_simp
  ring

/-- **[The Smarr relation in entropic-time form]** `T_H · (k_B·τ_ent) = M c²/2`. The Hawking
temperature at the Schwarzschild surface gravity times the Bekenstein **entropic time**
`τ_ent = A/(4ℓ_P²)` (in `k_B` units — the quarter-area entropy) is exactly half the mass-energy:
the Smarr formula of black-hole thermodynamics, stated on the entropic-time carrier with `G`
entering only through the Planck area `ℓ_P² = ℏG/c³`. Equipartition over the holographic bits
(`E = ½·N·k_B·T`, Verlinde) is this same identity read backwards. -/
theorem hawking_bekensteinTauEnt_smarr
    {M G ℏ c kB ℓP : ℝ} (hM : M ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0)
    (hkB : kB ≠ 0) (h_ℓP_sq : ℓP^2 = ℏ * G / c^3) :
    hawkingTemperature ℏ (schwarzschildSurfaceGravity G M c) c kB
        * (kB * Physlib.Thermodynamics.bekensteinTauEnt (schwarzschildArea M G c) ℓP)
      = M * c^2 / 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hawkingTemperature_def]
  unfold Physlib.Thermodynamics.bekensteinTauEnt schwarzschildArea schwarzschildSurfaceGravity
  rw [h_ℓP_sq]
  field_simp
  ring

/-- **[The first law of Schwarzschild mechanics, on the entropic-time carrier]**
`d(k_B·τ_ent)/dM = c²/T_H` as a genuine derivative: the Bekenstein entropic time (in Boltzmann
units), as a function of the mass through the horizon area, has derivative
`8πGMk_B/(ℏc)` at `M` — and the Hawking temperature times that derivative is exactly `c²`,
i.e. `δ(Mc²) = T_H·δS`. The static Smarr identity (`hawking_bekensteinTauEnt_smarr`) upgraded to
the first-law **variation**, with `G` still entering only through the Planck area. -/
theorem schwarzschild_first_law
    {M G ℏ c kB ℓP : ℝ} (hM : M ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0)
    (h_ℓP_sq : ℓP ^ 2 = ℏ * G / c ^ 3) :
    HasDerivAt
        (fun m : ℝ => kB * Physlib.Thermodynamics.bekensteinTauEnt (schwarzschildArea m G c) ℓP)
        (8 * Real.pi * G * M * kB / (ℏ * c)) M
      ∧ hawkingTemperature ℏ (schwarzschildSurfaceGravity G M c) c kB
          * (8 * Real.pi * G * M * kB / (ℏ * c)) = c ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · have hpow : HasDerivAt (fun m : ℝ => m ^ 2) (2 * M) M := by
      simpa using hasDerivAt_pow 2 M
    have h1 := hpow.const_mul (kB * (16 * Real.pi * G ^ 2 / c ^ 4) / (4 * ℓP ^ 2))
    have h2 : HasDerivAt
        (fun m : ℝ =>
          kB * Physlib.Thermodynamics.bekensteinTauEnt (schwarzschildArea m G c) ℓP)
        (kB * (16 * Real.pi * G ^ 2 / c ^ 4) / (4 * ℓP ^ 2) * (2 * M)) M :=
      h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun m => by
        unfold Physlib.Thermodynamics.bekensteinTauEnt schwarzschildArea
        ring)
    have hval : kB * (16 * Real.pi * G ^ 2 / c ^ 4) / (4 * ℓP ^ 2) * (2 * M)
        = 8 * Real.pi * G * M * kB / (ℏ * c) := by
      rw [h_ℓP_sq]
      field_simp
      ring
    rw [← hval]
    exact h2
  · rw [hawkingTemperature_def]
    unfold schwarzschildSurfaceGravity
    field_simp
    ring

/-- **[Horizon entropy is strictly increasing in mass — the kinematic half of the second law]**
on `M > 0`, the Bekenstein entropic time in Boltzmann units is strictly monotone in the mass:
more mass, strictly more horizon entropy. Together with the H-theorem-derived non-negativity of
coarse-graining dissipation (`CoarseGrainingStep.tauEnt_nonneg`, the carrier of
`erasure_heat_priced_in_bits`), this is the kinematic content available short of dynamics: any
process that grows the mass grows the entropy, and dissipation never runs negative. The dynamical
second law (evolution) remains the declared frontier of this file's contract. -/
theorem schwarzschild_entropy_strictMonoOn
    {G c kB ℓP : ℝ} (hkB : 0 < kB) (hG : G ≠ 0) (hc : c ≠ 0) (hℓP : ℓP ≠ 0) :
    StrictMonoOn
      (fun m : ℝ => kB * Physlib.Thermodynamics.bekensteinTauEnt (schwarzschildArea m G c) ℓP)
      (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold Physlib.Thermodynamics.bekensteinTauEnt schwarzschildArea
  have hC : 0 < kB * (16 * Real.pi * G ^ 2 / c ^ 4) / (4 * ℓP ^ 2) := by positivity
  have hsq : a ^ 2 < b ^ 2 := by nlinarith
  calc kB * (16 * Real.pi * G ^ 2 * a ^ 2 / c ^ 4 / (4 * ℓP ^ 2))
      = kB * (16 * Real.pi * G ^ 2 / c ^ 4) / (4 * ℓP ^ 2) * a ^ 2 := by ring
    _ < kB * (16 * Real.pi * G ^ 2 / c ^ 4) / (4 * ℓP ^ 2) * b ^ 2 :=
        mul_lt_mul_of_pos_left hsq hC
    _ = kB * (16 * Real.pi * G ^ 2 * b ^ 2 / c ^ 4 / (4 * ℓP ^ 2)) := by ring

/-- **[Mass-nondecreasing processes have nondecreasing horizon entropy]** the `≤`-form of the
kinematic second law: on `M > 0` the horizon entropy is monotone in the mass, so any process whose
mass never decreases never decreases the entropy — the horizon face of the discrete second law
(`processDissipation_take_monotone`, the H-theorem summed along a process). -/
theorem schwarzschild_entropy_monotoneOn
    {G c kB ℓP : ℝ} (hkB : 0 < kB) (hG : G ≠ 0) (hc : c ≠ 0) (hℓP : ℓP ≠ 0) :
    MonotoneOn
      (fun m : ℝ => kB * Physlib.Thermodynamics.bekensteinTauEnt (schwarzschildArea m G c) ℓP)
      (Set.Ioi 0) :=
  (schwarzschild_entropy_strictMonoOn hkB hG hc hℓP).monotoneOn

/-! ## ZIL metadata -/

/-- Link found by `#zil_link`: `comptonTemperature` is `schwarzschildRadius` under `m ↦ M` with conversion `kB^-1 · c^4 · G^-1` and prescription `× 1/4 · π^-1`. -/
theorem comptonTemperature_eq_schwarzschildRadius_scaled (m c kB G : ℝ) (hG : G ≠ 0)
    (hc : c ≠ 0) :
    Physlib.Thermodynamics.comptonTemperature m c kB
      = ((1 / 4 : ℝ) * c ^ 4 / (kB * G * Real.pi)) * Physlib.Relativity.SemiClassical.schwarzschildRadius m G c := by
  unfold Physlib.Thermodynamics.comptonTemperature Physlib.Thermodynamics.deBroglieTemperature
    Physlib.Relativity.SemiClassical.schwarzschildRadius
  field_simp
  ring

/- ZIL-BEGIN -/

zil attach bekensteinTauEnt_eq_holographicBits_div_four where
  formalizes @ "claim:quarter-area-law-as-bits-entropic-time-identity",
  supported_by @ "paper:bekenstein-1973",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  caveat @ "claim:algebraic-identity-under-planck-area-hypothesis"

zil attach schwarzschildArea_holographicBits where
  formalizes @ "claim:schwarzschild-horizon-bit-count-sixteen-pi-g-m-squared-over-hbar-c",
  supported_by @ "paper:verlinde-2010-emergent-gravity"

zil_theorem_intent verlindeTemperature_at_horizon_is_hawking where
  at_level bridge_theorem
  must_mention [Physlib.Thermodynamics.verlindeGravityTemperature, hawkingTemperature]

zil attach verlindeTemperature_at_horizon_is_hawking where
  formalizes @ "claim:verlinde-screen-temperature-at-horizon-is-hawking-temperature",
  requires @ "claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  caveat @ "claim:static-schwarzschild-eigenvalue-identity-not-dynamical-hawking-radiation"

zil_theorem_intent hawking_bekensteinTauEnt_smarr where
  at_level bridge_theorem
  must_mention [hawkingTemperature, Physlib.Thermodynamics.bekensteinTauEnt]

zil attach hawking_bekensteinTauEnt_smarr where
  formalizes @ "claim:smarr-relation-hawking-temperature-times-bekenstein-entropic-time-is-half-mass-energy",
  requires @ "claim:verlinde-screen-temperature-at-horizon-is-hawking-temperature",
  supported_by @ "paper:smarr-1973",
  supported_by @ "paper:bekenstein-1973",
  caveat @ "claim:static-smarr-identity-no-first-law-variation-proven"

zil_theorem_intent schwarzschild_first_law where
  at_level bridge_theorem
  must_mention [hawkingTemperature, Physlib.Thermodynamics.bekensteinTauEnt]

zil attach schwarzschild_first_law where
  formalizes @ "claim:first-law-of-schwarzschild-mechanics-on-entropic-time-carrier",
  requires @ "claim:smarr-relation-hawking-temperature-times-bekenstein-entropic-time-is-half-mass-energy",
  supported_by @ "paper:bardeen-carter-hawking-1973",
  supported_by @ "paper:bekenstein-1973",
  caveat @ "claim:mass-parameter-variation-not-a-dynamical-process"

zil attach schwarzschild_entropy_monotoneOn where
  formalizes @ "claim:mass-nondecreasing-process-has-nondecreasing-horizon-entropy",
  requires @ "claim:horizon-entropy-strictly-increasing-in-mass-kinematic-second-law",
  supported_by @ "paper:bekenstein-1973",
  caveat @ "claim:le-form-of-kinematic-monotonicity-dynamics-still-not-derived"

zil attach schwarzschild_entropy_strictMonoOn where
  formalizes @ "claim:horizon-entropy-strictly-increasing-in-mass-kinematic-second-law",
  requires @ "claim:first-law-of-schwarzschild-mechanics-on-entropic-time-carrier",
  requires @ "claim:erasure-dissipation-nonnegative",
  supported_by @ "paper:bekenstein-1973",
  caveat @ "claim:kinematic-monotonicity-only-dynamical-second-law-remains-the-frontier"

zil_file_contract physlib.schwarzschildVerlinde where
  promises "The Schwarzschild horizon closes the Verlinde circle on existing carriers: the holographic bit count is the horizon area in Planck units, the Bekenstein entropic time is a quarter of the bit count, the Einstein light deflection is twice the Schwarzschild radius over the impact parameter, the Verlinde equipartition screen temperature evaluated at the Schwarzschild radius IS the Hawking KMS temperature at the horizon surface gravity, the Smarr relation holds in entropic-time form with the Hawking temperature times the Bekenstein entropic time in Boltzmann units equal to half the mass-energy, and the first law holds as a genuine variation with the mass-derivative of that entropy times the Hawking temperature equal to c squared, G entering only through the Planck area."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Relativity.SemiClassical.hawkingTemperature",
    "lean:Physlib.Thermodynamics.holographicBits",
    "lean:Physlib.Thermodynamics.bekensteinTauEnt",
    "lean:Physlib.Thermodynamics.verlindeGravityTemperature"]
  forbids_substitutes ["dynamical Hawking radiation or backreaction claimed from static eigenvalue identities",
    "the second law or any dynamical process, which needs evolution not proven here",
    "a first-principles value of G, which enters through the Planck area"]
  witnessed_by [bekensteinTauEnt_eq_holographicBits_div_four, schwarzschildArea_holographicBits,
    einsteinLightDeflection_eq_two_schwarzschildRadius_over_b,
    verlindeTemperature_at_horizon_is_hawking, hawking_bekensteinTauEnt_smarr,
    schwarzschild_first_law, schwarzschild_entropy_strictMonoOn,
    schwarzschild_entropy_monotoneOn]

/- ZIL-END -/

end Physlib.Relativity.SemiClassical

end
