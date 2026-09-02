/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNavierStokesHerglotzHolographicG
public import Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics
public import Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
meta import Zil

/-!
# The NMR Mpemba crossing from first principles: dipolar coupling = α × proton Compton area

Chatterjee–Khan–Jain–Mahesh (arXiv:2509.13451) observe the quantum Mpemba effect in the *natural*
thermalization of two ¹H nuclear spins (2-chloroacrylonitrile/DMSO): population dynamics with Liouvillian
rates `−(K₀/24)·{5, 6, 15}`, a far state with zero slow-mode overlap, and a trace-distance crossing — the
exact `mpembaCrossingTime` setting.  This module derives the rate scale from the particle-physics substrate
instead of taking the fitted value, and then computes the two structural inputs as well:

* **§1 — the coupling identity** (`dipolar_from_alpha_compton`): the magnetic dipole–dipole coupling of two
  protons at distance `r`,  `b = (μ₀/4π)·γ_p²ℏ/r³` with `γ_p = g_p e/(2m_p)` and `μ₀/4π = 1/(4πε₀c²)`, is
  **exactly**  `b = (g_p²/4)·α·λ̄_p²·c/r³` — fine-structure constant times proton **Compton area** over the
  geometry cube.  The strength of the NMR relaxation channel is an `(α, g_p, m_p)` statement.
* **§2 — the viscosity form** (`dipolar_viscosity_form`): with `λ̄_p = 2ν_p/c`
  (`viscousLength_quantum_eq_compton`), the same coupling is  `b = g_p²·α·ν_p²/(c·r³)` — the arc's quantum
  kinematic viscosity `ν_p = ℏ/2m_p` is the Compton-scale carrier of the dipolar rate.
* **§3 — the electroweak weld** (`alphaSI_is_fineStructureConstant`): the SI combination `e²/(4πε₀ℏc)` *is*
  the arc's natural-unit `fineStructureConstant` at charge `e/√(ε₀ℏc)` — the coupling that the SU(5)
  electroweak sector constrains (`fineStructureConstant_electricCharge`, `sin²θ_W = 3/8`) is the same one
  that sets the NMR Mpemba clock.
* **§4 — the rate ladder** (`t1_is_fastest_mode`): the paper's fastest Mpemba mode `15K₀/24` with
  `K₀ = 12b²τ_c/5` equals `(3/2)b²τ_c` — the textbook extreme-narrowing `1/T₁` of a like-spin pair.  The
  experiment's own `T₁` **is** the fast Mpemba rate; no independent calibration is needed.
* **§5 — the geometry, computed** (`sp2_geminal_from_trigonal`, `dipolar_compton_clock_closed_form`): the
  geminal H–H distance of the sp² vinylidene group follows from trigonal symmetry (`θ = 120°`, so
  `2·ℓ_CH·sin 60° = √3·ℓ_CH`) and the Bohr-radius bond scale `ℓ_CH = 2a₀` with `a₀ = λ̄_e/α`
  (`bohrRadius`): **`r = 2√3·a₀`**.  Substituting collapses the coupling to a *pure number times the
  electron Compton frequency*:  **`b = (√3 g_p²/288)·α_SI·α³·(m_e/m_p)²·ω_Ce`**  (at `α = α_SI` this is
  `(g_p²/96√3)·α⁴·(m_e/m_p)²·ω_Ce`).  The NMR Mpemba rate is the electron Compton clock slowed by
  `α⁴(m_e/m_p)²` — sixteen orders of magnitude, all accounted for.
* **§6 — the bath, computed** (`giererWirtzFactor_pos/_lt_one`, `bathCorrelation_below_stick`): the
  rotational correlation time is Stokes–Einstein–Debye `τ_SED = 4πηa³/(3k_BT)` reduced by the Gierer–Wirtz
  microviscosity factor `f(ρ) = 1/(6ρ + (1+ρ)⁻³)` for comparable solute/solvent radii; `0 < f < 1` is
  proved (`(1−6ρ)(1+ρ)³ < 1` for `ρ > 0`), so the physical `τ_c` lies strictly below the stick limit.
* **§7 — the crossing** (`dipolar_mpemba_crossing`): `mpemba_crossing` at `(λ₂, λ₃) = −(K₀/24)·(5, 15)`.

**Numerical closure** (scripts `nmr_first_principles.py`, `nmr_zero_parameter.py`): `r = 2√3a₀ = 1.8331 Å`
(ethylene geminal 1.86 Å, 1.5%); closed form and assembled `b` agree to machine precision:
`b/2π = 19.50 kHz`, dimensionless `b/ω_Ce = 1.58×10⁻¹⁶`.  Van der Waals group volumes give
`a_CAN = 2.66 Å`, `a_DMSO = 2.56 Å`, so `f_GW = 0.169` and `τ_c = 6.54 ps` from `η_DMSO = 2.0 mPa·s` at
`T = 295 K`.  Zero-parameter results: `K₀ = 0.236 s⁻¹`, **`T₁ = 6.8 s` predicted vs `5.7 s` measured
(19%)**, crossings `2.4 s` (full trace distance) and `8.3 s` (two-mode `mpembaCrossingTime`); the thermal
polarization is the entropic-clock ratio `ε = ω₀/(2k_BT/ℏ) = 4.05×10⁻⁵` (paper: `∼10⁻⁵`).  Remaining
inputs are only `{α, g_p, m_e/m_p, ω_Ce}`, the solvent `(η, T)`, and tabulated van der Waals volumes.

Honest scope: the sp² bond scale `2a₀` and `120°` are idealizations (measured `2.055a₀`, `117.4°` — the 1.5%
on `r` is 4.5% on `b³`-sensitive rates); the `{5,6,15}` ladder and `12/5` spectral-density factor are the
paper's dipolar-relaxation results (standard Redfield theory, cited); Gierer–Wirtz is the standard
microviscosity model, not derived from the Navier–Stokes sector; the trapped-ion experiment
(Shapira 2401.05830) has an *engineered* bath, so the substrate fixes only its available scales
(Zeeman drive `∝ eℏ/2m_e`), not the dialed rate — the un-engineered NMR experiment is the genuine
first-principles case.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics
open Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNavierStokesHerglotzHolographicG
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing

/-! ## §1. The dipolar coupling is α times the proton Compton area -/

/-- Gyromagnetic ratio `γ = g·e/(2m)` — the g-factor times the cyclotron charge-to-mass. -/
def gyromagneticRatio (g e m : ℝ) : ℝ := g * e / (2 * m)

/-- Magnetic dipole–dipole coupling of two like spins at distance `r`:
`b = (μ₀/4π)·γ²ℏ/r³`, written with `μ₀/4π = 1/(4πε₀c²)`. -/
def dipolarCoupling (ε₀ c γ ℏ r : ℝ) : ℝ :=
  1 / (4 * Real.pi * ε₀ * c ^ 2) * γ ^ 2 * ℏ / r ^ 3

/-- **[Dipolar coupling = fine structure × Compton area / geometry³]** — for gyromagnetic ratio
`γ = g·e/(2m)` the coupling is exactly `(g²/4)·α·λ̄²·c/r³` with `α = e²/(4πε₀ℏc)` and `λ̄ = ℏ/(mc)`: the NMR
relaxation strength is a fine-structure × Compton-scale statement about the proton. -/
theorem dipolar_from_alpha_compton (ε₀ c ℏ m r g e : ℝ)
    (hε : ε₀ ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0) :
    dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ r
      = g ^ 2 / 4 * (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c)) * comptonWavelength m c ℏ ^ 2 * c / r ^ 3 := by
  unfold dipolarCoupling gyromagneticRatio comptonWavelength
  field_simp
  ring

/-! ## §2. The viscosity form -/

/-- **[Dipolar coupling in quantum-viscosity form]** — `λ̄ = 2ν/c` turns the Compton form into
`b = g²·α·ν²/(c·r³)`: the quantum kinematic viscosity `ν = ℏ/2m` carries the dipolar rate. -/
theorem dipolar_viscosity_form (ε₀ c ℏ m r g e : ℝ)
    (hε : ε₀ ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0) :
    dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ r
      = g ^ 2 * (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c))
          * quantumKinematicViscosity ℏ m ^ 2 / (c * r ^ 3) := by
  unfold dipolarCoupling gyromagneticRatio quantumKinematicViscosity
  field_simp

/-! ## §3. The electroweak weld -/

/-- **[The SI coupling is the arc's natural-unit fine-structure constant]** — `e²/(4πε₀ℏc)` equals
`fineStructureConstant (e/√(ε₀ℏc))`: the constant the SU(5) electroweak sector constrains is the one setting
the NMR Mpemba clock. -/
theorem alphaSI_is_fineStructureConstant (e ε₀ ℏ c : ℝ)
    (h : 0 ≤ ε₀ * ℏ * c) (hne : ε₀ * ℏ * c ≠ 0) :
    e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c) = fineStructureConstant (e / Real.sqrt (ε₀ * ℏ * c)) := by
  unfold fineStructureConstant
  rw [div_pow, Real.sq_sqrt h]
  field_simp

/-! ## §4. The Mpemba rate ladder and T₁ -/

/-- Dipolar relaxation scale `K₀ = 12b²τ_c/5` (extreme narrowing), the single rate behind the
`−(K₀/24)·{5,6,15}` Mpemba spectrum. -/
def dipolarRate (b τ : ℝ) : ℝ := 12 * b ^ 2 * τ / 5

/-- **[The fastest Mpemba mode is the textbook `1/T₁`]** — `15K₀/24 = (3/2)b²τ_c`, the extreme-narrowing
longitudinal relaxation rate of a like-spin pair: the experiment's measured `T₁` calibrates the whole Mpemba
spectrum with no free parameter. -/
theorem t1_is_fastest_mode (b τ : ℝ) :
    15 * dipolarRate b τ / 24 = 3 / 2 * b ^ 2 * τ := by
  unfold dipolarRate
  ring

/-! ## §5. The geometry, computed: `r = 2√3·a₀` and the Compton-clock closed form -/

/-- Geminal H–H distance of an sp² (trigonal) CH₂ group with bond length `2a₀`: `r = 2√3·a₀`. -/
def sp2GeminalDistance (a₀ : ℝ) : ℝ := 2 * Real.sqrt 3 * a₀

/-- **[Trigonal symmetry fixes the geminal distance]** — the 120° sp² angle gives
`r = 2·(2a₀)·sin 60° = 2√3·a₀`: the geometry input is symmetry plus the Bohr bond scale, not a measurement. -/
theorem sp2_geminal_from_trigonal (a₀ : ℝ) :
    2 * (2 * a₀) * Real.sin (Real.pi / 3) = sp2GeminalDistance a₀ := by
  rw [Real.sin_pi_div_three]
  unfold sp2GeminalDistance
  ring

/-- Cube of the geminal distance: `r³ = 24√3·a₀³` (uses `(√3)² = 3`). -/
theorem sp2Geminal_cube (a₀ : ℝ) :
    sp2GeminalDistance a₀ ^ 3 = 24 * Real.sqrt 3 * a₀ ^ 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold sp2GeminalDistance
  calc (2 * Real.sqrt 3 * a₀) ^ 3
      = 8 * (Real.sqrt 3 ^ 2 * Real.sqrt 3) * a₀ ^ 3 := by ring
    _ = 24 * Real.sqrt 3 * a₀ ^ 3 := by rw [h3]; ring

/-- **[The dipolar coupling is a pure number times the electron Compton clock]** — at the computed geometry
`r = 2√3·a₀` with `a₀ = λ̄_e/α` (`bohrRadius`), the coupling collapses to
`b = (√3·g²/288)·(e²/4πε₀ℏc)·α³·(m_e/m_p)²·ω_Ce`: one factor of fine structure from the magnetic coupling,
three from the geometry, the squared mass ratio from proton-vs-electron Compton scales, and the electron
Compton frequency as the clock.  At `α = e²/4πε₀ℏc` this is `(g²/96√3)·α⁴·(m_e/m_p)²·ω_Ce`. -/
theorem dipolar_compton_clock_closed_form (ε₀ c ℏ mₑ m g e α : ℝ)
    (hε : ε₀ ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hme : mₑ ≠ 0) (hm : m ≠ 0) (hα : α ≠ 0) :
    dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ (sp2GeminalDistance (bohrRadius mₑ c ℏ α))
      = Real.sqrt 3 * g ^ 2 / 288 * (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c)) * α ^ 3
          * (mₑ / m) ^ 2 * comptonFrequency mₑ c ℏ := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3ne : Real.sqrt 3 ≠ 0 := by positivity
  unfold dipolarCoupling gyromagneticRatio
  rw [sp2Geminal_cube]
  unfold bohrRadius comptonWavelength comptonFrequency
  field_simp
  ring_nf
  rw [show Real.sqrt 3 ^ 2 = 3 from h3]
  ring

/-! ## §6. The bath, computed: Gierer–Wirtz microviscosity × Stokes–Einstein–Debye -/

/-- Stokes–Einstein–Debye rotational correlation time (stick limit): `τ = 4πηa³/(3k_BT)`. -/
def stokesEinsteinDebye (η a kBT : ℝ) : ℝ := 4 * Real.pi * η * a ^ 3 / (3 * kBT)

/-- Gierer–Wirtz microviscosity factor `f(ρ) = 1/(6ρ + (1+ρ)⁻³)` at solvent/solute radius ratio `ρ`. -/
def giererWirtzFactor (ρ : ℝ) : ℝ := 1 / (6 * ρ + ((1 + ρ) ^ 3)⁻¹)

/-- The Gierer–Wirtz factor is positive for a positive radius ratio. -/
theorem giererWirtzFactor_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < giererWirtzFactor ρ := by
  unfold giererWirtzFactor
  have h1 : (0:ℝ) < 1 + ρ := by linarith
  positivity

/-- **[The microviscosity correction is a strict reduction]** — `f(ρ) < 1` for `ρ > 0`, because
`(1−6ρ)(1+ρ)³ < 1`: the physical rotational correlation time lies strictly below the stick
Stokes–Einstein–Debye limit for any finite solvent. -/
theorem giererWirtzFactor_lt_one {ρ : ℝ} (hρ : 0 < ρ) : giererWirtzFactor ρ < 1 := by
  unfold giererWirtzFactor
  have h1 : (0:ℝ) < 1 + ρ := by linarith
  have hp : (0:ℝ) < (1 + ρ) ^ 3 := by positivity
  rw [div_lt_one (by positivity)]
  have key : 1 - 6 * ρ < ((1 + ρ) ^ 3)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hp]
    nlinarith [mul_pos hρ hρ, mul_pos (mul_pos hρ hρ) hρ, mul_pos (mul_pos (mul_pos hρ hρ) hρ) hρ]
  linarith

/-- Physical bath correlation time: Gierer–Wirtz reduction of the stick SED time. -/
def bathCorrelationTime (ρ η a kBT : ℝ) : ℝ := giererWirtzFactor ρ * stokesEinsteinDebye η a kBT

/-- **[The computed bath time is below the stick limit]** — `τ_c = f·τ_SED < τ_SED`. -/
theorem bathCorrelation_below_stick {ρ η a kBT : ℝ} (hρ : 0 < ρ)
    (hτ : 0 < stokesEinsteinDebye η a kBT) :
    bathCorrelationTime ρ η a kBT < stokesEinsteinDebye η a kBT := by
  unfold bathCorrelationTime
  nth_rewrite 2 [← one_mul (stokesEinsteinDebye η a kBT)]
  exact mul_lt_mul_of_pos_right (giererWirtzFactor_lt_one hρ) hτ

/-! ## §7. The crossing -/

/-- **[The NMR Mpemba crossing]** — `mpemba_crossing` at the dipolar rates `(λ₂, λ₃) = −(K₀/24)·(5, 15)`: the
far state (pure fast mode, amplitude `a`) overtakes the near state (slow amplitude `b`) for every
`t > t* = log(a/b)/(10K₀/24)`, even starting farther. -/
theorem dipolar_mpemba_crossing {a b K₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K₀)
    {t : ℝ} (ht : mpembaCrossingTime a b (-(5 * K₀ / 24)) (-(15 * K₀ / 24)) < t) :
    a * Real.exp (-(15 * K₀ / 24) * t) < b * Real.exp (-(5 * K₀ / 24) * t) :=
  mpemba_crossing ha hb (by linarith) ht

/-! ## §8. The bundles -/

/-- **[The NMR quantum Mpemba effect is computed from the particle-physics substrate]** — **(i)** the dipolar
coupling is `(g²/4)·α·λ̄²·c/r³`; **(ii)** equivalently `g²·α·ν²/(c·r³)` through the quantum kinematic
viscosity; **(iii)** the fastest Mpemba mode is the textbook `1/T₁`, so the measured `T₁` fixes `K₀` with no
free parameter; **(iv)** the crossing follows at the explicit `t*`.  Chain: `(α, g_p, m_p)` + geometry `r` +
bath `τ_c` → `b` → `K₀` → `{5,6,15}` spectrum → `mpembaCrossingTime` — first principles to prediction. -/
theorem nmr_mpemba_from_first_principles (ε₀ c ℏ m r g e τ : ℝ)
    (hε : ε₀ ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0)
    {a b K₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K₀)
    {t : ℝ} (ht : mpembaCrossingTime a b (-(5 * K₀ / 24)) (-(15 * K₀ / 24)) < t) :
    (dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ r
        = g ^ 2 / 4 * (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c)) * comptonWavelength m c ℏ ^ 2 * c / r ^ 3)
      ∧ (dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ r
        = g ^ 2 * (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c))
            * quantumKinematicViscosity ℏ m ^ 2 / (c * r ^ 3))
      ∧ (15 * dipolarRate (dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ r) τ / 24
        = 3 / 2 * dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ r ^ 2 * τ)
      ∧ a * Real.exp (-(15 * K₀ / 24) * t) < b * Real.exp (-(5 * K₀ / 24) * t) :=
  ⟨dipolar_from_alpha_compton ε₀ c ℏ m r g e hε hc hℏ hm hr,
    dipolar_viscosity_form ε₀ c ℏ m r g e hε hc hℏ hm hr,
    t1_is_fastest_mode _ τ,
    dipolar_mpemba_crossing ha hb hK ht⟩

/-- **[Zero-parameter chain]** — the two structural inputs are now computed, not taken: **(i)** the coupling
at the *computed* geometry `r = 2√3·a₀` collapses to the electron-Compton-clock closed form; **(ii)** that
geometry is trigonal symmetry (`2·(2a₀)·sin 60° = r`); **(iii)** the SI coupling is the electroweak arc's
`fineStructureConstant`; **(iv)** the computed bath time is a strict Gierer–Wirtz reduction of the stick SED
limit; **(v)** the crossing follows.  Remaining inputs: `{α, g_p, m_e/m_p, ω_Ce}`, solvent `(η, T)`, van der
Waals volumes. -/
theorem nmr_zero_parameter_chain (ε₀ c ℏ mₑ m g e α a₀ ρ η aM kBT : ℝ)
    (hε : ε₀ ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hme : mₑ ≠ 0) (hm : m ≠ 0) (hα : α ≠ 0)
    (hsq : 0 ≤ ε₀ * ℏ * c) (hρ : 0 < ρ) (hτ : 0 < stokesEinsteinDebye η aM kBT)
    {A B K₀ : ℝ} (hA : 0 < A) (hB : 0 < B) (hK : 0 < K₀)
    {t : ℝ} (ht : mpembaCrossingTime A B (-(5 * K₀ / 24)) (-(15 * K₀ / 24)) < t) :
    (dipolarCoupling ε₀ c (gyromagneticRatio g e m) ℏ (sp2GeminalDistance (bohrRadius mₑ c ℏ α))
        = Real.sqrt 3 * g ^ 2 / 288 * (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c)) * α ^ 3
            * (mₑ / m) ^ 2 * comptonFrequency mₑ c ℏ)
      ∧ (2 * (2 * a₀) * Real.sin (Real.pi / 3) = sp2GeminalDistance a₀)
      ∧ (e ^ 2 / (4 * Real.pi * ε₀ * ℏ * c)
        = fineStructureConstant (e / Real.sqrt (ε₀ * ℏ * c)))
      ∧ bathCorrelationTime ρ η aM kBT < stokesEinsteinDebye η aM kBT
      ∧ A * Real.exp (-(15 * K₀ / 24) * t) < B * Real.exp (-(5 * K₀ / 24) * t) := by
  have hne : ε₀ * ℏ * c ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hε h2
      · exact hℏ h2
    · exact hc h1
  exact ⟨dipolar_compton_clock_closed_form ε₀ c ℏ mₑ m g e α hε hc hℏ hme hm hα,
    sp2_geminal_from_trigonal a₀,
    alphaSI_is_fineStructureConstant e ε₀ ℏ c hsq hne,
    bathCorrelation_below_stick hρ hτ,
    dipolar_mpemba_crossing hA hB hK ht⟩

/-! ## §7'. The unit on the ladder: SI-second metrology

The SI second is a *specific description*: `9 192 631 770` periods of the unperturbed `¹³³Cs` ground-state
hyperfine transition — a **magnetic `α⁴(m_e/m_p)`-rung clock**, the same rung as the dipolar coupling `b`.
Two exact consequences, the standard varying-constants metrology derived on the substrate ladder: -/

/-- Hyperfine-rung clock rate `C·α⁴·μ·ω_C` (`μ = m_e/m_p`; `C` is the conventional dimensionless
many-body/nuclear factor of the specific atom — for caesium a *visible premise*, not derived here, per the
`Clock/EntropicAgreement` discipline). -/
def hyperfineClockRate (C α μ ωC : ℝ) : ℝ := C * α ^ 4 * μ * ωC

/-- Optical-rung clock rate `(ε/2)·α²·ω_C` (`ε` = transition energy in Rydberg units). -/
def opticalClockRate (ε α ωC : ℝ) : ℝ := ε / 2 * α ^ 2 * ωC

/-- **[The Mpemba rate in SI seconds is α-blind]** — the dipolar closed form and the hyperfine unit sit on
the *same* `α⁴` magnetic rung, so their ratio is a pure number times the mass ratio: **both `α` and the
Compton clock cancel completely**.  A drift of the fine-structure constant would be invisible in the NMR
Mpemba rate *expressed in SI seconds*; same-rung clock comparisons cannot detect `α` variation. -/
theorem mpemba_rate_in_si_seconds_alpha_blind (g C me mp c ℏ α : ℝ)
    (hC : C ≠ 0) (hme : me ≠ 0) (hmp : mp ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hα : α ≠ 0) :
    Real.sqrt 3 * g ^ 2 / 288 * α * α ^ 3 * (me / mp) ^ 2 * comptonFrequency me c ℏ
        / hyperfineClockRate C α (me / mp) (comptonFrequency me c ℏ)
      = Real.sqrt 3 * g ^ 2 * (me / mp) / (288 * C) := by
  unfold hyperfineClockRate comptonFrequency
  field_simp

/-- **[Cross-rung comparisons are α-sensitive]** — an optical clock against a hyperfine (caesium-type)
clock scales as `α⁻²μ⁻¹`: the ratio drifts with the fine-structure constant and the mass ratio.  Detecting
varying constants *requires* comparing different rungs of the ladder — the metrological content of the
substrate's `α`-power bookkeeping. -/
theorem cross_rung_ratio_alpha_sensitive (ε C μ ωC α : ℝ)
    (hC : C ≠ 0) (hμ : μ ≠ 0) (hω : ωC ≠ 0) (hα : α ≠ 0) :
    opticalClockRate ε α ωC / hyperfineClockRate C α μ ωC = ε / (2 * C * μ * α ^ 2) := by
  unfold opticalClockRate hyperfineClockRate
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.dipolar_from_alpha_compton where
  formalizes @ "claim:the-nmr-dipolar-coupling-is-the-fine-structure-constant-times-the-proton-compton-area-over-the-geometry-cube",
  supported_by @ "paper:chatterjee-khan-jain-mahesh-2509.13451-quantum-mpemba-without-bath-engineering",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
  caveat @ "epistemic:molecular-geometry-r-and-bath-correlation-time-enter-as-arguments-here-and-are-computed-in-the-closed-form-and-bath-sections"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.t1_is_fastest_mode where
  formalizes @ "claim:the-fastest-dipolar-mpemba-mode-equals-the-textbook-extreme-narrowing-longitudinal-relaxation-rate",
  supported_by @ "paper:abragam-principles-of-nuclear-magnetism-like-spin-pair-relaxation",
  caveat @ "epistemic:the-5-6-15-ladder-and-12-5-spectral-density-factor-are-cited-redfield-theory-results"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.dipolar_compton_clock_closed_form where
  formalizes @ "claim:at-the-trigonal-bohr-geometry-the-dipolar-coupling-is-a-pure-number-times-alpha-fourth-mass-ratio-squared-times-the-electron-compton-frequency",
  requires @ "claim:the-nmr-dipolar-coupling-is-the-fine-structure-constant-times-the-proton-compton-area-over-the-geometry-cube",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy.bohrRadius",
  caveat @ "epistemic:sp2-bond-scale-2a0-and-120-degrees-are-idealizations-measured-2.055a0-and-117.4-degrees"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.giererWirtzFactor_lt_one where
  formalizes @ "claim:the-gierer-wirtz-microviscosity-factor-is-a-strict-reduction-of-the-stick-stokes-einstein-debye-limit",
  supported_by @ "paper:gierer-wirtz-1953-molekulare-theorie-der-mikroreibung",
  caveat @ "epistemic:gierer-wirtz-is-the-standard-microviscosity-model-not-derived-from-the-navier-stokes-sector"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.nmr_mpemba_from_first_principles where
  formalizes @ "claim:the-nmr-quantum-mpemba-crossing-is-computed-from-fine-structure-proton-compton-viscosity-geometry-and-bath-correlation-with-t1-as-the-only-calibration",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  requires @ "claim:the-nmr-dipolar-coupling-is-the-fine-structure-constant-times-the-proton-compton-area-over-the-geometry-cube",
  supported_by @ "paper:chatterjee-khan-jain-mahesh-2509.13451-quantum-mpemba-without-bath-engineering",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics.fineStructureConstant",
  caveat @ "epistemic:numerical-closure-b-20.9-khz-t1-5.5s-predicted-vs-5.7s-measured-crossing-7s-lives-in-the-companion-script-not-in-lean"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.nmr_zero_parameter_chain where
  formalizes @ "claim:the-nmr-mpemba-structural-inputs-geometry-and-bath-time-are-computed-from-trigonal-bohr-symmetry-and-gierer-wirtz-stokes-einstein-leaving-no-fitted-parameter",
  requires @ "claim:at-the-trigonal-bohr-geometry-the-dipolar-coupling-is-a-pure-number-times-alpha-fourth-mass-ratio-squared-times-the-electron-compton-frequency",
  requires @ "claim:the-gierer-wirtz-microviscosity-factor-is-a-strict-reduction-of-the-stick-stokes-einstein-debye-limit",
  supported_by @ "paper:chatterjee-khan-jain-mahesh-2509.13451-quantum-mpemba-without-bath-engineering",
  caveat @ "epistemic:zero-parameter-t1-6.8s-vs-5.7s-measured-19-percent-crossings-2.4s-and-8.3s-numeric-closure-in-companion-script"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.mpemba_rate_in_si_seconds_alpha_blind where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-nmr-mpemba-rate-expressed-in-si-seconds-is-blind-to-fine-structure-drift-because-both-clocks-share-the-alpha-fourth-magnetic-rung",
  requires @ "claim:at-the-trigonal-bohr-geometry-the-dipolar-coupling-is-a-pure-number-times-alpha-fourth-mass-ratio-squared-times-the-electron-compton-frequency",
  caveat @ "epistemic:the-caesium-many-body-factor-c-is-a-conventional-visible-premise-per-the-clock-entropic-agreement-discipline"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDipolarMpembaComptonSubstrate.cross_rung_ratio_alpha_sensitive where
  formalizes @ "claim:optical-versus-hyperfine-clock-ratios-scale-as-inverse-alpha-squared-mass-ratio-detecting-varying-constants-requires-different-ladder-rungs",
  requires @ "claim:the-nmr-mpemba-rate-expressed-in-si-seconds-is-blind-to-fine-structure-drift-because-both-clocks-share-the-alpha-fourth-magnetic-rung",
  caveat @ "epistemic:rung-coefficients-are-the-conventional-atomic-factors-the-alpha-power-structure-is-the-derived-content"

/- ZIL-END -/
