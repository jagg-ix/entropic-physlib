/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWRetardedGreen
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.CalibratedDistance
public import Physlib.Thermodynamics.GravitationalCouplingSystem

/-!
# Electron–positron annihilation through the gravitational-wave equations

`e⁻e⁺ → γγ` analyzed with the linearized-gravity machinery on the tetrad background —
the Feynman–Stückelberg vertex meets the retarded wave equation.  Every step is an
exact identity on existing definitions; nothing kinematic is assumed beyond what the
quoted modules already prove.

* **§A — the vertex.** Charge/baryon/lepton bookkeeping: the initial and final states
  have the *same* additive quantum numbers (`annihilation_quantum_numbers`, from
  `AntiparticleConjugation.electron_positron_annihilate`).  Phase bookkeeping: the
  electron branch times the Feynman–Stückelberg positron branch is a single phase at
  the *total* energy (`annihilation_pair_phase`), and at the Compton frequency that
  total is exactly the rest-frame Zitterbewegung frequency
  (`annihilation_phase_zitterbewegung`) — the interference of the two Dirac branches
  that annihilate is the `ω_Z = 2ω_C` beat (Schrödinger 1930).  Each emitted photon
  sits at `ω_C` on the null shell (`annihilation_photon_onshell`), so the photon mode
  solves the *same* homogeneous d'Alembertian as the gravitational plane wave
  (`annihilation_photon_dalembertian`, instantiating `GWWaveEquation.gw_dalembertian`).

* **§B — the stress-energy jump.** Annihilation converts dust (two rest masses) into
  radiation of the same energy density.  Radiation is traceless exactly at the
  radiation equation of state (`radiation_traceless_iff`, `T = ρc² − 3p = 0` iff
  `p = ρc²/3`), so the trace-reversed source of the linearized Einstein equation loses
  its `½T` subtraction (`radiation_traceReversed_source`) and the annihilation
  *doubles* the effective Poisson source at fixed energy density
  (`annihilation_doubles_poisson_source`, against
  `GravitationalCouplingSystem.dust_traceReversed_source`) — Tolman's `ρ + 3p/c²`
  active mass, the same factor `2` as light bending.  In holographic-bit form the
  doubled source reads `8π·(A/N)/(ℏc)·ρc²` (`annihilation_source_bitForm`).

* **§C — the retarded gravitational signal.** The *change* of the gravitational field
  caused by the annihilation is the retarded Green's solution sourced by the
  stress-energy jump `T_rad − T_dust` (`annihilation_gw_jump`, extending
  `GWRetardedGreen` by the subtractive superposition) — no advanced component, the
  signal propagates causally per `RetardedKernelLightCone`.

* **§D — the curved-spacetime QFT face.** The two annihilation photons are the
  original Bell pair (Wheeler 1946; Wu–Shaknov 1950).  At tetrad proper separation
  `√(xᵀgx)` calibrated to the Schmidt number (`IsEntanglementCalibrated`, the standard
  distance interface), the vacuum CHSH envelope evaluates at the boost velocity
  `tanh η` (`annihilation_bell_calibrated`); and the virtual electron between the two
  photon vertices — the Wick-rotated Feynman–Stückelberg phase at the Compton energy —
  is suppressed by `e^{−√(xᵀgx)/λ_C}` *independently of the local Lorentz frame*
  (`annihilation_virtual_electron_gauge_invariant`, composing
  `wick_rotation_gives_calibration` with `properSeparationSq_lorentz_gauge`).

Honest layering: the annihilation cross-section (Dirac 1930), the quadrupole formula
for the (astrophysically negligible) GW power of a single annihilation event, and the
Wu–Shaknov polarization correlations are *not* formalized; the Green inversion
`□ ∘ I = id` remains the isolated analytic input `hGreen` exactly as in
`GWRetardedGreen`/Heras, and the κ-normalization is consumed from
`GravitationalCouplingSystem`, not rederived.

## References

* E. C. G. Stückelberg, Helv. Phys. Acta 14 (1941) 588; R. P. Feynman, Phys. Rev. 76
  (1949) 749 (the antiparticle branch); M. Thomson, *Modern Particle Physics*,
  Cambridge (2013), Ch. 4 (the annihilation vertex).
* E. Schrödinger, Sitzungsber. Preuss. Akad. Wiss. (1930) 418 (Zitterbewegung as
  interference of the two Dirac branches).
* R. C. Tolman, *Relativity, Thermodynamics and Cosmology*, Oxford (1934), §110
  (`ρ + 3p/c²`; radiation gravitates doubly).
* L. Lusanna, IJGMMP 12 (2015) 1530001, §5 (the retarded GW evolution; modules
  `GWWaveEquation`, `GWRetardedGreen`).
* J. A. Wheeler, Ann. N.Y. Acad. Sci. 48 (1946) 219; C. S. Wu, I. Shaknov, Phys. Rev.
  77 (1950) 136 (annihilation photons as the first entangled pair).
* Repo modules used: `AntiparticleConjugation`, `ComptonClock.FrequencyTrinity`,
  `ComptonClock.CalibratedDistance`, `CanonicalTetradGravity.ComptonVacuumBell`,
  `Thermodynamics.GravitationalCouplingSystem`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.PairAnnihilationGravitationalWave

open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.CalibratedDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWRetardedGreen
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Matrix

/-! ## §A — the annihilation vertex -/

/-- **[Quantum-number conservation at the vertex] `e⁻ + e⁺` and `γγ` have the same
additive quantum numbers.** Both sides are `(0,0,0)` — the annihilation to two photons
is allowed by every additive conservation law
(`electron_positron_annihilate`, `photon_selfConjugate`). -/
theorem annihilation_quantum_numbers : electron + positron = photon + photon := by
  rw [electron_positron_annihilate]
  ext <;> simp [photon]

/-- **[The pair phase equals the total-energy phase] `e^{−iωt}·e^{−i(−ω)(−t)} = e^{−i(2ω)t}`.**
The electron branch times the Feynman–Stückelberg positron branch (negative energy,
backward in time — `feynman_stueckelberg_phase`) is a single phase at the *total*
energy `2ω`: the annihilation vertex hands `2ω` to the photon pair. -/
theorem annihilation_pair_phase (ω t : ℝ) :
    Complex.exp (-Complex.I * ω * t) * Complex.exp (-Complex.I * (-ω : ℝ) * (-t : ℝ))
      = Complex.exp (-Complex.I * (2 * ω : ℝ) * t) := by
  rw [feynman_stueckelberg_phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **[The pair beat is Zitterbewegung] at the Compton frequency the two-branch phase
oscillates at `ω_Z = 2ω_C`.** The interference of the positive- and negative-energy
Dirac branches — the two branches that annihilate — is exactly the rest-frame
Zitterbewegung beat (Schrödinger 1930; `zitterbewegung_rest_eq_two_compton`): the
energy `2mc²` the vertex releases is `ħω_Z`. -/
theorem annihilation_phase_zitterbewegung (m c ħ t : ℝ) (hm : 0 ≤ m) :
    Complex.exp (-Complex.I * comptonFrequency m c ħ * t)
        * Complex.exp (-Complex.I * (-comptonFrequency m c ħ : ℝ) * (-t : ℝ))
      = Complex.exp (-Complex.I * (zitterbewegungFrequency 0 m c ħ : ℝ) * t) := by
  rw [annihilation_pair_phase, zitterbewegung_rest_eq_two_compton m c ħ hm]

/-- **[Each photon rides the null shell at the Compton scale] `ω_C² = c²·(λ_C⁻¹)²`.**
At rest each annihilation photon has `E_γ = mc²`, i.e. angular frequency `ω_C` and
wavenumber `k = 1/λ_C` — and these satisfy the luminal dispersion `ω² = c²k²`
unconditionally (the division-by-zero conventions of `ω_C = mc²/ħ` and `λ_C = ħ/(mc)`
agree). -/
theorem annihilation_photon_onshell (m c ħ : ℝ) :
    comptonFrequency m c ħ ^ 2 = c ^ 2 * ((comptonWavelength m c ħ)⁻¹) ^ 2 := by
  unfold comptonFrequency comptonWavelength
  rw [inv_div]
  ring

/-- **[The photon mode solves the gravitational wave equation] `□R = 0` at
`(ω, k) = (ω_C, 1/λ_C)`.** The annihilation photon's plane-wave mode satisfies the
*same* homogeneous d'Alembertian as the GW plane wave of `GWWaveEquation` — massless
radiation, gravitational or electromagnetic, propagates by one wave operator, so the
GW formalism applies verbatim to the annihilation's radiation zone. -/
theorem annihilation_photon_dalembertian (m c ħ R : ℝ) (hc : c ≠ 0) :
    (1 / c ^ 2) * (-comptonFrequency m c ħ ^ 2 * R)
      - (-((comptonWavelength m c ħ)⁻¹) ^ 2 * R) = 0 :=
  gw_dalembertian ((comptonWavelength m c ħ)⁻¹) (comptonFrequency m c ħ) c R hc
    (annihilation_photon_onshell m c ħ)

/-! ## §B — the stress-energy jump: dust into radiation -/

/-- **[Traceless ⟺ radiation equation of state] `ρc² − 3p = 0 ↔ p = ρc²/3`.** The
photon gas produced by annihilation is exactly the traceless stress-energy — the
equation of state `p = ρc²/3` *is* the vanishing of the trace. -/
theorem radiation_traceless_iff (ρ c p : ℝ) :
    ρ * c ^ 2 - 3 * p = 0 ↔ p = ρ * c ^ 2 / 3 := by
  constructor <;> intro h <;> linarith

/-- **[The trace-reversed source of radiation] `κ·(T₀₀ − ½T) = 8πGρ/c²`.** At the
radiation equation of state the trace subtraction vanishes and the full `T₀₀ = ρc²`
sources the linearized Einstein equation — twice the dust value
`κ·(ρc²/2) = 4πGρ/c²` of `dust_traceReversed_source`. -/
theorem radiation_traceReversed_source (G c ρ p : ℝ) (hc : c ≠ 0)
    (h : p = ρ * c ^ 2 / 3) :
    (8 * Real.pi * G / c ^ 4) * (ρ * c ^ 2 - (ρ * c ^ 2 - 3 * p) / 2)
      = 8 * Real.pi * G * ρ / c ^ 2 := by
  rw [h]
  field_simp
  ring

/-- **[Annihilation doubles the Poisson source] radiation gravitates twice as strongly
as dust of equal energy density.** `e⁻e⁺ → γγ` at fixed local energy density replaces
the dust source `T₀₀ − ½T = ½ρc²` by the traceless radiation source `ρc²`: Tolman's
active gravitational mass `ρ + 3p/c² = 2ρ`, the same factor `2` as the deflection of
light — the gravitational field *knows* the annihilation happened even though energy
is conserved. -/
theorem annihilation_doubles_poisson_source (G c ρ p : ℝ) (hc : c ≠ 0)
    (h : p = ρ * c ^ 2 / 3) :
    (8 * Real.pi * G / c ^ 4) * (ρ * c ^ 2 - (ρ * c ^ 2 - 3 * p) / 2)
      = 2 * ((8 * Real.pi * G / c ^ 4) * (ρ * c ^ 2 / 2)) := by
  rw [radiation_traceReversed_source G c ρ p hc h, dust_traceReversed_source G c ρ hc]
  ring

/-- **[The radiation source in holographic-bit form] `κ·ρc² = 8π·(A/N)/(ℏc)·ρc²`.**
The annihilation's doubled source, with the Einstein coupling written as `8π` Planck
areas-per-bit over `ℏc` (`einsteinCoupling_bitForm`) — the gravitational response to
the annihilation counted in holographic bits. -/
theorem annihilation_source_bitForm (G ℏ c N R ρ p : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c) (h : p = ρ * c ^ 2 / 3) :
    (8 * Real.pi * G / c ^ 4) * (ρ * c ^ 2 - (ρ * c ^ 2 - 3 * p) / 2)
      = (8 * Real.pi * (sphereArea R / N) / (ℏ * c)) * (ρ * c ^ 2) := by
  rw [show ρ * c ^ 2 - (ρ * c ^ 2 - 3 * p) / 2 = ρ * c ^ 2 from by rw [h]; ring,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hN]

/-! ## §C — the retarded gravitational signal of the annihilation -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **[The gravitational signal is the retarded solution of the stress-energy jump]
`□(R_after − R_before) = T_rad − T_dust`.** The *change* of the gravitational field
caused by the annihilation — retarded radiation field minus retarded dust field — is
itself a retarded Green's solution, sourced by the stress-energy jump (the subtractive
face of the `GWRetardedGreen` superposition).  No advanced component: the signal that
the pair annihilated propagates causally, on the light cone of
`RetardedKernelLightCone`, alongside the photons themselves. -/
theorem annihilation_gw_jump (box I : V →ₗ[ℝ] V) (hGreen : ∀ s, box (I s) = s)
    (Tdust Trad : V) :
    box (gwRetarded I Trad - gwRetarded I Tdust) = Trad - Tdust := by
  unfold gwRetarded
  rw [← map_sub]
  exact hGreen _

/-! ## §D — the annihilation photons as a Bell pair on the tetrad -/

variable {d : ℕ}

/-- **[The annihilation Bell pair at calibrated proper separation] the CHSH envelope
evaluates at the boost velocity `tanh η`.** The two annihilation photons are the
original Bell pair (Wheeler 1946; Wu–Shaknov 1950).  When their tetrad proper
separation `√(xᵀgx)` is calibrated to the Schmidt number (`IsEntanglementCalibrated`
at the standard `λ_C`), the vacuum Bell envelope of `ComptonVacuumBell` becomes the
envelope at `tanh η` — the Bell decay measured at GR proper distance *is* the boost
velocity of the entanglement arc, on the curved background. -/
theorem annihilation_bell_calibrated (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (C₀ m c ħ η : ℝ) (hη : 0 < η)
    (h : IsEntanglementCalibrated (Real.sqrt (properSeparationSq E x))
      (comptonWavelength m c ħ) (schmidtNumber η))
    (hℓ : comptonWavelength m c ħ ≠ 0) :
    chshEnvelope (C₀ * Real.exp
        (-(Real.sqrt (properSeparationSq E x) / comptonWavelength m c ħ)))
      = chshEnvelope (C₀ * Real.tanh η) := by
  rw [calibrated_vacuumBell hη h hℓ]

/-- **[The virtual electron between the two vertices is a Lorentz scalar]** the
Wick-rotated Feynman–Stückelberg phase at the Compton energy, evaluated at the tetrad
proper separation of the two photon-emission vertices, equals the calibration decay
`e^{−√(xᵀgx)/λ_C}` — and the local Lorentz frame drops out
(`properSeparationSq_lorentz_gauge`): the spacelike suppression of the virtual
electron line in `e⁻e⁺ → γγ` is a frame-independent observable on the curved
background, the same exponential whose real-time branches are the annihilating pair
(`wick_rotation_gives_calibration`). -/
theorem annihilation_virtual_electron_gauge_invariant
    {Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ} (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (m c ħ : ℝ) :
    Complex.exp (-Complex.I * ((m * c ^ 2 / ħ : ℝ) : ℂ)
        * (-Complex.I * ((Real.sqrt (properSeparationSq (Λ * E) x) / c : ℝ) : ℂ)))
      = ((Real.exp
          (-(Real.sqrt (properSeparationSq E x) / comptonWavelength m c ħ)) : ℝ) : ℂ) := by
  rw [wick_rotation_gives_calibration m c ħ (Real.sqrt (properSeparationSq (Λ * E) x)),
    properSeparationSq_lorentz_gauge hΛ]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.PairAnnihilationGravitationalWave

end
