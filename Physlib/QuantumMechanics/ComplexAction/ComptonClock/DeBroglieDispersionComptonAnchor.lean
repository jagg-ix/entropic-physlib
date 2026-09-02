/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
meta import Zil

/-!
# De Broglie 1924, the unexploited remainder: dispersion and the Compton anchor

Two quantitative results of de Broglie's thesis (*Recherches sur la théorie des quanta*,
1925; Kracklauer tr.) had no formal counterpart in the library.  This module lands both,
and the second closes an empirical loop for the holographic bit cell.

**§A — the dispersion theorems (thesis Ch. 1.2).**  De Broglie's phase wave has
`ω(β) = ω₀/√(1−β²)` and `k(β) = ω₀β/(c√(1−β²))`; his "ultimately very useful" theorem is
that the **group velocity `dω/dk` equals the particle velocity `βc`**, while the phase
velocity is `c/β`, so `V_phase · V_group = c²`.  Both are proved here from actual
derivatives (`HasDerivAt`), not algebraic shorthand.  The Compton clock is additive in
the mass — de Broglie's two-clock difficulty of Ch. 4 in its simplest exact form.

**§B — the Compton anchor (thesis Ch. 6.3, Eq. 6.3.4).**  The Compton–Debye wavelength
shift `Δλ(θ) = (2πℏ/mc)(1 − cos θ) = λ₀·2α sin²(θ/2)`, with de Broglie's own
normalization `α = ν₀/ν_C` — the photon frequency *in Compton-clock units*.  The
leverage: the right-angle shift is exactly the (non-reduced) Compton wavelength, so the
length used by the Compton--Fisher cell has an experimental scattering anchor. The additional
one-effective-mode-per-squared-resolution assignment is represented explicitly below; it is a
discretization premise, not a consequence of the scattering formula. Under that premise the mode
density is `(2π/Δλ(π/2))²` at the inference mass.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor

/-! ## §A — the phase-wave dispersion theorems -/

/-- The phase-wave frequency `ω(β) = ω₀/√(1−β²)` (thesis Eq. 1.1.7 in `ω` form). -/
noncomputable def phaseFrequency (ω₀ β : ℝ) : ℝ := ω₀ / Real.sqrt (1 - β ^ 2)

/-- The phase-wave wavenumber `k(β) = ω₀β/(c√(1−β²))`. -/
noncomputable def phaseWavenumber (ω₀ c β : ℝ) : ℝ := ω₀ * β / (c * Real.sqrt (1 - β ^ 2))

/-- **The phase velocity is `c/β`** (thesis Eq. 1.2.1): `ω/k = c/β`. -/
theorem phaseVelocity_eq (ω₀ c β : ℝ) (hω : ω₀ ≠ 0) (hβ : β ≠ 0) (h1 : β ^ 2 < 1) :
    phaseFrequency ω₀ β / phaseWavenumber ω₀ c β = c / β := by
  have hs : Real.sqrt (1 - β ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  unfold phaseFrequency phaseWavenumber
  field_simp

private lemma hasDerivAt_invSqrt (β : ℝ) (h1 : β ^ 2 < 1) :
    HasDerivAt (fun b => (Real.sqrt (1 - b ^ 2))⁻¹)
      (β / (Real.sqrt (1 - β ^ 2)) ^ 3) β := by
  have hpos : 0 < 1 - β ^ 2 := by linarith
  have hs : Real.sqrt (1 - β ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hinner : HasDerivAt (fun b : ℝ => 1 - b ^ 2) (-(2 * β)) β := by
    simpa using ((hasDerivAt_pow 2 β).const_sub 1)
  have hsqrt : HasDerivAt (fun b => Real.sqrt (1 - b ^ 2))
      (1 / (2 * Real.sqrt (1 - β ^ 2)) * -(2 * β)) β :=
    (Real.hasDerivAt_sqrt hpos.ne').comp β hinner
  have hinv := hsqrt.inv hs
  refine hinv.congr_deriv ?_
  have h3 : (Real.sqrt (1 - β ^ 2)) ^ 3
      = Real.sqrt (1 - β ^ 2) ^ 2 * Real.sqrt (1 - β ^ 2) := by ring
  rw [h3]
  field_simp

/-- The frequency's derivative: `dω/dβ = ω₀β/(√(1−β²))³`. -/
theorem hasDerivAt_phaseFrequency (ω₀ β : ℝ) (h1 : β ^ 2 < 1) :
    HasDerivAt (phaseFrequency ω₀) (ω₀ * β / (Real.sqrt (1 - β ^ 2)) ^ 3) β := by
  have hfun : phaseFrequency ω₀ = fun b => ω₀ * (Real.sqrt (1 - b ^ 2))⁻¹ := by
    funext b
    unfold phaseFrequency
    rw [div_eq_mul_inv]
  rw [hfun]
  exact ((hasDerivAt_invSqrt β h1).const_mul ω₀).congr_deriv (by ring)

/-- The wavenumber's derivative: `dk/dβ = (ω₀/c)/(√(1−β²))³`. -/
theorem hasDerivAt_phaseWavenumber (ω₀ c β : ℝ) (hc : c ≠ 0) (h1 : β ^ 2 < 1) :
    HasDerivAt (phaseWavenumber ω₀ c)
      (ω₀ / (c * (Real.sqrt (1 - β ^ 2)) ^ 3)) β := by
  have hpos : 0 < 1 - β ^ 2 := by linarith
  have hs : Real.sqrt (1 - β ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hβd : HasDerivAt (fun b : ℝ => b) 1 β := hasDerivAt_id β
  have hf := hasDerivAt_invSqrt β h1
  have hprod : HasDerivAt (fun b => b * (Real.sqrt (1 - b ^ 2))⁻¹)
      (1 * (Real.sqrt (1 - β ^ 2))⁻¹ + β * (β / (Real.sqrt (1 - β ^ 2)) ^ 3)) β :=
    hβd.mul hf
  have hfun : phaseWavenumber ω₀ c = fun b => (ω₀ / c) * (b * (Real.sqrt (1 - b ^ 2))⁻¹) := by
    funext b
    unfold phaseWavenumber
    ring
  rw [hfun]
  refine (hprod.const_mul (ω₀ / c)).congr_deriv ?_
  have hsq3 : (Real.sqrt (1 - β ^ 2)) ^ 3 = (1 - β ^ 2) * Real.sqrt (1 - β ^ 2) := by
    rw [pow_succ, Real.sq_sqrt hpos.le]
  rw [hsq3]
  field_simp
  ring

/-- **De Broglie's group-velocity theorem** (thesis Ch. 1.2, "ultimately very useful"):
the group velocity of the phase wave equals the particle velocity,
`(dω/dβ)/(dk/dβ) = βc`. -/
theorem groupVelocity_eq_particleVelocity (ω₀ c β : ℝ)
    (hω : ω₀ ≠ 0) (hc : c ≠ 0) (h1 : β ^ 2 < 1) :
    (ω₀ * β / (Real.sqrt (1 - β ^ 2)) ^ 3)
        / (ω₀ / (c * (Real.sqrt (1 - β ^ 2)) ^ 3)) = β * c := by
  have hpos : 0 < 1 - β ^ 2 := by linarith
  have hs : Real.sqrt (1 - β ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp

/-- **Phase times group is `c²`** — the dispersion duality `V·U = c²`. -/
theorem phase_mul_group_eq_c_sq (c β : ℝ) (hβ : β ≠ 0) :
    (c / β) * (β * c) = c ^ 2 := by
  field_simp

/-- **The Compton clock is additive in the mass** — the simplest exact form of the
thesis's two-clock problem (Ch. 4): two rest masses tick together as their sum. -/
theorem comptonFrequency_additive (m₁ m₂ c ħ : ℝ) (hħ : ħ ≠ 0) :
    comptonFrequency m₁ c ħ + comptonFrequency m₂ c ħ = comptonFrequency (m₁ + m₂) c ħ := by
  unfold comptonFrequency
  field_simp

/-! ## §B — the Compton scattering anchor of the bit cell -/

/-- The Compton–Debye wavelength shift `Δλ(θ) = (2πℏ/mc)(1 − cos θ)`
(thesis Eq. 6.3.4 with `λ₀·2α sin²(θ/2) = (h/mc)(1−cos θ)`). -/
noncomputable def comptonShift (m c ħ θ : ℝ) : ℝ :=
  2 * Real.pi * ħ / (m * c) * (1 - Real.cos θ)

/-- The shift in de Broglie's own normalization: `Δλ = λ₀ · 2α sin²(θ/2)` with
`α = ω₀/ω_C` the photon frequency in Compton-clock units — his Eq. 6.3.4. -/
theorem comptonShift_deBroglie_form (m c ħ θ : ℝ) :
    comptonShift m c ħ θ = 2 * Real.pi * ħ / (m * c) * (2 * Real.sin (θ / 2) ^ 2) := by
  have h := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ from by ring] at h
  unfold comptonShift
  rw [h]
  ring

/-- **The right-angle shift is the (non-reduced) Compton wavelength**:
`Δλ(π/2) = 2π·λ_C` — Compton's 1923 measurement reads the clock's cell edge directly. -/
theorem comptonShift_right_angle (m c ħ : ℝ) :
    comptonShift m c ħ (Real.pi / 2) = 2 * Real.pi * comptonWavelength m c ħ := by
  unfold comptonShift comptonWavelength
  rw [Real.cos_pi_div_two]
  ring

/-- The backscatter maximum: `Δλ(π) = 4π·λ_C`. -/
theorem comptonShift_backscatter (m c ħ : ℝ) :
    comptonShift m c ħ Real.pi = 4 * Real.pi * comptonWavelength m c ħ := by
  unfold comptonShift comptonWavelength
  rw [Real.cos_pi]
  ring

/-- **The Compton cell scale has a measured scattering anchor**: `lambda_C^2` equals
`(Delta lambda(pi/2)/(2 pi))^2`. Calling this area one microscopic cell remains a separate
discretization choice. -/
theorem cellArea_eq_shift_sq (m c ħ : ℝ) :
    comptonWavelength m c ħ ^ 2 = (comptonShift m c ħ (Real.pi / 2) / (2 * Real.pi)) ^ 2 := by
  rw [comptonShift_right_angle]
  rw [mul_comm (2 * Real.pi) (comptonWavelength m c ħ), mul_div_assoc,
    div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0), mul_one]

/-! # C. A finite operational carrier for one resolved cell -/

/-- The single effective transverse mode assigned to one Compton-resolution cell. -/
abbrev ComptonResolutionMode : Type := Fin 1

/-- The two-state occupation register of one resolved Compton mode. -/
abbrev ComptonResolutionCellState : Type := ComptonResolutionMode → Bool

/-- One Compton-resolution cell contains exactly one effective mode. -/
lemma comptonResolutionMode_card : Fintype.card ComptonResolutionMode = 1 := by
  simp [ComptonResolutionMode]

/-- The Boolean occupation register of one Compton-resolution mode has two states. -/
lemma comptonResolutionCellState_card : Fintype.card ComptonResolutionCellState = 2 := by
  rw [Fintype.card_fun, Fintype.card_bool, comptonResolutionMode_card, pow_one]

/-- The operational areal mode density: one effective transverse mode per square of the
right-angle Compton resolution `Δλ(π/2)/(2π)`. The one-mode discretization is explicit in
`ComptonResolutionMode`; the length entering the denominator is the scattering observable. -/
noncomputable def measuredComptonModeDensity (m c ħ : ℝ) : ℝ :=
  (Fintype.card ComptonResolutionMode : ℝ) /
    (comptonShift m c ħ (Real.pi / 2) / (2 * Real.pi)) ^ 2

/-- The measured one-mode-per-cell density is the inverse reduced-Compton area. -/
lemma measuredComptonModeDensity_eq_inv_cellArea (m c ħ : ℝ) :
    measuredComptonModeDensity m c ħ = 1 / comptonWavelength m c ħ ^ 2 := by
  unfold measuredComptonModeDensity
  rw [show Fintype.card ComptonResolutionMode = 1 from comptonResolutionMode_card]
  norm_num
  rw [← cellArea_eq_shift_sq]

/-- At the inference mass, the operational one-mode density agrees with the existing
Compton--Fisher screen density. -/
lemma measuredComptonModeDensity_eq_comptonBitDensity (σ₀ c ħ : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    measuredComptonModeDensity (inferenceMass σ₀) c ħ = comptonBitDensity σ₀ c ħ := by
  rw [measuredComptonModeDensity_eq_inv_cellArea,
    comptonBitDensity_eq_inv_cellArea σ₀ c ħ hσ hc hħ]

/-- **The bit density is an inverse squared measured shift**: at the inference mass, the
Compton–Fisher bit density of `tiledScreen_gravitationalResponse` is `(2π/Δλ(π/2))²`.
The Planck calibration then says: `G = ħcσ₀⁴` holds iff this *measured* cell is the
Planck area — the holographic Newton chain is anchored to Compton's scattering
experiment at one end and to the measured `G` at the other, with the calibration the
unique bridge. -/
theorem comptonBitDensity_eq_inv_shift_sq (σ₀ c ħ : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonBitDensity σ₀ c ħ
      = (2 * Real.pi / comptonShift (inferenceMass σ₀) c ħ (Real.pi / 2)) ^ 2 := by
  rw [comptonShift_right_angle,
    comptonBitDensity_eq_inv_cellArea σ₀ c ħ hσ hc hħ]
  have hlam : comptonWavelength (inferenceMass σ₀) c ħ ≠ 0 := by
    unfold comptonWavelength inferenceMass
    exact div_ne_zero hħ (mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hσ)) hc)
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor

zil attach groupVelocity_eq_particleVelocity where
  supported_by @ "lean:HermitianMat.sqrt_pos",
  formalizes @ "claim:de-broglies-1924-group-velocity-theorem-the-group-velocity-of-the-\
phase-wave-equals-the-particle-velocity-proved-from-actual-derivatives",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:de-broglie-1925-recherches-sur-la-theorie-des-quanta-ann-de-phys-10-iii"

zil attach comptonShift_right_angle where
  formalizes @ "claim:the-right-angle-compton-shift-is-the-non-reduced-compton-wavelength-\
comptons-1923-measurement-reads-the-clock-cell-edge-directly",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:de-broglie-1925-recherches-sur-la-theorie-des-quanta-ann-de-phys-10-iii",
  supported_by @ "paper:compton-1923-a-quantum-theory-of-the-scattering-of-x-rays-phys-rev-21-483"

zil attach comptonBitDensity_eq_inv_shift_sq where
  supported_by @ "lean:comptonShift_right_angle",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.comptonBitDensity_eq_inv_cellArea",
  formalizes @ "claim:the-compton-fisher-bit-density-of-the-gravitational-response-chain-\
is-the-inverse-squared-right-angle-compton-shift-at-the-inference-mass-so-the-holographic-\
area-per-bit-is-anchored-to-a-measured-scattering-observable",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.comptonBitDensity_eq_inv_cellArea"

zil attach measuredComptonModeDensity_eq_inv_cellArea where
  formalizes @ "claim:one-effective-transverse-mode-per-squared-right-angle-compton-\
resolution-has-areal-density-one-over-the-reduced-compton-wavelength-squared",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:comptonShift_right_angle",
  caveat @ "epistemic:compton-scattering-anchors-the-length-while-one-mode-per-\
resolution-cell-is-an-explicit-discretization-premise"

zil attach measuredComptonModeDensity_eq_comptonBitDensity where
  formalizes @ "claim:at-the-inference-mass-the-one-mode-per-measured-compton-\
resolution-cell-density-equals-the-compton-fisher-screen-density",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:measuredComptonModeDensity_eq_inv_cellArea",
  caveat @ "epistemic:agreement-of-two-density-definitions-does-not-show-that-\
gravitational-screens-in-nature-realize-the-cell-partition"

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
