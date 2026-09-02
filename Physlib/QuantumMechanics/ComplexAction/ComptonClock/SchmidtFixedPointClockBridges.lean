/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.HamiltonianRenormalisation.FreeScalarCovarianceFlow
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicMacroscopicLadder
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum

/-!
# The Thiemann fixed point, the Schmidt clock, and the Caticha metric: three bridges

Three exact bridges welding the Hamiltonian-renormalisation arc, the entropic-distance/
de Broglie clock arc, and Caticha's information geometry into one hyperbolic structure:

* `imageLadder_coincidence_eq_schmidtNumber` — **Thiemann meets Schmidt**: the fixed-point
  image-ladder covariance of the Hamiltonian-renormalisation flow
  (`FreeScalarCovarianceFlow.image_ladder_resummed`, `sinh q/(cosh q − cos t)`), evaluated
  at coincidence `t = 0`, equals `coth(q/2) = schmidtNumber (q/2)` by the half-angle
  identities — the resummed ladder of thermal images stores the entanglement dictionary at
  half the damping parameter.
* `bell_boost_sq`, `bell_boost`, `bell_deBroglie_clock` — **the one-region pair's de
  Broglie clock**: the Bell marginal's collision weight `1/2` gives Schmidt number `2`;
  the boost–Schmidt relation `γ²(K²−1) = K²` then fixes `γ² = 4/3`, so the pair's Madelung
  fiber winds at `ω_dB = (2/√3)·ω_C` — the entanglement content of the one-region pair
  determines its momentum-side clock through
  `EntanglementReparametrization.entangled_compton_clock_eq_cosh`.
* `bell_marginal_density_difference_zero`, `bell_fisherRao_separation_zero` — **Caticha's
  curved configuration space flattens on the pair**: the two marginal densities agree
  pointwise, so the Fisher–Rao line element — the entropic-dynamics quantum potential
  (`quantumPotential_is_fisherRao_lineElement`) — vanishes between the pair's two ends:
  the information-geometric twin of the trace-distance and Szabados flatness statements
  of the one-region model.

## References

* Carriers: `QFT.HamiltonianRenormalisation.FreeScalarCovarianceFlow` (Thiemann fixed
  point), `ComptonClock.EntropicProperDistance` + `MuonAnomaly.SchmidtRapidityHyperbolicUnification`
  (Schmidt/boost), `ComptonClock.EntropicMacroscopicLadder` (the Bell collision weight),
  `EntropicTime.HamiltonKillingNormalizationInformationMetric` (Caticha Fisher–Rao),
  `HorizonCell.ElectronMadelungDeBroglieMomentum` (the Madelung fiber this clock winds).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicMacroscopicLadder
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.SchmidtFixedPointClockBridges

/-! ## §A — the Thiemann fixed point stores the Schmidt dictionary -/

/-- **The fixed-point image ladder at coincidence is the Schmidt number**: the resummed
covariance `sinh q/(cosh q − cos t)` of the Hamiltonian-renormalisation fixed point,
evaluated at `t = 0`, equals `coth(q/2) = schmidtNumber (q/2)` — the half-angle
identities turn the thermal-image ladder into the entanglement dictionary. -/
theorem imageLadder_coincidence_eq_schmidtNumber (q : ℝ) (hq : 0 < q) :
    Real.sinh q / (Real.cosh q - Real.cos 0) = schmidtNumber (q/2) := by
  rw [Real.cos_zero]
  unfold schmidtNumber
  have hhalf : 0 < q/2 := by linarith
  have hs : 0 < Real.sinh (q/2) := by
    have hexp := Real.exp_lt_exp.mpr (show -(q/2) < q/2 by linarith)
    rw [Real.sinh_eq]
    linarith
  have hsinh : Real.sinh q = 2 * Real.sinh (q/2) * Real.cosh (q/2) := by
    have h := Real.sinh_two_mul (q/2)
    rwa [show 2*(q/2) = q by ring] at h
  have hcosh : Real.cosh q - 1 = 2 * Real.sinh (q/2)^2 := by
    have h1 := Real.cosh_two_mul (q/2)
    rw [show 2*(q/2) = q by ring] at h1
    have h2 := Real.cosh_sq_sub_sinh_sq (q/2)
    linarith
  rw [hsinh, hcosh]
  field_simp

/-! ## §B — the one-region pair's de Broglie clock -/

/-- **The Bell pair's boost is fixed by its entanglement**: Schmidt number `2` (from the
collision weight `1/2` of the computed marginal) in the boost–Schmidt relation gives
`cosh²η = 4/3`. -/
theorem bell_boost_sq (η : ℝ) (hη : 0 < η)
    (hK : schmidtNumber η
      = (collisionWeight ((MState.pure bellPhiPlus).traceRight))⁻¹) :
    Real.cosh η ^ 2 = 4/3 := by
  have h2 : schmidtNumber η = 2 := by
    rw [hK, collisionWeight_bellMarginal]
    norm_num
  have hb := boost_sq_schmidt_relation η hη
  rw [h2] at hb
  linarith

/-- **The Bell boost itself**: `cosh η = 2/√3`. -/
theorem bell_boost (η : ℝ) (hη : 0 < η)
    (hK : schmidtNumber η
      = (collisionWeight ((MState.pure bellPhiPlus).traceRight))⁻¹) :
    Real.cosh η = 2 / Real.sqrt 3 := by
  have h := bell_boost_sq η hη hK
  have hpos : 0 < Real.cosh η := Real.cosh_pos η
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (2 / Real.sqrt 3)^2 = 4/3 := by
    rw [div_pow, hs3]
    norm_num
  have hfac : (Real.cosh η - 2/Real.sqrt 3) * (Real.cosh η + 2/Real.sqrt 3) = 0 := by
    linear_combination h - h2
  rcases mul_eq_zero.mp hfac with hf | hf
  · linarith
  · exfalso
    have : 0 < 2/Real.sqrt 3 := by positivity
    linarith

/-- **The one-region pair's Madelung fiber winds at `ω_dB = (2/√3)·ω_C`**: the de Broglie
clock boost of the entangled pair is determined by its entanglement content — the
momentum-side clock of `ElectronMadelungDeBroglieMomentum`, fixed by the collision datum
of the entropic ladder. -/
theorem bell_deBroglie_clock (m c ħ η : ℝ) (hη : 0 < η)
    (hK : schmidtNumber η
      = (collisionWeight ((MState.pure bellPhiPlus).traceRight))⁻¹) :
    deBroglieFrequency (Real.cosh η * (m * c^2)) ħ
      = (2/Real.sqrt 3) * comptonFrequency m c ħ := by
  rw [Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization.entangled_compton_clock_eq_cosh
    η m c ħ, bell_boost η hη hK]

/-! ## §C — Caticha's information metric flattens on the pair -/

/-- **The pair's two marginal densities agree pointwise**: the density difference between
the two ends vanishes at every configuration point. -/
theorem bell_marginal_density_difference_zero (i : Fin 2) :
    (((MState.pure bellPhiPlus).traceLeft).m i i).re
      - (((MState.pure bellPhiPlus).traceRight).m i i).re = 0 := by
  rw [bellPhiPlus_traceLeft_uniform, bellPhiPlus_traceRight_uniform]
  ring

/-- **The Fisher–Rao line element between the pair's ends vanishes**: with zero density
displacement, Caticha's information metric — the entropic-dynamics quantum potential — is
flat across the identification locus, the information-geometric twin of the
trace-distance and Szabados flatness statements. -/
theorem bell_fisherRao_separation_zero (ρ : ℝ) (hρ : ρ ≠ 0) (i : Fin 2) :
    edQuantumPotential 1 ρ
      ((((MState.pure bellPhiPlus).traceLeft).m i i).re
        - (((MState.pure bellPhiPlus).traceRight).m i i).re) = 0 := by
  rw [bell_marginal_density_difference_zero,
    quantumPotential_is_fisherRao_lineElement ρ 0 hρ]
  ring

/-! ## §D — the welded chain, assembled -/

/-- **The one-region resolution, assembled**: for the Bell rapidity — the `η` whose Schmidt
number is the inverse collision weight of the computed marginal — the whole chain holds at
once:

1. **Caticha's gauge is the Compton clock**: the normalization Killing flow advanced by the
   de Broglie rest frequency multiplies the entropic-dynamics wave function by the
   Compton-clock phase;
2. **the rest fiber winds at the Compton clock**: `ω_dB(mc²) = ω_C`;
3. **the entanglement fixes the Schmidt number**: `K = 2`;
4. **the entropic radius is one bit**: `r = λ_C·log 2`;
5. **the boosted fiber winds at** `ω_dB = (2/√3)·ω_C`;
6. **the Thiemann fixed point stores the datum**: the image-ladder covariance at
   coincidence, at damping `2η`, equals the Bell Schmidt number `2`.

Caticha gauge flow = Compton clock = rest de Broglie fiber, boosted by `2/√3`, with `K = 2`
from the collision weight, `r = λ_C log 2` on the entropic ladder, and the `coth` stored in
the Hamiltonian-renormalisation fixed point — every arrow one structure. -/
theorem bell_oneRegion_resolution (m c ħ η : ℝ) (hη : 0 < η)
    (hK : schmidtNumber η
      = (collisionWeight ((MState.pure bellPhiPlus).traceRight))⁻¹) :
    (∀ ρ Φ t : ℝ, edWaveFunction ρ (Φ + deBroglieFrequency (m * c ^ 2) ħ * t)
        = Complex.exp (((comptonFrequency m c ħ * t : ℝ) : ℂ) * Complex.I)
            * edWaveFunction ρ Φ)
    ∧ deBroglieFrequency (m * c ^ 2) ħ = comptonFrequency m c ħ
    ∧ schmidtNumber η = 2
    ∧ entropicProperDistance m c ħ η = comptonWavelength m c ħ * Real.log 2
    ∧ deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ
        = (2 / Real.sqrt 3) * comptonFrequency m c ħ
    ∧ Real.sinh (2 * η) / (Real.cosh (2 * η) - Real.cos 0) = 2 := by
  have h2 : schmidtNumber η = 2 := by
    rw [hK, collisionWeight_bellMarginal]
    norm_num
  refine ⟨fun ρ Φ t => hamiltonKilling_phaseGauge_is_comptonClock ρ Φ m c ħ t,
    deBroglie_rest_is_comptonClock m c ħ, h2, ?_, bell_deBroglie_clock m c ħ η hη hK, ?_⟩
  · unfold entropicProperDistance
    rw [h2]
  · have h := imageLadder_coincidence_eq_schmidtNumber (2 * η) (by linarith)
    rw [show (2 * η) / 2 = η by ring, h2] at h
    exact h

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.SchmidtFixedPointClockBridges

end
