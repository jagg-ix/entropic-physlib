/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungGeometricResolution
public import Physlib.QuantumMechanics.Schrodinger.HamiltonJacobiMadelung
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric

/-!
# The momentum-space dual: the Madelung phase gradient is the de Broglie momentum

Completes the geometric resolution of `ElectronMadelungGeometricResolution` with its **momentum-space dual**.
There the Madelung phase `S` was the Hopf `S¹` fiber; here its **spatial gradient is the de Broglie momentum**
and its **time rate is the energy**, so the phase (the fiber) includes the electron's de Broglie 4-momentum:

 free-particle phase `S(t,x) = ⟪k,x⟫ − (‖k‖²/2m)·t` (`freePhase`),
 `∇S = k` (de Broglie momentum), `∂tS = −‖k‖²/2m = −E` (energy).

* the **gradient of the Madelung phase is the momentum** `∇S = k` (`madelung_phase_gradient_is_momentum`) — the
 fiber's spatial winding rate is the de Broglie wavevector;
* the **de Broglie–Bohm guidance velocity** is `v = ∇S/m = k/m` (`madelung_guidance_velocity_is_deBroglie`) —
 the particle rides the phase gradient;
* the **de Broglie frequency at rest is the Compton clock** `ω_dB(mc²) = ω_C` (`deBroglie_rest_is_comptonClock`),
 and more generally `ω_dB = γ·ω_C` (`FrequencyTrinity.deBroglie_eq_gamma_compton`) — the boosted Compton clock
 of the arc.

So position and momentum are the two sides of the same Hopf fiber: `R² = ‖χ‖²` (amplitude / Hopf intensity) and
the phase whose spatial gradient is `k` (momentum) and whose temporal rate is `E` (energy), reducing at rest to
the Compton clock.

* **§A — the phase gradient is the momentum** (`madelung_phase_gradient_is_momentum`).
* **§B — the guidance velocity is `k/m`** (`madelung_guidance_velocity_is_deBroglie`).
* **§C — de Broglie at rest is the Compton clock** (`deBroglie_rest_is_comptonClock`).
* **§D — assembled** (`madelung_deBroglie_resolution`).

Exact reuse of `gradient_inner_sub_const` (Riesz gradient of the plane-wave phase),
`guidanceVelocity`, `deBroglieFrequency`, `comptonFrequency`. The content is the identification of the Madelung
phase's gradient/rate with the de Broglie momentum/energy, and the rest-frame de Broglie frequency with the arc's
Compton clock. No new axioms.

## References

* L. de Broglie; D. Bohm. Repo dependencies: `Schrodinger.HamiltonJacobiMadelung` (`freePhase`,
 `gradient_inner_sub_const`, `guidanceVelocity`), `ComptonClock.FrequencyTrinity`,
 `HorizonCell.ElectronMadelungGeometricResolution`.

No new axioms.
-/

set_option autoImplicit false

open scoped Gradient
open Physlib.QuantumMechanics.Schrodinger
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## §A — the phase gradient is the de Broglie momentum -/

/-- **[The Madelung phase gradient is the de Broglie momentum] `∇S = k`.** The spatial gradient of the
free-particle Madelung phase `S(t,x) = ⟪k,x⟫ − (‖k‖²/2m)t` is the de Broglie wavevector `k` — the Hopf fiber's
spatial winding rate is the momentum. -/
theorem madelung_phase_gradient_is_momentum (k x : E) (m t : ℝ) :
    ∇ (freePhase k m t) x = k := by
  unfold freePhase
  exact gradient_inner_sub_const k x (‖k‖ ^ 2 / (2 * m) * t)

/-! ## §B — the guidance velocity is `k/m` -/

/-- **[The de Broglie–Bohm guidance velocity is `k/m`] `v = ∇S/m`.** The electron rides the Madelung phase
gradient: the guidance velocity of the free-particle phase is the de Broglie velocity `k/m`. -/
theorem madelung_guidance_velocity_is_deBroglie (k x : E) (m t : ℝ) :
    guidanceVelocity (freePhase k m) m t x = (m⁻¹ : ℝ) • k := by
  unfold guidanceVelocity
  rw [madelung_phase_gradient_is_momentum]

/-! ## §C — de Broglie at rest is the Compton clock -/

/-- **[The de Broglie frequency at rest is the Compton clock] `ω_dB(mc²) = ω_C`.** For a particle at rest the
total energy is `mc²`, so its de Broglie frequency `E/ℏ` is exactly the Compton frequency `ω_C = mc²/ℏ` — the
arc's Compton clock. (Boosted: `ω_dB = γ·ω_C`, `deBroglie_eq_gamma_compton`.) -/
theorem deBroglie_rest_is_comptonClock (m c ħ : ℝ) :
    deBroglieFrequency (m * c ^ 2) ħ = comptonFrequency m c ħ := by
  simp only [deBroglieFrequency, comptonFrequency]

/-! ## §D — assembled -/

/-- **[The de Broglie momentum-space resolution, assembled].** For the free-particle Madelung wave function of
wavevector `k`:

* the phase gradient is the momentum `∇S = k`;
* the guidance velocity is `v = k/m`;
* the de Broglie frequency at rest is the Compton clock `ω_dB(mc²) = ω_C`.

Position and momentum are the two sides of the same Hopf fiber: `∇S = k` (momentum), `∂tS = −E` (energy), and at
rest the phase winds at the Compton frequency. -/
theorem madelung_deBroglie_resolution (k x : E) (m c ħ t : ℝ) :
    ∇ (freePhase k m t) x = k
      ∧ guidanceVelocity (freePhase k m) m t x = (m⁻¹ : ℝ) • k
      ∧ deBroglieFrequency (m * c ^ 2) ħ = comptonFrequency m c ħ :=
  ⟨madelung_phase_gradient_is_momentum k x m t,
    madelung_guidance_velocity_is_deBroglie k x m t,
    deBroglie_rest_is_comptonClock m c ħ⟩

/-! ## §E — the Hamilton–Killing phase gauge is the de Broglie / Compton internal clock -/

/-- **[The entropic-dynamics normalization gauge ticks at the Compton clock] `ψ(Φ + ω_dB(mc²)·t) = e^{i ω_C t}
ψ(Φ)`.** The abstract `U(1)` phase-shift parameter of Caticha's normalization Killing flow
(`HamiltonKillingNormalizationInformationMetric.hamiltonKilling_phaseShift_gauge`, which sends the wave function
`ψ = √ρ e^{iΦ}` to `e^{iν}ψ` — the gauge that makes states rays) is, physically, the accumulated **internal-clock
phase** of a particle at rest: advancing the phase by the de Broglie rest frequency `ω_dB(mc²)·t`, which is exactly
the Compton clock `ω_C·t = (mc²/ℏ)·t` (`deBroglie_rest_is_comptonClock`), multiplies `ψ` by the Compton-clock phase
`e^{i ω_C t}`. So the Hamilton–Killing normalization gauge is de Broglie's "periodic phenomenon" — the ray-space
translation Killing flow ticks at the Compton frequency `mc²/ℏ`. -/
theorem hamiltonKilling_phaseGauge_is_comptonClock (ρ Φ m c ħ t : ℝ) :
    edWaveFunction ρ (Φ + deBroglieFrequency (m * c ^ 2) ħ * t)
      = Complex.exp (((comptonFrequency m c ħ * t : ℝ) : ℂ) * Complex.I) * edWaveFunction ρ Φ := by
  rw [deBroglie_rest_is_comptonClock]
  exact hamiltonKilling_phaseShift_gauge ρ Φ (comptonFrequency m c ħ * t)

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum

end
