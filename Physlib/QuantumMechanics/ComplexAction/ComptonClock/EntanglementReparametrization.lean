/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-!
# Entanglement reparametrizes the Compton clock: the same `ω = E/ℏ`, a boosted value

The Compton clock is the de Broglie relation `ω = deBroglieFrequency(E) = E/ℏ`
(`ComptonClock.FrequencyTrinity`). In the rest frame it is the Compton frequency `ω_C = ω_dB(mc²)`, the
de Broglie frequency of the rest energy. This module records how that one relation is *reparametrized* by
entanglement: two regions in a Schmidt/two-mode state of Schmidt number `K = coth η` (a Bogoliubov
transform of rapidity `η`) have a de Broglie boost `γ = cosh η`, so the clock keeps the identical form
`ω = E/ℏ` but with the energy value shifted from `mc²` to `γ mc²` (and `ω_C → γ ω_C`).

* **§A — the reparametrization.** `unentangled_compton_clock` (`γ = 1`, `ω_dB(mc²) = ω_C`),
 `entangled_compton_clock` (`ω_dB(γ mc²) = (K·sinh η) ω_C`, the boosted value written through the Schmidt
 number), `entangled_compton_clock_eq_cosh` (`γ = cosh η`), `entangled_boost_ge_one` (`γ ≥ 1`, the value
 only grows), `compton_boost_ratio` (the entangled/rest ratio is exactly `γ = cosh η`).
* **§B — the shift is the entropic / Reeh–Schlieder scale.** `entangled_scale_eq_entropicAction`
 (`log K = S_I/ℏ`); the same `log K` is the vacuum Bell decay length in Compton wavelengths,
 `r/λ_C = log K`, at which `e^{−r/λ_C} = tanh η` (`FrequencyArc.vacuumBell_at_entropicScale`).
* **§C — the assembly.** `comptonClock_entanglement_reparametrization` bundles: entangled clock
 `= γ ω_C`, `γ = cosh η = K sinh η`, `γ ≥ 1`.
* **§D — the full Einstein energy** `E = √((mc²)²+(pc)²)`, not only the rest energy. `einsteinEnergy`,
 `einsteinEnergy_sq` (`E² = (mc²)²+(pc)²`), `einsteinEnergy_rest`/`moving_clock_rest_eq_compton` (`p=0`
 recovers §A), `einsteinEnergy_eq_rest_cosh_rapidity` (`E = mc²·cosh θ`, `p = mc·sinh θ` — a *kinematic*
 rapidity parallel to the entanglement rapidity `η`), `zitterbewegung_eq_two_deBroglie_einstein`
 (`ω_Z = 2 ω_dB(E)`, tying the full energy to `FrequencyTrinity.zitterbewegungFrequency`), and
 `entangled_einstein_clock` (the Schmidt boost `cosh η` acts on the *full* energy, generalizing §A–§C).
* **§E — the two boosts compose** `E = mc²·cosh θ·cosh η`. `doubly_boosted_energy`,
 `doubly_boosted_compton_clock` (`ω = (cosh θ·cosh η) ω_C` — a moving, entangled region includes the
 kinematic momentum boost `cosh θ` and the Schmidt entanglement boost `cosh η` multiplicatively),
 `doubly_boosted_ratio` (the clock is multiplied by exactly `cosh θ·cosh η`).

The mathematics — form-invariance of `ω = E/ℏ`, `γ = cosh η = K sinh η ≥ 1`,
`log K = S_I/ℏ` — is exact and mostly already proven in the imported modules. The reading that Schmidt
entanglement *physically boosts* a region's rest energy is the interpretive framework, kept to prose.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization

open Real
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ## §A — the reparametrization: same `ω = E/ℏ`, value `mc² → γ mc²` -/

/-- **The unentangled (rest-frame) Compton clock** `ω_dB(mc²) = ω_C` — the `γ = 1` case. -/
theorem unentangled_compton_clock (m c ħ : ℝ) :
    deBroglieFrequency (m * c ^ 2) ħ = comptonFrequency m c ħ := rfl

/-- **The entangled Compton clock**: the same de Broglie relation evaluated at the boosted energy
`γ mc² = bogoliubovEnergy(sinh η, 1)·mc²` gives `(K·sinh η) ω_C` — the value shifted by the Schmidt number
`K = coth η` of the entangled state. -/
theorem entangled_compton_clock (η m c ħ : ℝ) (hη : 0 < η) :
    deBroglieFrequency (bogoliubovEnergy (Real.sinh η) 1 * (m * c ^ 2)) ħ
      = (schmidtNumber η * Real.sinh η) * comptonFrequency m c ħ := by
  rw [deBroglie_eq_bogoliubovEnergy_compton, deBroglie_boost_eq_schmidt_mul_momentum η hη]

/-- **The entangled clock at the de Broglie boost `γ = cosh η`** `ω_dB(cosh η · mc²) = cosh η · ω_C`. -/
theorem entangled_compton_clock_eq_cosh (η m c ħ : ℝ) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ = Real.cosh η * comptonFrequency m c ħ :=
  deBroglie_eq_gamma_compton (Real.cosh η) m c ħ

/-- **The boosted value only grows** `γ = cosh η ≥ 1`: the entangled Compton frequency is at least the
rest-frame `ω_C`, with equality iff `η = 0` (product state, `K → ∞`). -/
theorem entangled_boost_ge_one (η : ℝ) : 1 ≤ Real.cosh η := Real.one_le_cosh η

/-- **The entangled/rest frequency ratio is exactly the boost `γ = cosh η`**: the reparametrization
multiplies the Compton clock's value by the de Broglie boost and nothing else. -/
theorem compton_boost_ratio (η m c ħ : ℝ) (hω : comptonFrequency m c ħ ≠ 0) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ / comptonFrequency m c ħ = Real.cosh η := by
  rw [entangled_compton_clock_eq_cosh, mul_div_assoc, div_self hω, mul_one]

/-! ## §B — the shift scale is the entropic action / Reeh–Schlieder decay length -/

/-- **The reparametrization scale is the entropic action** `log K = S_I/ℏ`: the logarithm of the Schmidt
number (which is the vacuum Bell decay length in Compton wavelengths, `r/λ_C = log K`, at which
`e^{−r/λ_C} = tanh η` by `FrequencyArc.vacuumBell_at_entropicScale`) equals the entanglement's entropic
action `S_I` in units of `ℏ`. -/
theorem entangled_scale_eq_entropicAction (ħ η : ℝ) (hħ : ħ ≠ 0) :
    Real.log (schmidtNumber η) = entropicAction ħ η / ħ := by
  unfold entropicAction
  field_simp

/-! ## §C — the assembly -/

/-- **[Entanglement reparametrizes the Compton clock].** For rapidity `η > 0` the entangled clock is the
rest clock evaluated at the boosted energy `γ mc²`, `ω_dB(γ mc²) = γ ω_C`, with the boost `γ = cosh η`
equal to the Schmidt energy `K·sinh η` and never below the rest value, `γ ≥ 1`. The `ω = E/ℏ` relation is
form-invariant; only the value changes, by exactly the entanglement boost. -/
theorem comptonClock_entanglement_reparametrization (η m c ħ : ℝ) (hη : 0 < η) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ = Real.cosh η * comptonFrequency m c ħ
      ∧ Real.cosh η = schmidtNumber η * Real.sinh η
      ∧ 1 ≤ Real.cosh η :=
  ⟨deBroglie_eq_gamma_compton (Real.cosh η) m c ħ,
    (diamond_horizon_energy η).symm.trans (deBroglie_boost_eq_schmidt_mul_momentum η hη),
    Real.one_le_cosh η⟩

/-! ## §D — the full Einstein energy `E = √((mc²)² + (pc)²)`, not only the rest energy -/

/-- **The full relativistic (Einstein) energy** `E = √((mc²)² + (pc)²)` (energy–momentum relation): the
value fed into the Compton clock `ω = E/ℏ` for a *moving* region, reducing to the rest energy `mc²` at
`p = 0`. -/
noncomputable def einsteinEnergy (m c p : ℝ) : ℝ := Real.sqrt (m ^ 2 * c ^ 4 + p ^ 2 * c ^ 2)

/-- **The energy–momentum relation** `E² = (mc²)² + (pc)²`. -/
theorem einsteinEnergy_sq (m c p : ℝ) :
    einsteinEnergy m c p ^ 2 = m ^ 2 * c ^ 4 + p ^ 2 * c ^ 2 := by
  unfold einsteinEnergy
  exact Real.sq_sqrt (by positivity)

/-- **The rest energy is the `p = 0` value** `E = mc²`: the full Einstein clock reduces to the Compton
clock of §A when the region is at rest. -/
theorem einsteinEnergy_rest (m c : ℝ) (hm : 0 ≤ m) : einsteinEnergy m c 0 = m * c ^ 2 := by
  unfold einsteinEnergy
  rw [show m ^ 2 * c ^ 4 + (0 : ℝ) ^ 2 * c ^ 2 = (m * c ^ 2) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]

/-- **The full Einstein clock recovers the unentangled Compton clock at rest** `ω_dB(E)|_{p=0} = ω_C`. -/
theorem moving_clock_rest_eq_compton (m c ħ : ℝ) (hm : 0 ≤ m) :
    deBroglieFrequency (einsteinEnergy m c 0) ħ = comptonFrequency m c ħ := by
  rw [einsteinEnergy_rest m c hm]
  exact unentangled_compton_clock m c ħ

/-- **The momentum is a kinematic rapidity** `E = mc²·cosh θ` with `p = mc·sinh θ`: the full Einstein
energy is the rest energy boosted by the *kinematic* rapidity `θ`, in exact parallel to the *entanglement*
boost `cosh η` of §A–§C. The moving Compton clock records two hyperbolic angles — momentum `θ` and Schmidt
entanglement `η`. -/
theorem einsteinEnergy_eq_rest_cosh_rapidity (m c θ : ℝ) (hm : 0 ≤ m) :
    einsteinEnergy m c (m * c * Real.sinh θ) = m * c ^ 2 * Real.cosh θ := by
  have hcosh : 0 ≤ Real.cosh θ := (Real.cosh_pos θ).le
  unfold einsteinEnergy
  rw [show m ^ 2 * c ^ 4 + (m * c * Real.sinh θ) ^ 2 * c ^ 2 = (m * c ^ 2 * Real.cosh θ) ^ 2 from by
    linear_combination (-(m ^ 2 * c ^ 4)) * Real.cosh_sq θ]
  exact Real.sqrt_sq (by positivity)

/-- **The Zitterbewegung frequency is twice the full-energy de Broglie frequency** `ω_Z = 2 ω_dB(E)`: the
existing `FrequencyTrinity.zitterbewegungFrequency` is `2E/ℏ` built on exactly the full Einstein energy
`E = √((mc²)²+(pc)²)`, so the moving Compton clock is its half. -/
theorem zitterbewegung_eq_two_deBroglie_einstein (p m c ħ : ℝ) :
    zitterbewegungFrequency p m c ħ = 2 * deBroglieFrequency (einsteinEnergy m c p) ħ := by
  unfold zitterbewegungFrequency deBroglieFrequency einsteinEnergy
  rw [show p ^ 2 * c ^ 2 + m ^ 2 * c ^ 4 = m ^ 2 * c ^ 4 + p ^ 2 * c ^ 2 from by ring]
  ring

/-- **The de Broglie clock scales linearly with the energy** `ω_dB(γE) = γ ω_dB(E)` — the boost law behind
`deBroglie_eq_gamma_compton`, now stated for any energy value `E`. -/
theorem deBroglieFrequency_boost (γ E ħ : ℝ) :
    deBroglieFrequency (γ * E) ħ = γ * deBroglieFrequency E ħ := by
  unfold deBroglieFrequency; ring

/-- **Entanglement boosts the full Einstein energy** `ω_dB(cosh η · E) = cosh η · ω_dB(E)`: the Schmidt
boost `γ = cosh η` of §A–§C acts on the *full* moving-region energy `E = √((mc²)²+(pc)²)`, not only on the
rest energy. At `p = 0` this is `entangled_compton_clock_eq_cosh`. -/
theorem entangled_einstein_clock (η m c p ħ : ℝ) :
    deBroglieFrequency (Real.cosh η * einsteinEnergy m c p) ħ
      = Real.cosh η * deBroglieFrequency (einsteinEnergy m c p) ħ :=
  deBroglieFrequency_boost (Real.cosh η) (einsteinEnergy m c p) ħ

/-! ## §E — the two boosts compose: `E = mc²·cosh θ·cosh η` -/

/-- **The doubly-boosted energy** `E = mc²·cosh θ·cosh η`: a region of momentum `p = mc·sinh θ`
(kinematic rapidity `θ`) that is Schmidt-entangled at rapidity `η` includes the rest energy `mc²` multiplied
by *both* hyperbolic boosts. -/
theorem doubly_boosted_energy (m c θ η : ℝ) (hm : 0 ≤ m) :
    Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ) = (Real.cosh θ * Real.cosh η) * (m * c ^ 2) := by
  rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm]; ring

/-- **The moving, entangled Compton clock** `ω = (cosh θ · cosh η) · ω_C`: the same de Broglie relation
`ω = E/ℏ`, with the value with the kinematic momentum boost `cosh θ` and the Schmidt entanglement
boost `cosh η` together. At `θ = 0` it is the pure-entanglement clock `entangled_compton_clock_eq_cosh`;
at `η = 0` it is the pure-momentum (Zitterbewegung/half) clock. -/
theorem doubly_boosted_compton_clock (m c ħ θ η : ℝ) (hm : 0 ≤ m) :
    deBroglieFrequency (Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ)) ħ
      = (Real.cosh θ * Real.cosh η) * comptonFrequency m c ħ := by
  rw [doubly_boosted_energy m c θ η hm, deBroglie_eq_gamma_compton]

/-- **The doubly-boosted/rest frequency ratio is `cosh θ · cosh η`**: the reparametrization multiplies the
Compton clock by exactly the product of the two boosts and nothing else. -/
theorem doubly_boosted_ratio (m c ħ θ η : ℝ) (hm : 0 ≤ m) (hω : comptonFrequency m c ħ ≠ 0) :
    deBroglieFrequency (Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ)) ħ
        / comptonFrequency m c ħ = Real.cosh θ * Real.cosh η := by
  rw [doubly_boosted_compton_clock m c ħ θ η hm, mul_div_assoc, div_self hω, mul_one]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization

end
