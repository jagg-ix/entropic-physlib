/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization -/

/-!
# Entanglement reparametrizes the Compton clock: the same `ω = E/ℏ`, a boosted value

The Compton clock is the de Broglie relation `ω = deBroglieFrequency(E) = E/ℏ`
(`ComptonClock.FrequencyTrinity`). In the rest frame it is the Compton frequency `ω_C = ω_dB(mc²)`, the
de Broglie frequency of the rest energy. This module records how that one relation is *reparametrized* by
entanglement: two regions in a Schmidt/two-mode state of Schmidt number `K = coth η` (a Bogoliubov
transform of rapidity `η`) carry a de Broglie boost `γ = cosh η`, so the clock keeps the identical form
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
  `doubly_boosted_compton_clock` (`ω = (cosh θ·cosh η) ω_C` — a moving, entangled region carries the
  kinematic momentum boost `cosh θ` and the Schmidt entanglement boost `cosh η` multiplicatively),
  `doubly_boosted_ratio` (the clock is multiplied by exactly `cosh θ·cosh η`).

**Honest layering.** The mathematics — form-invariance of `ω = E/ℏ`, `γ = cosh η = K sinh η ≥ 1`,
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


/-- **The unentangled (rest-frame) Compton clock** `ω_dB(mc²) = ω_C` — the `γ = 1` case. -/
lemma unentangled_compton_clock (m c ħ : ℝ) :
    deBroglieFrequency (m * c ^ 2) ħ = comptonFrequency m c ħ := rfl

/-- **The entangled Compton clock**: the same de Broglie relation evaluated at the boosted energy
`γ mc² = bogoliubovEnergy(sinh η, 1)·mc²` gives `(K·sinh η) ω_C` — the value shifted by the Schmidt number
`K = coth η` of the entangled state. -/
lemma entangled_compton_clock (η m c ħ : ℝ) (hη : 0 < η) :
    deBroglieFrequency (bogoliubovEnergy (Real.sinh η) 1 * (m * c ^ 2)) ħ
      = (schmidtNumber η * Real.sinh η) * comptonFrequency m c ħ := by
  rw [deBroglie_eq_bogoliubovEnergy_compton, deBroglie_boost_eq_schmidt_mul_momentum η hη]

/-- **The entangled clock at the de Broglie boost `γ = cosh η`** `ω_dB(cosh η · mc²) = cosh η · ω_C`. -/
lemma entangled_compton_clock_eq_cosh (η m c ħ : ℝ) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ = Real.cosh η * comptonFrequency m c ħ :=
  deBroglie_eq_gamma_compton (Real.cosh η) m c ħ

/-- **The boosted value only grows** `γ = cosh η ≥ 1`: the entangled Compton frequency is at least the
rest-frame `ω_C`, with equality iff `η = 0` (product state, `K → ∞`). -/
lemma entangled_boost_ge_one (η : ℝ) : 1 ≤ Real.cosh η := Real.one_le_cosh η

/-- **The entangled/rest frequency ratio is exactly the boost `γ = cosh η`**: the reparametrization
multiplies the Compton clock's value by the de Broglie boost and nothing else. -/
lemma compton_boost_ratio (η m c ħ : ℝ) (hω : comptonFrequency m c ħ ≠ 0) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ / comptonFrequency m c ħ = Real.cosh η := by
  rw [entangled_compton_clock_eq_cosh, mul_div_assoc, div_self hω, mul_one]


/-- **The reparametrization scale is the entropic action** `log K = S_I/ℏ`: the logarithm of the Schmidt
number (which is the vacuum Bell decay length in Compton wavelengths, `r/λ_C = log K`, at which
`e^{−r/λ_C} = tanh η` by `FrequencyArc.vacuumBell_at_entropicScale`) equals the entanglement's entropic
action `S_I` in units of `ℏ`. -/
lemma entangled_scale_eq_entropicAction (ħ η : ℝ) (hħ : ħ ≠ 0) :
    Real.log (schmidtNumber η) = entropicAction ħ η / ħ := by
  unfold entropicAction
  field_simp


/-- **[Entanglement reparametrizes the Compton clock].** For rapidity `η > 0` the entangled clock is the
rest clock evaluated at the boosted energy `γ mc²`, `ω_dB(γ mc²) = γ ω_C`, with the boost `γ = cosh η`
equal to the Schmidt energy `K·sinh η` and never below the rest value, `γ ≥ 1`. The `ω = E/ℏ` relation is
form-invariant; only the value changes, by exactly the entanglement boost. -/
lemma comptonClock_entanglement_reparametrization (η m c ħ : ℝ) (hη : 0 < η) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ = Real.cosh η * comptonFrequency m c ħ
      ∧ Real.cosh η = schmidtNumber η * Real.sinh η
      ∧ 1 ≤ Real.cosh η :=
  ⟨deBroglie_eq_gamma_compton (Real.cosh η) m c ħ,
    (diamond_horizon_energy η).symm.trans (deBroglie_boost_eq_schmidt_mul_momentum η hη),
    Real.one_le_cosh η⟩


/-- **The full relativistic (Einstein) energy** `E = √((mc²)² + (pc)²)` (energy–momentum relation): the
value fed into the Compton clock `ω = E/ℏ` for a *moving* region, reducing to the rest energy `mc²` at
`p = 0`. -/
noncomputable def einsteinEnergy (m c p : ℝ) : ℝ := Real.sqrt (m ^ 2 * c ^ 4 + p ^ 2 * c ^ 2)

/-- **The energy–momentum relation** `E² = (mc²)² + (pc)²`. -/
lemma einsteinEnergy_sq (m c p : ℝ) :
    einsteinEnergy m c p ^ 2 = m ^ 2 * c ^ 4 + p ^ 2 * c ^ 2 := by
  unfold einsteinEnergy
  exact Real.sq_sqrt (by positivity)

/-- **The rest energy is the `p = 0` value** `E = mc²`: the full Einstein clock reduces to the Compton
clock of §A when the region is at rest. -/
lemma einsteinEnergy_rest (m c : ℝ) (hm : 0 ≤ m) : einsteinEnergy m c 0 = m * c ^ 2 := by
  unfold einsteinEnergy
  rw [show m ^ 2 * c ^ 4 + (0 : ℝ) ^ 2 * c ^ 2 = (m * c ^ 2) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]

/-- **The full Einstein clock recovers the unentangled Compton clock at rest** `ω_dB(E)|_{p=0} = ω_C`. -/
lemma moving_clock_rest_eq_compton (m c ħ : ℝ) (hm : 0 ≤ m) :
    deBroglieFrequency (einsteinEnergy m c 0) ħ = comptonFrequency m c ħ := by
  rw [einsteinEnergy_rest m c hm]
  exact unentangled_compton_clock m c ħ

/-- **The momentum is a kinematic rapidity** `E = mc²·cosh θ` with `p = mc·sinh θ`: the full Einstein
energy is the rest energy boosted by the *kinematic* rapidity `θ`, in exact parallel to the *entanglement*
boost `cosh η` of §A–§C. The moving Compton clock carries two hyperbolic angles — momentum `θ` and Schmidt
entanglement `η`. -/
lemma einsteinEnergy_eq_rest_cosh_rapidity (m c θ : ℝ) (hm : 0 ≤ m) :
    einsteinEnergy m c (m * c * Real.sinh θ) = m * c ^ 2 * Real.cosh θ := by
  have hcosh : 0 ≤ Real.cosh θ := (Real.cosh_pos θ).le
  unfold einsteinEnergy
  rw [show m ^ 2 * c ^ 4 + (m * c * Real.sinh θ) ^ 2 * c ^ 2 = (m * c ^ 2 * Real.cosh θ) ^ 2 from by
    linear_combination (-(m ^ 2 * c ^ 4)) * Real.cosh_sq θ]
  exact Real.sqrt_sq (by positivity)

/-- **The Zitterbewegung frequency is twice the full-energy de Broglie frequency** `ω_Z = 2 ω_dB(E)`: the
existing `FrequencyTrinity.zitterbewegungFrequency` is `2E/ℏ` built on exactly the full Einstein energy
`E = √((mc²)²+(pc)²)`, so the moving Compton clock is its half. -/
lemma zitterbewegung_eq_two_deBroglie_einstein (p m c ħ : ℝ) :
    zitterbewegungFrequency p m c ħ = 2 * deBroglieFrequency (einsteinEnergy m c p) ħ := by
  unfold zitterbewegungFrequency deBroglieFrequency einsteinEnergy
  rw [show p ^ 2 * c ^ 2 + m ^ 2 * c ^ 4 = m ^ 2 * c ^ 4 + p ^ 2 * c ^ 2 from by ring]
  ring

/-- **The de Broglie clock scales linearly with the energy** `ω_dB(γE) = γ ω_dB(E)` — the boost law behind
`deBroglie_eq_gamma_compton`, now stated for any energy value `E`. -/
lemma deBroglieFrequency_boost (γ E ħ : ℝ) :
    deBroglieFrequency (γ * E) ħ = γ * deBroglieFrequency E ħ := by
  unfold deBroglieFrequency; ring

/-- **Entanglement boosts the full Einstein energy** `ω_dB(cosh η · E) = cosh η · ω_dB(E)`: the Schmidt
boost `γ = cosh η` of §A–§C acts on the *full* moving-region energy `E = √((mc²)²+(pc)²)`, not only on the
rest energy. At `p = 0` this is `entangled_compton_clock_eq_cosh`. -/
lemma entangled_einstein_clock (η m c p ħ : ℝ) :
    deBroglieFrequency (Real.cosh η * einsteinEnergy m c p) ħ
      = Real.cosh η * deBroglieFrequency (einsteinEnergy m c p) ħ :=
  deBroglieFrequency_boost (Real.cosh η) (einsteinEnergy m c p) ħ


/-- **The doubly-boosted energy** `E = mc²·cosh θ·cosh η`: a region of momentum `p = mc·sinh θ`
(kinematic rapidity `θ`) that is Schmidt-entangled at rapidity `η` carries the rest energy `mc²` multiplied
by *both* hyperbolic boosts. -/
lemma doubly_boosted_energy (m c θ η : ℝ) (hm : 0 ≤ m) :
    Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ) = (Real.cosh θ * Real.cosh η) * (m * c ^ 2) := by
  rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm]; ring

/-- **The moving, entangled Compton clock** `ω = (cosh θ · cosh η) · ω_C`: the same de Broglie relation
`ω = E/ℏ`, with the value carrying the kinematic momentum boost `cosh θ` and the Schmidt entanglement
boost `cosh η` together. At `θ = 0` it is the pure-entanglement clock `entangled_compton_clock_eq_cosh`;
at `η = 0` it is the pure-momentum (Zitterbewegung/half) clock. -/
lemma doubly_boosted_compton_clock (m c ħ θ η : ℝ) (hm : 0 ≤ m) :
    deBroglieFrequency (Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ)) ħ
      = (Real.cosh θ * Real.cosh η) * comptonFrequency m c ħ := by
  rw [doubly_boosted_energy m c θ η hm, deBroglie_eq_gamma_compton]

/-- **The doubly-boosted/rest frequency ratio is `cosh θ · cosh η`**: the reparametrization multiplies the
Compton clock by exactly the product of the two boosts and nothing else. -/
lemma doubly_boosted_ratio (m c ħ θ η : ℝ) (hm : 0 ≤ m) (hω : comptonFrequency m c ħ ≠ 0) :
    deBroglieFrequency (Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ)) ħ
        / comptonFrequency m c ħ = Real.cosh θ * Real.cosh η := by
  rw [doubly_boosted_compton_clock m c ħ θ η hm, mul_div_assoc, div_self hω, mul_one]


/-- **The Compton-clock boost as an explicit function of the entropic action** `S_I = ħ log K`:
`γ = cosh η = (1 − e^{−2 S_I/ħ})^{−1/2}`. Feeding the entanglement-suppression identity
`e^{−S_I/ħ} = tanh η` (`SchmidtRapidityHyperbolicUnification.suppression_eq_tanh`) into
`cosh²η = (1 − tanh²η)⁻¹` writes the de Broglie boost `γ` purely through the imaginary action `S_I` that
the survival / transition maximization extremizes: as `S_I → 0` (maximal survival, `e^{−2S_I/ħ} → 1`)
`γ → ∞` (the short-distance Reeh–Schlieder limit), and as `S_I → ∞` `γ → 1` (the clock returns to its
rest value `ω_C`). -/
lemma comptonClock_boost_eq_entropicAction (η ħ : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) :
    Real.cosh η = Real.sqrt ((1 - Real.exp (-2 * (entropicAction ħ η / ħ)))⁻¹) := by
  have hexp2 : Real.exp (-2 * (entropicAction ħ η / ħ)) = Real.tanh η ^ 2 := by
    rw [show (-2 * (entropicAction ħ η / ħ))
          = -(entropicAction ħ η / ħ) + -(entropicAction ħ η / ħ) from by ring,
        Real.exp_add, suppression_eq_tanh ħ η hħ hη]
    ring
  have hc : Real.cosh η ≠ 0 := ne_of_gt (Real.cosh_pos η)
  have hstep : (1 - Real.tanh η ^ 2)⁻¹ = Real.cosh η ^ 2 := by
    have hid : 1 - Real.tanh η ^ 2 = (Real.cosh η ^ 2)⁻¹ := by
      rw [Real.tanh_eq_sinh_div_cosh, div_pow]
      field_simp
      linarith [Real.cosh_sq_sub_sinh_sq η]
    rw [hid, inv_inv]
  rw [hexp2, hstep, Real.sqrt_sq (Real.cosh_pos η).le]

/-- **The entangled/rest Compton-clock frequency ratio as a function of the entropic action**:
`ω_dB(γ mc²)/ω_C = (1 − e^{−2 S_I/ħ})^{−1/2}`. Combines `compton_boost_ratio` (the observable ratio is
the boost `γ = cosh η`) with `comptonClock_boost_eq_entropicAction` (the boost is the entropic-action
expression). The observable Compton-clock rate is thus fixed by the same imaginary action `S_I` that the
NN survival / Caticha ED transition maximization extremizes. -/
lemma comptonClock_frequency_boost_eq_entropicAction
    (η m c ħ : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) (hω : comptonFrequency m c ħ ≠ 0) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ / comptonFrequency m c ħ
      = Real.sqrt ((1 - Real.exp (-2 * (entropicAction ħ η / ħ)))⁻¹) := by
  rw [compton_boost_ratio η m c ħ hω, comptonClock_boost_eq_entropicAction η ħ hħ hη]



/-- **The wavelength anti-scaling** `λ_C(γm) = λ_C(m)/γ` — the mirror of the clock's boost
law: boosting the mass contracts the Compton wavelength, hence the Yukawa screening range
(`Yukawa.ScreenedPotential.reducedYukawa_compton_screening`). -/
theorem comptonWavelength_scaling (γ m c ħ : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength (γ * m) c ħ = Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength m c ħ / γ := by
  unfold Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
  rw [div_div]
  ring_nf

/-- **The doubly boosted screening range**: a moving, entangled region (kinematic rapidity
`θ`, Schmidt rapidity `η`) sees the mediator's screening range contracted by exactly
`cosh θ · cosh η` — the §E composition acting on the Yukawa range. -/
theorem doubly_boosted_screening (θ η m c ħ : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength (Real.cosh θ * Real.cosh η * m) c ħ
      = Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength m c ħ / (Real.cosh θ * Real.cosh η) :=
  comptonWavelength_scaling (Real.cosh θ * Real.cosh η) m c ħ

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization

end

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementBoostEnergyCost -/

/-!
# What the entanglement boost would cost, if it were physical

`EntanglementReparametrization` writes the entangled clock as `ω_dB(γ mc²) = γ ω_C` with
`γ = cosh η`, and `SchmidtFixedPointClockBridges.bell_boost` fixes `γ = 2/√3` for a maximally
entangled pair (`K = 2`).  The library is careful to call this a **reparametrization**:
`ComptonClockMalamentProperTimeLinks` records the caveat that it is *"parameter identifiability on
the nonnegative rapidity branch, not an independent derivation that entanglement physically boosts
rest energy."*

This file asks what happens if that caveat is dropped — i.e. if the boost is read as a claim about
nature, so that an entangled constituent really carries energy `γ mc²` rather than `mc²`.  The
answer is that the reading is refuted, and not marginally.

**The cost.**  The excess is `(γ − 1) mc²`, a *fixed fraction* of the rest energy with no small
parameter anywhere:

  `2/√3 − 1 = 0.154701…`,  i.e. **15.47 %** of `mc²` per maximally entangled constituent.

§B proves the bracket `0.15 < 2/√3 − 1 < 0.16`, so this cannot be argued down.

**Why that refutes it.**  Preparing a Bell pair would have to inject that energy from nowhere:

| constituent | `mc²` | required excess |
|---|---|---|
| ⁴⁰Ca⁺ | 37.3 GeV | **5.76 GeV** |
| ⁸⁷Sr, ⁸⁷Rb | 81.0 GeV | 12.5 GeV |
| ¹⁷¹Yb⁺ | 159.3 GeV | 24.6 GeV |

An ion-trap entangling gate is driven by Raman or microwave photons carrying `~10⁻⁶ eV`.  The
physical-boost reading demands `5.8 × 10¹⁵` times the energy the gate supplies, per ion, appearing
on entanglement and vanishing again on disentanglement.  No energy-conservation test at any
precision permits this; it is excluded by roughly fifteen orders of magnitude, which is why no
dedicated experiment is needed to settle it.

**What survives.**  Only the interpretation dies.  `entangled_compton_clock_eq_cosh`,
`bell_boost_sq`, `bell_boost` and the whole `K = coth η` structure stand untouched as exact
algebra — a reparametrization of the clock in terms of the Schmidt coordinate.  What is removed is
the reading on which `γ mc²` is a physically carried energy.  This is the same kind of subtraction
as the Compton-anchor coherence bound, which refuted the dissipative reading of `S_I` while leaving
the phase-like reading intact.

Scope.  The theorems below are the arithmetic of the excess.  The refutation is the physical
reading of that arithmetic against energy conservation, recorded in the ZIL bound rather than
proved here — Lean is not being asked to certify that entangling two ions fails to create 5.76 GeV.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementBoostEnergyCost

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — the energy the boost would require -/

/-- The rest-energy excess demanded by reading the entanglement boost as physical:
`(γ − 1) mc²`, the energy an entangled constituent would carry beyond `mc²`. -/
def boostEnergyExcess (γ m c : ℝ) : ℝ := (γ - 1) * (m * c ^ 2)

/-- **The excess vanishes exactly on the unentangled point.**  `γ = 1` is `K = 1`, the separable
case, and it is the only value costing nothing — so any genuine entanglement carries a bill. -/
theorem boostEnergyExcess_eq_zero_iff {γ m c : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) :
    boostEnergyExcess γ m c = 0 ↔ γ = 1 := by
  unfold boostEnergyExcess
  constructor
  · intro h
    have hmc : m * c ^ 2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 hc)
    have hsub : γ - 1 = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact absurd h2 hmc
    linarith
  · intro h
    rw [h]
    ring

/-! ### §B — at the Bell value the fraction is 15%, and cannot be argued down -/

/-- **The Bell-pair excess bracket.**  With `γ = 2/√3` from `bell_boost` (`K = 2`), the fractional
rest-energy excess lies strictly between `0.15` and `0.16`.  There is no limit in which this is
small: it is `15.47 %` of `mc²`, per maximally entangled constituent. -/
theorem bell_boost_fraction_bounds :
    (15 : ℝ) / 100 < 2 / Real.sqrt 3 - 1 ∧ 2 / Real.sqrt 3 - 1 < 16 / 100 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr h3
  have hsne : Real.sqrt 3 ≠ 0 := ne_of_gt hs
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo : (1.732 : ℝ) < Real.sqrt 3 := by nlinarith [hsq, hs]
  have hhi : Real.sqrt 3 < 1.7321 := by nlinarith [hsq, hs]
  have hrw : 2 / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    field_simp
    nlinarith [hsq]
  rw [hrw]
  constructor <;> linarith [hlo, hhi]

/-- **The excess is strictly positive for any nontrivial entanglement.**  Since `γ = cosh η > 1`
for `η > 0`, every entangled constituent would carry strictly more energy than its rest mass —
there is no sign choice or branch on which the cost cancels. -/
theorem boostEnergyExcess_pos {γ m c : ℝ} (hγ : 1 < γ) (hm : 0 < m) (hc : c ≠ 0) :
    0 < boostEnergyExcess γ m c := by
  unfold boostEnergyExcess
  have hc2 : 0 < c ^ 2 := by positivity
  have hmc : 0 < m * c ^ 2 := mul_pos hm hc2
  have hg : 0 < γ - 1 := by linarith
  exact mul_pos hg hmc

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementBoostEnergyCost.bell_boost_fraction_bounds where
  formalizes @ "claim:reading-the-entanglement-boost-as-a-physical-rest-energy-requires-each-maximally-entangled-constituent-to-carry-fifteen-percent-more-than-m-c-squared-which-energy-conservation-excludes",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization.entangled_compton_clock_eq_cosh",
  experimental_bound @ "value:energy-conservation-in-ion-trap-entangling-gates-driven-by-photons-of-order-one-microelectronvolt;test:the-physical-boost-reading-demands-5.76-GeV-per-calcium-40-ion-appearing-on-entanglement-and-vanishing-on-disentanglement-about-5.8e15-times-the-gate-energy-so-the-reading-is-excluded-by-roughly-fifteen-orders-of-magnitude",
  caveat @ "what-is-refuted-is-the-physical-boost-interpretation-only-the-reparametrization-theorems-entangled-compton-clock-eq-cosh-and-bell-boost-remain-exact-algebra-in-the-schmidt-coordinate"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementBoostEnergyCost.boostEnergyExcess_pos where
  formalizes @ "claim:every-nontrivial-entanglement-boost-carries-a-strictly-positive-rest-energy-cost-so-no-branch-or-sign-choice-cancels-the-excess",
  epistemic_status @ "consistency-identity",
  requires @ "claim:reading-the-entanglement-boost-as-a-physical-rest-energy-requires-each-maximally-entangled-constituent-to-carry-fifteen-percent-more-than-m-c-squared-which-energy-conservation-excludes",
  caveat @ "positivity-follows-from-cosh-eta-greater-than-one-it-does-not-assert-that-the-excess-is-physically-carried"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementBoostEnergyCost

end

